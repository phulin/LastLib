# Ihara Theory and Saturated Degeneracy Maps on Shimura Curves

## Contents

1. [Why integral level change is difficult](#1-why-integral-level-change-is-difficult)
   - [The old map and the question it leaves](#11-the-old-map-and-the-question-it-leaves)
   - [The three meanings of injectivity](#12-the-three-meanings-of-injectivity)
   - [The geometric mechanism](#13-the-geometric-mechanism)
   - [Dependency boundary](#14-dependency-boundary)
2. [The clean Shimura-curve datum](#2-the-clean-shimura-curve-datum)
   - [Global quaternionic data](#21-global-quaternionic-data)
   - [The changing prime and its two levels](#22-the-changing-prime-and-its-two-levels)
   - [Coefficients, neatness, and exceptional primes](#23-coefficients-neatness-and-exceptional-primes)
   - [Hecke and Eisenstein conventions](#24-hecke-and-eisenstein-conventions)
3. [Integral linear algebra before geometry](#3-integral-linear-algebra-before-geometry)
   - [Primitive submodules](#31-primitive-submodules)
   - [Reduction detects saturation](#32-reduction-detects-saturation)
   - [Orthogonal new lattices](#33-orthogonal-new-lattices)
   - [Localization and completion](#34-localization-and-completion)
4. [The local tree at the changing prime](#4-the-local-tree-at-the-changing-prime)
   - [Lattices and adjacent vertices](#41-lattices-and-adjacent-vertices)
   - [Why the lattice graph is a tree](#42-why-the-lattice-graph-is-a-tree)
   - [Vertex and edge stabilizers](#43-vertex-and-edge-stabilizers)
   - [The one-edge quotient](#44-the-one-edge-quotient)
5. [Cohomology of a group acting on a tree](#5-cohomology-of-a-group-acting-on-a-tree)
   - [The cellular resolution](#51-the-cellular-resolution)
   - [The Mayer--Vietoris sequence](#52-the-mayer--vietoris-sequence)
   - [The kernel of the two degeneracy restrictions](#53-the-kernel-of-the-two-degeneracy-restrictions)
   - [Hecke action on arithmetic characters](#54-hecke-action-on-arithmetic-characters)
6. [The geometric Ihara criterion](#6-the-geometric-ihara-criterion)
   - [Complex uniformization and comparison](#61-complex-uniformization-and-comparison)
   - [The degeneracy map as restriction](#62-the-degeneracy-map-as-restriction)
   - [The exact kernel and its congruence part](#63-the-exact-kernel-and-its-congruence-part)
   - [The residual Ihara criterion](#64-the-residual-ihara-criterion)
7. [Integral saturation](#7-integral-saturation)
   - [Freeness of curve cohomology](#71-freeness-of-curve-cohomology)
   - [From residual injectivity to a primitive image](#72-from-residual-injectivity-to-a-primitive-image)
   - [Torsion-freeness of the old quotient](#73-torsion-freeness-of-the-old-quotient)
   - [What fails without localization](#74-what-fails-without-localization)
8. [The Iwahori integral model](#8-the-iwahori-integral-model)
   - [The incidence moduli problem](#81-the-incidence-moduli-problem)
   - [The nodal chart and regularity](#82-the-nodal-chart-and-regularity)
   - [The two degeneracy maps on the special fiber](#83-the-two-degeneracy-maps-on-the-special-fiber)
   - [Fine covers and coarse descent](#84-fine-covers-and-coarse-descent)
9. [Nodal cohomology and monodromy](#9-nodal-cohomology-and-monodromy)
   - [Normalization of a nodal curve](#91-normalization-of-a-nodal-curve)
   - [The graph exact sequence](#92-the-graph-exact-sequence)
   - [Nearby cycles and the integral filtration](#93-nearby-cycles-and-the-integral-filtration)
   - [The monodromy pairing](#94-the-monodromy-pairing)
10. [Component groups and degeneracy maps](#10-component-groups-and-degeneracy-maps)
    - [The discriminant presentation](#101-the-discriminant-presentation)
    - [Functoriality and adjunction](#102-functoriality-and-adjunction)
    - [Why old classes have no toric part](#103-why-old-classes-have-no-toric-part)
    - [The localized component-control theorem](#104-the-localized-component-control-theorem)
11. [The Gram matrix and its limits](#11-the-gram-matrix-and-its-limits)
    - [Adjoints of the two maps](#111-adjoints-of-the-two-maps)
    - [The exact matrix](#112-the-exact-matrix)
    - [Congruence factors](#113-congruence-factors)
    - [Why a determinant is not an Ihara proof](#114-why-a-determinant-is-not-an-ihara-proof)
12. [The integral new quotient](#12-the-integral-new-quotient)
    - [Quotient and orthogonal definitions](#121-quotient-and-orthogonal-definitions)
    - [Perfect duality](#122-perfect-duality)
    - [Hecke stability and transpose](#123-hecke-stability-and-transpose)
    - [Monodromy carried by the new quotient](#124-monodromy-carried-by-the-new-quotient)
13. [Descent and exceptional cases](#13-descent-and-exceptional-cases)
    - [Residue-field and Galois descent](#131-residue-field-and-galois-descent)
    - [Ramified base change and thickness](#132-ramified-base-change-and-thickness)
    - [Stabilizers and small coefficient primes](#133-stabilizers-and-small-coefficient-primes)
    - [Scalar, Eisenstein, and vexing cases](#134-scalar-eisenstein-and-vexing-cases)
14. [The saturated Ihara package](#14-the-saturated-ihara-package)
    - [Main theorem](#141-main-theorem)
    - [Proof of the main theorem](#142-proof-of-the-main-theorem)
    - [Hypothesis and dependency ledger](#143-hypothesis-and-dependency-ledger)
    - [Exact boundary of the theorem](#144-exact-boundary-of-the-theorem)
15. [Conclusion](#15-conclusion)
   - [The mathematical package](#151-the-mathematical-package)
   - [The role in integral level change](#152-the-role-in-integral-level-change)

## 1. Why integral level change is difficult

### 1.1 The old map and the question it leaves

Let $F$ be a totally real field, let $B/F$ be a quaternion algebra split at exactly one real place, and let $X_U$ be a compact Shimura curve of sufficiently fine level $U$. Fix a finite place $v$ at which $B$ is split and $U_v$ is hyperspecial. Replacing $U_v$ by the standard Iwahori subgroup $I_v$ gives a second curve $X_{U_0(v)}$ and two finite degeneracy maps

$$
\pi_0,\pi_1:X_{U_0(v)}\longrightarrow X_U.
$$

Pullback along these maps produces the old map

$$
d=(\pi_0^*,\pi_1^*):
H^1(X_{U,\overline F},\mathcal O)^{\oplus2}
\longrightarrow
H^1(X_{U_0(v),\overline F},\mathcal O), \tag{1.1}
$$

where $\mathcal O$ is a complete discrete valuation ring of residue characteristic $\ell$, and $v\nmid\ell$. The old submodule is the image of $d$.

Over the fraction field of $\mathcal O$, local representation theory explains the dimension of the old space. That rational statement is not enough for arithmetic. If the image of (1.1) has finite index in its saturation, reducing modulo the uniformizer can create a false kernel. If the quotient has torsion, a residual class that appears to be new may be only the shadow of that torsion. If a special-fiber component group has been ignored, a rational old--new decomposition can miss precisely the congruence class one wants to retain.

The integral question is therefore not merely whether $d$ is injective in characteristic zero. It is whether, after localization at the relevant non-Eisenstein Hecke maximal ideal,

$$
\bar d:
H^1(X_{U},k)^{\oplus2}_{\mathfrak m}
\longrightarrow
H^1(X_{U_0(v)},k)_{\mathfrak m} \tag{1.2}
$$

is injective and whether the integral image in (1.1) is saturated. Here $k=\mathcal O/\varpi$. These are the two assertions usually grouped under the name **Ihara lemma** in the present setting.

### 1.2 The three meanings of injectivity

Three statements that look similar must be separated.

First, rational injectivity says that $d\otimes E$ has zero kernel, where $E=\operatorname{Frac}(\mathcal O)$. It determines the dimension of the old subspace but forgets finite index.

Second, residual injectivity says that $d\otimes k$ has zero kernel after Hecke localization. This is stronger. For maps between finite free modules over a DVR it is exactly the criterion that the integral image be primitive.

Third, geometric injectivity concerns the homomorphism of Jacobians

$$
\delta:J_U\times J_U\longrightarrow J_{U_0(v)},
\qquad (x,y)\longmapsto\pi_0^*x+\pi_1^*y. \tag{1.3}
$$

The kernel of $\delta$ can contain a finite subgroup even if its tangent map is injective. Such a subgroup is harmless at a non-Eisenstein localization only after its Hecke action has been calculated. Declaring the kernel finite is not enough: its order may be divisible by $\ell$, and its reduction may then create exactly the kernel in (1.2).

The tree calculation below identifies the entire residual kernel exactly. It also proves that the part coming from congruence-continuous characters of the norm-one arithmetic group is Eisenstein. Reduced norm, the center, and the component set are incorporated separately through component routing, central-character twists, and tame descent. What the calculation does not prove from the stated catalog hypotheses is that every abstract finite character of the $S$-arithmetic group is congruence-continuous, or the weaker assertion that the remaining characters have Eisenstein Hecke transfer. That distinction is decisive. The integral saturation and component package is therefore proved under the exact residual vanishing condition isolated in Section 6.4; Section 14 records why removing that condition requires a new arithmetic theorem.

### 1.3 The geometric mechanism

There are two geometries, one generic and one integral.

At the generic place, the Bruhat--Tits tree for $\operatorname{PGL}_2(F_v)$ has two adjacent vertices stabilized by the two hyperspecial levels and an edge stabilized by the Iwahori level. The two degeneracy maps become the two restriction maps in the cohomology of vertex and edge stabilizers. The cellular resolution of the tree shows that the kernel comes from the cohomology of the group obtained by allowing arbitrary level at $v$. In degree one with constant coefficients, this cohomology consists of additive characters. A direct double-coset calculation expresses the difference between a good Hecke operator and its Eisenstein degree as an explicit commensurator discrepancy. That discrepancy vanishes on congruence-continuous characters; its possible noncongruence part is the exact unresolved term. Non-Eisenstein localization kills the whole kernel only when that remaining term vanishes.

At the integral place, the fine Iwahori PEL model is regular semistable. Its completed nodal charts are

$$
xy=\pi_v.
$$

The special fiber has a dual graph $\Gamma$. Its cycle lattice

$$
X_\Gamma=H_1(\Gamma,\mathbf Z)
$$

is the character lattice of the torus in the special Jacobian. The edge-length pairing

$$
q_\Gamma:X_\Gamma\longrightarrow X_\Gamma^\vee
$$

has cokernel equal to the geometric Néron component group. Thus the same bad fiber records both the nontrivial monodromy of the new quotient and the finite obstruction that rational linear algebra would erase.

There is a second, logically independent Smith module. Projecting the old image to the normalized components gives the branch matrix $\left(\begin{smallmatrix}1&F_v^*\\F_v^*&1\end{smallmatrix}\right)$. Under the residual Ihara condition this is an equal-rank injection, so its cokernel is finite and measures whether the sum of the old lattice and the bottom graph lattice is primitive. Full old-image saturation does not force this cokernel to vanish, so the component filtration below retains it explicitly.

### 1.4 Dependency boundary

Six earlier books supply the exact imported facts.

Book 16 supplies the normalization sequence of a nodal curve, graph homology, weighted monodromy pairings, their discriminant groups, subdivision invariance, and functoriality under finite maps. Book 38 supplies Néron models, extension of Jacobian homomorphisms, identity components, component maps, and the Raynaud description of a semistable Jacobian. Book 39 supplies integral pull--norm correspondences, adjunction, specialization, and the intersection- and graph-lattice formulas for their component actions. Book 124 supplies the two Shimura degeneracy maps with the right-double-coset orientation, their adjoints, and the exact old-level Gram formalism; it explicitly does not supply saturation. Book 118 supplies rank-one strong approximation for the simply connected norm-one quaternion group, with the required archimedean noncompactness and arbitrary compact-open conditions at every finite place. Book 122 supplies the parahoric PEL model, the chart $xy=\pi_v$, strict semistability, the graph description of monodromy, and Hecke functoriality away from $v$; it explicitly makes integral conclusions conditional on saturation.

No listed prerequisite computes the prime-to-small-prime abelianization of the norm-one $S$-arithmetic group or the action of its good-place commensurators. In particular Book 118 proves strong approximation, which gives density and the one-edge tree quotient, but not a congruence-subgroup property and not continuity of an abstract finite character for the congruence topology.

The new work here is the specialization of strong approximation to the tree quotient, the exact Bass--Serre and Mayer--Vietoris calculation, the good-place calculation on congruence-continuous norm-one characters with the separate norm and component routing, the precise isolation of the noncongruence character obstruction, the conditional primitive-image and torsion-free-quotient theorems, and their synthesis with the monodromy, component, and branch-correction sequences. No rational old--new decomposition, later level-change theorem, or later automorphic comparison is used to conceal the unresolved arithmetic condition.

## 2. The clean Shimura-curve datum

### 2.1 Global quaternionic data

We now specify the curves for which the theorem is proved. Let $F$ be totally real and $B/F$ a quaternion algebra split at exactly one real place $\tau$ and ramified at all other real places. We assume $B$ is a division algebra. The associated Shimura curves are then proper: no cusp or boundary term enters their first cohomology.

Let

$$
G=\operatorname{Res}_{F/\mathbf Q}B^\times
$$

with the central convention already fixed in the chosen canonical model. For the group-theoretic calculation put $H=\operatorname{SL}_1(B)$ over $F$ and use the derived group

$$
G^1=\operatorname{Res}_{F/\mathbf Q}H.
$$

Passing from $G$ to $G^1$ fixes a connected component and removes the reduced-norm coordinate, but it need not identify the effective arithmetic stabilizers literally. Let $\overline\Gamma$ be the effective projective stabilizer of one connected $G$-component and let $\Gamma^1$ be the image of its norm-one subgroup. Reduced norm modulo central squares gives an injection

$$
\overline\Gamma/\Gamma^1
\hookrightarrow F^\times/F^{\times2}.
$$

Indeed, if the reduced norm of $b$ is $z^2$, then $z^{-1}b$ has norm one and represents the same projective element. This quotient has exponent two and is finite because the arithmetic stabilizer is finitely generated. Ineffective rational central units have already been divided out; any remaining central kernel of the norm-one cover also has order at most two.

Write $\Delta_{\mathrm{cen}}$ for this finite effective descent group. Since $\ell\ge7$, restriction and averaging give

$$
H^j(\overline\Gamma,A)
\simeq H^j(\Gamma^1,A)^{\Delta_{\mathrm{cen}}}
$$

for every finite $\ell$-primary trivial coefficient module $A$. Indeed the Hochschild--Serre spectral sequence has terms $H^a(\Delta_{\mathrm{cen}},H^b(\Gamma^1,A))$, and averaging by $|\Delta_{\mathrm{cen}}|^{-1}$ kills every term with $a>0$. The same statement holds after adjoining any normal fine-cover deck group of order prime to $\ell$. Choose one common normal cover at hyperspecial and Iwahori level, so that its descent action preserves the two vertex types and both degeneracy maps. We write $\Delta$ for the resulting finite descent group and take $\Delta=1$ when the chosen curve is already the norm-one fine cover. Thus reduced norm and the center contribute exact prime-to-$\ell$ invariants, not new $\ell$-primary characters.

The finite component routing of a central double coset is handled before this passage, as in the established Shimura-curve convention. We require the chosen component union to be stable under every correspondence used below, and every norm-one tree sequence below is understood componentwise before applying the exact functor $(\ )^\Delta$.

Fix a compact open

$$
U=U^vU_v\subset G(\mathbf A_f)
$$

which is neat. Neatness means that the arithmetic stabilizers acting on the complex upper half-plane are torsion-free. It makes the quotient a smooth curve rather than an orbifold and eliminates stabilizer denominators. Section 13.3 explains the weaker prime-to-$\ell$ condition sufficient for descent from a fine cover.

For orientation, take $F=\mathbf Q$ and let $B$ be indefinite and ramified at a nonempty even set of finite primes. Then $B$ is division, $B\otimes\mathbf R\simeq M_2(\mathbf R)$, and a neat Eichler level gives a compact Riemann surface

$$
\Gamma\backslash\mathfrak H.
$$

At a prime $v$ outside the quaternion discriminant and level, $B_v\simeq M_2(\mathbf Q_v)$ and the hyperspecial-to-Iwahori change is exactly the adjacent-lattice construction below. The general totally real case differs by component routing and residue degree, not by the local tree or integral saturation argument.

The division hypothesis has a precise role. It removes cusps, so singular cohomology of the curve is group cohomology of a cocompact torsion-free lattice with no boundary module. For a split modular curve, a tree argument still exists, but its Mayer--Vietoris sequence includes parabolic and cusp terms. Those terms are Eisenstein only after a separate boundary calculation. They are outside the stated quaternionic theorem rather than silently discarded.

### 2.2 The changing prime and its two levels

Let $v$ be a finite place of $F$ with residue field cardinality $q_v$, and assume:

1. $B_v\simeq M_2(F_v)$;
2. the PEL datum and polarization lattice are unramified and self-dual at $v$;
3. under a fixed integral splitting, $U_v=\operatorname{GL}_2(\mathcal O_{F_v})$ modulo the chosen center;
4. $I_v\subset U_v$ is the inverse image of the upper triangular Borel modulo $v$;
5. the rank-two determinant local model is the flat incidence model.

Put

$$
U_0(v)=U^vI_v.
$$

Choose

$$
h_v=\begin{pmatrix}\varpi_v&0\\0&1\end{pmatrix}.
$$

The two maps from Iwahori to hyperspecial level are the forgetful map $\pi_0$ and the translated-then-forgotten map $\pi_1$. The latter includes the final forgetful morphism after right translation; without it the codomain would be the conjugate level. Both maps are finite, and on Jacobians their pullbacks are the two summands in (1.3).

We always distinguish $v$ from the coefficient prime $\ell$. The assumption $v\nmid\ell$ is what permits ordinary finite coefficients in the tree argument and prime-to-residue-characteristic monodromy on the semistable model.

### 2.3 Coefficients, neatness, and exceptional primes

Let $E/\mathbf Q_\ell$ be finite, $\mathcal O$ its valuation ring, $\varpi$ a uniformizer, and $k$ its residue field. We work in the catalog's clean coefficient range $\ell\ge7$. This also avoids the classical stabilizer orders on the selected fine quotient. Some fine-level arguments remain valid at smaller odd primes, but the uniform theorem does not suppress the extra checks they require.

All cohomology modules are taken with constant coefficients. We write

$$
M=H^1(X_{U,\overline F},\mathcal O),
\qquad
N=H^1(X_{U_0(v),\overline F},\mathcal O). \tag{2.1}
$$

After choosing an embedding $\overline F\hookrightarrow\mathbf C$, comparison identifies these with singular cohomology. The compact oriented surfaces underlying the curves have torsion-free integral first homology, so $M$ and $N$ are finite free over $\mathcal O$. This elementary fact will be proved in Section 7.1 rather than assumed at the point where saturation is needed.

At nonneat level, choose a neat normal subgroup $U'\triangleleft U$. If the order of the deck group is a unit in $\mathcal O$, taking invariants is exact and every result, including the abelian Ihara condition when known upstairs, descends. If $\ell$ divides that order, a stabilizer cohomology class can enter the Ihara kernel. Such a level is outside the clean conditional package; it requires a stack-level or type-enhanced calculation.

### 2.4 Hecke and Eisenstein conventions

Let $\Sigma$ contain $v$, the places where $B$, the level, or the integral PEL datum is ramified, and the coefficient place. After fixing representatives for the finite component union, enlarge $\Sigma$ by the finitely many places where one of those representatives is nonintegral. For $w\notin\Sigma$, let $T_w$ be the unnormalized spherical right-double-coset operator. Thus $T_w$ has degree $q_w+1$ on constants. Let $S_w$ be the central one-coset operator.

Component routing must be fixed before an Eisenstein ideal is named. On a Hecke-stable union of geometric components, let $P_w$ be the one-coset transport induced by right multiplication by the abelianized class of a uniformizer at $w$. On labels it is a permutation; on the direct sum of component cohomologies it includes the canonical right-translation identification, expressed in chosen uniformizations by the corresponding rational transition. The intrinsic arithmetic Eisenstein relations on that union are

$$
T_w-(q_w+1)P_w,
\qquad
S_w-P_w^2. \tag{2.2}
$$

If a central or component character $\eta$ is selected, then $P_w$ acts by $\eta_w(\varpi_w)$ and these relations become

$$
T_w-(q_w+1)\eta_w(\varpi_w),
\qquad
S_w-\eta_w(\varpi_w)^2. \tag{2.3}
$$

The clean block used below is a Hecke-stable block on which both component routing and the central character are trivial. There $P_w=1$, and we write

$$
\mathfrak E=\bigl(T_w-(q_w+1),\ S_w-1:
w\notin\Sigma\bigr). \tag{2.4}
$$

A maximal ideal $\mathfrak m$ of the integral Hecke image is **non-Eisenstein** if it does not contain $\mathfrak E$ in the sense that at least one generator in (2.4) acts invertibly after localization at $\mathfrak m$. Equivalently, the trivial arithmetic scalar system does not occur at $\mathfrak m$. On a nontrivial component or central block one uses (2.2) or (2.3), not (2.4).

This definition is deliberately operator-theoretic. When a residual two-dimensional representation has already been constructed, absolute irreducibility implies non-Eisensteinness, but no such representation is needed in the conditional argument. The calculation below proves the displayed relations on congruence-continuous arithmetic characters. It does not build continuity into the word “character.”

There are two reasons to define the ideal using infinitely many good operators. First, it makes the definition independent of a chosen generating set of the finite image algebra. Since the image algebra acting on a fixed finite module is finite over $\mathcal O$, finitely many of the displayed relations generate the same localized ideal on that module. Second, it separates a geometric condition from a Galois interpretation. Once the exact residual condition of Section 6.4 is imposed, the proof only needs one operator $T_w-(q_w+1)$ or $S_w-1$ to become a unit. It never needs a representation attached to $\mathfrak m$.

If a central character is retained, a one-dimensional unramified system has two Satake characters, one of which is trivial after normalization and the other determined by that character. The scalar relation is (2.3). Rather than guess an inverse diamond, one obtains it by applying the declared right-coset correspondence to the central component. The transpose identity then checks the result. This is why the main theorem records the trivial-central relation explicitly and treats the twisted relation by the invariant matrix (11.4).

A maximal ideal supported only on component permutation is not automatically Eisenstein. The chosen component union must first be stable, so every $T_w$ is an actual endomorphism. Only then do (2.2)--(2.4) make sense in one image algebra. Component routing and Eisenstein localization solve different typing problems.

## 3. Integral linear algebra before geometry

### 3.1 Primitive submodules

Let $R$ be a DVR with fraction field $K$, uniformizer $\pi$, and residue field $\kappa$. If $L$ is a finite free $R$-module and $A\subset L$ is a submodule, the saturation of $A$ is

$$
A^{\mathrm{sat}}=L\cap(A\otimes_RK). \tag{3.1}
$$

The submodule $A$ is **primitive** or **saturated** if $A=A^{\mathrm{sat}}$. This is equivalent to $L/A$ being torsion-free.

The equivalence is immediate. If $\pi x\in A$ and $A$ is saturated, then $x\in A\otimes K$ and hence $x\in A$; thus $L/A$ has no $\pi$-torsion. Conversely, if $x\in L$ and $\pi^n x\in A$, torsion-freeness of $L/A$ gives $x\in A$. Since every element of (3.1) has this form, $A$ is saturated.

Over a DVR every finite torsion-free module is free. Thus a primitive submodule of a finite free module and its quotient are both free. This is why saturation, rather than a rational direct-sum decomposition, is the useful integral notion.

### 3.2 Reduction detects saturation

The fundamental criterion is the following.

**Lemma 3.1 (residual criterion).** Let $f:L\to P$ be a homomorphism of finite free $R$-modules. The following are equivalent:

1. $f$ is injective and $P/f(L)$ is torsion-free;
2. the reduction $\bar f:L/\pi L\to P/\pi P$ is injective;
3. in Smith normal form, every nonzero elementary divisor of $f$ is a unit and the number of nonzero elementary divisors is $\operatorname{rank}L$.

**Proof.** Choose bases and put the matrix of $f$ in Smith normal form

$$
\operatorname{diag}(\pi^{a_1},\ldots,\pi^{a_r},0,\ldots,0),
\qquad 0\le a_1\le\cdots\le a_r.
$$

Reduction is injective precisely when $r=\operatorname{rank}L$ and every $a_i=0$. The same condition says that $f$ is injective and that its cokernel has no summand $R/\pi^{a_i}R$. This proves all equivalences. $\square$

An important consequence is that residual injectivity already contains both clauses of the clean integral Ihara statement once the source and target cohomology are known to be free. No separate determinant argument is required.

### 3.3 Orthogonal new lattices

Suppose $P$ has a perfect $R$-bilinear pairing

$$
(\ ,\ ):P\times P\longrightarrow R
$$

and $A\subset P$ is saturated. Define

$$
A^\perp=\{x\in P:(x,A)=0\}. \tag{3.2}
$$

**Lemma 3.2 (quotient--kernel duality).** There is a canonical isomorphism

$$
A^\perp\simeq(P/A)^\vee. \tag{3.3}
$$

In particular $A^\perp$ and $P/A$ are finite free.

**Proof.** Perfectness identifies $P$ with $P^\vee$. Under this identification, $A^\perp$ is the kernel of the restriction map $P^\vee\to A^\vee$. Because $A$ is saturated, $P/A$ is free, so the exact sequence

$$
0\to A\to P\to P/A\to0
$$

splits as a sequence of $R$-modules. Dualizing is therefore exact and gives

$$
0\to(P/A)^\vee\to P^\vee\to A^\vee\to0.
$$

The two kernels agree, proving (3.3). $\square$

Without saturation, the restriction map need not be onto and the dual of the torsion-free quotient is the orthogonal lattice only after replacing $A$ by $A^{\mathrm{sat}}$. This is the precise reason an orthogonal complement cannot repair a nonsaturated old image by definition.

### 3.4 Localization and completion

Let $\mathbb T$ be a finite commutative $R$-algebra acting on finite free modules. For a maximal ideal $\mathfrak m$, localization is exact. If $f:L\to P$ is $\mathbb T$-linear, then

$$
(\ker f)_{\mathfrak m}=\ker(f_{\mathfrak m}),
\qquad
(\operatorname{coker}f)_{\mathfrak m}
=\operatorname{coker}(f_{\mathfrak m}). \tag{3.4}
$$

Reduction and localization also commute:

$$
(L_{\mathfrak m})/\pi
\simeq(L/\pi L)_{\mathfrak m}. \tag{3.5}
$$

Indeed localization is tensoring with the flat algebra $\mathbb T_{\mathfrak m}$, and quotient by $\pi$ is tensoring with $R/\pi$. Associativity of tensor products gives (3.5).

Completion at $\mathfrak m$ is faithfully flat on finite $\mathbb T_{\mathfrak m}$-modules. Injectivity, vanishing, and torsion-freeness can therefore be checked either before or after completion. We shall write a subscript $\mathfrak m$ without distinguishing localization from its finite completion when the assertion is unchanged by this faithfully flat passage.

Two examples show how little rational linear algebra remembers.

Let

$$
f:R^2\longrightarrow R^2,
\qquad
f=\begin{pmatrix}1&0\\0&\pi^a\end{pmatrix}.
$$

For every $a$, the rational map is an isomorphism. Its saturation quotient is $R/\pi^aR$. Reduction is injective exactly at $a=0$, in agreement with Lemma 3.1.

Now let

$$
g:R\longrightarrow R^2,
\qquad g(x)=(x,\pi^ax).
$$

The first coordinate is a unit minor, so the image is primitive for every $a$. With the standard pairing, its restricted Gram is $1+\pi^{2a}$, a unit. If the ambient pairing is changed to $\operatorname{diag}(1,-u)$ with $u\equiv1\pmod\pi$, the image remains primitive while its Gram $1-u\pi^{2a}$ can be a nonunit. Primitivity belongs to the map and ambient lattice; the Gram belongs additionally to a pairing.

Localization introduces no exception to the residual criterion. Although $\mathbb T_{\mathfrak m}$ need not itself be a DVR, all modules remain finite over the coefficient DVR $R$, and saturation is tested for $R$-torsion. The Hecke localization only removes unwanted direct factors. Thus Lemma 3.1 is applied to the underlying finite free $R$-modules after localization, not to a fictitious Smith form over the Hecke algebra.

## 4. The local tree at the changing prime

### 4.1 Lattices and adjacent vertices

Put $K=F_v$, let $\mathcal O_v$ be its valuation ring, and choose a uniformizer $\varpi$. A vertex of the Bruhat--Tits graph $\mathscr T_v$ is a homothety class $[L]$ of rank-two $\mathcal O_v$-lattices in $K^2$. Two vertices are adjacent when representatives can be chosen with

$$
\varpi L\subsetneq L'\subsetneq L. \tag{4.1}
$$

Then $L/L'$ is a line over the residue field. There are $q_v+1$ such lines, so every vertex has valence $q_v+1$.

Let

$$
L_0=\mathcal O_ve_1\oplus\mathcal O_ve_2,
\qquad
L_1=\mathcal O_ve_1\oplus\varpi\mathcal O_ve_2. \tag{4.2}
$$

Their homothety classes are adjacent. The stabilizer of $[L_0]$ in $\operatorname{GL}_2(K)$ is $K^\times\operatorname{GL}_2(\mathcal O_v)$, and the common stabilizer of the oriented edge $[L_0]\to[L_1]$ is, modulo scalars, the Iwahori subgroup. Conjugating the first vertex stabilizer by $h_v=\operatorname{diag}(\varpi,1)$ gives the stabilizer of the other endpoint.

The two vertex types are the parity of

$$
v(\det g)\pmod2
$$

for an element carrying $[L_0]$ to the vertex. The group $\operatorname{SL}_2(K)$ preserves type, is transitive on vertices of either fixed type, and is transitive on edges. The full projective group can exchange the types.

It is useful to see the $q_v+1$ neighbors without choosing representatives abstractly. The neighbors of $[L_0]$ correspond to points of $\mathbf P^1(k_v)$. For $a\in k_v$, lift $a$ to $\widetilde a\in\mathcal O_v$ and put

$$
L_a=\mathcal O_v(e_1+\widetilde a e_2)
+\varpi\mathcal O_ve_2.
$$

The remaining point $\infty$ gives

$$
L_\infty=\varpi\mathcal O_ve_1+\mathcal O_ve_2.
$$

Changing a lift changes no lattice. Reduction modulo $\varpi$ identifies the intermediate lattice in (4.1) with a line of $L_0/\varpi L_0$, proving that this list is complete and has no repetition. The standard Iwahori fixes the neighbor $L_0\supset L_1$ and acts transitively on the other $q_v$ oriented continuations. This elementary distinction is the local reason a spherical operator has degree $q_v+1$ while an oriented Iwahori operator has degree $q_v$.

### 4.2 Why the lattice graph is a tree

The absence of cycles is the local fact on which the global Mayer--Vietoris argument rests.

**Proposition 4.1.** The graph $\mathscr T_v$ is connected and has a unique nonbacktracking path between any two vertices. In particular it is a tree.

**Proof.** Given lattices $L$ and $L'$, multiply $L'$ by a scalar and use the elementary divisor theorem over the DVR to choose a basis of $L$ in which

$$
L'=\mathcal O_v\varpi^ae_1\oplus
\mathcal O_v\varpi^be_2,
\qquad a\le b.
$$

Homothety removes $a$, so the relative position is represented by $(0,n)$ with $n=b-a\ge0$. The chain

$$
[L]=[\mathcal O_ve_1\oplus\mathcal O_ve_2],
[\mathcal O_ve_1\oplus\varpi\mathcal O_ve_2],\ldots,
[\mathcal O_ve_1\oplus\varpi^n\mathcal O_ve_2]
$$

connects the vertices. Thus the graph is connected.

Define the distance between $[L]$ and $[L']$ to be the integer $n$ just obtained. It is independent of bases because it is the difference of the two elementary divisors. If $[M]$ is adjacent to $[L']$, its distance from $[L]$ is $n-1$ or $n+1$; it is $n-1$ for exactly one neighbor, namely the predecessor obtained by decreasing the larger elementary divisor. Hence from $[L']$ there is exactly one first step on a shortest path toward $[L]$. Induction gives uniqueness of the shortest path. Any nonbacktracking path must lower the distance whenever it points toward its endpoint and cannot return to a previously visited vertex without creating two possible predecessors. It is therefore the unique shortest path. A cycle would give two nonbacktracking paths between two of its vertices, which is impossible. $\square$

The proof also gives a useful orientation rule: moving across an edge alternates vertex type. Thus the quotient by a type-preserving group is naturally bipartite.

Distance also records double cosets. The sphere of radius one around $[L_0]$ is the right-coset set

$$
K_v\begin{pmatrix}\varpi&0\\0&1\end{pmatrix}K_v/K_v,
$$

and has $q_v+1$ points. Nonbacktracking paths of length $r$ correspond to relative position $\operatorname{diag}(\varpi^r,1)$ and number $q_v^{r-1}(q_v+1)$. A backtracking pair returns to the original vertex with a central scalar. These counts recover the first spherical convolution relation and check that the tree orientation agrees with the right-double-coset convention used for $T_v$.

### 4.3 Vertex and edge stabilizers

Let

$$
\Gamma^v=H(F)\cap U^{1,v}, \tag{4.3}
$$

where $U^{1,v}$ is the part away from $v$ of the chosen level in the norm-one group. We impose no condition at $v$ in (4.3). Inside $\Gamma^v$ define

$$
\Gamma_0=\operatorname{Stab}([L_0]),
\qquad
\Gamma_1=\operatorname{Stab}([L_1]),
\qquad
\Gamma_e=\operatorname{Stab}([L_0],[L_1]). \tag{4.4}
$$

The quotient $\Gamma_0\backslash\mathfrak H$ is the first lower-level component. Right translation by the finite adele $h_v$ routes the second vertex to a lower-level component; the component formula of Book 124 supplies the rational transition which identifies that component with $\Gamma_1\backslash\mathfrak H$. The quotient $\Gamma_e\backslash\mathfrak H$ is the Iwahori-level curve. The inclusions $\Gamma_e\subset\Gamma_i$, with that rational transition on the second leg, induce its two degeneracy maps. No local adele is being used to conjugate a diagonal rational group.

There is no orientation reversal in $\Gamma^v$. An element reversing the edge would exchange vertex types, but every norm-one element has determinant valuation zero under the chosen splitting. This matters in the cellular resolution: the edge stabilizer acts trivially on the chosen orientation module.

### 4.4 The one-edge quotient

We need the action of $\Gamma^v$ on $\mathscr T_v$ to have one edge as quotient. This is exactly the rank-one strong-approximation theorem proved in Book 118, Section 6.2; it is not a consequence of weak approximation on a rational chart.

**Theorem 4.2 (strong approximation in the required form).** Let $B/F$ be a quaternion algebra split at the distinguished real place. For every open compact $U^{1,v}\subset H(\mathbf A_{F,f}^v)$, the projection of

$$
H(F)\cap U^{1,v}
$$

to $H(F_v)\simeq\operatorname{SL}_2(F_v)$ is dense. Consequently $\Gamma^v$ is transitive on edges of $\mathscr T_v$ and on vertices of each type, and

$$
\Gamma^v\backslash\mathscr T_v
$$

is a single closed edge with its two endpoints.

**Proof.** The group $H$ is simply connected. Because $B$ is split at the distinguished real place $\tau$, the group $H(F_\tau)$ is $\operatorname{SL}_2(\mathbf R)$ and is noncompact. The rank-one strong-approximation theorem of Book 118, Section 6.2, therefore says that

$$
\operatorname{SL}_1(B)(F)
\quad\hbox{is dense in}\quad
\operatorname{SL}_1(B)(\mathbf A_{F,f}). \tag{4.5}
$$

This theorem includes the integral compact-open condition at every finite place outside any prescribed finite set. Apply it to the nonempty adelic open

$$
W_v\times U^{1,v}
\subset
H(F_v)\times H(\mathbf A_{F,f}^v), \tag{4.6}
$$

where $W_v$ is an arbitrary neighborhood of an arbitrary element of $H(F_v)$. A rational point in this open lies in $H(F)\cap U^{1,v}$ and has $v$-component in $W_v$. Hence the projection of $\Gamma^v$ is dense.

The stabilizer in $\operatorname{SL}_2(F_v)$ of a vertex or edge is open. Density therefore implies that every translate of $[L_0]$, $[L_1]$, or their edge under $\operatorname{SL}_2(F_v)$ is already a translate under $\Gamma^v$. The local transitivity from Section 4.1 gives the asserted quotient. $\square$

The hypotheses just checked are essential. The cited theorem is for the simply connected norm-one group and requires a noncompact archimedean factor. It makes no strong-approximation assertion for the reduced-norm torus or for $B^\times$; those groups retain the component, ideal-class, and sign obstructions recorded in Book 118. We selected one connected norm-one component before applying it.
There is also a useful algebraic consequence of the one-edge quotient. A group acting without inversion on a tree with fundamental domain one edge is the amalgamated product

$$
\Gamma^v\simeq\Gamma_0*_{\Gamma_e}\Gamma_1. \tag{4.7}
$$

To prove this, the inclusions define a homomorphism from the amalgam to $\Gamma^v$. Transitivity on edges makes it surjective. A reduced word alternating between the two vertex stabilizers traces a nonbacktracking path starting at the fundamental edge. If the word represented the identity, that path would close, contradicting that the lattice graph is a tree. This proves injectivity. We shall use the cohomological form of the same statement, because it keeps all coefficient rings visible.

## 5. Cohomology of a group acting on a tree

### 5.1 The cellular resolution

Let a group $\Gamma$ act without inversion on a tree $T$ whose quotient is one edge. Choose representatives $v_0,v_1,e$, with stabilizers $\Gamma_0,\Gamma_1,\Gamma_e$. Let $A$ be a commutative ring with trivial $\Gamma$-action.

The augmented cellular chain complex of the contractible graph $T$ is

$$
0\longrightarrow\mathbf Z[E(T)]
\xrightarrow{\partial}
\mathbf Z[V(T)]
\xrightarrow{\epsilon}\mathbf Z
\longrightarrow0. \tag{5.1}
$$

The absence of cycles gives injectivity on the left; connectedness gives exactness in the middle. Orbit decomposition identifies the permutation modules as

$$
\mathbf Z[E(T)]\simeq
\mathbf Z[\Gamma/\Gamma_e],
$$

$$
\mathbf Z[V(T)]\simeq
\mathbf Z[\Gamma/\Gamma_0]\oplus
\mathbf Z[\Gamma/\Gamma_1]. \tag{5.2}
$$

Applying $\operatorname{Hom}_\Gamma(-,A)$ to (5.1) begins the cochain complex

$$
0\longrightarrow A
\longrightarrow A^{\Gamma_0}\oplus A^{\Gamma_1}
\longrightarrow A^{\Gamma_e}. \tag{5.3}
$$

To reach degree one group cohomology, take projective resolutions of the three permutation modules and form the double complex. Shapiro's lemma identifies the resulting vertical cohomology with the cohomology of the stabilizers.

### 5.2 The Mayer--Vietoris sequence

**Theorem 5.1 (tree Mayer--Vietoris).** In the preceding setting there is a natural long exact sequence

$$
\begin{aligned}
0&\to H^0(\Gamma,A)
\to H^0(\Gamma_0,A)\oplus H^0(\Gamma_1,A)
\to H^0(\Gamma_e,A)\\
&\to H^1(\Gamma,A)
\to H^1(\Gamma_0,A)\oplus H^1(\Gamma_1,A)
\xrightarrow{r_0-r_1}H^1(\Gamma_e,A)
\to H^2(\Gamma,A)\to\cdots . \tag{5.4}
\end{aligned}
$$

Here $r_i$ is restriction, with the second inclusion followed by the fixed rational component transition identifying its vertex quotient with the routed lower-level curve.

**Proof.** Replace the three terms of (5.1) by projective $\mathbf Z[\Gamma]$-resolutions and apply $\operatorname{Hom}_\Gamma(-,A)$. The horizontal homology is $H^*(\Gamma,A)$ because (5.1) resolves the trivial module. The vertical homology of the induced resolution $\mathbf Z[\Gamma/\Gamma_H]$ is $H^*(H,A)$ by the adjunction

$$
\operatorname{Hom}_\Gamma
(\mathbf Z[\Gamma/H]\otimes P,A)
\simeq\operatorname{Hom}_H(P,A).
$$

The two spectral sequences of the double complex therefore produce the long exact sequence (5.4). The cellular boundary sends the oriented edge to $v_1-v_0$, which accounts for the difference $r_0-r_1$. $\square$

Because the coefficient action is trivial,

$$
H^1(\Gamma,A)=\operatorname{Hom}(\Gamma^{\mathrm{ab}},A). \tag{5.5}
$$

Indeed a one-cocycle is an additive homomorphism and a one-coboundary is zero. This elementary description is what makes the Hecke action on the possible kernel computable.

### 5.3 The kernel of the two degeneracy restrictions

Take $\Gamma=\Gamma^v$ and $T=\mathscr T_v$. Exactness of (5.4) gives

$$
\ker(r_0-r_1)=
\operatorname{im}\left(
H^1(\Gamma^v,A)\longrightarrow
H^1(\Gamma_0,A)\oplus H^1(\Gamma_1,A)
\right). \tag{5.6}
$$

The geometric old map uses $r_0+r_1$ rather than $r_0-r_1$ if the two pullbacks are written without changing the orientation of the second vertex. Multiplication by $-1$ on the second source copy converts one convention to the other. Thus their kernels are canonically identified and injectivity is independent of this sign.

Formula (5.6) is the heart of Ihara's argument. It does not say the kernel is zero. It identifies every possible relation between the two old copies as the restriction of an additive character of the $S$-arithmetic group $\Gamma^v$. The next section computes the Hecke action on precisely those characters.

### 5.4 Hecke action on arithmetic characters

There is a subtlety which must be settled before using a transfer formula. A Hecke representative at a place $w$ need not belong to $\Gamma^v$, so conjugation by it is not inner on $\Gamma^{v,\mathrm{ab}}$. Strong approximation does not remove this problem: it controls the congruence closure of $\Gamma^v$, whereas a homomorphism from the abstract group to a finite abelian group need not be continuous for that topology.

Fix the finite stable component set from Section 2.4 and choose a finite-adelic representative $x_c$ for each label $c$; write $x_c^v$ for its away-from-$v$ component. Put

$$
H=\operatorname{SL}_1(B),
\qquad
K_c^v=H(\mathbf A_{F,f}^v)\cap x_c^vU^v(x_c^v)^{-1},
\qquad
\Gamma_c=H(F)\cap K_c^v. \tag{5.7}
$$

Book 118 makes $\Gamma_c$ dense in $K_c^v$. For a finite $\ell$-primary $\mathcal O$-module $A$, define

$$
H^1_{\mathrm{cong}}(\Gamma_c,A)
=\operatorname{Hom}_{\mathrm{cont}}(K_c^v,A)
\hookrightarrow\operatorname{Hom}(\Gamma_c,A)
=H^1(\Gamma_c,A), \tag{5.8}
$$

where injectivity follows from density, and define

$$
H^1_{\mathrm{nc}}(\Gamma_c,A)
=H^1(\Gamma_c,A)/H^1_{\mathrm{cong}}(\Gamma_c,A). \tag{5.9}
$$

On the stable union these modules are summed over $c$; write the resulting modules as $\mathcal H^1(A)$, $\mathcal H^1_{\mathrm{cong}}(A)$, and $\mathcal H^1_{\mathrm{nc}}(A)$. The quotient in (5.9) measures only failure of congruence continuity. No finiteness or centrality assertion about the congruence kernel is being made.

Let $w\notin\Sigma$, and let $h_w$ be the finite adele whose $w$-component is $\operatorname{diag}(\varpi_w,1)$ and whose other components are $1$. It belongs to the ambient quaternionic similitude group, not in general to $H(F)$. Thus it must not be used to conjugate a diagonal rational arithmetic group.

The Hecke span routes $c$ to $c'=P_wc$. Its intermediate component has fundamental group

$$
\Gamma_{c,w}
=H(F)\cap x_c^v
\bigl(U^{1,v}\cap h_wU^{1,v}h_w^{-1}\bigr)
(x_c^v)^{-1}. \tag{5.10}
$$

At $w$ the compact intersection is an Iwahori subgroup. Density makes $\Gamma_c$ surject onto its finite coset set, and hence

$$
[\Gamma_c:\Gamma_{c,w}]=q_w+1.
$$

Both legs give genuine embeddings of rational groups

$$
i_{0,c}:\Gamma_{c,w}\longrightarrow\Gamma_c,
\qquad
i_{1,c}:\Gamma_{c,w}\longrightarrow\Gamma_{c'}. \tag{5.11}
$$

The first is inclusion. The exact component formula of Books 118 and 124 lets us choose the representatives so that

$$
q_{c,w}x_ch_w=x_{c'}k_{c,w}
$$

for some $q_{c,w}\in G(\mathbf Q)_+$ and $k_{c,w}\in U$; then $i_{1,c}(\delta)=q_{c,w}\delta q_{c,w}^{-1}$. Changing this choice conjugates inside $\Gamma_{c'}$ and hence does not change trivial-coefficient $H^1$. This is the rational transition hidden by the shorthand of conjugating with the local matrix $h_w$.

The transition $q_{c,w}$ is a rational quaternionic commensurator, not an element of an absolute Galois group. There is no natural homomorphism $B^\times(F)\to G_F$, so an attached residual Galois representation cannot be evaluated at $q_{c,w}$. Good-place Frobenius characteristic polynomials specify conjugacy classes, not a multiplicative comparison functor on rational quaternion units. A Galois or patched proof of the localized leg equality would first have to construct such a correctly typed local--global comparison; residual adequacy alone cannot do so.

Sum (5.11) over the stable component set. After using $P_w$ to route the second target back to the corresponding direct-sum factor, define

$$
D_w=i_1^*-i_0^*P_w. \tag{5.12}
$$

Restriction along $i_1$ followed by corestriction along $i_0$ is the Hecke operator. Restriction along $i_0$ followed by corestriction is multiplication by $q_w+1$. Therefore

$$
T_w-(q_w+1)P_w
=\operatorname{cor}_{i_0}\circ D_w. \tag{5.13}
$$

In the trivial-routing block $P_w=1$. Formula (5.13) is the exact abelianization identity needed in Ihara's argument. To see it directly, choose right-coset representatives $a_i$ for $\Gamma_{c,w}\backslash\Gamma_c$ and write

$$
a_i\gamma=\gamma_i a_{\sigma_\gamma(i)},
\qquad \gamma_i\in\Gamma_{c,w}. \tag{5.14}
$$

Then

$$
(T_w\chi)_c(\gamma)
=\sum_i\chi_{c'}(i_{1,c}(\gamma_i)),
\qquad
((q_w+1)P_w\chi)_c(\gamma)
=\sum_i(P_w\chi)_c(i_{0,c}(\gamma_i)). \tag{5.15}
$$

The second equality follows by multiplying (5.14) around every cycle of $\sigma_\gamma$ and abelianizing. Subtraction gives (5.13), without any continuity assumption.

We can now prove the Eisenstein relation on the part whose arithmetic nature is actually controlled.

**Lemma 5.2 (congruence-character invariance).** On the stable component sum, $D_w$ vanishes on $H^1_{\mathrm{cong}}$ for every $w\notin\Sigma$.

**Proof.** Extend a character on the $c$-factor continuously to $K_c^v$. In the compact-open groupoid defined by the Hecke span, the two legs agree away from $w$ after the prescribed component transport and differ at $w$ by conjugation with $h_w$. The rational elements $q_{c,w}$ above merely express those adelic legs in the chosen component representatives.

At the good place $w$, reduction of $K_w=\operatorname{SL}_2(\mathcal O_{F_w})$ has a pro-$p_w$ kernel, which has no nonzero map to the $\ell$-primary group $A$. The abelianization of $\operatorname{SL}_2(k_w)$ is trivial when $|k_w|>3$ and has order $2$ or $3$ for $|k_w|=2$ or $3$. Hence

$$
\operatorname{Hom}_{\mathrm{cont}}(K_w,A)=0
\qquad(\ell\ge7). \tag{5.16}
$$

Because $w\notin\Sigma$, the compact open splits as $K_c^v=K_w\times K_c^{v,w}$. Any homomorphism from this product to the abelian group $A$ is the sum of its restrictions to the two factors, so (5.16) makes the extension factor through $K_c^{v,w}$. After the transport $P_w$, the two Hecke legs have the same projection to $K_c^{v,w}$ and differ only on $K_w$. Their pullbacks therefore agree, so $D_w\chi=0$. $\square$

The proof retains every other local factor. At a quaternion division place $r\nmid\ell$, reduction of a maximal norm-one compact has quotient

$$
k_{r^2}^{\,1}
=\ker\!\left(
N_{k_{r^2}/k_r}:k_{r^2}^{\times}\to k_r^\times
\right), \tag{5.17}
$$

of order $q_r+1$, and its $\ell$-part can contribute a character. A nonmaximal bad-level factor or a coefficient-place factor can also contribute. These factors occur away from $w$ and are fixed pointwise by conjugation at $w$; they are arithmetic Eisenstein characters, not errors to be discarded. No perfection assertion at a coefficient-place or bad-level compact is needed.

**Proposition 5.3 (arithmetic Eisenstein submodule).** On the trivial-routing, trivial-central block, $\mathcal H^1_{\mathrm{cong}}(A)$ is annihilated by $\mathfrak E$. On a stable component union it satisfies (2.2), and on a component or norm-character block $\eta$ it satisfies (2.3).

**Proof.** Lemma 5.2 and (5.13) give $T_w=(q_w+1)$ on the congruence submodule. The central one-coset acts as the declared central and component translation. Every right coset at $w$ has reduced norm $\varpi_w$ modulo units, which gives exactly (2.2)--(2.3). Restriction, conjugation, and corestriction between open compact subgroups preserve continuous characters, so the submodule is stable under the full away-from-$v$ Hecke algebra and its quotient in (5.9) inherits that action. $\square$

The remaining issue has an exact formulation. The following are sufficient conditions for the full character module to be Eisenstein at a fixed good place:

$$
\operatorname{cor}_{i_0}D_w=0
\quad\hbox{on }\mathcal H^1(A), \tag{5.18}
$$

or, more strongly,

$$
(i_1)_*=(P_w)_*(i_0)_*:
\bigoplus_c\Gamma_{c,w}^{\mathrm{ab}}\otimes\mathbf Z_\ell
\longrightarrow
\bigoplus_c\Gamma_c^{\mathrm{ab}}\otimes\mathbf Z_\ell. \tag{5.19}
$$

Condition (5.18) is equivalent to $T_w=(q_w+1)P_w$ by (5.13). Condition (5.19) says that the two abelianized leg maps agree after component routing and implies (5.18). Lemma 5.2 proves the dual equality after restriction to the congruence-continuous character submodule, so every possible failure is carried by $\mathcal H^1_{\mathrm{nc}}(A)$.

Neither the one-edge quotient nor strong approximation proves (5.18) or (5.19) on that quotient. Density only says that each $\Gamma_c$ and the kernel of a finite-index abstract character have specified closures; it does not identify the character with a continuous character of those closures. Thus the precise missing uniform input is an abelian commensurator theorem, not a full congruence-subgroup property:

The logical gap already appears in the elementary dense embedding $\mathbf Z\hookrightarrow\mathbf Z_p$. If $r\ne p$, reduction $\mathbf Z\to\mathbf Z/r\mathbf Z$ is an abstract finite character, but it is not continuous for the topology induced from $\mathbf Z_p$: its kernel $r\mathbf Z$ is dense because $r$ is a unit in $\mathbf Z_p$. Therefore neither density nor approximation of finitely many local multiplication tables can show that an arbitrary finite character is congruence-continuous. In particular, an argument that makes a local error arbitrarily small and then declares its value zero in an unrelated abstract finite quotient has already assumed the desired conclusion.

> For the norm-one $S$-arithmetic component family (5.7), prove (5.18) for every good $w$ and every finite $\ell$-primary coefficient module, or at least prove it on the $\Delta$-invariant noncongruence quotient localized at the chosen non-Eisenstein maximal ideal.

This statement is not supplied by Books 16, 38--39, 118, 122, or 124. Replacing it by the claim that the whole congruence kernel is finite central and $2$-primary would be strictly stronger and would not be a proof from the declared dependencies.

## 6. The geometric Ihara criterion

### 6.1 Complex uniformization and comparison

For the norm-one fine cover of a chosen connected component, complex uniformization gives

$$
\widetilde X_U(\mathbf C)\simeq\Gamma_0\backslash\mathfrak H,
\qquad
\widetilde X_{U_0(v)}(\mathbf C)\simeq\Gamma_e\backslash\mathfrak H, \tag{6.1}
$$

and the routed lower component is $\Gamma_1\backslash\mathfrak H$. Neatness makes the groups torsion-free. The upper half-plane is contractible, so each quotient is a classifying space for its arithmetic group. Hence

$$
H^1(\widetilde X_U(\mathbf C),A)\simeq H^1(\Gamma_0,A),
$$

$$
H^1(\widetilde X_{U_0(v)}(\mathbf C),A)\simeq H^1(\Gamma_e,A). \tag{6.2}
$$

For the original selected component union, apply the compatible finite descent group $\Delta$ of Section 2.1. Since $|\Delta|$ is a unit in $A$, its invariants are exact and

$$
H^1(X_U(\mathbf C),A)
\simeq H^1(\Gamma_0,A)^\Delta,
\qquad
H^1(X_{U_0(v)}(\mathbf C),A)
\simeq H^1(\Gamma_e,A)^\Delta.
$$

For $A=k$, the comparison theorem between singular and finite étale cohomology gives

$$
H^1(X(\mathbf C),k)\simeq
H^1(X_{\overline F},k). \tag{6.3}
$$

The isomorphism is functorial for finite maps, so it respects degeneracy pullback and every algebraic Hecke correspondence. Thus the tree calculation is a geometric cohomology calculation, not merely a calculation on an unrelated group.

### 6.2 The degeneracy map as restriction

Under (6.2), pullback on the norm-one cover along the finite covering induced by $\Gamma_e\subset\Gamma_0$ is restriction $r_0$. For the second degeneracy map, right translation by $h_v$ first identifies the source with the conjugate vertex quotient and then forgets level; its pullback is $r_1$ after the rational component transition. Taking exact $\Delta$-invariants gives the map on the original curve. Therefore

$$
d_k=(r_0,r_1)^\Delta:
\bigl(H^1(\Gamma_0,k)\oplus H^1(\Gamma_1,k)\bigr)^\Delta
\longrightarrow H^1(\Gamma_e,k)^\Delta, \tag{6.4}
$$

up to the harmless sign on the second summand already discussed.

Every away-from-$v$ Hecke correspondence is defined by changing level at a different finite place. It commutes with both inclusions and with the conjugation at $v$. The identifications (6.2)--(6.4) are therefore Hecke equivariant.

### 6.3 The exact kernel and its congruence part

**Theorem 6.1 (exact tree kernel and cokernel).** For every finite quotient $A$ of $\mathcal O$, comparison and the tree give a natural Hecke-equivariant exact sequence

$$
0\longrightarrow H^1(\Gamma^v,A)^\Delta
\longrightarrow H^1(X_U,A)^{\oplus2}
\xrightarrow{d_A}H^1(X_{U_0(v)},A)
\longrightarrow H^2(\Gamma^v,A)^\Delta
\longrightarrow\bigl(H^2(\Gamma_0,A)\oplus H^2(\Gamma_1,A)\bigr)^\Delta. \tag{6.5}
$$

The sign on the second source summand is changed when the geometric old map is written with a sum rather than the cellular difference. In particular,

$$
\ker d_A\simeq H^1(\Gamma^v,A)^\Delta, \tag{6.6}
$$

and

$$
\operatorname{coker}d_A\simeq
\ker\!\left(
H^2(\Gamma^v,A)^\Delta\longrightarrow
\bigl(H^2(\Gamma_0,A)\oplus H^2(\Gamma_1,A)\bigr)^\Delta
\right). \tag{6.7}
$$

**Proof.** In the degree-zero part of (5.4), the map $A\oplus A\to A$ is $(a,b)\mapsto a-b$ and is surjective. Hence the connecting map into $H^1(\Gamma^v,A)$ vanishes and the next arrow is injective. This gives the asserted sequence on the norm-one cover. The order of $\Delta$ is invertible in $A$, so applying $(\ )^\Delta$ preserves its exactness. Sections 6.1--6.2 identify the three stabilizer cohomology groups and their restriction maps with the cohomology of the two lower curves and the Iwahori curve after that descent. Naturality of the cellular resolution gives Hecke equivariance. $\square$

Thus the amalgam does more than bound the kernel: it identifies it. Before descent, a character on $\Gamma^v=\Gamma_0*_{\Gamma_e}\Gamma_1$ is exactly a pair $(\chi_0,\chi_1)$ whose restrictions to $\Gamma_e$ agree. Replacing $\chi_1$ by $-\chi_1$ turns agreement into the relation $r_0\chi_0+r_1(-\chi_1)=0$; the relations on the original curve are exactly the $\Delta$-invariant such pairs. Formula (6.7) records the next obstruction rather than silently declaring the two-map cokernel free.

Under (6.6), the submodule $H^1_{\mathrm{cong}}(\Gamma^v,A)^\Delta$ gives the arithmetic part of the kernel. Proposition 5.3 proves that this submodule is Eisenstein. Exactness of invariants gives

$$
0\longrightarrow H^1_{\mathrm{cong}}(\Gamma^v,A)^\Delta
\longrightarrow\ker d_A
\longrightarrow H^1_{\mathrm{nc}}(\Gamma^v,A)^\Delta
\longrightarrow0. \tag{6.8}
$$

This is the strongest unconditional Eisenstein-kernel statement supplied by the declared sources. Continuous characters of division-place, coefficient-place, and bad-level compact factors occur in the first term. Reduced norm and the component set do not create characters of the fixed norm-one group: they route that first term between connected-component factors through $P_w$, producing the twists (2.2)--(2.3). Ineffective central units are divided out, while the effective norm-squareclass and fine-cover descent is carried by $\Delta$. Since $\ell\nmid|\Delta|$, averaging is exact and $H^i(\Delta,A)=0$ for $i>0$, so no additional degree-one character appears. If $\ell\mid|\Delta|$, the assertion is deliberately excluded. Only the $\Delta$-invariant noncongruence quotient of the norm-one character module remains in the clean range.

For $A=\mathbf Z/\ell^n\mathbf Z$, Kummer theory identifies

$$
H^1(X,A(1))\simeq J_X[\ell^n](\overline F). \tag{6.9}
$$

Consequently the same exact obstruction describes the $\ell$-primary part of the geometric kernel of $J_U\times J_U\to J_{U_0(v)}$. Its congruence-character part is Eisenstein; vanishing of the whole localized kernel requires the condition in the next section.

### 6.4 The residual Ihara criterion

Let $\mathfrak m$ be non-Eisenstein in the sense of Section 2.4. Localizing (6.8) kills its first term and gives

$$
\ker(d_k)_{\mathfrak m}
\simeq \bigl(H^1(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}
\simeq \bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}. \tag{6.10}
$$

The middle isomorphism uses (6.6), and the last uses Proposition 5.3. Hence the following are equivalent:

$$
\begin{array}{c}
(d_k)_{\mathfrak m}\text{ is injective},\\
\bigl(H^1(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}=0,\\
\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}=0.
\end{array} \tag{6.11}
$$

We denote the conditions in (6.11) by

$$
({\rm AIH})_{v,\mathfrak m}
$$

and call them the **abelian Ihara condition** at $\mathfrak m$. This is exactly what remains after the tree, component, center, stabilizer, and congruence-character calculations have been completed. A uniform proof from the hypotheses of Section 2 would amount to the localized form of (5.18), or to another theorem forcing the last group in (6.10) to vanish. No such theorem occurs among the listed dependencies.

Under the abelian Ihara condition, the desired residual map is therefore injective:

$$
\bar d_{\mathfrak m}:
H^1(X_U,k)_{\mathfrak m}^{\oplus2}
\longrightarrow
H^1(X_{U_0(v)},k)_{\mathfrak m}. \tag{6.12}
$$

The condition and conclusion survive finite coefficient extension by faithful flatness. They also assemble over a finite Hecke-stable orbit of connected components: one writes (6.5) for every representative and lets the routing operators $P_w$ permute the summands. A nonstable single component gives a correspondence between different factors, not an endomorphism.

No assumption that $q_v\not\equiv\pm1\pmod\ell$ is involved in (6.11). Those congruences enter only when a later argument separates signed Gram factors. Neatness, or descent through a deck quotient of order prime to $\ell$, remains essential: otherwise stabilizer cohomology adds another term before (6.5).

Constant coefficients are also essential. Formula (5.5) turns $H^1(\Gamma^v,A)$ into ordinary homomorphisms. For a nontrivial local system, one-cocycles are crossed homomorphisms and neither (5.8) nor the arithmetic-character calculation applies without a type-enhanced theorem.

## 7. Integral saturation

From this chapter through Chapter 12, fix a non-Eisenstein maximal ideal $\mathfrak m$ and assume the abelian Ihara condition (6.11). Everything after this sentence is a source-closed consequence of that explicit condition. The condition is repeated in the main theorem so that none of the lattice conclusions is mistaken for an unconditional consequence of strong approximation.

### 7.1 Freeness of curve cohomology

Let $C$ be a smooth proper geometrically connected curve over a characteristic-zero field. Choose an embedding into $\mathbf C$. The compact connected Riemann surface $C(\mathbf C)$ has a CW decomposition with one zero-cell, $2g$ one-cells, and one two-cell whose attaching word is the product of commutators. After abelianization the cellular boundary of the two-cell is zero. Hence

$$
H_1(C(\mathbf C),\mathbf Z)\simeq\mathbf Z^{2g},
\qquad
H^1(C(\mathbf C),\mathbf Z)\simeq\mathbf Z^{2g}. \tag{7.1}
$$

Tensoring with $\mathcal O$ and using comparison gives

$$
H^1(C_{\overline F},\mathcal O)
\simeq\mathcal O^{2g}. \tag{7.2}
$$

The same conclusion follows from the inverse system of finite étale coefficients: $H^1(C,\mathbf Z_\ell)$ is the dual of the free $\mathbf Z_\ell$-Tate module of the Jacobian, with the chosen twist convention. Formula (7.1) also shows directly that reduction is exact:

$$
H^1(C,\mathcal O)/\varpi
\simeq H^1(C,k). \tag{7.3}
$$

Thus both modules $M$ and $N$ in (2.1), and their localizations, are finite free over $\mathcal O$.

### 7.2 From residual injectivity to a primitive image

Consider

$$
d_{\mathfrak m}:M_{\mathfrak m}^{\oplus2}
\longrightarrow N_{\mathfrak m}. \tag{7.4}
$$

By (7.3), its reduction is the map in (6.12). It is injective by the abelian Ihara condition. Lemma 3.1 therefore gives at once:

$$
d_{\mathfrak m}\text{ is injective}, \tag{7.5}
$$

$$
\operatorname{im}d_{\mathfrak m}
\text{ is saturated in }N_{\mathfrak m}. \tag{7.6}
$$

This implication is integral and exact. It does not pass through the fraction field. In particular it remains valid when the determinant of the old Gram matrix is divisible by $\varpi$, which is precisely the level-raising situation.

### 7.3 Torsion-freeness of the old quotient

Define

$$
N^{\mathrm{old}}_{\mathfrak m}
=d(M_{\mathfrak m}^{\oplus2}),
\qquad
Q^{\mathrm{new}}_{\mathfrak m}
=N_{\mathfrak m}/N^{\mathrm{old}}_{\mathfrak m}. \tag{7.7}
$$

**Theorem 7.1 (conditional saturated degeneracy theorem).** Under the abelian Ihara condition, the sequence

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q^{\mathrm{new}}_{\mathfrak m}
\longrightarrow0 \tag{7.8}
$$

is exact and $Q^{\mathrm{new}}_{\mathfrak m}$ is finite free over $\mathcal O$.

**Proof.** Exactness on the left and saturation are (7.5)--(7.6). The quotient is finite and torsion-free, hence free over the DVR. $\square$

The notation “new” in (7.7) means the integral quotient by the geometrically proved old image. Characteristic-zero local newvector theory may later identify its generic fiber with the representation-theoretic new space. That identification is not used to establish its freeness.

Freeness is stable under every safe scalar operation used afterward. For a finite flat coefficient extension $\mathcal O\to\mathcal O'$, tensoring (7.8) remains exact and the quotient is $Q^{\mathrm{new}}\otimes\mathcal O'$. For reduction modulo $\varpi^n$, primitivity gives

$$
0\to(M/\varpi^nM)_{\mathfrak m}^{\oplus2}
\xrightarrow{d}
(N/\varpi^nN)_{\mathfrak m}
\to Q^{\mathrm{new}}_{\mathfrak m}/\varpi^n
\to0. \tag{7.9}
$$

Indeed $\operatorname{Tor}_1^{\mathcal O}(Q,\mathcal O/\varpi^n)=0$ because $Q$ is free. Thus there is no hidden loss of exactness at finite coefficient precision. This compatibility is stronger than injectivity modulo $\varpi$ alone and is the form needed whenever congruences are followed through increasing powers of the coefficient uniformizer.

Conversely, exactness for every $n$ detects saturation. If $N/d(M^2)$ had a nonzero element killed by $\varpi^a$, tensoring with $\mathcal O/\varpi^a$ would create a nonzero $\operatorname{Tor}_1$ term and a kernel on the left of (7.9). Thus the following are equivalent in the present finite free setting:

$$
\begin{array}{c}
d\bmod\varpi\text{ injective},\\
d\bmod\varpi^n\text{ injective for every }n,\\
d(M^2)\text{ saturated},\\
Q\text{ torsion-free}.
\end{array} \tag{7.10}
$$

The equivalence is special to a one-dimensional coefficient ring. Over a higher-dimensional local ring, a quotient can be torsion-free without being projective, and reduction modulo one parameter need not detect primitivity along another. The present theorem establishes the DVR statement at fixed coefficient level; any later variation of deformation parameters must preserve it by a separate flatness argument.

If $e$ is an idempotent in the **integral** localized Hecke algebra, applying $e$ to (7.8) preserves exactness and freeness because $eM$ is a direct summand. If an idempotent exists only in $\mathbb T\otimes E$, its denominator may meet $\varpi$, and its intersection with $N$ can be nonsaturated. Theorem 7.1 should therefore be applied to the full Iwahori lattice before a rational branch projector is introduced.

### 7.4 What fails without localization

The kernel before localization is not asserted to vanish. Theorem 6.1 identifies it with the $\Delta$-invariant part of the full norm-one arithmetic character module. Its congruence part is Eisenstein, but a $\Delta$-invariant noncongruence character can survive even at a non-Eisenstein localization unless (6.11) is known. Such a class makes the residual map noninjective and prevents the saturation conclusion.

Nor can rational injectivity replace (6.12). The map

$$
R\xrightarrow{\ \pi\ }R
$$

is injective over $R$ and over $K$, but its reduction is zero and its cokernel is $R/\pi R$. The same elementary divisor can occur in a degeneracy lattice if one uses only a characteristic-zero old decomposition.

Finally, invertibility of the Gram determinant is sufficient for the old image to split orthogonally, but it is not necessary for saturation. At a level-raising congruence the Gram determinant is deliberately a nonunit. Under (6.11), the old image is nevertheless primitive by Theorem 7.1; what fails is orthogonal splitting, and that failure is the congruence with the new lattice.

## 8. The Iwahori integral model

### 8.1 The incidence moduli problem

Under the abelian Ihara condition, the tree proves injectivity on the generic curve. We now turn to the integral geometry that controls monodromy and components.

Let $R_v$ be the henselian valuation ring at the changing place. The hyperspecial PEL curve $\mathscr X/R_v$ is smooth and proper under the datum of Section 2.2. The Iwahori curve $\mathscr C/R_v$ records two PEL abelian schemes and an isogeny

$$
A_0\longrightarrow A_1 \tag{8.1}
$$

whose kernel has the finite locally free type prescribed by the adjacent lattice pair. Its prime-to-$v$ level is transported through the isogeny, both Lie algebras satisfy the determinant condition, and the polarizations have the prescribed similitude.

On the active rank-two de Rham factor, the local model asks for lines $L_i\subset U_i$ compatible with

$$
U_0\xrightarrow{\alpha}U_1,
\qquad
U_1\xrightarrow{\beta}U_0,
\qquad
\beta\alpha=\alpha\beta=\pi_v. \tag{8.2}
$$

In bases for which

$$
\alpha=\begin{pmatrix}1&0\\0&\pi_v\end{pmatrix},
\qquad
\beta=\begin{pmatrix}\pi_v&0\\0&1\end{pmatrix}, \tag{8.3}
$$

the exceptional affine chart writes

$$
L_0=R_v(x,1),
\qquad
L_1=R_v(1,y).
$$

Compatibility is the single equation

$$
xy=\pi_v. \tag{8.4}
$$

The established local-model diagram transfers this equation smoothly to the PEL moduli curve. Projectivity follows from the proper PEL problem, and no compactification is needed because the quaternion algebra is division.

### 8.2 The nodal chart and regularity

**Theorem 8.1 (strict semistable Iwahori model).** The fine Iwahori model $\mathscr C/R_v$ is regular, projective, and flat. Its geometric special fiber is reduced and nodal, and every completed strict henselian local ring at a node is

$$
R_v^{\mathrm{sh}}[[x,y]]/(xy-\pi_v). \tag{8.5}
$$

**Proof.** The PEL representability and properness argument gives a projective flat model carrying the universal isogeny. The framed local-model diagram is smooth on both sides. Hence the completed strict henselian local ring of the moduli problem differs from that of the incidence model only by formally smooth variables. Both have relative dimension one, so no additional singular variable remains. Formula (8.4) gives (8.5).

At the closed point of (8.5), the maximal ideal is generated by $x$ and $y$ because $\pi_v=xy$. The ring has dimension two and embedding dimension two, so it is regular. Its special fiber is $xy=0$, the union of two smooth transverse branches, each with multiplicity one. Away from the crossing stratum the incidence model is smooth, and smooth descent through the local-model diagram proves regularity there. $\square$

Let

$$
Y=\mathscr C_{\bar k_v}=\bigcup_{a\in V}Y_a
$$

and let $\Gamma$ be its geometric dual graph. A local branch label $0$ or $1$ does not by itself determine a global irreducible component. We therefore retain every geometric component as a vertex and every node as an edge, including multiple edges and loops.

### 8.3 The two degeneracy maps on the special fiber

Both generic degeneracy maps extend to finite morphisms

$$
\pi_0,\pi_1:\mathscr C\longrightarrow\mathscr X. \tag{8.6}
$$

The first forgets the subgroup in (8.1). The second takes the quotient and transports the PEL datum. Finite local freeness follows from the Cohen--Macaulay criterion: $\mathscr C$ is regular, hence Cohen--Macaulay; $\mathscr X$ is regular; the maps are finite with equidimensional fibers; and the generic degree is $q_v+1$. Thus the source local ring is maximal Cohen--Macaulay over the target regular local ring and therefore free.

The special restrictions can be read on the ordinary locus. The active height-two group has a connected rank-$q_v$ direction and an étale rank-$q_v$ direction. Quotient by the connected direction is relative Frobenius; polarization identifies the other direction with its dual. Taking closures gives the two branches of (8.5).

**Proposition 8.2 (branch table).** After the canonical Frobenius-twist identifications of the normalized branches with the hyperspecial special curve, the restrictions of the degeneracy maps are

$$
\begin{array}{c|cc}
&\pi_0&\pi_1\\ \hline
Y^{(0)}&1&F\\
Y^{(1)}&F&1
\end{array} \tag{8.7}
$$

in the trivial-central block. Here $F$ is relative $q_v$-power Frobenius. With a nontrivial central convention, one off-diagonal entry is followed by the corresponding scalar translation.

**Proof.** On the branch where the chosen kernel is connected, forgetting it retains $A_0$, while quotienting gives $A_0^{(q_v)}$ by relative Frobenius. This is the first row. On the branch where the dual direction is connected, the quotient datum is the untwisted endpoint and the forgotten source is its Frobenius twist, giving the second row. These identifications hold on the dense ordinary locus.

Each branch is reduced at its generic point by (8.5), and each map there has the displayed generic degree, $1$ or $q_v$. Two finite maps between reduced proper curves that agree on a dense open agree everywhere. The PEL level transport fixes the central factor; in the trivial-central block it is the identity. $\square$

The degree check is

$$
\deg\pi_i=1+q_v.
$$

Although Frobenius is bijective on geometric points, it has scheme-theoretic degree $q_v$. This is why counting reduced fibers would give the wrong correspondence.

The branch table also explains why it cannot prove Ihara injectivity by itself. On normalized-component cohomology, the two old classes $(x,y)$ restrict through the matrix

$$
\begin{pmatrix}1&F^*\\F^*&1\end{pmatrix}. \tag{8.8}
$$

At a level-raising congruence this matrix can have a residual kernel. That does not mean the generic old map has a kernel. A class vanishing on the normalizations can survive in the gluing cohomology $H^1(\Gamma,k)$ or in the vanishing-cycle quotient. The tree argument proves that the complete generic class is nonzero; the semistable filtration identifies where the missing information lies. Looking only at the two normalized components discards the very graph class which rescues injectivity.

Nodes occur where the connected and étale descriptions meet. Let $\Sigma$ be the finite superspecial incidence set. On one reduced branch $\pi_0$ is generically separable of degree one and $\pi_1$ is radicial of degree $q_v$; on the other branch the roles reverse. These are scheme-theoretic degrees, so their sums give

$$
\deg(\pi_0)=\deg(\pi_1)=q_v+1. \tag{8.9}
$$

This degree calculation uses the global branch normalizations and their Frobenius restrictions, not an unproved formula for a target parameter in the nodal completed ring. The Atkin--Lehner involution exchanges the two branches and the two rows of (8.7), providing the corresponding orientation check.

### 8.4 Fine covers and coarse descent

The proof has been carried out at neat level. Suppose a finite group $\Delta$ acts on the fine model and the desired curve is its quotient. The universal isogeny and both degeneracy maps are $\Delta$-equivariant. If $|\Delta|$ is invertible in $\mathcal O$, the averaging idempotent

$$
e_\Delta=|\Delta|^{-1}\sum_{\delta\in\Delta}\delta \tag{8.10}
$$

makes invariants an exact functor. The tree sequence, cohomology, old map, and saturation theorem descend by applying $e_\Delta$.

At fixed points, the coarse special fiber can have quotient singularities even when the fine model is semistable. Component and monodromy calculations are then performed equivariantly on the fine graph before invariants are taken. Quotienting the unoriented graph first can lose a branch reversal and its sign.

If $\ell\mid|\Delta|$, (8.10) is unavailable. The invariant functor can have higher cohomology, and a stabilizer character can appear in the Ihara kernel. The clean conditional package does not hide this failure; it requires a neat level or prime-to-$\ell$ descent in addition to (6.11).

From Chapter 9 onward, $\Gamma$ denotes the geometric dual graph of this common fine model. When the curve of interest is a tame quotient, every graph module, filtration, and branch map means its exact $\Delta$-invariant descent. Since $|\Delta|$ is a unit in $\mathcal O$, invariants and coinvariants are identified by averaging; the graph pairing, its adjunction, and its discriminant sequence descend after the corresponding unit normalization. This does not assert that the pairing is unimodular, and we do not assert that the coarse quotient model itself is regular semistable.

## 9. Nodal cohomology and monodromy

### 9.1 Normalization of a nodal curve

Let $A$ be $\mathbf Z_\ell$, $\mathcal O$, or a finite quotient of $\mathcal O$. Write

$$
\nu:\widetilde Y=\coprod_{a\in V}\widetilde Y_a\longrightarrow Y
$$

for normalization, and let $\Sigma$ be the geometric node set. Choose an orientation on each edge. There is an exact sequence of étale sheaves

$$
0\longrightarrow A_Y
\longrightarrow\nu_*A_{\widetilde Y}
\xrightarrow{\partial^*}A_\Sigma
\longrightarrow0, \tag{9.1}
$$

where $\partial^*$ takes the difference of the two branch values. Exactness is local: at a node, a locally constant function descends precisely when its two branch values agree.

Taking cohomology gives

$$
A^V\xrightarrow{\partial^*}A^E
\longrightarrow H^1(Y,A)
\longrightarrow\bigoplus_{a\in V}H^1(\widetilde Y_a,A)
\longrightarrow0. \tag{9.2}
$$

The cokernel of the first map is cellular $H^1(\Gamma,A)$. Thus:

**Proposition 9.1 (nodal cohomology).** There is a canonical exact sequence

$$
0\longrightarrow H^1(\Gamma,A)
\longrightarrow H^1(Y,A)
\longrightarrow\bigoplus_aH^1(\widetilde Y_a,A)
\longrightarrow0. \tag{9.3}
$$

**Proof.** Only surjectivity on the right remains to be explained. The sheaf $A_\Sigma$ is supported on finitely many geometric points, so $H^1(Y,A_\Sigma)=0$. Exactness of the long cohomology sequence of (9.1) gives the result. $\square$

The sequence splits after choosing paths and branch trivializations, but not canonically. The graph term records gluing around cycles; the normalized-component term records ordinary curve cohomology.

### 9.2 The graph exact sequence

Choose orientations and write

$$
C_1(\Gamma,A)\xrightarrow{\partial}C_0(\Gamma,A).
$$

For a connected graph,

$$
0\to H_1(\Gamma,A)\to C_1(\Gamma,A)
\xrightarrow{\partial}C_0(\Gamma,A)
\xrightarrow{\epsilon}A\to0. \tag{9.4}
$$

The incidence matrix is totally unimodular: every square minor is $0$, $1$, or $-1$. This follows by induction on the number of columns. A submatrix with a column containing at most one nonzero entry expands along that column; if every column contains two nonzero entries, the row sum is zero and the determinant vanishes. Consequently the image and kernel in (9.4) are saturated over $\mathbf Z$, and every graph group in (9.3)--(9.4) is free over $A$.

This small integral fact is important. The incidence sequence itself creates no $\ell$-torsion. The finite group appears only when the positive edge-length pairing embeds the cycle lattice in its dual.

### 9.3 Nearby cycles and the integral filtration

Let $C=\mathscr C_{\overline K_v}$. For a strict semistable curve, the local nearby-cycle complex at a node has $A$ in degree zero and $A(-1)$ in degree one. Gluing these local complexes through the incidence map gives the exact specialization sequence

$$
0\longrightarrow H^1(Y,A)
\xrightarrow{\operatorname{sp}}
H^1(C,A)
\xrightarrow{\operatorname{res}}
H_1(\Gamma,A)(-1)
\longrightarrow0. \tag{9.5}
$$

For completeness, the right map can be described without derived terminology. On an annulus $xy=\pi_v$ choose the Kummer class of $x$. A generic cohomology class has a residue on each oriented annulus. Reversing orientation changes its sign. The sum of residues at the branches of every normalized component is zero, so the residue vector is a graph cycle. Conversely, prescribe a cycle of residues. On each normalized component the total residue is zero, so the standard residue sequence for a smooth proper curve with punctures produces a class; the cycle condition lets the local classes glue. This proves surjectivity. A class with zero annular residues extends across every node and therefore comes from $H^1(Y,A)$, proving exactness in the middle. Since the residue and incidence modules are free, the argument works integrally.

Combining (9.3) and (9.5) gives a three-step filtration

$$
0\subset W_0\subset W_1\subset W_2=H^1(C,A), \tag{9.6}
$$

with

$$
W_0=H^1(\Gamma,A),
$$

$$
W_1/W_0=\bigoplus_aH^1(\widetilde Y_a,A),
$$

$$
W_2/W_1=H_1(\Gamma,A)(-1). \tag{9.7}
$$

Every term is free. The filtration is stable under the away-from-$v$ Hecke algebra and the residue Galois action.

We spell out the residue construction in a little more detail because it is the integral point at which torsion could otherwise enter. Remove the nodes from every normalized component and call the result $Y_a^\circ$. The localization sequence is

$$
0\to H^1(\widetilde Y_a,A)
\to H^1(Y_a^\circ,A)
\xrightarrow{\operatorname{res}}
\bigoplus_{b\in B_a}A(-1)
\xrightarrow{\sum}A(-1)\to0, \tag{9.8}
$$

where $B_a$ is the set of branches on $\widetilde Y_a$. The last map is the sum of residues. Its kernel is free and is generated by differences of branch basis vectors. For a global oriented edge, the two branch residues must be opposite. Therefore a global residue assignment is an element $(r_e)\in A^E$ satisfying

$$
\sum_{t(e)=a}r_e-\sum_{o(e)=a}r_e=0
$$

at every vertex $a$. This is exactly $\partial r=0$, so the residue module is $H_1(\Gamma,A)(-1)$.

Choose local classes realizing these residues by exactness of (9.8). On the overlap annuli, two choices differ by a class extending over the node. Adjusting by component classes glues them. If a multiple $\varpi z$ glues, the incidence matrices in the adjustment equations are totally unimodular, so $z$ glues as well. Hence the image in (9.5) is saturated. This gives a direct integral proof of the freeness asserted after (9.7), independent of a rational degeneration argument.

The ranks provide a useful audit. If $g_a$ is the genus of $\widetilde Y_a$ and $b=b_1(\Gamma)$, then

$$
\operatorname{rank}W_0=b,
$$

$$
\operatorname{rank}(W_1/W_0)=2\sum_ag_a,
$$

$$
\operatorname{rank}(W_2/W_1)=b.
$$

Their sum is

$$
2\sum_ag_a+2b=2g(C), \tag{9.9}
$$

because the arithmetic genus of the special fiber is $\sum g_a+b$. Thus no cohomology rank is missing from the filtration.

### 9.4 The monodromy pairing

Give each geometric edge its thickness $n_e$. For the model of Theorem 8.1, $n_e=1$; after ramified base change it need not be. Define

$$
q_\Gamma(a,b)=\sum_{e}n_ea_eb_e,
\qquad a,b\in H_1(\Gamma,\mathbf Z). \tag{9.10}
$$

This positive definite pairing induces

$$
q_\Gamma:H_1(\Gamma,A)
\longrightarrow H_1(\Gamma,A)^\vee. \tag{9.11}
$$

Cellular duality identifies

$$
H_1(\Gamma,A)^\vee=H^1(\Gamma,A). \tag{9.12}
$$

The logarithm of tame inertia on (9.6) is zero on $W_1$ and factors as

$$
H^1(C,A)\twoheadrightarrow
H_1(\Gamma,A)(-1)
\xrightarrow{q_\Gamma}
H^1(\Gamma,A)(-1)
\hookrightarrow H^1(C,A)(-1). \tag{9.13}
$$

**Proof of the factorization.** At a node $xy=\pi_v^{n_e}$, a tame loop changes a branch Kummer logarithm by $n_e$ times the tame character. A class with residue $a_e$ therefore acquires the graph cocycle whose pairing with a second residue vector $b$ is $n_ea_eb_e$. Summing over nodes gives (9.10). Classes extending across the special fiber have zero residues, so monodromy kills $W_1$. This proves (9.13). $\square$

The rank of monodromy is $b_1(\Gamma)$ after tensoring with $E$. Integrally, its cokernel retains the edge lengths and is the component group studied next.

Three elementary graphs illustrate the distinction.

If $\Gamma$ is a tree, then $H_1(\Gamma)=0$. There is no torus, no monodromy, and no component group, even though the special curve may be reducible.

If $\Gamma$ has one vertex and one loop of length $n$, then

$$
q_\Gamma=[n],
\qquad
\Phi\simeq\mathbf Z/n\mathbf Z. \tag{9.14}
$$

At $n=1$ monodromy has rank one but its integral pairing is unimodular, so the component group is zero. Nonzero monodromy and nonzero components are different properties.

If two vertices are joined by $m$ unit edges, the cycle lattice has basis $c_i=e_i-e_m$ for $1\le i<m$. Its Gram matrix is

$$
Q_m=
\begin{pmatrix}
2&1&\cdots&1\\
1&2&\cdots&1\\
\vdots&\vdots&\ddots&\vdots\\
1&1&\cdots&2
\end{pmatrix}. \tag{9.15}
$$

Subtract the first row from every other row and then the first column from every other column. Smith reduction gives

$$
\operatorname{SNF}(Q_m)=
\operatorname{diag}(1,\ldots,1,m). \tag{9.16}
$$

Thus monodromy rank is $m-1$, while the component group is cyclic of order $m$.

## 10. Component groups and degeneracy maps

### 10.1 The discriminant presentation

Let $\mathcal J$ be the Néron model of the Iwahori-level Jacobian $J_C$. The identity component of its geometric special fiber fits into

$$
0\longrightarrow T_\Gamma
\longrightarrow\mathcal J_{\bar k_v}^0
\longrightarrow\prod_aJ(\widetilde Y_a)
\longrightarrow0, \tag{10.1}
$$

where

$$
X^*(T_\Gamma)=H_1(\Gamma,\mathbf Z). \tag{10.2}
$$

The geometric component group has the canonical presentation

$$
0\longrightarrow H_1(\Gamma,\mathbf Z)
\xrightarrow{q_\Gamma}
H_1(\Gamma,\mathbf Z)^\vee
\longrightarrow\Phi_C(\bar k_v)
\longrightarrow0. \tag{10.3}
$$

For unit thickness this is equivalently the critical group

$$
\operatorname{Div}^0(\Gamma)/\Delta\mathbf Z^V. \tag{10.4}
$$

The proof is the separated Picard calculation: vertical divisors change multidegrees by the graph Laplacian, while normalization identifies the torus character group with graph cycles. Resolving a thick node subdivides its edge and turns the unit pairing into (9.10). These are exactly the hypotheses established for $\mathscr C$.

Tensoring (10.3) with $\mathbf Z_\ell$ gives

$$
\Phi_C(\bar k_v)[\ell^\infty]
\simeq
\operatorname{coker}\left(
q_\Gamma:X_\Gamma\otimes\mathbf Z_\ell
\to X_\Gamma^\vee\otimes\mathbf Z_\ell
\right). \tag{10.5}
$$

Thus the integral defect of monodromy in (9.13) and the $\ell$-primary component group are the same finite module.

For a regular model, (10.4) gives an equivalent vertex calculation. If two components meet in $m$ geometric points, a degree-zero vertex divisor is $a(Y_0-Y_1)$ and the Laplacian sends $(r,s)$ to

$$
m(r-s)(Y_0-Y_1).
$$

The quotient is $\mathbf Z/m\mathbf Z$, agreeing with (9.16). If the closed nodes have residue degrees $f_1,\ldots,f_t$, the intersection number over the ground residue field is $\sum f_i$, but the geometric graph has $\sum f_i$ edges with Frobenius permutation. The integer gives the geometric order; it does not determine the rational fixed subgroup.

For weighted parallel edges of lengths $n_1,\ldots,n_m$, the cycle basis $c_i=e_i-e_m$ has matrix

$$
Q_{ij}=
\begin{cases}
n_i+n_m,&i=j,\\
n_m,&i\ne j.
\end{cases} \tag{10.5a}
$$

Expansion after subtracting one row shows

$$
\det Q=
\sum_{j=1}^{m}\prod_{i\ne j}n_i. \tag{10.5b}
$$

The determinant gives the order but not the invariant factors. If $m=3$ and all $n_i=2$, then

$$
Q=\begin{pmatrix}4&2\\2&4\end{pmatrix},
$$

whose Smith form is $\operatorname{diag}(2,6)$. The component group is $\mathbf Z/2\mathbf Z\oplus\mathbf Z/6\mathbf Z$, not cyclic of order twelve. This is why component control must retain the entire lattice map rather than only its determinant.

### 10.2 Functoriality and adjunction

An away-from-$v$ Hecke correspondence extends finite étale over the parahoric model at fine level. It permutes components and nodes with their local degrees and hence induces pullback and pushforward on $X_\Gamma$. These maps are adjoint:

$$
q_\Gamma(f^*a,b)=q_\Gamma(a,f_*b). \tag{10.6}
$$

For a two-legged correspondence, compose pullback on the source leg with pushforward on the target leg. Its transpose gives the adjoint graph map. Passing to the cokernel in (10.3) produces the action on $\Phi_C$ and the perfect discriminant pairing

$$
\Phi_C\times\Phi_C\longrightarrow\mathbf Q/\mathbf Z. \tag{10.7}
$$

All maps are equivariant for the signed residue Galois action. If Frobenius reverses an oriented edge, it acts by $-1$ on that edge coordinate. This sign must be retained before taking invariants.

The degeneracy maps themselves go from the semistable curve to the smooth hyperspecial curve. Their pullbacks on Jacobians extend uniquely to Néron models by the integral correspondence theorem. Since the hyperspecial Jacobian has good reduction, its component group is zero. The old homomorphism therefore enters the identity component of $\mathcal J$.

### 10.3 Why old classes have no toric part

The last assertion can be sharpened.

**Lemma 10.1 (proper source versus graph torus).** Let $\mathcal A/R_v$ be an abelian scheme and $u:\mathcal A\to\mathcal J$ a homomorphism to the Néron model of a semistable Jacobian. On prime-to-$v$ cohomology, the image of the generic fiber lies in $W_1$ and has zero intersection with $W_0$. Equivalently, it has no top residue class and no nonzero class supported in the graph-torus lattice.

**Proof.** The image $H$ of the proper connected group $\mathcal A_{\bar k_v}$ in the separated group $\mathcal J_{\bar k_v}^0$ is proper and connected. Its maximal connected affine subgroup is trivial, so $H$ is an abelian variety. Its intersection with the torus $T_\Gamma$ is finite. A finite group scheme has bounded exponent and therefore contributes nothing to the inverse system of prime-to-$v$ Tate modules. Functoriality of the semiabelian filtration consequently makes the map on the top torus cocharacter lattice zero; on cohomology this says that the image lies in $W_1$.

For the intersection with $W_0$, tensor with the characteristic-zero coefficient field. The source has good reduction, so geometric Frobenius on its first cohomology is pure of weight $1$. The graph term $W_0=H^1(\Gamma,\mathcal O)$ is pure of weight $0$, with the signed finite permutation action on edges and vertices. A Frobenius-equivariant map between these two spaces is zero because their eigenvalues have different complex absolute values. The integral modules are torsion-free, so vanishing after tensoring with the coefficient field gives zero intersection integrally. $\square$

Apply the lemma to the single combined homomorphism

$$
\delta:J_U\times J_U\longrightarrow J_C,
\qquad (x,y)\longmapsto\pi_0^*x+\pi_1^*y.
$$

Its source is again an abelian scheme at $v$, so the lemma proves directly that the **sum** of the two old images lies in the normalized-component layer and has zero intersection with $W_0$. This conclusion is not inferred separately from the two summands: two submodules can each meet $W_0$ trivially while their sum meets it nontrivially. The combined proper-source argument is the geometric reason graph monodromy is genuinely new; it cannot be supplied by good-reduction old classes.

### 10.4 The localized component-control theorem

Set

$$
R=\mathcal O,\qquad
A=N^{\mathrm{old}}_{\mathfrak m},\qquad
Q=N_{\mathfrak m}/A,
$$

and localize the filtration (9.6). Write

$$
X=H_1(\Gamma,R)_{\mathfrak m},
\qquad
X^\vee=H^1(\Gamma,R)_{\mathfrak m},
\qquad
H_{\mathrm{nor}}=(W_1/W_0)_{\mathfrak m}. \tag{10.8}
$$

Lemma 10.1 gives $A\subset W_1$ and $A\cap W_0=0$. It does **not** imply that $A+W_0$ is saturated. The elementary counterexample $W_0=Re_1$ and $A=R(e_1+\varpi e_2)$ inside $R^2$ shows why an index calculation is indispensable.

Projecting the old map to normalized-component cohomology defines the branch map

$$
B_v:M_{\mathfrak m}^{\oplus2}\longrightarrow H_{\mathrm{nor}}.
\tag{10.9}
$$

Under smooth proper base change and the two branch identifications of Proposition 8.2, it is

$$
B_v=
\begin{pmatrix}
1&F_v^*\\
F_v^*&1
\end{pmatrix}. \tag{10.10}
$$

Define the branch-correction module

$$
\mathcal C_{\mathrm{br},v}
=\operatorname{coker}(B_v). \tag{10.11}
$$

It is an explicit module, not an unspecified index; Theorem 10.2 proves that it is finite under the abelian Ihara condition. Block row and column operations with unit determinant give

$$
\begin{pmatrix}1&0\\-F_v^*&1\end{pmatrix}
B_v
\begin{pmatrix}1&-F_v^*\\0&1\end{pmatrix}
=
\begin{pmatrix}1&0\\0&1-(F_v^*)^2\end{pmatrix}. \tag{10.12}
$$

Consequently

$$
\mathcal C_{\mathrm{br},v}
\simeq
\operatorname{coker}\!\left(
1-(F_v^*)^2:M_{\mathfrak m}\to M_{\mathfrak m}
\right), \tag{10.13}
$$

and its elementary divisors are the nonunit entries in the Smith form of $1-(F_v^*)^2$. With a nontrivial central branch transport, the same calculation uses the corresponding product of the two off-diagonal maps rather than silently setting that scalar to one.

**Theorem 10.2 (conditional component and branch control).** Assume the abelian Ihara condition. The module $Q$ is finite free. Put

$$
L_0=(W_1)_{\mathfrak m}/A\subset Q.
$$

Then the four relevant saturation statements are

$$
W_0=X^\vee\text{ is saturated in }N_{\mathfrak m},
\qquad
A\text{ is saturated in }N_{\mathfrak m}, \tag{10.13a}
$$

$$
(A+W_0)^{\mathrm{sat},N_{\mathfrak m}}=(W_1)_{\mathfrak m},
\qquad
\bigl(\operatorname{im}(W_0\to Q)\bigr)^{\mathrm{sat},Q}=L_0. \tag{10.13b}
$$

In particular, $L_0$ is a saturated free submodule of $Q$, and there are canonical Hecke- and Galois-equivariant exact sequences

$$
0\longrightarrow X^\vee
\longrightarrow L_0
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0, \tag{10.14}
$$

$$
0\longrightarrow L_0
\longrightarrow Q
\longrightarrow X(-1)
\longrightarrow0. \tag{10.15}
$$

After cancelling the common Tate twist, monodromy from the top quotient to the saturated bottom lattice is the composite

$$
X\xrightarrow{q_\Gamma}X^\vee\longrightarrow L_0. \tag{10.16}
$$

Its cokernel sits in the canonical exact sequence

$$
0\longrightarrow
\Phi_C(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}R
\longrightarrow
\operatorname{coker}(N_Q:X\to L_0)
\longrightarrow
\mathcal C_{\mathrm{br},v}
\longrightarrow0. \tag{10.17}
$$

In particular, $X^\vee$ is a primitive bottom graph lattice in $Q$ if and only if $\mathcal C_{\mathrm{br},v}=0$. Without that additional unimodularity condition, the saturated bottom lattice is $L_0$, and the finite branch correction must be retained.

**Proof.** The old map is injective and its image $A$ is saturated in $N_{\mathfrak m}$ by Theorem 7.1, so $Q$ is free. If $B_v(x)=0$, then $d(x)$ lies in $A\cap W_0$, which is zero by Lemma 10.1. Injectivity of $d$ gives $x=0$. The normalization consists, with the component routing fixed in Section 2.1, of the two lower-level branch copies. Hence

$$
\operatorname{rank}_R H_{\mathrm{nor}}
=\operatorname{rank}_R M_{\mathfrak m}^{\oplus2}.
$$

Thus $B_v$ is an injection of equal-rank free modules and (10.11) is finite. Formula (10.12) proves the Smith presentation (10.13).

The two exact sequences in the semistable filtration have free quotients:

$$
0\to W_0\to W_1\to H_{\mathrm{nor}}\to0,
\qquad
0\to W_1\to N_{\mathfrak m}\to X(-1)\to0.
$$

Consequently $W_0$ is saturated in $W_1$, $W_1$ is saturated in $N_{\mathfrak m}$, and transitivity through torsion-free quotients makes $W_0$ saturated in $N_{\mathfrak m}$. This proves the first assertion of (10.13a); the second is Theorem 7.1. These two individual primitivity assertions do not imply that their sum is primitive.

Projection $W_1\to W_1/W_0$ identifies

$$
W_1/(A+W_0)\simeq\operatorname{coker}(B_v)
=\mathcal C_{\mathrm{br},v}. \tag{10.18}
$$

Because $A\cap W_0=0$, the image of $W_0$ in $W_1/A=L_0$ is $X^\vee$, and (10.18) gives (10.14). Moreover

$$
Q/L_0\simeq N_{\mathfrak m}/(W_1)_{\mathfrak m}
\simeq X(-1),
$$

which is free; hence $L_0$ is saturated in $Q$ and (10.15) follows. Equivalently,

$$
(A+W_0)^{\mathrm{sat}}=(W_1)_{\mathfrak m},
\qquad
(A+W_0)^{\mathrm{sat}}/(A+W_0)
\simeq\mathcal C_{\mathrm{br},v}. \tag{10.19}
$$

Here the saturation in (10.19) may be taken in $W_1$ or in $N_{\mathfrak m}$. Indeed, the finite equal-rank cokernel in (10.18) shows that every element of $W_1$ enters the saturation of $A+W_0$, while the torsion-free quotient $N_{\mathfrak m}/W_1$ shows that no element outside $W_1$ can enter it. Passing to $Q=N_{\mathfrak m}/A$ carries $A+W_0$ to the graph copy and $W_1$ to $L_0$, proving (10.13b). Thus the graph copy is primitive in the ambient lattice $N_{\mathfrak m}$ but need not remain primitive after quotienting by the old lattice; its exact saturation there is $L_0$.

Functoriality gives $N_{\mathrm{mon}}d=0$. Formula (9.13) therefore descends to $Q$, kills $L_0$, and induces (10.16) on the top quotient. Taking cokernels of

$$
X\xrightarrow{q_\Gamma}X^\vee\longrightarrow L_0
$$

and using (10.14) gives (10.17), because (10.5) identifies $\operatorname{coker}(q_\Gamma)$ with the localized geometric component group. This also proves every asserted equivariance. $\square$

The correction $\mathcal C_{\mathrm{br},v}$ can be nonzero precisely in the congruence range. For example, an eigenvalue $F_v^*\equiv\varepsilon$ modulo $\varpi$ makes $1-(F_v^*)^2$ singular and corresponds, through $T_v=F_v^*+q_v(F_v^*)^{-1}$, to the level-raising congruence $T_v\equiv\varepsilon(q_v+1)$. Thus saturation of the full generic old image does not force the graph bottom to remain primitive after quotienting. Under the abelian Ihara condition, $Q$ is torsion-free, the ambient component module is exactly $\operatorname{coker}(q_\Gamma)$, and the monodromy cokernel for the saturated quotient is the extension (10.17). Without that condition, the ambient graph and branch calculations remain valid, but they apply to the quotient by the actual old image, which may have coefficient torsion.

Consider explicitly the frequent case in which $Y=Y_0\cup Y_1$ and the two components meet at $m$ unit nodes. Let an away-from-$v$ self-correspondence act on vertex divisors through

$$
A_T=\begin{pmatrix}a&b\\b&a\end{pmatrix}. \tag{10.20}
$$

The row sum $a+b$ is the degree on the total fiber. On the degree-zero generator $Y_0-Y_1$, however,

$$
A_T(Y_0-Y_1)=(a-b)(Y_0-Y_1). \tag{10.21}
$$

Since $\Phi\simeq\mathbf Z/m\mathbf Z$, the component action is multiplication by $a-b$ modulo $m$. Two correspondences with the same degree can therefore have different component actions. Total degree cannot replace the graph calculation.

The involution exchanging the two components acts by $-1$ on $Y_0-Y_1$ and hence by $-1$ on $\Phi$. On the cycle lattice it reverses the orientation of each path from one vertex to the other and is again adjoint to itself. This is a complete check of the sign in the discriminant pairing.

Suppose instead that Frobenius exchanges the two components and permutes the $m$ edges. A geometric generator of $\Phi$ need not be rational. One first computes the signed permutation on the cycle basis, then passes to the cokernel, and only then takes fixed points. Taking the quotient graph first produces one vertex with loop orbits and can change the answer because edge stabilizers and orientation reversal have been forgotten.

The component theorem also controls specialization of divisor classes. If $P$ and $Q$ are sections reducing to smooth points on $Y_0$ and $Y_1$, then

$$
\operatorname{sp}([P-Q])=[Y_0-Y_1]\in\Phi. \tag{10.22}
$$

In the unit-edge two-vertex case this class generates $\Phi$. Applying $T$ before specialization multiplies it by $a-b$; applying the component operator after specialization gives the same answer by the correspondence specialization theorem. If $P$ or $Q$ is defined only over a residue extension, its full Galois orbit contributes, with residue degrees. A single geometric branch point does not define a rational divisor class.

## 11. The Gram matrix and its limits

### 11.1 Adjoints of the two maps

The principal polarizations on the two Jacobians give perfect alternating pairings on their prime-to-$v$ Tate modules and perfect Poincaré pairings on first cohomology. Pullback along a finite map is adjoint to norm. Thus the adjoint of

$$
d=(\pi_0^*,\pi_1^*):M^{\oplus2}\to N
$$

is

$$
d^*=\binom{\pi_{0,*}}{\pi_{1,*}}:
N\longrightarrow M^{\oplus2}. \tag{11.1}
$$

The diagonal composites are

$$
\pi_{i,*}\pi_i^*=[\deg\pi_i]=[q_v+1]. \tag{11.2}
$$

The off-diagonal composites are the two orientations of the hyperspecial Hecke correspondence at $v$. In the fixed trivial-central block they agree. Before central specialization they are transposes and can differ by the central operator; retaining that distinction is necessary for a nontrivial character.

The pairings used here are integral and perfect at fine level. If one descends through a finite quotient, the trace pairing must be divided or scaled consistently on both levels. Prime-to-$\ell$ descent makes the scaling a unit. A hidden stabilizer factor would change (11.2) integrally even though the rational adjoint remained correct.

### 11.2 The exact matrix

In the normalization of Sections 2 and 5, double-coset composition gives

$$
d^*d=
\begin{pmatrix}
q_v+1&T_v\\
T_v&q_v+1
\end{pmatrix}. \tag{11.3}
$$

**Proof.** The diagonal entries are (11.2). For the upper-right entry, pull back through $\pi_1$ and trace through $\pi_0$. The fiber product parametrizes the relative-position-$v$ neighbors of the hyperspecial lattice. With the declared right-action orientation this is the unnormalized double coset $T_v$. The other off-diagonal entry is the transpose correspondence. In the trivial-central block the spherical correspondence is self-adjoint, giving the same $T_v$. Scheme lengths retain coincident neighbors, so no averaging factor occurs. $\square$

The formula holds on Jacobians, Tate modules, cohomology, and every Hecke-stable localization. It is a consequence of correspondence composition, not a numerical identity valid only on eigenvectors.

The special fiber provides an independent check of the off-diagonal entry. Restrict $\pi_0$ and $\pi_1$ using (8.7). Pullback followed by trace on the two normalized branches gives the sum of Frobenius and Verschiebung, with the central transport inserted in the nontrivial-character convention. On prime-to-$v$ Tate modules,

$$
V_v=q_vF_v^{-1}.
$$

Thus the cross composite has the same good-prime Hecke polynomial as the spherical correspondence. This does not prove (11.3)—nearby cycles include the graph terms—but it checks its orientation and central factor. The generic double-coset composition remains the proof because it controls every fiber and every realization simultaneously.

There is also a degree audit. On $H^0$, both diagonal composites multiply constants by $q_v+1$. The cross correspondence has $q_v+1$ sheets as well. On top cohomology, pullback and trace exchange which leg contributes degree, but Poincaré adjunction gives the same matrix after the source pairings are normalized. An averaged Hecke operator would divide the off-diagonal entries without dividing the geometric degrees and would break this audit.

For a nontrivial central convention, the invariant statement is

$$
d^*d=
\begin{pmatrix}
\deg\pi_0&\pi_{0,*}\pi_1^*\\
\pi_{1,*}\pi_0^*&\deg\pi_1
\end{pmatrix}, \tag{11.4}
$$

with the two off-diagonal terms related by transpose and the known central factor. All saturation results are unchanged because their proof uses the tree rather than a chosen symmetric presentation of (11.4).

### 11.3 Congruence factors

Suppose a rank-one Hecke eigensummand of $M\otimes E$ has $T_v$-eigenvalue $a_v$. On the associated old plane, (11.3) has determinant

$$
\Delta_v=(q_v+1)^2-a_v^2
=(q_v+1-a_v)(q_v+1+a_v). \tag{11.5}
$$

If

$$
a_v\equiv\varepsilon(q_v+1)\pmod\varpi,
\qquad \varepsilon\in\{1,-1\}, \tag{11.6}
$$

then the residual vector $(1,-\varepsilon)$ lies in the kernel of the Gram matrix. Under the abelian Ihara condition it does **not** lie in the kernel of $d$, by (6.12). Rather, its image is orthogonal modulo $\varpi$ to the old image. This is the seed of a congruence with the new quotient.

The two signed factors are

$$
c_v^\varepsilon=q_v+1-\varepsilon a_v,
\qquad
c_v^{-\varepsilon}=q_v+1+\varepsilon a_v. \tag{11.7}
$$

If $q_v\not\equiv-1\pmod\ell$ and $\ell$ is odd, the second factor is a unit whenever the first vanishes residually. Hence

$$
\operatorname{ord}_\varpi\Delta_v
=\operatorname{ord}_\varpi c_v^\varepsilon. \tag{11.8}
$$

If $q_v\equiv-1\pmod\ell$, both signed factors can be nonunits. The full determinant then no longer measures one chosen branch. Conditional residual Ihara and saturation still hold, but a signed level-change theorem requires a refined $U_v$-selected calculation.

### 11.4 Why a determinant is not an Ihara proof

There are three regimes.

If $\Delta_v$ is a unit, the old image is an orthogonal direct summand. The inverse of the Gram matrix gives an integral projector. This is stronger than saturation but contains no level-raising congruence.

If $\Delta_v$ is a nonzero nonunit, the old image may be saturated while failing to split orthogonally. This is the desired congruence regime. The map $R\to R^2$, $x\mapsto(x,x)$, is primitive although the Gram determinant for a suitably scaled pairing can be a nonunit; splitting and primitivity are different questions.

If $\Delta_v=0$ on a characteristic-zero summand, the Gram matrix alone says only that a nonzero old vector lies in the orthogonal intersection of the old space with itself. It does not say that the two old vectors are rationally dependent: excluding this case requires a separate characteristic-zero temperedness or automorphic input, and does not follow from the tree sequence.

Conversely, a nonzero determinant does not prove saturation. Multiplication by $\pi$ has nonzero determinant but nonsaturated image. Any proof that computes (11.5), observes that it is nonzero in $E$, and declares the integral quotient torsion-free has skipped the central arithmetic step.

The relation among image, orthogonal kernel, and Gram matrix can be made exact. Let $A=d(M^2)\subset N$, assume $d$ is injective and primitive, and identify $M^2$ with $A$. Restriction of the perfect pairing gives a homomorphism

$$
G=d^*d:M^2\longrightarrow(M^2)^\vee. \tag{11.9}
$$

There is an exact sequence

$$
0\longrightarrow N^\perp
\longrightarrow N
\xrightarrow{d^*}(M^2)^\vee
\longrightarrow\operatorname{coker}(d^*)
\longrightarrow0. \tag{11.10}
$$

The image of $A$ under $d^*$ is $G(M^2)$. Hence the finite module

$$
\mathcal C_{\mathrm{Gram}}
=\operatorname{im}(d^*)/G(M^2) \tag{11.11}
$$

measures the intersection of old and new modulo the old pairing. It injects into $\operatorname{coker}G$, but equality requires $d^*$ to be surjective. Perfectness of $N$ and primitivity of $A$ do make the restriction $N^\vee\to A^\vee$ surjective, so after identifying $N\simeq N^\vee$ one obtains

$$
\operatorname{im}(d^*)=(M^2)^\vee,
\qquad
\mathcal C_{\mathrm{Gram}}\simeq\operatorname{coker}G. \tag{11.12}
$$

Thus the Gram cokernel measures the old lattice's failure to be self-dual inside $N$, not failure of primitivity. On an eigenline its order is governed by (11.5). This finite congruence module is compatible with a torsion-free quotient because it compares a lattice with its **dual**, not with its saturation.

To see the distinction in rank one, take $N=R^2$ with the standard pairing and $A=R(1,a)$, where at least one of $1,a$ is a unit. Then $A$ is primitive for every $a$, while its Gram is multiplication by $1+a^2$. If $1+a^2$ is a nonunit, $N/A$ is still free of rank one but $A$ is not self-dual for the restricted pairing. Its orthogonal line meets $A\otimes K$ only at zero, yet the reductions of the two lines can meet. This is the elementary model of an old--new congruence.

## 12. The integral new quotient

### 12.1 Quotient and orthogonal definitions

Retain the non-Eisenstein localization $\mathfrak m$. There are two natural new objects:

$$
Q_{\mathfrak m}
=N_{\mathfrak m}/d(M_{\mathfrak m}^{\oplus2}), \tag{12.1}
$$

and

$$
N^{\perp}_{\mathfrak m}
=\ker(d^*:N_{\mathfrak m}\to M_{\mathfrak m}^{\oplus2}). \tag{12.2}
$$

The first is a quotient. It is the object on which torsion would record failure of saturation. The second is a submodule. It is automatically torsion-free but, without saturation, it is dual to the quotient by the **saturation** of the old image rather than to (12.1). Theorem 7.1 is exactly what makes the two definitions match by duality.

Neither definition asserts a direct-sum decomposition

$$
N=N^{\mathrm{old}}\oplus N^\perp.
$$

Such a decomposition exists integrally only when the restricted old pairing is unimodular. At a congruence prime it is expected to fail.

### 12.2 Perfect duality

Let $\langle\ ,\ \rangle_N$ be the perfect Poincaré pairing, with the Tate twist and transpose involution understood. It defines

$$
N^{\perp}_{\mathfrak m}\longrightarrow Q_{\mathfrak m}^\vee,
\qquad
z\longmapsto(\bar n\mapsto\langle z,n\rangle_N). \tag{12.3}
$$

This is well defined because $z$ annihilates the old image.

**Theorem 12.1 (conditional new quotient duality).** Under the abelian Ihara condition, the map (12.3) is an isomorphism. In particular both $Q_{\mathfrak m}$ and $N^{\perp}_{\mathfrak m}$ are finite free of the same rank.

**Proof.** The old image is saturated by Theorem 7.1. Apply Lemma 3.2 with $P=N_{\mathfrak m}$ and $A=N^{\mathrm{old}}_{\mathfrak m}$. Under the perfect pairing, its orthogonal is precisely the kernel of the adjoint $d^*$. $\square$

After tensoring with $E$, a polarization identifies the quotient new space and the orthogonal new space noncanonically. Integrally the canonical statement is the duality (12.3), not equality of two submodules of $N$.

### 12.3 Hecke stability and transpose

Away-from-$v$ Hecke operators commute with both degeneracy maps. Hence the old image and quotient $Q_{\mathfrak m}$ are Hecke stable. If $T$ is such an operator and $T^t$ its transpose, then

$$
\langle Tz,n\rangle_N
=\langle z,T^tn\rangle_N. \tag{12.4}
$$

Since the old image is stable under $T^t$, equation (12.4) shows that $N^\perp$ is stable under $T$. Under (12.3), the action on $N^\perp$ is dual to the transposed action on $Q$.

At $v$, the Iwahori Hecke correspondence acts integrally on $N$. Its action on a representation-theoretic new line may later be identified with a sign or local type. The present book uses only the integral correspondence and its adjoint. It does not infer the relation $U_v^2=1$ from the hyperspecial polynomial, because the Iwahori correspondence and the spherical correspondence are different geometric objects.

### 12.4 Monodromy carried by the new quotient

The lower-level curve has good reduction at $v$, so inertia acts trivially on $M$ and its monodromy operator is zero. Functoriality gives

$$
N_{\mathrm{mon}}\circ d=d\circ0=0. \tag{12.5}
$$

Thus monodromy descends to $Q_{\mathfrak m}$. Theorem 10.2 identifies the top quotient with $X(-1)$ and the saturated bottom lattice with $L_0$. After cancelling the common Tate twist, the descended operator is

$$
X\xrightarrow{q_\Gamma}X^\vee\longrightarrow L_0. \tag{12.6}
$$

There are two immediate consequences.

First, every nonzero graph cycle in the localized quotient gives a length-two monodromy block after tensoring with $E$. The old subspace cannot contain such a block.

Second, the ambient graph pairing still has cokernel

$$
\Phi_C[\ell^\infty]_{\mathfrak m}. \tag{12.7}
$$

But $X^\vee$ need not be saturated in $Q$. The quotient $L_0/X^\vee$ is the explicit branch correction $\mathcal C_{\mathrm{br},v}$, and the full monodromy cokernel is the extension (10.17). Saturation of the old image removes torsion from $Q$; it does not make the sum of the old and graph lattices primitive.

This is the form of component control needed in level lowering. A residual class killed by monodromy can be compared directly with the lower-level image only after checking $\mathcal C_{\mathrm{br},v}[\varpi]=0$, or after carrying the class through the two-step extension (10.17). The two finite sources are now distinguished: $\Phi_C$ is the discriminant of $q_\Gamma$, while $\mathcal C_{\mathrm{br},v}$ is the Smith cokernel of the normalized branch map.

One can also see directly how a Gram-kernel vector enters the orthogonal new reduction. Let $x\in M^2$ have nonzero reduction and suppose

$$
Gx\in\varpi(M^2)^\vee. \tag{12.8}
$$

Surjectivity of $d^*$ from (11.12) supplies $z\in N$ with

$$
d^*z=\varpi^{-1}Gx. \tag{12.9}
$$

Then

$$
y=d(x)-\varpi z
$$

satisfies $d^*y=0$, so $y\in N^\perp$. Modulo $\varpi$,

$$
\bar y=\overline{d(x)}. \tag{12.10}
$$

The abelian Ihara condition makes the right side nonzero. Thus a nonzero Gram-kernel vector produces a nonzero new residual class. Saturation guarantees that this class is the reduction of a free new lattice rather than the boundary of torsion in $Q$. This calculation explains why both injectivity and saturation are needed even though they arise from the same residual criterion once (6.11) is supplied.

If (12.8) holds only after multiplying $x$ by a denominator, the construction fails integrally. Likewise, if $d^*$ is not surjective because the old image is not primitive, (12.9) may have no solution. These are not technical inconveniences; they are the two precise ways a rational level-raising argument can fail to produce an integral new class.

Assume now that $x$ is an eigenvector and (11.6) holds. Choosing

$$
x_\varepsilon=(x,-\varepsilon x)
$$

makes (12.8) equivalent to divisibility of $c_v^\varepsilon$. If the companion factor is a unit, the Gram cokernel on this eigenplane is cyclic with length

$$
\operatorname{ord}_\varpi c_v^\varepsilon.
$$

The construction (12.9)--(12.10) then produces a residual orthogonal class of the selected sign. Notice the order of the conditional argument: (6.11) first proves $d(x_\varepsilon)\not\equiv0$; perfectness moves its Gram divisibility into the orthogonal kernel; saturation proves that the quotient carrying the class is free. Reversing this order would use the desired new class to justify its own integrality.

If both signed factors are nonunits, the Gram cokernel can have two generators and the single vector $x_\varepsilon$ does not determine its elementary divisors. Smith normal form of the full $2\times2$ operator matrix is then required. This is the algebraic content of the $q_v\equiv-1$ exception.

## 13. Descent and exceptional cases

### 13.1 Residue-field and Galois descent

All graph calculations are geometric. Let $G_{k_v}$ act on vertices and on oriented edges. If an element exchanges the branches of a node, it sends the oriented generator $e$ to $-e$. The pairing $q_\Gamma$ is invariant because both coefficients change sign.

The component group over the residue field is the finite étale group scheme descending from (10.3). Its rational points are

$$
\Phi_C(k_v)=\Phi_C(\bar k_v)^{G_{k_v}} \tag{13.1}
$$

when $k_v$ is perfect. This fixed subgroup can be smaller than the geometric group. A nonsplit loop of length $n$ has geometric component group $\mathbf Z/n\mathbf Z$ with Frobenius acting by $-1$; its rational subgroup consists of the classes killed by $2$.

Every degeneracy and away-from-$v$ Hecke map is Galois equivariant because the PEL correspondence descends to the chosen component field. If a correspondence routes one generic connected component to another, the correct object is the product over a stable component orbit. Restricting it to a nonstable single factor would not define an endomorphism and is excluded from the datum of Section 2.1.

### 13.2 Ramified base change and thickness

Let $R'_v/R_v$ have ramification index $e$. The local equation becomes

$$
xy=u(\pi'_v)^e. \tag{13.2}
$$

Resolving replaces the edge by a chain of $e$ unit edges. A graph cycle has the same coefficient on every segment, so

$$
q_{\Gamma,R'}=e q_{\Gamma,R}. \tag{13.3}
$$

Writing $X=H_1(\Gamma,\mathbf Z)$, the inclusions

$$
eqX\subset qX\subset X^\vee
$$

give the exact sequence

$$
0\longrightarrow X/eX
\xrightarrow{q}
\Phi_{R'}(\bar k_v)
\longrightarrow\Phi_R(\bar k_v)
\longrightarrow0. \tag{13.4}
$$

The proof is successive quotienting: the kernel of $X^\vee/eqX\to X^\vee/qX$ is $qX/eqX$, canonically isomorphic to $X/eX$ because $q$ is injective.

The sequence need not split. Ramification can enlarge an invariant factor rather than append a separate copy of $\mathbf Z/e\mathbf Z$. Rational monodromy rank is unchanged, while the integral component group grows by $e^{b_1(\Gamma)}$ in order.

Unramified base change leaves thickness unchanged and merely reduces the residue Galois group. It can split a node or component orbit, but it does not create new geometric edges after passage to a common separable closure.

For a one-loop graph, (13.4) is completely explicit:

$$
0\to\mathbf Z/e\mathbf Z
\to\mathbf Z/(en)\mathbf Z
\to\mathbf Z/n\mathbf Z\to0. \tag{13.5}
$$

It splits exactly when $e$ and $n$ are coprime. If they have a common factor, the middle cyclic group is not the direct sum of the endpoints. This elementary example is the safest warning against replacing the exact lattice sequence by an order formula.

Ramified base change does not change the tree obstruction (6.10): the tree and its arithmetic groups are attached to the original level-changing place. What changes is the integral model used to read monodromy. The cycle lattice remains canonically the same after subdivision, while $q$ is multiplied by $e$. Thus, when the abelian Ihara condition holds, saturation of the old cohomology image and enlargement of the component group are compatible and independent phenomena.

### 13.3 Stabilizers and small coefficient primes

At neat level, the analytic and algebraic curves have no stabilizers. At tame nonneat level, choose a normal neat cover with deck group $\Delta$. If $\ell\nmid|\Delta|$, transfer followed by pullback is $|\Delta|$, a unit, and invariants are exact. Every theorem descends.

If $\ell\mid|\Delta|$, three failures can occur:

1. $H^1(\Delta,k)$ contributes extra classes to the quotient curve;
2. coarse trace can contain a nonunit stabilizer factor;
3. a primitive image upstairs can become nonprimitive after taking nonexact invariants.

For the fine rational quaternionic levels used in the clean coefficient range, possible effective projective stabilizers have orders supported at small primes, and $\ell\ge7$ avoids them. Over a general totally real datum one should not replace the explicit prime-to-$\ell$ stabilizer condition by a numerical slogan; neatness is the uniform safe hypothesis.

The prime $\ell=2$ also changes signs in the tree map: $r_0-r_1$ and $r_0+r_1$ become identical, and branch reversal is invisible modulo two. The uniform theorem is intentionally stated for $\ell\ge7$. At $\ell=3$ or $5$, the fine constant-coefficient tree calculation can remain valid, but arithmetic abelianization, coarse descent, and type lattices require separate small-prime checks.

### 13.4 Scalar, Eisenstein, and vexing cases

The tree theorem says that arithmetic characters of $\Gamma^v$ give exactly all relations on the norm-one cover, and the original curve retains their $\Delta$-invariant part. The congruence-continuous characters, including those supported at division, coefficient, and bad-level compact factors, are Eisenstein. Reduced norm, central action, and component routing supply the corresponding twists and exact descent rather than extra characters of $\Gamma^v$. A $\Delta$-invariant noncongruence character is the additional obstruction isolated in (6.10). Thus non-Eisenstein localization is necessary but, without the abelian Ihara condition, not by itself sufficient for residual injectivity.

The congruences $q_v\equiv1$ and $q_v\equiv-1\pmod\ell$ are different exceptional phenomena.

If $q_v\equiv1$, the two residual roots $\varepsilon$ and $\varepsilon q_v$ of the old $U_v$ polynomial collide. The unramified residual representation can be scalar, so an ordered Frobenius line is not intrinsic. Under the abelian Ihara condition the full two-map image is still saturated, but this does not produce a canonical integral projector onto one branch.

If $q_v\equiv-1$, the two roots $\varepsilon$ and $-\varepsilon$ remain distinct for odd $\ell$, but both signed Gram factors in (11.7) can vanish. The valuation identity (11.8) fails. A $U_v$-selected determinant calculation can distinguish the branches, but the unselected Gram determinant cannot.

A **vexing** local datum is one in which the residual scalar or ramified type admits more than one integral lattice or flag with the same unlabelled reduction. Even after the constant-coefficient abelian Ihara condition is supplied, the resulting theorem controls only the full cohomology lattice; it does not assert that an independently chosen type projector has saturated image. Such a case requires the type-enhanced level structure and its own prime-to-stabilizer hypotheses. Primitive wild supercuspidal types are outside the catalog scope.

Even when the abelian Ihara condition holds, the branch correction need not vanish. Its support is the Smith support of $1-(F_v^*)^2$, so it is expected at a signed level-raising congruence. It does not alter conditional residual injectivity or the resulting freeness of $Q$; it changes the integral identification of the bottom monodromy lattice and must be carried in any lowering argument.

It is useful to summarize the exceptional cases as failures of exact statements rather than as labels.

| Situation | Statement that can fail | Statement that remains valid under the other hypotheses |
|---|---|---|
| Eisenstein localization | residual injectivity and saturation | tree identification of the kernel and cokernel |
| noncongruence character at $\mathfrak m$ | residual injectivity even when $\mathfrak m$ is non-Eisenstein | Eisenstein calculation on the congruence-character submodule |
| $\ell$-divisible stabilizer | exact descent from a fine cover | fine-level tree criterion and, if (6.11) holds there, fine-level saturation |
| $q_v\equiv1\pmod\ell$ | integral separation of the two old $U_v$ roots | conditional full two-map saturation |
| $q_v\equiv-1\pmod\ell$ | one-factor valuation formula | full Gram matrix and conditional saturation |
| nonunimodular branch map | primitive bottom graph copy and correction-free lowering | under (6.11), free new quotient and exact sequence (10.17) |
| ramified base change | unit edge lengths and unchanged component group | subdivision-invariant cycle lattice |
| nonstable component | endomorphism of one factor | correspondence between the routed factors |

This table separates three independent questions: the noncongruence character obstruction to full Ihara, the signed projector obstruction, and the branch-correction obstruction. None can be used to erase another.

The coefficient-prime equality $v\mid\ell$ is more serious. The analytic tree still exists, but the integral geometric comparison changes: the $v$-power torsion of the Jacobian is finite flat rather than étale, Kummer residues no longer produce a free $\mathbf Z_\ell$ local system in the same way, and connected group schemes can contribute. The present component and saturation package is therefore deliberately prime-to-$v$.

## 14. The saturated Ihara package

### 14.1 Main theorem

We collect the exact source-closed implication proved in this book. The extra hypothesis in item 8 is the obstruction isolated by the tree, not a disguised congruence-subgroup property.

**Theorem 14.1 (conditional geometric Ihara, saturation, and components).** Let $F$, $B$, $U$, $v$, $U_0(v)$, $\mathcal O$, and $\mathfrak m$ satisfy the following hypotheses:

1. $F$ is totally real and $B/F$ is a division quaternion algebra split at exactly one real place;
2. the chosen Shimura component union is proper, stable under the relevant correspondences, and represented at a neat level, or obtained from such a level by a quotient of order prime to $\ell$;
3. $B$ is split at $v$, $U_v$ is hyperspecial, and $U_0(v)_v$ is the standard Iwahori;
4. the PEL datum at $v$ is unramified with self-dual lattice and verified flat rank-two incidence local model;
5. $\ell\ge7$, $v\nmid\ell$, and $\mathcal O$ is a finite extension of $\mathbf Z_\ell$;
6. component routing and the center act trivially on the selected Hecke-stable block, with $T_w,S_w$ normalized as unnormalized right-double-coset operators;
7. $\mathfrak m$ is non-Eisenstein for the ideal (2.4);
8. the abelian Ihara condition $({\rm AIH})_{v,\mathfrak m}$ holds:
   $$
   \bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}=0,
   $$
   equivalently any of the conditions in (6.11).

Put

$$
M=H^1(X_{U,\overline F},\mathcal O),
\qquad
N=H^1(X_{U_0(v),\overline F},\mathcal O),
$$

and let

$$
d=(\pi_0^*,\pi_1^*):M^{\oplus2}\to N.
$$

Then:

1. the residual map
   $$
   d_k:(M/\varpi M)_{\mathfrak m}^{\oplus2}
   \longrightarrow(N/\varpi N)_{\mathfrak m}
   $$
   is injective;
2. the integral map $d_{\mathfrak m}$ is injective with saturated image;
3. the quotient
   $$
   Q_{\mathfrak m}=N_{\mathfrak m}/d(M_{\mathfrak m}^{\oplus2})
   $$
   is finite free over $\mathcal O$;
4. for the perfect Poincaré pairing,
   $$
   \ker d^*_{\mathfrak m}\simeq Q_{\mathfrak m}^\vee;
   $$
5. in the trivial-central normalization,
   $$
   d^*d=
   \begin{pmatrix}q_v+1&T_v\\T_v&q_v+1\end{pmatrix};
   $$
6. the common fine Iwahori model at $v$ is regular strict semistable with weighted dual graph $\Gamma$. If $\Delta\ne1$, all modules in this clause mean their exact $\Delta$-invariant descent from that model. If
   $$
   X=H_1(\Gamma,\mathcal O)_{\mathfrak m},
   \qquad
   X^\vee=H^1(\Gamma,\mathcal O)_{\mathfrak m},
   $$
   then $W_0=X^\vee$ is saturated in $N_{\mathfrak m}$, the saturation of
   $d(M_{\mathfrak m}^{\oplus2})+W_0$ is $(W_1)_{\mathfrak m}$, and its image in
   $Q_{\mathfrak m}$ has saturation $L_0=(W_1)_{\mathfrak m}/d(M_{\mathfrak m}^{\oplus2})$.
   The lattice $L_0$ is free and saturated in $Q_{\mathfrak m}$, with exact sequences
   $$
   0\to X^\vee\to L_0\to\mathcal C_{\mathrm{br},v}\to0,
   \qquad
   0\to L_0\to Q_{\mathfrak m}\to X(-1)\to0,
   $$
   where
   $$
   \mathcal C_{\mathrm{br},v}
   \simeq\operatorname{coker}\!\left(1-(F_v^*)^2\right)_{\mathfrak m};
   $$
7. after cancelling the common Tate twist, monodromy is
   $$
   X\xrightarrow{q_\Gamma}X^\vee\to L_0,
   $$
   and its cokernel is the canonical extension
   $$
   0\to
   \Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
   \otimes_{\mathbf Z_\ell}\mathcal O
   \to\operatorname{coker}(N_Q)
   \to\mathcal C_{\mathrm{br},v}\to0;
   $$
8. all statements are equivariant for away-from-$v$ Hecke operators, transpose adjunction, and the signed residue Galois action.

In particular the localized old image is primitive and the integral new quotient has no torsion. The two finite special-fiber effects are measured separately: the Néron component group is the discriminant of $q_\Gamma$, while the branch correction is the Smith cokernel of the normalized-component degeneracy map.

### 14.2 Proof of the main theorem

**Proof strategy.** The proof has four independent parts: the tree isolates the full kernel and its noncongruence quotient; the arithmetic calculation makes the congruence part Eisenstein and hypothesis 8 removes the remaining localization; DVR algebra turns residual injectivity into saturation; and the nodal model identifies the component and branch modules.

**Proof.** The lattice graph at $v$ is a tree by Proposition 4.1. Strong approximation, Theorem 4.2, makes its quotient by the $S$-arithmetic group a single edge. The tree Mayer--Vietoris sequence therefore gives the exact kernel and cokernel sequence (6.5). Complex uniformization and cohomological comparison identify its two restriction maps with $\pi_0^*$ and $\pi_1^*$.

Proposition 5.3 makes the congruence-continuous norm-one character submodule Eisenstein, including its division-, coefficient-, and bad-level local factors; reduced norm, central action, and component routing give the declared twists. Exact prime-to-$\ell$ descent then takes $\Delta$-invariants. Non-Eisenstein localization kills the resulting congruence submodule. Formula (6.10) identifies the remaining kernel with $\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}$, which is zero by hypothesis 8. This proves clause 1 without any assertion about the full congruence kernel.

The two cohomology modules are finite free over $\mathcal O$ by the Riemann-surface cell calculation of Section 7.1. Lemma 3.1 applied to the localized map now proves injectivity and saturation, hence clauses 2 and 3. Perfect Poincaré duality and Lemma 3.2 prove clause 4. Pull--norm adjunction and the right-double-coset calculation prove clause 5.

The parahoric PEL local model has equation $xy=\pi_v$, so Theorem 8.1 gives the required regular semistable fine model. In the tame quotient case, Section 8.4 applies exact $\Delta$-invariants to every following construction; no regularity assertion about the coarse quotient is used. The normalization and nearby-cycle calculations give the free filtration (9.6)--(9.7). Since the lower Jacobian has good reduction, Lemma 10.1 places the old image in $W_1$ with zero intersection with $W_0$. The projection to normalized-component cohomology is the branch matrix (10.10). Its Smith reduction (10.12), rather than saturation of the old image alone, gives the finite module $\mathcal C_{\mathrm{br},v}$.

Quotienting the filtration yields (10.14)--(10.15): the top graph lattice survives unchanged, while the saturated bottom lattice $L_0$ contains the graph dual with quotient $\mathcal C_{\mathrm{br},v}$. The local Kummer calculation identifies monodromy with the composite (10.16). The Raynaud graph theorem identifies the first cokernel in (10.17) with the Néron component group, and the cokernel sequence retains the branch correction. This proves clauses 6 and 7.

Correspondence extension, graph adjunction, and descent preserve each construction, proving clause 8. $\square$

### 14.3 Hypothesis and dependency ledger

The logical use of the six direct prerequisites is exact.

| Source | Imported result | Hypotheses retained | Work done here |
|---|---|---|---|
| Book 16 | nodal normalization, graph cycles, weighted pairing, discriminant component group, subdivision, finite-map adjunction | semistable curve; geometric graph; thickness and signed descent retained | application to the Iwahori quotient and separation of the graph discriminant from the branch correction |
| Book 38 | Néron mapping property, identity component, component group, semistable Jacobian, unramified base change | excellent DVR; henselianity where reduction is used; perfect residue field for fixed-point notation | identification of the ambient component term in the localized monodromy-cokernel sequence |
| Book 39 | extension of pull--norm correspondences, transpose, specialization, graph and intersection maps | smooth proper generic curves; regular models; controlled resolved correspondence | simultaneous Hecke action and adjunction on the new and component lattices |
| Book 124 | Shimura degeneracy maps, right-coset orientation, component routing, old map, adjoints, Gram matrix framework | stable component union; fine or tame descent; unnormalized operators | exact tree criterion and, under (6.11), geometric injectivity and saturation, which Book 124 explicitly leaves open |
| Book 118 | rank-one strong approximation for simply connected quaternion norm-one groups | a noncompact archimedean factor; arbitrary finite compact-open conditions | exact specialization to the one-edge quotient in Theorem 4.2 |
| Book 122 | rank-two parahoric PEL model, $xy=\pi_v$, strict semistability, graph monodromy, Hecke functoriality | verified flat incidence local model; neat level; prime-to-$v$ coefficients | integral quotient filtration, normalized branch map, and its Smith correction |
| Abelian Ihara condition | explicit additional hypothesis, not an imported theorem | vanishing of $\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}$ | exact point at which the conditional residual theorem becomes injective |

The tree Mayer--Vietoris sequence, the local-factor calculation on congruence-continuous arithmetic characters, the exact noncongruence obstruction, the conditional saturation criterion, and the branch Smith calculation are proved here. Strong approximation is imported only from Book 118. No congruence-kernel theorem, automorphic decomposition, multiplicity-one theorem, local newvector theorem, or modularity argument is invoked.

The mathematical direct-dependency row is therefore

$$
139\mid 16,38,39,124,118,122. \tag{14.1}
$$

The first seven hypotheses of Theorem 14.1 do not currently imply hypothesis 8 from those sources. A proof of (5.18) on the localized noncongruence quotient, an exact computation of (5.19), or a different theorem proving the last vanishing in (6.10) would close the catalog objective. Strong approximation alone cannot do so.

### 14.4 Exact boundary of the theorem

The theorem proves the clean full-Iwahori two-map statement conditional on the exact abelian Ihara condition. It does not assert that condition from the geometric and strong-approximation hypotheses alone.

The single missing arithmetic theorem can now be named without strengthening it.

**Missing arithmetic theorem $({\rm AC}^{\rm loc}_\ell)$ (localized odd-primary abelian congruence).** For every datum satisfying hypotheses 1--7 of Theorem 14.1, including every fixed tame spectator level needed downstream, one has

$$
\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}=0.
\tag{14.2}
$$

This theorem is not proved here. At one fixed datum it is exactly $({\rm AIH})_{v,\mathfrak m}$, hence is equivalent to residual Ihara injectivity by (6.10)--(6.11). A full odd-primary abelian congruence-subgroup property would assert $H^1_{\mathrm{nc}}(\Gamma^v,A)=0$ before localization for every finite $\ell$-primary $A$; it would imply (14.2), but is strictly stronger than the theorem actually needed. Likewise, centrality or $2$-primary finiteness of the entire congruence kernel would be stronger. The minimal missing assertion is the localized vanishing (14.2), not either of those global claims.

At an Eisenstein maximal ideal, the congruence arithmetic character module can survive. At a non-Eisenstein ideal, the noncongruence quotient in (6.10) is the separate possible kernel. At a nonneat quotient with $\ell$-divisible stabilizers, group cohomology of the stabilizer can add another kernel. Once (6.11) and tame descent hold, $q_v\equiv1\pmod\ell$ affects only the integral choice of an ordered $U_v$ branch, while $q_v\equiv-1\pmod\ell$ can make both signed Gram factors nonunits.

The theorem concerns constant first cohomology of the compact quaternionic Shimura curves with the verified rank-two local model. It does not cover deeper parahoric chains, primitive wild supercuspidal type projectors, nonflat determinant loci, boundary cohomology of noncompact curves, or coefficient characteristic equal to the residue characteristic at $v$.

Nor does torsion-freeness produce a canonical integral direct-sum old--new decomposition. It produces the quotient lattice and its perfect orthogonal dual. A direct summand requires the Gram determinant to be a unit, which is incompatible with the congruence regime in which level raising is used.

Finally, component control does not mean component-group vanishing, nor does old-image saturation imply that $A+W_0$ is primitive. The localized component group can be nonzero and is exactly the discriminant of the weighted graph pairing. Independently, the branch map can have the finite Smith cokernel $\mathcal C_{\mathrm{br},v}$. The clean two-piece monodromy statement is available only when that module vanishes; otherwise (10.17) is the exact interface.

There is also a precise definite-routing boundary. Book 139 constructs the geometric edge and cycle lattices $X$ and $X^\vee$, their signed Galois and Hecke actions, and the pairing $q_\Gamma$. It does **not** identify the node set with a class set for the quaternion algebra obtained by switching the invariants at $v$ and the distinguished real place. That integral graph--definite identification requires the datum-specific, coefficient-one node-uniformization theorem imposed in Book 140, together with its stabilizer, mass-pairing, and component-routing checks. Rational Jacquet--Langlands does not supply this integral identification.

The downstream interface is therefore the following. Every freeness, type-transfer, or seed entry in the right column is conditional on the stated instances of $({\rm AIH})$.

| Consumer | Valid input from this book and retained boundary |
|---|---|
| Book 140 | It may use the exact tree kernel unconditionally. Under $({\rm AIH})_{v,\mathfrak m}$ it may additionally use residual injectivity, the saturated old image, free $Q$, quotient--orthogonal duality, the Gram matrix, and (10.14)--(10.17). Its formula (8.2) is precisely the corrected filtration here. Identifying $X$ with a switched definite quaternionic lattice still requires its separate node-uniformization and generic-support inputs. |
| Book 176 | Its one-prime nonminimal comparison may import the same conditional free-quotient package and the three distinct finite modules: Gram, component, and branch. It may not promote the one-prime theorem to the finite set required by its final modularity-lifting target; mixed Ihara, product residue, and joint support remain additional inputs. |
| Book 174 | Constant-coefficient residual injectivity may be used in the integral flag-excision argument only after $({\rm AIH})$ has been imposed for **every** constant-level curve in the finite flag diagram, with the actual tame spectator levels. Book 139 neither proves the type-coefficient transfer nor makes its quotient projective over a tame deformation algebra; those are the conditional achievements of Book 174 after flag excision. |
| Book 181 | Book 139 supplies no automorphic seed by itself. For the seed used in the finite-image argument, (14.2) is the first missing input in proof order; even after it is supplied, node uniformization, the relevant one- or several-prime carrier, component support, and the other seed hypotheses must still be verified. No balanced-lift or finite-image conclusion flows directly from this book. |
| level lowering | Even under $({\rm AIH})$, require $\Phi[\varpi]_{\mathfrak n}=0$ and $\mathcal C_{\mathrm{br},v}[\varpi]_{\mathfrak n}=0$, or work inside the full extension (10.17). Component cleanliness does not erase the branch correction. |

In particular, no consumer can use $T_w\chi=(q_w+1)P_w\chi$ for every abstract character without first supplying (5.18) or (14.2). After that arithmetic gap is closed, a statement that the component group is the only finite module in the semistable quotient, or that component cleanliness alone makes residual monodromy an isomorphism between the two graph copies, still requires the independent hypothesis $\mathcal C_{\mathrm{br},v}=0$.

## 15. Conclusion

### 15.1 The mathematical package

The two degeneracy maps are deceptively simple. They come from the two endpoints of one edge in the local lattice tree, but integrally their images can meet the new lattice in a congruence of positive index. The correct argument therefore begins before any determinant is computed.

The Bruhat--Tits tree turns the two pullbacks into a Mayer--Vietoris map. On the norm-one cover its kernel is not guessed from dimensions: it is exactly the first cohomology of the group with the $v$-level removed, and its cokernel is the next explicit $H^2$ kernel. Exact prime-to-$\ell$ descent takes the corresponding $\Delta$-invariants on the original curve. In degree one the obstruction consists of additive arithmetic characters. Strong approximation embeds the congruence-continuous ones densely into the compact product. Division-place tori, coefficient-place factors, and bad-level factors are retained inside that module, while norms, centers, and components are retained through routing and descent; the transfer formula makes the resulting congruence submodule Eisenstein.

An abstract finite character need not be congruence-continuous. The unresolved quotient on the original curve is $\bigl(H^1_{\mathrm{nc}}(\Gamma^v,k)^\Delta\bigr)_{\mathfrak m}$, and residual Ihara is equivalent to its vanishing. This is the exact point at which the catalog objective presently needs a new abelian commensurator or localized $H^1$ theorem. A full congruence-subgroup property is neither assumed nor substituted for it.

Once the abelian Ihara condition supplies residual injectivity, elementary divisor theory does the integral work. The old image is saturated, its quotient is free, and perfect duality identifies the orthogonal new lattice with the dual of that quotient. This remains true when the Gram determinant is a nonunit. The nonunit then records a genuine old--new congruence rather than torsion caused by a defective lattice.

The semistable model supplies the second half of the package. Its node $xy=\pi_v$ produces a geometric dual graph, graph cycles produce the torus in the special Jacobian, and edge thicknesses produce the integral monodromy pairing. The discriminant of that pairing is the Néron component group. Good reduction places old classes in the normalized-component layer, but it does not make their sum with the bottom graph lattice primitive. The branch matrix measures the exact index, and its Smith cokernel $\mathcal C_{\mathrm{br},v}$ is retained in the quotient filtration.

### 15.2 The role in integral level change

Under the abelian Ihara condition, the final structure is a short exact sequence of free lattices

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q_{\mathfrak m}\longrightarrow0,
$$

its perfect adjoint dual

$$
\ker d^*_{\mathfrak m}\simeq Q_{\mathfrak m}^\vee,
$$

the quotient filtration

$$
0\longrightarrow X^\vee
\longrightarrow L_0
\longrightarrow\mathcal C_{\mathrm{br},v}
\longrightarrow0,
$$

$$
0\longrightarrow L_0
\longrightarrow Q_{\mathfrak m}
\longrightarrow X(-1)
\longrightarrow0,
$$

and the ambient monodromy--component sequence

$$
0\longrightarrow H_1(\Gamma,\mathbf Z_\ell)_{\mathfrak m}
\xrightarrow{q_\Gamma}
H_1(\Gamma,\mathbf Z_\ell)_{\mathfrak m}^\vee
\longrightarrow\Phi[\ell^\infty]_{\mathfrak m}
\longrightarrow0.
$$

Each finite module now has one source and one meaning. Under (6.11), the old quotient has no torsion. The failure of orthogonal splitting is measured by the Gram congruence. The Néron component group is the graph discriminant. The possible failure of the bottom graph copy to be primitive is $\mathcal C_{\mathrm{br},v}$. Before (6.11), the additional module is the localized noncongruence character group in (6.10); non-Eisenstein localization alone has not removed it.

Thus the geometric, linear-algebraic, and component parts of saturated Ihara theory are complete, and their downstream interfaces are exact. The full catalog theorem for the stated range is not source-closed until the localized odd-primary vanishing $({\rm AC}^{\rm loc}_\ell)$ in (14.2) is proved by additional arithmetic input. The abelian commensurator identity (5.18) would suffice, but is stronger than that minimal localized theorem.
