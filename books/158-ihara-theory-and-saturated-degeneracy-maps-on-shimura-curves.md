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
6. [Geometric Ihara injectivity](#6-geometric-ihara-injectivity)
   - [Complex uniformization and comparison](#61-complex-uniformization-and-comparison)
   - [The degeneracy map as restriction](#62-the-degeneracy-map-as-restriction)
   - [The Eisenstein kernel theorem](#63-the-eisenstein-kernel-theorem)
   - [The mod-$\ell$ Ihara theorem](#64-the-mod-ell-ihara-theorem)
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

This book proves the needed conclusion by identifying the entire residual kernel as Eisenstein. It then turns residual injectivity into saturation by elementary integral algebra. The semistable model at $v$ supplies the further monodromy and component-group description needed to know what survives in the new quotient.

### 1.3 The geometric mechanism

There are two geometries, one generic and one integral.

At the generic place, the Bruhat--Tits tree for $\operatorname{PGL}_2(F_v)$ has two adjacent vertices stabilized by the two hyperspecial levels and an edge stabilized by the Iwahori level. The two degeneracy maps become the two restriction maps in the cohomology of vertex and edge stabilizers. The cellular resolution of the tree shows that the kernel comes from the cohomology of the group obtained by allowing arbitrary level at $v$. In degree one with constant coefficients, this cohomology consists of additive characters. A direct double-coset calculation shows that every away-from-$v$ Hecke operator acts on these characters by its Eisenstein degree. Non-Eisenstein localization therefore kills the kernel.

At the integral place, the Iwahori PEL model is regular semistable. Its completed nodal charts are

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

### 1.4 Dependency boundary

Five earlier books supply the exact imported facts.

Book 12 supplies the normalization sequence of a nodal curve, graph homology, weighted monodromy pairings, their discriminant groups, subdivision invariance, and functoriality under finite maps. Book 39 supplies Néron models, extension of Jacobian homomorphisms, identity components, component maps, and the Raynaud description of a semistable Jacobian. Book 41 supplies integral pull--norm correspondences, adjunction, specialization, and the intersection- and graph-lattice formulas for their component actions. Book 122 supplies the two Shimura degeneracy maps with the right-double-coset orientation, their adjoints, and the exact old-level Gram formalism; it explicitly does not supply saturation. Book 131 supplies the parahoric PEL model, the chart $xy=\pi_v$, strict semistability, the graph description of monodromy, and Hecke functoriality away from $v$; it explicitly makes integral conclusions conditional on saturation.

The new work here is the tree calculation, the Eisenstein-kernel theorem, residual injectivity, the primitive-image theorem, the torsion-free new quotient, and their synthesis with the monodromy and component sequences. No rational old--new decomposition, later level-change theorem, or later automorphic comparison is used to prove them.

## 2. The clean Shimura-curve datum

### 2.1 Global quaternionic data

We now specify the curves for which the theorem is proved. Let $F$ be totally real and $B/F$ a quaternion algebra split at exactly one real place $\tau$ and ramified at all other real places. We assume $B$ is a division algebra. The associated Shimura curves are then proper: no cusp or boundary term enters their first cohomology.

Let

$$
G=\operatorname{Res}_{F/\mathbf Q}B^\times
$$

with the central convention already fixed in the chosen canonical model. For the group-theoretic calculation it is convenient to use the derived group

$$
G^1=\operatorname{Res}_{F/\mathbf Q}\operatorname{SL}_1(B).
$$

Passing from $G$ to $G^1$ fixes a connected component and removes the reduced-norm character. The finite component routing of a central double coset is handled before this passage, as in the established Shimura-curve convention. We require the chosen component union to be stable under every correspondence used below.

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

At nonneat level, choose a neat normal subgroup $U'\triangleleft U$. If the order of the deck group is a unit in $\mathcal O$, taking invariants is exact and the theorem descends. If $\ell$ divides that order, a stabilizer cohomology class can enter the Ihara kernel. Such a level is outside the clean theorem; it requires a stack-level or type-enhanced calculation.

### 2.4 Hecke and Eisenstein conventions

Let $\Sigma$ contain $v$, the places where $B$, the level, or the integral PEL datum is ramified, and the coefficient place. For $w\notin\Sigma$, let $T_w$ be the unnormalized spherical right-double-coset operator. Thus $T_w$ has degree $q_w+1$ on constants. Let $S_w$ be the central one-coset operator.

For the fixed connected, trivial-central-character block used in the clean theorem, define the Eisenstein ideal

$$
\mathfrak E=\bigl(T_w-(q_w+1),\ S_w-1:
w\notin\Sigma\bigr). \tag{2.2}
$$

A maximal ideal $\mathfrak m$ of the integral Hecke image is **non-Eisenstein** if it does not contain $\mathfrak E$ in the sense that at least one generator in (2.2) acts invertibly after localization at $\mathfrak m$. Equivalently, the simultaneous scalar system carried by arithmetic characters does not occur at $\mathfrak m$.

This definition is deliberately operator-theoretic. When a residual two-dimensional representation has already been constructed, absolute irreducibility implies non-Eisensteinness, but no such representation is needed in the proof. For a nontrivial fixed central character, the degree relation is twisted by the corresponding one-dimensional character. The proof is identical after replacing (2.2) by that visibly twisted scalar ideal. We state the main theorem in the trivial-central form because it is the exact clean block used in the coefficient-prime range under consideration.

There are two reasons to define the ideal using infinitely many good operators. First, it makes the definition independent of a chosen generating set of the finite image algebra. Since the image algebra acting on a fixed finite module is finite over $\mathcal O$, finitely many of the displayed relations generate the same localized ideal on that module. Second, it separates a geometric condition from a Galois interpretation. The proof below only needs one operator $T_w-(q_w+1)$ or $S_w-1$ to become a unit. It never needs a representation attached to $\mathfrak m$.

If a central character $\chi$ is retained, a one-dimensional unramified system has two Satake characters, one of which is trivial after normalization and the other determined by $\chi$. The scalar relation becomes the trace of those two characters. Rather than guess an inverse diamond, one obtains it by applying the declared right-coset correspondence to the central component. The transpose identity then checks the result. This is why the main theorem records the trivial-central relation explicitly and treats the twisted relation by the invariant matrix (11.4).

A maximal ideal supported only on component permutation is not automatically Eisenstein. The chosen component union must first be stable, so every $T_w$ is an actual endomorphism. Only then does (2.2) make sense in one image algebra. Component routing and Eisenstein localization solve different typing problems.

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
v(\det g)pmod2
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
\Gamma^v=G^1(F)\cap U^{1,v}, \tag{4.3}
$$

where $U^{1,v}$ is the part away from $v$ of the chosen level in the norm-one group. We impose no condition at $v$ in (4.3). Inside $\Gamma^v$ define

$$
\Gamma_0=\operatorname{Stab}([L_0]),
\qquad
\Gamma_1=\operatorname{Stab}([L_1]),
\qquad
\Gamma_e=\operatorname{Stab}([L_0],[L_1]). \tag{4.4}
$$

After conjugating $\Gamma_1$ by the chosen $h_v$, the quotients $\Gamma_0\backslash\mathfrak H$ and $\Gamma_1\backslash\mathfrak H$ are the two copies of the lower-level complex Shimura curve. The quotient $\Gamma_e\backslash\mathfrak H$ is the Iwahori-level curve. The inclusions $\Gamma_e\subset\Gamma_i$ induce its two degeneracy maps.

There is no orientation reversal in $\Gamma^v$. An element reversing the edge would exchange vertex types, but every norm-one element has determinant valuation zero under the chosen splitting. This matters in the cellular resolution: the edge stabilizer acts trivially on the chosen orientation module.

### 4.4 The one-edge quotient

We need the action of $\Gamma^v$ on $\mathscr T_v$ to have one edge as quotient. This is the precise strong-approximation input, so we prove the form being used.

**Theorem 4.2 (strong approximation in the required form).** Let $B/F$ be a quaternion algebra split at the distinguished real place. For every open compact $U^{1,v}\subset G^1(\mathbf A_f^v)$, the projection of

$$
G^1(F)\cap U^{1,v}
$$

to $G^1(F_v)\simeq\operatorname{SL}_2(F_v)$ is dense. Consequently $\Gamma^v$ is transitive on edges of $\mathscr T_v$ and on vertices of each type, and

$$
\Gamma^v\backslash\mathscr T_v
$$

is a single closed edge with its two endpoints.

**Proof.** We give the approximation argument for the norm-one quaternion group. Choose finitely many places $S$ containing $v$, every place at which the prescribed compact open is not maximal, and the distinguished split real place. The affine quadric

$$
Q(x)=\operatorname{Nrd}(x)=1 \tag{4.5}
$$

has the rational point $1$. Projection from this point gives a rational parametrization on the complement of the tangent hyperplane: if $z$ lies in the trace-zero subspace and $1-Q(z)\ne0$, then

$$
c(z)=(1+z)(1-z)^{-1} \tag{4.6}
$$

has reduced norm one, and every element with $-1$ not an eigenvalue is obtained in this way. Formula (4.6) is the quaternionic Cayley transform.

Let $g_v\in G^1(F_v)$ and let $W_v$ be a neighborhood of it. At every place of $S\setminus\{v\}$ choose an open subset of the prescribed factor of $U^{1,v}$, and at every finite place outside $S$ use the maximal norm-one compact. Lemma 4.3 below produces a rational norm-one element in all of these sets. It therefore belongs to $G^1(F)\cap U^{1,v}$ and its $v$-component belongs to $W_v$. Since $g_v$ and $W_v$ were arbitrary, the required projection is dense.

The stabilizer in $\operatorname{SL}_2(F_v)$ of a vertex or edge is open. Density therefore implies that every translate of $[L_0]$, $[L_1]$, or their edge under $\operatorname{SL}_2(F_v)$ is already a translate under $\Gamma^v$. The local transitivity from Section 4.1 gives the asserted quotient. $\square$

The denominator-reduction argument is exactly where the split real place is used: it supplies a noncompact approximation place, so the rational Cayley parameter can be altered without being trapped in a compact global set. No assertion of strong approximation for a torus or for $B^\times$ modulo its derived group is being made.

We record more detail about the denominator step, both to fix its scope and to prevent a common misuse of weak approximation. The needed statement is the following integral approximation lemma.

**Lemma 4.3 (integral norm-one approximation).** Let $S$ contain one place at which $B$ is split and noncompact, together with all finite places at which an order or level condition is prescribed. Given open subsets

$$
W_s\subset\operatorname{SL}_1(B)(F_s)
\quad(s\in S)
$$

and maximal compact norm-one subgroups $K_r$ for finite $r\notin S$, there is $g\in\operatorname{SL}_1(B)(F)$ such that

$$
g\in W_s\quad(s\in S),
\qquad
g\in K_r\quad(r\notin S). \tag{4.7}
$$

**Proof.** Choose a maximal order $\mathcal R$ outside $S$. We first solve the approximation problem with a bounded denominator ideal $\mathfrak a$ supported outside $S$. This follows from the Cayley chart (4.6) and additive weak approximation in the trace-zero vector space: after clearing the finitely many denominators, one obtains $g_0$ of norm one which is integral outside $S\cup\operatorname{Supp}(\mathfrak a)$ and lies in the prescribed $W_s$.

Among all such solutions choose one for which

$$
D(g_0)=\sum_{r\notin S}
\max\{0,-\min v_r(\text{coordinates of }g_0)} \tag{4.8}
$$

is minimal. Suppose $D(g_0)>0$, and choose a prime $r$ at which a denominator remains. Multiplying by a scalar power of a uniformizer merely changes the reduced norm and is not allowed. Instead use the norm equation itself.

Let $m>0$ be the largest denominator exponent at $r$. Reduction of $\varpi_r^m g_0$ gives a nonzero element $\bar x$ of the quaternion algebra over $k_r$ with reduced norm zero. If the local quaternion algebra is division, an element of negative valuation cannot have norm valuation zero, so such an $r$ cannot occur. Thus the algebra is split and $\bar x$ has rank one. Choose rank-one matrices $\bar u,\bar z$ with

$$
\bar u\bar x=0,
\qquad
\bar x\bar z=0,
\qquad
\operatorname{tr}(\bar u\bar z)=1. \tag{4.9}
$$

Lift $\bar u,\bar z$ to trace-zero elements of the order. The split noncompact place in $S$ lets us use additive weak approximation to choose global lifts $u,z\in B(F)$ that satisfy (4.9) at $r$, are arbitrarily small at the prescribed places in $S$, and are integral elsewhere. Consider

$$
g(t)=(1+tu)g_0(1+tz) \tag{4.10}
$$

with $t\in F$ initially chosen to have valuation $m$ at $r$ and to be sufficiently small at $S$. The two first-order rank conditions in (4.9) cancel the leading denominator of $g_0$. Allow $t$ and one still-unused coefficient of $z$ to vary. The remaining scalar condition $\operatorname{Nrd}(g(t))=1$ cuts out an affine conic $C$ over $F$ in these two variables. It contains the rational point corresponding to $t=0$, and its linear term at the desired $r$-adic correction is the nonzero trace in (4.9). Hensel lifting therefore gives a smooth point $P_r\in C(F_r)$ with the required cancellation. At every other prescribed place take a point of $C$ arbitrarily close to the uncorrected rational point.

Projection from the rational point at $t=0$ identifies a dense open subset of $C$ with a dense open subset of the affine line: a line of slope $a$ through that point meets the conic in exactly one further point, whose two coordinates are rational functions of $a$ with coefficients in $F$. Choose local slopes representing $P_r$ and the selected points at the other prescribed places, avoiding the finitely many poles. Additive weak approximation chooses one $a\in F$ simultaneously close to those slopes. Substitution in the rational parametrization gives a global point of $C(F)$, so the norm equation holds exactly, while openness preserves every imposed congruence and the denominator cancellation at $r$.

The corrected element has norm one, remains in every $W_s$, is integral at all primes where $g_0$ was integral, and has strictly smaller denominator exponent at $r$. It introduces no new denominator because both correcting factors are integral away from $S\cup\{r\}$ and have unit reduced norm there. This contradicts minimality of (4.8). Hence $D(g_0)=0$, which proves (4.7). $\square$

The lemma is stated only for the simply connected norm-one group. For $B^\times$, reduced norm gives an additional ideal-class and sign obstruction, and the analogue of (4.7) is false without recording components. In Theorem 4.2 we first selected a connected norm-one component, exactly so that Lemma 4.3 applies.

There is also a useful algebraic consequence of the one-edge quotient. A group acting without inversion on a tree with fundamental domain one edge is the amalgamated product

$$
\Gamma^v\simeq\Gamma_0*_{\Gamma_e}\Gamma_1. \tag{4.11}
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

Here $r_i$ is restriction, with the second inclusion understood after the fixed conjugation identifying its vertex quotient with the lower-level curve.

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

There is a subtlety which must be settled before using a transfer formula. The Hecke representative at a place $w$ need not belong to $\Gamma^v$, so its conjugation is not automatically inner on $\Gamma^{v,\mathrm{ab}}$. The required invariance is an arithmetic fact about the clean norm-one level.

**Abelian congruence claim.** Every homomorphism from $\Gamma^v$ to a finite abelian $\ell$-group kills a principal congruence subgroup.

To prove the claim, enlarge a maximal order at $v$ and the split real place and write $\mathcal R_S^1$ for its norm-one $S$-units. The group $\Gamma^v$ is cut from $\mathcal R_S^1$ by finitely many congruence conditions. At a split finite place, Gaussian elimination expresses a sufficiently deep principal congruence element as a product of upper and lower elementary matrices. Over the $S$-integer order, rank-one ideals can obstruct a single elimination step; replacing the level ideal $\mathfrak a$ by $\mathfrak a^c$, where $c$ is the exponent of the finite ideal class group, makes all those ideals principal. Performing the factorization after a finite splitting field and multiplying its Galois conjugates descends it to the quaternionic inner form.

The elementary factors are commutators. Strong approximation supplies a global element whose component at the chosen split place is $h=\operatorname{diag}(a,a^{-1})$, with $a^2-1$ a unit, and which satisfies the fixed level elsewhere. Then

$$
[h,u_{12}(x)]=u_{12}((a^2-1)x),
\qquad
[h,u_{21}(x)]=u_{21}((a^{-2}-1)x). \tag{5.7}
$$

Thus, after increasing the exponent of $\mathfrak a$ once more, every elementary factor is a commutator in $\Gamma^v$. The diagonal remainder in Gaussian elimination is itself a product of four elementary matrices; direct multiplication of the standard upper--lower--upper--lower factorization verifies this. Consequently there is a nonzero ideal $\mathfrak b$ away from $S$ such that

$$
\Gamma^v(\mathfrak b)\subset[\Gamma^v,\Gamma^v]. \tag{5.8}
$$

Every homomorphism to an abelian group kills the right side, proving the claim. Notice that only abelian quotients have been treated; no assertion that every finite-index subgroup is congruence is required.

**Lemma 5.2 (arithmetic abelianization).** Assume the level is neat and hyperspecial at the coefficient place, and that every finite stabilizer or deck quotient used to descend the chosen level has order prime to $\ell$. For a finite $\mathcal O$-module $A$ with trivial $\Gamma^v$-action, every homomorphism

$$
\chi:\Gamma^v\longrightarrow A
$$

is invariant under the away-from-$v$ Hecke commensurator, modulo the reduced-norm central character. In the norm-one, trivial-central block the latter character is zero.

**Proof strategy.** Strong approximation lets global commutators approximate the local elementary commutators. The only abelian quotients left after those commutators are the center and the explicitly excluded stabilizer quotients.

**Proof.** Because $A$ is finite, $\ker\chi$ has finite index. Its closure in every compact local factor is therefore open. At a split hyperspecial place $r$, reduction modulo $r$ gives $\operatorname{SL}_2(k_r)$. For $|k_r|>3$, this group is generated by the elementary matrices and is perfect modulo its center. The successive congruence kernels are generated by

$$
u_{12}(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},
\qquad
u_{21}(x)=\begin{pmatrix}1&0\\x&1\end{pmatrix}. \tag{5.9}
$$

Choose a unit $a$ such that $a^2-1$ is a unit. The identities

$$
\left[
\begin{pmatrix}a&0\\0&a^{-1}\end{pmatrix},u_{12}(x)
\right]
=u_{12}((a^2-1)x), \tag{5.10}
$$

and its lower-triangular analogue show that every sufficiently deep elementary generator is a commutator. At the finitely many small residue fields, enlarge the excluded stabilizer set; in the coefficient range $\ell\ge7$ their orders are units.

At a division place, the first congruence subgroup is pro-$p_r$. It has no nonzero homomorphism to an $\ell$-primary module when $p_r\ne\ell$. At the coefficient place, the hyperspecial split calculation (5.9)--(5.10) applies and $\ell\ge5$ makes the residual special linear group perfect modulo its order-two center. Thus no local noncentral $\ell$-primary character remains.

By the abelian congruence claim, $\chi$ kills some principal congruence subgroup. Strong approximation in the form of Lemma 4.3 then lifts every local elementary commutator modulo that subgroup. Hence $\chi$ kills every noncentral local generator. Since those generators and the center generate every finite congruence quotient of a Hecke commensurator intersection, $\chi$ factors through the reduced-norm center and the finite level stabilizers. The latter have prime-to-$\ell$ order by hypothesis. In the norm-one trivial-central block the former is trivial. Conjugation by an away-from-$v$ Hecke representative therefore fixes $\chi$. $\square$

We can now compute the operator. Let $w\notin\Sigma$ and choose a double coset

$$
K_wg_wK_w=\coprod_{i=1}^{d_w}g_iK_w,
\qquad d_w=q_w+1. \tag{5.11}
$$

The Hecke action on group cohomology is restriction to the intersection subgroup, conjugation by $g_w$, and corestriction. For a character $\chi:\Gamma^v\to A$, choose right-coset representatives $a_i$ for the corresponding finite-index subgroup. For every $\gamma\in\Gamma^v$, write

$$
a_i\gamma=\gamma_i a_{\sigma_\gamma(i)}, \tag{5.12}
$$

where $\gamma_i$ lies in the subgroup on which the conjugated character is evaluated. The transfer formula is

$$
(T_w\chi)(\gamma)=\sum_i\chi(g_w\gamma_i g_w^{-1}). \tag{5.13}
$$

Lemma 5.2 permits removal of the outer conjugation. Taking the product of (5.12) over the cycles of the permutation $\sigma_\gamma$ makes the $a_i$ telescope. In the abelianization one obtains

$$
\sum_i[\gamma_i]=d_w[\gamma]. \tag{5.14}
$$

Consequently

$$
T_w\chi=d_w\chi=(q_w+1)\chi. \tag{5.15}
$$

A central one-coset correspondence conjugates nothing and acts as the chosen central character; it is the identity in the block fixed in Section 2.4.

**Proposition 5.3 (Eisenstein character module).** The Hecke action on $H^1(\Gamma^v,A)$ is annihilated by the Eisenstein ideal $\mathfrak E$ of (2.2).

**Proof.** Equation (5.15) gives $T_w-(q_w+1)=0$ for every $w\notin\Sigma$. The central convention gives $S_w-1=0$. These elements generate $\mathfrak E$. $\square$

The prime-to-$\ell$ level condition in Lemma 5.2 is not cosmetic. Without it, a local stabilizer character can transform nontrivially under the commensurator, and the assertion that conjugation “has no effect” would be false. The clean theorem either works at neat level throughout or descends through a quotient whose order is a unit.

## 6. Geometric Ihara injectivity

### 6.1 Complex uniformization and comparison

For a chosen connected component, complex uniformization gives

$$
X_U(\mathbf C)\simeq\Gamma_0\backslash\mathfrak H,
\qquad
X_{U_0(v)}(\mathbf C)\simeq\Gamma_e\backslash\mathfrak H, \tag{6.1}
$$

and the conjugate lower component is $\Gamma_1\backslash\mathfrak H$. Neatness makes the groups torsion-free. The upper half-plane is contractible, so each quotient is a classifying space for its arithmetic group. Hence

$$
H^1(X_U(\mathbf C),A)\simeq H^1(\Gamma_0,A),
$$

$$
H^1(X_{U_0(v)}(\mathbf C),A)\simeq H^1(\Gamma_e,A). \tag{6.2}
$$

For $A=k$, the comparison theorem between singular and finite étale cohomology gives

$$
H^1(X(\mathbf C),k)\simeq
H^1(X_{\overline F},k). \tag{6.3}
$$

The isomorphism is functorial for finite maps, so it respects degeneracy pullback and every algebraic Hecke correspondence. Thus the tree calculation is a geometric cohomology calculation, not merely a calculation on an unrelated group.

### 6.2 The degeneracy map as restriction

Under (6.2), pullback along the finite covering induced by $\Gamma_e\subset\Gamma_0$ is restriction $r_0$. For the second degeneracy map, right translation by $h_v$ first identifies the source with the conjugate vertex quotient and then forgets level; its pullback is $r_1$ after conjugation. Therefore

$$
d_k=(r_0,r_1):
H^1(\Gamma_0,k)\oplus H^1(\Gamma_1,k)
\longrightarrow H^1(\Gamma_e,k), \tag{6.4}
$$

up to the harmless sign on the second summand already discussed.

Every away-from-$v$ Hecke correspondence is defined by changing level at a different finite place. It commutes with both inclusions and with the conjugation at $v$. The identifications (6.2)--(6.4) are therefore Hecke equivariant.

### 6.3 The Eisenstein kernel theorem

**Theorem 6.1 (geometric Eisenstein kernel).** For every finite quotient $A$ of $\mathcal O$, the kernel of

$$
d_A:H^1(X_U,A)^{\oplus2}\longrightarrow
H^1(X_{U_0(v)},A) \tag{6.5}
$$

is a quotient of $H^1(\Gamma^v,A)$ and is annihilated by $\mathfrak E$. More precisely, after the fixed identification of the two lower vertex quotients,

$$
\ker d_A=
\operatorname{im}\left(
H^1(\Gamma^v,A)\longrightarrow
H^1(\Gamma_0,A)\oplus H^1(\Gamma_1,A)
\right). \tag{6.6}
$$

**Proof strategy.** The tree identifies the relation between the two pullbacks. The double-coset transfer then identifies its Hecke character.

**Proof.** The one-edge quotient of Theorem 4.2 permits application of Theorem 5.1. Exactness gives (6.6), with a sign change on the second summand if (6.5) is written as a sum. Proposition 5.3 says that the source of the right side is annihilated by $\mathfrak E$. Its image, hence the kernel, is annihilated by the same ideal. Comparison and uniformization identify this group-cohomological map with the geometric degeneracy map. $\square$

The theorem includes the entire kernel, not merely its semisimplification. An extension of Eisenstein characters remains annihilated by the displayed operators because the calculation (5.15) is an equality on the full character module.

It is helpful to compare (6.6) with the amalgam (4.11). A character on $\Gamma^v$ is exactly a pair of characters $(\chi_0,\chi_1)$ on $\Gamma_0$ and $\Gamma_1$ whose restrictions to $\Gamma_e$ agree. Replacing $\chi_1$ by $-\chi_1$ turns agreement into the relation

$$
r_0\chi_0+r_1(-\chi_1)=0.
$$

Thus no relation is lost in passing from group presentations to cohomology. The tree theorem says that a reduced alternating word supplies every relation in the amalgam, while the Hecke calculation says that abelianizing such words erases all cuspidal information and leaves only degree.

There is a Jacobian version. For $A=\mathbf Z/\ell^n\mathbf Z$, Kummer theory identifies

$$
H^1(X,A(1))\simeq J_X[\ell^n](\overline F). \tag{6.8}
$$

Twisting Theorem 6.1 therefore shows that the $\ell$-primary subgroup of the geometric kernel of

$$
J_U\times J_U\xrightarrow{\delta}J_{U_0(v)}
$$

is Eisenstein. Indeed a point of order $\ell^n$ in the kernel gives a class in the kernel with $A(1)$ coefficients, and the Tate twist changes only the Galois action, not the geometric Hecke transfer. Conversely every such cohomology class is a torsion point. Hence

$$
\ker(\delta)[\ell^\infty]_{\mathfrak m}=0. \tag{6.9}
$$

This does not say the full finite kernel is trivial. It says that its part visible to the chosen coefficient localization vanishes. Prime-to-$\ell$ kernel is irrelevant to saturation of an $\mathcal O$-lattice, while Eisenstein $\ell$-torsion has been explicitly isolated.

### 6.4 The mod-$\ell$ Ihara theorem

**Corollary 6.2 (mod-$\ell$ Ihara injectivity).** Let $\mathfrak m$ be a non-Eisenstein maximal ideal of the Hecke image on the two curve cohomology groups. Then

$$
\bar d_{\mathfrak m}:
H^1(X_U,k)_{\mathfrak m}^{\oplus2}
\longrightarrow
H^1(X_{U_0(v)},k)_{\mathfrak m} \tag{6.7}
$$

is injective.

**Proof.** Localizing Theorem 6.1 at $\mathfrak m$ kills every module annihilated by $\mathfrak E$: one generator of $\mathfrak E$ is a unit in $\mathbb T_{\mathfrak m}$. Thus the localized kernel is zero. Exactness of localization identifies it with the kernel of the localized map. $\square$

No assumption that $q_v\not\equiv\pm1\pmod\ell$ is required for (6.7). Those congruences enter later when one wants a unique signed factor of the old Gram determinant or an integral projector onto one $U_v$ root. They are not part of geometric Ihara injectivity.

The result also survives finite coefficient extensions. If $k'/k$ is finite, tensoring (6.7) with $k'$ is exact and preserves injectivity. Conversely, faithful flatness of $k'/k$ shows that injectivity after extension implies injectivity before extension. One may therefore enlarge the residue field to contain Hecke eigenvalues without changing the theorem.

The same proof works for a finite product of connected Shimura components. The tree sequence is written for each component representative, and the component-routing permutation assembles the sequences into one induced module. A Hecke-stable orbit gives an endomorphism of the direct sum, while a single nonstable component gives only a map between two different summands. After the stable orbit is chosen, induction and restriction are exact and the Eisenstein-kernel calculation proceeds componentwise.

The use of constant coefficients is essential at one precise point: (5.5) identifies $H^1(\Gamma^v,A)$ with ordinary homomorphisms. For a nontrivial local system, one-cocycles are crossed homomorphisms and the arithmetic kernel need not be one-dimensional or Eisenstein. A type lattice can sometimes be incorporated by replacing Lemma 5.2 with a type-enhanced abelianization calculation, but that is new input, not a formal coefficient change.

## 7. Integral saturation

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

By (7.3), its reduction is the map in (6.7). It is injective. Lemma 3.1 therefore gives at once:

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

**Theorem 7.1 (saturated degeneracy theorem).** The sequence

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

The kernel before localization is not asserted to vanish. Theorem 6.1 permits arithmetic characters, and their $\ell$-torsion can make the global image nonsaturated. This is not a defect of the proof: it is the exact Eisenstein exception.

Nor can rational injectivity replace (6.7). The map

$$
R\xrightarrow{\ \pi\ }R
$$

is injective over $R$ and over $K$, but its reduction is zero and its cokernel is $R/\pi R$. The same elementary divisor can occur in a degeneracy lattice if one uses only a characteristic-zero old decomposition.

Finally, invertibility of the Gram determinant is sufficient for the old image to split orthogonally, but it is not necessary for saturation. At a level-raising congruence the Gram determinant is deliberately a nonunit. The old image is nevertheless primitive by Theorem 7.1; what fails is orthogonal splitting, and that failure is the congruence with the new lattice.

## 8. The Iwahori integral model

### 8.1 The incidence moduli problem

The tree proves injectivity on the generic curve. We now turn to the integral geometry that controls monodromy and components.

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
\begin{pmatrix}1&F^*\\F^*&1\end{pmatrix}. \tag{8.9}
$$

At a level-raising congruence this matrix can have a residual kernel. That does not mean the generic old map has a kernel. A class vanishing on the normalizations can survive in the gluing cohomology $H^1(\Gamma,k)$ or in the vanishing-cycle quotient. The tree argument proves that the complete generic class is nonzero; the semistable filtration identifies where the missing information lies. Looking only at the two normalized components discards the very graph class which rescues injectivity.

Nodes occur where the connected and étale descriptions meet. Let $\Sigma$ be the finite superspecial incidence set. Étale locally at a point of $\Sigma$, the two branches of the source have parameters $x$ and $y$, while a parameter $t$ on the smooth hyperspecial target pulls back, up to a unit, as

$$
\pi_0^*t=x+y^{q_v}+\text{higher terms},
$$

$$
\pi_1^*t=x^{q_v}+y+\text{higher terms}. \tag{8.10}
$$

On $y=0$ the first map is separable and the second is Frobenius; on $x=0$ the roles reverse. The higher terms do not alter generic branch degrees. Formula (8.10) is not needed to define the maps, but it checks simultaneously the table, the local degree $q_v+1$, and the exchange under the Atkin--Lehner involution.

### 8.4 Fine covers and coarse descent

The proof has been carried out at neat level. Suppose a finite group $\Delta$ acts on the fine model and the desired curve is its quotient. The universal isogeny and both degeneracy maps are $\Delta$-equivariant. If $|\Delta|$ is invertible in $\mathcal O$, the averaging idempotent

$$
e_\Delta=|\Delta|^{-1}\sum_{\delta\in\Delta}\delta \tag{8.8}
$$

makes invariants an exact functor. The tree sequence, cohomology, old map, and saturation theorem descend by applying $e_\Delta$.

At fixed points, the coarse special fiber can have quotient singularities even when the fine model is semistable. Component and monodromy calculations are then performed equivariantly on the fine graph before invariants are taken. Quotienting the unoriented graph first can lose a branch reversal and its sign.

If $\ell\mid|\Delta|$, (8.8) is unavailable. The invariant functor can have higher cohomology, and a stabilizer character can appear in the Ihara kernel. The clean theorem does not hide this failure; it requires a neat level or prime-to-$\ell$ descent.

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
\xrightarrow{\sum}A(-1)\to0, \tag{9.12}
$$

where $B_a$ is the set of branches on $\widetilde Y_a$. The last map is the sum of residues. Its kernel is free and is generated by differences of branch basis vectors. For a global oriented edge, the two branch residues must be opposite. Therefore a global residue assignment is an element $(r_e)\in A^E$ satisfying

$$
\sum_{t(e)=a}r_e-\sum_{o(e)=a}r_e=0
$$

at every vertex $a$. This is exactly $\partial r=0$, so the residue module is $H_1(\Gamma,A)(-1)$.

Choose local classes realizing these residues by exactness of (9.12). On the overlap annuli, two choices differ by a class extending over the node. Adjusting by component classes glues them. If a multiple $\varpi z$ glues, the incidence matrices in the adjustment equations are totally unimodular, so $z$ glues as well. Hence the image in (9.5) is saturated. This gives a direct integral proof of the freeness asserted after (9.7), independent of a rational degeneration argument.

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
2\sum_ag_a+2b=2g(C), \tag{9.13}
$$

because the arithmetic genus of the special fiber is $\sum g_a+b$. Thus no cohomology rank is missing from the filtration.

### 9.4 The monodromy pairing

Give each geometric edge its thickness $n_e$. For the model of Theorem 8.1, $n_e=1$; after ramified base change it need not be. Define

$$
q_\Gamma(a,b)=\sum_{e}n_ea_eb_e,
\qquad a,b\in H_1(\Gamma,\mathbf Z). \tag{9.8}
$$

This positive definite pairing induces

$$
q_\Gamma:H_1(\Gamma,A)
\longrightarrow H_1(\Gamma,A)^\vee. \tag{9.9}
$$

Cellular duality identifies

$$
H_1(\Gamma,A)^\vee=H^1(\Gamma,A). \tag{9.10}
$$

The logarithm of tame inertia on (9.6) is zero on $W_1$ and factors as

$$
H^1(C,A)\twoheadrightarrow
H_1(\Gamma,A)(-1)
\xrightarrow{q_\Gamma}
H^1(\Gamma,A)(-1)
\hookrightarrow H^1(C,A)(-1). \tag{9.11}
$$

**Proof of the factorization.** At a node $xy=\pi_v^{n_e}$, a tame loop changes a branch Kummer logarithm by $n_e$ times the tame character. A class with residue $a_e$ therefore acquires the graph cocycle whose pairing with a second residue vector $b$ is $n_ea_eb_e$. Summing over nodes gives (9.8). Classes extending across the special fiber have zero residues, so monodromy kills $W_1$. This proves (9.11). $\square$

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

The proof is the separated Picard calculation: vertical divisors change multidegrees by the graph Laplacian, while normalization identifies the torus character group with graph cycles. Resolving a thick node subdivides its edge and turns the unit pairing into (9.8). These are exactly the hypotheses established for $\mathscr C$.

Tensoring (10.3) with $\mathbf Z_\ell$ gives

$$
\Phi_C(\bar k_v)[\ell^\infty]
\simeq
\operatorname{coker}left(
q_\Gamma:X_\Gamma\otimes\mathbf Z_\ell
\to X_\Gamma^\vee\otimes\mathbf Z_\ell
\right). \tag{10.5}
$$

Thus the integral defect of monodromy in (9.11) and the $\ell$-primary component group are the same finite module.

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
\end{cases} \tag{10.11}
$$

Expansion after subtracting one row shows

$$
\det Q=
\sum_{j=1}^{m}\prod_{i\ne j}n_i. \tag{10.12}
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

**Lemma 10.1 (proper source versus graph torus).** Let $\mathcal A/R_v$ be an abelian scheme and $u:\mathcal A\to\mathcal J$ a homomorphism to the Néron model of a semistable Jacobian. On the geometric special fiber, the induced map has zero component in the torus $T_\Gamma$. Equivalently, on the filtration (9.6), the cohomological image of $u$ has zero projection to $W_0$ and to $W_2/W_1$.

**Proof.** The image $H$ of the proper connected group $\mathcal A_{\bar k_v}$ in the separated group $\mathcal J_{\bar k_v}^0$ is proper and connected. Its maximal connected affine subgroup is therefore trivial: a proper connected affine group over a field has a coordinate ring which is both finite-dimensional and a domain, hence it is a point. Thus $H$ is an abelian variety and has toric rank zero. Its intersection with $T_\Gamma$ can be finite, but it has bounded exponent and contributes nothing to an inverse system of prime-to-$v$ Tate modules.

Functoriality of the semiabelian filtration now says that the map from the good-reduction source has zero map on torus character and cocharacter lattices. Those lattices give the bottom and top graph pieces of (9.6), dually. Hence the cohomological image has zero projection to both extreme graded pieces. $\square$

Apply the lemma to each $\pi_i^*:J_U\to J_C$. The old lattice lies in the normalized-component layer. This is the geometric reason the graph monodromy is genuinely new; it cannot be supplied by good-reduction old classes.

### 10.4 The localized component-control theorem

Let $Q^{\mathrm{new}}_{\mathfrak m}$ be (7.7). Intersect the filtration (9.6) with $N_{\mathfrak m}$ and pass to the quotient by the saturated old image. Lemma 10.1 shows that the extreme graph pieces are unchanged.

**Theorem 10.2 (component control).** The torsion-free module $Q^{\mathrm{new}}_{\mathfrak m}$ has a canonical Hecke- and Galois-stable filtration whose extreme graded pieces are

$$
\operatorname{gr}_0Q^{\mathrm{new}}_{\mathfrak m}
=H^1(\Gamma,\mathcal O)_{\mathfrak m}, \tag{10.8}
$$

$$
\operatorname{gr}_2Q^{\mathrm{new}}_{\mathfrak m}
=H_1(\Gamma,\mathcal O)_{\mathfrak m}(-1). \tag{10.9}
$$

The induced monodromy map between them is $q_\Gamma$, and

$$
\operatorname{coker}(q_\Gamma)_{\mathfrak m}
\simeq
\Phi_C(\bar k_v)[\ell^\infty]_{\mathfrak m}
\otimes_{\mathbf Z_\ell}\mathcal O. \tag{10.10}
$$

No further finite module is introduced by quotienting by the old lattice.

**Proof.** The filtration of $N$ is integral with free graded pieces by Sections 9.2--9.3. Lemma 10.1 places $N^{\mathrm{old}}$ entirely in the middle layer and gives zero intersection with the bottom graph layer. Because the old image is saturated in $N$, its intersections with the filtration steps are saturated: if $\pi x$ lies in the intersection and $x$ lies in the filtration step, saturation in $N$ gives $x$ in the old image. Passing to the quotient is therefore exact and creates no torsion. The two extreme pieces remain (10.8)--(10.9).

Monodromy commutes with every degeneracy and Hecke map. It is zero on old classes because the lower curve has good reduction. Its induced map on the quotient is consequently the same graph map (9.11). The component identification (10.10) is (10.5) after localization and coefficient extension. Since the quotient was formed by a primitive submodule, there is no additional saturation cokernel. $\square$

The theorem does not claim that the localized component group vanishes. At a level-raising prime it can be nonzero and can carry the desired non-Eisenstein system. What is controlled is its exact origin: it is the discriminant of the new monodromy lattice, not torsion accidentally created by the old quotient.

There is a useful diagrammatic restatement. Let $X_\ell=X_\Gamma\otimes\mathcal O$ and write $Q=Q^{\mathrm{new}}_{\mathfrak m}$. The extreme part of its filtration fits into

$$
\begin{array}{ccccccccc}
0&\to&X_{\ell,\mathfrak m}&\to&X_{\ell,\mathfrak m}^\vee&\to&\Phi_{\mathfrak m}&\to&0\\
&&\downarrow&&\downarrow&&\Vert&&\\
0&\to&\operatorname{gr}_2Q(1)&\xrightarrow{N_{\mathrm{mon}}}&
\operatorname{gr}_0Q&\to&\Phi_{\mathfrak m}&\to&0.
\end{array} \tag{10.13}
$$

The vertical arrows are the residue and specialization identifications. Away-from-$v$ Hecke operators act on both rows and transpose the two lattice arrows under the discriminant pairing. Formula (10.13) is the precise bridge between vanishing cycles and Néron components.

Suppose one had used the unsaturated quotient $N/A$ for an arbitrary old submodule $A$. Its torsion $A^{\mathrm{sat}}/A$ would sit beside $\Phi$ in the lower-right corner, and a residual class could not be assigned uniquely to monodromy or to old-index torsion. Theorem 7.1 removes that extra term. This is the exact mathematical content of the phrase “component-group control.”

Consider explicitly the frequent case in which $Y=Y_0\cup Y_1$ and the two components meet at $m$ unit nodes. Let an away-from-$v$ self-correspondence act on vertex divisors through

$$
A_T=\begin{pmatrix}a&b\\b&a\end{pmatrix}. \tag{10.14}
$$

The row sum $a+b$ is the degree on the total fiber. On the degree-zero generator $Y_0-Y_1$, however,

$$
A_T(Y_0-Y_1)=(a-b)(Y_0-Y_1). \tag{10.15}
$$

Since $\Phi\simeq\mathbf Z/m\mathbf Z$, the component action is multiplication by $a-b$ modulo $m$. Two correspondences with the same degree can therefore have different component actions. Total degree cannot replace the graph calculation.

The involution exchanging the two components acts by $-1$ on $Y_0-Y_1$ and hence by $-1$ on $\Phi$. On the cycle lattice it reverses the orientation of each path from one vertex to the other and is again adjoint to itself. This is a complete check of the sign in the discriminant pairing.

Suppose instead that Frobenius exchanges the two components and permutes the $m$ edges. A geometric generator of $\Phi$ need not be rational. One first computes the signed permutation on the cycle basis, then passes to the cokernel, and only then takes fixed points. Taking the quotient graph first produces one vertex with loop orbits and can change the answer because edge stabilizers and orientation reversal have been forgotten.

The component theorem also controls specialization of divisor classes. If $P$ and $Q$ are sections reducing to smooth points on $Y_0$ and $Y_1$, then

$$
\operatorname{sp}([P-Q])=[Y_0-Y_1]\in\Phi. \tag{10.16}
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

then the residual vector $(1,-\varepsilon)$ lies in the kernel of the Gram matrix. It does **not** lie in the kernel of $d$: Corollary 6.2 says that its image is nonzero at a non-Eisenstein localization. Rather, its image is orthogonal modulo $\varpi$ to the old image. This is the seed of a congruence with the new quotient.

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

If $q_v\equiv-1\pmod\ell$, both signed factors can be nonunits. The full determinant then no longer measures one chosen branch. Geometric Ihara and saturation still hold, but a signed level-change theorem requires a refined $U_v$-selected calculation.

### 11.4 Why a determinant is not an Ihara proof

There are three regimes.

If $\Delta_v$ is a unit, the old image is an orthogonal direct summand. The inverse of the Gram matrix gives an integral projector. This is stronger than saturation but contains no level-raising congruence.

If $\Delta_v$ is a nonzero nonunit, the old image may be saturated while failing to split orthogonally. This is the desired congruence regime. The map $R\to R^2$, $x\mapsto(x,x)$, is primitive although the Gram determinant for a suitably scaled pairing can be a nonunit; splitting and primitivity are different questions.

If $\Delta_v=0$ on a characteristic-zero summand, the two old vectors are rationally dependent. Such a summand is scalar or one-dimensional in the clean quaternionic setting and belongs to the Eisenstein exception. Its exclusion follows from Theorem 6.1, not from formally canceling a zero determinant.

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

**Theorem 12.1 (new quotient duality).** The map (12.3) is an isomorphism. In particular both $Q_{\mathfrak m}$ and $N^{\perp}_{\mathfrak m}$ are finite free of the same rank.

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

Thus monodromy descends to $Q_{\mathfrak m}$. Theorem 10.2 identifies its extreme graded pieces and says that the descended operator is the graph pairing.

There are two immediate consequences.

First, every nonzero graph cycle in the localized quotient gives a length-two monodromy block after tensoring with $E$. The old subspace cannot contain such a block.

Second, the failure of this monodromy map to be an integral isomorphism is precisely

$$
\Phi_C[\ell^\infty]_{\mathfrak m}. \tag{12.6}
$$

There is no unnamed congruence module between (12.5) and (12.6). Saturation has removed the only additional finite quotient that the old lattice could create.

This is the form of component control needed in level lowering. A residual class killed by monodromy can be compared with the lower-level image without mistaking old-quotient torsion for a component class. Any remaining finite obstruction is visible in the explicit discriminant group (10.3).

One can also see directly how a Gram-kernel vector enters the orthogonal new reduction. Let $x\in M^2$ have nonzero reduction and suppose

$$
Gx\in\varpi(M^2)^\vee. \tag{12.7}
$$

Surjectivity of $d^*$ from (11.12) supplies $z\in N$ with

$$
d^*z=\varpi^{-1}Gx. \tag{12.8}
$$

Then

$$
y=d(x)-\varpi z
$$

satisfies $d^*y=0$, so $y\in N^\perp$. Modulo $\varpi$,

$$
\bar y=\overline{d(x)}. \tag{12.9}
$$

Ihara injectivity makes the right side nonzero. Thus a nonzero Gram-kernel vector produces a nonzero new residual class. Saturation guarantees that this class is the reduction of a free new lattice rather than the boundary of torsion in $Q$. This calculation explains why both injectivity and saturation are needed even though they arise from the same residual criterion in the clean curve setting.

If (12.7) holds only after multiplying $x$ by a denominator, the construction fails integrally. Likewise, if $d^*$ is not surjective because the old image is not primitive, (12.8) may have no solution. These are not technical inconveniences; they are the two precise ways a rational level-raising argument can fail to produce an integral new class.

Assume now that $x$ is an eigenvector and (11.6) holds. Choosing

$$
x_\varepsilon=(x,-\varepsilon x)
$$

makes (12.7) equivalent to divisibility of $c_v^\varepsilon$. If the companion factor is a unit, the Gram cokernel on this eigenplane is cyclic with length

$$
\operatorname{ord}_\varpi c_v^\varepsilon.
$$

The construction (12.8)--(12.9) then produces a residual orthogonal class of the selected sign. Notice the order of the argument: Ihara first proves $d(x_\varepsilon)\not\equiv0$; perfectness moves its Gram divisibility into the orthogonal kernel; saturation proves that the quotient carrying the class is free. Reversing this order would use the desired new class to justify its own integrality.

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

Ramified base change does not affect Ihara injectivity on the characteristic-zero generic curves: the tree and its arithmetic groups are attached to the original level-changing place. What changes is the integral model used to read monodromy. The cycle lattice remains canonically the same after subdivision, while $q$ is multiplied by $e$. Thus saturation of the old cohomology image and enlargement of the component group are compatible and independent phenomena.

### 13.3 Stabilizers and small coefficient primes

At neat level, the analytic and algebraic curves have no stabilizers. At tame nonneat level, choose a normal neat cover with deck group $\Delta$. If $\ell\nmid|\Delta|$, transfer followed by pullback is $|\Delta|$, a unit, and invariants are exact. Every theorem descends.

If $\ell\mid|\Delta|$, three failures can occur:

1. $H^1(\Delta,k)$ contributes extra classes to the quotient curve;
2. coarse trace can contain a nonunit stabilizer factor;
3. a primitive image upstairs can become nonprimitive after taking nonexact invariants.

For the fine rational quaternionic levels used in the clean coefficient range, possible effective projective stabilizers have orders supported at small primes, and $\ell\ge7$ avoids them. Over a general totally real datum one should not replace the explicit prime-to-$\ell$ stabilizer condition by a numerical slogan; neatness is the uniform safe hypothesis.

The prime $\ell=2$ also changes signs in the tree map: $r_0-r_1$ and $r_0+r_1$ become identical, and branch reversal is invisible modulo two. The uniform theorem is intentionally stated for $\ell\ge7$. At $\ell=3$ or $5$, the fine constant-coefficient tree calculation can remain valid, but arithmetic abelianization, coarse descent, and type lattices require separate small-prime checks.

### 13.4 Scalar, Eisenstein, and vexing cases

The Eisenstein localization is essential. Arithmetic characters of $\Gamma^v$ give actual relations between the two degeneracy pullbacks, and Theorem 6.1 says precisely that these are the only relations. At an Eisenstein maximal ideal, (6.7) can fail and the old quotient can have torsion. No conclusion of the clean theorem is asserted there.

The congruences $q_v\equiv1$ and $q_v\equiv-1\pmod\ell$ are different exceptional phenomena.

If $q_v\equiv1$, the two residual roots $\varepsilon$ and $\varepsilon q_v$ of the old $U_v$ polynomial collide. The unramified residual representation can be scalar, so an ordered Frobenius line is not intrinsic. Geometric Ihara still proves saturation of the full two-map image, but it does not produce a canonical integral projector onto one branch.

If $q_v\equiv-1$, the two roots $\varepsilon$ and $-\varepsilon$ remain distinct for odd $\ell$, but both signed Gram factors in (11.7) can vanish. The valuation identity (11.8) fails. A $U_v$-selected determinant calculation can distinguish the branches, but the unselected Gram determinant cannot.

A **vexing** local datum is one in which the residual scalar or ramified type admits more than one integral lattice or flag with the same unlabelled reduction. The constant-coefficient Ihara theorem controls the full cohomology lattice; it does not assert that an independently chosen type projector has saturated image. Such a case requires the type-enhanced level structure and its own prime-to-stabilizer hypotheses. Primitive wild supercuspidal types are outside the catalog scope.

It is useful to summarize the exceptional cases as failures of exact statements rather than as labels.

| Situation | Statement that can fail | Statement that remains valid under the other hypotheses |
|---|---|---|
| Eisenstein localization | residual injectivity and saturation | tree identification of the kernel |
| $\ell$-divisible stabilizer | exact descent from a fine cover | fine-level Ihara theorem |
| $q_v\equiv1\pmod\ell$ | integral separation of the two old $U_v$ roots | full two-map saturation |
| $q_v\equiv-1\pmod\ell$ | one-factor valuation formula | full Gram matrix and saturation |
| ramified base change | unit edge lengths and unchanged component group | subdivision-invariant cycle lattice |
| nonstable component | endomorphism of one factor | correspondence between the routed factors |

This table prevents two opposite mistakes. One must not discard the full Ihara theorem merely because a branch projector fails; but one must not use full-image saturation as if it supplied the missing labelled branch.

The coefficient-prime equality $v\mid\ell$ is more serious. The analytic tree still exists, but the integral geometric comparison changes: the $v$-power torsion of the Jacobian is finite flat rather than étale, Kummer residues no longer produce a free $\mathbf Z_\ell$ local system in the same way, and connected group schemes can contribute. The present component and saturation package is therefore deliberately prime-to-$v$.

## 14. The saturated Ihara package

### 14.1 Main theorem

We collect the exact result proved in this book.

**Theorem 14.1 (geometric Ihara, saturation, and components).** Let $F$, $B$, $U$, $v$, $U_0(v)$, $\mathcal O$, and $\mathfrak m$ satisfy the following hypotheses:

1. $F$ is totally real and $B/F$ is a division quaternion algebra split at exactly one real place;
2. the chosen Shimura component union is proper, stable under the relevant correspondences, and represented at a neat level, or obtained from such a level by a quotient of order prime to $\ell$;
3. $B$ is split at $v$, $U_v$ is hyperspecial, and $U_0(v)_v$ is the standard Iwahori;
4. the PEL datum at $v$ is unramified with self-dual lattice and verified flat rank-two incidence local model;
5. $\ell\ge7$, $v\nmid\ell$, and $\mathcal O$ is a finite extension of $\mathbf Z_\ell$;
6. the central character is trivial on the selected connected block, with $T_w,S_w$ normalized as unnormalized right-double-coset operators;
7. $\mathfrak m$ is non-Eisenstein for the ideal (2.2).

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
6. the Iwahori model at $v$ is regular strict semistable with weighted dual graph $\Gamma$, and $Q_{\mathfrak m}$ inherits extreme monodromy pieces
   $$
   H^1(\Gamma,\mathcal O)_{\mathfrak m},
   \qquad
   H_1(\Gamma,\mathcal O)_{\mathfrak m}(-1);
   $$
7. monodromy between those pieces is the weighted edge pairing $q_\Gamma$, and its cokernel is canonically
   $$
   \Phi_{J_{U_0(v)}}(\bar k_v)[\ell^\infty]_{\mathfrak m}
   \otimes_{\mathbf Z_\ell}\mathcal O;
   $$
8. all statements are equivariant for away-from-$v$ Hecke operators, transpose adjunction, and the signed residue Galois action.

In particular the localized old image is primitive, the integral new quotient has no torsion, and every remaining component obstruction is the explicit monodromy discriminant rather than an unmeasured saturation defect.

### 14.2 Proof of the main theorem

**Proof strategy.** The proof has four independent parts: the tree isolates the kernel; Hecke transfer makes it Eisenstein; DVR algebra turns residual injectivity into saturation; and the nodal model identifies the component module.

**Proof.** The lattice graph at $v$ is a tree by Proposition 4.1. Strong approximation, Theorem 4.2, makes its quotient by the $S$-arithmetic group a single edge. The tree Mayer--Vietoris sequence therefore identifies the kernel of the two restriction maps with the image of $H^1(\Gamma^v,k)$. Complex uniformization and cohomological comparison identify those restriction maps with $\pi_0^*$ and $\pi_1^*$.

For a character of $\Gamma^v$, the transfer formula telescopes in the abelianization and gives $T_w=q_w+1$ and $S_w=1$. Hence the kernel is Eisenstein. Localization at $\mathfrak m$ kills it, proving clause 1.

The two cohomology modules are finite free over $\mathcal O$ by the Riemann-surface cell calculation of Section 7.1. Lemma 3.1 applied to the localized map now proves injectivity and saturation, hence clauses 2 and 3. Perfect Poincaré duality and Lemma 3.2 prove clause 4. Pull--norm adjunction and the right-double-coset calculation prove clause 5.

The parahoric PEL local model has equation $xy=\pi_v$, so Theorem 8.1 gives the required regular semistable model. The normalization and nearby-cycle calculations give the free filtration (9.6)--(9.7). Since the lower Jacobian has good reduction, Lemma 10.1 shows that the old image has no graph-toric part. Passing through the saturated quotient therefore retains both extreme graph lattices. The local Kummer calculation identifies monodromy with $q_\Gamma$, proving clause 6 and the first part of clause 7. The Raynaud graph theorem identifies its cokernel with the Néron component group, finishing clause 7.

Correspondence extension, graph adjunction, and descent preserve each construction, proving clause 8. $\square$

### 14.3 Hypothesis and dependency ledger

The logical use of the five direct prerequisites is exact.

| Source | Imported result | Hypotheses retained | Work done here |
|---|---|---|---|
| Book 12 | nodal normalization, graph cycles, weighted pairing, discriminant component group, subdivision, finite-map adjunction | semistable curve; geometric graph; thickness and signed descent retained | application to the Iwahori quotient and proof that the old image does not alter the graph extremes |
| Book 39 | Néron mapping property, identity component, component group, semistable Jacobian, unramified base change | excellent DVR; henselianity where reduction is used; perfect residue field for fixed-point notation | localized component-control sequence for the saturated quotient |
| Book 41 | extension of pull--norm correspondences, transpose, specialization, graph and intersection maps | smooth proper generic curves; regular models; controlled resolved correspondence | simultaneous Hecke action and adjunction on the new and component lattices |
| Book 122 | Shimura degeneracy maps, right-coset orientation, old map, adjoints, Gram matrix framework | stable component union; fine or tame descent; unnormalized operators | proof of geometric injectivity and saturation, which Book 122 explicitly leaves open |
| Book 131 | rank-two parahoric PEL model, $xy=\pi_v$, strict semistability, graph monodromy, Hecke functoriality | verified flat incidence local model; neat level; prime-to-$v$ coefficients | integral filtration after quotienting by the primitive old image and exact component discriminant |

The strong-approximation statement, tree Mayer--Vietoris sequence, Hecke calculation on arithmetic characters, residual Ihara theorem, and saturation criterion were proved in this book. No class-field-theoretic or density theorem for Frobenius elements is used. No automorphic decomposition, multiplicity-one theorem, local newvector theorem, or modularity argument enters the proof.

### 14.4 Exact boundary of the theorem

The theorem proves the clean full-Iwahori two-map statement. It does not silently imply stronger variants.

At an Eisenstein maximal ideal, the $S$-arithmetic character module can survive and residual injectivity can fail. At a nonneat quotient with $\ell$-divisible stabilizers, group cohomology of the stabilizer can add a kernel. At $q_v\equiv1\pmod\ell$, the full old image remains saturated, but an ordered $U_v$ branch need not be defined integrally. At $q_v\equiv-1\pmod\ell$, both signed Gram factors can be nonunits, so one determinant does not measure one sign. These cases require additional labelled or type-enhanced data.

The theorem concerns constant first cohomology of the compact quaternionic Shimura curves with the verified rank-two local model. It does not cover deeper parahoric chains, primitive wild supercuspidal type projectors, nonflat determinant loci, boundary cohomology of noncompact curves, or coefficient characteristic equal to the residue characteristic at $v$.

Nor does torsion-freeness produce a canonical integral direct-sum old--new decomposition. It produces the quotient lattice and its perfect orthogonal dual. A direct summand requires the Gram determinant to be a unit, which is incompatible with the congruence regime in which level raising is used.

Finally, component control does not mean component-group vanishing. The localized component group can be nonzero. The theorem identifies it exactly as the discriminant of the weighted monodromy pairing on the new graph lattice and proves that no extra finite quotient is hidden in the old image.

## 15. Conclusion

### 15.1 The mathematical package

The two degeneracy maps are deceptively simple. They come from the two endpoints of one edge in the local lattice tree, but integrally their images can meet the new lattice in a congruence of positive index. The correct argument therefore begins before any determinant is computed.

The Bruhat--Tits tree turns the two pullbacks into a Mayer--Vietoris map. Its kernel is not guessed from dimensions: it is exactly the image of the first cohomology of the group with the $v$-level removed. In degree one that cohomology consists of additive arithmetic characters. The transfer formula calculates their full Hecke action and makes it Eisenstein. Non-Eisenstein localization kills the entire kernel, including its possible $\ell$-torsion.

Once residual injectivity is known, elementary divisor theory does the integral work. The old image is saturated, its quotient is free, and perfect duality identifies the orthogonal new lattice with the dual of that quotient. This remains true when the Gram determinant is a nonunit. The nonunit then records a genuine old--new congruence rather than torsion caused by a defective lattice.

The semistable model supplies the second half of the package. Its node $xy=\pi_v$ produces a geometric dual graph, graph cycles produce the torus in the special Jacobian, and edge thicknesses produce the integral monodromy pairing. The discriminant of that pairing is the Néron component group. Because the lower-level Jacobian has good reduction, old classes carry no graph-toric part. Passing to the saturated new quotient therefore preserves the graph extremes and their monodromy without creating another finite error term.

### 15.2 The role in integral level change

The final structure is a short exact sequence of free lattices

$$
0\longrightarrow M_{\mathfrak m}^{\oplus2}
\xrightarrow{d}N_{\mathfrak m}
\longrightarrow Q_{\mathfrak m}\longrightarrow0,
$$

its perfect adjoint dual

$$
\ker d^*_{\mathfrak m}\simeq Q_{\mathfrak m}^\vee,
$$

and the monodromy--component sequence

$$
0\longrightarrow H_1(\Gamma,\mathbf Z_\ell)_{\mathfrak m}
\xrightarrow{q_\Gamma}
H_1(\Gamma,\mathbf Z_\ell)_{\mathfrak m}^\vee
\longrightarrow\Phi[\ell^\infty]_{\mathfrak m}
\longrightarrow0.
$$

Each finite module now has one source and one meaning. The old quotient has no torsion. The failure of orthogonal splitting is measured by the Gram congruence. The remaining special-fiber torsion is the component discriminant. The exceptional kernel is Eisenstein and has been removed by a stated localization.

This is the saturated Ihara theory required for integral level change on the selected Shimura curves. It is strong enough to carry a residual congruence into a genuine torsion-free new lattice and precise enough to distinguish that congruence from scalar characters, stabilizer torsion, branch collisions, and Néron component classes.
