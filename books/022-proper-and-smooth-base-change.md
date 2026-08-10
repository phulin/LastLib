# Proper and Smooth Base Change

## Contents

1. [Cohomology moving in a family](#1-cohomology-moving-in-a-family)
   - [The comparison problem](#11-the-comparison-problem)
   - [Conventions and coefficient regimes](#12-conventions-and-coefficient-regimes)
   - [The four main theorems](#13-the-four-main-theorems)
   - [Comparison with coherent base change](#14-comparison-with-coherent-base-change)
2. [Geometric stalks and comparison maps](#2-geometric-stalks-and-comparison-maps)
   - [Strict localizations](#21-strict-localizations)
   - [The base-change morphism](#22-the-base-change-morphism)
   - [Specializations and their direction](#23-specializations-and-their-direction)
3. [Constructibility and finite cohomology](#3-constructibility-and-finite-cohomology)
   - [Why finiteness must precede comparison](#31-why-finiteness-must-precede-comparison)
   - [Absolute finiteness in the required range](#32-absolute-finiteness-in-the-required-range)
   - [Constructibility of direct images](#33-constructibility-of-direct-images)
   - [Uniform amplitude and complexes](#34-uniform-amplitude-and-complexes)
   - [What the finiteness hypotheses exclude](#35-what-the-finiteness-hypotheses-exclude)
4. [The reduction machinery](#4-the-reduction-machinery)
   - [Noetherian induction and dévissage](#41-noetherian-induction-and-dévissage)
   - [Compactification and the boundary](#42-compactification-and-the-boundary)
   - [Reduction to a strict henselian trait](#43-reduction-to-a-strict-henselian-trait)
   - [Why the reductions terminate](#44-why-the-reductions-terminate)
5. [The strict-local proper theorem](#5-the-strict-local-proper-theorem)
   - [The decisive comparison](#51-the-decisive-comparison)
   - [The curve calculation](#52-the-curve-calculation)
   - [Higher relative dimension](#53-higher-relative-dimension)
   - [Complexes and constructible coefficients](#54-complexes-and-constructible-coefficients)
6. [Proper base change](#6-proper-base-change)
   - [Finite torsion coefficients](#61-finite-torsion-coefficients)
   - [Arbitrary change of base](#62-arbitrary-change-of-base)
   - [Products, projection, and composition](#63-products-projection-and-composition)
   - [Failure without properness](#64-failure-without-properness)
   - [Three model base changes](#65-three-model-base-changes)
7. [Smooth base change](#7-smooth-base-change)
   - [Changing the base by a smooth morphism](#71-changing-the-base-by-a-smooth-morphism)
   - [The standard smooth-local calculation](#72-the-standard-smooth-local-calculation)
   - [Derived compatibility](#73-derived-compatibility)
   - [Étale, smooth, and universal changes](#74-étale-smooth-and-universal-changes)
8. [Local acyclicity](#8-local-acyclicity)
   - [Vanishing local change](#81-vanishing-local-change)
   - [Smooth morphisms with lisse coefficients](#82-smooth-morphisms-with-lisse-coefficients)
   - [Universal local acyclicity and its limits](#83-universal-local-acyclicity-and-its-limits)
9. [Specialization and locally constant direct images](#9-specialization-and-locally-constant-direct-images)
   - [Specialization maps](#91-specialization-maps)
   - [The smooth proper theorem](#92-the-smooth-proper-theorem)
   - [Monodromy and arithmetic actions](#93-monodromy-and-arithmetic-actions)
10. [Passage to adic coefficients](#10-passage-to-adic-coefficients)
   - [Finite-level control of the tower](#101-finite-level-control-of-the-tower)
   - [Integral and rational base change](#102-integral-and-rational-base-change)
   - [Specialization at the adic level](#103-specialization-at-the-adic-level)
   - [The derived-limit warning](#104-the-derived-limit-warning)
11. [Products and derived operations](#11-products-and-derived-operations)
   - [Cup products and external products](#111-cup-products-and-external-products)
   - [Projection formula and Leray](#112-projection-formula-and-leray)
   - [Correspondences and change of base](#113-correspondences-and-change-of-base)
12. [Relative curves](#12-relative-curves)
   - [Smooth proper curves](#121-smooth-proper-curves)
   - [Marked and open curves](#122-marked-and-open-curves)
   - [A nodal degeneration](#123-a-nodal-degeneration)
13. [Abelian schemes](#13-abelian-schemes)
   - [The first direct image](#131-the-first-direct-image)
   - [Exterior powers and arbitrary base change](#132-exterior-powers-and-arbitrary-base-change)
   - [Isogenies, polarizations, and endomorphisms](#133-isogenies-polarizations-and-endomorphisms)
14. [Selected PEL families](#14-selected-pel-families)
   - [The geometric hypotheses](#141-the-geometric-hypotheses)
   - [Universal abelian families and coefficient systems](#142-universal-abelian-families-and-coefficient-systems)
   - [Proper and nonproper parameter spaces](#143-proper-and-nonproper-parameter-spaces)
   - [Good reduction and specialization](#144-good-reduction-and-specialization)
   - [A product-type PEL calculation](#145-a-product-type-pel-calculation)
15. [A reusable comparison package](#15-a-reusable-comparison-package)
   - [The theorem checklist](#151-the-theorem-checklist)
   - [The chain of reductions](#152-the-chain-of-reductions)
   - [Conclusion](#153-conclusion)

## 1. Cohomology moving in a family

### 1.1 The comparison problem

A variety over a field has cohomology groups. A morphism $f:X\to S$ has something richer: the cohomology of every geometric fiber, together with the ways those groups vary as the point of $S$ moves. The central question is whether this variation is genuinely geometric or merely a collection of unrelated groups.

For a cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
S'&\xrightarrow{g}&S,
\end{array}
$$

there is a canonical comparison

$$
g^*Rf_*K\longrightarrow Rf'_*g'^*K.
$$

It always exists. It need not be an isomorphism. Proper base change says that properness of $f$ makes it an isomorphism for the finite torsion coefficients used in this book. Smooth base change says that smoothness of $g$ is another mechanism making the same comparison an isomorphism. Local acyclicity answers a different but adjacent question: when $f$ itself is smooth and the coefficient is lisse, small changes in the base create no new local cohomology. Combining local acyclicity with properness makes the higher direct images lisse and makes specialization between fibers invertible.

These statements are the étale counterparts of familiar topological ideas. A proper continuous map does not let cohomology escape to infinity. A smooth proper map resembles a locally trivial bundle. Yet the analogies are guides, not proofs. Algebraic families have no sufficiently fine ordinary topology in which every smooth proper morphism is a fiber bundle. The proof passes instead through strict henselian neighborhoods, finite stratifications, compactification, and a calculation over traits.

The order matters. Before saying that a direct image is locally constant, one must know that its stalks are finite. Before passing to an inverse system of coefficients, one must prove uniform bounds and control derived limits. Before identifying a stalk with fiber cohomology, one must distinguish the strict-local total space from the geometric fiber. This book makes each of those transitions explicit.

### 1.2 Conventions and coefficient regimes

All schemes are locally noetherian unless stated otherwise. The strongest constructibility theorem will be used over an excellent noetherian base; this includes schemes of finite type over a field, a discrete valuation ring, or $\mathbf Z[1/N]$, and therefore includes the arithmetic families needed here. Morphisms called proper, smooth, or of finite type are understood in the usual scheme-theoretic sense. A geometric point $\bar s\to S$ has separably closed residue field, and

$$
X_{\bar s}=X\times_S\bar s
$$

is the geometric fiber.

Fix a positive integer $N$. A finite coefficient ring $\Lambda$ is killed by $N$. Unless a theorem explicitly says otherwise, $N$ is invertible on every scheme under consideration. Thus the residue characteristics are prime to the coefficient torsion. The principal examples are

$$
\Lambda_n=\mathbf Z/\ell^n\mathbf Z,
\qquad \ell\in\mathcal O_S^\times.
$$

A constructible sheaf has finite stalks and is lisse on the pieces of a finite locally closed stratification. A bounded constructible complex belongs to $D^b_c(X,\Lambda)$. We use the derived direct image $Rf_*$, exact inverse image $g^*$, derived tensor $\otimes^L$, and cohomological grading. The foundations, spectral sequences, finite-level finiteness, and derived inverse limits were established in Book 21.

The invertibility hypothesis plays different roles in different results. The formal proper comparison theorem has versions for arbitrary torsion, but the proof developed here uses prime-to-residue-characteristic purity, tame local calculations, and uniform cohomological-dimension bounds. Accordingly every stated finiteness, smooth base-change, and local-acyclicity result keeps $N$ invertible. This is exactly the range required for $\ell$-adic cohomology at places away from $\ell$. At a residue characteristic equal to $\ell$, these statements cannot simply be reused: wild ramification and inseparable phenomena demand another theory.

### 1.3 The four main theorems

The narrative culminates in four assertions.

**Constructibility.** If $f:X\to S$ is separated and of finite type, $S$ is excellent noetherian, $N$ is invertible on $S$, and $K\in D^b_c(X,\Lambda)$, then $Rf_*K$ has constructible cohomology and is locally bounded above. If the relative dimension is at most $d$, a uniform bound depending on $d$ and the amplitude of $K$ is available.

**Proper base change.** If $f:X\to S$ is proper, with $S$ noetherian, and $K\in D^b_c(X,\Lambda)$ with $N$ invertible on $S$, then for every $g:S'\to S$ the canonical map

$$
g^*Rf_*K\xrightarrow{\sim}Rf'_*g'^*K
$$

is an isomorphism. In particular,

$$
(R^qf_*K)_{\bar s}\cong H^q(X_{\bar s},K|_{X_{\bar s}}).
$$

**Smooth base change.** In the displayed square, if $g$ is smooth and $f$ is separated of finite type between excellent noetherian schemes, then the same comparison is an isomorphism for bounded constructible prime-to-residue-characteristic coefficients. Properness of $f$ is not required.

**Smooth local acyclicity.** If $f:X\to S$ is smooth and $K$ is lisse with finite stalks killed by an integer invertible on $S$, then $f$ is universally locally acyclic relative to $K$. If $f$ is also proper, each $R^qf_*K$ is lisse, commutes with arbitrary change of base, and its specialization maps are isomorphisms.

The hypotheses are deliberately asymmetric. Proper base change concerns the vertical map $f$ and permits arbitrary $g$. Smooth base change concerns the horizontal map $g$ and permits nonproper $f$. Local acyclicity concerns the vertical map $f$ and a lisse coefficient. Confusing these three roles is a common source of false arguments.

### 1.4 Comparison with coherent base change

Book 15 studied a similarly named theorem for coherent sheaves. The resemblance is useful, but the mechanisms differ. For a coherent sheaf $\mathcal E$ on a proper family, the comparison map involves

$$
Lg^*Rf_*\mathcal E,
$$

and its cohomology can acquire Tor. Flatness of $\mathcal E$, vanishing in an adjacent degree, or perfection governs when an underived fiber map is an isomorphism. Dimensions may jump even in a proper flat family.

For étale sheaves, inverse image is exact, so no left-derived symbol is needed on $g^*$. Proper base change is correspondingly stronger: for finite constructible torsion coefficients in the stated range it allows arbitrary $g$ without a flatness condition on the coefficient. Nilpotent thickenings do not change the étale site at all.

The price is paid elsewhere. Coefficient order must be separated from residue characteristic for the tame finiteness and local-acyclicity package. A lisse étale coefficient is a locally constant finite system rather than a quasi-coherent module, and its variation is measured by monodromy rather than by ranks of matrices over the structure sheaf.

The two theories meet in applications but should not be conflated. On an abelian scheme, coherent base change controls invariant differentials and the Hodge bundle; proper smooth étale base change controls the Tate module and geometric cohomology. A polarization relates the resulting structures, but neither base-change theorem proves the other.

## 2. Geometric stalks and comparison maps

### 2.1 Strict localizations

Let $\bar s\to S$ lie over $s$. The strict localization

$$
S_{(\bar s)}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S,\bar s}
$$

is the filtered inverse limit of pointed étale neighborhoods of $\bar s$. It is a local scheme with separably closed residue field. Its closed point is $\bar s$, but it generally has many generizations. Thus

$$
X_{(\bar s)}=X\times_S S_{(\bar s)}
$$

contains the geometric fiber $X_{\bar s}$ and also records how that fiber sits inside every sufficiently small étale neighborhood.

For a quasi-compact separated $f$ and a constructible torsion complex $K$, continuity gives the strict-local stalk formula

$$
(Rf_*K)_{\bar s}\simeq R\Gamma(X_{(\bar s)},K).
$$

This is a consequence of the definition of a stalk as a filtered colimit over pointed étale neighborhoods and of continuity of étale cohomology for constructible torsion coefficients. It is not proper base change. The latter is precisely the further assertion that restriction to the closed fiber induces

$$
R\Gamma(X_{(\bar s)},K)\xrightarrow{\sim}
R\Gamma(X_{\bar s},K).
$$

This distinction is the first diagnostic test in any base-change proof. Computing a stalk only reaches the strict-local total space.

### 2.2 The base-change morphism

For the cartesian square of Section 1.1, adjunction begins with the counit

$$
f^*Rf_*K\longrightarrow K.
$$

Pull it back to $X'$, use $g'^*f^*=f'^*g^*$, and adjoint back along $f'$. The result is

$$
\mathrm{BC}_{f,g}:g^*Rf_*K\longrightarrow Rf'_*g'^*K.
$$

The construction shows three compatibilities without any theorem. It commutes with morphisms of $K$ and hence with distinguished triangles. It is transitive under pasting base-change squares. It is compatible with tensor pairings because all arrows arise from units, counits, and monoidal pullback.

Taking cohomology sheaves produces edge maps

$$
g^*R^qf_*\mathcal F\longrightarrow R^qf'_*g'^*\mathcal F.
$$

Unlike coherent cohomology, no Tor correction appears merely from inverse image: inverse image for étale sheaves of $\Lambda$-modules is exact. Derived tensor still matters when the coefficient ring itself changes. The simplicity of $g^*$ must not be confused with automatic invertibility of the comparison map.

Two elementary cases are worth retaining. If $f$ is finite, $f_*$ is exact and can be computed on finite fibers, so base change is immediate. If $X=S\times Z$ and $K$ is pulled back from a bounded finite complex on $Z$, the direct image is locally the constant complex $R\Gamma(Z,K)$ and base change is again transparent. The general theorem says that proper families behave, for this purpose, as though they were assembled from these finite and constant pieces.

### 2.3 Specializations and their direction

A specialization of geometric points $\bar t\rightsquigarrow\bar s$ consists of a specialization $t\rightsquigarrow s$ together with compatible choices of separable closures, equivalently a geometric point over the generic part of $S_{(\bar s)}$. Every sheaf $\mathcal G$ on $S$ then has a generization map

$$
\mathcal G_{\bar s}\longrightarrow\mathcal G_{\bar t}.
$$

Applying this to $R^qf_*K$ and using proper base change at both ends gives

$$
\operatorname{sp}_{\bar t/\bar s}:
H^q(X_{\bar s},K_{\bar s})\longrightarrow
H^q(X_{\bar t},K_{\bar t}).
$$

The arrow runs from the special fiber to the generizing fiber because it comes from a sheaf generization map. It can depend on the chosen geometric specialization. Different choices differ by the action of the relevant fundamental group. If $R^qf_*K$ is lisse, every specialization map is an isomorphism, but not necessarily the identity after arbitrary trivializations. This residual monodromy is information, not ambiguity.

## 3. Constructibility and finite cohomology

### 3.1 Why finiteness must precede comparison

Suppose all geometric fibers have finite cohomology. That alone does not show $R^qf_*K$ is constructible. Constructibility asks for a finite stratification on which the stalks are transported by finite monodromy. Pointwise finiteness supplies neither the stratification nor continuity of transport.

The relative theorem is proved by spreading absolute finiteness through noetherian induction. One first obtains a dense open set on which the direct images are lisse, then treats the complement, whose dimension is smaller. Compactification controls infinity, and local acyclicity controls the smooth locus. The result is a finite stratification because a noetherian space admits no infinite strictly descending chain of closed subsets.

Finiteness is also indispensable for adic coefficients. For a tower of finite groups, the images in each fixed level stabilize, so the tower is Mittag--Leffler. Without finite groups, the first derived inverse limit can survive and destroy an apparently obvious passage from finite-level base change to integral coefficients.

### 3.2 Absolute finiteness in the required range

Book 21 established the following absolute input. If $k$ is separably closed, $Y$ is separated of finite type over $k$ with $\dim Y\leq2$, and $\mathcal F$ is a constructible finite $\Lambda$-sheaf with $N$ prime to $\operatorname{char}k$, then every $H^q(Y,\mathcal F)$ is finite and

$$
H^q(Y,\mathcal F)=0\qquad(q>2\dim Y).
$$

It also established the corresponding finite bound $2g$ for an abelian variety of dimension $g$. These statements are enough for relative curves, abelian schemes, and the selected surfaces. For a proper curve, the bound is $[0,2]$; for a smooth affine curve it improves to $[0,1]$. For a proper surface it is $[0,4]$.

These results used constructible dévissage, finite étale descent, compactification, and the Kummer calculation for curves and abelian varieties. We do not reprove those derived foundations. We do prove the relative constructibility needed here, whose additional content is uniformity as the fiber moves.

No corresponding assertion is made when $N$ is not invertible. In characteristic $p$, Artin--Schreier covers create abundant $p$-torsion phenomena on affine schemes, and the tame purity calculation used below is unavailable.

### 3.3 Constructibility of direct images

**Relative constructibility theorem.** Let $S$ be excellent and noetherian, let $f:X\to S$ be separated and of finite type, and let $K\in D^b_c(X,\Lambda)$, where $N\Lambda=0$ and $N$ is invertible on $S$. Then every $R^qf_*K$ is constructible. On a quasi-compact $S$, only finitely many $q$ occur.

**Proof strategy.** Truncation reduces to a constructible sheaf. A finite filtration reduces that sheaf to $j_!\mathcal L$ for a lisse finite sheaf on a locally closed stratum. Replacing the stratum by a finite étale cover reduces $\mathcal L$ to a constant finite module, with finite-group descent recovering the original coefficient. Compactify the resulting separated finite-type morphism. The proper part is controlled by the strict-local theorem of Chapter 5; the boundary is supported on a smaller-dimensional closed subset and is handled by noetherian induction. Generic smoothness after a finite stratification and the local-acyclicity calculation of Chapter 8 show that on a dense open subset of each base component the higher direct images are lisse. Removing that open decreases the base.

Excellence ensures that normalization in the finite cover is finite and that the compactifications and regular alterations of the relevant low-dimensional strata remain noetherian and finite type. Proper base change identifies stalks of the compactified contribution with finite geometric-fiber cohomology. The boundary triangle

$$
j_!j^*K\longrightarrow K\longrightarrow i_*i^*K\longrightarrow
$$

separates the dense open from a closed subset. Each step either replaces the coefficient by a constant one after finite descent or lowers the support dimension. Induction terminates and produces a finite lisse stratification. $\square$

There is no circularity. The strict-local proper statement is proved first for elementary coefficients by the geometric argument below. Constructibility then passes from those cases to bounded constructible complexes and packages the result globally.

### 3.4 Uniform amplitude and complexes

Let the geometric fibers of $f$ have dimension at most $d$, and let $K$ have cohomology only in $[a,b]$. The hypercohomology spectral sequence

$$
R^p f_*\mathcal H^q(K)\Longrightarrow R^{p+q}f_*K
$$

shows that a uniform fiberwise bound for sheaves gives one for complexes. In the proper prime-to-characteristic range, the safe bound is

$$
R^m f_*K=0\qquad(m\notin[a,b+2d]).
$$

For smooth affine curves the upper addition can be reduced to $1$. Uniformity in the exponent $n$ of $\Lambda_n$ is crucial: it permits finite totalizations and derived inverse limits to be interchanged.

Constructibility is stable under cones, truncations, and pullback. Consequently it is enough to prove a comparison on sheaves and check that the class of complexes for which it holds is triangulated. The finite filtration by cohomology sheaves then reconstructs every $K\in D^b_c$.

### 3.5 What the finiteness hypotheses exclude

Each finiteness condition blocks a concrete pathology. If $X$ is an infinite disjoint union of points over a field, then

$$
H^0(X,\Lambda)=\prod_{x\in X}\Lambda
$$

is infinite; finite type excludes this. On a noetherian curve, infinitely many skyscraper sheaves can have finite individual stalks but no finite constructibility stratification. If the base is nonnoetherian, a descending family of closed supports can require infinitely many strata.

Excellence enters less visibly. Without it, normalization in a finite extension of a function field need not be finite. Replacing a lisse sheaf by a finite cover can then leave finite-type geometry. For schemes of finite type over fields or over $\mathbf Z[1/N]$, excellence is automatic.

Properness is not needed for absolute finiteness: an affine curve still has finite cohomology. Its role is uniform fiber comparison. Invertibility supplies tame cohomological dimension and purity. A proper scheme with nonconstructible coefficients may still have infinite cohomology, and a smooth finite-type scheme with wild torsion need not satisfy the stated bounds.

## 4. The reduction machinery

### 4.1 Noetherian induction and dévissage

The proofs repeatedly use one pattern. Let $P(Z,K)$ be stable under distinguished triangles and finite étale descent. Choose a dense open $U$ of the support of $K$ on which $K$ is lisse. For $j:U\hookrightarrow Z$ and $i:Z\setminus U\hookrightarrow Z$, the localization triangle

$$
j_!j^*K\longrightarrow K\longrightarrow i_*i^*K\longrightarrow
$$

reduces $P(Z,K)$ to the lisse term on $U$ and a term with smaller support. A finite étale cover $v:V\to U$ trivializes the lisse sheaf. After passing to a Galois closure with group $G$, the original object is recovered from the constant coefficient upstairs by the Čech nerve, equivalently by finite-group descent. The bar resolution need not be bounded when $|G|$ is not invertible in $\Lambda$; in a fixed geometric cohomological range, uniform dimension bounds permit the required finite truncation. Thus the difficult case is a constant finite coefficient on a normal connected stratum.

This is constructible dévissage. It is more precise than working stratum by stratum: extension by zero records how strata attach, while the localization triangle carries the connecting morphisms between their cohomology. Ignoring these morphisms may preserve dimensions but loses the derived comparison.

Noetherian induction is used on closed subsets, not on individual points. At each stage a dense open is settled uniformly; its closed complement has strictly smaller support. Hence the procedure ends after finitely many stages.

### 4.2 Compactification and the boundary

A separated finite-type morphism $f:X\to S$ admits a factorization

$$
X\xrightarrow{j}\overline X\xrightarrow{\bar f}S
$$

with $j$ an open immersion and $\bar f$ proper. This does not assert that $\overline X$ is smooth or that its boundary is a divisor. Those improvements require shrinking, stratifying, and, in the low-dimensional applications, normalization and controlled alteration.

Let $i:D=\overline X\setminus X\hookrightarrow\overline X$. Then

$$
Rf_*K=R\bar f_*Rj_*K,
\qquad
Rf_!K=R\bar f_*j_!K.
$$

The cone of $j_!K\to Rj_*K$ is supported on $D$. Proper base change handles the compactified map, while the difference between ordinary and compactly supported cohomology is a boundary problem. When $D$ is a normal-crossings divisor, its local pieces are products of punctured strict henselian traits. Prime-to-characteristic inertia is procyclic in each branch, so its cohomology is bounded and constructible. Intersections of components lower dimension.

Compactification is essential in constructibility and smooth base change, where $f$ need not be proper. It also explains counterexamples: a nonproper family can change because its boundary changes.

### 4.3 Reduction to a strict henselian trait

The stalk formula reduces proper base change to a proper map over a strictly local base $S$ and

$$
R\Gamma(X,K)\longrightarrow R\Gamma(X_s,K_s).
$$

A second reduction turns an arbitrary generization into a one-dimensional problem. Let $\eta$ specialize to $s$. Take the closure of $\eta$, normalize it, and localize at a point over $s$. Excellence makes normalization finite in the required setting. Strict henselization then produces a strict henselian trait $T\to S$, with closed point over $s$ and generic point over a finite extension of $\kappa(\eta)$. Since constructible sheaves are detected on geometric stalks, it is enough to control specialization over such traits.

For a base of larger dimension, choose a chain of immediate specializations and repeat. Noetherianity makes the dimension drop finite. The trait calculation is therefore a detection argument, not merely an illustrative slice.

### 4.4 Why the reductions terminate

Three measures decrease. Constructible dévissage lowers the dimension of coefficient support. Compactification moves failure to a boundary of smaller dimension. Trait reduction replaces a specialization by a one-dimensional local problem. Finite étale descent changes none of these measures but trivializes monodromy after a finite step.

In the required low-dimensional range, normalization resolves the zero-dimensional defects of curves, and a normal-crossings alteration of a surface gives boundary components and crossings of dimensions one and zero. Every descent totalization is uniformly bounded in each cohomological degree. Thus neither an infinite geometric process nor a convergence assumption is concealed.

## 5. The strict-local proper theorem

### 5.1 The decisive comparison

**Strict-local proper theorem.** Let $S$ be a strictly henselian noetherian local scheme with closed point $s$, let $f:X\to S$ be proper, and let $K\in D^b_c(X,\Lambda)$, where $N\Lambda=0$ and $N$ is invertible on $S$. Then restriction induces

$$
R\Gamma(X,K)\xrightarrow{\sim}R\Gamma(X_s,K_s).
$$

**Proof strategy.** A constructible filtration and finite étale descent reduce to constant coefficients on a proper normal stratum. Properness lets us replace closures by normalizations; complements have smaller dimension. Induct on relative dimension. In dimension zero, proper and quasi-finite means finite. Finite algebras over a strictly henselian local ring split according to closed-fiber points, and direct image is exact.

In positive dimension choose, after a finite cover and projective modification, a relative pencil. Exceptional and branch loci have smaller dimension. The new relative-curve contribution is treated in Section 5.2; the base of the pencil and exceptional pieces are treated inductively. Proper cohomological descent along the modification is computed by its augmented Čech nerve. Away from the exceptional locus the nerve is split, while over that locus dimension falls. Uniform bounds make the totalization finite in every degree. This proves constant coefficients and hence, by the initial dévissage and truncation triangles, every bounded constructible complex. $\square$

Properness forces specializations in $X$ to meet the closed fiber, strict henselianity removes residue-field descent, and the prime-to-characteristic local calculation shows that filling normal-crossings strata creates the same cohomology on the total space and closed fiber.

### 5.2 The curve calculation

Let $T$ be a strict henselian trait and let $C\to T$ be a proper relative curve. Normalize $C$ and separate the singular and nonflat loci; these are finite over $T$ or supported in the closed fiber. Finite pieces satisfy comparison directly. After a finite extension of traits and a modification, the remaining curve is semistable: étale-locally at a node it has equation

$$
xy=\pi.
$$

Cover the semistable curve by the smooth locus and small node neighborhoods. On a smooth neighborhood, a constant prime-to-characteristic sheaf is locally acyclic by Chapter 8. At a node, remove the node. The punctured neighborhood has tame fundamental group generated by one loop, and after choosing a tame generator its cohomology with a finite module $M$ is represented by

$$
M\xrightarrow{\tau-1}M.
$$

For constant $M$, the differential is zero; intrinsically the degree-one term carries the inverse cyclotomic twist suppressed by the chosen generator. The two branches in the special fiber contribute the same incidence map as the annulus in the generic fiber; it is the edge map of the dual graph. Thus the node contribution agrees on total space and special fiber. Mayer--Vietoris glues the pieces. Descent from the finite trait extension and localization for normalization and exceptional components return the result for $C$.

This explains why smoothness is not needed for proper base change. A nodal fiber may have different cohomology from a nearby smooth fiber, but the direct-image stalk at the nodal point still equals the cohomology of the nodal fiber. Proper base change identifies stalks with fibers; it does not make stalks locally constant.

### 5.3 Higher relative dimension

After a projective modification, a sufficiently general relative projection gives a fibration $h$ whose generic fibers have dimension one less. The locus where it fails to be flat, where singularities exceed normal crossings, or where coefficients cease to be constant has smaller support. Over the good locus, Leray reads

$$
R\Gamma(Y,Rh_*\Lambda)\simeq R\Gamma(X,\Lambda).
$$

The curve calculation controls $Rh_*\Lambda$ under restriction to the closed fiber. Its cohomology sheaves are constructible by the lower-relative-dimension case of the same induction; on each stratum the induction hypothesis applies to the lower-dimensional base. Thus constructibility and strict-local comparison are proved simultaneously, ordered first by relative dimension and then by support dimension. This removes a possible circularity between Chapters 3 and 5. The Leray spectral sequence has finitely many rows, so comparison on its $E_2$-page gives comparison on the abutment.

To remove the modification, form the augmented Čech nerve $X_\bullet\to X$. Proper descent gives

$$
R\Gamma(X,K)\simeq\operatorname{Tot}R\Gamma(X_\bullet,K).
$$

Over the isomorphism locus the augmentation is split. Every failure is supported over the exceptional locus, already covered by induction. This closes the dimension step.

Only relative dimensions one, two, and smooth abelian families are required later. The pencil argument records why the theorem is structural rather than a list of low-dimensional coincidences.

### 5.4 Complexes and constructible coefficients

The full subcategory of $D^b_c(X,\Lambda)$ on which strict-local comparison holds is triangulated. The preceding arguments put every extension by zero from a constructibility stratum in it. A finite constructible filtration therefore gives all constructible sheaves.

The truncation triangles

$$
\tau_{\leq m-1}K\longrightarrow\tau_{\leq m}K
\longrightarrow\mathcal H^m(K)[-m]\longrightarrow
$$

then give induction over the finite amplitude of $K$. This step is formal only because boundedness and constructibility have already been proved.

## 6. Proper base change

### 6.1 Finite torsion coefficients

**Proper base-change theorem.** Let $f:X\to S$ be proper with $S$ noetherian. Let $\Lambda$ be finite, killed by $N$, assume $N$ is invertible on $S$, and let $K\in D^b_c(X,\Lambda)$. For every cartesian square, the canonical map is an isomorphism:

$$
g^*Rf_*K\xrightarrow{\sim}Rf'_*g'^*K.
$$

**Proof.** Test on a geometric point $\bar s'\to S'$ with image $\bar s\to S$. The stalk on the left is $R\Gamma(X_{(\bar s)},K)$. The strict-local theorem identifies it with $R\Gamma(X_{\bar s},K_{\bar s})$. The fibers $X'_{\bar s'}$ and $X_{\bar s}$ differ only by extension between separably closed fields, which leaves finite prime-to-characteristic cohomology unchanged. Applying the strict-local theorem to $f'$ identifies the result with the stalk on the right. Tracing adjunctions shows that this is the stalk of the canonical map. $\square$

For a sheaf $\mathcal F$,

$$
g^*R^qf_*\mathcal F\xrightarrow{\sim}
R^qf'_*g'^*\mathcal F,
$$

and at a geometric point

$$
(R^qf_*\mathcal F)_{\bar s}\cong
H^q(X_{\bar s},\mathcal F_{\bar s}).
$$

Properness belongs to $f$; $g$ is arbitrary.

### 6.2 Arbitrary change of base

The stalk proof allows nonnoetherian $S'$ when the data descend from the stated noetherian situation. Thus a completion, strict henselization, field extension, nilpotent thickening, or inverse limit of affine schemes is allowed after spreading out.

The small étale sites of $S$ and $S_{\mathrm{red}}$ are equivalent, and likewise for $X$. Proper base change therefore cannot see nilpotents. This contrasts with coherent base change in Book 15, where derived tensor can detect infinitesimal structure.

For an extension $\Omega/k$ of separably closed fields and a proper $k$-scheme $Y$,

$$
R\Gamma(Y,\mathcal F)\xrightarrow{\sim}
R\Gamma(Y_\Omega,\mathcal F_\Omega).
$$

This field-extension instance is often what permits one to enlarge a geometric point without changing an answer.

### 6.3 Products, projection, and composition

If $X\xrightarrow fY\xrightarrow hS$ are proper, base change for $h\circ f$ equals the composite of base change for $f$ and $h$ under

$$
R(h\circ f)_*K\simeq Rh_*Rf_*K.
$$

It therefore respects the Leray spectral sequence

$$
R^a h_*R^b f_*K\Longrightarrow R^{a+b}(h\circ f)_*K.
$$

For proper $p:X\to S$ and a bounded finite-Tor-amplitude $L$ on $S$, the projection formula

$$
Rp_*(K\otimes^Lp^*L)\simeq Rp_*K\otimes^LL
$$

commutes with base change. For proper $X\to S$ and $Y\to S$, external product gives

$$
Rf_*K\otimes^LRh_*L
\longrightarrow R(f\times_Sh)_*(K\boxtimes^LL).
$$

This arrow is compatible with base change. Whenever the fiberwise Künneth theorem makes it an isomorphism, constructibility and geometric stalks make it an isomorphism over the whole base.

### 6.4 Failure without properness

Let

$$
X=\{(x,t)\in\mathbf A^1_x\times\mathbf A^1_t:tx\ne1\}
$$

and project to $\mathbf A^1_t$. The map is smooth. At $t=0$ the fiber is $\mathbf A^1$; at $t\ne0$ it is $\mathbf A^1$ minus a point. Their first prime-to-characteristic cohomology differs, so $R^1f_*\Lambda$ cannot be lisse across $0$.

The missing point travels in from infinity. Compactifying in $\mathbf P^1\times\mathbf A^1$ exposes a boundary whose fiber changes at $0$. Smoothness controls local singularities inside $X$; properness controls escape through the boundary.

### 6.5 Three model base changes

Three common squares illustrate different uses of the theorem.

For $S'=\bar s$ a geometric point, proper base change is the stalk formula

$$
(Rf_*K)_{\bar s}\simeq R\Gamma(X_{\bar s},K_{\bar s}).
$$

It calculates ranks but does not compare distinct points. For $S'=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S,\bar s}$, it identifies the pullback of $Rf_*K$ with the strict-local family; restricting onward to the closed point constructs specialization. For $S'=\operatorname{Spec}k'$ a field extension, it identifies geometric cohomology after compatible choices of separable closures. The last isomorphism respects the Galois action of the common subgroup, but it does not identify the full absolute Galois groups of $k$ and $k'$.

For $f:\mathbf P^1_S\to S$, the geometric calculation and proper base change give

$$
R^0f_*\Lambda=\Lambda,\qquad
R^1f_*\Lambda=0,\qquad
R^2f_*\Lambda=\Lambda(-1).
$$

The point class defining the last sheaf survives every base change. Its Tate twist makes the assertion canonical over a nonclosed base.

## 7. Smooth base change

### 7.1 Changing the base by a smooth morphism

Proper base change fixes the vertical map by requiring it to be proper. There is a second theorem in which the vertical map may be nonproper, but the horizontal change of base is smooth.

**Smooth base-change theorem.** Consider a cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
S'&\xrightarrow{g}&S.
\end{array}
$$

Assume $S$ is excellent noetherian, $f$ is separated and of finite type, and $g$ is smooth. Let $K\in D^b_c(X,\Lambda)$, where $\Lambda$ is finite, killed by $N$, and $N$ is invertible on $S$. Then

$$
g^*Rf_*K\xrightarrow{\sim}Rf'_*g'^*K.
$$

Because the assertion is local for the étale topology on $S'$, a smooth morphism can be reduced étale-locally to a projection

$$
\mathbf A^r_S\longrightarrow S.
$$

Factor that projection into affine-line projections. It is enough to handle one new parameter. Compactify $f$ and use proper base change on the compactification. The possible discrepancy is supported at the boundary. Constructible dévissage and the normal-crossings calculation reduce that boundary to a punctured strict henselian trait. Its cohomology is the two-term tame inertia complex, unchanged after adjoining a smooth parameter. The localization triangle now proves the theorem.

This proof exhibits every assumption. Separation and finite type give compactification. Excellence makes normalization and constructibility finite. Smoothness gives an étale-local affine-space model. Invertibility of $N$ makes the punctured-trait calculation tame. If $g$ is arbitrary and $f$ nonproper, the theorem is false.

### 7.2 The standard smooth-local calculation

Let $A$ be strictly henselian and let

$$
p:\mathbf A^r_A\to\operatorname{Spec}A
$$

be projection. For a constant finite module $M$ of order invertible in $A$,

$$
Rp_*M\simeq M.
$$

For $r=1$, compactify to $\mathbf P^1_A$. Proper base change computes its cohomology from the closed geometric fiber. The localization sequence for infinity and purity for a smooth divisor cancel the degree-two point class, leaving only $M$ in degree zero. Products and induction give $r>1$.

A smooth morphism $u:U\to S$ is, around every point, étale over affine space. Étale pullback preserves the calculation, and descent glues it. For a lisse $\mathcal L$, pass to a finite étale neighborhood on which it is constant. Thus sufficiently small strict neighborhoods have no relative cohomology beyond degree zero.

This is local on the source. It does not say $R^qu_*\mathcal L$ is globally lisse when $u$ is nonproper. Section 6.4 is locally a smooth projection everywhere; its jump occurs because no fixed source neighborhood contains a whole noncompact fiber.

### 7.3 Derived compatibility

Smooth base change is first proved for a constructible sheaf. The complexes for which comparison is an isomorphism form a triangulated subcategory. The finite sequence of truncation triangles therefore gives the result for every $K\in D^b_c$.

It follows that smooth base change respects connecting maps, hypercohomology, and the Leray filtration. For finite-Tor-amplitude $K$ and $L$, the comparison square for $K\otimes^LL$ commutes with the square formed from the comparisons for $K$ and $L$. All maps arise from the same monoidal adjunctions before cohomology is taken.

One cannot replace “smooth” by “flat.” Flat maps may introduce new valuations and boundary specializations. Smoothness supplies both flatness and a regular affine-space local model; the latter is decisive.

### 7.4 Étale, smooth, and universal changes

An étale change is the relative-dimension-zero case. It can also be checked directly: an étale neighborhood after base change refines one pulled from the original site. Smooth base change extends this invariance by allowing affine-space directions.

It is not a theorem for every universally open map. Openness controls images of subsets; the proof needs acyclicity of geometric directions. Nor does smoothness of $g$ make $Rf_*K$ lisse. If $f$ has singular fibers, smooth pullback reproduces their constructible stratification on $S'$.

For smooth $S''\to S'\to S$, comparison for the composite equals the composite of comparisons. One may therefore use smooth charts in stages. This transitivity makes the result independent of the chosen affine-space chart.

## 8. Local acyclicity

### 8.1 Vanishing local change

Base change compares direct images. Local acyclicity compares a point with a nearby strict-local tube. Let $f:X\to S$, let $\bar x\to X$ map to $\bar s\to S$, and let $\bar t$ be a geometric generization of $\bar s$ in $S_{(\bar s)}$. There is a canonical map

$$
K_{\bar x}\longrightarrow
R\Gamma\left(
X_{(\bar x)}\times_{S_{(\bar s)}}\bar t,\ K
\right).
$$

The morphism $f$ is **locally acyclic relative to $K$** if this is an isomorphism for every such triple. It is **universally locally acyclic** if the assertion remains true after every base change.

The cone measures newly appearing local cohomology. The definition is local on $X$, unlike the cohomology of whole fibers. It is stable under distinguished triangles and étale localization.

For the identity $X=S$ and a lisse sheaf, the map is an isomorphism because the sheaf becomes constant on strict neighborhoods. For a skyscraper at a closed point it fails across a generization. Smoothness cannot rescue an arbitrary constructible coefficient; lissity is essential.

### 8.2 Smooth morphisms with lisse coefficients

**Smooth local-acyclicity theorem.** Let $f:X\to S$ be smooth of finite presentation. Let $\mathcal L$ be a lisse finite $\Lambda$-sheaf, with $N\Lambda=0$ and $N$ invertible on $S$. Then $f$ is universally locally acyclic relative to $\mathcal L$.

**Proof.** Work étale-locally on source and base. Trivialize $\mathcal L$ by a finite étale cover. A smooth morphism is étale-locally a projection from affine space, so reduce to $\mathbf A^r_S\to S$ with constant coefficients. Strict localization at a source point and its image identifies the nearby tube with a strict localization of affine space over a separably closed field. Section 7.2 gives $\Lambda$ in degree zero and zero above. The stalk map is an isomorphism.

After arbitrary base change, the morphism remains smooth, the coefficient remains lisse, and the same calculation applies. Finite étale descent returns the original coefficient. $\square$

The theorem extends to bounded complexes with lisse cohomology by truncation. It does not include coefficients whose ramification moves along the fibers.

### 8.3 Universal local acyclicity and its limits

Properness is absent from local acyclicity. The smooth nonproper family of Section 6.4 is locally acyclic for the constant sheaf despite jumping global $H^1$; the boundary escapes every fixed source neighborhood. Conversely, properness does not imply local acyclicity. A nodal degeneration is proper, but a node has a nearby annulus with degree-one cohomology.

Coefficient invertibility is essential for the stated result. In characteristic $p$, Artin--Schreier equations create $p$-torsion étale phenomena that the tame affine-space calculation does not control. Smoothness of the scheme does not make $p$-primary cohomology tame.

Local acyclicity is coefficient-dependent. A morphism may be locally acyclic for a constant prime-to-characteristic sheaf and fail for a constructible sheaf singular along a moving divisor.

## 9. Specialization and locally constant direct images

### 9.1 Specialization maps

For proper $f:X\to S$ and a geometric specialization $\bar t\rightsquigarrow\bar s$, proper base change converts the generization of $R^qf_*K$ into

$$
\operatorname{sp}_{\bar t/\bar s}:
H^q(X_{\bar s},K_{\bar s})
\longrightarrow H^q(X_{\bar t},K_{\bar t}).
$$

These maps are functorial in $K$, compatible with long exact sequences, and transitive:

$$
\operatorname{sp}_{\bar u/\bar s}
=
\operatorname{sp}_{\bar u/\bar t}\circ
\operatorname{sp}_{\bar t/\bar s}.
$$

They commute with cup products, pullback, and proper pushforward because they arise at the derived-sheaf level. Without local acyclicity they need not be invertible, but they still exist.

### 9.2 The smooth proper theorem

**Smooth proper base-change theorem.** Let $f:X\to S$ be smooth and proper, and let $\mathcal L$ be lisse finite, killed by an integer invertible on $S$. Then:

1. every $R^qf_*\mathcal L$ is lisse with finite stalks;
2. it vanishes outside the uniform geometric range;
3. its formation commutes with arbitrary base change;
4. every specialization map is an isomorphism.

**Proof.** Proper base change identifies stalks with geometric-fiber cohomology and proves arbitrary base change. Absolute finiteness makes stalks finite. Smooth local acyclicity makes every generization map an isomorphism. Refine a constructibility stratification; adjacent strata then carry local systems with invertible transport and glue to a lisse sheaf. Fiber dimension supplies vanishing. $\square$

On connected $S$, the ranks of fiber cohomology are constant. There is canonical transport along an étale path, not a canonical simultaneous trivialization. Monodromy records the obstruction to such a trivialization.

### 9.3 Monodromy and arithmetic actions

At a geometric basepoint $\bar s$ of connected $S$, lissity gives

$$
\pi_1(S,\bar s)\longrightarrow
\operatorname{Aut}_\Lambda
H^q(X_{\bar s},\mathcal L_{\bar s}).
$$

Transport along a path is the specialization isomorphism; a loop gives monodromy. For $S=\operatorname{Spec}k$, this is the absolute Galois action.

If a smooth proper family extends over a henselian discrete valuation ring and $\ell$ is invertible there, the generic-fiber representation is unramified. Indeed, the lisse direct image extends across the closed point, so inertia acts trivially. Frobenius on the special fiber matches unramified Frobenius on the generic fiber, with the chosen arithmetic or geometric normalization.

The converse is not asserted. An unramified cohomology representation need not construct a smooth proper model; cohomology can miss geometric singularities.

## 10. Passage to adic coefficients

### 10.1 Finite-level control of the tower

Fix $\ell\in\mathcal O_S^\times$ and set $\Lambda_n=\mathbf Z/\ell^n\mathbf Z$. Let $\mathcal F=(\mathcal F_n)$ be normalized constructible with

$$
\mathcal F_{n+1}\otimes^L_{\Lambda_{n+1}}\Lambda_n
\simeq\mathcal F_n.
$$

Book 21 defined continuous direct image using the normalized tower $(Rf_*\mathcal F_n)_n$. Three facts transport base change:

1. finite-level comparison is an isomorphism for every $n$;
2. cohomological amplitude is bounded independently of $n$;
3. each fixed-degree tower is Mittag--Leffler.

Proper or smooth base change supplies the first, geometric dimension the second, and finiteness the third. Images in each finite target stabilize. Cohomology transition maps need not be surjective.

The three facts let one commute geometric stalks, finite totalizations, and $R\varprojlim$. They also show that the direct-image tower remains normalized, since derived reduction can be checked on geometric-fiber complexes.

### 10.2 Integral and rational base change

**Adic proper base change.** Let $f:X\to S$ be proper in the noetherian prime-to-$\ell$ setting, and let $\mathcal F$ be bounded normalized constructible with uniform amplitude and finite-level stalk generators. Then

$$
g^*Rf_{*,\mathrm{cont}}\mathcal F
\xrightarrow{\sim}
Rf'_{*,\mathrm{cont}}g'^*\mathcal F
$$

for every $g:S'\to S$.

**Proof.** Finite proper base change gives the comparison modulo $\ell^n$. Apply $R\varprojlim_n$. Uniform amplitude puts every cone in a common finite range, and Mittag--Leffler kills the possible first-derived-limit obstruction on stalk cohomology. The inverse limit of the zero cones is zero. Normalization identifies the result with continuous direct image. $\square$

The same proof gives adic smooth base change when $g$ is smooth. Rationalize only afterward:

$$
Rf_{*,\mathrm{cont}}\mathcal F
\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

Flatness of $\mathbf Q_\ell$ preserves comparison. Tensoring a finite level with $\mathbf Q_\ell$ would give zero and is not rationalization.

### 10.3 Specialization at the adic level

Finite-level specialization maps form a compatible tower and induce

$$
\operatorname{sp}_{\bar t/\bar s}:
H^q_{\mathrm{cont}}(X_{\bar s},\mathcal F_{\bar s})
\longrightarrow
H^q_{\mathrm{cont}}(X_{\bar t},\mathcal F_{\bar t}).
$$

For smooth proper $f$ and a lisse system, every finite-level map is an isomorphism, hence so are the integral and rational limits. The map is continuous for the $\ell$-adic topology.

Each $R^qf_{*,\mathrm{cont}}\mathcal F$ is then a lisse $\mathbf Z_\ell$-sheaf with finitely generated stalk. It is finite free if fiber cohomology has no $\ell$-torsion. Freeness must be checked; lissity alone does not imply it.

### 10.4 The derived-limit warning

For an arbitrary tower $(M_n)$, cohomology fits into

$$
0\longrightarrow
\varprojlim\nolimits^1 H^{q-1}(M_n)
\longrightarrow
H^q(R\varprojlim M_n)
\longrightarrow
\varprojlim H^q(M_n)
\longrightarrow0.
$$

Finite-level comparison identifies the right-hand towers, but without Mittag--Leffler a naive limit can miss the left term. Towers whose transitions multiply an infinite $\ell$-primary module by $\ell$ provide algebraic models with nonstabilizing images and nonzero derived limit.

Here every target $H^q(X_{\bar s},\mathcal F_n)$ is finite, so its descending chain of images stabilizes. Constructibility and uniform bounds spread this pointwise conclusion across a finite stratification. Finiteness, not assumed surjectivity of cohomology reduction, closes the adic argument.

## 11. Products and derived operations

### 11.1 Cup products and external products

Multiplication gives

$$
Rf_*K\otimes^LRf_*L
\longrightarrow Rf_*(K\otimes^LL).
$$

Pullback is symmetric monoidal, so proper and smooth base-change comparisons commute with this arrow. Therefore

$$
\operatorname{sp}(a\smile b)
=\operatorname{sp}(a)\smile\operatorname{sp}(b).
$$

For $X,Y\to S$, external product lands in $X\times_SY$. On a geometric fiber the Künneth spectral sequence is

$$
\operatorname{Tor}^{\Lambda}_{a}
\bigl(H^b(X_{\bar s},K),H^c(Y_{\bar s},L)\bigr)
\Longrightarrow
H^{b+c-a}(X_{\bar s}\times Y_{\bar s},K\boxtimes L).
$$

Base change transports this sequence. If fiber groups are free, Tor vanishes and the ordinary tensor formula results. At the adic level products are formed modulo every $\ell^n$ and normalized after derived inverse limit.

### 11.2 Projection formula and Leray

For proper $f:X\to Y$ and finite-Tor-amplitude $L$ on $Y$,

$$
Rf_*(K\otimes^Lf^*L)\simeq Rf_*K\otimes^LL.
$$

It is compatible with base change. This can be checked on geometric points, where proper base change reduces it to the fiberwise projection formula and a finite resolution of $L_{\bar y}$.

For proper $X\xrightarrow fY\xrightarrow hS$, the Leray sequence

$$
R^ah_*R^bf_*K\Longrightarrow R^{a+b}(h\circ f)_*K
$$

is functorial under base change; the differentials correspond, not just the limiting groups. Derived tensor cannot be discarded when coefficient modules have torsion. Base change transports Tor classes but does not erase them.

### 11.3 Correspondences and change of base

For a correspondence over $S$,

$$
X\xleftarrow{p}Z\xrightarrow{q}X,
$$

with $q$ proper and the necessary coefficient morphism, pullback followed by proper pushforward acts on $Rf_*K$. Proper base change for $q$ and functoriality of $p^*$ show that this action commutes with every base change on $S$.

Specialization therefore commutes with algebraic endomorphisms, isogenies, and proper prime-to-level correspondences. The assertion passes modulo every $\ell^n$ to the adic limit.

A nonproper $q$ needs compact support. A correspondence on an open PEL space may also fail to extend across a chosen compactification. The comparison theorem proves compatibility once the proper geometric correspondence exists; it does not construct that extension.

## 12. Relative curves

### 12.1 Smooth proper curves

Let $f:C\to S$ be a smooth proper curve with geometrically connected fibers of genus $g$, and let $\ell$ be invertible on $S$. Apply smooth proper base change to the constant system. At finite level,

$$
R^0f_*\Lambda_n\simeq\Lambda_n,
\qquad
R^1f_*\Lambda_n\ \text{is lisse free of rank }2g,
\qquad
R^2f_*\Lambda_n\simeq\Lambda_n(-1),
$$

and $R^qf_*\Lambda_n=0$ for $q>2$. The first statement follows from geometric connectedness. Fiberwise Kummer theory and the $\ell^n$-torsion of the Jacobian give the middle rank. The last identification uses the class of a geometric point and its transformation under change of field; the twist records that transformation.

These fiberwise identifications globalize because the direct images are lisse and proper base change detects maps on geometric stalks. Passing through the tower gives

$$
R^0f_*\mathbf Z_\ell=\mathbf Z_\ell,
\qquad
R^1f_*\mathbf Z_\ell\ \text{lisse free of rank }2g,
\qquad
R^2f_*\mathbf Z_\ell=\mathbf Z_\ell(-1).
$$

Every change of base $S'\to S$ preserves these sheaves and their cup products. Thus genus is constant on connected components of $S$, not merely semicontinuous. The cup product

$$
R^1f_*\mathbf Z_\ell\otimes
R^1f_*\mathbf Z_\ell
\longrightarrow\mathbf Z_\ell(-1)
$$

is alternating and is transported by every specialization. Perfectness of this pairing belongs to the duality package of Book 23; here we need only its construction and comparison compatibility.

If $S$ is the spectrum of a henselian discrete valuation ring and $C$ is smooth proper over $S$, then

$$
H^1(C_{\bar s},\mathbf Z_\ell)
\xrightarrow{\sim}
H^1(C_{\bar\eta},\mathbf Z_\ell)
$$

for a chosen geometric specialization. The generic representation is unramified. This is the basic good-reduction comparison for curves.

For a lisse coefficient $\mathcal L$ on $C$, the same conclusions hold with ranks determined by any one geometric fiber. They need not equal the constant-coefficient ranks. A nontrivial geometric monodromy representation on $\mathcal L$ changes fiber cohomology even though its dimension remains locally constant over $S$.

### 12.2 Marked and open curves

Suppose $\bar f:\overline C\to S$ is a smooth proper curve and $D\hookrightarrow\overline C$ is finite étale of constant degree $r$. Put $C=\overline C\setminus D$. Although $C\to S$ is not proper, its boundary has been rigidified: no puncture can appear or collide under base change.

For a lisse finite coefficient $\mathcal L$ on $\overline C$, localization gives

$$
j_!\mathcal L|_C\longrightarrow
\mathcal L\longrightarrow i_*\mathcal L|_D\longrightarrow.
$$

Both the proper curve term and the finite étale boundary term commute with arbitrary base change. Therefore $R\bar f_*j_!\mathcal L|_C$, which computes compactly supported fiber cohomology, also commutes with arbitrary base change. For ordinary cohomology use the triangle comparing $j_!$ and $Rj_*$. The local boundary contribution is tame inertia, constant because $D\to S$ is étale. It follows that $R^q f_*\mathcal L|_C$ is lisse and commutes with base change as well.

For constant coefficients and geometrically connected fibers,

$$
\operatorname{rank}H^1(C_{\bar s},\mathbf Z_\ell)
=2g+r-1.
$$

One way to see the $r-1$ is to take degree-zero combinations of small loops around the $r$ punctures: their sum is zero. This description is stable in the family because the punctures form a finite étale local system.

The hypothesis on $D$ is substantial. If sections collide, or a puncture arrives from infinity, boundary cohomology changes. Section 6.4 is precisely the case in which a degree-one boundary point exists over $t\ne0$ but disappears at $t=0$. Smoothness of the open total space does not repair a nonflat boundary.

### 12.3 A nodal degeneration

Let $T$ be a strict henselian trait and let $C\to T$ be a proper flat curve whose generic fiber is a smooth elliptic curve and whose special fiber is an irreducible rational curve with one node. Proper base change gives stalk formulas on both fibers and a specialization map

$$
H^1(C_{\bar s},\Lambda_n)
\longrightarrow
H^1(C_{\bar\eta},\Lambda_n).
$$

Normalize the special fiber:

$$
\nu:\mathbf P^1\longrightarrow C_{\bar s}.
$$

The two preimages of the node give the exact sheaf sequence

$$
0\longrightarrow\Lambda_n
\longrightarrow\nu_*\Lambda_n
\longrightarrow(i_{\mathrm{node}})_*\Lambda_n
\longrightarrow0,
$$

where the last map takes the difference of the values on the two branches. Its long exact sequence yields

$$
H^1(C_{\bar s},\Lambda_n)\cong\Lambda_n,
\qquad
H^2(C_{\bar s},\Lambda_n)\cong\Lambda_n(-1).
$$

The smooth elliptic generic fiber has

$$
H^1(C_{\bar\eta},\Lambda_n)\cong\Lambda_n^2.
$$

Hence specialization in degree one cannot be an isomorphism. The missing rank-one class is the local annular class that collapses at the node. Properness still gives the map and identifies each stalk correctly; failure of smoothness prevents local acyclicity and lissity.

If the special fiber were a tree of smooth components, the dual graph would have no first cohomology; if it contained loops, each graph loop would contribute a degree-one class. This separates component cohomology from combinatorial cohomology and foreshadows the nearby-cycle analysis of Book 24.

## 13. Abelian schemes

### 13.1 The first direct image

Let $f:A\to S$ be an abelian scheme of relative dimension $g$, and assume $\ell$ invertible on $S$. Multiplication by $\ell^n$ is finite étale, so

$$
A[\ell^n]\to S
$$

is a lisse sheaf of free $\Lambda_n$-modules of rank $2g$. Fiberwise, a degree-one cohomology class with constant coefficients is a character of the $\ell^n$-torsion. There is therefore a canonical isomorphism

$$
R^1f_*\Lambda_n
\cong
\underline{\operatorname{Hom}}_{\Lambda_n}
(A[\ell^n],\Lambda_n).
$$

To prove it globally, construct the pairing fiberwise from the Kummer torsors defined by torsion points. Proper base change identifies both stalks with their geometric versions, where the standard abelian-variety calculation is an isomorphism. A morphism between constructible sheaves that is an isomorphism at every geometric stalk is an isomorphism.

Passing to the inverse limit gives

$$
R^1f_*\mathbf Z_\ell
\cong
\underline{\operatorname{Hom}}_{\mathbf Z_\ell}
(T_\ell A,\mathbf Z_\ell).
$$

Thus the cohomological and torsion constructions of the lisse rank-$2g$ sheaf agree. This identification commutes with arbitrary base change because both constructions do.

### 13.2 Exterior powers and arbitrary base change

On every geometric fiber, constant-coefficient cohomology is the exterior algebra on degree one. The cup-product maps

$$
\bigwedge\nolimits^i R^1f_*\Lambda_n
\longrightarrow R^if_*\Lambda_n
$$

are maps of lisse sheaves. They are isomorphisms on every geometric stalk, hence globally. Therefore

$$
R^if_*\Lambda_n
\cong
\bigwedge\nolimits^i R^1f_*\Lambda_n,
\qquad
\operatorname{rank}_{\Lambda_n}R^if_*\Lambda_n
=\binom{2g}{i},
$$

and the sheaf vanishes for $i>2g$.

The transition maps are compatible with exterior powers and are finite free. Adic base change gives

$$
R^if_*\mathbf Z_\ell
\cong
\bigwedge\nolimits^i R^1f_*\mathbf Z_\ell.
$$

For any $S'\to S$, the entire graded algebra pulls back to the corresponding algebra for $A_{S'}$. In particular, specialization between any two geometrically related fibers is an isomorphism in every degree and respects multiplication.

For $g=1$, the ranks are $1,2,1$. For $g=2$, they are $1,4,6,4,1$. The middle rank six includes products of classes from different degree-one directions; it is not obtained by merely listing the cohomology of one-dimensional factors.

### 13.3 Isogenies, polarizations, and endomorphisms

An isogeny $u:A\to B$ over $S$ induces

$$
u^*:R^1f_{B*}\mathbf Z_\ell
\longrightarrow R^1f_{A*}\mathbf Z_\ell
$$

dual to $T_\ell u$. If $\deg u$ is prime to $\ell$, its kernel has no $\ell$-primary part, so this is an integral isomorphism. If $\ell$ divides the degree, kernel or cokernel may survive over $\mathbf Z_\ell$, although the map becomes an isomorphism over $\mathbf Q_\ell$ for every isogeny.

Every endomorphism of $A$ acts on $R^1$ and hence on all exterior powers. Proper base change and Section 11.3 show that these actions commute with specialization. An idempotent in an endomorphism algebra cuts out a direct summand whenever its denominator is invertible in the coefficient ring. If the denominator is divisible by $\ell$, a rational summand need not have an integral direct complement.

A polarization supplies a Weil pairing on $T_\ell A$ with values in $\mathbf Z_\ell(1)$. Dualizing yields the usual alternating form on degree-one cohomology with its Tate twist. Because the polarization is defined over $S$, the form is invariant under monodromy and all specialization isomorphisms are symplectic. This compatibility, rather than only constancy of ranks, is what makes the result useful in arithmetic families.

Over a henselian trait of residue characteristic different from $\ell$, an abelian scheme has unramified $T_\ell A$ and unramified cohomology in all degrees. The statement uses the existence of the abelian scheme over the trait. A generic abelian variety with semistable but non-good reduction is not covered; its nontrivial inertia belongs to the monodromy theory developed later.

## 14. Selected PEL families

### 14.1 The geometric hypotheses

A PEL parameter space records abelian schemes equipped with polarizations, endomorphisms, and level structures. Those words alone do not imply smoothness, representability, or properness. We isolate the precise geometric input.

Let $M\to B$ be one of the low-dimensional parameter spaces used in the arithmetic route. Assume:

1. $B$ is excellent noetherian and $\ell$ is invertible on $B$;
2. $M$ is a smooth quasi-projective scheme over $B$, of relative dimension at most two;
3. the level is sufficiently small that a universal abelian scheme

   $$
   a:\mathcal A\to M
   $$

   exists, and $a$ is smooth proper;
4. the polarization and action by a finite projective order are defined over $M$;
5. when cohomology of $M$ itself is considered, either $M$ is proper over $B$, or a proper compactification $\bar M$ with relative normal-crossings boundary $D$ is part of the data;
6. every prime inverted to make the level, endomorphism order, and boundary tame is also inverted on $B$.

Quaternionic compact families satisfy the proper alternative. Hilbert and unitary families are often nonproper and require the compactified-pair alternative. These are hypotheses, not consequences of the label “PEL.” Construction of the spaces and compactifications belongs to later geometric volumes.

Book 15 supplies coherent finiteness and Hodge bundles once such proper families or compactifications exist. The present results concern their prime-to-residue-characteristic étale coefficient systems and geometric fiber cohomology.

### 14.2 Universal abelian families and coefficient systems

Apply Chapter 13 to $a:\mathcal A\to M$. The sheaf

$$
\mathbb V_{\ell}=R^1a_*\mathbf Z_\ell
$$

is lisse free, commutes with arbitrary change of $M$, and carries the polarization form and endomorphism action. Tensor powers, duals, exterior powers, and direct summands cut out by integral idempotents remain lisse and commute with base change. These are the coefficient systems arising from the algebraic PEL representations needed here.

For example, in relative abelian dimension two,

$$
R^2a_*\mathbf Z_\ell
\cong\bigwedge\nolimits^2\mathbb V_\ell
$$

has rank six. The polarization line is a rank-one Tate-twisted summand after the required denominator is inverted. Its complementary primitive piece is then a lisse direct summand. If that denominator is not invertible at $\ell$, only the rational splitting is justified.

An algebraic correspondence between two universal families, defined by a prime-to-$\ell$ isogeny, acts integrally and commutes with every specialization. A correspondence of degree divisible by $\ell$ still acts, but need not be invertible on the lattice. These distinctions are essential when comparing Hecke operators across characteristic.

The result is relative over $M$, whether or not $M$ is proper over $B$. Properness used here is the properness of the universal abelian scheme $a$. It does not imply that the global cohomology of the open parameter space $M$ commutes with arbitrary base change on $B$.

### 14.3 Proper and nonproper parameter spaces

Suppose first that $m:M\to B$ is smooth proper. For any lisse finite-level PEL coefficient $\mathcal L_n$, smooth proper base change gives lisse sheaves

$$
R^qm_*\mathcal L_n
$$

on $B$, arbitrary base change, and invertible specialization. If the fibers are surfaces, the cohomology lies in $[0,4]$. Passing through the coefficient tower gives the integral and rational statements. Every correspondence proper over both factors acts compatibly.

Now suppose $M$ is nonproper with compactification $j:M\hookrightarrow\bar M$ and relative normal-crossings boundary $i:D\hookrightarrow\bar M$. Compactly supported cohomology is governed by

$$
R\bar m_*j_!\mathcal L_n.
$$

If $\bar m:\bar M\to B$ is proper, proper base change applies to this constructible complex. Thus compactly supported cohomology commutes with arbitrary base change even though $M\to B$ is not proper.

Ordinary cohomology is governed by $R\bar m_*Rj_*\mathcal L_n$. The boundary complex

$$
\mathcal B_n=i^*Rj_*\mathcal L_n
$$

has stalks given by tame inertia cohomology. At a smooth boundary point there is one inertia direction; at a crossing there are two. Under the assumed relative normal-crossings and tame-monodromy hypotheses, these cohomology sheaves are constructible and commute with smooth changes of $B$. If the pair $(\bar M,D)$ is itself smooth in the logarithmic sense over $B$, the boundary stratification is locally constant and ordinary cohomology also has invertible specialization. Without that condition, proper base change still handles $j_!\mathcal L_n$, but ordinary cohomology may jump through the boundary.

Interior cohomology

$$
H^q_!(M_{\bar b},\mathcal L_n)
=
\operatorname{im}\bigl(
H^q_c(M_{\bar b},\mathcal L_n)
\to H^q(M_{\bar b},\mathcal L_n)
\bigr)
$$

is preserved by specialization whenever both maps in the defining arrow are identified compatibly. It is an image, not automatically a direct summand. A projector from correspondences may split it only after its denominators are controlled.

### 14.4 Good reduction and specialization

Let $B$ be a henselian trait with residue characteristic prime to $\ell$. Assume the selected PEL family, its universal abelian scheme, its endomorphisms, polarization, level away from the residue characteristic, and—when needed—its compactified boundary pair all extend smoothly over $B$.

For the universal abelian family, specialization gives

$$
H^q(\mathcal A_{\bar s},\mathbf Z_\ell)
\xrightarrow{\sim}
H^q(\mathcal A_{\bar\eta},\mathbf Z_\ell)
$$

and respects the exterior algebra, polarization, endomorphism algebra, and prime-to-$\ell$ correspondences. For a proper PEL parameter space, the same holds for $H^q(M_{\bar s},\mathcal L)$ and $H^q(M_{\bar\eta},\mathcal L)$. For a nonproper space it holds for compact support under properness of $\bar M$, and for ordinary cohomology only with the boundary control of Section 14.3.

Consequently the generic Galois representations obtained from these good models are unramified and their Frobenius actions can be computed on the special fiber. This is a transport theorem. It neither proves purity nor evaluates a Frobenius trace; those require the trace formula and weight theory of later books.

Bad reduction marks the exact frontier. If the universal abelian object becomes semiabelian, if boundary components collide, or if the coefficient prime equals the residue characteristic, specialization need not be invertible. The appropriate replacement retains inertia and the missing local classes rather than erasing them.

### 14.5 A product-type PEL calculation

Let a smooth parameter curve $M$ carry elliptic schemes $E_1$ and $E_2$ with additional endomorphisms, and put $\mathcal A=E_1\times_M E_2$. Write

$$
\mathbb V_i=R^1(E_i/M)_*\mathbf Z_\ell.
$$

Smooth proper base change and Künneth give

$$
R^1a_*\mathbf Z_\ell
\cong\mathbb V_1\oplus\mathbb V_2
$$

and

$$
R^2a_*\mathbf Z_\ell
\cong
\mathbf Z_\ell(-1)
\oplus(\mathbb V_1\otimes\mathbb V_2)
\oplus\mathbf Z_\ell(-1).
$$

The outer summands are the degree-two classes of the elliptic factors. The middle rank-four summand contains the mixed classes. An idempotent supplied by endomorphism data can isolate part of it when its denominator is invertible at $\ell$.

Every decomposition commutes with base change because it is built from projections, cup products, and integral idempotents. Under good reduction over a trait, Frobenius respects it. If an isogeny used in a projector has degree divisible by $\ell$, a rational splitting may remain while the integral decomposition fails.

## 15. A reusable comparison package

### 15.1 The theorem checklist

The following checklist packages the results without blurring their hypotheses.

**Finite constructibility package.** For a separated finite-type morphism over an excellent noetherian base and finite constructible coefficients of invertible order, higher direct images are constructible and uniformly bounded in the required dimensions. Geometric-fiber groups are finite.

**Proper package.** If the morphism whose direct image is taken is proper, its bounded constructible direct image commutes with every change of base. Stalks are geometric-fiber cohomology. No smoothness is required, and specialization maps exist even in singular degenerations.

**Smooth-horizontal package.** If the change-of-base map is smooth, direct image for a separated finite-type morphism commutes with that change. The original morphism need not be proper.

**Smooth-vertical package.** A smooth morphism is universally locally acyclic relative to lisse finite coefficients of invertible order. If it is also proper, higher direct images are lisse and all specialization maps are isomorphisms.

**Adic package.** The finite-level statements pass to a normalized $\mathbf Z_\ell$-system when amplitude is uniform and finite cohomology gives Mittag--Leffler. Rationalization takes place after derived inverse limit.

**Functorial package.** Cup products, external products, projection formulas, Leray filtrations, and proper correspondences commute with base change and specialization. Tor terms must be retained unless coefficient cohomology is free.

### 15.2 The chain of reductions

The proof mechanism can be summarized as a sequence in which every arrow has a purpose:

$$
\begin{array}{c}
\text{constructible complex}\\
\downarrow\ \text{truncation and support filtration}\\
\text{lisse sheaf on a normal stratum}\\
\downarrow\ \text{finite étale descent}\\
\text{constant finite coefficient}\\
\downarrow\ \text{compactification}\\
\text{proper term plus lower-dimensional boundary}\\
\downarrow\ \text{strict localization}\\
\text{closed fiber over a strictly henselian base}\\
\downarrow\ \text{trait and relative-pencil reduction}\\
\text{finite maps, smooth charts, and nodes}.
\end{array}
$$

Finite maps are immediate. Smooth charts reduce to affine-space acyclicity. Nodes reduce to the two-term tame inertia complex and the incidence map of their branches. Noetherian induction handles smaller supports; cohomological descent removes modifications. This proves finite-level comparison.

Constructibility then spreads the local result across a finite stratification. Properness identifies strict-local stalks with fibers. Smoothness makes local tubes acyclic. Finiteness makes coefficient towers Mittag--Leffler. These are four distinct transitions, and none can safely be omitted.

### 15.3 Conclusion

Base change turns fiberwise cohomology into a geometric object on the base. Properness prevents classes from escaping at infinity and identifies direct-image stalks with geometric fibers. Smoothness removes local vanishing classes for lisse prime-to-characteristic coefficients. Together they make the cohomology of a smooth proper family a lisse system with canonical transport, monodromy, products, and specialization.

The theorem remains informative when smoothness fails. A nodal curve still satisfies proper base change, so its special cohomology is the correct stalk; the failure of specialization to be invertible precisely records degeneration. It also remains informative when properness fails, provided a boundary is supplied: compactification and the boundary triangle show exactly which classes may enter from infinity.

For relative curves this yields constant genus cohomology and unramified good-reduction representations. For abelian schemes it globalizes the Tate module and the entire exterior cohomology algebra. For selected PEL families it transports endomorphisms, polarizations, coefficient systems, and proper correspondences across good fibers while keeping the open-boundary caveat visible.

The final lesson is a discipline of hypotheses. Coefficient invertibility controls tame local geometry. Excellence and noetherianity make dévissage finite. Properness controls global fibers. Smoothness controls local tubes. Geometric points detect the comparison. Uniform finite-level bounds justify the adic limit. Once each condition is placed where it is actually used, proper and smooth base change become not isolated miracles but a coherent transport mechanism for arithmetic geometry.
