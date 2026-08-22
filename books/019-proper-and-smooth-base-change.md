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
   - [Compactifiable morphisms and the boundary](#42-compactifiable-morphisms-and-the-boundary)
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

- [Exterior powers and arbitrary base change](#131-exterior-powers-and-arbitrary-base-change)
- [Isogenies, polarizations, and endomorphisms](#132-isogenies-polarizations-and-endomorphisms)

14. [PEL abelian families and parameter spaces](#14-pel-abelian-families-and-parameter-spaces)

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

A constructible sheaf has finite stalks and is lisse on the pieces of a finite locally closed stratification. A bounded constructible complex belongs to $D^b_c(X,\Lambda)$. We use the derived direct image $Rf_*$, exact inverse image $g^*$, derived tensor $\otimes^L$, and cohomological grading. The foundations, spectral sequences, finite-level finiteness, and derived inverse limits were established in Book 18.

The invertibility hypothesis plays different roles in different results. The formal proper comparison theorem has versions for arbitrary torsion, but the proof developed here uses prime-to-residue-characteristic purity, tame local calculations, and uniform cohomological-dimension bounds. Accordingly every stated finiteness, smooth base-change, and local-acyclicity result keeps $N$ invertible. This is exactly the range required for $\ell$-adic cohomology at places away from $\ell$. At a residue characteristic equal to $\ell$, these statements cannot simply be reused: wild ramification and inseparable phenomena demand another theory.

### 1.3 The four main theorems

The narrative culminates in four assertions.

**Constructibility.** If $f:X\to S$ is compactifiable in the sense of Section 4.2 — separated, of finite type, and an open subscheme of a proper $S$-scheme, which every quasi-projective $f$ is — and if $S$ is excellent noetherian, $N$ is invertible on $S$, and $K\in D^b_c(X,\Lambda)$, then $Rf_*K$ has constructible cohomology and is locally bounded. If $f$ is proper of relative dimension at most $d$ and $K$ has amplitude $[a,b]$, the bound is $[a,b+2d]$. For a nonproper map, boundary cohomology contributes to the bound; relative fiber dimension alone does not control the amplitude of $Rf_*$.

**Proper base change.** If $f:X\to S$ is proper, with $S$ noetherian, and $K\in D^b_c(X,\Lambda)$ with $N$ invertible on $S$, then for every $g:S'\to S$ the canonical map

$$
g^*Rf_*K\xrightarrow{\sim}Rf'_*g'^*K
$$

is an isomorphism. In particular,

$$
(R^qf_*K)_{\bar s}\cong H^q(X_{\bar s},K|_{X_{\bar s}}).
$$

**Smooth base change.** In the displayed square, if $g$ is smooth, $S$ and $S'$ are excellent noetherian, and $f$ is compactifiable, then the same comparison is an isomorphism for bounded constructible prime-to-residue-characteristic coefficients. Properness of $f$ is not required; a compactification of $f$ is.

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

Book 18 established the following absolute input. If $k$ is separably closed, $Y$ is separated of finite type over $k$ of dimension $d$, and $\mathcal F$ is a constructible finite $\Lambda$-sheaf with $N$ prime to $\operatorname{char}k$, then every $H^q(Y,\mathcal F)$ is finite and

$$
H^q(Y,\mathcal F)=0\qquad(q>2\dim Y).
$$

It also established the corresponding finite bound $2g$ for an abelian variety of dimension $g$. These statements are enough for relative curves, abelian schemes, and the Hilbert--Blumenthal parameter spaces retained below. For a proper curve, the bound is $[0,2]$; for a smooth affine curve it improves to $[0,1]$. In higher-dimensional Hilbert cases one uses the general $2d$ bound for a $d$-dimensional fiber.

These results used constructible dévissage, finite étale descent, compactification, and the Kummer calculation for curves and abelian varieties. We do not reprove those derived foundations. We do prove the relative constructibility needed here, whose additional content is uniformity as the fiber moves.

No corresponding assertion is made when $N$ is not invertible. In characteristic $p$, Artin--Schreier covers create abundant $p$-torsion phenomena on affine schemes, and the tame purity calculation used below is unavailable.

### 3.3 Constructibility of direct images

**Relative constructibility theorem.** Let $S$ be excellent and noetherian, let $f:X\to S$ be compactifiable in the sense of Section 4.2, and let $K\in D^b_c(X,\Lambda)$, where $N\Lambda=0$ and $N$ is invertible on $S$. Then:

1. Every $R^qf_*K$ is constructible, and the direct image is locally bounded. On each finite-dimensional quasi-compact open of $S$, only finitely many $q$ occur. The single exception is recorded after clause 3: for a proper family of curves, the top row is supplied through its formation and stalk values only.
2. There is a finite stratification of $S$ into locally closed subschemes such that, over each stratum $W$, every $R^qf_*K$ is lisse and its formation commutes with every base change $T\to W$: the canonical map $g^*R^qf_*K\to R^qf_{T*}g'^*K$ is an isomorphism for all $g:T\to W$.
3. Étale-locally on each stratum there is a single bounded complex $P^\bullet$ of finite free $\Lambda$-modules — the _uniform presentation complex_ — with $Rf_*K\simeq P^\bullet$ over that stratum, so that clause 2 holds simultaneously for all degrees through one object.

One deliberate narrowing is part of the statement, inherited from Book 18, Section 7.2: for a proper family whose geometric fibers are curves, the top row — relative degree two — is supplied with compatible formation and geometric stalk values, but not asserted lisse; identifying it belongs to purity and trace machinery later in this book and in Book 20. Every consumer below uses that row only through stalks and formation.

By the quasi-projective compactification theorem the hypothesis holds whenever $f$ is quasi-projective, which covers every application made in this book and its successors; by Nagata's theorem it holds for every separated finite-type $f$, but that theorem is not proved here and is not used.

The proof below constructs the uniform complex rather than choosing presentation matrices separately at each point of the base: the pointwise choices of Section 5.1 are replaced by relative objects whose formation commutes with base change, and strict localization enters once, through the continuity machinery of Book 18, Sections 4.5 and 4.6, instead of being reverified matrix by matrix.

**Step 1: reduction to lisse strata.** Truncation triangles express $K$ through its cohomology sheaves, and the class of sheaves satisfying clauses 1–3 is stable under kernels, cokernels, and extensions because the corresponding operations on direct images are read off long exact sequences, in which kernels, cokernels, and extensions of lisse sheaves on a fixed stratum are again lisse (Book 18, Section 3.1). The localization triangle of Section 4.1 reduces further to $\mathcal F=j_!\mathcal L$ for a lisse finite $\Lambda$-sheaf $\mathcal L$ on a locally closed stratum $Z\subseteq X$: the cone terms have strictly smaller coefficient support, and noetherian induction on that support disposes of them. A finite étale Galois cover $v:V_Z\to Z$ trivializes $\mathcal L$; as in Section 4.1 we keep the group $G$ and its finitely many descent operators visible rather than killing them by an unbounded resolution. By part (2) of the stability lemma of Section 4.2 the composite $Z\to S$ is again compactifiable, so each stratum carries its own compactification.

**Step 2: reduction of the general case to the proper case.** Compactify $f$ as $X\xrightarrow{j}\overline X\xrightarrow{\bar f}S$ and write $Rf_*K=R\bar f_*Rj_*K$. The localization triangle on $\overline X$,

$$
j_!K\longrightarrow Rj_*K\longrightarrow Q\longrightarrow,
$$

splits the problem into two terms pushed forward along the _proper_ morphism $\bar f$: the extension-by-zero term $j_!K$, which is a bounded constructible complex on $\overline X$ unconditionally (extension by zero preserves boundedness and constructibility, Book 18, Section 3.3), and the boundary cone $Q$, supported on $D=\overline X\setminus X$. Now observe that $Q$ is constructible as soon as $Rj_*K$ is, and that the assertion "$R^qj_*K$ is constructible on $\overline X$" is exactly the present theorem applied to the morphism $j:X\to\overline X$, whose fibers are single points. Ordering the proof by the relative dimension of the morphism therefore reduces clause-by-clause: everything is pushed forward properly, and the only input about nonproper geometry — the constructibility of $Rj_*K$ — belongs to relative dimension zero, treated first.

**Step 3: relative dimension zero.** Let $f:X\to S$ be compactifiable with fibers of dimension zero, and let $\mathcal F=j_!\mathcal L$ as in Step 1. Compactify $f$ and shrink $S$ so that $\overline X\to S$ has zero-dimensional fibers; a proper morphism all of whose fibers are finite sets is finite, by the standard argument recorded in Books 8, 9, and 17. Then $R^qf_*\mathcal F=R^q\bar f_*(j_!\mathcal F)$ with $\bar f$ finite, so $R^q=0$ for every $q>0$ and the problem is to stratify the sheaf $\bar f_*(j_!\mathcal L)$. Let $E\subseteq\overline X$ be the locus where $\overline X\to S$ is étale: it is open in $\overline X$, being the intersection of the flat locus — open over the locally noetherian base, by generic flatness applied fiberwise — with the unramified locus, which is always open. Over $E$, the morphism to its image in $S$ is finite étale, and finite étale morphisms are open, so the image is an open subscheme of $S$. On that image the pushforward of a lisse sheaf under a finite étale morphism is lisse, and its formation commutes with every base change, because finite étale pullbacks compose associatively and the pushforward along a finite étale cover is computed sectionwise. The sheaf $j_!\mathcal L$ restricts to $E$ as a lisse extension from a constructible stratification of $E$, and each stratum is finite étale over a locally closed piece of $S$, where the same sectionwise argument applies. The complement of the settled pieces is closed in $\overline X$ and still finite over $S$, with strictly smaller coefficient support; noetherian induction closes the case. This proves the theorem in relative dimension zero, including clause 3: over each piece the uniform complex has length one.

**Step 4: the proper case by induction on relative dimension.** Let $f:Y\to S$ be proper with fibers of dimension at most $d$, and assume the theorem proved for every compactifiable morphism whose geometric fibers have dimension less than $d$, over every excellent noetherian base. We prove it for $f$ and all of its strata simultaneously; the induction measure is the pair (relative dimension of the morphism carrying the coefficient, coefficient-support dimension), ordered lexicographically.

By Step 1 reduce to $\mathcal F=j_!\mathcal L$ on a locally closed stratum $Z\subseteq Y$, and replace $Y$ by the closure $\overline Z$ of $Z$ in a fixed compactification; $\bar f:\overline Z\to S$ remains proper. Since $\overline X$ is noetherian, we may argue component by component: shrink $S$ so that it is integral with generic point $\eta$, prove the theorem over a dense open of $S$, and then run noetherian induction on the complement (Step 6).

_Spreading the fibration._ The generic fiber $Y_\eta$ is a variety of dimension at most $d$ over the field $\kappa(\eta)$. Exactly as in the affine constructible lemma of Book 18, Section 7.2, choose a separating transcendence basis of $\kappa(Y_\eta)/\kappa(\eta)$ — separating after the harmless purely inseparable reduction, which does not change the étale site — and realize all but one basis element as coordinates of a rational projection of the chosen projective embedding. Every datum involved is defined over a finitely generated subring of $\kappa(\eta)$, and spreading finite-presentation data over dense opens (the same mechanism as the descent remark in Section 6.1) realizes, after shrinking $S$, an open subscheme $B\subseteq\mathbf P^{d-1}_S$, a dense open $Y^\circ\subseteq Y$ containing $Z$, and a factorization

$$
Y^\circ\xrightarrow{\;g\;}B\xrightarrow{\;\pi\;}S
$$

where $g$ is smooth with geometrically nonempty curve fibers and $\pi$ is proper with fibers of dimension at most $d-1$; moreover $g$ extends to a proper morphism $\bar g:\overline Y{}^\circ\to B$ of relative dimension one — the compactified fibration, realized inside $\mathbf P^1_B\times_SB$-charts by the same projection data — and $Y^\circ\subseteq\overline Y{}^\circ$ is the complement of a relative effective Cartier divisor $D_0$. Deleting first the nonflat locus of $D_0$ over $B$ and then its branch locus makes $D_0$ finite étale over $B$; both deletions are closed subsets of smaller dimension or support, reattached inductively as in the remark below. If $d=1$ one takes $B=S$ and skips $\pi$, keeping the curve stage itself.

_Composition of direct images._ Write $j:Y^\circ\hookrightarrow\overline Y{}^\circ$. Then

$$
Rf'_*(\mathcal F|_{Y^\circ})=R\pi_*\,R\bar g_*\,(Rj_*(\mathcal F|_{Y^\circ})).
$$

The coefficient complex $Rj_*(\mathcal F|_{Y^\circ})$ is bounded and constructible on $\overline Y{}^\circ$ because $j$ has zero-dimensional fibers and Step 3 applies to it. The morphism $\bar g$ is proper of relative dimension one with smooth curve fibers, so the base case of the induction governs it; we record that base case here.

_The base case: proper families of curves._ Let $h:C\to T$ be proper with smooth geometrically nonempty curve fibers, and let the coefficient be a lisse finite $\Lambda$-sheaf on a constructible stratification of $C$ — after the dévissage of Step 1 this is the only form in which coefficients enter. The relative curve theorem of Book 18, Section 7.2, part 1, applies verbatim to each lisse piece: $R^qh_*\mathcal L=0$ for $q\ge3$, the rows $R^0h_*$ and $R^1h_*$ are lisse, and the canonical base-change maps are isomorphisms for every $T'\to T$ and every $q$. The descent operators of the trivializing cover enter these lisse sheaves, since part 3 of that proof treats arbitrary lisse coefficients, not merely constant ones; gluing along the localization triangles of the stratification preserves all three properties. Row two deserves the same deliberate narrowing made in Book 18, Section 7.2: its geometric stalks are cyclic of order $n$ and form compatibly under every base change, but proving that the row itself is lisse amounts to identifying it with the cyclotomic twist, which belongs to the purity and trace machinery of Chapter 12 and Book 20 and is not available at this point of the logical order. Accordingly, for proper curve families this chapter supplies rows zero and one in full uniform-complex form, compatible formation and stalk values for row two, and nothing more about row two; no argument in Chapters 9 through 15 consumes more.

_Conclusion of the induction step._ With $P:=R\bar g_*(Rj_*(\mathcal F|_{Y^\circ}))$, the base case gives $P\in D^b(B)$ with amplitude $[0,2]$, whose rows zero and one are lisse on all of $B$ with formation commuting with every base change, and whose remaining row carries compatible formation and stalk values. Applying the induction hypothesis to $\pi$ — relative dimension $d-1$, excellence inherited — pushes $P$ forward: each constructible row lands in the finite stratification with lisse direct images of compatible formation, the amplitude bound of Section 3.4 shows only finitely many degrees occur, and, étale-locally on each stratum, the uniform complex of clause 3 for $\pi$, totalized against the two controlled rows, is the uniform complex for $f'$. For $d=1$ there is no $\pi$, and the output is exactly what the base case records.

_Remark on the deleted loci._ Everything deleted in the spreading step — the discriminant, the nonflat locus, the branch locus, the preimages in $Y$ — is a closed subset of $Y$ or $S$ of strictly smaller dimension or support, and carries the restricted coefficient. The localization triangle reattaches it, and the same two reductions (proper case, lower relative dimension or smaller support) apply. This is what replaces the old appeal to "the same finite matrices" controlling the boundary: the boundary is handled by re-running the theorem, not by asserting that pointwise matrices agree.

**Step 5: strict-localization compatibility.** Clause 2 asserts compatibility with arbitrary base change of the stratum, and strict localization is the special case relevant for stalks. We record why the identification is the canonical one. Let $W$ be a stratum, $P^\bullet$ the uniform complex on an étale neighborhood $V$ of a geometric point $\bar s$, with an isomorphism $\alpha:P^\bullet|_V\xrightarrow{\sim}R(f_V)_*K_V$. Both sides descend through the filtered system of affine pointed étale neighborhoods: the complex $P^\bullet$ is given by finitely many finite modules, maps, and homotopy relations, and the isomorphism $\alpha$ by finitely many cochain-level data, all of which spread to some common level $V_0$ by the descent mechanism of Section 6.1, whose proof used nothing beyond Book 18, Sections 4.5 and 4.6. The Descent theorem of Book 18, Section 4.5, computes cohomology on every member of the system from finite truncated hypercovers, and the Continuity theorem of Book 18, Section 4.6, identifies the colimit of the descended complexes with the cohomology over the strict localization $S_{(\bar s)}$. Chasing $\alpha$ through these identifications shows that the induced isomorphism on strict-local cohomology agrees with the stalk of $\alpha$ and identifies both with the cohomology of the geometric fiber — for the left side by clause 2 applied to the strict-local base change, for the right side by the strict-local proper theorem of Section 5.1, whose proof is independent of the present chapter. In particular the lisse sheaves of clause 2 have the geometric-fiber cohomology groups as stalks, compatibly with specialization.

**Step 6: termination.** Each application of a reduction step lowers exactly one of three measures: the relative dimension of the morphism carrying the coefficient (Steps 3 and 4), the coefficient-support dimension (Step 1), or the dimension of the closed subset of $S$ on which the conclusion is not yet established (the noetherian inductions inside Steps 3 and 4). Noetherian spaces admit no infinite strictly descending chains under these measures, so the procedure terminates and leaves finitely many strata. Excellence guarantees throughout that normalizations in finite field extensions are finite and that compactifications and strata remain noetherian of finite type, as recorded in Section 3.5. $\square$

There is no circularity. The strict-local proper statement of Chapter 5 is proved directly from finite hypercover presentations and does not use relative constructibility; the relative curve theorem of Book 18, Section 7.2, rests on Book 17a's Picard construction and Book 18's own descent and continuity results, not on this chapter; and the induction above consumes only statements about strictly smaller relative dimension or support. Smooth local acyclicity is not used anywhere in the proof; it is constructed independently in Chapters 7 and 8.

**Passage to adic coefficients.** The theorem as stated concerns finite coefficients killed by $N$. For a tower $(\Lambda_n)$ with compatible complexes $K_n$ forming an adic system in the sense of Book 18, Section 8, the stratification and the uniform complexes can be taken independent of $n$ — this is the content of the uniformity-in-exponent discussion of Book 18, Section 7.3, applied to the output of Steps 3 and 4 — and $Rf_*$ of the adic complex is then controlled levelwise, with the derived-inverse-limit caveats recorded in Chapter 10. What is _not_ claimed here is base-change compatibility for the adic direct images themselves; that passage is carried out in Chapter 10 after the finite-level comparison maps have been shown compatible in the tower, and it inherits the present clause 2 rather than strengthening it.

### 3.4 Uniform amplitude and complexes

Suppose first that $f$ is proper, its geometric fibers have dimension at most $d$, and $K$ has cohomology only in $[a,b]$. The hypercohomology spectral sequence

$$
R^p f_*\mathcal H^q(K)\Longrightarrow R^{p+q}f_*K
$$

shows that a uniform fiberwise bound for sheaves gives one for complexes. In the proper prime-to-characteristic range, the safe bound is

$$
R^m f_*K=0\qquad(m\notin[a,b+2d]).
$$

For the cohomology of a geometric smooth affine curve, the upper addition is $1$. This does not give the same bound for $Rf_*$ of an arbitrary nonproper relative curve: for an open immersion, tame boundary inertia can already create $R^1j_*$ although the relative fibers have dimension zero. In the nonproper case, a chosen compactification gives a finite local bound depending also on the boundary stratification. Uniformity in the exponent $n$ of $\Lambda_n$ is crucial: it permits finite totalizations and derived inverse limits to be interchanged.

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

reduces $P(Z,K)$ to the lisse term on $U$ and a term with smaller support. A finite étale cover $v:V\to U$ trivializes the lisse sheaf. After passing to a Galois closure with group $G$, the original object is recovered from the constant coefficient upstairs together with its descent operators. The bar resolution need not be bounded when $|G|$ is not invertible in $\Lambda$, so it is not used as a vanishing argument. Instead the finite presentation complexes of Section 5.1 retain the finitely many operators and relations required in each cohomological degree. Thus the difficult geometric case is a constant finite coefficient on a normal connected stratum, while descent remains visible in the matrices.

This is constructible dévissage. It is more precise than working stratum by stratum: extension by zero records how strata attach, while the localization triangle carries the connecting morphisms between their cohomology. Ignoring these morphisms may preserve dimensions but loses the derived comparison.

Noetherian induction is used on closed subsets, not on individual points. At each stage a dense open is settled uniformly; its closed complement has strictly smaller support. Hence the procedure ends after finitely many stages.

### 4.2 Compactifiable morphisms and the boundary

Every boundary argument below begins by embedding a nonproper morphism into a proper one. We give that property a name instead of assuming it for all morphisms.

**Definition.** A separated morphism of finite type $f:X\to S$ is _compactifiable_ if it admits a factorization

$$
X\xrightarrow{j}\overline X\xrightarrow{\bar f}S
$$

with $j$ an open immersion and $\bar f$ proper. The pair $(\overline X,j)$ is a _compactification_ of $f$, and $D=\overline X\setminus X$, with its reduced structure, is the _boundary_. Nothing is asserted about $\overline X$ beyond properness. It need not be smooth, normal, or reduced, and $D$ need not be a divisor, still less a normal-crossings one. Where smoothness or normal crossings are wanted — for marked curves in Section 12.2, for the parameter spaces of Section 14.1 — they are imposed as explicit hypotheses.

One may always arrange that $X$ is schematically dense in $\overline X$, by replacing $\overline X$ with the scheme-theoretic closure of $X$ in it. The replacement is a closed subscheme of $\overline X$ and hence still proper over $S$, and $X$ is still open in it by the argument used in the next proof.

**Quasi-projective compactification theorem.** Let $S$ be noetherian and let $f:X\to S$ be quasi-projective, that is, $f=\pi\circ i$ for an immersion $i:X\hookrightarrow\mathbf P^n_S$ and the structure morphism $\pi:\mathbf P^n_S\to S$. Then $f$ is compactifiable, and one may take $\overline X$ to be the scheme-theoretic closure of $X$ in $\mathbf P^n_S$.

**Proof.** An immersion factors as a closed immersion into an open subscheme: there is an open $W\subseteq\mathbf P^n_S$ such that $i$ induces a closed immersion $X\hookrightarrow W$. Since $S$ is noetherian, so is $\mathbf P^n_S$; therefore $i$ is quasi-compact and the scheme-theoretic image

$$
\overline X\subseteq\mathbf P^n_S,
\qquad
\mathcal I=\ker\bigl(\mathcal O_{\mathbf P^n_S}\to i_*\mathcal O_X\bigr),
$$

is a closed subscheme, the smallest one through which $i$ factors. Formation of $\mathcal I$ is a kernel of a map of sheaves and therefore commutes with restriction to an open subscheme. Hence $\overline X\cap W$ is the scheme-theoretic image of the closed immersion $X\hookrightarrow W$, which is $X$ itself. So $X=\overline X\cap W$ is open in $\overline X$ and $j$ is an open immersion. Finally $\overline X$ is a closed subscheme of $\mathbf P^n_S$, which is proper over $S$; a closed immersion is proper and properness is stable under composition, so $\bar f$ is proper. $\square$

**Stability lemma.** Let $S$ be noetherian and let $f:X\to S$ be compactifiable, with compactification $(\overline X,j)$.

1. _Base change._ For any $g:S'\to S$, the base change $f':X\times_SS'\to S'$ is compactifiable, and $\overline X\times_SS'$ is a compactification of it.
2. _Locally closed subschemes._ For any immersion $h:Z\hookrightarrow X$, the composite $f\circ h$ is compactifiable.

**Proof.** For (1), properness and open immersions are both stable under base change, so $\overline X\times_SS'\to S'$ is proper and $X\times_SS'$ is open in it. For (2), write $Z$ as a closed subscheme of an open $U\subseteq X$; then $U$ is open in $\overline X$, and $Z\to\overline X$ is quasi-compact because $\overline X$ is noetherian. Let $\overline Z$ be the scheme-theoretic closure of $Z$ in $\overline X$. Exactly as in the proof above, $\overline Z\cap U$ is the scheme-theoretic image of the closed immersion $Z\hookrightarrow U$, namely $Z$; so $Z$ is open in $\overline Z$, while $\overline Z$ is a closed subscheme of $\overline X$ and hence proper over $S$. $\square$

Part (2) is what the dévissage of Section 4.1 actually consumes: a constructible complex is reduced to extensions by zero from locally closed strata of $X$, and each stratum must itself be compactified over $S$. Quasi-projectivity is inherited in the same two ways, since an immersion into a quasi-projective $S$-scheme is again an immersion into $\mathbf P^n_S$, and $\mathbf P^n_{S'}=\mathbf P^n_S\times_SS'$. No closure of the compactifiable class under composition is asserted anywhere below, and none is used; that closure is precisely the difficult part of the general theory.

**Independence of the compactification.** Let $(\overline X_1,j_1)$ and $(\overline X_2,j_2)$ be compactifications of $f$ and let $K\in D^b_c(X,\Lambda)$. Then

$$
R\bar f_{1*}j_{1!}K\simeq R\bar f_{2*}j_{2!}K
$$

canonically. Because $f$ is separated, the diagonal $X\to X\times_SX$ is a closed immersion, and $X\times_SX$ is open in $\overline X_1\times_S\overline X_2$; hence $(j_1,j_2)$ is an immersion. Let $\overline X_3$ be its scheme-theoretic closure. As above $X$ is open in $\overline X_3$, and $\overline X_3$ is closed in the proper $S$-scheme $\overline X_1\times_S\overline X_2$, so $\bar f_3$ is proper. Each projection $p_i:\overline X_3\to\overline X_i$ is a morphism from a proper $S$-scheme to a separated $S$-scheme and is therefore proper, and $p_i\circ j_3=j_i$.

Now $p_1^{-1}(X)=X$ inside $\overline X_3$: the graph of $j_2$ realizes $X$ as a closed subscheme of $X\times_S\overline X_2$, because that graph is a base change of the diagonal of the separated $\overline X_2/S$, and $X\times_S\overline X_2$ is open in $\overline X_1\times_S\overline X_2$. Proper base change, proved in Section 6.1, computes the stalk of $Rp_{1*}j_{3!}K$ at a geometric point $\bar y$ of $\overline X_1$ as the cohomology of the geometric fiber $p_1^{-1}(\bar y)$ with coefficients $j_{3!}K$. If $\bar y$ lies in $X$ that fiber is the single point $\bar y$ and the stalk is $K_{\bar y}$; if $\bar y$ lies in the boundary the fiber misses $X$, where alone $j_{3!}K$ is nonzero, and the stalk vanishes. Hence $Rp_{1*}j_{3!}K\simeq j_{1!}K$, and

$$
R\bar f_{3*}j_{3!}K
\simeq R\bar f_{1*}Rp_{1*}j_{3!}K
\simeq R\bar f_{1*}j_{1!}K,
$$

with the same computation for the index $2$. This is the sense in which the compactly supported direct image $Rf_!$ below is attached to $f$ and not to a chosen boundary. The argument uses Chapter 6 and nothing later; conversely, Chapters 3 through 7 use only the _existence_ of a compactification, never its uniqueness, so the order of proof is not circular.

**Remark on the general statement.** Every separated morphism of finite type between noetherian schemes is compactifiable. This is Nagata's compactification theorem, and it is not proved here. The tempting short argument — compactify finitely many affine charts of $X$ inside projective spaces and glue the closures along the graphs of the identifications — does not close: the closures need not agree along the overlaps, and repairing them requires a controlled system of blowups, or an argument through the Zariski–Riemann space of the ambient function field. Modern write-ups run to tens of pages. The general statement is also stronger than anything used in this corpus. Every morphism compactified below is quasi-projective and is therefore covered by the theorem just proved: the affine and quasi-projective curves of Chapter 12 and their products, the affine-space projections of Sections 7.1 and 7.2, the locally closed strata of such schemes supplied by the stability lemma, and the smooth quasi-projective PEL parameter spaces of Section 14.1 — whose compactifications, when their global cohomology is considered at all, are part of the geometric data quantified over there rather than a consequence of any theorem.

Let $i:D=\overline X\setminus X\hookrightarrow\overline X$. Then

$$
Rf_*K=R\bar f_*Rj_*K,
\qquad
Rf_!K=R\bar f_*j_!K.
$$

The cone of $j_!K\to Rj_*K$ is supported on $D$. The strict-local proper theorem handles the compactified map, while the difference between ordinary and compactly supported cohomology is a boundary problem. No resolution of $D$ is needed for the general theorem. Normalize one dense boundary stratum at a time, trivialize its lisse coefficient by finite étale descent, and remove its branch and nonnormal loci. At the generic point of a codimension-one branch the local calculation is the punctured strict henselian trait

$$
M\xrightarrow{\tau-1}M.
$$

This display uses a chosen tame generator; intrinsically the degree-one term transforms with the inverse cyclotomic twist. Wild inertia has pro-order prime to the order of $M$, so taking its invariants is exact. Higher intersections, branch loci, and nonnormal loci have smaller support and are handled by noetherian induction. In the normal-crossings cases used for marked curves and compactified Hilbert--Blumenthal parameter spaces this procedure is the familiar tame-inertia complex, with one factor for each local boundary branch.

Compactifiability is essential in constructibility and smooth base change, where $f$ need not be proper. It also explains counterexamples: a nonproper family can change because its boundary changes.

### 4.3 Reduction to a strict henselian trait

The stalk formula reduces proper base change to a proper map over a strictly local base $S$ and

$$
R\Gamma(X,K)\longrightarrow R\Gamma(X_s,K_s).
$$

A second reduction turns an arbitrary generization into a one-dimensional problem. Let $\eta$ specialize to $s$. Take the closure of $\eta$, normalize it, and localize at a point over $s$. Excellence makes normalization finite in the required setting. Strict henselization then produces a strict henselian trait $T\to S$, with closed point over $s$ and generic point over a finite extension of $\kappa(\eta)$. Since constructible sheaves are detected on geometric stalks, it is enough to control specialization over such traits.

For a base of larger dimension, choose a chain of immediate specializations and repeat. Noetherianity makes the dimension drop finite. The trait calculation is therefore a detection argument, not merely an illustrative slice.

### 4.4 Why the reductions terminate

Three measures decrease. Constructible dévissage lowers the dimension of coefficient support. Compactification moves failure to a boundary of smaller dimension. Trait reduction replaces a specialization by a one-dimensional local problem. Finite étale descent changes none of these measures but trivializes monodromy after a finite step.

In the required range, normalization separates the zero-dimensional defects of curves, while a nonproper Hilbert--Blumenthal parameter space enters only when a normal-crossings compactification is supplied as an explicit hypothesis. Every presentation complex is finite in each fixed cohomological range, and Book 18 supplies a uniform cohomological bound. Thus neither an infinite geometric process nor an unproved alteration theorem is concealed.

## 5. The strict-local proper theorem

### 5.1 The decisive comparison

**Strict-local proper theorem.** Let $S$ be a strictly henselian noetherian local scheme with closed point $s$, let $f:X\to S$ be proper, and let $K\in D^b_c(X,\Lambda)$, where $N\Lambda=0$ and $N$ is invertible on $S$. Then restriction induces

$$
R\Gamma(X,K)\xrightarrow{\sim}R\Gamma(X_s,K_s).
$$

The proof rests on the following finite-presentation form of the proper-neighborhood argument.

**Proper-neighborhood lemma.** Let $(S,s)$ be as in the theorem, let $Y\to S$ be proper, and let $\mathcal F$ be a constructible finite $\Lambda$-sheaf on $Y$. For every $r\geq0$ there is a bounded complex $P_r$ of finite $\Lambda$-modules and compatible maps

$$
P_r\longrightarrow R\Gamma(Y,\mathcal F),
\qquad
P_r\longrightarrow R\Gamma(Y_s,\mathcal F_s)
$$

which induce isomorphisms in degrees at most $r$ and injections in degree $r+1$; under these identifications, restriction is the identity of $P_r$.

**Proof of the lemma.** We first explain the neighborhood principle. A finite collection of étale neighborhoods of points of $Y_s$ lifts to étale neighborhoods in $Y$: write each morphism locally in standard étale form and lift its finitely many coefficients. The images of the lifts contain $Y_s$. Their complement is closed in $Y$, and its image in $S$ is closed because $Y$ is proper. That image does not contain $s$, so it is empty: every nonempty closed subset of the spectrum of a local ring contains the closed point. Hence the lifted neighborhoods cover all of $Y$. The same argument applies after any finite fiber product and therefore lifts a finite truncated hypercover. A finite list of equalities between coefficient sections also lifts after refinement, because equality of sheaf sections is detected on stalks.

Now fix a degree $q\leq r$. A class of $H^q(Y_s,\mathcal F_s)$ is represented on an étale hypercover truncated in simplicial degree $q+1$. Properness of $Y_s$ and constructibility of $\mathcal F_s$ let us choose finitely many quasi-compact objects and finitely many coefficient sections at every occurring level. Lift this finite hypercover, its sections, and the cocycle identities by the neighborhood principle. The lifted cocycle gives a class on $Y$ restricting to the original class. This proves surjectivity.

For injectivity, let a class on $Y$ restrict to zero on $Y_s$. Represent it on a finite hypercover through degree $q+1$. Vanishing on the fiber is witnessed, after a finite refinement, by a finite cochain and finitely many homotopy identities. Lift that refinement, cochain, and those identities by the same principle. They exhibit the original class as a coboundary on $Y$. Thus restriction is injective.

To package all degrees through $r$ at once, take the union of the finitely many lifted data and totalize their truncated Čech complexes. Filter $\mathcal F$ by extensions by zero from connected locally closed strata; on each stratum a finite étale cover trivializes the coefficient, and its finitely many descent operators enter the same total complex. Kernels and cokernels off the chosen stratum have smaller support and are appended by the localization sequence and noetherian induction. The resulting bounded finite complex is $P_r$. Keeping one additional simplicial degree gives the injection in degree $r+1$ and makes the construction compatible as $r$ grows. No unbounded finite-group resolution is used. $\square$

Apply the lemma to every cohomology sheaf of $K$ and totalize the finitely many resulting complexes. Given a degree $q$, choose $r$ beyond $q$ and beyond the amplitude of the finite truncation spectral sequence. Restriction is then an isomorphism in degree $q$. This holds for every $q$, so the restriction morphism is a quasi-isomorphism and gives the displayed derived isomorphism. $\square$

This argument explains all three hypotheses. Properness turns a neighborhood of the closed fiber into a neighborhood of the whole space. Strict henselianity removes residue-field descent and makes finite étale closed-fiber pieces split when needed. Constructibility makes every coefficient, covering, and descent relation finite enough to enter one presentation complex. No semistable reduction, resolution, or later comparison theorem is used.

### 5.2 The curve calculation

The preceding proof is general, but a nodal curve displays its local matrix concretely. Let $T$ be a strict henselian trait and let $C\to T$ be a proper semistable relative curve. Étale-locally at a node the equation is

$$
xy=\pi.
$$

Cover the curve by the smooth locus and small node neighborhoods. On a smooth neighborhood, the affine-space calculation of Section 7.2 gives the local presentation directly; this does not appeal to Chapter 8. At a node, remove the node. The punctured neighborhood has tame fundamental group generated by one loop, and after choosing a tame generator its cohomology with a finite module $M$ is represented by

$$
M\xrightarrow{\tau-1}M.
$$

For constant $M$, the differential is zero; intrinsically the degree-one term carries the inverse cyclotomic twist suppressed by the chosen generator. The two branches in the special fiber contribute the same incidence map as the punctured node in the total space; it is the edge map of the dual graph. Thus the two finite presentation complexes agree. Mayer--Vietoris glues the pieces. Normalization adds only finite maps and closed-point terms, already covered by the dimension-zero case.

This explains why smoothness is not needed for proper base change. A nodal fiber may have different cohomology from a nearby smooth fiber, but the direct-image stalk at the nodal point still equals the cohomology of the nodal fiber. Proper base change identifies stalks with fibers; it does not make stalks locally constant.

### 5.3 Higher relative dimension

The proper-neighborhood lemma avoids resolution in higher dimension. For completeness, its induction can be organized by a relative projection on each irreducible affine stratum, along the lines of the fibration constructed in Section 3.3. Purely inseparable changes do not alter the étale site. After making that harmless reduction and deleting a smaller closed subset, a separating transcendence basis gives an elementary curve fibration $h$ over a stratum of dimension one less. The affine-curve finiteness and vanishing theorem of Book 18, Section 6.7, applied fiberwise to such a fibration, retains the tame boundary operators and gives

$$
R\Gamma(Y,Rh_*\Lambda)\simeq R\Gamma(X,\Lambda).
$$

The reduction then proceeds by composition, exactly as in Section 3.3, with comparison replacing constructibility as the property propagated. The direct image $Rh_*\Lambda$ is controlled row by row: rows zero and one by the relative curve theorem of Book 18, Section 7.2, whose formation commutes with every base change, so their strict-local realizations identify with the corresponding geometric-fiber groups; the top row enters through stalks only, as recorded there. Pushing forward along the lower-dimensional projection, the induction hypothesis supplies strict-local comparison for each row, and the Leray spectral sequence has finitely many rows, so comparison on its $E_2$-page gives comparison on the abutment. Constructibility of the intermediate sheaves is supplied by Section 3.3; what this chapter contributes is the comparison morphism itself, which the hypercover lifting of Section 5.1 provides degreewise and which the spectral sequence assembles.

The complement deleted to obtain the elementary fibration has smaller support and is reattached by localization. This closes the dimension step without a projective modification or an appeal to proper cohomological descent. Only relative dimensions one, two, and smooth abelian families are used in the applications, but the induction is dimension-independent.

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

The proof never compares two fibers over different fields; it transports both stalks to one strictly henselian scheme and applies the strict-local theorem once there.

**Descent remark for the coefficient complex.** Let $V\to S$ run over the pointed étale neighborhoods of $\bar s$, with affine ones cofinal as in Book 18, Section 4.6, and let $S_0=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S',\bar s'}$, so that $g$ factors through $S_0\to S$ by the universal property of the strict localization: every pointed étale neighborhood $V\to S$ pulls back along $S_0\to S$, and $S_0=\varprojlim_V V$ over this filtered system, whose transition maps are affine because they are base changes of open immersions between affines. Then $X\times_SS_0=\varprojlim_VX\times_SV$ over affine transitions. We claim that $K$ descends to some $X\times_SV_0$. Since $f$ is separated of finite type, stratify $X$ into finitely many locally closed subschemes on whose interiors the cohomology sheaves of $K$ are lisse; each such subscheme is cut out by finitely many equations and inequations of finite presentation, which pull back from some $X\times_SV_\alpha$; each lisse piece is trivialized by a finite étale cover whose finitely many structure equations likewise pull back from some stage; and the bounded complex $K$ together with its differentials is glued from finitely many such pieces, so one common $V_0$ carries all of them. This is the same spreading mechanism by which Book 18, Section 4.6, descends étale morphisms through the limit.

**Proof.** Test on a geometric point $\bar s'\to S'$ with image $\bar s\to S$, and write
$$
S_0=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S',\bar s'},\qquad
f''=f':X'=X\times_SS'\to S',\quad f_0:X_0=X\times_SS_0\to S_0,
$$

so that $f_0$ is the further base change of $f'$ along $S_0\to S'$, and $K''=g'^*K$, $K_0=(S_0\text{-pullback})$ accordingly. The scheme $S_0$ is strictly henselian local and noetherian, since $S'$ is noetherian.

_Stalk of the left side._ By definition $(Rf_*K)_{\bar s}=\varinjlim_VH^q(X\times_SV,K)$, the colimit over pointed étale neighborhoods of $\bar s$. By the descent remark, $K_0$ descends to some level of the system $(X\times_SV)_V$, so the Continuity theorem of Book 18, Section 4.6, gives a canonical isomorphism
$$
(Rf_*K)_{\bar s}\;\cong\;H^q(X_0,K_0).
$$

No comparison of residue fields enters this step: it only reorganizes the colimit that defines the stalk, using that $S_0\to S$ factors cofinally through pointed étale neighborhoods.

_Stalk of the right side._ The morphism $f_0$ is proper, being a base change of $f$, and $K_0\in D^b_c(X_0,\Lambda)$, constructibility being stable under pullback. Applying the Strict-local proper theorem of Section 5.1 to $f_0$ over the strictly henselian local base $S_0$ yields a quasi-isomorphism
$$
R\Gamma(X_0,K_0)\xrightarrow{\sim}R\Gamma((X_0)_{s''},(K_0)_{s''}),
$$

where $s''$ is the closed point. Its residue field is $\kappa(\bar s')$, so the fiber is exactly $X'_{\bar s'}$ with coefficients $K''$ pulled back to it.

_Combination and compatibility._ Chasing the two identifications through the adjunction units that define them shows that the composite isomorphism
$$
(Rf_*K)_{\bar s}\cong H^q(X_0,K_0)\cong H^q(X'_{\bar s'},K''_{s''})
$$

is induced by restriction along $X'_{\bar s'}\to X\times_SV$ for neighborhoods $V$, hence equals the stalk of the canonical base-change map at $\bar s'$. Since geometric stalks detect isomorphisms of sheaves of $\Lambda$-modules (Book 18, Section 2.2), the base-change map is an isomorphism. $\square$

Here $S_0$ was first formed when $S'$ is noetherian. For general $S'$, work on an affine neighborhood of $\bar s'$. The square, the pointed étale neighborhoods, and the descent data for $K$ all descend to a finitely generated $S$-algebra, and continuity of constructible torsion cohomology identifies the stalk with the filtered colimit of the noetherian comparisons. Thus no noetherian hypothesis on the changing base is hidden in “every.”

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

This is now a consequence of the theorem just proved rather than an input to it: apply proper base change to the square with $S=\operatorname{Spec}k$, $S'=\operatorname{Spec}\Omega$, and note that the proof above never compared fibers over two different fields, so no circularity arises from consuming the theorem here. This field-extension instance is what permits one to enlarge a geometric point without changing an answer.

### 6.3 Products, projection, and composition

If $X\xrightarrow fY\xrightarrow hS$ are proper, base change for $h\circ f$ equals the composite of base change for $f$ and $h$ under

$$
R(h\circ f)_*K\simeq Rh_*Rf_*K.
$$

It therefore respects the Leray spectral sequence

$$
R^a h_*R^b f_*K\Longrightarrow R^{a+b}(h\circ f)_*K.
$$

For proper $p:X\to S$ and a perfect constructible complex $L$ on $S$, the projection formula

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

Assume $S$ is excellent noetherian, $f$ is compactifiable in the sense of Section 4.2, and $g$ is smooth. Let $K\in D^b_c(X,\Lambda)$, where $\Lambda$ is finite, killed by $N$, and $N$ is invertible on $S$. Then

$$
g^*Rf_*K\xrightarrow{\sim}Rf'_*g'^*K.
$$

Because the assertion is local for the étale topology on $S'$, a smooth morphism can be reduced étale-locally to a projection

$$
\mathbf A^r_S\longrightarrow S.
$$

Factor that projection into affine-line projections. It is enough to handle one new parameter. Compactify $f$ and use proper base change on the compactification. The possible discrepancy is the failure of $Rj_*K$ to commute with the new parameter and is supported at the boundary. Filter that boundary by normal strata. At a generic codimension-one point the strict-local term is the two-term tame-inertia complex; adjoining a polynomial parameter leaves both its inertia group and its finite presentation matrix unchanged. Branch, nonnormal, and higher-codimension loci have smaller support. Noetherian induction and the localization triangle prove the theorem. This is the boundary induction of Section 4.2 with the smooth parameter carried through every matrix.

This proof exhibits every assumption. Compactifiability supplies the factorization through a proper morphism, and the stability lemma supplies compactifications of the boundary strata that the induction produces; quasi-projective $f$, the only case used later, satisfies both. Excellence makes normalization and constructibility finite. Smoothness gives an étale-local affine-space model. Invertibility of $N$ makes the punctured-trait calculation tame. If $g$ is arbitrary and $f$ nonproper, the theorem is false.

### 7.2 The standard smooth-local calculation

Let $A$ be strictly henselian and let

$$
p:\mathbf A^r_A\to\operatorname{Spec}A
$$

be projection. For a constant finite module $M$ of order invertible in $A$,

$$
Rp_*M\simeq M.
$$

For $r=1$, compactify to $\mathbf P^1_A$. Proper base change computes its cohomology from the closed geometric fiber. On that fiber, the affine-curve theorem of Book 18, Section 6.7, computes $\mathbf A^1$ directly: the prime-to-residue-characteristic cohomology of a constant finite module is $M$ in degree zero and zero above (the Kummer computation with $g=0$ and $r=1$; no fundamental-group presentation is involved). The boundary presentation at infinity is unchanged over $A$, so the localization triangles on $\mathbf P^1_A$ and its closed fiber identify and give the same answer over $A$. Products and induction give $r>1$.

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

**Proof.** Work étale-locally on source and base. Trivialize $\mathcal L$ by a finite étale cover. A smooth morphism is étale-locally a projection from affine space, so reduce to $\mathbf A^r_S\to S$ with constant coefficients.

If $\bar x$ lies over $\bar s$ and $\bar t$ is a geometric generization in $S_{(\bar s)}$, the smooth-tube calculation is

$$
R\Gamma\left(
(\mathbf A^r_S)_{(\bar x)}\times_{S_{(\bar s)}}\bar t,
\Lambda
\right)\simeq\Lambda.
$$

To prove it, choose coordinates centered at the image of $\bar x$ after an étale extension. Successively compactify each coordinate line. Proper base change identifies the projective-line term, while the unique boundary section has the same tame-inertia presentation before and after generization. The two localization triangles cancel that boundary term and leave the constant degree-zero class. Induction on $r$ gives the formula. The map from the stalk is the unit class and hence is the displayed isomorphism.

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
\operatorname{sp}_{\bar u/\bar s}=
\operatorname{sp}_{\bar u/\bar t}\circ
\operatorname{sp}_{\bar t/\bar s}.
$$

They commute with cup products and pullback because they arise at the derived-sheaf level. They also commute with finite étale trace maps, which Book 18 constructed by summing sheets. Pushforward for a general proper correspondence requires the trace and purity formalism of Book 20 and is not used here. Without local acyclicity the specialization maps need not be invertible, but they still exist.

### 9.2 The smooth proper theorem

**Smooth proper base-change theorem.** Let $f:X\to S$ be smooth and proper, and let $\mathcal L$ be lisse finite, killed by an integer invertible on $S$. Then:

1. every $R^qf_*\mathcal L$ is lisse with finite stalks;
2. it vanishes outside the uniform geometric range;
3. its formation commutes with arbitrary base change;
4. every specialization map is an isomorphism.

**Proof.** Proper base change identifies stalks with geometric-fiber cohomology and proves arbitrary base change. Absolute finiteness makes stalks finite. Smooth local acyclicity makes every generization map an isomorphism. Refine a constructibility stratification; adjacent strata then carry local systems with invertible transport and glue to a lisse sheaf. Fiber dimension supplies vanishing. $\square$

For clarity, the gluing step uses this lissity criterion: a constructible finite sheaf on a locally noetherian scheme is lisse if, on every strict localization, all maps from the closed geometric stalk to geometric generizations are isomorphisms. Trivialize on the finitely many strata meeting one strict localization. The assumed maps identify their finite stalks and descent operators; after one common pointed étale neighborhood these finitely many identifications glue the stratumwise trivializations. Thus the sheaf is lisse near every geometric point.

On connected $S$, the ranks of fiber cohomology are constant. There is canonical transport along an étale path, not a canonical simultaneous trivialization. Monodromy records the obstruction to such a trivialization.

### 9.3 Monodromy and arithmetic actions

At a geometric basepoint $\bar s$ of connected $S$, lissity gives

$$
\pi_1(S,\bar s)\longrightarrow
\operatorname{Aut}_\Lambda
H^q(X_{\bar s},\mathcal L_{\bar s}).
$$

Transport along a path is the specialization isomorphism; a loop gives monodromy. For $S=\operatorname{Spec}k$, this is the absolute Galois action.

If a smooth proper family extends over a henselian discrete valuation ring and $\ell$ is invertible there, the generic-fiber representation is unramified. Indeed, the lisse direct image extends across the closed point, so inertia acts trivially. With the left descent action fixed in Book 18, arithmetic Frobenius on the special fiber matches arithmetic unramified Frobenius on the generic fiber. Geometric Frobenius is the inverse on both sides.

The converse is not asserted. An unramified cohomology representation need not construct a smooth proper model; cohomology can miss geometric singularities.

## 10. Passage to adic coefficients

### 10.1 Finite-level control of the tower

Fix $\ell\in\mathcal O_S^\times$ and set $\Lambda_n=\mathbf Z/\ell^n\mathbf Z$. Let $\mathcal F=(\mathcal F_n)$ be normalized constructible with

$$
\mathcal F_{n+1}\otimes^L_{\Lambda_{n+1}}\Lambda_n
\simeq\mathcal F_n.
$$

Book 18 defined continuous direct image by applying $Rf_*$ levelwise and then normalizing the resulting tower. Three facts permit an ordinary $R\varprojlim$ realization and its stalkwise interpretation:

1. finite-level comparison is an isomorphism for every $n$;
2. cohomological amplitude is bounded independently of $n$;
3. each fixed-degree tower is Mittag--Leffler.

Proper or smooth base change supplies the first. Proper geometric dimension supplies the second; in the nonproper smooth-horizontal case one uses the uniform bound from the chosen compactification and boundary stratification. Finiteness supplies the third. Images in each finite target stabilize, although cohomology transition maps need not be surjective.

The three facts let one commute geometric stalks, finite totalizations, and $R\varprojlim$. Normalization is part of the definition of continuous direct image; it must not be inferred merely from degreewise Mittag--Leffler.

### 10.2 Integral and rational base change

**Adic proper base change.** Let $f:X\to S$ be proper in the noetherian prime-to-$\ell$ setting, and let $\mathcal F$ be a bounded normalized constructible system on a common finite stratification. Then

$$
g^*Rf_{*,\mathrm{cont}}\mathcal F
\xrightarrow{\sim}
Rf'_{*,\mathrm{cont}}g'^*\mathcal F
$$

for every $g:S'\to S$.

Both pullbacks in this display are normalized adic pullbacks; they are not pullbacks of an ordinary inverse-limit sheaf.

**Proof.** Finite proper base change gives an isomorphism at every level, compatibly with transition maps. It is therefore an isomorphism of systems; applying normalization gives the displayed isomorphism in the adic category. To realize it by ordinary $R\varprojlim$, proper dimension gives a bound independent of $n$, and finite geometric stalk cohomology makes every fixed-degree tower Mittag--Leffler. Book 18 then identifies normalization with the $R\varprojlim$ realization and permits stalkwise interpretation. $\square$

The same proof gives adic smooth base change when $g$ is smooth, under the bounded common-stratification hypotheses of Section 10.1. Rationalize only afterward:

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

Each $R^qf_{*,\mathrm{cont}}\mathcal F$ is then a lisse adic system with finitely generated $\mathbf Z_\ell$-stalk. The stalk is finite free if its fiber cohomology has no $\ell$-torsion. Freeness must be checked; lissity alone does not imply it.

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

For proper $f:X\to Y$ and a perfect constructible complex $L$ on $Y$,

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

For a finite étale correspondence over $S$,

$$
X\xleftarrow{p}Z\xrightarrow{q}X,
$$

with $q$ finite étale and the necessary coefficient identification, pullback followed by the finite étale trace acts on $Rf_*K$. Base change for $q$, compatibility of the sheet-summing trace, and functoriality of $p^*$ show that this action commutes with every base change on $S$.

Specialization therefore commutes with pullback by algebraic endomorphisms and isogenies, and with finite étale prime-to-level correspondences. The assertion passes modulo every $\ell^n$ to the adic limit.

A nonfinite proper $q$ needs a trace map, and a nonproper $q$ needs compact support. Those constructions belong to Book 20. A correspondence on an open PEL space may also fail to extend across a chosen compactification. The comparison theorem proves compatibility for the finite étale traces available here; it does not construct a boundary extension.

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

Here is a proof of the fiber calculation that does not use the later duality theorem. Over a separably closed field choose a point $x$ and put $U=C\setminus\{x\}$. The Kummer computation of Book 18, Sections 6.7 and 6.8, makes $H^1(U,\Lambda_n)$ free of rank $2g$ and kills the higher degrees; the rank statement rests on the ampleness of the theta divisor, proved in Book 17a, Section 8.4, and imported by Book 18, Section 6.8, while the vanishing needs no Jacobian input. Thus

$$
H^0(U,\Lambda_n)=\Lambda_n,\qquad
H^1(U,\Lambda_n)=\Lambda_n^{2g},\qquad
H^q(U,\Lambda_n)=0\quad(q>1).
$$

The local term at $x$ follows directly from Kummer theory on the strict henselian discrete valuation ring. A unit has zero valuation, a uniformizer has valuation one, and adjoining an $\ell^n$th root of a unit is étale. The valuation boundary therefore identifies cohomology with support as

$$
R\Gamma_x(C,\Lambda_n)\simeq\Lambda_n(-1)[-2].
$$

In the localization sequence, the residue from $H^1(U,\Lambda_n)$ is zero: the loop around the sole puncture is the product of the $g$ commutators in the curve presentation and hence vanishes after abelianization. Consequently restriction identifies $H^1(C,\Lambda_n)$ with $H^1(U,\Lambda_n)$, and the support generator identifies

$$
H^2(C,\Lambda_n)\simeq\Lambda_n(-1).
$$

Changing $x$ changes the local generator by the degree of the resulting zero-cycle, so the degree-one fundamental class and the displayed twisted identification are canonical. This proves the asserted ranks and twist before any perfect-pairing statement.

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

is alternating and is transported by every specialization. Alternation, including for $\ell=2$, follows from the one-relator curve presentation: the attaching relation is a product of commutators, so the diagonal coefficients of the degree-two cup matrix vanish. Perfectness of this pairing belongs to the duality package of Book 20; here we need only its construction and comparison compatibility.

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

If the special fiber were a tree of smooth components, the dual graph would have no first cohomology; if it contained loops, each graph loop would contribute a degree-one class. This separates component cohomology from combinatorial cohomology and foreshadows the nearby-cycle analysis of Book 22.

## 13. Abelian schemes

### 13.1 Exterior powers and arbitrary base change

Let $f:A\to S$ be an abelian scheme of relative dimension $g$, and assume $\ell$ invertible on $S$. Multiplication by $\ell^n$ is finite étale, so

$$
A[\ell^n]\to S
$$

is a lisse sheaf of free $\Lambda_n$-modules of rank $2g$. Both assertions are Book 18, Section 15.2, whose stated hypothesis is that the abelian scheme is polarizable, that is, Zariski-locally carries a relatively ample bundle — automatic in the polarized families considered here: étaleness because the differential of $[\ell^n]$ on the relative tangent bundle is the unit $\ell^n$, and the rank $\ell^{2gn}$ because the theorem of the square gives $[m]^*L\equiv L^{\otimes m^2}$ for a symmetric relatively ample $L$, whence $\deg[m]=m^{2g}$ by comparing leading Hilbert coefficients. That derivation uses no cohomology.

What this chapter adds is relative. It rests on one absolute input that is not proved in this book.

**Imported input (absolute fiber cohomology).** Let $A$ be an abelian variety of dimension $g$ over a separably closed field of characteristic different from $\ell$, and put $\Lambda_n=\mathbf Z/\ell^n\mathbf Z$. Then evaluation of degree-one classes on torsion points is an isomorphism

$$
H^1(A,\Lambda_n)
\xrightarrow{\ \sim\ }
\operatorname{Hom}_{\Lambda_n}(A[\ell^n],\Lambda_n),
$$

cup product induces isomorphisms

$$
\bigwedge\nolimits^i H^1(A,\Lambda_n)
\xrightarrow{\ \sim\ }
H^i(A,\Lambda_n)
\qquad(i\geq0),
$$

and both are functorial in $A$.

We state this rather than prove it, and the reason is chronological. The proof identifies the multiplication tower $[\ell^r]:A\to A$ as cofinal among connected pointed finite étale covers of $\ell$-power degree, shows that the tower is acyclic in positive degrees, and then reads the answer off the continuous cohomology of $T_\ell A\cong\mathbf Z_\ell^{2g}$ acting trivially on $\Lambda_n$. That last step is the cohomology of a profinite group with its Koszul complex, a theory developed only in Book 24, and the descent along an infinite tower is not the finite Galois descent available here. The calculation is therefore carried out in Book 36, where it is needed for the Jacobian of a curve and where Book 24 may be cited. Book 18 supplies, in the right order, the two absolute facts this book uses in its own proofs: finiteness of $H^q(A,\mathcal F)$ for constructible finite $\mathcal F$, and vanishing above degree $2g$. Nothing in Chapters 1 through 12 depends on the imported input; it enters only here and, through this chapter, in Chapter 14.

Granting it, the relative statements are exactly what proper base change contributes, and that contribution is the substance of the present chapter. Fiberwise, a degree-one cohomology class with constant coefficients is a character of the $\ell^n$-torsion. The character construction is functorial in the abelian scheme, so the fiberwise maps glue to a morphism of sheaves on $S$,

$$
R^1f_*\Lambda_n
\longrightarrow
\underline{\operatorname{Hom}}_{\Lambda_n}
(A[\ell^n],\Lambda_n).
$$

Proper base change identifies its two sides on every geometric stalk: the left stalk is $H^1(A_{\bar s},\Lambda_n)$ and the right stalk is $\operatorname{Hom}_{\Lambda_n}(A_{\bar s}[\ell^n],\Lambda_n)$. A morphism between constructible sheaves that is an isomorphism at every geometric stalk is an isomorphism. Hence

$$
R^1f_*\Lambda_n
\cong
\underline{\operatorname{Hom}}_{\Lambda_n}
(A[\ell^n],\Lambda_n),
$$

a lisse sheaf of free $\Lambda_n$-modules of rank $2g$. Passing to the inverse limit is legitimate by Section 10.1, the tower being lisse of constant finite rank and hence Mittag--Leffler in every degree, and gives

$$
R^1f_*\mathbf Z_\ell
\cong
\underline{\operatorname{Hom}}_{\mathbf Z_\ell}
(T_\ell A,\mathbf Z_\ell).
$$

Thus the cohomological and torsion constructions of the lisse rank-$2g$ sheaf agree. This identification commutes with arbitrary base change because both constructions do.

The same mechanism handles the higher degrees. The cup-product maps

$$
\bigwedge\nolimits^i R^1f_*\Lambda_n
\longrightarrow R^if_*\Lambda_n
$$

are maps of lisse sheaves. By the imported input and proper base change they are isomorphisms on every geometric stalk, hence globally. Therefore

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

### 13.2 Isogenies, polarizations, and endomorphisms

An isogeny $u:A\to B$ over $S$ induces

$$
u^*:R^1f_{B*}\mathbf Z_\ell
\longrightarrow R^1f_{A*}\mathbf Z_\ell
$$

dual to $T_\ell u$. If $\deg u$ is prime to $\ell$, its kernel has no $\ell$-primary part, so this is an integral isomorphism. If $\ell$ divides the degree, kernel or cokernel may survive over $\mathbf Z_\ell$, although the map becomes an isomorphism over $\mathbf Q_\ell$ for every isogeny.

Every endomorphism of $A$ acts on $R^1$ and hence on all exterior powers. Proper base change and Section 11.3 show that these actions commute with specialization. An idempotent in an endomorphism algebra cuts out a direct summand whenever its denominator is invertible in the coefficient ring. If the denominator is divisible by $\ell$, a rational summand need not have an integral direct complement.

A polarization $\lambda:A\to A^\vee$ supplies an alternating Weil form on $T_\ell A$ with values in $\mathbf Z_\ell(1)$. If $\deg\lambda$ is prime to $\ell$, its inverse dualizes to a perfect alternating form

$$
R^1f_*\mathbf Z_\ell\otimes R^1f_*\mathbf Z_\ell
\longrightarrow\mathbf Z_\ell(-1).
$$

For an arbitrary polarization the same construction is a rational perfect form and an integral form only after multiplying by a sufficient power of $\ell$; it need not be unimodular on the integral lattice. Because the polarization is defined over $S$, the form is invariant under monodromy, and all specialization isomorphisms preserve it. This compatibility, rather than only constancy of ranks, is what makes the result useful in arithmetic families.

Over a henselian trait of residue characteristic different from $\ell$, an abelian scheme has unramified $T_\ell A$ and unramified cohomology in all degrees. The statement uses the existence of the abelian scheme over the trait. A generic abelian variety with semistable but non-good reduction is not covered; its nontrivial inertia belongs to the monodromy theory developed later.

## 14. PEL abelian families and parameter spaces

### 14.1 The geometric hypotheses

A PEL parameter space records abelian schemes equipped with polarizations, endomorphisms, and level structures. Those words alone do not imply smoothness, representability, or properness. We isolate the precise geometric input.

Let $M\to B$ be a modular or quaternionic parameter curve, or a Hilbert--Blumenthal parameter space used in the arithmetic route. Assume:

1. $B$ is excellent noetherian and $\ell$ is invertible on $B$;
2. $M$ is a smooth quasi-projective scheme over $B$;
3. the level is sufficiently small that a universal abelian scheme

   $$
   a:\mathcal A\to M
   $$

   exists, and $a$ is smooth proper;
4. the polarization and action by a finite projective order are defined over $M$;
5. when cohomology of $M$ itself is considered, either $M$ is proper over $B$, or a proper compactification $\bar M$ with relative normal-crossings boundary $D$ is part of the data;
6. every prime inverted to make the level, endomorphism order, and boundary tame is also inverted on $B$.

Hypothesis 2 is what puts these families inside the theorems of Chapters 3 and 7: a quasi-projective $M\to B$ is compactifiable by the theorem of Section 4.2, as is every locally closed stratum of it, and the same holds for the smooth projective universal abelian scheme $\mathcal A\to M$ and for the products used below. No appeal to the general compactification theorem is needed anywhere in this chapter. Hypothesis 5 is a stronger and independent requirement: it asks not merely for some proper $\bar M$ but for one whose boundary is a relative normal-crossings divisor, and that is a property of a chosen compactification, not a consequence of compactifiability.

Compact quaternionic parameter curves satisfy the proper alternative. Hilbert--Blumenthal parameter spaces are often nonproper and require the compactified-pair alternative. These are hypotheses, not consequences of the label “PEL.” Construction of the spaces and compactifications belongs to later geometric volumes.

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

on $B$, arbitrary base change, and invertible specialization. For parameter curves the cohomology lies in $[0,2]$; a Hilbert--Blumenthal space of relative dimension $d$ lies in the general range $[0,2d]$. Passing through the coefficient tower gives the integral and rational statements. Pullbacks by endomorphisms and finite étale correspondences with their sheet-summing traces act compatibly. General proper-correspondence traces are not asserted in this book.

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
H^q_!(M_{\bar b},\mathcal L_n)=
\operatorname{im}\bigl(
H^q_c(M_{\bar b},\mathcal L_n)
\to H^q(M_{\bar b},\mathcal L_n)
\bigr)
$$

is preserved by specialization whenever both maps in the defining arrow are identified compatibly. It is an image, not automatically a direct summand. A projector from correspondences may split it only after its denominators are controlled.

### 14.4 Good reduction and specialization

Let $B$ be a henselian trait with residue characteristic prime to $\ell$. Assume the selected PEL family, its universal abelian scheme, its endomorphisms, polarization, level away from the residue characteristic, and—when needed—its compactified boundary pair all extend smoothly over $B$.

For a geometric specialization of points $\bar x_s\rightsquigarrow\bar x_\eta$ in $M$, the universal abelian family gives

$$
H^q(\mathcal A_{\bar x_s},\mathbf Z_\ell)
\xrightarrow{\sim}
H^q(\mathcal A_{\bar x_\eta},\mathbf Z_\ell)
$$

and respects the exterior algebra, polarization, endomorphism algebra, and prime-to-$\ell$ correspondences. This is a statement about fibers of $\mathcal A\to M$, not yet about the cohomology of the nonproper total space $\mathcal A\to B$. For a proper PEL parameter space, the same holds for $H^q(M_{\bar s},\mathcal L)$ and $H^q(M_{\bar\eta},\mathcal L)$, and Leray then gives the corresponding total-space statement. For a nonproper space it holds for compact support under properness of $\bar M$, and for ordinary cohomology only with the boundary control of Section 14.3.

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

**Finite constructibility package.** For a compactifiable — in particular, for a quasi-projective — morphism over an excellent noetherian base and finite constructible coefficients of invertible order, higher direct images are constructible and uniformly bounded in the required dimensions. Geometric-fiber groups are finite.

**Proper package.** If the morphism whose direct image is taken is proper, its bounded constructible direct image commutes with every change of base. Stalks are geometric-fiber cohomology. No smoothness is required, and specialization maps exist even in singular degenerations.

**Smooth-horizontal package.** If the change-of-base map is smooth, direct image for a compactifiable morphism commutes with that change. The original morphism need not be proper, but it must admit a compactification.

**Smooth-vertical package.** A smooth morphism is universally locally acyclic relative to lisse finite coefficients of invertible order. If it is also proper, higher direct images are lisse and all specialization maps are isomorphisms.

**Adic package.** The finite-level statements pass to a normalized $\mathbf Z_\ell$-system when amplitude is uniform and finite cohomology gives Mittag--Leffler. Rationalization takes place after derived inverse limit.

**Functorial package.** Cup products, external products, projection formulas, Leray filtrations, pullbacks by endomorphisms, and finite étale traces commute with base change and specialization. Tor terms must be retained unless coefficient cohomology is free.

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

For relative curves this yields constant genus cohomology and unramified good-reduction representations. For abelian schemes it globalizes the Tate module and the entire exterior cohomology algebra — granting, as Section 13.1 says openly, the absolute cohomology of a single geometric fiber, which is computed only in Book 36 because its proof needs the profinite-group cohomology of Book 24. For selected PEL families it transports endomorphisms, polarizations, coefficient systems, and finite étale prime-to-level correspondences across good fibers while keeping the open-boundary caveat visible.

The final lesson is a discipline of hypotheses. Coefficient invertibility controls tame local geometry. Excellence and noetherianity make dévissage finite. Properness controls global fibers. Smoothness controls local tubes. Geometric points detect the comparison. Uniform finite-level bounds justify the adic limit. Once each condition is placed where it is actually used, proper and smooth base change become not isolated miracles but a coherent transport mechanism for arithmetic geometry.
