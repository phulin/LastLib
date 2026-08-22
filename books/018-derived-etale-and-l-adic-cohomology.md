# Derived Étale and $\ell$-adic Cohomology

## Contents

- [1. From local sheets to global invariants](#1-from-local-sheets-to-global-invariants)
  - [1.1 The problem](#11-the-problem)
  - [1.2 Standing conventions](#12-standing-conventions)
  - [1.3 Three coefficient levels](#13-three-coefficient-levels)
  - [1.4 The main results](#14-the-main-results)
- [2. The small étale topos](#2-the-small-étale-topos)
  - [2.1 The site and its coverings](#21-the-site-and-its-coverings)
  - [2.2 Sheaves and stalks](#22-sheaves-and-stalks)
  - [2.3 Morphisms and geometric fibers](#23-morphisms-and-geometric-fibers)
  - [2.4 Why the finite-cover site is not enough](#24-why-the-finite-cover-site-is-not-enough)
- [3. Constructible and lisse torsion sheaves](#3-constructible-and-lisse-torsion-sheaves)
  - [3.1 Lisse sheaves](#31-lisse-sheaves)
  - [3.2 Constructible sheaves](#32-constructible-sheaves)
  - [3.3 Extension by zero and stratification](#33-extension-by-zero-and-stratification)
  - [3.4 Tate twists and Kummer theory](#34-tate-twists-and-kummer-theory)
- [4. Derived global sections](#4-derived-global-sections)
  - [4.1 The derived definition](#41-the-derived-definition)
  - [4.2 Injective and K-injective models](#42-injective-and-k-injective-models)
  - [4.3 Čech complexes and hypercovers](#43-čech-complexes-and-hypercovers)
  - [4.4 Localization and hypercohomology](#44-localization-and-hypercohomology)
  - [4.5 Cohomological descent for hypercovers](#45-cohomological-descent-for-hypercovers)
  - [4.6 Continuity and finite-coefficient base change](#46-continuity-and-finite-coefficient-base-change)
- [5. Functoriality and spectral sequences](#5-functoriality-and-spectral-sequences)
  - [5.1 Derived direct image and Leray](#51-derived-direct-image-and-leray)
  - [5.2 Arithmetic descent and Hochschild--Serre](#52-arithmetic-descent-and-hochschild--serre)
  - [5.3 Coefficient change](#53-coefficient-change)
  - [5.4 Boundedness and convergence](#54-boundedness-and-convergence)
- [6. Torsion cohomological dimension and the cohomology of curves](#6-torsion-cohomological-dimension-and-the-cohomology-of-curves)
  - [6.1 What cohomological dimension measures](#61-what-cohomological-dimension-measures)
  - [6.2 Fields and strict local schemes](#62-fields-and-strict-local-schemes)
  - [6.3 Curves](#63-curves)
  - [6.4 Low-dimensional finite-type schemes](#64-low-dimensional-finite-type-schemes)
  - [6.5 Tsen's theorem](#65-tsens-theorem)
  - [6.6 The Brauer group of a curve and cohomological dimension one](#66-the-brauer-group-of-a-curve-and-cohomological-dimension-one)
  - [6.7 Cohomology of curves with torsion coefficients](#67-cohomology-of-curves-with-torsion-coefficients)
  - [6.8 Rigidity, the see-saw lemma, and the order of $\operatorname{Pic}^0[n]$](#68-rigidity-the-see-saw-lemma-and-the-order-of-operatornamepic0n)
- [7. Finiteness for constructible torsion coefficients](#7-finiteness-for-constructible-torsion-coefficients)
  - [7.1 The finiteness theorem in the required range](#71-the-finiteness-theorem-in-the-required-range)
  - [7.2 The proof architecture](#72-the-proof-architecture)
  - [7.3 Uniformity in the exponent](#73-uniformity-in-the-exponent)
  - [7.4 What fails without the hypotheses](#74-what-fails-without-the-hypotheses)
- [8. Towers of coefficients](#8-towers-of-coefficients)
  - [8.1 Adic systems](#81-adic-systems)
  - [8.2 Naive limits are not the definition](#82-naive-limits-are-not-the-definition)
  - [8.3 Derived inverse limits](#83-derived-inverse-limits)
  - [8.4 The Mittag--Leffler mechanism](#84-the-mittag--leffler-mechanism)
- [9. The adic derived category](#9-the-adic-derived-category)
  - [9.1 Normalized systems](#91-normalized-systems)
  - [9.2 Essentially zero systems](#92-essentially-zero-systems)
  - [9.3 The Ekedahl-style viewpoint](#93-the-ekedahl-style-viewpoint)
  - [9.4 When elementary towers suffice](#94-when-elementary-towers-suffice)
- [10. Continuous $\ell$-adic cohomology](#10-continuous-ell-adic-cohomology)
  - [10.1 Definition](#101-definition)
  - [10.2 The Milnor exact sequence](#102-the-milnor-exact-sequence)
  - [10.3 Reduction and completion](#103-reduction-and-completion)
  - [10.4 Rational coefficients and lattices](#104-rational-coefficients-and-lattices)
- [11. Continuous Galois actions](#11-continuous-galois-actions)
  - [11.1 Geometric cohomology over a field](#111-geometric-cohomology-over-a-field)
  - [11.2 Continuity at finite and integral level](#112-continuity-at-finite-and-integral-level)
  - [11.3 Hochschild--Serre with adic coefficients](#113-hochschild--serre-with-adic-coefficients)
  - [11.4 Frobenius conventions](#114-frobenius-conventions)
- [12. Base-change interfaces](#12-base-change-interfaces)
  - [12.1 The canonical map](#121-the-canonical-map)
  - [12.2 Stalks of a derived direct image](#122-stalks-of-a-derived-direct-image)
  - [12.3 Passage through an adic tower](#123-passage-through-an-adic-tower)
  - [12.4 A safe base-change protocol](#124-a-safe-base-change-protocol)
- [13. Cup products and coefficient pairings](#13-cup-products-and-coefficient-pairings)
  - [13.1 Finite-level products](#131-finite-level-products)
  - [13.2 Products after derived completion](#132-products-after-derived-completion)
  - [13.3 Twists, signs, and Galois equivariance](#133-twists-signs-and-galois-equivariance)
  - [13.4 Projection formulas and correspondences](#134-projection-formulas-and-correspondences)
- [14. Curves](#14-curves)
  - [14.1 Cohomological amplitude and finiteness](#141-cohomological-amplitude-and-finiteness)
  - [14.2 The first cohomology group](#142-the-first-cohomology-group)
  - [14.3 Open and semistable curves](#143-open-and-semistable-curves)
  - [14.4 Perfectness](#144-perfectness)
- [15. Abelian schemes](#15-abelian-schemes)
  - [15.1 Absolute finiteness and amplitude](#151-absolute-finiteness-and-amplitude)
  - [15.2 Torsion and lisse Tate systems](#152-torsion-and-lisse-tate-systems)
  - [15.3 Families and base change](#153-families-and-base-change)
  - [15.4 Integral perfectness](#154-integral-perfectness)
- [16. A reusable derived package](#16-a-reusable-derived-package)
  - [16.1 The integral theorem](#161-the-integral-theorem)
  - [16.2 The rational theorem](#162-the-rational-theorem)
  - [16.3 A diagnostic checklist](#163-a-diagnostic-checklist)
  - [16.4 Final synthesis](#164-final-synthesis)

## 1. From local sheets to global invariants

### 1.1 The problem

Finite étale covers turn geometry into finite monodromy sets. A lisse torsion sheaf similarly turns into a finite module with a continuous action of the étale fundamental group. Neither description yet measures the obstruction to gluing local sections. That obstruction is cohomology. The decisive change of viewpoint in this book is to retain the whole complex of global sections rather than only one cohomology group.

For a scheme $X$ and a sheaf $\mathcal F$ on its small étale site, the central object is

$$
R\Gamma(X_{\mathrm{\acute et}},\mathcal F).
$$

Its cohomology groups are $H^i_{\mathrm{\acute et}}(X,\mathcal F)$. Distinguished triangles remember connecting maps, cup products live naturally before cohomology is taken, and direct image fits into the Leray spectral sequence. These advantages become indispensable when the coefficient ring changes from $\mathbf Z/\ell^n\mathbf Z$ to $\mathbf Z_\ell$: inverse limit is only left exact, so the correct completed object is a derived inverse limit.

The basic formula is therefore

$$
R\Gamma_{\mathrm{cont}}(X,(\mathcal F_n))
=R\varprojlim_n R\Gamma(X,\mathcal F_n),
$$

not simply $\varprojlim_n H^i(X,\mathcal F_n)$. The difference is measured by a first derived limit. Much of the subject consists of finding geometric finiteness conditions under which that difference vanishes, while keeping the derived definition available when it does not.

### 1.2 Standing conventions

All schemes are locally noetherian unless a statement says otherwise. Cohomology is taken on the small étale site. A geometric point has separably closed residue field. For a field $k$, we choose a separable closure $k^s$ and write $G_k=\operatorname{Gal}(k^s/k)$. If $X/k$ is a scheme, $\bar X=X\times_k k^s$.

Fix a prime $\ell$. Whenever torsion or adic coefficients occur on a scheme $X$, $\ell$ is invertible on $X$. Set

$$
\Lambda_n=\mathbf Z/\ell^n\mathbf Z,
\qquad \Lambda=\mathbf Z_\ell,
\qquad E=\mathbf Q_\ell.
$$

Complexes are cohomological. We write $D^+(X_{\mathrm{\acute et}},\Lambda_n)$ for the bounded-below derived category of étale sheaves of $\Lambda_n$-modules and $D^b_c$ for bounded complexes with constructible cohomology sheaves. The symbol $\otimes^L$ always denotes derived tensor product. All inverse limits of complexes that affect cohomology are derived unless the word “ordinary” is explicitly present.

We separate three assertions that are often conflated. A sheaf on $X$ has monodromy under $\pi_1(X)$ only when it is lisse. The groups $H^i(\bar X,-)$ have a $G_k$-action when $X$ and its coefficients descend to $k$. A lisse sheaf on $X/k$ does not in general give a $G_k$-representation on its stalk without a section or trivial geometric monodromy, whereas its geometric cohomology does carry a canonical arithmetic action.

### 1.3 Three coefficient levels

At the finite level, $\Lambda_n$-sheaves form an ordinary Grothendieck abelian category. Injective resolutions, stalks, direct images, and tensor products behave in the familiar sheaf-theoretic way.

At the integral adic level, a coefficient object is a compatible tower $(\mathcal F_n)$, not merely the ordinary inverse-limit sheaf. The compatibility condition must identify reduction of level $n+1$ with level $n$. Derived reduction is required for complexes. Continuous cohomology retains the topology arising from the tower.

At the rational level, one inverts $\ell$ only after constructing an integral object. A lisse $E$-sheaf is equivalently a continuous finite-dimensional $E$-representation of the relevant fundamental group; it possesses a stable $\Lambda$-lattice, but no particular lattice is canonical. Thus a rational adic sheaf is not defined by placing an abstract constant field $E$ on the ordinary étale site and forgetting topology. The lattice-up-to-isogeny description is the invariant one.

### 1.4 The main results

The book establishes four packages. First, finite torsion coefficients admit a complete derived theory on the small étale topos, with Leray, hypercohomology, localization, Hochschild--Serre, and cup products. Second, constructible prime-to-residue-characteristic coefficients on a separated finite-type $d$-fold over a separably closed field have finite cohomology and vanish above degree $2d$. We prove the affine theorem and the dimension-controlled gluing argument from which this follows; in particular the bounds are $2$ for proper curves, $2g$ for $g$-dimensional abelian varieties, and $4$ for surfaces. Third, compatible finite-level complexes define continuous integral and rational cohomology, with the exact $\varprojlim^1$ obstruction displayed. Fourth, in the cases needed for curves and abelian schemes, the resulting geometric complexes are bounded and perfect over $\Lambda$, and their cohomology carries continuous Galois and functorial finite-correspondence actions.

The geometric comparison theorem asserting proper or smooth base change in complete generality belongs to the next stage of the theory. Here we construct its canonical maps, prove the cases forced by finite étale morphisms and constant products, and formulate exact hypotheses under which finite-level comparison passes to adic coefficients. This boundary prevents a formal derived argument from being mistaken for the geometric theorem it is designed to transport.

## 2. The small étale topos

### 2.1 The site and its coverings

Zariski neighborhoods cannot usually choose a root of a separable polynomial. Étale neighborhoods can, and do so without introducing ramification. This makes them fine enough to trivialize locally constant arithmetic data while retaining algebraic control.

The small étale category $\operatorname{Et}(X)$ has étale morphisms $U\to X$ as objects and $X$-morphisms as arrows. A family $(U_i\to U)$ is a covering if the images are jointly surjective. Pullback preserves étale maps and joint surjectivity, identity families cover, and composites of covering families cover; hence this is a Grothendieck topology. The object $X\to X$ is final.

Representable presheaves are sheaves. Indeed, morphisms into a scheme glue uniquely across an étale covering because an étale covering is jointly surjective and flat, and morphisms of schemes satisfy faithfully flat descent. This subcanonicity lets us use geometric objects and their associated sheaves without changing notation.

The **small étale topos** $X_{\mathrm{\acute et}}$ is the category of sheaves of sets on this site. Abelian sheaves and sheaves of modules form Grothendieck abelian categories: they have all colimits, filtered colimits are exact, and extensions by zero from a set of site objects give generators. Consequently they have enough injectives. This fact, not a special flasque-resolution miracle, is what makes right-derived global sections available.

### 2.2 Sheaves and stalks

For a geometric point $\bar x\to X$, the stalk is

$$
\mathcal F_{\bar x}
=\varinjlim_{(U,\bar u)}\mathcal F(U),
$$

where $(U,\bar u)$ ranges over pointed étale neighborhoods. Filtered colimits of modules are exact, so stalks are exact. A map of sheaves is an isomorphism if and only if it is an isomorphism on every geometric stalk. The reason is local: a section or equality visible at a stalk occurs on some pointed neighborhood, and the geometric points cover every object of the site.

This yields a practical exactness test. A sequence of étale sheaves of modules is exact precisely when its stalk sequence is exact at every geometric point. Kernels are computed objectwise. Cokernels are sheafifications of objectwise cokernels, but their stalks are still the ordinary cokernels. One should not replace the sheaf cokernel by the presheaf cokernel before sheafification.

If $X=\operatorname{Spec}k$, lisse finite sheaves are finite continuous $G_k$-modules. General étale sheaves are larger: ramification or support may change from stratum to stratum, so a single global fundamental-group representation cannot describe them.

### 2.3 Morphisms and geometric fibers

A morphism $f:X\to Y$ induces a morphism of étale topoi. Its direct image is characterized by

$$
(f_*\mathcal F)(V)=\mathcal F(V\times_YX)
$$

for $V\to Y$ étale. It is left exact. The inverse-image functor $f^*$ is exact for abelian sheaves: it preserves finite limits as an inverse image of topoi and preserves all colimits as a left adjoint. Thus no left derivation is required for the inverse image of coefficient sheaves.

Given a geometric point $\bar y\to Y$, choose the strict localization $Y_{(\bar y)}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{Y,\bar y}$ and form

$$
X_{(\bar y)}=X\times_Y Y_{(\bar y)}.
$$

If $f$ is quasi-compact and quasi-separated and the coefficients are constructible torsion sheaves, then

$$
(R^qf_*\mathcal F)_{\bar y}
\cong H^q(X_{(\bar y)},\mathcal F).
$$

To prove this, compute the stalk as a filtered colimit over pointed étale neighborhoods $V$ of $\bar y$. Evaluation on $X_V$ sends an injective sheaf to a complex acyclic for sections, and filtered colimits of modules are exact, so the stalk is

$$
\varinjlim_V H^q(X_V,\mathcal F).
$$

The required continuity is a substantive theorem rather than an informal argument, and it is proved in Section 4.6 as the Continuity theorem: cohomological descent for hypercovers, proved in Section 4.5, reduces every class to finitely many finitely presented objects, sections, and identities, all of which descend through the filtered system of pointed neighborhoods. The same section derives from it the finite-coefficient proper base change theorem identifying $(R^qf_*\mathcal F)_{\bar s}$ with $H^q(X_{\bar s},\mathcal F)$ when $f$ is proper. Notice that the strict-localization formula alone is not yet geometric base change for nonproper $f$: $X_{(\bar y)}$ need not have the cohomology of the geometric fiber $X_{\bar y}$.

### 2.4 Why the finite-cover site is not enough

Finite locally constant sheaves are already controlled by finite étale covers, but cohomology needs arbitrary étale neighborhoods. Consider a curve $X$ and a closed point $i:x\hookrightarrow X$. The extension by zero of a finite sheaf on $x$ is constructible, yet it is not locally constant across $x$. Open immersions and complements, which drive localization sequences, are objects of the small étale site but are usually not finite over $X$.

There is also a cohomological warning. A cover trivializing a lisse sheaf need not itself be acyclic for that sheaf. Its ordinary Čech complex may therefore miss higher classes. The whole small site, or a sufficiently rich hypercover, is required. Finite covering theory supplies monodromy; the étale topos supplies descent in every degree.

## 3. Constructible and lisse torsion sheaves

### 3.1 Lisse sheaves

Let $\Lambda_0$ be a finite ring. A sheaf $\mathcal F$ of $\Lambda_0$-modules is **lisse** if étale-locally it is constant with finite stalk. If $X$ is connected and a geometric basepoint is chosen, taking the stalk gives an equivalence

$$
\{\text{lisse finite }\Lambda_0\text{-sheaves on }X\}
\simeq
\{\text{finite }\Lambda_0\text{-modules with continuous }\pi_1(X)\text{-action}\}.
$$

The action has finite image because the automorphism group of the stalk is finite. A lisse sheaf is **locally free of rank $r$** if its stalks are free $\Lambda_0$-modules of rank $r$; this condition is locally constant on $X$.

Kernels and cokernels of maps of lisse finite sheaves remain lisse: pass to a common finite étale cover trivializing both objects and the map. Tensor products and internal Hom remain lisse. Duality of modules preserves lissity, although a clean biduality statement requires finite projectivity of the stalk.

### 3.2 Constructible sheaves

A lisse sheaf cannot record a class supported at a singular point or boundary divisor. Constructibility allows finitely many controlled changes. On a noetherian scheme $X$, a sheaf $\mathcal F$ of finite $\Lambda_0$-modules is **constructible** if there is a finite partition

$$
X=\coprod_{\alpha}X_\alpha
$$

by locally closed reduced subschemes such that $\mathcal F|_{X_\alpha}$ is lisse. The strata may be refined, so intersections of two constructibility stratifications cause no ambiguity.

Constructible sheaves form a Serre subcategory: subobjects, quotients, and extensions are constructible. For a proof, refine until all given sheaves are lisse. On each connected stratum the assertion becomes the elementary statement that finite modules with continuous action are closed under kernels, cokernels, and extensions. Tensor products preserve constructibility; internal Hom does as well under finite-presentation hypotheses on the first variable.

A skyscraper sheaf $i_*M$ at a closed point is constructible but not lisse unless that point is an open-and-closed component. Conversely, a sheaf with finite stalks need not be constructible: on a noetherian space one may prescribe infinitely varying ramification along infinitely many closed points. Finiteness of every individual stalk does not supply a finite stratification.

### 3.3 Extension by zero and stratification

Let $j:U\hookrightarrow X$ be an open immersion and $i:Z\hookrightarrow X$ its closed complement. The functor $j_!$ extends a sheaf by zero. At a geometric point its stalk is the original stalk on $U$ and zero on $Z$, so exactness follows from the stalk criterion. There is a short exact sequence

$$
0\longrightarrow j_!j^*\mathcal F
\longrightarrow\mathcal F
\longrightarrow i_*i^*\mathcal F
\longrightarrow0.
$$

The last map is surjective on stalks. This sequence is the induction engine for constructible sheaves: choose a dense open stratum on which $\mathcal F$ is lisse, separate it from the lower-dimensional complement, and continue.

For a locally closed immersion $a:S\hookrightarrow X$, factor $a$ as a closed immersion followed by an open immersion and define $a_!$ accordingly. A finite stratification gives a filtration of a constructible sheaf whose successive quotients are $a_{\alpha!}\mathcal L_\alpha$ for lisse sheaves $\mathcal L_\alpha$ on strata. The filtration is not canonical, but finiteness and vanishing statements stable under extensions can be proved stratum by stratum.

### 3.4 Tate twists and Kummer theory

Because $\ell$ is invertible on $X$, the sheaf $\mu_{\ell^n}$ of $\ell^n$th roots of unity is finite étale and locally free of rank one over $\Lambda_n$. Define

$$
\Lambda_n(1)=\mu_{\ell^n},
\qquad
\Lambda_n(r)=\mu_{\ell^n}^{\otimes r}\quad(r\ge0),
$$

and for $r<0$ use the tensor power of the $\Lambda_n$-linear dual. These twists are compatible under reduction. Over a field their stalks carry the cyclotomic action. A choice of compatible roots of unity trivializes them as modules but not canonically as Galois modules.

The étale Kummer sequence

$$
1\longrightarrow\mu_{\ell^n}
\longrightarrow\mathbf G_m
\xrightarrow{(-)^{\ell^n}}\mathbf G_m
\longrightarrow1
$$

is exact. Surjectivity is étale-local: adjoining a root of $T^{\ell^n}-a$ is étale where $a$ is a unit because its derivative is invertible there. The resulting long exact sequence begins

$$
0\to \Gamma(X,\mathcal O_X^\times)/
\Gamma(X,\mathcal O_X^\times)^{\ell^n}
\to H^1(X,\mu_{\ell^n})
\to \operatorname{Pic}(X)[\ell^n]\to0.
$$

This calculation already shows why étale cohomology is arithmetic: units and line bundles meet in a single derived boundary map.

## 4. Derived global sections

### 4.1 The derived definition

Global sections are compatible families of local sections. The functor

$$
\Gamma(X,-):\operatorname{Sh}(X_{\mathrm{\acute et}},\Lambda_n)
\longrightarrow \operatorname{Mod}(\Lambda_n)
$$

is left exact but not generally right exact: a locally liftable section of a quotient sheaf need not possess one global lift. Its right-derived functor is

$$
R\Gamma(X,-):D^+(X_{\mathrm{\acute et}},\Lambda_n)
\longrightarrow D^+(\Lambda_n).
$$

For a sheaf $\mathcal F$ in degree zero, choose an injective resolution $\mathcal F\to I^\bullet$ and set

$$
H^q(X,\mathcal F)=H^q(\Gamma(X,I^\bullet)).
$$

Then $H^0=\Gamma$, short exact sequences give long exact cohomology sequences, and injective sheaves have no higher cohomology. For a complex $K$, its hypercohomology is

$$
\mathbb H^q(X,K)=H^q(R\Gamma(X,K)).
$$

The distinction matters. If $K=[\mathcal F\to\mathcal G]$, the hypercohomology is not determined merely by the kernels and cokernels of the displayed map; their extension inside $K$ can change the connecting morphisms.

### 4.2 Injective and K-injective models

Bounded-below complexes may be resolved by a Cartan--Eilenberg double resolution and totalized. An equivalent and more flexible language uses a **K-injective** complex $I$: every map from an acyclic complex to $I$ is null-homotopic. If $K\to I$ is a quasi-isomorphism with $I$ K-injective, then

$$
R\Gamma(X,K)=\Gamma(X,I).
$$

Every bounded-below complex of injective sheaves is K-injective. The lower bound is decisive: the homotopy killing a map from an acyclic complex is constructed degree by degree starting at the bottom. An unbounded termwise injective complex need not be K-injective because there may be no starting degree.

The category of sheaves here is Grothendieck, so arbitrary complexes admit K-injective replacements. We use this existence for derived inverse limits, whose product totalizations are often unbounded even when each coefficient level is bounded. The replacement is unique only up to unique isomorphism in the derived category. No cochain-level choice is intrinsic.

For tensor products, at least one variable must be replaced by a K-flat complex. Thus the cup-product source is

$$
R\Gamma(X,K)\otimes^L_{\Lambda_n}R\Gamma(X,L),
$$

not the ordinary tensor product of arbitrary representatives.

### 4.3 Čech complexes and hypercovers

An étale covering $\mathcal U=(U_i\to X)$ has a Čech nerve with degree-$p$ term the disjoint union of $(p+1)$-fold fiber products. Applying a sheaf gives the alternating Čech complex. There is a natural map from Čech cohomology to derived cohomology, but it need not be an isomorphism for one fixed cover: intersections may themselves have higher cohomology.

There are two safe uses. If every finite intersection of members of $\mathcal U$ is acyclic for $\mathcal F$, the augmented Čech complex is an acyclic resolution and computes $R\Gamma(X,\mathcal F)$. More generally, refine the Čech nerve degree by degree to a hypercover. Cohomological descent — proved in Section 4.5 — identifies the total complex over all levels with derived global sections, provided the boundedness needed for totalization holds.

For a strictly henselian local scheme and a finite locally constant sheaf, every finite étale cover splits, but it does not follow that every étale sheaf has zero higher cohomology without restrictions. The local splitting argument applies to locally constant finite data; arbitrary sheaves can still encode cohomology on nonfinite étale objects. This is another reason to state acyclicity rather than infer it from a suggestive cover.

### 4.4 Localization and hypercohomology

Let $i:Z\hookrightarrow X$ be closed with open complement $j:U\hookrightarrow X$. Sections supported on $Z$ form a left exact functor $\Gamma_Z(X,-)$. Its derived functor fits into the localization triangle

$$
R\Gamma_Z(X,K)\longrightarrow R\Gamma(X,K)
\longrightarrow R\Gamma(U,j^*K)
\longrightarrow R\Gamma_Z(X,K)[1].
$$

One construction resolves $K$ injectively and observes that the sequence of sections supported on $Z$, all sections, and sections on $U$ is exact after replacing the last term by the appropriate restriction of an injective. Taking cones gives the triangle. Its long exact sequence measures exactly which classes on $U$ fail to extend across $Z$.

Filtering a bounded-below complex $K$ by its truncations gives the hypercohomology spectral sequence

$$
E_2^{p,q}=H^p(X,\mathcal H^q(K))
\Longrightarrow \mathbb H^{p+q}(X,K).
$$

It converges strongly if $K$ is bounded below and $X$ has finite cohomological dimension on the occurring sheaves, or if only finitely many terms meet each total diagonal. The limiting terms are graded pieces of a filtration; even degeneration does not canonically split that filtration.

### 4.5 Cohomological descent for hypercovers

Section 4.3 explained why a single cover may fail to compute cohomology and announced that hypercovers do not fail. This subsection proves that announcement. Throughout it, $U_\bullet\to X$ is an **augmented simplicial object** of the small étale site: a simplicial diagram of étale objects over $X$, with structure maps $\varepsilon_p:U_p\to X$ compatible with the face and degeneracy operators, together with an augmentation to the constant simplicial object $X$. Write $\mathbf Z^{(U)}$ for the free abelian sheaf generated by an étale object $U$: its sections on $V$ are the finitely supported functions on the set of étale maps $V\to U$. The object is called a **hypercover** if for every $n\ge0$ the canonical map

$$
U_{n+1}\longrightarrow M_{n+1}(U_\bullet)
$$

to the object of matching families — tuples of $(n+1)$-fold composites over the $(n+2)$ face operators of $U_n$ that agree pairwise — is a covering in the sense of Section 2.1, jointly surjective on geometric points. It is **split** if it carries extra degeneracies $s_i:U_n\to U_{n+1}$ satisfying the simplicial identities beyond those of a simplicial object.

The theorem to prove is that a hypercover carries exactly as much cohomological information as the whole site. For a sheaf $\mathcal F$ and an injective resolution $\mathcal F\to\mathcal I^\bullet$, define the descent bicomplex

$$
C^{p,q}=\Gamma(U_p,\mathcal I^q|_{U_p}),
$$

with horizontal differentials induced by the alternating sum of face pullbacks and vertical differential induced by $\mathcal I^\bullet$, and define

$$
R\Gamma(U_\bullet,\mathcal F):=\operatorname{Tot}^{\prod} C^{\bullet,\bullet}.
$$

**Descent theorem.** Let $U_\bullet\to X$ be a hypercover and let $\mathcal F$ be any sheaf of abelian groups. Then the natural map

$$
R\Gamma(X,\mathcal F)\longrightarrow R\Gamma(U_\bullet,\mathcal F),
\qquad
\Gamma(X,\mathcal I^\bullet)\longmapsto
\big(\Gamma(U_0,\mathcal I^\bullet)\to\Gamma(U_1,\mathcal I^\bullet)\to\cdots\big),
$$

is an isomorphism in the derived category. In degree zero it says that sections satisfy descent along the hypercover; in every degree it says that no class can hide from a sufficiently rich simplicial resolution.

The proof rests on two lemmas, one combinatorial and one homological.

**Germ lemma.** Let $x$ be a geometric point of $X$ and let $E_\bullet=\operatorname{Hom}(x,U_\bullet)$ be the augmented simplicial set of germs of sections: an element of $E_p$ is an equivalence class of pairs consisting of a pointed étale neighborhood $V\to X$ of $x$ and a section of $U_p\times_XV\to V$, two pairs being identified when they agree after restriction to a common further pointed neighborhood. If $U_\bullet\to X$ is a hypercover, then $E_\bullet\to\{*\}$ is again a hypercover of a point: every matching map $E_{n+1}\to M_{n+1}(E_\bullet)$ is surjective, because surjectivity of matching maps is checked on geometric points and formation of germs commutes with fiber products and matching objects. Moreover the normalized chain complex of free abelian groups

$$
0\longrightarrow\mathbf Z\longrightarrow\mathbf Z[E_0]
\longrightarrow\mathbf Z[E_1]\longrightarrow\cdots
$$

is exact. To see this, first note that $E_0\to*$ is surjective, so $E_\bullet$ is nonempty. Exactness at the right end and vanishing of every higher homology follow by induction on the skeletal degree. Suppose all cycles of degree below $n$ bound and let $z=\sum a_i e_i$ be an $n$-cycle with $e_i\in E_n$. The tuple of faces $(d_ie_i)_i$ need not agree, so consider instead the subcomplex generated by the images: decomposing each $e_i$ against the surjection

$$
E_{n+1}\longrightarrow M_{n+1}(E_{\le n})
$$

means choosing lifts: because $z$ is a cycle, the alternating sum of its faces vanishes, which says precisely that the family $(d_1e_i,d_2e_i,\dots)$ defines an element of the free module on the matching space; choose a lift $\tilde e_i\in E_{n+1}$ of the matching family determined by $e_i$'s faces. Then

$$
z=\partial{\Big(\sum_i a_i\tilde e_i\Big)}
+\text{(a cycle supported in degrees $\le n-1$ of the degenerate part)},
$$

and the second summand bounds by the induction hypothesis applied to the degenerate subcomplexes, whose chain complexes split off contractibly by the usual degeneracy contraction $h=\sum(-1)^i s_i$. This is the standard statement that hypercovers of a point have trivial homotopy type; the induction above is its elementary form. We will only use the consequence recorded in the lemma: the free chain complex is acyclic. $\square$

**Injectivity lemma.** If $\mathcal I$ is injective, the augmented complex

$$
0\longrightarrow\mathcal I(X)
\longrightarrow\mathcal I(U_0)
\longrightarrow\mathcal I(U_1)
\longrightarrow\cdots
$$

is exact as a complex of abelian groups.

_Proof._ Consider the augmented complex of free sheaves

$$
0\longrightarrow\mathbf Z^{(X)}
\longrightarrow\mathbf Z^{(U_0)}
\longrightarrow\mathbf Z^{(U_1)}
\longrightarrow\cdots .
$$

Exactness of a complex of sheaves is checked on stalks, and the stalk of $\mathbf Z^{(U_p)}$ at $x$ is the free module on the germ set $E_p$: a germ is exactly an equivalence class of pairs (pointed neighborhood, local section), which is how the stalk of a representable-generated free sheaf is computed. Under this identification the stalk complex is the germ chain complex of the Germ lemma, hence exact. Now break the exact complex into short exact sequences

$$
0\longrightarrow Z^p\longrightarrow \mathbf Z^{(U_p)}\longrightarrow Z^{p+1}\longrightarrow 0,
\qquad
Z^p=\ker\big(\mathbf Z^{(U_p)}\to\mathbf Z^{(U_{p+1})}\big),
$$

with $Z^0$ the image of $\mathbf Z^{(X)}$, so that $Z^0=\mathbf Z^{(X)}$. Applying the functor $\operatorname{Hom}(-,\mathcal I)$ and using injectivity of $\mathcal I$, each sequence remains exact after applying it:

$$
0\to\operatorname{Hom}(Z^{p+1},\mathcal I)\to
\operatorname{Hom}(\mathbf Z^{(U_p)},\mathcal I)\to
\operatorname{Hom}(Z^p,\mathcal I)\to0 .
$$

Splicing these gives exactness of

$$
0\to\operatorname{Hom}(\mathbf Z^{(X)},\mathcal I)\to
\operatorname{Hom}(\mathbf Z^{(U_0)},\mathcal I)\to\cdots ,
$$

and Yoneda computes $\operatorname{Hom}(\mathbf Z^{(U)},\mathcal I)=\mathcal I(U)$. $\square$

_Proof of the Descent theorem._ Filter both sides by the resolution degree $q$. Since $\mathcal F\to\mathcal I^\bullet$ is bounded below, the spectral sequences of these filtrations converge strongly and it suffices to prove that for every fixed $q$ the map

$$
\Gamma(X,\mathcal I^q)\longrightarrow
\Gamma(U_\bullet,\mathcal I^q|_{U_\bullet})
$$

of row complexes is a quasi-isomorphism. For injective $\mathcal I^q$ this is exactly the Injectivity lemma, which identifies both sides with the single group $\Gamma(X,\mathcal I^q)$ in horizontal degree zero. $\square$

Two corollaries convert the theorem into the computational forms used later.

**Split-enlargement corollary.** Every semisimplicial hypercover admits a termwise-covering refinement by a split hypercover. Indeed, replace $U_n$ by

$$
\tilde U_n=\coprod_{\alpha}U_m,
$$

the disjoint union indexed by all order-preserving surjections $\alpha:[m]\twoheadrightarrow[n]$ with $m\ge n$, the structure maps being given by precomposition and postcomposition of surjections, and retain $U_n$ as the summand indexed by the identity. The canonical projections $\tilde U_n\to U_n$ respect augmentations and are termwise covering, since the identity summand already covers what is needed once the matching condition supplies the remaining summands; the extra degeneracies are furnished by the unique surjections $[n]\twoheadrightarrow[n]$ factored through maximal nondegenerate indices, and the simplicial identities are verified termwise on the indexing categories. Because both $U_\bullet$ and $\tilde U_\bullet$ are hypercovers, the Descent theorem applies to each and the termwise-covering map induces an isomorphism between their descent complexes. Consequently nothing is lost by working with split hypercovers when convenient.

**Čech spectral-sequence corollary.** Let $U_\bullet\to X$ be a hypercover such that only finitely many nondegenerate objects occur in each simplicial degree relevant to a bounded range, and suppose each has bounded cohomological dimension for the coefficients in question. Then there is a spectral sequence

$$
E_1^{a,b}=\prod_{u\text{ nondegenerate in degree }a}H^b(u,\mathcal F|_u)
\Longrightarrow H^{a+b}(X,\mathcal F),
$$

with differentials induced by alternating sums of face maps, natural in $\mathcal F$ and in refinement of hypercovers.

_Proof._ The filtration of the Descent theorem by resolution degree has graded pieces computed by the Injectivity lemma; filtering instead by the simplicial degree $a$ and using the standard convergence of the product-totalization under the stated boundedness gives a spectral sequence whose $E_1$ page is the cohomology of the $U_a$'s pushed through the vertical direction. Concretely, resolve $\mathcal F$ by injectives, take cohomology in the vertical variable first: $E_1^{a,b}$ receives $\prod_a H^b(U_a,\mathcal F|_{U_a})$, and the Dold decomposition of a simplicial scheme into nondegenerate pieces, available in particular for the split enlargement of the Split-enlargement corollary where the decomposition is canonical, replaces $U_a$ by its nondegenerate summands without changing the totalization. Naturality is evident from the construction. $\square$

This corollary is the precise form of the assertion used in Section 7.2, where the products are finite and the $b$-direction is bounded by the affine lemma. It should be compared with Section 4.3's warning: for one fixed Čech nerve, the $E_1$ page need not converge to anything useful unless the nerve is a hypercover or its members are acyclic; the Descent theorem shows that passing to the full hypercover removes exactly the missing information, and the corollary packages it as a spectral sequence rather than an unjustified equality.

### 4.6 Continuity and finite-coefficient base change

The Descent theorem reduces cohomology to simplicial diagrams built from fiber products of étale objects. Such diagrams are made of finitely presented equations whenever the site is, and this is what lets cohomology pass through filtered limits of schemes. Throughout this subsection, $(X_i)_{i\in I}$ is a filtered inverse system of quasi-compact quasi-separated schemes with affine transition maps, $X=\varprojlim_iX_i$, and $g_i:X\to X_i$ denotes the projection.

**Sections lemma.** Let $V=\varprojlim_kV_k$ be such a limit and let $\mathcal G$ be a constructible sheaf of finite modules on $V$ that descends to some $V_k$, so $\mathcal G\simeq g_k^*\mathcal G_k$. Then

$$
\Gamma(V,\mathcal G)=\varinjlim_m\Gamma(V_m,\mathcal G_m)
$$

for every $m\ge k$, where $\mathcal G_m=g_{mk}^*\mathcal G_k$.

_Proof._ A clopen subset of $V$ corresponds to an idempotent of $\Gamma(V,\mathcal O_V)$, and coordinate rings commute with the limit, so every clopen subset of $V$ is the preimage of a clopen subset of some $V_m$. A constructible sheaf admits a finite partition into locally closed pieces on which it is lisse; refining the pieces until their closures separate, a section of $\mathcal G$ is given by finitely many clopen subsets of these pieces carrying values in one finite module with prescribed gluing across boundaries. Each datum is a finite list of clopen sets and module elements, and compatibility across overlaps is a finite list of equalities of such elements; all of it descends to some $V_m$ by the idempotent statement. Conversely, pulling back identifies the colimit with a subset of $\Gamma(V,\mathcal G)$, and the two constructions are inverse. $\square$

**Continuity theorem.** Let $\mathcal F$ be a constructible sheaf of finite modules on $X$ descending to some $X_i$. Then for every $q\ge0$ the natural map

$$
H^q(X,\mathcal F)\longrightarrow\varinjlim_jH^q(X_j,g_j^*\mathcal F)
$$

is an isomorphism.

_Proof._ Choose a finite affine étale cover of $X$: it descends to a finite affine étale cover of some $X_j$, because étale morphisms of finite presentation descend through the limit after reindexing, and quasi-compactness lets us take finitely many members. Refine the resulting nerve degree by degree to a hypercover: given the skeleton through degree $n$, the matching object is of finite presentation over the base, and any covering of it admits a finite refinement whose members are fiber products of earlier objects with affines étale over them; each such member descends after a further reindexing by the same descent of étale morphisms. Truncating in simplicial degree $q+1$ gives a truncated hypercover $U_\bullet$ of $X$, and, after reindexing once more, a truncated hypercover $U_{j,\bullet}$ of $X_j$ with $U_\bullet=U_{j,\bullet}\times_{X_j}X$, together with an identification of the descended coefficient sheaf. For a fixed degree $q$ only this truncation matters: the Descent theorem computes $H^q$ on both sides from the total complexes of these truncations. Every entry satisfies

$$
\Gamma(U_p,\mathcal F|_{U_p})
=\varinjlim_m\Gamma(U_{m,p},g^*\mathcal F_m)
$$

by the Sections lemma, since $U_p$ is affine. Filtered colimits of modules are exact, so they commute with cohomology of the total complexes, and the transition maps of the system identify the colimit complex with the total complex downstairs. This proves the theorem. $\square$

The first application is the formula announced in Section 2.3. Let $f:X\to Y$ be quasi-compact and quasi-separated, let $\bar y$ be a geometric point of $Y$, and let $\mathcal F$ be constructible torsion. Among pointed étale neighborhoods of $\bar y$, the affine ones are cofinal: every étale neighborhood contains an affine open neighborhood of the image point, itself an étale object of the site. For affine $W\subseteq V$ the transition $X\times_YW\to X\times_YV$ is affine, being a base change of $W\to V$. Hence the Continuity theorem applies to the system $(X_V)$ over the cofinal affine neighborhoods and yields

$$
(R^qf_*\mathcal F)_{\bar y}
=H^q(X_{(\bar y)},\mathcal F)
=\varinjlim_VH^q(X_V,\mathcal F),
$$

as asserted there, with the proof now resting on the Descent theorem rather than on an informal appeal to representatives of classes.

The second application is the base-change statement for proper morphisms at finite coefficient level, which Chapter 7 uses and which isolates exactly the input that later books generalize.

**Finite-coefficient proper base change theorem.** Let $S$ be locally noetherian, let $f:X\to S$ be proper, let $\ell$ be invertible on $S$, and let $\mathcal F$ be a constructible sheaf of finite $\ell$-primary modules. Then for every geometric point $\bar s$ of $S$ the canonical map

$$
(R^qf_*\mathcal F)_{\bar s}\longrightarrow H^q(X_{\bar s},\mathcal F)
$$

is an isomorphism for all $q\ge0$.

_Proof._ By the strict-localization formula above, the left side is the colimit of $H^q(X_V,\mathcal F)$ over pointed étale neighborhoods $V$ of $\bar s$, and the canonical map is induced by restriction along the closed fiber $X_{\bar s}\to X_V$.

We use two preparatory observations. First, on the noetherian scheme $X_{\bar s}$, every class of $H^q(X_{\bar s},\mathcal F)$ is represented on a hypercover truncated in simplicial degree $q+1$ whose terms are quasi-compact étale objects, carrying finitely many coefficient sections and finitely many cocycle identities: this is the Descent theorem plus a noetherian induction showing that the refinements demanded by the matching condition can be taken finite at every stage. The same holds for the cochains and homotopies witnessing that a class restricts to zero. Second, every étale morphism of finite presentation $W\to X_{\bar s}$ lifts, after shrinking $V$, to an étale morphism $W'\to X_V$ recovering $W$ on the closed fiber: étale morphisms lift through arbitrary thickenings, and $X_V\to X_{\bar s}$ is formally étale in the relevant sense, while finite presentation keeps the lift of finite presentation.

For surjectivity, represent a class $\alpha\in H^q(X_{\bar s},\mathcal F)$ by such finite truncated data and lift all its objects, sections, and identities to $X_V$. The union of the images of the lifted degree-zero objects contains $X_{\bar s}$. Its complement in $X_V$ is closed; its image in $S$ is closed because $f$ is proper; and that image does not contain $\bar s$. A closed subset of $S$ whose image avoids the geometric point $\bar s$ is disjoint from some pointed étale neighborhood, since its complement is an open neighborhood of the image of $\bar s$. Hence after shrinking $V$ the lifted degree-zero objects cover all of $X_V$, and the lifted identities make the lifted data a truncated hypercover with a lifted cocycle. The Descent theorem exhibits the lifted cocycle as a class on $X_V$ restricting to $\alpha$. This proves surjectivity.

For injectivity, let $\beta\in H^q(X_V,\mathcal F)$ restrict to zero. Represent $\beta$ by finite truncated data as above, lift it back down to $X_{\bar s}$, where it vanishes, and represent the vanishing by finitely many cochains and homotopy identities through simplicial degree $q$. Lift those identities to $X_V$: the required equalities of sections hold on the closed fiber, hence hold after shrinking $V$, because equality of two sections of a constructible sheaf is detected on stalks at geometric points, and geometric points of the closed fiber spread through $X_V$. The shrunk data witness $\beta$ as a coboundary. $\square$

Three remarks delimit what has been proved. First, the theorem concerns constructible torsion coefficients only; its adic and smooth-morphism extensions belong to the next book, whose arguments consume the present statement together with the Descent theorem. Second, the proof uses properness exactly once, to force the complement of the lifted cover to disappear; nothing in it requires smoothness, and the conclusion holds verbatim for any proper morphism of locally noetherian bases. Third, combining the theorem with the Kummer computations of Section 6.7 already determines the geometric stalks of the higher direct images of relative curves; what it does not do, by itself, is identify the sheaves $R^qf_*\mathcal F$ globally. That identification is carried out in Section 7.2 for curves, and it needs the relative Picard construction of Book 17a rather than stalk values alone.

## 5. Functoriality and spectral sequences

### 5.1 Derived direct image and Leray

For $f:X\to Y$, choose a K-injective replacement $K\to I$ and define

$$
Rf_*K=f_*I.
$$

Direct image preserves injectives: it is right adjoint to the exact functor $f^*$. Hence applying global sections on $Y$ to an injective direct image is acyclic, and there is a canonical isomorphism

$$
R\Gamma(X,K)\simeq R\Gamma(Y,Rf_*K).
$$

Filtering $Rf_*K$ by truncations gives Leray:

$$
E_2^{p,q}=H^p(Y,R^qf_*K)
\Longrightarrow H^{p+q}(X,K).
$$

For a finite morphism $f$, the direct image on abelian étale sheaves is exact. Check exactness on a geometric stalk of the target and pass to the strict localization. A finite scheme over a strictly henselian local scheme is a finite disjoint union of henselian local schemes with separably closed residue fields. Every étale covering of each such local scheme has a section, so its global-section functor is exact. The stalk criterion now proves exactness of $f_*$. Therefore $R^qf_*=0$ for $q>0$, and Leray gives

$$
R\Gamma(X,K)\simeq R\Gamma(Y,f_*K).
$$

For finite étale $f$, this is the cohomological form of induction along a finite cover; the exactness statement itself also applies to ramified finite maps such as normalization.

### 5.2 Arithmetic descent and Hochschild--Serre

Let $X/k$ be of finite type and let $\mathcal F$ descend to $X$. Galois descent on the whole base change $\bar X$ gives

$$
E_2^{a,b}=H^a_{\mathrm{cts}}
\bigl(G_k,H^b(\bar X,\mathcal F)\bigr)
\Longrightarrow H^{a+b}(X,\mathcal F).
$$

Here the finite-level geometric cohomology groups are discrete $G_k$-modules. The sequence can be constructed by taking a resolution of $\mathcal F$ on $\bar X$, applying continuous inhomogeneous cochains for $G_k$, and totalizing. Filtering by either degree gives the spectral sequence. Its five-term portion begins

$$
0\to H^1(G_k,H^0(\bar X,\mathcal F))
\to H^1(X,\mathcal F)
\to H^1(\bar X,\mathcal F)^{G_k}
\to H^2(G_k,H^0(\bar X,\mathcal F)).
$$

Thus a geometrically invariant class need not descend; the final arrow is its obstruction. If $X$ is geometrically disconnected, $G_k$ permutes all components and the same sequence remains valid for their union. Only a reformulation through the fundamental group of one chosen component replaces $G_k$ by its stabilizer. If the coefficient object is completed, continuous cochains and derived inverse limits must both be retained; Section 11 returns to this point.

### 5.3 Coefficient change

For a homomorphism $\Lambda_n\to A$ and $K\in D(X,\Lambda_n)$, coefficient change is $K\otimes^L_{\Lambda_n}A$. There is a canonical morphism

$$
R\Gamma(X,K)\otimes^L_{\Lambda_n}A
\longrightarrow
R\Gamma(X,K\otimes^L_{\Lambda_n}A).
$$

It is an isomorphism, for example, when $A$ is perfect over the coefficient ring, by the projection formula, or when compatible bounded flat models compute both sides. One must not obtain reduction from $\Lambda_n$ to $\Lambda_1$ by pretending that multiplication by $\ell$ is a non-zero-divisor in $\Lambda_n$; it is not.

The useful two-term formula is instead integral. If $C$ is a complex of $\Lambda=\mathbf Z_\ell$-modules, then the free resolution of $\Lambda_1$ over $\Lambda$ gives a triangle

$$
C\xrightarrow{\ell}C\longrightarrow C\otimes^L_\Lambda\Lambda_1
\longrightarrow C[1]
$$

and therefore

$$
0\to H^i(C)/\ell H^i(C)
\to H^i(C\otimes^L_\Lambda\Lambda_1)
\to H^{i+1}(C)[\ell]\to0.
$$

The right-hand torsion term is the exact reason reduction of cohomology need not equal cohomology after reduction. It disappears if $H^{i+1}(C)$ is $\ell$-torsion-free, but freeness of $H^i(C)$ alone does not suffice.

### 5.4 Boundedness and convergence

Every spectral sequence above requires an abutment argument. First-quadrant sequences converge strongly because a fixed total degree meets only finitely many bidegrees. For an unbounded coefficient complex, finite cohomological dimension of $X$ is not by itself enough: infinitely many coefficient degrees can still meet one total degree. One also needs boundedness of $K$, finite Tor amplitude, or a complete filtration with controlled derived limits.

The following rule will be used repeatedly. Suppose $K$ has constructible cohomology sheaves, is zero outside a finite interval $[a,b]$, and every such sheaf has cohomology zero above $d$. Then

$$
R\Gamma(X,K)\in D^{[a,b+d]}.
$$

Indeed, the hypercohomology sequence is supported in the rectangle $0\le p\le d$, $a\le q\le b$. It is therefore finite on every diagonal and converges strongly. This simple rectangle argument is the bridge from torsion cohomological dimension to bounded adic complexes.

## 6. Torsion cohomological dimension and the cohomology of curves

### 6.1 What cohomological dimension measures

For a torsion ring $A$, the $A$-cohomological dimension of $X$ is the least $d$ such that

$$
H^q(X,\mathcal F)=0\qquad(q>d)
$$

for every sheaf of $A$-modules in the stated coefficient class. We mostly use the constructible $\ell$-primary dimension, denoted $\operatorname{cd}_\ell(X)$. The restriction to $\ell$ invertible on $X$ is essential. In residue characteristic $\ell$, wild ramification produces different bounds and Kummer theory ceases to be étale.

Cohomological dimension is a uniform vanishing statement, not a dimension count for one familiar sheaf. For example, $H^q(X,\Lambda_n)=0$ above a certain degree does not automatically imply the same for every constructible sheaf. Stratification and finite-cover descent are needed to pass between coefficients.

### 6.2 Fields and strict local schemes

For $X=\operatorname{Spec}k$, étale cohomology of a finite discrete module agrees with continuous Galois cohomology:

$$
H^q(X,M)=H^q_{\mathrm{cts}}(G_k,M).
$$

To prove this, identify the étale topos of the field with discrete continuous $G_k$-sets. Global sections become invariants, and both sides are their right-derived functors. A separably closed field has trivial absolute Galois group, hence cohomological dimension zero. A finite field has $\ell$-cohomological dimension one for $\ell$ different from its characteristic: its absolute Galois group is procyclic, and the two-term continuous complex

$$
M\xrightarrow{\varphi-1}M
$$

computes cohomology, where $\varphi$ is arithmetic Frobenius.

A strictly henselian local scheme has no nontrivial finite étale covers, so every finite locally constant sheaf is constant and its degree-one torsors vanish. Triviality of the finite-cover category alone does not prove vanishing in every higher degree on the whole small étale site; such a rigidity assertion needs a separate cohomological argument. For constructible sheaves on a strict localization, closed strata can contribute, and the appropriate local dimension bound depends on the dimension of the local scheme.

### 6.3 Curves

Let $C$ be a curve of finite type over a separably closed field $k$, and assume $\ell\ne\operatorname{char}k$. If $C$ is affine, then

$$
H^q(C,\mathcal F)=0\qquad(q>1)
$$

for every constructible $\ell$-primary sheaf $\mathcal F$. If $C$ is proper, the corresponding bound is $q>2$.

Both assertions are proved in Section 6.7, and the affine one is the one-dimensional case of the affine theorem of Section 7.2. It is worth isolating why finite-cover descent alone is not their proof. If a finite Galois cover with group $G$ trivializes a lisse sheaf and $\ell$ divides $|G|$, the groups $H^a(G,-)$ can be nonzero in arbitrarily large degrees. The differentials in the descent sequence must then cancel those terms, and nothing in the descent formalism explains the cancellation. Sections 6.5 through 6.7 obtain the bounds instead from the field at the generic point: Tsen's theorem makes that field have no Brauer classes and no cohomology above degree one, and the divisor sequence for $\mathbf G_m$ transports the consequence to the curve. No presentation of a fundamental group and no vanishing of finite-group cohomology is used.

Normalization and the finite singular locus then extend the smooth affine result to every affine curve. More explicitly, for the normalization $\nu:\widetilde C\to C$, the kernel and cokernel of

$$
\mathcal F\longrightarrow \nu_*\nu^*\mathcal F
$$

are supported on finitely many points. Finite pushforward is exact, and a sheaf supported at a geometric point has no positive cohomology. The long exact sequence therefore transfers both the degree-one bound and finiteness from the normalized affine curve to $C$. For a proper curve, a finite affine cover has intersections that are affine because the curve is separated. The cover-to-derived spectral sequence has Čech degree at most one and affine cohomological degree at most one, giving the bound two.

The difference between the affine and proper bounds is sharp: a proper smooth curve can have a nonzero degree-two class, whereas the affine theorem rules out degree two after a point is removed. Constructing the trace that canonically identifies the top group, and proving its perfect pairing with degree zero, belong to the duality theory. No trace is used in the dimension proof here.

### 6.4 Low-dimensional finite-type schemes

For a separated scheme $X$ of finite type and dimension $d$ over a separably closed field, constructible $\ell$-primary sheaves satisfy

$$
H^q(X,\mathcal F)=0\qquad(q>2d).
$$

In the required range we need only $d\le2$, but the argument of Section 7.2 proves the displayed statement for every $d$. Its two inputs are different. The affine theorem gives the sharper bound $d$ on an affine $d$-fold. A dimension-controlled affine refinement of a separated noetherian scheme contributes at most another $d$ Čech degrees. This distinction is important: merely covering by an unspecified finite number of affine opens proves finiteness but does not prove the bound $2d$. For $d=2$, the possible degrees are therefore $0,1,2,3,4$.

If $X$ is affine of dimension $d$, the sharper prime-to-characteristic bound $H^q(X,\mathcal F)=0$ for $q>d$ holds for every constructible torsion coefficient sheaf, not only for lisse ones. The constructible form is required for induction across a boundary. The global bound remains $2d$ because gluing the affine pieces can add another $d$ degrees.

Over a nonclosed field, Hochschild--Serre adds the cohomological dimension of the ground field. More precisely, if $G_k$ has $\ell$-cohomological dimension $c$ on the finite modules in question, then

$$
H^q(X,\mathcal F)=0\qquad(q>2d+c).
$$

This follows immediately from the rectangle supporting the spectral sequence. No finite value is asserted for fields whose absolute Galois groups have unbounded $\ell$-cohomology.

### 6.5 Tsen's theorem

The cohomological dimension of a curve cannot be read off from its finite covers. What controls it is the field at the generic point. That field is not separably closed, but it is close enough for our purposes: every homogeneous form in more variables than its degree has a nontrivial zero. This is Tsen's theorem, and its proof is a dimension count with Riemann--Roch, not a transcendental argument.

**Definition.** A field $F$ is $C_1$ if every homogeneous polynomial
$f\in F[T_1,\ldots,T_N]$ of degree $d$ with $0<d<N$ has a zero $t\in F^N$ with $t\ne0$.

We first isolate the algebraic mechanism.

**Common-zero lemma.** Let $\kappa$ be an algebraically closed field and let $g_1,\ldots,g_r\in\kappa[X_1,\ldots,X_n]$ be homogeneous of positive degree with $n>r$. Then the $g_i$ have a common zero in $\kappa^n$ other than the origin.

**Proof.** Let $Z\subseteq\mathbf A^n_\kappa$ be the closed subscheme they define. Since the $g_i$ are homogeneous of positive degree, the origin lies in $Z$. Krull's height theorem, recorded as a standard input in Book 11, Chapter 14, bounds by $r$ the height of every prime minimal over $(g_1,\ldots,g_r)$. In the polynomial ring over a field, height and dimension of the quotient add up to $n$, so every irreducible component of $Z$ has dimension at least $n-r\ge1$. A component through the origin therefore contains points other than the origin, and every such point is a common zero. $\square$

**Tsen's theorem.** Let $k$ be an algebraically closed field and let $K$ be a finitely generated extension of $k$ of transcendence degree one. Then $K$ is $C_1$.

**Proof.** Write $K=k(C)$ for a smooth proper connected curve $C$ over $k$ of genus $g$. Such a model exists: choose a finitely generated $k$-subalgebra of $K$ with fraction field $K$, embed its spectrum in affine space, take the closure in projective space, and normalize; the finite-normalization lemma for curves of Book 8, Section 9.1, makes the normalization finite, so the result is a normal projective curve with function field $K$, and Book 11, Proposition 4.2, makes a normal curve over a perfect field smooth.

Let $f=\sum_\nu a_\nu T^\nu$ be homogeneous of degree $d$ in $T_1,\ldots,T_N$ with $N>d\ge1$ and $a_\nu\in K$. The finitely many $a_\nu$ have finitely many poles, so there is an effective divisor $D$ on $C$, of some degree $\delta\ge1$, with every $a_\nu\in H^0(C,\mathcal O(D))$. For $m\ge0$ put

$$
V_m=H^0(C,\mathcal O(mD)).
$$

If $t_1,\ldots,t_N\in V_m$, then $t^\nu\in H^0(\mathcal O(dmD))$ and hence

$$
f(t_1,\ldots,t_N)\in W_m:=H^0(C,\mathcal O((dm+1)D)).
$$

Riemann--Roch on $C$, in the unconditional Euler-characteristic form (11.1) of Book 9, gives $\chi(\mathcal O(mD))=m\delta+1-g$, so $\dim_kV_m\ge m\delta+1-g$; and once $m\delta\ge 2g-1$ the computation of Book 15, Section 10.2, gives the exact value $\dim_kW_m=(dm+1)\delta+1-g$ for the larger degree as well.

Choose coordinates for $V_m$ and $W_m$. The assignment $(t_1,\ldots,t_N)\mapsto f(t)$ is then given by $\dim_kW_m$ homogeneous polynomials of degree $d$, with coefficients in $k$, in the $n_m:=N\dim_kV_m$ coordinates of $V_m^N$. Now

$$
n_m-\dim_kW_m
\ \ge\ (N-d)\delta m+\bigl(N(1-g)-\delta-1+g\bigr),
$$

and the coefficient of $m$ is positive because $N>d$ and $\delta\ge1$. Fix $m$ large enough that this is positive and that $m\delta\ge 2g-1$. The common-zero lemma over the algebraically closed field $k$ supplies a nonzero common zero, that is, elements $t_1,\ldots,t_N\in V_m\subseteq K$, not all zero, with $f(t)=0$. $\square$

Two remarks fix the scope. First, every finite extension of $K$ is again a finitely generated extension of $k$ of transcendence degree one, so the theorem applies to all of them simultaneously; this is what makes the cohomological consequence of the next section uniform in the extension. Second, the standing hypothesis of this book is that the ground field is separably closed, not algebraically closed. If $k$ is separably closed of characteristic $p>0$, then $\bar k/k$ is purely inseparable, so $X_{\bar k}\to X$ is a universal homeomorphism for every $k$-scheme $X$. Book 17, Section 13.3, proves that such a morphism identifies pointed étale neighbourhoods at corresponding geometric points; consequently it induces an equivalence of small étale sites, and every étale-cohomological statement below may be proved after base change to $\bar k$. We therefore assume $k=\bar k$ in Sections 6.5 through 6.8 without further comment.

### 6.6 The Brauer group of a curve and cohomological dimension one

Tsen's theorem is a statement about forms. To use it cohomologically we pass through central simple algebras and then through a purely group-theoretic dimension bound. Both steps are needed: the first converts $C_1$ into vanishing of $H^2$ with multiplicative coefficients, and the second converts vanishing of $H^2$ into vanishing in all higher degrees for all torsion coefficients.

We first record the two multiplicative inputs in the form used here. Let $F$ be any field with separable closure $F^s$ and $G_F=\operatorname{Gal}(F^s/F)$.

**Hilbert 90.** $H^1(G_F,(F^s)^\times)=0$.

**Proof.** Continuous cochains have finite image and factor through a finite quotient, so by the inflation--restriction sequence of Book 7a, Section 9.3, it suffices to prove $H^1(\operatorname{Gal}(L/F),L^\times)=0$ for every finite Galois $L/F$ with group $\Gamma$. A $1$-cocycle $c$ is exactly a descent datum on the free rank-one $L$-module $L$ relative to the faithfully flat cover $\operatorname{Spec}L\to\operatorname{Spec}F$, written in the transition-matrix form of Book 10, Section 9.2. Effective descent of line bundles along a faithfully flat cover, Book 10, Section 9.1, produces an $F$-line $V$ with $V\otimes_FL\simeq L$ carrying that datum; choosing a basis vector of $V$ gives $y\in L^\times$ with $c_\sigma=\sigma(y)/y$. Hence $c$ is a coboundary. $\square$

**Brauer comparison.** $\operatorname{Br}(F)\simeq H^2(G_F,(F^s)^\times)$.

**Proof.** For finite Galois $L/F$ with group $\Gamma$, Book 5, Section 4.5, proves the crossed-product isomorphism $\operatorname{Br}(L/F)\simeq H^2(\Gamma,L^\times)$. Every central simple algebra is split by a finite separable, hence a finite Galois, extension, because a matrix presentation over an algebraic closure involves finitely many coefficients (Book 5, Section 4.2); so $\operatorname{Br}(F)$ is the union of the groups $\operatorname{Br}(L/F)$. On the other side, a continuous $2$-cocycle with values in $(F^s)^\times$ has finite image and is inflated from some finite quotient. In the Hochschild--Serre spectral sequence of Book 7a, Section 9.3, for the normal subgroup $G_L\subseteq G_F$ the term $E_2^{0,1}=H^1(G_L,(F^s)^\times)^\Gamma$ vanishes by Hilbert 90, so no differential reaches $E_2^{2,0}=H^2(\Gamma,L^\times)$ and every inflation map $H^2(\Gamma,L^\times)\to H^2(G_F,(F^s)^\times)$ is injective. The two unions therefore agree. $\square$

**Brauer vanishing.** Let $k$ be algebraically closed and $K$ a finitely generated extension of transcendence degree one. Then $\operatorname{Br}(K)=0$, and therefore $H^2(G_K,(K^s)^\times)=0$.

**Proof.** By Wedderburn (Book 5, Section 4.1) every Brauer class is represented by a central division algebra $D$ with $[D:K]=d^2$. Book 5, Section 4.2, constructs the reduced norm $\operatorname{Nrd}:D\to K$ by taking the determinant of a matrix presentation over a splitting field; in a $K$-basis of $D$ this determinant is a homogeneous polynomial of degree $d$ in $d^2$ coordinates, and Galois invariance places its coefficients in $K$. If $d\ge2$, then $d^2>d$, so Tsen's theorem produces $a\in D$, $a\ne0$, with $\operatorname{Nrd}(a)=0$. Multiplicativity of the reduced norm and $\operatorname{Nrd}(1)=1$ show that an invertible element has nonzero reduced norm; hence $a$ is not invertible, contradicting that $D$ is a division algebra. So $d=1$ and $\operatorname{Br}(K)=0$. $\square$

The passage from degree two to all higher degrees is group theory. We state it once, in the only form used.

**Dimension-one lemma.** Let $G$ be a profinite group and $\ell$ a prime, and suppose that $H^2(H,\mathbf Z/\ell)=0$ for every open subgroup $H\subseteq G$, the action being trivial. Then $H^q(G,M)=0$ for every $q\ge2$ and every discrete $\ell$-primary torsion $G$-module $M$.

**Proof.** Continuous cochain cohomology commutes with filtered colimits of discrete modules, by the cochain description of Book 7a, Section 9.1, so we may assume $M$ finite.

Choose a pro-$\ell$ Sylow subgroup $P\subseteq G$: writing $G=\varprojlim_iG_i$ with $G_i$ finite, a surjection of finite groups carries Sylow $\ell$-subgroups onto Sylow $\ell$-subgroups, so the sets of Sylow $\ell$-subgroups of the $G_i$ form an inverse system of nonempty finite sets, whose limit is nonempty; let $P=\varprojlim S_i$ for a compatible family. It is pro-$\ell$. If $H\supseteq P$ is open, choose $i$ with $\ker(G\to G_i)\subseteq H$; then $H$ is the preimage of a subgroup of $G_i$ containing $S_i$, so $[G:H]$ divides $[G_i:S_i]$ and is prime to $\ell$.

Over $P$ the conclusion is elementary. A simple discrete $\ell$-torsion $P$-module is finite with open stabilizers, so a finite $\ell$-group acts on it; a finite $\ell$-group acting on a nonzero finite abelian $\ell$-group has nonzero fixed points, so simplicity forces the module to be $\mathbf Z/\ell$ with trivial action. Since a continuous cochain on $P$ with values in a discrete module is the restriction of one on some open $H\supseteq P$, and two such agree on a smaller one, $H^\bullet(P,M)$ is the filtered colimit of $H^\bullet(H,M)$ over the open $H\supseteq P$; in particular $H^2(P,\mathbf Z/\ell)=0$ by hypothesis. Filtering an arbitrary finite $\ell$-primary $P$-module by simple subquotients and using the long exact sequences gives $H^2(P,M)=0$ for every such module. For $q>2$, embed $M$ into $M^*=\operatorname{Map}_{\mathrm{cts}}(P,M)$ by $m\mapsto(g\mapsto gm)$. Book 7a, Section 9.1, shows that such coinduced modules are acyclic, so with $N=M^*/M$ the long exact sequence gives $H^q(P,M)\simeq H^{q-1}(P,N)$ for $q\ge2$; iterating lands in degree two, and $N$ is again $\ell$-primary. Hence $H^q(P,M)=0$ for all $q\ge2$.

Finally transfer this to $G$. Let $c\in H^q(G,M)$ with $q\ge2$; the group is $\ell$-primary because $M$ is. Its restriction to $P$ vanishes, and by the colimit description of $H^q(P,-)$ already used, its restriction to some open $H\supseteq P$ vanishes. For an open subgroup $H$ of index $m=[G:H]$, the module $M^\sharp=\operatorname{Map}_H(G,M)$ satisfies $H^q(G,M^\sharp)\simeq H^q(H,M)$ by Shapiro's lemma (Book 6, Section 4.8), and the two $G$-maps

$$
M\longrightarrow M^\sharp,\quad m\mapsto(g\mapsto gm),
\qquad
M^\sharp\longrightarrow M,\quad \varphi\mapsto\sum_{g\in H\backslash G}g^{-1}\varphi(g),
$$

compose to multiplication by $m$. Therefore multiplication by $m$ on $H^q(G,M)$ factors through $H^q(H,M)$, so $mc=0$. Since $m$ is prime to $\ell$ and $c$ is $\ell$-primary, $c=0$. $\square$

**Generic dimension theorem.** Let $k$ be algebraically closed of characteristic $p\ge0$ and let $K$ be a finitely generated extension of transcendence degree one. Then

$$
H^q(G_K,M)=0\qquad(q\ge2)
$$

for every torsion $G_K$-module $M$ whose order is prime to $p$.

**Proof.** It suffices to treat the $\ell$-primary part for each $\ell\ne p$. An open subgroup of $G_K$ is $G_L$ for a finite separable $L/K$, and $L$ is again a finitely generated extension of $k$ of transcendence degree one. The Kummer sequence for $\ell$, which is exact on $(L^s)^\times$ because $\ell$ is invertible, together with Hilbert 90 and Brauer vanishing over $L$, gives

$$
0=H^1(G_L,(L^s)^\times)\to H^2(G_L,\mu_\ell)\to H^2(G_L,(L^s)^\times)=0 .
$$

Since $k\subseteq L$ is algebraically closed, $\mu_\ell\simeq\mathbf Z/\ell$ as $G_L$-modules, so $H^2(G_L,\mathbf Z/\ell)=0$. The dimension-one lemma applies. $\square$

The same statement holds at the local fields that occur along a curve, and there it is even more elementary.

**Local dimension theorem.** Let $R$ be a strictly henselian discrete valuation ring with residue characteristic $p\ge0$ and fraction field $F$. Then $H^q(G_F,M)=0$ for every $q\ge2$ and every torsion $G_F$-module $M$ of order prime to $p$. Moreover $H^0$ is the inertia invariants and $H^1$ the coinvariants of a topological generator of tame inertia, so both are finite when $M$ is.

**Proof.** Book 17, Section 15.5, together with the classification of tamely ramified extensions of a henselian discretely valued field, identifies the tame quotient of $G_F$ with $\varprojlim_n\mu_n(\bar\kappa)$, procyclic of prime-to-$p$ order, the wild subgroup $P_F$ being pro-$p$. Cohomology of a pro-$p$ group with coefficients of order prime to $p$ vanishes in positive degrees, since on every finite $p$-group quotient the averaging idempotent is available (Book 7a, Section 9.3). The Hochschild--Serre sequence for $P_F\subseteq G_F$ therefore identifies $H^q(G_F,M)$ with $H^q(\widehat{\mathbf Z}^{(p')},M^{P_F})$. For a procyclic group and a finite module, $H^q$ is the colimit over the finite cyclic quotients. On a finite cyclic group the cohomology is periodic with period two, and inflation multiplies the degree-two periodicity class by the index ratio; hence in every degree at least two the transition maps of the colimit are multiplication by that ratio. Choosing quotients whose ratios are divisible by the exponent of the module makes these maps zero, so the colimit vanishes. Degrees zero and one are the invariants and coinvariants of a generator. $\square$

### 6.7 Cohomology of curves with torsion coefficients

We can now compute. Throughout this section $k$ is algebraically closed of characteristic $p\ge0$, $C$ is a smooth proper connected curve over $k$ of genus $g$, $D\subseteq C$ is a finite set of closed points with $r=\#D$, and $U=C\setminus D$; thus $U$ is proper when $r=0$ and affine when $r>0$. When $r>0$ the affineness is elementary: $U$ is the complement of a nonempty effective divisor on a projective curve, and a suitable power of $\mathcal O(D)$ is very ample by Book 9, Section 11.3, so $U$ is a standard affine open of a projective embedding. No general compactification theorem is used anywhere below: the smooth proper model is obtained by closure and normalization exactly as in Section 6.5.

Write $j:\eta\to U$ for the generic point and $K=k(C)$.

**Divisor sequence.** On $U_{\mathrm{\acute et}}$ there is an exact sequence

$$
1\longrightarrow\mathbf G_m
\longrightarrow j_*\mathbf G_{m,\eta}
\longrightarrow\bigoplus_{x\in U_0}i_{x*}\mathbf Z
\longrightarrow0,
$$

where $U_0$ is the set of closed points.

**Proof.** Exactness is checked on geometric stalks. At a geometric point over $x\in U_0$ the strict local ring $\mathcal O^{\mathrm{sh}}_{U,\bar x}$ is a strictly henselian discrete valuation ring, because $U$ is a regular one-dimensional scheme (Book 11, Proposition 4.2). The stalk of $j_*\mathbf G_m$ there is the multiplicative group of its fraction field, the stalk of $\mathbf G_m$ is its unit group, and the valuation identifies the quotient with $\mathbf Z$, which is the stalk of the skyscraper. At the generic geometric point the skyscraper vanishes and the first map is the identity of $(K^s)^\times$. $\square$

**Multiplicative theorem.** For $U$ as above,

$$
H^0(U,\mathbf G_m)=\mathcal O(U)^\times,\qquad
H^1(U,\mathbf G_m)=\operatorname{Pic}(U),\qquad
H^2(U,\mathbf G_m)=0 .
$$

**Proof.** A skyscraper at a closed point of a scheme over a separably closed field has vanishing higher cohomology, and since $U$ is noetherian, cohomology commutes with the filtered colimit defining the direct sum; so the third term of the divisor sequence has $H^0=\operatorname{Div}(U)$ and no higher cohomology. For the middle term, Leray for $j$ is degenerate in the relevant range: the stalk of $R^qj_*\mathbf G_m$ at a geometric point over $x$ is $H^q$ of the fraction field of $\mathcal O^{\mathrm{sh}}_{U,\bar x}$ with coefficients in $\mathbf G_m$, which vanishes for $q=1$ by Hilbert 90, while the stalk at the generic geometric point vanishes for $q\ge1$ because a separably closed field has trivial Galois group. Hence $R^1j_*\mathbf G_m=0$, and $R^qj_*\mathbf G_m$ is a skyscraper for $q\ge2$. Consequently the edge map gives $H^n(U,j_*\mathbf G_m)\hookrightarrow H^n(\eta,\mathbf G_m)$ for $n\le2$ with no interference from the higher rows, and $H^1(\eta,\mathbf G_m)=0$, $H^2(\eta,\mathbf G_m)=\operatorname{Br}(K)=0$ by Hilbert 90 and Brauer vanishing. The long exact sequence of the divisor sequence now reads

$$
1\to\mathcal O(U)^\times\to K^\times\to\operatorname{Div}(U)
\to H^1(U,\mathbf G_m)\to0,
\qquad
H^2(U,\mathbf G_m)\hookrightarrow H^2(U,j_*\mathbf G_m)=0 .
$$

The identification of $\operatorname{Div}(U)/\operatorname{Prin}(U)$ with $\operatorname{Pic}(U)$ on a regular integral curve is Book 9, Section 4.4. $\square$

This reproves, for curves, the identification of $H^1(\mathbf G_m)$ with $\operatorname{Pic}$ used in Section 3.4, and it is the only place where the Brauer group enters.

**Kummer theorem for curves.** Let $n$ be prime to $p$. Then

1. $H^0(U,\mu_n)=\mu_n(k)$ is cyclic of order $n$;
2. there is an exact sequence $0\to\mathcal O(U)^\times/n\to H^1(U,\mu_n)\to\operatorname{Pic}(U)[n]\to0$;
3. $H^2(U,\mu_n)\simeq\operatorname{Pic}(U)/n$, which is cyclic of order $n$ if $r=0$ and zero if $r>0$;
4. $H^q(U,\mu_n)=0$ for $q\ge3$.

All the groups are finite. If $M$ is an arbitrary constant finite abelian group of order prime to $p$, decompose it as a direct sum of cyclic groups $\mathbf Z/n_i$ and choose an identification $\mathbf Z/n_i\simeq\mu_{n_i}$ for each summand. Additivity then reduces $H^q(U,M)$ to the corresponding Kummer calculations. A single identification $\mathbf Z/n\simeq\mu_n$ applies only when the coefficient group is cyclic.

**Proof.** Parts 1--3 are the long exact sequence of the Kummer sequence of Section 3.4 combined with the multiplicative theorem; part 4 is the a priori bound proved below, whose proof does not use the present theorem. It remains to identify $\operatorname{Pic}(U)$ modulo $n$ and its $n$-torsion, and to see finiteness.

Since $k$ is algebraically closed, $C$ has a rational point, so Book 15, Section 10.3, applies and represents $\operatorname{Pic}^d_{C/k}$ by a smooth proper $k$-scheme; Section 10.4 identifies the identity component $J=\operatorname{Pic}^0_{C/k}$ as a smooth proper group scheme of dimension $g$, and over the point $\operatorname{Spec}k$ rigidification imposes no condition on isomorphism classes, so $J(k)=\operatorname{Pic}^0(C)$. On $J$ the differential of $[n]$ at the identity is multiplication by $n$ on the tangent space $H^1(C,\mathcal O_C)$, hence an isomorphism because $n$ is invertible; translating by points of $J$, the relation $[n]\circ t_a=t_{[n]a}\circ[n]$ shows that the differential is an isomorphism at every point, so $[n]$ is étale. It is proper and quasi-finite, hence finite; and its image is a closed subgroup of dimension $g$ in the connected group $J$, hence all of $J$. Therefore $J(k)$ is $n$-divisible and $J(k)[n]$ is finite.

Since the degree map is injective on torsion, $\operatorname{Pic}(C)[n]=J(k)[n]$, and $\operatorname{Pic}(C)/n\simeq\mathbf Z/n$ through the degree because $J(k)$ is divisible. Now let $r>0$ and choose $x_0\in D$. Restriction of divisors makes $\operatorname{Pic}(C)\to\operatorname{Pic}(U)$ surjective with kernel generated by the classes of the points of $D$; using $x_0$ to split off the degree, this identifies

$$
\operatorname{Pic}(U)\simeq J(k)/\Lambda,
\qquad
\Lambda=\text{image in }J(k)\text{ of the degree-zero divisors supported on }D,
$$

so $\Lambda$ is a quotient of $\mathbf Z^{r-1}$. Divisibility of $J(k)$ passes to the quotient, so $\operatorname{Pic}(U)/n=0$; and the snake lemma applied to $0\to\Lambda\to J(k)\to\operatorname{Pic}(U)\to0$ exhibits $\operatorname{Pic}(U)[n]$ as an extension of a subgroup of the finite group $\Lambda/n\Lambda$ by a quotient of $J(k)[n]$, hence finite. Finally $\mathcal O(U)^\times/k^\times$ injects into the free group of divisors supported on $D$, because a rational function with neither zeros nor poles on the proper curve $C$ is constant, and $k^\times$ is $n$-divisible; so $\mathcal O(U)^\times/n$ is finite, and vanishes when $r=0$. $\square$

The next statement is the a priori bound that makes every later dévissage terminate. It holds on proper and affine curves alike.

**A priori bound.** Let $U$ be as above and let $\mathcal F$ be a constructible sheaf of finite abelian groups of order prime to $p$. Then $H^q(U,\mathcal F)=0$ for $q\ge3$.

**Proof.** The canonical map $\mathcal F\to j_*j^*\mathcal F$ is an isomorphism on a dense open subset, so its kernel and cokernel are supported on finitely many closed points and have no positive cohomology; hence $H^q(U,\mathcal F)\simeq H^q(U,j_*G)$ for $q\ge2$, where $G=j^*\mathcal F$ is a finite $G_K$-module of order prime to $p$. In the Leray sequence for $j$ the stalks of $R^qj_*G$ at closed points are the Galois cohomology groups of the fraction fields of the strict local rings, so $R^qj_*G=0$ for $q\ge2$ by the local dimension theorem, and $R^1j_*G$ is a skyscraper, hence acyclic in positive degrees. The abutment is $H^n(\eta,G)=H^n(G_K,G)$, which vanishes for $n\ge2$ by the generic dimension theorem. For $n\ge3$ the only surviving term of total degree $n$ is $E_2^{n,0}=H^n(U,j_*G)$, and no differential can enter or leave it, so it equals the abutment and vanishes. $\square$

**Affine curve theorem.** Let $U$ be a smooth affine curve over $k$ and let $\mathcal F$ be a constructible sheaf of finite abelian groups of order prime to $p$. Then $H^q(U,\mathcal F)$ is finite for every $q$ and vanishes for $q\ge2$. If $C$ is a smooth proper curve, the same coefficients have finite cohomology, vanishing for $q\ge3$.

**Proof.** We first prove vanishing for $q\ge2$ on affine $U$, in three steps.

_Constant coefficients._ This is the Kummer theorem, part 3 with $r>0$ and part 4.

_Extension by zero of constant coefficients._ Let $j_V:V\hookrightarrow U$ be open with finite complement $Z$ and let $M$ be constant finite of order prime to $p$. The sequence $0\to j_{V!}M\to M_U\to i_{Z*}M\to0$ and the vanishing of $H^q(Z,M)$ for $q\ge1$ give $H^q(U,j_{V!}M)=0$ for $q\ge2$.

_Lisse coefficients and the trace._ Let $\mathcal L$ be lisse on $V$; treating the connected components separately we may assume $V$ connected. Let $\pi:V'\to V$ be a connected finite étale cover trivializing $\mathcal L$, so that $\pi^*\mathcal L=M$ is constant (Book 17). Let $U'$ be the normalization of $U$ in the function field of $V'$; it is finite over $U$ by the finite-normalization lemma for curves, hence affine, and it is normal, hence a smooth curve, and $\pi'^{-1}(V)=V'$ for the induced finite map $\pi':U'\to U$. Writing $j':V'\hookrightarrow U'$, comparison of stalks gives $\pi'_*j'_!=j_{V!}\pi_*$. The trace map $\pi_*\pi^*\mathcal L\to\mathcal L$, which étale-locally on $V$ is the sum over the finitely many sheets and descends by permutation invariance — the same construction as in Section 13.4 — is surjective on every geometric stalk; applying the exact functor $j_{V!}$ produces a surjection

$$
\mathcal A:=\pi'_*j'_!M=j_{V!}\pi_*\pi^*\mathcal L
\longrightarrow j_{V!}\mathcal L,
$$

with constructible kernel $\mathcal R$. Since $\pi'$ is finite, $H^q(U,\mathcal A)=H^q(U',j'_!M)$, which vanishes for $q\ge2$ by the previous step. The long exact sequence and the a priori bound give, for $q=2$,

$$
0=H^2(U,\mathcal A)\to H^2(U,j_{V!}\mathcal L)\to H^3(U,\mathcal R)=0 ,
$$

and the same argument in higher degrees, so $H^q(U,j_{V!}\mathcal L)=0$ for $q\ge2$.

For a general constructible $\mathcal F$, choose a dense open $V$ on which $\mathcal F$ is lisse; the sequence $0\to j_{V!}\mathcal F|_V\to\mathcal F\to i_{Z*}\mathcal F|_Z\to0$ has skyscraper right-hand term and reduces the assertion to the case just treated.

Finiteness now follows by descending induction on $q$, on affine and proper curves alike. For $q\ge3$ all the groups vanish. Suppose every constructible sheaf has finite cohomology in degree $q+1$. Given $\mathcal F$, the two displayed sequences reduce us to $\mathcal F=j_{V!}\mathcal L$ with $\mathcal L$ lisse, and there $H^q(U,\mathcal A)=H^q(U',j'_!M)$ is finite, because the sequence $0\to j'_!M\to M_{U'}\to i_*M\to0$ expresses it in terms of the finite groups of the Kummer theorem. The long exact sequence places $H^q(U,j_{V!}\mathcal L)$ between the finite group $H^q(U,\mathcal A)$ and the finite group $H^{q+1}(U,\mathcal R)$. $\square$

Two features of this proof deserve emphasis, because they are exactly the places where a shorter-looking argument would fail. Nothing here uses a presentation of the tame fundamental group of a punctured curve, and nothing asserts that a punctured curve is a $K(\pi,1)$; the finite covers enter only through the exact functor $\pi'_*$ and the trace map, both of which are elementary. The single global input is Tsen's theorem, and the single geometric input is that $\operatorname{Pic}^0$ of a proper curve is a proper smooth group scheme, which Book 15 constructs.

### 6.8 Rigidity, the see-saw lemma, and the order of $\operatorname{Pic}^0[n]$

The Kummer theorem computes the groups $H^q(U,\mu_n)$ in terms of $\operatorname{Pic}$, and proves them finite. It does not compute their orders, because the order of $\operatorname{Pic}^0(C)[n]$ is a statement about the Jacobian and not about cohomology. This section supplies the missing count. The see-saw lemma and the degree theorem below are independent of Sections 6.5 through 6.7, and no theorem of Chapter 7 depends on this section; its results are used for the rank statements of Sections 7.2 and 14.2 and for the abelian-scheme calculation of Section 15.2.

We begin with the tool that replaces every informal appeal to a see-saw principle in this book.

**See-saw lemma.** Let $T$ be a reduced noetherian scheme and let $h:X\to T$ be proper, flat and finitely presented with geometrically integral fibers, equipped with a section $e:T\to X$. Assume the fiber dimensions $\dim_{\kappa(t)}H^j(X_t,\mathcal O_{X_t})$ are locally constant in $t$ for every $j$. If $\mathcal L$ is a line bundle on $X$ whose restriction to $X_t$ is trivial for every $t\in T$, then

$$
\mathcal L\simeq h^*(e^*\mathcal L).
$$

In particular $\mathcal L$ is trivial when $e^*\mathcal L$ is.

**Proof.** For every $t$ we have $\mathcal L|_{X_t}\simeq\mathcal O_{X_t}$, so $\dim H^j(X_t,\mathcal L_t)=\dim H^j(X_t,\mathcal O_{X_t})$ is locally constant in $t$ for every $j$. The base is reduced, so the constant-rank corollary of Book 15, Section 5.4, applies: $h_*\mathcal L$ is finite locally free, of rank $h^0(X_t,\mathcal O_{X_t})=1$ because the fibers are proper and geometrically integral, and its formation commutes with arbitrary base change. The evaluation map $h^*h_*\mathcal L\to\mathcal L$ is therefore a map of line bundles whose restriction to $X_t$ is the map $H^0(X_t,\mathcal L_t)\otimes\mathcal O_{X_t}\to\mathcal L_t$ given by a trivializing section, which is nowhere zero. A map of line bundles that is surjective on every fiber is an isomorphism. Pulling back along $e$ identifies $h_*\mathcal L$ with $e^*\mathcal L$. $\square$

The hypothesis of constant fiber dimensions is satisfied in the two cases used here: smooth proper curves, by Book 15, Section 5.5, and abelian schemes, by the exterior algebra theorem of Book 15, Section 11.3. Reducedness cannot be dropped. On $X\times_k\operatorname{Spec}k[\varepsilon]$ a line bundle restricting trivially to the unique fiber and to the section is classified by $H^1(X,\mathcal O_X)$, which is nonzero as soon as $X$ has positive irregularity. This is why the lemma is stated for reduced parameter schemes and why the cube identity below is proved by rigidity rather than by iterated see-saw over an arbitrary base.

**Cube and square identities.** Let $A$ be a smooth proper connected group scheme over a field and let $L$ be a line bundle on $A$ rigidified at the identity. Then the alternating tensor product

$$
m_{123}^*L\otimes m_{12}^*L^{-1}\otimes m_{13}^*L^{-1}
\otimes m_{23}^*L^{-1}\otimes
\operatorname{pr}_1^*L\otimes\operatorname{pr}_2^*L\otimes\operatorname{pr}_3^*L
$$

on $A^3$ is trivial, and consequently $t_{a+b}^*L\otimes L\simeq t_a^*L\otimes t_b^*L$.

This is the cube lemma of Book 15, Section 11.2, together with the theorem of the square derived there. Its proof uses only properness, flatness, connectedness of the fibers, and the rigidity observation that a morphism from a proper connected scheme to the affine scheme of trivializations is constant; the projectivity that Book 15 includes in its definition of an abelian scheme is not used at this point. The see-saw lemma above is the form in which fiberwise triviality together with triviality along the identity section yields triviality, and it is what replaces, in Section 15.2, the appeal to a see-saw principle from a later book. Pulling the cube identity back along a triple of morphisms $(f,g,h):T\to A^3$ gives the identity in the form

$$
(f+g+h)^*L\otimes(f+g)^*L^{-1}\otimes(f+h)^*L^{-1}
\otimes(g+h)^*L^{-1}\otimes f^*L\otimes g^*L\otimes h^*L
\simeq\mathcal O_T .
$$

**Degree theorem.** Let $\kappa$ be an algebraically closed field, let $A$ be a smooth proper connected group scheme over $\kappa$ of dimension $g$, and assume that $A$ carries an ample line bundle. Let $m\ge1$ be prime to $\operatorname{char}\kappa$. Then $[m]:A\to A$ is finite étale of degree $m^{2g}$, and

$$
A[m](\kappa)\simeq(\mathbf Z/m\mathbf Z)^{2g}.
$$

**Proof.** As in the proof of the Kummer theorem, the differential of $[m]$ at the identity is multiplication by $m$ on the tangent space, hence invertible, and translation propagates this to every point; so $[m]$ is étale, and being proper and quasi-finite it is finite étale. Its degree $d$ is constant because $A$ is connected, and $[m]$ is surjective because its image is a closed subgroup of dimension $g$.

Let $L_0$ be ample and put $L=L_0\otimes[-1]^*L_0$, rigidified at the identity. It is ample, since $[-1]$ is an automorphism and a tensor product of ample bundles is ample, and it is symmetric. Applying the pulled-back cube identity to $(f,g,h)=([m],\mathrm{id},[-1])$ and using $[-1]^*L\simeq L$ gives

$$
[m+1]^*L\otimes[m-1]^*L\simeq([m]^*L)^{\otimes2}\otimes L^{\otimes2},
$$

and induction from $[0]^*L=\mathcal O$ and $[1]^*L=L$ yields $[m]^*L\simeq L^{\otimes m^2}$.

Now compare Hilbert polynomials with respect to $L$, in the sense of Book 8, Chapter 7. Being proper with an ample bundle, $A$ is projective (Book 8, Section 4.5), and being smooth and connected over an algebraically closed field it is integral. Write $P(t)=\chi(A,L^{\otimes t})$; by Book 8, Section 7.3, it has degree $g$ and leading coefficient $e/g!$ with $e=\deg_L(A)$ a positive integer. Because $[m]$ is finite, $[m]_*$ is exact and the projection formula gives

$$
\chi\bigl(A,([m]^*L)^{\otimes t}\bigr)
=\chi\bigl(A,[m]_*\mathcal O_A\otimes L^{\otimes t}\bigr),
$$

where $[m]_*\mathcal O_A$ is locally free of rank $d$. For a coherent sheaf $\mathcal F$ of generic rank $\rho$ on an integral projective variety of dimension $g$, the leading coefficient of its Hilbert polynomial is $\rho$ times that of the structure sheaf: choose $m_0$ with a map $\mathcal O(-m_0)^{\oplus\rho}\to\mathcal F$ that is an isomorphism at the generic point, note that its kernel and cokernel have support of dimension less than $g$, and use additivity of Hilbert polynomials (Book 8, Section 7.2) together with the degree statement of Section 7.3. Hence the right-hand side has leading coefficient $d\,e/g!$. On the other hand $[m]^*L\simeq L^{\otimes m^2}$, and replacing $L$ by $L^{\otimes m^2}$ replaces $P(t)$ by $P(m^2t)$ (Book 8, Section 7.4), whose leading coefficient is $m^{2g}e/g!$. Since $e>0$ we get $d=m^{2g}$.

Finally $A(\kappa)$ is divisible, being the group of $\kappa$-points of a connected group variety on which every $[m]$ prime to the characteristic is surjective, and $A[\ell^j](\kappa)$ has order $\ell^{2gj}$ for every $j$ and every $\ell\ne\operatorname{char}\kappa$. A divisible abelian $\ell$-primary group with $\ell^j$-torsion of order $\ell^{2gj}$ is isomorphic to $(\mathbf Q_\ell/\mathbf Z_\ell)^{2g}$, so $A[\ell^j](\kappa)\simeq(\mathbf Z/\ell^j)^{2g}$; the Chinese remainder theorem gives the statement for $m$. $\square$

The degree theorem is now reduced to its stated geometric hypotheses. To apply it to a Jacobian one still needs an ample line bundle. Book 15, Section 10.3, proves that $\operatorname{Pic}^d_{C/k}$ is smooth and proper; Book 8, Section 3.3, records that "proper implies projective" is false in general, so ampleness is a genuine further statement. For a curve of genus $g\ge1$, Book 17a, Section 8.2, constructs the theta divisor $\Theta$ on $J=\operatorname{Pic}^0_{C/k}$ by the determinant of cohomology, and Book 17a, Section 8.4, asserts that $\mathcal O(\Theta)$ is ample and induces a principal polarization. That argument uses divisor theory, determinantal cycles, and coherent cohomology rather than étale cohomology, so citing it here creates no circularity with the present calculation. Subject to that earlier theta-ampleness theorem, the Jacobian is projective in the sense required by the degree theorem and the following corollary applies.

**Torsion order corollary.** With $C$, $g$, $D$, $r$, $U$ and $n$ as in Section 6.7 and $n$ prime to $p$,

$$
\operatorname{Pic}^0(C)[n]\simeq(\mathbf Z/n)^{2g},
\qquad
H^1(C,\mu_n)\simeq(\mathbf Z/n)^{2g},
$$

and for $r>0$ the group $H^1(U,\mu_n)$ is free of rank $2g+r-1$ over $\mathbf Z/n$, while $H^0(U,\mu_n)=\mathbf Z/n$ and $H^q(U,\mu_n)=0$ for $q\ge2$.

**Proof.** The Jacobian is a smooth proper connected group scheme of dimension $g$, and for $g\ge1$ it carries the ample bundle $\mathcal O(\Theta)$ of Book 17a, Section 8.4, so the degree theorem applies and gives $J(k)[n]\simeq(\mathbf Z/n)^{2g}$; for $g=0$ the same isomorphism holds trivially. The Kummer theorem then gives $H^1(C,\mu_n)=\operatorname{Pic}(C)[n]=J(k)[n]$.

Let $r>0$. Keep the notation of the Kummer theorem: $\Lambda\subseteq J(k)$ is the image of the group $\operatorname{Div}^0_D\simeq\mathbf Z^{r-1}$ of degree-zero divisors supported on $D$, and $\operatorname{Pic}(U)=J(k)/\Lambda$. The kernel of $\operatorname{Div}^0_D\to J(k)$ consists of the principal divisors supported on $D$, so it is isomorphic to $\mathcal O(U)^\times/k^\times$; write $s$ for its rank and $\rho=r-1-s$ for the rank of $\Lambda$. Then $\mathcal O(U)^\times/n\simeq(\mathbf Z/n)^{s}$.

For the middle term, $\Lambda$ is finitely generated of rank $\rho$, so $|\Lambda/n\Lambda|=n^{\rho}\,|\Lambda[n]|$. Since $J(k)$ is $n$-divisible, the snake lemma applied to $0\to\Lambda\to J(k)\to\operatorname{Pic}(U)\to0$ gives an exact sequence

$$
0\to J(k)[n]/\Lambda[n]\to\operatorname{Pic}(U)[n]\to\Lambda/n\Lambda\to0,
$$

whence $|\operatorname{Pic}(U)[n]|=n^{2g}\,n^{\rho}$. Multiplying by $n^{s}$ through the Kummer sequence gives $|H^1(U,\mu_n)|=n^{2g+r-1}$.

Freeness is automatic. The group $\operatorname{Pic}(U)$ is divisible, being a quotient of the divisible group $J(k)$, and a divisible abelian group is a direct sum of copies of $\mathbf Q$ and of Prüfer groups; hence its $n$-torsion is a free $\mathbf Z/n$-module, necessarily of rank $2g+\rho$ by the order just computed. The Kummer sequence then presents $H^1(U,\mu_n)$ as an extension of the free module $\operatorname{Pic}(U)[n]$ by the free module $\mathcal O(U)^\times/n$. A free module over $\mathbf Z/n$ is projective, so the extension splits and $H^1(U,\mu_n)$ is free of rank $2g+r-1$. $\square$

The rank $2g+r-1$ is the same number that the classical presentation of the tame fundamental group of a punctured curve would predict. That presentation is not proved in this book and is not used anywhere in it; the number is obtained here from divisor theory and the degree of multiplication on the Jacobian.

## 7. Finiteness for constructible torsion coefficients

### 7.1 The finiteness theorem in the required range

Vanishing alone does not make inverse limits manageable. We also need every finite-level group to be finite.

**Finite-coefficient theorem.** Let $k$ be separably closed, let $X$ be separated of finite type over $k$ of dimension $d$, and let $\mathcal F$ be a constructible sheaf of finite $\ell$-primary modules, where $\ell\ne\operatorname{char}k$. Then every $H^q(X,\mathcal F)$ is finite and

$$
H^q(X,\mathcal F)=0\qquad(q>2d).
$$

If $X$ is affine, the sharper bound is $q>d$. Thus the theorem gives $[0,2]$ for proper curves, $[0,2g]$ for $g$-dimensional abelian varieties, and $[0,4]$ for surfaces. No properness or smoothness is needed for finiteness. In the applications, coefficients are constant, lisse finite free, or obtained from these by a finite stratification. In dimensions zero and one the proof below is complete as stated; in dimensions above one its vanishing half carries one explicitly flagged input, recorded in Section 7.2, while the finiteness mechanism is unconditional there.

### 7.2 The proof architecture

The proof has one geometric lemma and one gluing lemma. We give their proofs because neither finite monodromy nor the derived formalism alone implies finiteness. The geometric input that makes the induction step relative rather than fiberwise is the following theorem, which we prove first; it is the precise substitute for the informal appeal to spreading fiber data.

**Relative curve theorem.** Let $S$ be locally noetherian and excellent, let $n\ge1$ be invertible on $S$, and write $\Lambda_n=\mathbf Z/n\mathbf Z$.

1. Let $g:D\to S$ be smooth and proper whose geometric fibers are nonempty curves. Then for every lisse $\Lambda_n$-sheaf $\mathcal F$ on $D$,

$$
R^qg_*\mathcal F=0\quad(q\ge3),
$$

while $R^0g_*\mathcal F$ and $R^1g_*\mathcal F$ are lisse, and for every morphism of bases $T\to S$ the canonical base-change maps

$$
g^*R^qg_*\mathcal F\longrightarrow R^qg_{T*}\mathcal F_T
$$

are isomorphisms for every $q$.

2. Let $h:U\to S$ be a smooth affine relative curve admitting a realization $U=C\setminus D_0$, where $C\to S$ is as in 1. and $D_0\subseteq C$ is a relative effective Cartier divisor finite étale over $S$. Then for every lisse $\Lambda_n$-sheaf $\mathcal F$ on $U$, the sheaves $R^0h_*\mathcal F$ and $R^1h_*\mathcal F$ are lisse, their formation commutes with every base change, and

$$
(R^qh_*\mathcal F)_{\bar s}\cong H^q(U_{(\bar s)},\mathcal F)
\qquad\text{for all }q,
$$

so the higher direct images carry no information beyond what strict localizations see.

The excellence hypothesis is used exactly once, to guarantee finiteness of normalizations in step 2; in the application below the base is an affine variety over a field, where it holds automatically.

_Proof._ We proceed in four steps, then deduce 2.

**Step 1: constant coefficients with connected fibers.** Assume first $g:D\to S$ has geometrically connected fibers and $\mathcal F=M_U$ is the constant sheaf attached to a finite module $M$ killed by $n$, or the sheaf $\mu_n$. Since $g$ is proper, smooth, and has geometrically connected fibers, Book 15, Section 5.5 gives $g_*\mathcal O_D=\mathcal O_S$ after every base change, so $g_*M_U=M_S$ and, by the same argument on units, $g_*\mathbf G_m=\mathbf G_{m,S}$.

Consider the Kummer sequence of Section 3.4 on $D$ and push it forward. For its terms we need two identifications. First,

$$
R^1g_*\mathbf G_m\simeq \operatorname{Pic}_{D/S},
$$

where $\operatorname{Pic}_{D/S}$ is the fppf Picard sheaf of Book 17a. Both sides are sheaves on $S_{\mathrm{\acute et}}$, so it suffices to compare geometric stalks. The stalk of the right side at $\bar s$ is the colimit of $\operatorname{Pic}(D_V)$ over pointed étale neighborhoods $V$: a line bundle is given by finitely many transition functions on finitely many affines with finitely many cocycle identities, all of which descend through the filtered system, while Hilbert's theorem 90 identifies each $\operatorname{Pic}(D_V)$ with $H^1(D_V,\mathbf G_m)$. The stalk of the left side is computed by the strict-localization formula of Section 2.3 together with the same descent of line-bundle data through the colimit, giving the same group. Second, the degree map of Book 17a, Section 4.1, makes n-torsion classes have degree zero, because the degree is additive and $\mathbf Z$ is torsion-free; hence

$$
\ker\big(n:\operatorname{Pic}_{D/S}\to\operatorname{Pic}_{D/S}\big)
=\ker\big(n:J\to J\big)=J[n],
$$

with $J=\operatorname{Pic}^0_{D/S}$ the Jacobian, an abelian scheme by Book 17a, Section 4.3.

The multiplication-by-$n$ map $[n]$ on $J$ is finite étale and surjective. Its Lie differential is multiplication by $n$ on $\operatorname{Lie}(J)\simeq R^1g_*\mathcal O_D$, the identification (5.3) of Book 17a, Section 5.2; tensoring a first-order deformation given by transition functions $1+\epsilon a_{ij}$ with its $n$th power multiplies the cocycle class by $n$. Since $n$ is invertible on $S$, this differential is an isomorphism at every point, so $[n]$, being a morphism of smooth $S$-schemes with everywhere-invertible differential, is étale; it is proper and quasi-finite, hence finite, by the standard argument used in Books 8, 9, and 17; and its image is a closed subgroup meeting every geometric fiber in the whole fiber — over an algebraically closed field, $[n]:J_s\to J_s$ is surjective because its differential is invertible, $J_s$ is connected, and the image is closed of the same dimension as $J_s$ — so it is surjective as a map of fppf sheaves. A finite étale cover of a strictly henselian local scheme is a disjoint union of copies of that scheme, so $[n]$ remains surjective on sections over such rings; this will be used momentarily.

Now read off the long exact sequence of derived direct images:

$$
0\to\mathbf Z/n(1)_S\to R^1g_*\mu_n\to J[n]\to0,
$$

because $\operatorname{coker}(n:\mathbf G_{m,S}\to\mathbf G_{m,S})=\mathbf Z/n(1)$ by the Kummer sequence on $S$, because $R^0g_*\mu_n=\mu_n$, and because the next term is $\ker(n:\operatorname{Pic}_{D/S}\to\operatorname{Pic}_{D/S})=J[n]$. Both ends are lisse: $\mathbf Z/n(1)_S=\mu_n$ by definition, and $J[n]$ is the kernel of a finite étale homomorphism, hence finite étale locally free of rank equal to the genus of the geometric fibers. Lisse sheaves are closed under extensions (Section 3.1), so $R^1g_*\mu_n$ is lisse, and $R^1g_*M_U\simeq R^1g_*\mu_n$ after choosing a primitive root étale-locally on $S$; since local constancy descends along finite étale covers, $R^1g_*M_U$ is lisse of the same rank for any constant $M$.

Vanishing above degree two follows from stalks. By the finite-coefficient proper base change theorem of Section 4.6, applied to $g$ and to the geometric point $\bar s$,

$$
(R^qg_*M_U)_{\bar s}=H^q(D_{\bar s},M),
$$

and the fiber computations of Section 6.7 give $H^q(D_{\bar s},M)=0$ for $q\ge3$. Hence $R^qg_*M_U=0$ there.

The sheaf $R^2g_*M_U$ deserves a separate remark. Its geometric stalks are $H^2(D_{\bar s},M)$, which by Section 6.7 is cyclic of order $n$ for $M=\mu_n$ and vanishes in the affine situation, so the stalk values are known. Identifying the sheaf itself with $\mathbf Z/n(1)_S$, or proving that it is lisse, would require showing that the boundary map $R^2g_*\mu_n\to R^2g_*\mathbf G_m$ of the Kummer sequence into the relative Brauer term carries no additional information; the relative Brauer sheaf $R^2g_*\mathbf G_m$ is not analyzed in this book, and no result below uses more about $R^2g_*M_U$ than its stalks. The same applies to the higher direct images with general constant coefficients. This is the one point where the relative theory developed here is deliberately narrower than what the fiberwise computations of Section 6.7 would suggest.

**Step 2: constant coefficients, general fibers.** Drop geometric connectedness. The function $s\mapsto\#\pi_0(D_s)$ is locally constant: $g_*\mathcal O_D$ is locally free by cohomology and base change, Book 15, Sections 5.2 and 5.5, since $h^0$ equals the number of components on every geometric fiber, and its spectrum $T\to S$ is finite étale because its fibers are split algebras $\kappa(s)^r$. Over $T$ the idempotents are defined and decompose

$$
D_T=\coprod_{j}D_j,
$$

with each $D_j\to T$ smooth, proper, and with geometrically connected fibers. Cohomology converts disjoint unions into products, so

$$
R^q(g_T)_*(M) = \prod_j R^qg_{j*}(M),
$$

lisse by Step 1. The canonical restriction map $(R^qg_*M)|_T\to R^q(g_T)_*M$ is an isomorphism: both sides have the same stalks at geometric points of $T$, namely $H^q(D_{\bar t},M)$, the left side by Section 4.6 applied to $g$, the right side by Step 1. A sheaf that becomes lisse after pullback by the finite étale cover $T\to S$ is lisse, because a trivializing étale cover of $T$ composed with $T\to S$ trivializes it over $S$. This proves the constant-coefficient case of 1.

**Step 3: lisse coefficients.** Let $\mathcal F$ be a lisse $\Lambda_n$-sheaf on $D$, and choose a finite étale cover $\pi:D'\to D$ trivializing it, $\pi^*\mathcal F=M$. The adjunction unit gives an injection of lisse sheaves

$$
0\to\mathcal F\longrightarrow\pi_*M,
$$

injective because $\pi$ is surjective and restriction to geometric fibers detects zero sections; its cokernel $\mathcal C'$ is again lisse, and $R^qg_*(\pi_*M)=R^q(g\circ\pi)_*M$ falls under Step 2. The long exact sequence shows that $R^0g_*\mathcal F$ is the kernel of a map between lisse sheaves and that $R^1g_*\mathcal F$ is an extension whose outer terms are kernels and cokernels of maps between lisse sheaves:

$$
0\to R^0g_*\mathcal F\to R^0g_*\pi_*M\to R^0g_*\mathcal C',
$$

$$
0\to\operatorname{coker}(R^0g_*\pi_*M\to R^0g_*\mathcal C')
\to R^1g_*\mathcal F
\to \ker(R^1g_*\pi_*M\to R^1g_*\mathcal C')\to0 .
$$

Since lisse sheaves are closed under kernels, cokernels, and extensions, $R^0g_*\mathcal F$ and $R^1g_*\mathcal F$ are lisse.

For the vanishing and the base-change assertion no such construction is needed. Every $\mathcal F$ as above is constructible of finite modules, so Section 4.6 applies directly:

$$
(R^qg_*\mathcal F)_{\bar s}=H^q(D_{\bar s},\mathcal F),
$$

which vanishes for $q\ge3$ by the fiber computations of Section 6.7, extended from constant to lisse coefficients by the same trace-and-sequence argument used there. This proves 1.

**Step 4: base change.** Let $T\to S$ be arbitrary. A map of sheaves is an isomorphism if and only if it is an isomorphism on all geometric stalks, so it suffices to compare

$$
(R^qg_*\mathcal F)_{\bar s}
\qquad\text{and}\qquad
(R^qg_{T*}\mathcal F_T)_{\bar t}.
$$

By Section 4.6 these are $H^q(D_{\bar s},\mathcal F)$ and $H^q(D_{T,(t)},\mathcal F_T)$ respectively, and applying Section 4.6 to $g_T$ rewrites the latter as $H^q(D_{\bar t},\mathcal F_T)$. The fields $\kappa(\bar s)\subseteq\kappa(\bar t)$ are algebraically closed, and $D_{\bar t}=\varprojlim_i D_i$ over the filtered system of models of $D_{\bar s}$ over finitely generated subfields of $\kappa(\bar s)$, base-changed along intermediate extensions; the transitions are affine, being morphisms of spectra of fields, so the Continuity theorem of Section 4.6 applies and exhibits both groups as colimits over a common cofinal subsystem, compatibly with the base-change map. Hence the map is an isomorphism on all geometric stalks.

**Proof of 2.** Let $h:U=C\setminus D_0\to S$ as in 2., write $f:C\to S$ for the compactification morphism, with $j:U\hookrightarrow C$ and $i:D_0\hookrightarrow C$, and first take $\mathcal F=M_U$ constant. The two short exact sequences of sheaves on $C$,

$$
0\to j_!M_U\to M_C\to i_*M_{D_0}\to0,
\qquad
0\to j_!M_U\to j_*M_U\to i_*Q\to0,
$$

hold with $Q=i^*j_*M_U=M_{D_0}$, the last identification because a punctured strictly henselian disk carries no nonconstant locally constant functions. Pushing forward to $S$ and using that $R^mg_{0*}M_{D_0}=0$ for $m>0$, where $g_0:D_0\to S$ is finite étale, the first sequence determines $R^mf_*j_!M_U$: for $m\ge2$ it is isomorphic to $R^mg_*M_C$, both flanking terms of the sequence vanishing; for $m=1$ it is the cokernel of $R^0(g_0)_*M_{D_0}\to R^1g_*M_C$, hence lisse; for $m=0$ it is the kernel of $f_*M_C\to(g_0)_*M_{D_0}$, hence lisse. The second sequence then gives

$$
R^0h_*M_U:\quad
0\to R^0f_*j_!M_U\to R^0h_*M_U\to g_{0*}M_{D_0},
$$

so $R^0h_*M_U$ is lisse as an extension whose outer terms are lisse, and

$$
R^1h_*M_U\simeq\operatorname{coker}\big((g_0)_*M_{D_0}\to R^1f_*j_!M_U\big),
$$

lisse for the same reason. This proves 2. for constant coefficients. For lisse $\mathcal F$ one first realizes the trivializing cover: if $\pi:U'\to U$ is finite étale, let $C'$ be the normalization of $C$ in it. Excellence makes $C'\to C$ finite; $C$ being a regular one-dimensional scheme, $C'$ is finite flat over $C$, being Cohen--Macaulay over a regular base of dimension one; hence $C'\to S$ is flat and finitely presented, proper because finite over $C$, and its geometric fibers are normal curves over algebraically closed fields, hence regular and therefore smooth. Writing $D_0'=C'\times_CD_0$, which is finite étale over $S$, realizes $U'=C'\setminus D_0'$ as required by 2. Now insert

$$
0\to\mathcal F\to\pi_*M\to\mathcal C'\to0
$$

on $U$ and read off from the resulting long exact sequences, using that $R^qh_*(\pi_*M)=R^q(h\circ\pi)_*M$ and that $h\circ\pi$ satisfies the hypotheses of 2., that $R^0h_*\mathcal F$ is a kernel and $R^1h_*\mathcal F$ an extension of kernels and cokernels of maps between lisse sheaves.

The base-change assertion for 2. in degrees zero and one follows from the stalk formula just stated together with Step 4's identification argument, which never used properness of the morphism being pushed forward: the strict-localization formula of Section 2.3 holds for every quasi-compact quasi-separated morphism, and the field-extension comparison is again a Continuity-theorem computation over affine transition systems, now modeling the affine curve $U_{\bar t}$. What the nonproperness does prevent is any vanishing statement beyond what stalks give: unlike the situation over a field, where Section 6.7 shows $H^2=0$ on affine curves, the sheaves $R^qh_*\mathcal F$ for $q\ge2$ need not vanish even for constant coefficients, because their stalks are computed on total spaces over strictly henselian rings rather than on fibers; no result below uses them. $\square$

The ranks delivered by the theorem are worth recording, because later books quote them. If the geometric fibers of $g$ have genus $g_0$ and $\mathcal F$ is constant of rank $r$ on connected fibers occurring with multiplicity $\#\pi_0$, then $R^0g_*\mathcal F$ has rank $r\cdot\#\pi_0$ and $R^1g_*\mathcal F$ has rank $(2g_0+r-1)\cdot\#\pi_0$ after a choice of root of unity identifies the coefficients; the stalks of $R^2g_*(\mu_n)$ are cyclic of order $n$. For the affine curve of 2. with $e\ge1$ boundary points per fiber, $R^1h_*(\mu_n)$ has stalk-rank $2g_0+e-1$, matching Section 6.8's count.

**Affine constructible lemma.** If $U$ is affine of finite type of dimension $d$ over $k$, then, for every constructible finite $\ell$-primary sheaf $\mathcal F$,

$$
H^q(U,\mathcal F)=0\quad(q>d),
$$

and every group in the remaining range is finite.

**Proof.** We argue simultaneously by dimension and noetherian induction on the support. The assertion is immediate in dimension zero: the reduced support is a finite set of spectra of finite purely inseparable extensions of $k$, hence has the same étale topos as a finite set of separably closed points.

The curve step is Section 6.7 and needs no separate argument here. In dimension one, let $U$ be an affine curve of finite type over $k$. Its étale site is that of its reduction, and its finitely many irreducible components may be separated by a sheaf sequence supported at the finitely many crossing points, so we may assume $U$ integral. Let $\nu:\widetilde U\to U$ be its normalization, finite by the finite-normalization lemma for curves of Book 8, Section 9.1. The kernel and cokernel of $\mathcal F\to\nu_*\nu^*\mathcal F$ are supported on the finitely many nonnormal points; finite direct image is exact and a sheaf supported at finitely many closed points has no positive cohomology, so the long exact sequence reduces the assertion to $\widetilde U$, which is affine and, being normal of dimension one over a field we may take algebraically closed by the reduction of Section 6.5, smooth. The affine curve theorem of Section 6.7 now gives finiteness in every degree and vanishing above degree one, for every constructible sheaf of finite $\ell$-primary modules. This proves the lemma in dimension one.

It is worth being explicit about the route that has been avoided, since it is the one a reader is likely to expect. One would like to say that the prime-to-characteristic tame fundamental group of a punctured curve has a presentation on $2g+r$ generators with a single relation, and that finite torsors compute the étale cohomology of $U$, that is, that a punctured curve is a $K(\pi,1)$. The presentation is a genuine theorem, but its known proofs pass through the Riemann existence theorem and are unavailable in an algebraic development; the $K(\pi,1)$ property is a further theorem and not a formal consequence of covering theory. Neither statement is proved in this book, and neither is used in it. What the calculation of Section 6.7 supplies instead is the same numerical output where it is needed: by the torsion order corollary of Section 6.8 the group $H^1(U,\mu_n)$ is free of rank $2g+r-1$ over $\mathbf Z/n$ for a smooth affine $U=C\setminus D$ with $r=\#D>0$, and $H^q(U,\mu_n)=0$ for $q\ge2$; the vanishing and finiteness statements used in the present proof do not even need that count.

For the induction step in dimension at least two, first refine the constructibility stratification and replace the support by one irreducible stratum. After removing a smaller closed subset, the stratum is smooth and the sheaf is lisse. A generic linear projection, after shrinking source and target, gives an elementary affine-curve fibration

$$
U^\circ\xrightarrow{f}V
$$

with $V$ affine of dimension $d-1$: there is a smooth proper relative curve $\overline U^\circ\to V$ containing $U^\circ$, and the complement is finite over $V$. To obtain it, choose a separating transcendence basis for the smooth function field and realize $d-1$ of its elements as sufficiently general linear projections on an affine embedding. The generic fiber is then a smooth curve; openness of the smooth locus gives a smooth morphism after deleting the discriminant. Normalizing the projective closure and deleting the nonflat locus makes the boundary finite; deleting its branch locus makes it étale. This argument remains valid over an imperfect separably closed field because the chosen basis is separating. Every deletion has smaller-dimensional complement and is handled by noetherian induction.

We need the relative curve calculation only for this elementary fibration, and it is now supplied by the relative curve theorem: after the shrink just performed, $\overline U^\circ\to V$ is smooth and proper with geometrically nonempty curve fibers and its complement is finite étale over $V$, so assertion 2. applies to $f:U^\circ\to V$ and to the lisse sheaf $\mathcal F$. It follows that $R^0f_*\mathcal F$ and $R^1f_*\mathcal F$ are lisse — in particular constructible and finite — and that their formation commutes with every base change; on geometric stalks they compute the fiberwise groups of Section 6.7, concentrated in degrees zero and one. The boundary mechanism behind these two sheaves is worth recording even though the theorem makes its explicit description unnecessary: at a boundary branch the strict-local group is an extension of wild inertia by a procyclic tame group; wild inertia is pro-$p$ and acts through finite $\ell$-primary quotients of order prime to $p$, so averaging by the inverse of the group order splits invariants, while the remaining tame cochains are represented by a two-term complex $M\xrightarrow{\tau-1}M$. Descent along the finite trivializing cover is retained inside these complexes rather than replaced by the generally unbounded groups $H^a(G,-)$. The same construction with extension by zero handles a locally closed stratum: the missing sections simply impose zero in the corresponding local term. This is the only step of the proof that is relative rather than fiberwise; the one-dimensional case established above uses nothing of the kind.

**Status of the higher rows.** Assertion 2. controls exactly the rows zero and one, together with the stalk values of every row, and this book does not prove more. The remaining rows cannot be dismissed: for constant coefficients the sheaf $R^2f_*\mathcal F$ need not vanish when the base has dimension at least one, because its stalks are computed on total spaces over strictly henselian rings rather than on fibers, and the torus-like elementary fibrations show that nonzero monodromic lisse sheaves can occur there. Consequently the finiteness half of the affine lemma closes as soon as the abutment receives only finitely many finite rows — which the theorem supplies for rows zero and one and which the induction on $\dim V$ must supply for any surviving higher rows — while the vanishing half, as executed below, rests on the supplementary vanishing of the total-degree-$d+1$ contribution from such rows. For the applications in this book, which are made over separably closed ground fields with the fibrations produced by linear projection, this supplementary vanishing holds in the cases used; a proof independent of case checks belongs to the general theory of the next book, where it follows from proper base change and local acyclicity. We flag it here rather than conceal it: within this book, the vanishing statement of Section 7.1 in dimensions above one carries this explicitly conditional input, while the finiteness statement and everything proved in dimensions zero and one are unconditional.

In the Leray sequence for $f$, the rows zero and one are the lisse sheaves just produced; their terms are finite by the induction hypothesis on $\dim V$ applied over the affine base $V$, and they vanish when $a>d-1$. With the supplementary vanishing flagged above in force, no higher row contributes to a total degree above $d$, and none contributes at all to the range where Section 6.7's fiber bounds already control the abutment; hence $H^{a+b}(U^\circ,\mathcal F)$ vanishes above $d$ and is finite. This is the form in which the lemma is used below. The kernel and cokernel of the map from the extension by zero on $U^\circ$ to the original sheaf are supported on the deleted closed subset. The localization long exact sequence and noetherian induction transfer the same assertions to $U$. This closes both inductions. $\square$

The proof also explains the prime-to-characteristic hypothesis. It is exactly what makes wild-inertia invariants exact and leaves a length-one tame local complex. It explains the uniformity in the exponent as well: for a fixed stratification and fixed ranks, the same finite Čech and inertia complexes work for every $\Lambda_n$.

It is worth recording where the weight of the argument now lies. For curves the affine lemma is proved outright in Section 6.7, from Tsen's theorem and the divisor sequence, with no fundamental-group presentation, no $K(\pi,1)$ assertion and no base-change theorem. In dimension at least two the elementary fibration carries the induction, and its rows zero and one are controlled by the relative curve theorem proved at the head of this section: that theorem is what makes the fiberwise curve computation and the strict-localization computation agree, and it is proved here from the cohomological descent and continuity results of Sections 4.5 and 4.6 together with Book 17a's relative Picard construction. The general adic and smooth-morphism base-change statements remain in the next book; what is used and proved here is exactly their finite-coefficient shadow for relative curves. A reader tracking hypotheses should therefore treat the curve case as unconditional and the higher-dimensional vanishing as carrying one explicitly flagged input.

We pass from affine to separated schemes without assuming quasi-projectivity. A separated noetherian space of dimension $d$ has a finite affine refinement of order at most $d+1$, meaning that no nonempty intersection uses more than $d+1$ members. Construct such a refinement by induction on dimension: choose disjoint affine neighborhoods of the finitely many generic points, remove their closed complement, and refine that complement, whose dimension is smaller; shrinking the new affine neighborhoods away from the previously chosen closed pieces preserves the asserted order. Separatedness makes every finite intersection affine.

For such a cover $\mathfrak U$, cohomological descent gives

$$
E_1^{a,b}=
\prod_{i_0<\cdots<i_a}
H^b(U_{i_0}\cap\cdots\cap U_{i_a},\mathcal F)
\Longrightarrow H^{a+b}(X,\mathcal F).
$$

Every product is finite. The affine lemma gives $b\le d$, while the order of the cover gives $a\le d$. Thus the abutment is finite and zero above $2d$. This proves the finite-coefficient theorem. Notice that the argument uses a Čech-to-derived spectral sequence, not the ordinary Čech complex of one allegedly acyclic cover.

### 7.3 Uniformity in the exponent

For passage to $\mathbf Z_\ell$, finiteness must be compatible as $n$ varies. Suppose $(\mathcal F_n)$ is a constructible system on a common finite stratification, with bounded ranks and compatible derived reduction. The preceding dimension bounds are independent of $n$. Each $H^q(X,\mathcal F_n)$ is finite, and the transition maps form an inverse system of finite groups. For fixed $n$, the descending sequence of images

$$
\operatorname{im}(H^q(X,\mathcal F_m)\to H^q(X,\mathcal F_n)),
\qquad m\ge n,
$$

stabilizes because the target is finite. Thus every such tower is Mittag--Leffler, even when its transition maps are not surjective.

This argument is stronger than a careless appeal to coefficient surjectivity. A surjection $\mathcal F_{n+1}\to\mathcal F_n$ need not induce a surjection on $H^q$; the connecting map into $H^{q+1}$ can obstruct lifting. Finiteness of the target, not exactness of cohomology, supplies Mittag--Leffler.

There is a second, stronger uniform statement used for perfectness. Anticipating the systematic treatment in Chapter 9, call $K=(K_n)$ normalized when, for $K_\infty=R\varprojlim K_n$ in the derived category of étale $\Lambda$-module sheaves, every canonical reduction map is an isomorphism. Thus

$$
K_n\simeq K_\infty\otimes^L_\Lambda\Lambda_n.
$$

Derived global sections preserve derived inverse limits. Moreover, $\Lambda_n$ is represented over $\Lambda$ by the two-term finite free complex $[\Lambda\xrightarrow{\ell^n}\Lambda]$. Tensoring with this complex uses only finite direct sums and a cone, all of which commute with derived global sections. Therefore

$$
\left(R\varprojlim_mR\Gamma(X,K_m)\right)
\otimes^L_\Lambda\Lambda_n
\simeq R\Gamma(X,K_n). \tag{7.1}
$$

This proves finite-level reduction before perfectness is invoked; there is no circular appeal to a bounded free representative. In particular, reduction modulo $\ell$ of the continuous complex is bounded with finite-dimensional cohomology by the finite-coefficient theorem.

We shall use the following complete-DVR lemma. If $C$ is derived $\ell$-complete and $C\otimes^L_\Lambda\Lambda_1$ is a bounded complex with finite-dimensional cohomology, then $C$ is perfect over $\Lambda$. To prove it, choose a minimal free resolution of $C$: lift a basis of the mod-$\ell$ cocycles degree by degree and remove every differential entry that is a unit by a contractible two-term summand. The remaining differentials lie in $\ell\Lambda$. Reduction of this minimal complex has zero differential, so its term in degree $i$ has rank $\dim H^i(C\otimes^L\Lambda_1)$. Those dimensions are finite and vanish outside a finite interval. The minimal resolution is therefore a bounded complex of finite free modules. Derived completeness excludes an additional complex on which multiplication by $\ell$ is invertible, since such a complex has zero derived completion. This proves the lemma and, together with (7.1), the integral perfectness statements below.

### 7.4 What fails without the hypotheses

If $X$ is not of finite type, infinitely many components can already make $H^0(X,\Lambda_1)$ infinite. If coefficients are not constructible, a product of skyscraper sheaves at infinitely many closed points has infinite global sections even on a noetherian curve. If $\ell$ is not invertible, wild ramification invalidates the prime-to-characteristic dimension and purity arguments.

Properness is not required for finite cohomology of constructible prime-to-characteristic sheaves on a finite-type scheme, but it becomes crucial for the cleanest relative statements and for ordinary cohomology to behave like a fiberwise invariant. Open varieties also carry boundary information, and ordinary cohomology does not alone remember compact support.

Finally, finiteness at every level does not identify the inverse limit with completed cohomology automatically. It kills $\varprojlim^1$ for the tower of finite cohomology groups, but derived tensor and compatibility of the coefficient system must still be checked. Those are distinct issues.

## 8. Towers of coefficients

### 8.1 Adic systems

An integral $\ell$-adic coefficient object should remember all reductions at once. A strict lisse $\Lambda$-system is a tower $(\mathcal F_n)_{n\ge1}$ with each $\mathcal F_n$ lisse finite free over $\Lambda_n$ and specified isomorphisms

$$
\mathcal F_{n+1}\otimes_{\Lambda_{n+1}}\Lambda_n
\xrightarrow{\sim}\mathcal F_n
$$

satisfying transitivity. Its stalk is the profinite module

$$
\mathcal F_{\bar x}=\varprojlim_n(\mathcal F_n)_{\bar x},
$$

finite free over $\Lambda$ and equipped with a continuous fundamental-group action. Conversely, reducing a continuous action on a finite free $\Lambda$-module produces such a system.

For complexes the underived condition is too rigid. The correct compatibility is

$$
\Lambda_n\otimes^L_{\Lambda_{n+1}}K_{n+1}
\xrightarrow{\sim}K_n.
$$

It allows cohomology sheaves to contain torsion while insisting that the derived object really is one integral object seen modulo successive powers of $\ell$.

### 8.2 Naive limits are not the definition

The ordinary inverse-limit sheaf $\varprojlim\mathcal F_n$ exists, but it lives among sheaves of abstract $\Lambda$-modules and can forget the topology that makes monodromy continuous. Worse, inverse limit is left exact rather than exact. Taking it before cohomology can therefore destroy extension information.

Even when the tower consists of constant sheaves, the two expressions

$$
H^q\left(X,\varprojlim_n\mathcal F_n\right)
\quad\text{and}\quad
\varprojlim_nH^q(X,\mathcal F_n)
$$

need not agree. The first treats the limit as an ordinary sheaf; the second ignores derived-limit corrections. Neither is the definition of continuous cohomology. They agree with it only after explicit acyclicity and Mittag--Leffler arguments.

There is also a categorical mismatch. A locally constant sheaf of abstract $\mathbf Z_\ell$-modules on the ordinary étale site has discrete stalk topology. A continuous representation on a finite free $\mathbf Z_\ell$-module usually has infinite compact image and is not locally constant for that discrete topology. The compatible finite quotients, not the abstract limit sheaf, encode the intended continuity.

### 8.3 Derived inverse limits

For a tower of complexes

$$
K_1\longleftarrow K_2\longleftarrow K_3\longleftarrow\cdots,
$$

the derived inverse limit can be represented by the shifted cone

$$
R\varprojlim_nK_n
=\operatorname{Cone}\left(
\prod_nK_n\xrightarrow{1-T}\prod_nK_n
\right)[-1],
$$

where $T((x_n))=(f_{n+1}(x_{n+1}))$. Products are taken degreewise after choosing suitable replacements. The formula shows that for countable towers only $\varprojlim$ and $\varprojlim^1$ occur.

Taking cohomology gives the Milnor exact sequence

$$
0\longrightarrow
\varprojlim_n{}^1 H^{q-1}(K_n)
\longrightarrow H^q(R\varprojlim_nK_n)
\longrightarrow\varprojlim_nH^q(K_n)
\longrightarrow0.
$$

It is natural but not canonically split. A first derived limit is therefore not an error term that may be dropped by convention; it is actual cohomology one degree higher.

For a concrete warning, take the tower

$$
\mathbf Z\xleftarrow{2}\mathbf Z\xleftarrow{2}\mathbf Z\xleftarrow{2}\cdots.
$$

Its ordinary inverse limit is zero, while its first derived limit is nonzero; it may be identified with $\mathbf Z_2/\mathbf Z$. Placing this tower in degree zero produces a derived inverse limit with nonzero $H^1$. Thus a tower can have zero ordinary limit and still carry completed derived information.

### 8.4 The Mittag--Leffler mechanism

A tower $(A_n)$ is Mittag--Leffler if for every $n$ the images of $A_m\to A_n$ stabilize for large $m$. Surjective transition maps imply the condition. Towers of finite groups satisfy it because a descending chain of subgroups of a finite target stabilizes.

For a countable Mittag--Leffler tower,

$$
\varprojlim_n{}^1A_n=0.
$$

To see the decisive step, solve $(1-T)(x)=y$ recursively. Stabilized images let one choose a compatible tail correction at each stage; diagonal selection produces $x$ with the prescribed discrepancy $y$. Surjectivity of $1-T$ is exactly vanishing of its cokernel, which is $\varprojlim^1$.

Applied to Section 7, this gives

$$
H^q\left(R\varprojlim_nR\Gamma(X,\mathcal F_n)\right)
\cong\varprojlim_nH^q(X,\mathcal F_n)
$$

for constructible finite systems on the required finite-type schemes. The derived definition remains essential: it is what makes this equality a theorem with visible hypotheses rather than an implicit assumption.

## 9. The adic derived category

### 9.1 Normalized systems

Strict towers are convenient for lisse lattices but are not stable enough under cones and derived functors. Let $\Lambda_\bullet=(\Lambda_n)$ be the coefficient tower. For a system $K=(K_n)$ of complexes, form its derived inverse limit $R\varprojlim K_n$ as a complex of $\Lambda$-modules and then reduce it back to every level. The resulting **normalization** is

$$
\widehat K_n
=\Lambda_n\otimes^L_\Lambda R\varprojlim_mK_m.
$$

There is a natural map $\widehat K\to K$. A system is **normalized** if this map is an isomorphism at every level in the derived sense. Equivalently in the bounded constructible situations used here, the transition maps satisfy derived reduction and the tower is derived complete.

Normalization solves two problems at once. It rules out towers carrying spurious information that disappears under completion, and it makes reduction from an integral complex canonical. If $P$ is a bounded complex of finite free $\Lambda$-modules, then $(P\otimes^L\Lambda_n)_n$ is normalized and its inverse limit recovers $P$.

An underived compatible tower of flat lisse sheaves is automatically normalized. A tower of arbitrary cohomology sheaves need not be: Tor from the next degree can enter reduction, exactly as the universal-coefficient sequence predicts.

### 9.2 Essentially zero systems

A system $(M_n)$ is **essentially zero**, or pro-zero, if for every $n$ there is $m\ge n$ such that the transition $M_m\to M_n$ is zero. It is **Artin--Rees null** if there is one integer $r\ge0$ such that $M_{n+r}\to M_n$ is zero for every $n$. For sheaves, the latter condition is imposed locally on $X$; on a fixed finite constructibility stratification one chooses $r$ uniformly on each stratum. Artin--Rees null implies essentially zero, but the converse need not provide a uniform shift. Such towers can have nonzero terms at every level while carrying no persistent adic information.

For example, let $M_n=\Lambda_1$ and make every transition zero. The ordinary product of the levels is enormous, but every fixed level is killed from the next one. Treating this tower as a genuine integral sheaf would make the answer depend on irrelevant presentation data.

A complex of systems is **Artin--Rees null in cohomology** if each cohomology system is locally Artin--Rees null. These complexes form a thick triangulated subcategory: the long exact cohomology sequence shows stability under cones after adding the two uniform shifts, and finite direct summands preserve the condition. Merely pro-zero systems are useful for diagnosing ordinary limits, but the uniform Artin--Rees condition is the one used in the localization below.

### 9.3 The Ekedahl-style viewpoint

The robust adic derived category is obtained in two conceptual steps. Begin with the derived category of inverse systems of $\Lambda_n$-sheaves. Then take the Verdier quotient by complexes whose cohomology systems are Artin--Rees null, and retain the normalized constructible objects. Morphisms whose cones differ only by a uniformly vanishing finite-level artifact become isomorphisms.

This **Ekedahl-style category** is necessary when one wants all six-operation constructions on constructible adic complexes or when strict transition maps are unavailable. It is not the same as the derived category of ordinary $\Lambda$-module sheaves. Its objects remember a topology through their finite quotients, and its localization removes pro-zero noise before normalization.

Three notions should therefore remain distinct:

1. the ordinary inverse-limit sheaf $\varprojlim\mathcal F_n$;
2. a strict compatible system $(\mathcal F_n)$ with specified reduction maps;
3. the normalized object represented by that system in the localized adic derived category.

They agree for finite free lisse towers under the finiteness hypotheses already proved. They need not agree for arbitrary constructible complexes. Invoking the adic category is not permission to suppress $R\varprojlim$; rather, it organizes exactly when $R\varprojlim$ and reduction behave as expected.

### 9.4 When elementary towers suffice

Most geometric representations in this book arise from a strict lisse lattice $(\mathcal F_n)$ on a finite-type scheme. Its finite-level cohomology groups are finite, the towers are Mittag--Leffler, and the cohomological range is uniform. In that setting one may define everything directly through

$$
R\varprojlim_nR\Gamma(X,\mathcal F_n)
$$

without constructing the entire localized category.

The larger viewpoint becomes indispensable for cones of morphisms between adic sheaves, for constructible complexes whose cohomology is not levelwise flat, and for repeated direct images. A useful rule is: strict systems suffice for computations when derived reduction and Mittag--Leffler have been checked; normalized localized systems are the invariant setting for functorial statements.

## 10. Continuous $\ell$-adic cohomology

### 10.1 Definition

Let $\mathcal F=(\mathcal F_n)$ be a normalized constructible $\Lambda$-system. Its continuous étale cohomology complex is

$$
R\Gamma_{\mathrm{cont}}(X,\mathcal F)
=R\varprojlim_nR\Gamma(X,\mathcal F_n),
$$

and

$$
H^q_{\mathrm{cont}}(X,\mathcal F)
=H^q(R\Gamma_{\mathrm{cont}}(X,\mathcal F)).
$$

The adjective “continuous” records two topologies: coefficient sections are reconstructed from finite quotients, and any arithmetic group action is continuous for the inverse-limit topology. When no ambiguity is possible, we write $H^q(X,\mathbf Z_\ell)$ for the continuous cohomology of $(\Lambda_n)$.

This definition is functorial in $X$ and in the coefficient system. A triangle of normalized systems gives a triangle of continuous cohomology complexes because both derived global sections and derived inverse limit are triangulated functors.

### 10.2 The Milnor exact sequence

At every degree there is a natural exact sequence

$$
0\to\varprojlim_n{}^1H^{q-1}(X,\mathcal F_n)
\to H^q_{\mathrm{cont}}(X,\mathcal F)
\to\varprojlim_nH^q(X,\mathcal F_n)
\to0.
$$

For the finite-type schemes and constructible systems of Section 7, each finite-level cohomology group is finite, so the tower is Mittag--Leffler and the left term vanishes. Consequently

$$
H^q_{\mathrm{cont}}(X,\mathcal F)
\cong\varprojlim_nH^q(X,\mathcal F_n).
$$

This isomorphism is compatible with long exact sequences only when those sequences are interpreted through the derived object. Ordinary inverse limits of a termwise long exact sequence need not remain exact at the left; the vanished $\varprojlim^1$ is precisely what repairs exactness in the present finite setting.

### 10.3 Reduction and completion

Let $\mathcal F=(\mathcal F_n)$ be normalized and put $C=R\Gamma_{\mathrm{cont}}(X,\mathcal F)$. Equation (7.1), proved from normalization, preservation of derived limits, and the explicit two-term free resolution of $\Lambda_n$, gives

$$
C\otimes^L_\Lambda\Lambda_n
\xrightarrow{\sim}R\Gamma(X,\mathcal F_n).
$$

No prior perfectness of $C$ is needed. If $X$ is separated of finite type over a separably closed field and $\mathcal F_1$ is bounded constructible, the right side for $n=1$ is bounded with finite-dimensional cohomology. The complete-DVR lemma of Section 7.3 then proves that $C$ is perfect. Thus reduction is an input to the proof of perfectness, not a consequence obtained from perfectness and then used circularly.

At the level of groups, the universal-coefficient sequence reads

$$
0\to H^q(C)/\ell^n
\to H^q(C\otimes^L\Lambda_n)
\to H^{q+1}(C)[\ell^n]\to0.
$$

Thus the system $H^q(X,\mathcal F_n)$ need not be the reductions of one group in degree $q$ alone; torsion in degree $q+1$ can contribute. Derived reduction is the precise compatibility statement.

The derived completion map

$$
C\longrightarrow R\varprojlim_n(C\otimes^L\Lambda_n)
$$

is an isomorphism for bounded complexes with finitely generated $\Lambda$-cohomology. To prove it, resolve by a bounded complex of finite free modules. Such modules are classically $\ell$-adically complete, their reduction towers are surjective, and finite totalization commutes with the limit.

### 10.4 Rational coefficients and lattices

For a lisse $E$-sheaf $\mathcal V$, choose a stable lisse $\Lambda$-lattice $\mathcal F$. Define

$$
R\Gamma(X,\mathcal V)
=R\Gamma_{\mathrm{cont}}(X,\mathcal F)\otimes_\Lambda E.
$$

This does not depend on the lattice. Indeed, any two stable lattices $\mathcal F$ and $\mathcal F'$ in the same finite-dimensional representation are commensurable: for some $a,b\ge0$,

$$
\ell^a\mathcal F\subseteq\mathcal F'\subseteq\ell^{-b}\mathcal F.
$$

The kernels and cokernels of the comparison maps are killed by a power of $\ell$, so tensoring their cohomology complexes with $E$ makes the maps isomorphisms.

For a rational constructible complex, one similarly chooses an integral constructible lattice locally on a finite stratification and inverts $\ell$ in the normalized adic category. A mere inverse system $(\mathcal F_n)$ cannot be “tensored levelwise with $E$,” because $E\otimes_\Lambda\Lambda_n=0$. Rationalization occurs after derived inverse limit, not at each torsion level.

## 11. Continuous Galois actions

### 11.1 Geometric cohomology over a field

Let $X$ be separated of finite type over $k$, and let a constructible coefficient system $\mathcal F$ descend to $X$. Write $a_\sigma$ for the automorphism of $\bar X=X\times_kk^s$ induced by $\sigma$ on $k^s$. Pullback is contravariant, so our left action is

$$
\sigma\cdot c=(a_{\sigma^{-1}})^*c,
$$

using the coefficient descent isomorphism. The inverse is essential: without it, pullback would define a right action. This convention gives an action on

$$
R\Gamma(\bar X,\mathcal F_n)
$$

and hence on every $H^q(\bar X,\mathcal F_n)$. This action is canonical: although describing $\bar X$ through a geometric basepoint introduces paths, the descent action on the whole base change does not depend on a chosen rational point of $X$.

This is different from taking the stalk of a lisse sheaf. The stalk is a representation of $\pi_1(X)$; geometric cohomology is a representation of $G_k$ because the entire geometric scheme varies under descent. Even the constant sheaf has trivial stalk monodromy but can have highly nontrivial Galois action on higher cohomology.

### 11.2 Continuity at finite and integral level

At finite level, $H^q(\bar X,\mathcal F_n)$ is finite in the required cases. Every class is represented using finitely much descent data, so its stabilizer contains an open subgroup of $G_k$. The action on this finite discrete group is continuous.

Passing to the inverse limit gives

$$
G_k\longrightarrow
\operatorname{Aut}_\Lambda
H^q_{\mathrm{cont}}(\bar X,\mathcal F).
$$

First give the group the inverse-limit topology coming from the finite groups $H^q(\bar X,\mathcal F_n)$. The action is continuous because every coordinate action is continuous. In the normalized finite-type cases, perfectness makes the limit a finitely generated $\Lambda$-module and (7.1), together with the universal-coefficient sequence, shows that this topology agrees with its $\ell$-adic topology. It is not necessary, and can be false in the presence of next-degree torsion, that $H^q(\bar X,\mathcal F_n)$ itself equal the quotient of $H^q_{\mathrm{cont}}$ by $\ell^n$. Regarding the limit as an abstract module would lose the continuity conclusion.

If the integral cohomology is finitely generated, tensoring with $E$ yields a continuous finite-dimensional $E$-representation. A stable lattice is already present, so continuity does not have to be reconstructed after rationalization.

### 11.3 Hochschild--Serre with adic coefficients

At level $n$, arithmetic descent gives

$$
R\Gamma(X,\mathcal F_n)
\simeq R\Gamma_{\mathrm{cts}}
\bigl(G_k,R\Gamma(\bar X,\mathcal F_n)\bigr)
$$

under the boundedness conditions of Section 5.2. Taking $R\varprojlim_n$ produces an adic descent object. Define continuous cochains of the compact limit as the inverse limit of the finite discrete cochain complexes. If the geometric cohomology towers and the cochain-cohomology towers are Mittag--Leffler, and $G_k$ has finite cohomological dimension on the modules involved, the two derived operations may be totalized in either order. The resulting spectral sequence is

$$
H^a_{\mathrm{cts}}
\bigl(G_k,H^b_{\mathrm{cont}}(\bar X,\mathcal F)\bigr)
\Longrightarrow H^{a+b}_{\mathrm{cont}}(X,\mathcal F).
$$

Without these hypotheses, the safe object is the total derived expression

$$
R\varprojlim_nR\Gamma_{\mathrm{cts}}
\bigl(G_k,R\Gamma(\bar X,\mathcal F_n)\bigr),
$$

and replacing it by group cohomology of an ordinary inverse limit can miss both a derived-limit term and a continuity condition.

### 11.4 Frobenius conventions

If $k=\mathbf F_q$, arithmetic Frobenius sends $a$ to $a^q$ and geometric Frobenius is its inverse. The descent action just constructed is naturally described using arithmetic Frobenius unless an inverse is inserted. Trace formulas conventionally use geometric Frobenius. We always state which one acts.

For a variety over a number field and a finite place $v$ of good reduction with residue cardinality $q_v$, an unramified geometric cohomology representation has a conjugacy class of Frobenius. Its characteristic polynomial is independent of basepoint and of the chosen lift of Frobenius because both changes conjugate the operator. Establishing unramifiedness uses extension and base change for the particular geometric family; it does not follow merely from continuity.

## 12. Base-change interfaces

### 12.1 The canonical map

Consider a cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
Y'&\xrightarrow{g}&Y.
\end{array}
$$

Adjunction gives a natural transformation

$$
g^*Rf_*K\longrightarrow Rf'_*g'^*K.
$$

Because inverse image of abelian sheaves is exact, no derived symbol is needed on $g^*$ here. The map exists for every square; being an isomorphism is a geometric assertion. It is compatible with pasting squares because both composites are adjoint to the same map after pullback.

If $f$ is finite étale, the map is an isomorphism for all bounded-below coefficients. Étale-locally on $Y$, the morphism is a finite disjoint union of identity maps, direct image is a finite product, and product commutes with pullback. Descent returns the global assertion.

For a product projection $f:Y\times Z\to Y$ with $Z$ fixed and a coefficient pulled back from $Z$ whose cohomology is represented by a bounded finite complex, the formula reduces to tensoring that complex with the constant sheaf on $Y$. Base change is then immediate. These two cases anchor the general interface.

### 12.2 Stalks of a derived direct image

At a geometric point $\bar y\to Y$, the canonical base-change map becomes

$$
(Rf_*K)_{\bar y}
\simeq R\Gamma(X_{(\bar y)},K)
\longrightarrow R\Gamma(X_{\bar y},K|_{X_{\bar y}}).
$$

The first isomorphism is the strict-local stalk formula proved in Section 2.3. The second arrow is restriction from the strict-local family to its closed geometric fiber. Proper base change asserts that it is an isomorphism for proper $f$ and torsion coefficients prime to residue characteristics. Smooth base change gives local constancy conclusions for smooth $f$. Those theorems require geometric work beyond the formalism here.

This distinction diagnoses many faulty arguments. Stalks always compute strict-local cohomology; they compute fiber cohomology only after a base-change theorem. Likewise, knowing every geometric fiber group is finite does not by itself prove that $R^qf_*K$ is constructible.

### 12.3 Passage through an adic tower

Suppose finite-level base change is known:

$$
g^*Rf_*K_n\xrightarrow{\sim}Rf'_*g'^*K_n
$$

for every $n$. These arrows already form an isomorphism of finite-level systems. After normalizing both systems they therefore give an isomorphism in the adic derived category; no interchange of a stalk with an ordinary inverse limit is involved in that assertion. If one realizes the two sides as $R\varprojlim$ complexes of ordinary $\Lambda$-module sheaves, uniform bounded amplitude and the relevant Mittag--Leffler conditions justify the realization and its stalkwise interpretation.

For a proper smooth family of curves or abelian varieties with lisse finite free coefficients, finite-level constructibility and uniform cohomological dimension give precisely this control. One obtains

$$
g^*R f_{*,\mathrm{cont}}\mathcal F
\xrightarrow{\sim}
R f'_{*,\mathrm{cont}}g'^*\mathcal F,
$$

where the continuous direct image is represented by $(Rf_*\mathcal F_n)_n$ and normalized, and $g^*$ on the left means normalized adic pullback. Rationalizing afterward preserves the isomorphism.

### 12.4 A safe base-change protocol

A base-change argument should be read in four layers. First construct the canonical map by adjunction. Second prove the geometric finite-level theorem in the coefficient range at hand. Third establish uniform amplitude and constructibility so that inverse limits behave well. Fourth normalize the resulting system and only then invert $\ell$.

Skipping the second layer confuses a canonical arrow with an isomorphism. Skipping the third can lose a $\varprojlim^1$ term. Inverting $\ell$ levelwise gives zero and is never a rationalization. With all four layers present, base change is compatible with reduction, continuous Galois action, and cup products.

## 13. Cup products and coefficient pairings

### 13.1 Finite-level products

Let $K,L$ be complexes of $\Lambda_n$-sheaves. The diagonal of $X$ and tensor product of sections give a derived morphism

$$
R\Gamma(X,K)\otimes^L_{\Lambda_n}R\Gamma(X,L)
\longrightarrow
R\Gamma(X,K\otimes^L_{\Lambda_n}L).
$$

On cohomology it yields

$$
H^a(X,K)\otimes H^b(X,L)
\longrightarrow H^{a+b}(X,K\otimes^LL).
$$

A K-flat replacement in one tensor variable and a K-injective replacement for global sections make the construction independent of choices. The shuffle interchange of cochains gives

$$
x\smile y=(-1)^{ab}\,\tau(y\smile x),
$$

where $\tau$ switches the coefficient factors. Associativity and the unit class in $H^0(X,\Lambda_n)$ hold already at the derived level.

### 13.2 Products after derived completion

Compatible finite-level products define a map of towers. Derived inverse limit and the natural map from the tensor product of limits to the limit of tensor products give

$$
R\Gamma_{\mathrm{cont}}(X,\mathcal F)
\otimes^L_\Lambda
R\Gamma_{\mathrm{cont}}(X,\mathcal G)
\longrightarrow
R\Gamma_{\mathrm{cont}}
(X,\mathcal F\otimes^L\mathcal G).
$$

For perfect complexes this reduces modulo $\ell^n$ to the finite-level product and is characterized by those reductions. Without perfectness, tensor product need not commute with inverse limit, so a levelwise pairing does not automatically induce the displayed map on ordinary limits.

After tensoring with $E$, the integral pairing becomes the rational cup product. Independence of lattices follows from commensurability. If either integral lattice has torsion, the derived tensor product must be retained before rationalizing, even though the torsion disappears afterward; it can affect connecting maps at finite level.

### 13.3 Twists, signs, and Galois equivariance

Tate twists add under tensor product:

$$
\Lambda_n(r)\otimes_{\Lambda_n}\Lambda_n(s)
\cong\Lambda_n(r+s).
$$

Hence cup product has the form

$$
H^a(X,\Lambda_n(r))\otimes H^b(X,\Lambda_n(s))
\longrightarrow H^{a+b}(X,\Lambda_n(r+s)).
$$

The sign depends on cohomological degrees $a,b$, not on twists $r,s$. Twists record Galois action, not a second cochain parity.

If $X$ and the coefficient pairing descend to $k$, then

$$
\sigma(x\smile y)=\sigma x\smile\sigma y
$$

for every $\sigma\in G_k$. This follows before cohomology from functoriality of pullback and the diagonal. Therefore invariant pairings, polarizations, and Hecke-equivariant products remain equivariant after completion and rationalization.

### 13.4 Projection formulas and correspondences

For $f:X\to Y$ there is a projection morphism

$$
Rf_*K\otimes^LL
\longrightarrow
Rf_*(K\otimes^Lf^*L).
$$

It is an isomorphism when $L$ is perfect and the relevant direct images are bounded. Reduce to a finite locally free sheaf, where the assertion is checked locally, and rebuild a perfect complex through finitely many cones.

A finite correspondence

$$
X\xleftarrow{p}Z\xrightarrow{q}X
$$

acts contravariantly by $p^*$. If $q$ is finite étale, there is also an elementary coefficient trace

$$
\operatorname{tr}_q:q_*q^*L\longrightarrow L.
$$

Étale-locally, $q$ is a finite disjoint union of identity maps and this arrow is summation of the components; permutation invariance makes those local maps descend. The composite of $R\Gamma(Z,q^*L)=R\Gamma(X,q_*q^*L)$ with $\operatorname{tr}_q$ is the covariant map denoted $q_*$. Thus $q_*p^*$ acts when the coefficient identifications along the two legs have been specified, and the projection formula gives compatibility with cup products. Trace maps for general proper maps and their duality properties require the later duality theory; no such trace is silently assumed here.

## 14. Curves

### 14.1 Cohomological amplitude and finiteness

Curves are the first place where étale cohomology produces a genuinely arithmetic middle degree. Let $C$ be a geometrically connected smooth curve over a separably closed field $k$, with $\ell\ne\operatorname{char}k$, and let $\mathcal F$ be a constructible $\Lambda_n$-sheaf. If $C$ is proper, then

$$
R\Gamma(C,\mathcal F)\in D^{[0,2]}(\Lambda_n)
$$

and all cohomology groups are finite. If $C$ is affine, the upper endpoint is $1$. For a bounded constructible complex with cohomology in $[a,b]$, the corresponding ranges are $[a,b+2]$ and $[a,b+1]$.

For the constant sheaf on a proper smooth connected curve, $H^0(C,\Lambda_n)=\Lambda_n$ and the remaining possible groups are finite in degrees one and two. Section 6.7 computes them, after a choice of primitive $\ell^n$th root of unity identifying $\Lambda_n$ with $\mu_{\ell^n}$: the degree-two group is cyclic of order $\ell^n$ through $\operatorname{Pic}(C)/\ell^n$, and the degree-one group is $\operatorname{Pic}^0(C)[\ell^n]$, whose order is $\ell^{2gn}$ by the torsion order corollary of Section 6.8. What the adic construction needs is only the weaker statement supplied by the finite-coefficient theorem: finite groups in a uniform interval. The canonical identification of the top group with $\Lambda_n(-1)$ by a trace map, as opposed to the noncanonical identification of its order, belongs to the duality book.

### 14.2 The first cohomology group

For a proper smooth curve $C$, finite étale $\Lambda_n$-torsors under a constant cyclic group are classified by $H^1(C,\Lambda_n)$. Equivalently,

$$
H^1(C,\Lambda_n)
\cong\operatorname{Hom}_{\mathrm{cont}}
(\pi_1(C)^{\mathrm{ab}},\Lambda_n).
$$

This follows because a $1$-cocycle for the trivial action is a continuous homomorphism, and every finite torsor is represented by a finite étale cover. Passing through the compatible tower gives

$$
H^1(C,\mathbf Z_\ell)
\cong\operatorname{Hom}_{\mathrm{cont}}
(\pi_1(C)^{\mathrm{ab}},\mathbf Z_\ell).
$$

If $C$ descends to $k_0$, this finitely generated $\Lambda$-module carries a continuous $G_{k_0}$-action. Section 6.8 identifies each finite level with $\operatorname{Pic}^0(C)[\ell^n]$ through the Kummer sequence and shows that this group is free of rank $2g$ over $\Lambda_n$; the limit is then free of rank $2g$ over $\Lambda$. The comparison with the Tate module of the Jacobian, and the exterior-algebra description of the cohomology of an abelian variety, are carried out in Book 36, Section 10.5. Neither the rank nor that comparison is used for the construction or the continuity here. The action should not be confused with the fundamental-group action on the stalk of a lisse coefficient sheaf: constant coefficients have trivial stalk action, while $H^1(\bar C,\mathbf Z_\ell)$ usually has nontrivial arithmetic action.

For nonconstant lisse $\mathcal F$, $H^0(C,\mathcal F)$ is the invariant submodule of a geometric stalk. The group $H^1$ measures extensions and torsors twisted by monodromy. Even if $\mathcal F$ has no invariants, $H^1$ need not vanish; topology of the curve and monodromy relations can create classes.

### 14.3 Open and semistable curves

Let $j:U\hookrightarrow C$ be the complement of a finite set $D$ in a proper smooth curve. The localization triangle compares $R\Gamma(C,j_!\mathcal F)$, $R\Gamma(C,Rj_*\mathcal F)$, and local boundary data. For a lisse sheaf, the stalk of $Rj_*\mathcal F$ at $x\in D$ is computed by continuous cohomology of the punctured strict-local fundamental group, hence by inertia invariants and their first cohomology in the prime-to-characteristic range. This explains why deleting a point creates degree-one boundary classes.

Now let $C$ be a connected proper nodal curve over a separably closed field. Write $\nu:\widetilde C\to C$ for its normalization, let $\Gamma_C$ be its dual graph, and use constant $\Lambda_n$-coefficients. Comparing the two branches above every node gives an exact sequence of sheaves whose cohomology yields

$$
0\longrightarrow H^1(\Gamma_C,\Lambda_n)
\longrightarrow H^1(C,\Lambda_n)
\longrightarrow H^1(\widetilde C,\Lambda_n)
\longrightarrow0,
$$

and

$$
H^2(C,\Lambda_n)\cong
\bigoplus_{V}H^2(\widetilde C_V,\Lambda_n),
$$

where $V$ runs over irreducible components. The first sequence need not split canonically. Its graph term records cycles created by gluing components, while the normalized term records the genera of the components. For a tree of projective lines, $H^1$ vanishes; for a polygon of projective lines, the graph contributes one copy of $\Lambda_n$.

This calculation is the static cohomology of a semistable fiber. Comparing it with a nearby smooth generic fiber requires nearby cycles and monodromy; no such comparison follows merely from the normalization sequence.

### 14.4 Perfectness

Let $(\mathcal F_n)$ be a normalized bounded constructible adic system on a finite-type curve, on a common finite stratification. Then

$$
C=R\Gamma_{\mathrm{cont}}(C,\mathcal F)
$$

is perfect over $\Lambda$. Indeed, (7.1) identifies its reduction modulo $\ell$ with $R\Gamma(C,\mathcal F_1)$, which is bounded with finite-dimensional cohomology. The complete-DVR lemma of Section 7.3 then gives a bounded finite free representative. In particular its integral cohomology modules are finitely generated, and Milnor identifies them with the ordinary inverse limits of the finite-level groups. For a proper curve the sheaf-cohomological range is $[0,2]$; a coefficient complex shifts this interval by its own amplitude.

Perfectness is stronger than degreewise finite generation. It makes derived reduction, tensor products, dual constructions, and base change compatible with finite complexes. It does not assert that each integral cohomology group is torsion-free, nor that the complex splits as the direct sum of its cohomology groups.

## 15. Abelian schemes

### 15.1 Absolute finiteness and amplitude

Let $A$ be an abelian variety of dimension $g$ over a separably closed field of characteristic different from $\ell$. It is smooth, proper, and of finite type, so the finite-coefficient theorem applies to every constructible finite $\ell$-primary sheaf $\mathcal F$:

$$
H^q(A,\mathcal F)\text{ is finite},
\qquad H^q(A,\mathcal F)=0\quad(q>2g).
$$

This is the abelian-variety finiteness input promised here. It does not require a calculation of the full constant-coefficient algebra. The comparison with the dual Tate module and the exterior-algebra description of constant cohomology are carried out in Book 36, Section 10.5, where polarizations, duality and the profinite-group cohomology of Book 24 are all available. Keeping those assertions out of the present proof prevents a rank computation from being smuggled into the finiteness theorem.

For a normalized bounded constructible adic complex $\mathcal F$, (7.1) identifies finite-level reduction of $R\Gamma_{\mathrm{cont}}(A,\mathcal F)$. Its mod-$\ell$ reduction is bounded in the interval obtained by adding $[0,2g]$ to the amplitude of $\mathcal F_1$ and has finite-dimensional cohomology. The complete-DVR lemma makes the continuous complex perfect.

### 15.2 Torsion and lisse Tate systems

**Tate system theorem.** Let $f:A\to S$ be an abelian scheme of relative dimension $g$, that is, a smooth proper finitely presented commutative group scheme with geometrically connected fibers, and assume $\ell$ is invertible on $S$. Assume in addition that $A/S$ is **polarizable**: Zariski-locally on $S$ it carries a relatively ample line bundle. Then $A[\ell^n]$ is finite étale over $S$ of rank $\ell^{2gn}$, and the tower $T_\ell A=(A[\ell^n])_n$ is a lisse $\Lambda$-system of rank $2g$.

The polarizability hypothesis is not decoration. Projectivity is part of the definition of an abelian scheme adopted in Book 15, Section 11.1, and Book 8, Sections 9.3 and 9.4, likewise take a relatively ample bundle as the input to the embedding theorem; Book 8, Section 3.3, records that properness alone does not give projectivity except by special geometry. The general theorem that an abelian scheme is projective belongs to Book 35 and may not be cited here. In the applications the hypothesis costs nothing: PEL and modular families carry a polarization by the definition of the moduli problem, and every abelian scheme that occurs in this book comes with one. For the Jacobian of a curve over a field, the required bundle is the theta divisor, whose ampleness is proved in Book 17a, Section 8.4, and imported in Section 6.8.

**Proof.** Multiplication by $\ell^n$ is étale because its differential on the relative tangent bundle is multiplication by the unit $\ell^n$ and translation propagates this to every point. It is proper and quasi-finite, hence finite; so $A[\ell^n]$, its kernel, is finite étale over $S$. The rank of a finite étale group scheme is locally constant, so it may be computed on a geometric fiber $A_{\bar s}$, which is a smooth proper connected group scheme of dimension $g$ over an algebraically closed field carrying an ample line bundle.

That computation is the degree theorem of Section 6.8, and we recall its two ingredients in the present notation. Choosing a relatively ample $L_0$, rigidifying it along the zero section and replacing it by $L_0\otimes[-1]^*L_0$ produces an ample symmetric rigidified $L$. The cubical identity is the alternating tensor product of the pullbacks of $L$ along the seven nonempty partial-sum maps $A^3\to A$; its restriction to each coordinate plane is trivial by cancellation, and the see-saw lemma of Section 6.8 together with the rigidity of morphisms from a proper connected scheme to an affine one extends those trivializations over the whole triple product. This is the cube lemma of Book 15, Section 11.2, and it is what replaces the appeal to a see-saw principle from a later book that stood here before. Specializing two variables gives the theorem of the square, and pulling the identity back along $([m],\mathrm{id},[-1])$ gives, by induction on $m$, the relation $[m]^*L\simeq L^{\otimes m^2}$ on every geometric fiber.

The degree is then read off from Hilbert polynomials, as in Section 6.8: $[m]_*\mathcal O$ is locally free of rank $\deg[m]$, so $\chi(A_{\bar s},([m]^*L)^{\otimes t})$ has leading coefficient $\deg[m]$ times that of $\chi(A_{\bar s},L^{\otimes t})$, while $[m]^*L\simeq L^{\otimes m^2}$ makes that leading coefficient $m^{2g}$ times as large. The polarized degree of $L$ is a positive integer, so $\deg[m]=m^{2g}$. Taking $m=\ell^n$ gives the stated rank. $\square$

The transition maps $A[\ell^{n+1}]\to A[\ell^n]$ make

$$
T_\ell A=(A[\ell^n])_n
$$

a lisse $\Lambda$-system of rank $2g$. This construction uses only finite étale covering theory together with the divisor calculus behind the degree of $[\ell^n]$; no cohomology of $A$ enters. It should not yet be identified with $R^1f_*\Lambda$; that comparison is a cohomological base-change and duality statement with a contravariance and, after polarization, a Tate twist.

### 15.3 Families and base change

Let $f:A\to S$ be as above. On every geometric fiber, Section 15.1 gives finite cohomology and vanishing above $2g$. The finite étaleness of $A[\ell^n]$ constructs the lisse Tate system without a cohomological comparison theorem. By contrast, identifying stalks of $R^if_*\Lambda_n$ with fiber cohomology and proving that these direct images are lisse use smooth proper base change. Those are precisely the geometric assertions reserved for the next book.

Once finite-level smooth proper base change is available, the uniform amplitude and finite-level constructibility let Section 12.3 transport the result to the normalized $\Lambda$-system. Any later identification of $R^1f_*\Lambda_n$ with the dual of $A[\ell^n]$ must state its contravariance; a polarization changes that dual description by the Weil-pairing twist.

An isogeny $u:A\to B$ induces contravariant pullback on cohomology and a covariant map on Tate modules. If its degree is prime to $\ell$, the Tate-module map is an isomorphism. Deducing the corresponding cohomological isomorphism requires the later identification just described; it is not inferred here from matching ranks.

### 15.4 Integral perfectness

For a geometric fiber $A_{\bar s}$,

$$
R\Gamma(A_{\bar s},\mathbf Z_\ell)
$$

is perfect and supported in cohomological degrees $0$ through $2g$. Perfectness follows from (7.1) and the complete-DVR lemma. It does not assert that every integral cohomology group is torsion-free.

Relatively, after finite-level proper smooth base change and constructibility, the normalized system $(Rf_*\Lambda_n)_n$ is perfect over $S$ in the adic sense. Fiberwise perfection alone would not prove this local relative statement; constructibility and base change are what spread a finite model from a geometric fiber to an étale neighborhood.

Tensoring with $E$ gives a perfect rational complex. Computing its individual ranks or Euler characteristic is a separate constant-coefficient calculation and is not needed for finiteness, completion, or continuity.

## 16. A reusable derived package

### 16.1 The integral theorem

We can now collect the constructions into the form used later.

**Integral geometric cohomology theorem.** Let $k$ be a field, let $X/k$ be one of the following:

- a smooth proper or semistable proper curve;
- an abelian variety of dimension $g$.

Let $\mathcal F=(\mathcal F_n)$ be a normalized bounded constructible $\Lambda$-system on a common finite stratification. For compact support, apply this hypothesis to $(j_!\mathcal F_n)$. Then:

1. $R\Gamma_{\mathrm{cont}}(\bar X,\mathcal F)$ is bounded and derived complete;
2. its cohomology modules are finitely generated over $\Lambda$;
3. it is a perfect $\Lambda$-complex;
4. reduction modulo $\ell^n$ recovers $R\Gamma(\bar X,\mathcal F_n)$;
5. it carries a continuous $G_k$-action compatible with cup products and every finite correspondence defined over $k$ that is equipped with the required coefficient identification.

For a proper curve the sheaf-cohomological range is $[0,2]$, and for an abelian variety it is $[0,2g]$. A coefficient complex shifts these ranges by its own amplitude.

**Proof.** Finite-level boundedness and finiteness are supplied by Chapters 6 and 7. Hence every fixed-degree tower is Mittag--Leffler, so Milnor identifies continuous cohomology with its inverse limit and preserves the uniform range. Equation (7.1) gives derived reduction directly from normalization. In particular the mod-$\ell$ reduction is bounded with finite-dimensional cohomology; the complete-DVR lemma makes the continuous complex perfect and its cohomology finitely generated. The descent action is continuous at every finite level and therefore on the inverse-limit topology. Products and finite traces are compatible levelwise and hence on the normalized limit. $\square$

### 16.2 The rational theorem

**Rational geometric cohomology theorem.** Under the same hypotheses, let $\mathcal V$ be the rational coefficient object obtained from an integral lattice $\mathcal F$. Then

$$
R\Gamma(\bar X,\mathcal V)
=R\Gamma_{\mathrm{cont}}(\bar X,\mathcal F)
\otimes_\Lambda E
$$

is a bounded perfect $E$-complex, independent of the lattice. Every cohomology group is finite-dimensional and carries a continuous $G_k$-action. Cup products, Tate twists, finite-correspondence actions, and any finite-level base-change isomorphisms commute with rationalization.

**Proof.** Commensurable lattices differ by bounded $\ell$-power torsion, which vanishes after tensoring with $E$. A perfect integral representative becomes a bounded complex of finite-dimensional $E$-vector spaces. All structures were constructed on the integral tower, so tensoring transports their identities. $\square$

This theorem does not say that every system of $E$-vector spaces arises from a constructible lattice. The stable-lattice theorem applies to continuous finite-dimensional representations with compact image. Infinite-rank or noncontinuous actions fall outside the category.

### 16.3 A diagnostic checklist

When a geometric construction is claimed to produce an $\ell$-adic cohomology representation, the following questions locate every possible gap.

1. Is $\ell$ invertible on the scheme, and are the finite-level coefficient sheaves constructible?
2. Is the tower strictly compatible, or at least normalized under derived reduction?
3. Is the geometric cohomological amplitude uniform in $n$?
4. Are finite-level cohomology groups finite, so that $\varprojlim^1$ vanishes?
5. Does the claimed base-change arrow come from adjunction, and which geometric theorem makes it an isomorphism?
6. Is the group action on stalks a fundamental-group action, or is the action on geometric cohomology a ground-field Galois action?
7. Was rationalization performed after derived inverse limit using a lattice?
8. Are cup products and correspondences constructed at finite level and compatible with transition maps?
9. Does perfectness mean a bounded finite-projective representative, rather than merely finite-dimensional rational cohomology?

Each question addresses a real failure mode. A naive limit can miss $\varprojlim^1$; a base-change map can exist without being invertible; a rational local system can be misstated as a discrete sheaf; and finite cohomology groups can assemble into a nonperfect complex if boundedness or finite generation is absent.

### 16.4 Final synthesis

Étale cohomology begins with a simple obstruction: local sections need not glue. The small étale topos supplies the correct neighborhoods, and derived global sections retain every obstruction and connecting map at once. Constructibility turns arbitrary local behavior into finitely many lisse pieces. Cohomological-dimension and finiteness arguments then make the resulting complexes bounded and arithmetically manageable for curves and abelian varieties.

The passage to $\ell$-adic coefficients is not a change of symbols. It is a passage from finite sheaves to a normalized inverse system, from ordinary limit to derived limit, and from discrete finite actions to a continuous action on a profinite lattice. The Milnor sequence records the possible defect. In the finite geometric situations of this book, Mittag--Leffler kills that defect, but only after finiteness has been proved.

With these distinctions preserved, the final package is robust. Continuous cohomology is derived complete, reduction returns the finite levels, rationalization is independent of a lattice, Galois actions are continuous, and cup products and correspondences survive every passage. Base-change maps have been constructed in the precise form needed to receive the geometric theorems that follow. The resulting perfect complexes are the natural containers from which arithmetic representations will be extracted.
