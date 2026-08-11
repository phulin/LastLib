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
- [5. Functoriality and spectral sequences](#5-functoriality-and-spectral-sequences)
  - [5.1 Derived direct image and Leray](#51-derived-direct-image-and-leray)
  - [5.2 Arithmetic descent and Hochschild--Serre](#52-arithmetic-descent-and-hochschild--serre)
  - [5.3 Coefficient change](#53-coefficient-change)
  - [5.4 Boundedness and convergence](#54-boundedness-and-convergence)
- [6. Torsion cohomological dimension](#6-torsion-cohomological-dimension)
  - [6.1 What cohomological dimension measures](#61-what-cohomological-dimension-measures)
  - [6.2 Fields and strict local schemes](#62-fields-and-strict-local-schemes)
  - [6.3 Curves](#63-curves)
  - [6.4 Low-dimensional finite-type schemes](#64-low-dimensional-finite-type-schemes)
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
- [16. Selected Shimura surfaces](#16-selected-shimura-surfaces)
  - [16.1 The geometric input](#161-the-geometric-input)
  - [16.2 Interior and boundary complexes](#162-interior-and-boundary-complexes)
  - [16.3 Finiteness and perfectness](#163-finiteness-and-perfectness)
  - [16.4 Hecke and Galois actions](#164-hecke-and-galois-actions)
- [17. A reusable derived package](#17-a-reusable-derived-package)
  - [17.1 The integral theorem](#171-the-integral-theorem)
  - [17.2 The rational theorem](#172-the-rational-theorem)
  - [17.3 A diagnostic checklist](#173-a-diagnostic-checklist)
  - [17.4 Final synthesis](#174-final-synthesis)

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

The book establishes four packages. First, finite torsion coefficients admit a complete derived theory on the small étale topos, with Leray, hypercohomology, localization, Hochschild--Serre, and cup products. Second, constructible prime-to-residue-characteristic coefficients on a separated finite-type $d$-fold over a separably closed field have finite cohomology and vanish above degree $2d$. We prove the affine theorem and the dimension-controlled gluing argument from which this follows; in particular the bounds are $2$ for proper curves, $2g$ for $g$-dimensional abelian varieties, and $4$ for surfaces. Third, compatible finite-level complexes define continuous integral and rational cohomology, with the exact $\varprojlim^1$ obstruction displayed. Fourth, in the cases needed for curves, abelian schemes, and the selected two-dimensional PEL varieties, the resulting geometric complexes are bounded and perfect over $\Lambda$, and their cohomology carries continuous Galois and functorial correspondence actions.

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

The required continuity can be proved directly in the constructible torsion case. In a fixed degree, a class is represented on a hypercover truncated one degree beyond that class. Quasi-compactness and quasi-separatedness let one choose finitely many quasi-compact étale objects in every relevant degree. Their equations, the finitely many coefficient sections, and all face identities descend to one pointed neighborhood $V$. If a descended class becomes zero on the limit, the finitely many cochains and homotopies witnessing zero also descend after a further neighborhood. This proves both surjectivity and injectivity of the map from the displayed colimit to $H^q(X_{(\bar y)},\mathcal F)$. Notice that this is not yet geometric base change: $X_{(\bar y)}$ need not have the cohomology of the geometric fiber $X_{\bar y}$.

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

There are two safe uses. If every finite intersection of members of $\mathcal U$ is acyclic for $\mathcal F$, the augmented Čech complex is an acyclic resolution and computes $R\Gamma(X,\mathcal F)$. More generally, refine the Čech nerve degree by degree to a hypercover. Cohomological descent identifies the total complex over all levels with derived global sections, provided the boundedness needed for totalization holds.

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

## 6. Torsion cohomological dimension

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

The assertion is the one-dimensional case of the affine theorem proved in Section 7.2. It is worth isolating why finite-cover descent alone is not its proof. If a finite Galois cover with group $G$ trivializes a lisse sheaf and $\ell$ divides $|G|$, the groups $H^a(G,-)$ can be nonzero in arbitrarily large degrees. The differentials in the descent sequence must then cancel those terms. The affine theorem obtains the cancellation from a length-one geometric model for a punctured curve, not from an unjustified vanishing of finite-group cohomology.

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

## 7. Finiteness for constructible torsion coefficients

### 7.1 The finiteness theorem in the required range

Vanishing alone does not make inverse limits manageable. We also need every finite-level group to be finite.

**Finite-coefficient theorem.** Let $k$ be separably closed, let $X$ be separated of finite type over $k$ of dimension $d$, and let $\mathcal F$ be a constructible sheaf of finite $\ell$-primary modules, where $\ell\ne\operatorname{char}k$. Then every $H^q(X,\mathcal F)$ is finite and

$$
H^q(X,\mathcal F)=0\qquad(q>2d).
$$

If $X$ is affine, the sharper bound is $q>d$. Thus the theorem gives $[0,2]$ for proper curves, $[0,2g]$ for $g$-dimensional abelian varieties, and $[0,4]$ for surfaces. No properness or smoothness is needed for finiteness. In the applications, coefficients are constant, lisse finite free, or obtained from these by a finite stratification.

### 7.2 The proof architecture

The proof has one geometric lemma and one gluing lemma. We give their proofs because neither finite monodromy nor the derived formalism alone implies finiteness.

**Affine constructible lemma.** If $U$ is affine of finite type of dimension $d$ over $k$, then, for every constructible finite $\ell$-primary sheaf $\mathcal F$,

$$
H^q(U,\mathcal F)=0\quad(q>d),
$$

and every group in the remaining range is finite.

**Proof.** We argue simultaneously by dimension and noetherian induction on the support. The assertion is immediate in dimension zero: the reduced support is a finite set of spectra of finite purely inseparable extensions of $k$, hence has the same étale topos as a finite set of separably closed points.

We next establish the curve step without using the higher-dimensional induction. Normalize an affine curve, compactify each smooth component, and let $D$ be the nonempty finite boundary. Skyscraper kernels and cokernels at the singular points have no positive cohomology, so it is enough to treat a lisse finite sheaf on a smooth $U=C\setminus D$. The prime-to-characteristic tame fundamental group has the finite presentation

$$
\left\langle
a_1,b_1,\ldots,a_g,b_g,c_1,\ldots,c_r
\ \middle|\
\prod_{i=1}^g[a_i,b_i]\prod_{j=1}^r c_j=1
\right\rangle,
$$

in every finite quotient of order prime to the characteristic; $c_j$ is inertia at the $j$th boundary point. Here is the algebraic construction of the presentation. Choose separating functions with prescribed simple zeros and poles by Riemann--Roch, use their Kummer covers to produce the $c_j$, and use $g$ pairs of functions with disjoint polar divisors to produce the handle generators. Normalizing successive fiber products gives every finite tame cover: the valuation criterion says that a function-field extension unramified on $U$ can ramify only at $D$, and the product of the local inertia elements is one because the divisor of a rational function has degree zero. Riemann--Hurwitz shows that a proper quotient of the displayed group would omit a connected cover of the predicted degree and genus, so the map on every finite tame quotient is injective as well as surjective. This proves the presentation through the finite-cover classification of Book 19.

Because $r>0$, eliminate $c_r$; the maximal pro-$\ell$ quotient is a free pro-$\ell$ group on $2g+r-1$ generators. In characteristic $p>0$, wild inertia is pro-$p$, and invariants under it are exact on $\ell$-primary modules; in characteristic zero there is no wild subgroup. Prime-to-$\ell$ parts of the remaining finite monodromy are also exact by averaging. Thus continuous cohomology of the full group with a finite $\ell$-primary module is computed by the two-term free-group cochain complex

$$
M\longrightarrow M^{,2g+r-1}.
$$

It is finite and has no cohomology above degree one. Finite torsors give the same complex as étale cohomology on $U$, and a finite constructibility filtration extends the result from lisse sheaves to all constructible sheaves. This proves the lemma in dimension one.

For the induction step in dimension at least two, first refine the constructibility stratification and replace the support by one irreducible stratum. After removing a smaller closed subset, the stratum is smooth and the sheaf is lisse. A generic linear projection, after shrinking source and target, gives an elementary affine-curve fibration

$$
U^\circ\xrightarrow{f}V
$$

with $V$ affine of dimension $d-1$: there is a smooth proper relative curve $\overline U^\circ\to V$ containing $U^\circ$, and the complement is finite over $V$. To obtain it, choose a separating transcendence basis for the smooth function field and realize $d-1$ of its elements as sufficiently general linear projections on an affine embedding. The generic fiber is then a smooth curve; openness of the smooth locus gives a smooth morphism after deleting the discriminant. Normalizing the projective closure and deleting the nonflat locus makes the boundary finite; deleting its branch locus makes it étale. This argument remains valid over an imperfect separably closed field because the chosen basis is separating. Every deletion has smaller-dimensional complement and is handled by noetherian induction.

We need the relative curve calculation only for this elementary fibration. A lisse finite sheaf is trivialized by a finite étale cover. Normalize $\overline U^\circ$ in a Galois closure and shrink $V$ once more so that the normalization and every branch component are finite and flat over the corresponding strata. At a boundary branch the strict-local group is an extension of wild inertia by a procyclic tame group. In characteristic $p>0$, wild inertia is pro-$p$ and its invariants are exact on finite $\ell$-primary modules: on every finite quotient, averaging by the inverse of its $p$-power order splits invariants. In characteristic zero the wild group is trivial. The remaining tame cochains are represented by the two-term complex

$$
M\xrightarrow{\tau-1}M,
$$

where $\tau$ is a compatible tame generator. Apply the curve presentation just proved to the geometric fibers. The finite list of generators, inertia operators, and the single relation is defined after one pointed étale neighborhood of the base: all covers and branch sections involved are finitely presented. The resulting two-term presentation complexes therefore form constructible finite sheaves on $V$ and commute with further pointed étale restriction. Descent along the finite trivializing cover is retained in these complexes rather than replaced by the generally unbounded groups $H^a(G,-)$. It follows that $R^0f_*\mathcal F$ and $R^1f_*\mathcal F$ are constructible finite sheaves and that $R^qf_*\mathcal F=0$ for $q>1$. The same construction with extension by zero handles a locally closed stratum: the missing sections simply impose zero in the corresponding local term.

The Leray sequence now has only the rows $0$ and $1$. By induction on $\dim V$ its terms vanish when $a>d-1$, so $H^{a+b}(U^\circ,\mathcal F)$ vanishes above $d$ and is finite. The kernel and cokernel of the map from the extension by zero on $U^\circ$ to the original sheaf are supported on the deleted closed subset. The localization long exact sequence and noetherian induction transfer the same assertions to $U$. This closes both inductions. $\square$

The proof also explains the prime-to-characteristic hypothesis. It is exactly what makes wild-inertia invariants exact and leaves a length-one tame local complex. It explains the uniformity in the exponent as well: for a fixed stratification and fixed ranks, the same finite Čech and inertia complexes work for every $\Lambda_n$.

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

For a proper smooth family of curves, abelian varieties, or selected surfaces with lisse finite free coefficients, finite-level constructibility and uniform cohomological dimension give precisely this control. One obtains

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

For the constant sheaf on a proper smooth connected curve, $H^0(C,\Lambda_n)=\Lambda_n$ and the remaining possible groups are finite in degrees one and two. Their ranks and the canonical identification of the top twisted group require the divisor-class and trace calculations developed in the curve and duality books. The present result is exactly what the adic construction needs: finite groups in a uniform interval. Kummer theory still supplies useful individual classes on open curves, but it is not being used as a substitute for the full top-degree calculation.

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

If $C$ descends to $k_0$, this finitely generated $\Lambda$-module carries a continuous $G_{k_0}$-action. Later divisor-class theory proves that it is free of rank $2g$ and compares it with the Tate module of the Jacobian. That later identification is not used for its construction or continuity here. The action should not be confused with the fundamental-group action on the stalk of a lisse coefficient sheaf: constant coefficients have trivial stalk action, while $H^1(\bar C,\mathbf Z_\ell)$ usually has nontrivial arithmetic action.

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

This is the abelian-variety finiteness input promised here. It does not require a calculation of the full constant-coefficient algebra. The later comparison with the dual Tate module and the exterior-algebra description of constant cohomology use polarizations and duality. Keeping those assertions out of the present proof prevents a rank computation from being smuggled into the finiteness theorem.

For a normalized bounded constructible adic complex $\mathcal F$, (7.1) identifies finite-level reduction of $R\Gamma_{\mathrm{cont}}(A,\mathcal F)$. Its mod-$\ell$ reduction is bounded in the interval obtained by adding $[0,2g]$ to the amplitude of $\mathcal F_1$ and has finite-dimensional cohomology. The complete-DVR lemma makes the continuous complex perfect.

### 15.2 Torsion and lisse Tate systems

Let $f:A\to S$ be an abelian scheme of relative dimension $g$, and assume $\ell$ is invertible on $S$. Multiplication by $\ell^n$ is étale because its differential on the relative tangent bundle is multiplication by the unit $\ell^n$. It is proper and quasi-finite, hence finite. Its kernel $A[\ell^n]$ is therefore finite étale over $S$.

Its rank is $\ell^{2gn}$. To see the degree without assuming a cohomology calculation, choose a relatively ample line bundle and replace it by its tensor product with its pullback under $[-1]$; this makes it symmetric. For completeness, the cubical identity is obtained by taking the alternating tensor product of the pullbacks of $L$ along the seven nonempty partial-sum maps $A^3\to A$. Its restriction to every coordinate plane is trivial. Applying the seesaw argument twice shows that the bundle itself is pulled back from the zero section, hence is numerically trivial on every fiber. Specializing two variables gives the theorem of the square, and induction on $m$ gives, on every geometric fiber,

$$
[m]^*L\equiv L^{\otimes m^2}.
$$

On a geometric fiber, the leading coefficient of the Hilbert polynomial is the top self-intersection of $L$ divided by $g!$. Pullback multiplies that self-intersection by $\deg[m]$, while replacing $L$ by $L^{\otimes m^2}$ multiplies it by $m^{2g}$. Hence $\deg[m]=m^{2g}$; the degree is locally constant on $S$, giving the stated rank for $m=\ell^n$.

The transition maps $A[\ell^{n+1}]\to A[\ell^n]$ make

$$
T_\ell A=(A[\ell^n])_n
$$

a lisse $\Lambda$-system of rank $2g$. This construction uses only finite étale covering theory. It should not yet be identified with $R^1f_*\Lambda$; that comparison is a cohomological base-change and duality statement with a contravariance and, after polarization, a Tate twist.

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

## 16. Selected Shimura surfaces

### 16.1 The geometric input

The surfaces needed in the arithmetic route arise from PEL moduli problems at sufficiently small level. For the present cohomological package, their detailed moduli interpretation is compressed into the following explicit hypotheses. Let $S$ be a smooth geometrically connected quasi-projective surface over a number field $K$. Assume:

1. $S$ has a smooth projective compactification $j:S\hookrightarrow\overline S$ whose boundary $D$ is a strict normal-crossings divisor after a finite extension of $K$;
2. away from a finite set of primes there is a smooth model of the pair $(\overline S,D)$;
3. the coefficient systems under consideration arise from finite free $\Lambda$-lattices in algebraic PEL representations and are lisse on $S$;
4. $D$ has a finite stratification on which every finite-level local inertia action is constant up to isomorphism, and the corresponding inertia cohomology vanishes outside one bounded range independent of the level.

Compact quaternionic surfaces have $D=\varnothing$. For noncompact Hilbert or unitary examples, toroidal compactifications provide the normal-crossings boundary after the stated level and field adjustments. The book uses only the four geometric properties above; it does not infer them from the word “Shimura.”

### 16.2 Interior and boundary complexes

Let $\mathcal L=(\mathcal L_n)$ be one of the coefficient systems. At finite level define

$$
R\Gamma_c(S,\mathcal L_n)
=R\Gamma(\overline S,j_!\mathcal L_n),
\qquad
R\Gamma(S,\mathcal L_n)
=R\Gamma(\overline S,Rj_*\mathcal L_n).
$$

For the fixed compactifications here, the first displayed expression is the definition of compactly supported cohomology. The natural map $j_!\mathcal L_n\to Rj_*\mathcal L_n$ gives the boundary triangle

$$
R\Gamma_c(S,\mathcal L_n)
\longrightarrow R\Gamma(S,\mathcal L_n)
\longrightarrow R\Gamma(D,\mathcal B_n)
\longrightarrow,
$$

where

$$
\mathcal B_n=i^*Rj_*\mathcal L_n
$$

is the boundary complex. Its stalk at a smooth boundary point is continuous cohomology of the local inertia group acting on the stalk of $\mathcal L_n$; at a crossing, two inertia directions produce a two-variable local complex. The finite-level local-monodromy hypothesis in Section 16.1 makes these cohomology sheaves constructible.

Define interior cohomology by

$$
H^q_!(S,\mathcal L_n)
=\operatorname{im}\bigl(
H^q_c(S,\mathcal L_n)\to H^q(S,\mathcal L_n)
\bigr).
$$

It is a group, not generally the cohomology of a canonically split direct summand. Boundary classes can form nontrivial extensions with interior classes. Projectors supplied by correspondences may later isolate summands, but degeneration of a boundary sequence alone does not do so.

### 16.3 Finiteness and perfectness

Since $\dim S=2$, every constructible finite coefficient complex above has cohomology only in a uniform finite range; ordinary sheaf cohomology vanishes above degree $4$, and the bounded local-inertia amplitude enlarges the range of $Rj_*\mathcal L_n$ only by its stated finite amount. All groups are finite. The same holds for compact support because $j_!\mathcal L_n$ is constructible on the proper surface.

Taking derived inverse limits defines

$$
R\Gamma_c(S,\mathcal L),
\qquad
R\Gamma(S,\mathcal L),
\qquad
R\Gamma(D,\mathcal B).
$$

Finite-level finiteness makes every cohomology tower Mittag--Leffler, so the boundary triangle survives completion. Normalization and (7.1) identify the mod-$\ell$ reductions of the three continuous complexes with their finite-level counterparts. The complete-DVR lemma therefore makes each complex perfect over $\Lambda$ and its cohomology finitely generated. If $S$ is proper, the boundary complex is zero and ordinary and compactly supported cohomology coincide.

For the constant system on a smooth proper surface, the cohomological range is exactly contained in $[0,4]$. For an open surface, ordinary and compactly supported cohomology are still bounded, but their groups need not agree and boundary contributions can occur in several degrees. A claim that only the middle degree matters requires a separate projector, vanishing theorem, or weight argument; dimension alone does not provide it.

### 16.4 Hecke and Galois actions

A prime-to-level Hecke correspondence is represented by a diagram

$$
S\xleftarrow{p}S'\xrightarrow{q}S
$$

whose arrows are finite étale on the open surface and extend compatibly to the chosen compactifications after refinement. Pullback along $p$ and finite pushforward along $q$ define an endomorphism $q_*p^*$ of finite-level cohomology. Compatibility with reduction gives an action on the integral perfect complex and then on rational cohomology.

The notation includes the coefficient isomorphism $p^*\mathcal L_n\simeq q^*\mathcal L_n$ supplied by the PEL correspondence; without such an isomorphism the diagram does not act on cohomology with coefficients in $\mathcal L_n$.

Because the correspondence and coefficients descend to $K$, Hecke actions commute with the continuous $G_K$-action on geometric cohomology. This commutation is already true at every finite level and survives inverse limit. It is therefore legitimate to take generalized Hecke eigenspaces inside a finite-dimensional $E$-representation of $G_K$.

Two cautions remain. Integral eigenspaces need not be direct summands when eigenvalues are congruent modulo $\ell$; a rational projector can have denominators. And a Hecke correspondence that does not extend cleanly across the boundary may act on ordinary cohomology while requiring additional work on compact support or boundary cohomology. The finite étale open correspondence alone does not settle that extension problem.

## 17. A reusable derived package

### 17.1 The integral theorem

We can now collect the constructions into the form used later.

**Integral geometric cohomology theorem.** Let $k$ be a field, let $X/k$ be one of the following:

- a smooth proper or semistable proper curve;
- an abelian variety of dimension $g$;
- a selected smooth Shimura surface satisfying Section 16.1, with either ordinary or compactly supported cohomology.

Let $\mathcal F=(\mathcal F_n)$ be a normalized bounded constructible $\Lambda$-system on a common finite stratification. For compact support, apply this hypothesis to $(j_!\mathcal F_n)$. Then:

1. $R\Gamma_{\mathrm{cont}}(\bar X,\mathcal F)$ is bounded and derived complete;
2. its cohomology modules are finitely generated over $\Lambda$;
3. it is a perfect $\Lambda$-complex;
4. reduction modulo $\ell^n$ recovers $R\Gamma(\bar X,\mathcal F_n)$;
5. it carries a continuous $G_k$-action compatible with cup products and every finite correspondence defined over $k$ that is equipped with the required coefficient identification.

For a proper curve the sheaf-cohomological range is $[0,2]$, for an abelian variety it is $[0,2g]$, and for a proper surface it is $[0,4]$. A coefficient complex shifts these ranges by its own amplitude. For open surfaces with boundary complexes, add the finite local-inertia amplitude rather than asserting the proper range.

**Proof.** Finite-level boundedness and finiteness are supplied by Chapters 6 and 7. Hence every fixed-degree tower is Mittag--Leffler, so Milnor identifies continuous cohomology with its inverse limit and preserves the uniform range. Equation (7.1) gives derived reduction directly from normalization. In particular the mod-$\ell$ reduction is bounded with finite-dimensional cohomology; the complete-DVR lemma makes the continuous complex perfect and its cohomology finitely generated. The descent action is continuous at every finite level and therefore on the inverse-limit topology. Products and finite traces are compatible levelwise and hence on the normalized limit. $\square$

### 17.2 The rational theorem

**Rational geometric cohomology theorem.** Under the same hypotheses, let $\mathcal V$ be the rational coefficient object obtained from an integral lattice $\mathcal F$. Then

$$
R\Gamma(\bar X,\mathcal V)
=R\Gamma_{\mathrm{cont}}(\bar X,\mathcal F)
\otimes_\Lambda E
$$

is a bounded perfect $E$-complex, independent of the lattice. Every cohomology group is finite-dimensional and carries a continuous $G_k$-action. Cup products, Tate twists, finite-correspondence actions, and any finite-level base-change isomorphisms commute with rationalization.

**Proof.** Commensurable lattices differ by bounded $\ell$-power torsion, which vanishes after tensoring with $E$. A perfect integral representative becomes a bounded complex of finite-dimensional $E$-vector spaces. All structures were constructed on the integral tower, so tensoring transports their identities. $\square$

This theorem does not say that every system of $E$-vector spaces arises from a constructible lattice. The stable-lattice theorem applies to continuous finite-dimensional representations with compact image. Infinite-rank or noncontinuous actions fall outside the category.

### 17.3 A diagnostic checklist

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

### 17.4 Final synthesis

Étale cohomology begins with a simple obstruction: local sections need not glue. The small étale topos supplies the correct neighborhoods, and derived global sections retain every obstruction and connecting map at once. Constructibility turns arbitrary local behavior into finitely many lisse pieces. Cohomological-dimension and finiteness arguments then make the resulting complexes bounded and arithmetically manageable for curves, abelian varieties, and the two-dimensional PEL spaces required here.

The passage to $\ell$-adic coefficients is not a change of symbols. It is a passage from finite sheaves to a normalized inverse system, from ordinary limit to derived limit, and from discrete finite actions to a continuous action on a profinite lattice. The Milnor sequence records the possible defect. In the finite geometric situations of this book, Mittag--Leffler kills that defect, but only after finiteness has been proved.

With these distinctions preserved, the final package is robust. Continuous cohomology is derived complete, reduction returns the finite levels, rationalization is independent of a lattice, Galois actions are continuous, and cup products and correspondences survive every passage. Base-change maps have been constructed in the precise form needed to receive the geometric theorems that follow. The resulting perfect complexes are the natural containers from which arithmetic representations will be extracted.
