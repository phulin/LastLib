# Betti, de Rham, and Étale Comparison for Curves

## Contents

1. [One curve, three realizations](#1-one-curve-three-realizations)
   - [The comparison problem](#11-the-comparison-problem)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [The comparison triangle](#13-the-comparison-triangle)
   - [Normalizations that cannot be suppressed](#14-normalizations-that-cannot-be-suppressed)
2. [Simplicial chains, cochains, and products](#2-simplicial-chains-cochains-and-products)
   - [Finite simplicial complexes, chains, and homology](#21-finite-simplicial-complexes-chains-and-homology)
   - [Cochains and the universal coefficient theorem](#22-cochains-and-the-universal-coefficient-theorem)
   - [Cup products and cap products](#23-cup-products-and-cap-products)
   - [The fundamental class and Poincaré duality](#24-the-fundamental-class-and-poincaré-duality)
   - [Relative groups, compact support, and functoriality](#25-relative-groups-compact-support-and-functoriality)
3. [Compact Riemann surfaces as oriented topological surfaces](#3-compact-riemann-surfaces-as-oriented-topological-surfaces)
   - [Complex orientation and the fundamental class](#31-complex-orientation-and-the-fundamental-class)
   - [The genus calculation](#32-the-genus-calculation)
   - [Intersection and Poincaré duality](#33-intersection-and-poincaré-duality)
   - [Integral lattices and symplectic bases](#34-integral-lattices-and-symplectic-bases)
4. [The analytic de Rham theorem](#4-the-analytic-de-rham-theorem)
   - [Smooth forms and local exactness](#41-smooth-forms-and-local-exactness)
   - [Integration on singular simplices](#42-integration-on-singular-simplices)
   - [The global comparison theorem](#43-the-global-comparison-theorem)
   - [Products, traces, and the surface pairing](#44-products-traces-and-the-surface-pairing)
5. [From algebraic forms to analytic forms](#5-from-algebraic-forms-to-analytic-forms)
   - [Analytification of a smooth projective curve](#51-analytification-of-a-smooth-projective-curve)
   - [Coherent comparison in dimension one](#52-coherent-comparison-in-dimension-one)
   - [Algebraic de Rham comparison](#53-algebraic-de-rham-comparison)
   - [Functoriality and base field extension](#54-functoriality-and-base-field-extension)
6. [Periods, Hodge theory, and rational structures](#6-periods-hodge-theory-and-rational-structures)
   - [The period pairing](#61-the-period-pairing)
   - [Hodge decomposition in degree one](#62-hodge-decomposition-in-degree-one)
   - [The Hodge filtration and the rational lattice](#63-the-hodge-filtration-and-the-rational-lattice)
   - [Period matrices and the bilinear relations](#64-period-matrices-and-the-bilinear-relations)
7. [Finite étale covers and Riemann existence](#7-finite-étale-covers-and-riemann-existence)
   - [Analytification of an étale map](#71-analytification-of-an-étale-map)
   - [Algebraizing finite topological covers](#72-algebraizing-finite-topological-covers)
   - [The Riemann existence theorem](#73-the-riemann-existence-theorem)
   - [Local systems and fundamental groups](#74-local-systems-and-fundamental-groups)
8. [Finite-coefficient Betti--étale comparison](#8-finite-coefficient-betti--étale-comparison)
   - [The comparison morphism](#81-the-comparison-morphism)
   - [Proof for finite local systems](#82-proof-for-finite-local-systems)
   - [Constant coefficients on a proper curve](#83-constant-coefficients-on-a-proper-curve)
   - [Compact supports and punctures](#84-compact-supports-and-punctures)
9. [Passage to integral and rational ℓ-adic cohomology](#9-passage-to-integral-and-rational-ℓ-adic-cohomology)
   - [Inverse limits without hidden terms](#91-inverse-limits-without-hidden-terms)
   - [The integral comparison isomorphism](#92-the-integral-comparison-isomorphism)
   - [Rational coefficients and lattices](#93-rational-coefficients-and-lattices)
   - [What comparison does and does not identify](#94-what-comparison-does-and-does-not-identify)
   - [The coefficient-prime Hodge--Tate bridge](#95-the-coefficient-prime-hodge--tate-bridge)
10. [Cycle classes, twists, and trace normalizations](#10-cycle-classes-twists-and-trace-normalizations)
    - [Divisors in the three theories](#101-divisors-in-the-three-theories)
    - [The factor $2\pi i$](#102-the-factor-2pi-i)
    - [Trace and Poincaré pairings](#103-trace-and-poincaré-pairings)
    - [The first Chern class of a line bundle](#104-the-first-chern-class-of-a-line-bundle)
11. [Maps, correspondences, and Hecke operators](#11-maps-correspondences-and-hecke-operators)
    - [Pullback and transfer](#111-pullback-and-transfer)
    - [Finite correspondences and variance](#112-finite-correspondences-and-variance)
    - [Composition and transpose](#113-composition-and-transpose)
    - [Hecke actions and common characteristic polynomials](#114-hecke-actions-and-common-characteristic-polynomials)
12. [Polarizations and Jacobian period lattices](#12-polarizations-and-jacobian-period-lattices)
    - [The analytic Jacobian](#121-the-analytic-jacobian)
    - [The principal Riemann form](#122-the-principal-riemann-form)
    - [Comparison with cup-product polarizations](#123-comparison-with-cup-product-polarizations)
    - [Isogenies and denominators](#124-isogenies-and-denominators)
13. [Families, horizontal periods, and monodromy](#13-families-horizontal-periods-and-monodromy)
    - [The Betti local system](#131-the-betti-local-system)
    - [Gauss--Manin as the differential of periods](#132-gauss--manin-as-the-differential-of-periods)
    - [Hodge variation and polarization](#133-hodge-variation-and-polarization)
    - [Correspondences in families](#134-correspondences-in-families)
14. [Worked realizations](#14-worked-realizations)
    - [The projective line and the punctured line](#141-the-projective-line-and-the-punctured-line)
    - [A complex elliptic curve](#142-a-complex-elliptic-curve)
    - [A hyperelliptic curve](#143-a-hyperelliptic-curve)
    - [A correspondence sanity check](#144-a-correspondence-sanity-check)
15. [The comparison package](#15-the-comparison-package)
    - [The simultaneous theorem](#151-the-simultaneous-theorem)
    - [Hypothesis and normalization audit](#152-hypothesis-and-normalization-audit)
    - [Conclusion](#153-conclusion)

## 1. One curve, three realizations

A smooth projective curve over a subfield of the complex numbers can be viewed in three very different ways. Its complex points form a compact oriented surface; its algebraic differential forms form a two-term complex; and its finite étale covers support a cohomology theory with finite or ℓ-adic coefficients. Each viewpoint sees a rank-$2g$ object in degree one, but equality of ranks is not comparison. The purpose of this book is to construct the actual isomorphisms and to prove that every geometric operation has the same effect through them.

### 1.1 The comparison problem

Let $K\subseteq\mathbf C$ and let $X/K$ be a smooth, proper, geometrically connected curve. Put $X_{\mathbf C}=X\times_K\mathbf C$ and let $X^{\mathrm{an}}$ be the compact Riemann surface of its complex points. The three degree-one realizations are

$$
H^1_B(X,\mathbf Z)=H^1_{\mathrm{sing}}(X^{\mathrm{an}},\mathbf Z),
$$

$$
H^1_{\mathrm{dR}}(X/K)=\mathbb H^1
\bigl(X,[\mathcal O_X\xrightarrow d\Omega^1_{X/K}]\bigr),
$$

and, for a prime $\ell$,

$$
H^1_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Z_\ell)
=\varprojlim_m H^1_{\mathrm{\acute et}}
(X_{\mathbf C},\mathbf Z/\ell^m\mathbf Z).
$$

The first is an integral lattice with an intersection form. The second is a $K$-vector space with its Hodge filtration. The third is a profinite lattice suited to arithmetic descent. Comparison must explain not only why all have rank $2g$, but also why pullback, trace, cup product, divisor classes, transpose correspondences, and polarizations agree.

There are two different bridges. Integration gives

$$
\operatorname{comp}_{\mathrm{dR},B}:
H^n_{\mathrm{dR}}(X/K)\otimes_K\mathbf C
\xrightarrow{\sim}H^n_B(X,\mathbf Q)\otimes_{\mathbf Q}\mathbf C. \tag{1.1}
$$

Riemann existence and comparison of cohomology give, for every $m\geq1$,

$$
\operatorname{comp}_{B,\mathrm{\acute et},m}:
H^n_B(X,\mathbf Z/\ell^m\mathbf Z)
\xrightarrow{\sim}
H^n_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Z/\ell^m\mathbf Z). \tag{1.2}
$$

Taking inverse limits then gives the integral ℓ-adic comparison. The two bridges have different coefficient fields; there is no canonical isomorphism $\mathbf C\simeq\mathbf Q_\ell$, and no such choice is part of the theory.

### 1.2 Standing hypotheses and notation

Unless a section explicitly treats an open curve, $X$ and $Y$ are smooth, proper, geometrically connected curves over a field embedded in $\mathbf C$. Their complex analytifications are denoted $X^{\mathrm{an}}$ and $Y^{\mathrm{an}}$. The algebraic genus is

$$
g=\dim_K H^0(X,\Omega^1_{X/K});
$$

Books 9 and 46 identify this with $\dim_KH^1(X,\mathcal O_X)$ and show that $H^1_{\mathrm{dR}}(X/K)$ has dimension $2g$.

Under Hypothesis (T), Betti homology and cohomology are computed from the finite simplicial complex $K_X$: we write $H_n(X^{\mathrm{an}},A)$ for $H_n(K_X,A)$ and $H^n_B(X,A)$ for $H^n_B(K_X,A)$, the notation of Section 2.1 making these independent of the chosen triangulation. For a commutative ring $A$, constant coefficients mean the constant sheaf or constant local system associated with $A$. Étale coefficients have order invertible on the curve whenever the ground field has positive characteristic; over $\mathbf C$ this restriction is automatic. We write $\mathbf Z_\ell(1)=\varprojlim_m\mu_{\ell^m}$ and keep this twist visible.

Maps act contravariantly on cohomology. A finite map also has a covariant trace, denoted $f_*$. A finite correspondence

$$
X\xleftarrow{p_1}\Gamma^\nu\xrightarrow{p_2}Y
$$

acts from $X$ to $Y$ by $(p_2)_*p_1^*$. This is the convention already fixed for de Rham and étale cohomology in Books 21 and 46.

### 1.3 The comparison triangle

The shape of the final result is

$$
\begin{array}{ccc}
H^n_{\mathrm{dR}}(X/K)\otimes_K\mathbf C
&\xrightarrow{\ \operatorname{comp}_{\mathrm{dR},B}\ }&
H^n_B(X,\mathbf Q)\otimes_{\mathbf Q}\mathbf C\\
&&\uparrow\\[-6pt]
&&H^n_B(X,\mathbf Z)\otimes\mathbf Q\\
&&\downarrow\\[-6pt]
&&H^n_B(X,\mathbf Z_\ell)\otimes\mathbf Q_\ell
\xrightarrow{\ \operatorname{comp}_{B,\mathrm{\acute et}}\ }
H^n_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Q_\ell).
\end{array} \tag{1.3}
$$

The vertical arrows in the middle express change of coefficients from one integral Betti lattice. They do not identify $\mathbf C$ with $\mathbf Q_\ell$. Thus the Betti lattice is the common rational source, while the de Rham and étale realizations retain their own scalar fields and extra structures.

The construction proceeds in the only logically safe order. We first build simplicial (co)homology together with its universal coefficient theorem, surface duality, and fundamental class—everything reduced to finite combinatorics once Hypothesis (T) supplies a triangulation. We next prove analytic de Rham comparison, then algebraize it. Separately, we prove Riemann existence and finite-coefficient Betti--étale comparison before passing to inverse limits. Only after both bridges exist do we compare traces, cycles, correspondences, and polarizations.

### 1.4 Normalizations that cannot be suppressed

Three normalizations control the formulas.

First, the complex structure orients $X^{\mathrm{an}}$. Its fundamental class $[X]\in H_2(X^{\mathrm{an}},\mathbf Z)$ is positive when a holomorphic coordinate $z=x+iy$ identifies the local orientation with $dx\wedge dy$.

Second, Book 46 normalizes the algebraic de Rham trace so that the de Rham class of a degree-one point has trace $1$. Under unnormalized integration that point class maps to $2\pi i$ times the Betti orientation class. Consequently

$$
\langle\operatorname{comp}_{\mathrm{dR},B}(u),[X]\rangle
=2\pi i\,\operatorname{Tr}_{\mathrm{dR}}(u)
\qquad(u\in H^2_{\mathrm{dR}}(X/\mathbf C)). \tag{1.4}
$$

Third, the étale trace is naturally

$$
H^2_{\mathrm{\acute et}}(X,\mathbf Z_\ell(1))\longrightarrow\mathbf Z_\ell.
$$

Identifying $\mathbf Z_\ell(1)$ with $\mathbf Z_\ell$ requires a compatible choice of ℓ-power roots of unity. We will state canonical comparisons with twisted coefficients and state untwisted matrix formulas only after naming such a choice. These conventions prevent the most common sign and scalar errors later.

## 2. Simplicial chains, cochains, and products

Singular theory defines homology for every space, but for the curves of this book nothing of that generality is ever used: after one triangulation, every group, product, and duality statement we need becomes a finite combinatorial computation that can be carried out completely, with no appeal to unproved comparison machinery. This chapter therefore develops chains, cochains, products, duality, and relative groups on finite simplicial complexes. The universal coefficient theorem, excision, Poincaré duality, and the existence of the fundamental class all become finite combinatorial theorems proved below from first principles. Singular chains are retained for exactly one purpose—integration of differential forms in Chapter 4—and Section 2.1 compares them with simplicial chains once and for all.

**Standing triangulation hypothesis (T).** _Every Riemann surface occurring in this book admits a homeomorphism from the geometric realization of a finite abstract simplicial complex; moreover, whenever two such surfaces are related by a holomorphic map that is an unbranched covering, the homeomorphisms can be chosen so that the covering map pulls each triangle of the source triangulation linearly onto a simplex of a subdivision of the target triangulation._

The status of (T) must be stated plainly. Classically it follows from the theorem of Radó, which identifies Riemann surfaces among all topological surfaces by second countability, together with the theorem that every compact second-countable surface admits a finite triangulation. Neither theorem belongs to algebraic geometry, is proved in any earlier book of this series, or follows from the local analytic constructions used elsewhere in this volume; pretending otherwise would be dishonest. We therefore carry (T) as an explicit standing geometric hypothesis. It enters exactly once as an input, at the definition of the simplicial model in Section 2.1, and every later statement about Betti groups is derived combinatorially from the model rather than from (T). Hypothesis (T), its role, and its boundary are recorded again in the audit of Section 15.2. For open curves obtained by deleting finitely many points from a compact surface, the compatible version of (T) is automatic once the deleted points are made vertices of the compact triangulation.

### 2.1 Finite simplicial complexes, chains, and homology

A finite abstract simplicial complex consists of a finite set $V$ of vertices and a collection $K$ of nonempty subsets of $V$, called simplices, such that every nonempty subset of a simplex is again a simplex. A simplex with $n+1$ vertices has dimension $n$; the dimension of $K$ is the largest simplex dimension. The star of a vertex $v$ is the union of the interiors of the simplices containing $v$. The geometric realization $|K|$ embeds in $\mathbf R^{V}$ as the union of the convex hulls of the simplices; it is a compact polyhedron when $K$ is finite, and each point of $|K|$ lies in the interior of a unique smallest simplex, its carrier.

Because $V$ is finite, we may fix once and for all a total order on $V$. An ordered $n$-simplex is then an $(n+1)$-tuple $(v_0,\ldots,v_n)$ of distinct vertices whose underlying set is a simplex; since the order is fixed, every simplex has exactly one increasing representative, and we use increasing tuples as the standard generators. Let $C_n(K,\mathbf Z)$ be the free abelian group they span, and let $C_n(K,\mathbf Z)=0$ for $n<0$ or $n>\dim K$. The boundary operator is

$$
\partial[v_0,\ldots,v_n]=\sum_{i=0}^n(-1)^i\,[v_0,\ldots,\widehat{v_i},\ldots,v_n].
$$

A direct expansion shows $\partial^2=0$: for fixed $i<j$ the term $v_j$ survives in the $i$th summand and $v_i$ in none of the later ones, so each ordered $(n-2)$-face arises exactly twice, from the pairs $(i,j)$ and $(j,i)$, with opposite signs $(-1)^{i+j}$ and $(-1)^{j+i}$. No cancellation argument over a geometric picture is required—the sign count is literal. A simplicial map $f:K\to L$, that is, a map $V(K)\to V(L)$ carrying simplices to simplices, induces chain maps $f_\#=\sum f(v_i)$ entrywise, and functoriality $(gf)_\#=g_\#f_\#$ holds because both sides reindex tuples identically.

For an abelian group $A$ put $C_n(K,A)=C_n(K,\mathbf Z)\otimes A$ and define

$$
H_n(K,A)=\ker(\partial:C_n\to C_{n-1})\,/\,\operatorname{im}(\partial:C_{n+1}\to C_n).
$$

Since $K$ has finitely many simplices, each $C_n(K,\mathbf Z)$ is a finitely generated free abelian group; kernels and quotients of finitely generated groups are finitely generated, so every $H_n(K,\mathbf Z)$ is a finitely generated abelian group, without any appeal to general structure theorems for manifolds. If $\dim K=d$ then $H_n(K,A)=0$ for $n>d$ because there are no chains above degree $d$. This single sentence will later explain why a curve has no Betti groups above degree two.

It remains to connect this finite model to singular chains on $|K|$, both to justify writing $H_n(X^{\mathrm{an}},A)$ without naming a triangulation and to prepare the integration of Chapter 4. The increasing tuple $(v_0,\ldots,v_n)$ determines an affine map $|\sigma|:\Delta^n\to|K|$, and extending linearly gives an injective chain map
$\iota:C_\bullet^{\triangle}(K)\to C_\bullet(|K|,\mathbf Z)$
from simplicial to singular chains. We claim that $\iota$ induces an isomorphism on homology. The proof uses barycentric subdivision twice, once inside the complex and once inside the singular chains.

First, the barycentric subdivision $\operatorname{sd}K$ of an abstract complex has as vertices the simplices of $K$ and as simplices the strictly increasing chains of simplices of $K$ ordered by inclusion; its realization is naturally homeomorphic to $|K|$ by sending the barycenter of each simplex accordingly. Iterating subdivision makes every simplex of $K$ contain no simplex of $\operatorname{sd}^mK$ larger than a fraction $(m/(m+1))^d$ of its diameter, so meshes tend uniformly to zero.

Second, for singular chains define the subdivision operator $Sd$ inductively: the barycentric subdivision of the standard simplex is a specific linear combination of affine simplices $\Delta^n\to\Delta^n$, and for arbitrary $\sigma:\Delta^n\to T$ one sets $Sd(\sigma)=\sigma_{\#}(Sd(\operatorname{id}))$. Coning over the difference between a chain and its subdivision produces a natural homomorphism $T:C_n(T)\to C_{n+1}(T)$ satisfying the identity dual to the prism identity,

$$
Sd-\operatorname{id}=\partial T-T\partial,
$$

so $Sd$ induces the identity on homology.

Third, the simplicial approximation step. Let $f:|K|\to|L|$ be continuous. The stars of the vertices of $L$ form an open cover of $|L|$, so their preimages cover the compact metric space $|K|$. By the uniform Lebesgue number property, some iterated subdivision $\operatorname{sd}^mK$ has all its stars mapping into stars of $L$; choosing for each vertex $w$ of $\operatorname{sd}^mK$ a vertex $g(w)$ of $L$ with $f(\operatorname{star}(w))\subseteq\operatorname{star}(g(w))$ yields a simplicial map $g:\operatorname{sd}^mK\to L$, defined on a simplex because the images of its vertices span a common simplex of $L$. The straight-line homotopy inside each target star joins $f$ to $|g|$, so by the prism identity (2.1) below, $g_* = f_*$ on homology.

Combining the three steps: given a singular cycle $z$ on $|K|$, apply the approximation to the identity of $|K|$ to obtain, after subdivision, a simplicial chain homotopic to and hence homologous with $z$; conversely, if a simplicial cycle bounds by a singular chain, subdividing the bounding chain until it lies in the image of $\iota$ exhibits a simplicial bounding chain. Therefore $\iota_*:H_n^{\triangle}(K,A)\to H_n(|K|,A)$ is an isomorphism for every coefficient group $A$, natural in simplicial maps.

Two consequences fix notation for the rest of the book. First, under Hypothesis (T), a choice of triangulation identifies $X^{\mathrm{an}}$ with $|K_X|$, and we _define_

$$
H_n(X^{\mathrm{an}},A):=H_n(K_X,A),
$$

the preceding isomorphism showing the result independent of the choice and equal to singular homology; cohomology $H^\bullet_B(X,A)$ will be defined from the same complex in Section 2.2, which justifies the subscript used throughout. Second, if $X^{\mathrm{an}}$ and $Y^{\mathrm{an}}$ carry triangulations $K_X,K_Y$ and $h:|K_X|\to|K_Y|$ is a homeomorphism or more generally any continuous map, applying approximation to $h$ and to a homotopy inverse expresses $H_n(K_X,A)\cong H_n(K_Y,A)$ compatibly with induced maps; in particular homology is a homotopy invariant of the surface. Finally, the prism construction itself belongs to the singular side: for a homotopy $F$ from $f_0$ to $f_1$, subdividing $\Delta^n\times[0,1]$ into $(n+1)$ oriented simplices defines $P_n:C_n(T)\to C_{n+1}(U)$ with

$$
\partial P+P\partial=(f_1)_*-(f_0)_*. \tag{2.1}
$$

We shall need (2.1) only through the two uses above—the smooth approximation of Chapter 4 and the homotopies in the approximation argument—and everything else in this chapter is proved purely inside the finite complex $K_X$.

### 2.2 Cochains and the universal coefficient theorem

For an abelian group $A$ define the simplicial cochain group

$$
C^n(K,A)=\operatorname{Hom}_{\mathbf Z}(C_n(K,\mathbf Z),A),
\qquad d\varphi=\varphi\circ\partial,
$$

so that $d^2=0$ because $\partial^2=0$, and define $H^n_B(K,A)=H^n(C^\bullet(K,A))$. Evaluation of cochains on chains satisfies $\langle d\varphi,c\rangle=\langle\varphi,\partial c\rangle$ by construction; consequently cocycles pair with cycles, coboundaries vanish on boundaries, and evaluation descends to a bilinear pairing $\langle-,-\rangle:H^n_B(K,A)\otimes H_n(K,\mathbf Z)\to A$. Pullback along simplicial maps makes cohomology contravariantly functorial.

The universal coefficient theorems for these complexes are statements of finite linear algebra over $\mathbf Z$, valid in complete generality—no torsion-freeness is assumed anywhere. Write $Z_n=\ker\partial_n$ and $B_n=\operatorname{im}\partial_{n+1}$, so that $H_n=Z_n/B_n$ and $B_n\subseteq Z_n$. We use once, as a standing lemma of basic algebra, that every subgroup of a free abelian group is free; hence every $Z_n$ and every $B_n$ is free. Two exact sequences govern everything:

$$
0\longrightarrow Z_n\longrightarrow C_n\xrightarrow{\ \partial_n\ }B_{n-1}\longrightarrow0,
\tag{2.2a}
$$

which splits because its right term is free, and

$$
0\longrightarrow B_n\longrightarrow Z_n\longrightarrow H_n\longrightarrow0,
\tag{2.2b}
$$

which is the definition of $H_n$ together with freeness of its two subgroups.

**Universal coefficient theorem.** _For every abelian group $A$ there are natural short exact sequences_

$$
0\longrightarrow H_n(K,\mathbf Z)\otimes A\longrightarrow H_n(K,A)\longrightarrow\operatorname{Tor}_{\mathbf Z}(H_{n-1}(K,\mathbf Z),A)\longrightarrow0
$$

_and_

$$
0\longrightarrow\operatorname{Ext}^1_{\mathbf Z}(H_{n-1}(K,\mathbf Z),A)\longrightarrow H^n_B(K,A)\xrightarrow{\ e\ }\operatorname{Hom}_{\mathbf Z}(H_n(K,\mathbf Z),A)\longrightarrow0,
\tag{2.2}
$$

_where $e$ sends a cohomology class to its evaluation on integral cycles._

_Proof._ The homological sequence comes from viewing (2.2a) as a levelwise-split short exact sequence of complexes, after equipping $Z_\bullet$ with zero differentials and reindexing the boundary images so that the term in degree $n$ of the third complex is $B_{n-1}$. Tensoring with $A$ preserves exactness because $\operatorname{Tor}(B_{n-1},A)=0$ for free $B_{n-1}$, so we may tensor and take the long exact sequence. Since both flanking complexes have zero differential, that long exact sequence contains the segment

$$
B_n\otimes A\xrightarrow{\ \iota_*\ }Z_n\otimes A\longrightarrow H_n(K,A)
\longrightarrow B_{n-1}\otimes A\xrightarrow{\ \iota_*\ }Z_{n-1}\otimes A,
$$

where $\iota$ denotes the inclusions $B_n\hookrightarrow Z_n$ supplied by (2.2b). Applying $-\otimes A$ to (2.2b) at levels $n$ and $n-1$ yields

$$
0\to\operatorname{Tor}(H_n,A)\to B_n\otimes A\to Z_n\otimes A\to H_n\otimes A\to0,
$$

so the image of the left map in the segment, namely $(Z_n\otimes A)/\operatorname{im}(\iota_*)$, identifies with $H_n\otimes A$, and the image of the right-hand surjection out of $H_n(K,A)$ identifies with $\ker(\iota_*)=\operatorname{Tor}(H_{n-1},A)$. Exactness of the segment therefore produces the homological universal coefficient sequence, naturally in $K$ and $A$.

For cohomology, let $r:C^n(K,A)\to\operatorname{Hom}_{\mathbf Z}(Z_n,A)$ be restriction of functionals. Three observations give (2.2).

First, a cochain $\varphi$ is a cocycle precisely when $\varphi$ vanishes on $B_n$; and every functional $\psi:Z_n\to A$ vanishing on $B_n$ extends to such a cocycle—split (2.2a) as $C_n=Z_n\oplus E_n$ and extend by zero on $E_n$. Hence restriction identifies cocycles with functionals on $Z_n$ killing $B_n$, that is, with $\operatorname{Hom}_{\mathbf Z}(H_n,A)$; since coboundaries vanish on $Z_n$, evaluation on cycles descends to a surjection
$e:H^n_B(K,A)\twoheadrightarrow\operatorname{Hom}_{\mathbf Z}(H_n(K,\mathbf Z),A)$,
natural in $K$ and $A$.

Second, the kernel of $e$ consists of classes of cocycles vanishing on all of $Z_n$. Such a $\varphi$ factors uniquely through the surjection $\partial_n:C_n\twoheadrightarrow B_{n-1}$: define $\lambda_\varphi:B_{n-1}\to A$ by $\lambda_\varphi(\partial c)=\varphi(c)$, which is well defined because $\partial c=\partial c'$ forces $c-c'\in Z_n$. Conversely, for every $\lambda:B_{n-1}\to A$ the cochain $\lambda\circ\partial_n$ is a cocycle vanishing on $Z_n$, because $\partial^2=0$. Under this correspondence a coboundary $d\chi=\chi\circ\partial_n$ is sent to the restriction $\chi|_{B_{n-1}}$. Therefore

$$
\ker(e)\;\cong\;\operatorname{Hom}_{\mathbf Z}(B_{n-1},A)\Big/\operatorname{im}\bigl(\operatorname{Hom}_{\mathbf Z}(C_{n-1},A)\xrightarrow{\rho}\operatorname{Hom}_{\mathbf Z}(B_{n-1},A)\bigr),
$$

with $\rho$ the restriction map.

Third, the image of $\rho$ equals the image of restriction from $Z_{n-1}$ instead of $C_{n-1}$: one inclusion is obvious, and conversely every functional on $Z_{n-1}$ extends to $C_{n-1}$ by the splitting of (2.2a) at level $n-1$, extensions agreeing with the original on $B_{n-1}\subseteq Z_{n-1}$. Now apply $\operatorname{Hom}_{\mathbf Z}(-,A)$ to the free presentation (2.2b) at level $n-1$. Since $\operatorname{Ext}^1_{\mathbf Z}(Z_{n-1},A)=0$—the group $Z_{n-1}$ is free—we obtain the exact sequence

$$
0\to\operatorname{Hom}_{\mathbf Z}(H_{n-1},A)\to\operatorname{Hom}_{\mathbf Z}(Z_{n-1},A)
\xrightarrow{\rho'}\operatorname{Hom}_{\mathbf Z}(B_{n-1},A)
\to\operatorname{Ext}^1_{\mathbf Z}(H_{n-1},A)\to0.
$$

The displayed cokernel of $\rho'$ is thus $\operatorname{Ext}^1_{\mathbf Z}(H_{n-1}(K,\mathbf Z),A)$, canonically, this being the standard free-resolution presentation of Ext. Chaining the three observations gives (2.2). Naturality holds throughout: $e$ is evaluation on cycles and the kernel identification passes through the canonical presentation (2.2b), both functorial under pullback along simplicial maps. $\square$

Neither sequence need split naturally, and we shall never use a splitting. For reference, the end terms are the classical torsion corrections: if $H_{n-1}$ contains a cyclic summand of order $m$ then $\operatorname{Ext}^1_{\mathbf Z}(\mathbf Z/m,A)=A/mA$ and $\operatorname{Tor}_{\mathbf Z}(\mathbf Z/m,A)=\ker(A\xrightarrow{\times m}A)$, and these account for every deviation of (2.2) and of its homological companion from being isomorphisms.

For the curves of this book no correction ever occurs. The genus calculation of Section 3.2 exhibits the integral homology of a compact orientable surface explicitly as $\mathbf Z$, $\mathbf Z^{2h}$, and zero above degree two—in particular it is torsion-free—so both correction terms vanish and (2.2) collapses to the canonical evaluation isomorphism

$$
H^n_B(T,A)\simeq\operatorname{Hom}_{\mathbf Z}(H_n(T,\mathbf Z),A). \tag{2.3}
$$

Reduction modulo $n$, extension of coefficients to a ring, and passage to inverse limits therefore act entrywise on these Hom groups, and the Betti groups with finite or ℓ-adic coefficients used below inherit their structure from one finitely generated integral lattice without hidden derived terms.

### 2.3 Cup products and cap products

The Alexander--Whitney diagonal sends an $n$-simplex to the sum of its front-back splittings, the two pieces sharing the middle vertex:

$$
\operatorname{AW}(\sigma)=
\sum_{p+q=n}
(\sigma|[v_0,\ldots,v_p])\otimes
(\sigma|[v_p,\ldots,v_n]).
$$

Here $\sigma|[u]$ denotes the face of $\sigma$ spanned by the listed vertices, with their induced order, so that the first factor has dimension $p$ and the second $n-p$. A term-by-term expansion of boundaries proves that AW is a chain map $C_n(K)\to C_\bullet(K)\otimes C_\bullet(K)$: applying $\partial$ to a splitting produces one boundary piece in the left factor and, with the tensor sign $(-1)^p$, one in the right, and these are exactly the splittings contributed by $\operatorname{AW}(\partial\sigma)$; every other term cancels pairwise. This single finite identity is what makes all products below compatible with cohomology.

For cochains $a\in C^p(K,R)$ and $b\in C^q(K,R)$ with values in a commutative ring $R$, define

$$
(a\smile b)(\sigma)=a\bigl(\sigma|[v_0,\ldots,v_p]\bigr)\cdot b\bigl(\sigma|[v_p,\ldots,v_n]\bigr),
$$

that is, $a\smile b$ is the composite of AW with evaluation of $a$ on the left tensor factor and $b$ on the right. Because AW is a chain map and the differential on Hom out of a tensor product splits over the two factors, expanding faces gives the Leibniz rule

$$
d(a\smile b)=da\smile b+(-1)^pa\smile db. \tag{2.4}
$$

In particular the cup product of cocycles is a cocycle, and changing a factor by a coboundary changes the product by a coboundary; so cup product descends to $H^\bullet_B(K,R)$, where it is associative because AW is coassociative on the nose—regrouping the same triple splittings—and graded-commutative up to the canonical homotopy supplied by the acyclic-model argument: both AW and the flipped composite are natural chain approximations of the diagonal of the standard simplices, which are contractible, so they are naturally chain homotopic, and naturality transports the homotopy to every complex.

Cap product evaluates the front part of a simplex against a cochain and retains the back part: for $c\in C_n(K,\mathbf Z)$ and $a\in C^p(K,A)$,

$$
c\frown a=\sum_{\sigma} m_\sigma\;\bigl(a(\sigma|[v_0,\ldots,v_p])\bigr)\;\sigma|[v_p,\ldots,v_n]
\quad\text{when } c=\sum_\sigma m_\sigma\sigma,
$$

a chain of degree $n-p$. The boundary behavior of cap is governed by the following lemma, proved by the same face-by-face expansion as for AW; it is the only cap identity used anywhere below.

**Lemma (cap boundary formula).** _If $c$ is an integral chain and $a$ is a cochain of degree $p$, then_

$$
\partial(c\frown a)=(-1)^p\bigl((\partial c)\frown a-c\frown da\bigr).
$$

_Proof._ Both sides are additive in $c$, so it suffices to check the identity on a single ordered simplex $\sigma=[v_0,\ldots,v_n]$. Write $\Phi=a(\sigma|[v_0,\ldots,v_p])$ and, for $j\leq p$, let $\varphi_j=a([v_0,\ldots,\widehat{v_j},\ldots,v_p])$. The left side is

$$
\partial(\sigma\frown a)=\Phi\sum_{i=p}^{n}(-1)^{i-p}\,\sigma|[v_p,\ldots,\widehat{v_i},\ldots,v_n].
$$

On the right, each face $F_j=[v_0,\ldots,\widehat{v_j},\ldots,v_n]$ of $\sigma$ contributes through its own front $(p+1)$-face: for $j\leq p$ that front face is $[v_0,\ldots,\widehat{v_j},\ldots,v_{p+1}]$ with value $\varphi_j$, and the retained back part is $[v_{p+1},\ldots,v_n]$; for $j>p$ the front face is $[v_0,\ldots,v_p]$ with value $\Phi$ and the retained back part is $[v_p,\ldots,\widehat{v_j},\ldots,v_n]$. Hence

$$
(\partial\sigma)\frown a=\sum_{j\leq p}(-1)^j\varphi_j\,[v_{p+1},\ldots,v_n]
+\sum_{j>p}(-1)^j\Phi\,[v_p,\ldots,\widehat{v_j},\ldots,v_n].
$$

Since $\sigma\frown da=(da)([v_0,\ldots,v_{p+1}])\cdot[v_{p+1},\ldots,v_n]$ and $(da)([v_0,\ldots,v_{p+1}])=\sum_{j\leq p}(-1)^j\varphi_j+(-1)^{p+1}\Phi$, subtracting cancels the $\varphi_j$-terms of the two sums over $j\leq p$ identically and leaves for the face $[v_{p+1},\ldots,v_n]$ the single coefficient $(-1)^p\Phi$ after multiplication by $(-1)^p$, while each face $[v_p,\ldots,\widehat{v_j},\ldots,v_n]$ with $j>p$ carries $(-1)^{p+j}\Phi$. The result is

$$
(-1)^p\sum_{j>p}(-1)^j\Phi\,[v_p,\ldots,\widehat{v_j},\ldots,v_n]
=\Phi\sum_{j>p}(-1)^{j-p}[v_p,\ldots,\widehat{v_j},\ldots,v_n],
$$

which together with the surviving term $\Phi[v_{p+1},\ldots,v_n]$ (the case $i=p$) reproduces the left side. $\square$

Two consequences fix the interaction of products with classes. First, if $z$ is a cycle then $\partial(z\frown a)=\pm z\frown da$ vanishes whenever $da=0$, and replacing $a$ by $a+db$ changes $z\frown a$ by a boundary; capping therefore descends to bilinear pairings

$$
\frown\colon H_n(K,\mathbf Z)\otimes H^p(K,A)\longrightarrow H_{n-p}(K,A).
$$

Second, evaluation is compatible with both products at once—and here no computation is needed, only the definitions: evaluating $b$ on the chain $z\frown a$ reads off $b$ on the same back faces on which $a$ was evaluated, so for every cycle $z$,

$$
\langle b,\;z\frown a\rangle=\langle a\smile b,\;z\rangle,
$$

the adjunction between cap and cup on which every pairing comparison in this book rests.

### 2.4 The fundamental class and Poincaré duality

Everything so far concerned an arbitrary finite complex. We now specialize to dimension two, where the duality theory can be built by hand, cell by cell, and proved completely; this is the last remaining input the comparison chain will consume.

A finite two-dimensional complex $K$ is a _combinatorial surface_ when every edge is contained in exactly two faces and the link of every vertex is a circle: listing the edges and faces containing $v$ in the order in which they meet around $v$, the sequence closes up after one tour and visits each face once. A combinatorial surface is homeomorphic to a closed topological surface, and under Hypothesis (T) every compact curve in this book has such a model. An orientation of a face is an ordering of its three vertices up to even permutation; it induces an orientation on each of its boundary edges. The complex $K$ is _orientable_ when orientations of all faces can be chosen so that along every shared edge the two induced orientations are opposite. If orientations are chosen arbitrarily on one face after another, each crossing of a shared edge forces the unique flip; orientability means that propagating around every closed loop of adjacent faces returns to the starting orientation. For connected $K$ a compatible choice, if it exists, has exactly two variants, differing by a global sign.

**Lemma (fundamental class).** _Let $K$ be a connected combinatorial surface._

_(i) If $K$ is orientable and $(\varepsilon_F)$ is a compatible choice of face signs, then $z=\sum_F\varepsilon_F[F]$ is an integral cycle, every integral two-cycle is an integral multiple of $z$, and $H_2(K,\mathbf Z)\cong\mathbf Z\,z$._

_(ii) If $K$ is not orientable then $H_2(K,\mathbf Z)=0$._

_Proof._ Compatibility says precisely that the two occurrences of each edge in $\partial z$ cancel, so $\partial z=0$. Conversely let $w=\sum_Fa_FF$ be any cycle. On an edge shared by faces $F,G$ write $s_F,s_G\in\{\pm1\}$ for the signs with which they induce a fixed orientation of that edge; the vanishing of the edge coefficient reads $a_Fs_F+a_Gs_G=0$. If $K$ is orientable and $(\varepsilon_F)$ is compatible, then $s_G=-s_F$ for adjacent faces after comparing against the $\varepsilon$, so the relation forces $a_G=a_F$ along every edge; connectedness propagates equality across all faces and $w=a\cdot z$. This shows the cycles are exactly the multiples of $z$, whence $H_2=\mathbf Z z$. If $K$ is not orientable, some loop of adjacent faces returns with $s$ flipped, and the same relations force $a=-a$ for the common value, hence $a=0$ and there are no cycles at all. □

**Dual cells.** Fix an oriented connected closed combinatorial surface $K$. Place at the barycenter $m_\sigma$ of each simplex $\sigma$—for a vertex, $m_v=v$ itself—the following dual cells, drawn inside $|K|$:

- to each face $F$, the point $D(F):=\{m_F\}$;
- to each edge $e$ bordered by faces $F^+,F^-$, the open segment $D(e)$ from $m_{F^-}$ through $m_e$ to $m_{F^+}$, endpoints removed;
- to each vertex $v$, the open polygon $D(v)$ obtained as the union of the triangles $(v,m_e,m_F)$ over all flags $v\subset e\subset F$, boundary removed.

These cells are pairwise disjoint and their closures partition $|K|$; they turn $|K|$ into a finite cell complex $K^\ast$ whose $p$-cells correspond bijectively to the $(2-p)$-simplices of $K$. Orient each dual edge transversally to its edge so that, at the crossing point, the orientation of $D(e)$ followed by that of $e$ gives the chosen orientation of $K$; give each $D(v)$ the resulting boundary-compatible orientation. Writing $C_p(K^\ast,\mathbf Z)$ for the cellular chains, addition of these orientations identifies $C_p(K^\ast,\mathbf Z)=\bigoplus_{\dim\sigma=2-p}\mathbf Z\,D(\sigma)$ canonically with the group underlying $C^{2-p}(K,\mathbf Z)$. Let
$\Theta:C^{2-p}(K,\mathbf Z)\to C_p(K^\ast,\mathbf Z)$
send a cochain $\varphi$ to the chain $\sum_\sigma\varphi(\sigma)D(\sigma)$.

**Lemma (dual boundary formula).** _With the orientations just prescribed,_ $\partial\,\Theta(\varphi)=-\,\Theta(d\varphi)$ _for $\varphi\in C^{1}(K,\mathbf Z)$ and $\varphi\in C^{0}(K,\mathbf Z)$; in degree two both sides vanish identically._

_Proof._ Degree two: $C_3(K^\ast)=0$ and $d$ on $C^2$ lands in $C^3=0$. Edge case, $\varphi\in C^1$: the closure of $D(e)$ meets the closures of exactly two dual points, $m_{F^+}$ and $m_{F^-}$, and the transversal orientation rule attaches to them the coefficients $\pm1$ according as $F^\pm$ does or does not induce the prescribed orientation on $e$—which are exactly the incidences entering $(d\varphi)(e)=\varphi(\partial e)$ collected with the opposite sign. Vertex case, $\varphi\in C^0$: the boundary of the polygon $D(v)$ passes once through each dual edge $D(e)$ with $e\ni v$, and collecting over the two endpoint stars of each edge $e=[u,v]$ reproduces, with sign minus the incidence of the endpoint in $e$, the quantity $(d\varphi)(e)=\varphi(v)-\varphi(u)$. Both inspections are local pictures with two cells and no hidden terms. □

**Poincaré duality theorem.** _Let $K$ be a connected closed orientable combinatorial surface with fundamental class $z$, and let $A$ be any abelian group. Then capping with $z$ gives isomorphisms_

$$
z\frown-\;:\;H^p(K,A)\xrightarrow{\ \sim\ }H_{2-p}(K,A)
\qquad(p=0,1,2). \tag{2.5}
$$

_Proof._ By the dual boundary formula, $\Theta$ followed by multiplication with the fixed sign is an isomorphism of chain complexes between $C^{2-\bullet}(K,A)$ and $C_\bullet(K^\ast,A)$—tensoring with $A$ is harmless because both sides are free abelian levelwise and the identification is levelwise. Hence $H_p(K^\ast,A)\cong H^{2-p}(K,A)$. Since $|K^\ast|=|K|$ as spaces, literally the same polyhedron, the identity map is a homeomorphism and $H_p(K^\ast,A)\cong H_p(K,A)$. Composing yields isomorphisms $\Psi:H^{2-p}(K,A)\xrightarrow{\sim}H_p(K,A)$. It remains to identify $\Psi(a)$ with $z\frown a$. Both constructions are natural in $a$, and on generators they agree cell by cell: capping the fundamental cycle against a cochain supported on a single simplex retains precisely the dual cell of that simplex with the orientation prescribed above, because the front-face evaluation selects the incidence of $\sigma$ in $z$ and the retained back part is carried by the corresponding block. Hence $\Psi(a)=z\frown a$ for every cocycle, proving (2.5). $\square$

Three corollaries record what the later chapters consume.

First, taking $p=2$: evaluation on the fundamental class identifies $H^2(K,\mathbf Z)$ with $H_0(K,\mathbf Z)$, hence with $\mathbf Z$ for connected $K$; more generally $H^2(K,A)\cong A$ canonically via $z$.

Second, combining (2.5) in degree one with the universal coefficient theorem (2.2) and the torsion-freeness of $H_1$ supplied by the explicit genus calculation of Section 3.2, the cup-evaluation pairing

$$
H^1(K,\mathbf Z)\otimes H^1(K,\mathbf Z)\longrightarrow\mathbf Z,
\qquad
(\alpha,\beta)\longmapsto\langle\alpha\smile\beta,z\rangle
$$

is unimodular: indeed it equals $\langle\beta,z\frown\alpha\rangle$ by the adjunction of Section 2.3, and as $\beta$ ranges over cohomology these functionals run through all of $\operatorname{Hom}(H_1(K,\mathbf Z),\mathbf Z)$, a lattice in which every primitive vector is realized because $H_1$ is finitely generated free. This is the integral perfectness used for symplectic bases in Section 3.4.

Third, capping with $z$ also identifies cohomology with homology after any change of coefficients simultaneously on both sides, so no distinction between cohomological and homological lattices ever survives to Chapter 9's ℓ-adic comparison.

### 2.5 Relative groups, compact support, and functoriality

Let $L\subseteq K$ be a subcomplex. The quotient $C_n(K,L;\mathbf Z):=C_n(K,\mathbf Z)/C_n(L,\mathbf Z)$ is again a finite free complex, and its homology $H_n(K,L;A)=H_n(C_\bullet(K,L)\otimes A)$ fits into the long exact sequence of the pair, constructed termwise from the short exact sequence of complexes $0\to C_\bullet(L)\to C_\bullet(K)\to C_\bullet(K,L)\to0$. Relative cochains are the functionals vanishing on all simplices of $L$, that is, $\operatorname{Hom}(C_\bullet(K)/C_\bullet(L),A)$, and because the quotient complex still consists of finitely generated free groups, the universal coefficient theorem (2.2) holds verbatim for pairs.

Excision, in the finite form in which this book uses it, is now a one-line computation rather than an axiom. The quotient polyhedron $|K|/|L|$ inherits from $K$ a cell structure whose cellular chains are literally $C_\bullet(K)/C_\bullet(L)$, so for $|L|\neq\emptyset$

$$
H_n(K,L;\mathbf Z)\cong\widetilde H_n(|K|/|L|,\mathbf Z);
$$

whenever a pair of spaces $(T,Z)$ is realized as $(|K|,|L|)$ after subdivision—as happens for a compact curve and a union of deleted points made into vertices—the relative groups depend only on the quotient and are computable inside the complex. Concretely, let $X$ be a compact surface with triangulation $K$ in which a finite set $P$ of points consists of vertices, and put $U=X\setminus P$ and $K_P:=K\setminus\bigcup_{p\in P}\operatorname{star}^{\circ}(p)$, a closed subcomplex included in $U$. The stars give a deformation retraction of $U$ onto $K_P$, and we _define_ compactly supported cohomology by

$$
H_c^n(U,A):=H^n(K,K_P;A),
$$

which reproduces

$$
H_c^n(U,A)\simeq H^n(T,Z;A) \tag{2.6}
$$

for any pair realization as above. This is the topological counterpart of extension by zero in étale cohomology. Capping the fundamental class of $K$ with relative cocycles—whose coboundaries vanish modulo $K_P$—and using the dual-cell method of Section 2.4 unchanged near the deleted points, where the vertex-stars simply acquire boundary circles, yields compact-support duality $H_c^p(U,A)\cong H_{2-p}(U,A)$; Chapter 8 consumes exactly these groups.

A proper map induces pullback on compactly supported cohomology through functoriality of the pairs. A finite unbranched covering $f:T\to U$ of degree $d$ between surfaces with triangulations compatible as in Hypothesis (T) may be assumed simplicial after subdividing the source. Then every simplex $\sigma$ of $U$ lifts to exactly $d$ simplices of $T$, the chain-level composite $f_\#\circ f^\#$ multiplies each simplex by $d$, and therefore

$$
f_*f^*=d
$$

on homology and on the adjoint cohomological trace, where $f_*$ denotes pushforward of chains. The projection formula holds already on lifted simplices:

$$
f_*(f^*a\smile b)=a\smile f_*b. \tag{2.7}
$$

For a branched holomorphic map $f:T\to U$ of compact Riemann surfaces, define the cohomological pushforward without choosing lifts by Poincaré duality:

$$
f_*^{\mathrm{coh}}=\operatorname{PD}_U^{-1}
\circ f_*^{\mathrm{hom}}\circ\operatorname{PD}_T,
$$

with the duality isomorphisms of (2.5). On the complement of the branch values this is the sum over sheets, because there $f$ is a covering and the preceding paragraph applies. A small positive disc about a branch value pulls back with total local degree $d$, so the definition extends the covering trace and gives the same formulas with $d$ equal to the algebraic degree.

## 3. Compact Riemann surfaces as oriented topological surfaces

The complex structure contributes more than differentiability: it chooses an orientation and splits complex one-forms into holomorphic and antiholomorphic directions. Before exploiting that splitting, we determine the integral topology on which all later rational and ℓ-adic structures rest.

### 3.1 Complex orientation and the fundamental class

If $z=x+iy$ and $w=u+iv$ are overlapping holomorphic coordinates, the real Jacobian determinant of $w$ as a function of $z$ is $|dw/dz|^2>0$. Hence all holomorphic charts induce the same orientation of the real surface $X^{\mathrm{an}}$: the complex structure chooses an orientation once and for all. By Hypothesis (T) we may fix a finite triangulation $K_X$ of $X^{\mathrm{an}}$; refining it if necessary, each closed triangle lies inside a single holomorphic chart, and transporting the complex orientation to its three vertices orients every face compatibly, so that adjacent faces induce opposite orientations on their shared edge. In the language of Section 2.4, $K_X$ is an orientable connected combinatorial surface with a chosen orientation.

The fundamental-class lemma of Section 2.4 now applies verbatim: the oriented sum

$$
[X]=\sum_F\varepsilon_F[F]\;\in\;H_2(K_X,\mathbf Z)=H_2(X^{\mathrm{an}},\mathbf Z)
$$

is a cycle, generates $H_2(X^{\mathrm{an}},\mathbf Z)$, and is unique up to overall sign among nonzero cycles; choosing the other variant replaces $[X]$ by $-[X]$, which corresponds to reversing the surface orientation and never occurs as long as the complex structure is held fixed. The complex orientation also fixes that sign canonically: at every point the local homology is $\mathbf Z$, generated by a small positively oriented triangle, and $[X]$ maps to the positive generator in each local homology group. This characterizes $[X]$ uniquely.

Connectedness gives $H_0(X^{\mathrm{an}},\mathbf Z)=\mathbf Z$. Poincaré duality (2.5) then identifies $H^2$ with $H_0$, so $H_2(X^{\mathrm{an}},\mathbf Z)=\mathbf Z[X]$ with no additional argument, and there is no homology above degree two because the complex $K_X$ has no cells above dimension two.

### 3.2 The genus calculation

A connected closed oriented surface of topological genus $h$ has a CW decomposition with one vertex, $2h$ oriented one-cells

$$
a_1,b_1,\ldots,a_h,b_h,
$$

and one two-cell attached along

$$
[a_1,b_1]\cdots[a_h,b_h].
$$

After abelianization the cellular boundary of the two-cell is zero, as is the boundary from the one-cells to the unique vertex. Therefore

$$
H_0\simeq\mathbf Z,\qquad
H_1\simeq\mathbf Z^{2h},\qquad
H_2\simeq\mathbf Z. \tag{3.1}
$$

For a compact Riemann surface arising from a smooth projective curve, Chapter 6 will prove

$$
H^1_B(X,\mathbf C)
=H^{1,0}(X)\oplus H^{0,1}(X),
$$

with both summands of dimension equal to the algebraic genus $g$. Comparing (3.1) after tensoring with $\mathbf C$ shows $h=g$. This avoids assuming in advance that the analytic and algebraic notions of genus coincide.

The Euler characteristic is consequently

$$
\chi(X^{\mathrm{an}})=2-2g. \tag{3.2}
$$

Removing $r$ points replaces the top cell by $r$ boundary circles with one relation and gives $\chi_c=2-2g-r$, matching the étale calculation of Book 21.

### 3.3 Intersection and Poincaré duality

Represent two classes in $H_1(X,\mathbf Z)$ by oriented embedded one-cycles meeting transversely. Define their intersection number by summing $+1$ or $-1$ according as the ordered tangent directions agree or disagree with the surface orientation. A small isotopy makes intersections transverse. The boundary of an oriented two-chain has zero total intersection with a closed one-cycle, so the number depends only on homology classes.

For the standard loops one may arrange

$$
a_i\cdot a_j=b_i\cdot b_j=0,\qquad
a_i\cdot b_j=\delta_{ij},\qquad
b_j\cdot a_i=-\delta_{ij}. \tag{3.3}
$$

Thus intersection is alternating and unimodular. Under Poincaré duality it corresponds to cup product followed by evaluation on $[X]$:

$$
Q_B(\alpha,\beta)
=\langle\alpha\smile\beta,[X]\rangle,\qquad
\alpha,\beta\in H^1_B(X,\mathbf Z). \tag{3.4}
$$

To check the sign, take $\alpha_i,\beta_i$ dual to $a_i,b_i$. With the orientation of (3.3), $\langle\alpha_i\smile\beta_j,[X]\rangle=\delta_{ij}$. The matrix of $Q_B$ is therefore

$$
J=\begin{pmatrix}0&I_g\\-I_g&0\end{pmatrix}. \tag{3.5}
$$

Its determinant is $1$, which proves the integral perfectness rather than only nondegeneracy over a field.

### 3.4 Integral lattices and symplectic bases

The group

$$
H^1_B(X,\mathbf Z)=\operatorname{Hom}(H_1(X,\mathbf Z),\mathbf Z)
$$

is a free rank-$2g$ lattice. Any unimodular alternating form on a free abelian group admits a symplectic basis. The proof is integral induction: choose a primitive vector $e$; unimodularity supplies $f$ with $Q(e,f)=1$; the span $\mathbf Ze\oplus\mathbf Zf$ splits off orthogonally; repeat on its orthogonal complement. Applied to (3.4), this recovers the dual basis above without choosing a polygon presentation.

For any ring $A$, freeness and (2.3) give

$$
H^1_B(X,A)=H^1_B(X,\mathbf Z)\otimes A\simeq A^{2g}. \tag{3.6}
$$

The pairing remains perfect after base change. In particular the $\mathbf Z_\ell$-module obtained from singular cohomology is literally the completion of one integral lattice, a fact that will make the ℓ-adic comparison transparent.

## 4. The analytic de Rham theorem

Singular classes are defined by continuous simplices, while differential forms are local analytic objects. Integration is the only plausible bridge. The difficulty is proving that it loses neither global gluing classes nor torsion-free topological information. Local exactness and fine sheaves solve the problem.

### 4.1 Smooth forms and local exactness

Let $M$ be a smooth manifold and let $\mathcal A^p_M$ be the sheaf of complex-valued smooth $p$-forms. Exterior differentiation makes

$$
0\longrightarrow\mathbf C_M
\longrightarrow\mathcal A^0_M\xrightarrow d\mathcal A^1_M
\xrightarrow d\mathcal A^2_M\longrightarrow\cdots. \tag{4.1}
$$

This sequence is exact. In degree zero, a function with zero differential is locally constant. For positive degrees it is enough to work on a star-shaped ball. Let $E=\sum x_i\partial/\partial x_i$ and let $h_t(x)=tx$. For a $p$-form $\omega$ with $p>0$, set

$$
K\omega=\int_0^1 t^{p-1}h_t^*(\iota_E\omega)\,dt.
$$

Differentiation under the integral and Cartan's formula give

$$
dK+Kd=\operatorname{id}-h_0^*. \tag{4.2}
$$

The last term vanishes in positive degree, so every closed form is locally exact. This is the smooth Poincaré lemma.

Each $\mathcal A^p_M$ is fine: a locally finite smooth partition of unity subordinate to any open cover gives endomorphisms supported in the cover and summing to the identity. Fine sheaves have no higher sheaf cohomology; the standard contracting homotopy multiplies a Čech cochain by the partition functions and sums. Hence global sections of (4.1) compute sheaf cohomology of the constant sheaf.

### 4.2 Integration on singular simplices

For a smooth singular $p$-simplex $\sigma:\Delta^p\to M$ define

$$
I(\omega)(\sigma)=\int_{\Delta^p}\sigma^*\omega.
$$

Stokes' theorem gives

$$
I(d\omega)(\sigma)=I(\omega)(\partial\sigma), \tag{4.3}
$$

so integration is a cochain map from global smooth forms to smooth singular cochains. Every continuous simplex is homotopic, compatibly on faces after subdivision, to a smooth simplex. The prism identity shows that smooth and continuous singular cochains have the same cohomology.

The integration map also respects products on cohomology. At chain level wedge product and the Alexander--Whitney cup product are not identical. Triangulate $\Delta^{p+q}$ finely and integrate over the prisms interpolating between the diagonal and the Alexander--Whitney diagonal. Stokes' theorem supplies a natural cochain homotopy $H$ with

$$
I(\alpha\wedge\beta)-I(\alpha)\smile I(\beta)
=dH(\alpha,\beta)+H(d(\alpha\otimes\beta)). \tag{4.4}
$$

Thus the induced comparison is an isomorphism of graded algebras.

### 4.3 The global comparison theorem

**Analytic de Rham theorem.** For every smooth manifold $M$, integration induces natural isomorphisms

$$
H^n(\Gamma(M,\mathcal A_M^\bullet))
\xrightarrow{\sim}H^n_B(M,\mathbf C). \tag{4.5}
$$

They commute with pullback and cup products.

**Proof.** The smooth Poincaré lemma makes $\mathcal A_M^\bullet$ a resolution of $\mathbf C_M$, and fineness makes it an acyclic resolution. Therefore its global cohomology is $H^n(M,\mathbf C_M)$. Singular cochains form another resolution after sheafification: on a sufficiently small contractible ball their positive cohomology vanishes by the prism homotopy, while degree zero consists of locally constant functions. The integration map lifts the identity of $\mathbf C_M$ between the two resolutions. The comparison theorem for acyclic resolutions makes it a quasi-isomorphism on global sections. Naturality is visible on forms and simplices, and (4.4) proves product compatibility. $\square$

For a compact manifold, a closed form is therefore exact precisely when all its periods over cycles vanish. Indeed (4.5) identifies its cohomology class with the functional $[\gamma]\mapsto\int_\gamma\omega$, and the universal coefficient theorem detects the class by those functionals.

### 4.4 Products, traces, and the surface pairing

For an oriented compact surface, integration of a two-form depends only on its cohomology class by Stokes' theorem. Under (4.5),

$$
\int_X\eta=\langle I(\eta),[X]\rangle. \tag{4.6}
$$

If $\alpha$ and $\beta$ are closed one-forms, product compatibility gives

$$
\int_X\alpha\wedge\beta
=Q_B(I(\alpha),I(\beta)). \tag{4.7}
$$

Choose a symplectic basis $a_i,b_i$ of homology. Writing a cohomology class in the dual basis and applying (3.5) yields the Riemann bilinear identity

$$
\int_X\alpha\wedge\beta
=\sum_{i=1}^g
\left(
\int_{a_i}\alpha\int_{b_i}\beta
-\int_{b_i}\alpha\int_{a_i}\beta
\right). \tag{4.8}
$$

This formula will turn positivity of the area form into positivity of the period matrix. It also fixes every later sign: changing the orientation or interchanging the order $a_i,b_i$ changes both sides together.

## 5. From algebraic forms to analytic forms

The analytic theorem compares smooth forms with topology. Algebraic de Rham cohomology, however, uses regular algebraic forms and Zariski gluing. The missing step is to show that analytification preserves the hypercohomology of the two-term algebraic de Rham complex. In dimension one this can be proved from divisors, principal parts, and compactness.

### 5.1 Analytification of a smooth projective curve

Let $X/\mathbf C$ be smooth and projective. Its set of complex points has charts obtained by applying the complex implicit-function theorem to affine equations. Smoothness makes these charts one-dimensional complex manifolds, and projectivity makes the resulting Riemann surface compact. A regular algebraic function or differential becomes holomorphic, giving maps

$$
\mathcal O_X\longrightarrow\mathcal O_{X^{\mathrm{an}}},
\qquad
\Omega^1_{X/\mathbf C}\longrightarrow\Omega^1_{X^{\mathrm{an}},\mathrm{hol}}. \tag{5.1}
$$

These maps commute with $d$. Here the sheaves on the left are analytified: on an analytic open they are obtained locally by tensoring algebraic sections with holomorphic functions.

Every meromorphic function on $X^{\mathrm{an}}$ is algebraic. The needed dimension-one algebraization lemma says that a closed analytic curve in projective space is algebraic. To prove the lemma, choose a generic linear projection of the analytic curve to $\mathbf P^1$. Away from finitely many values, take the elementary symmetric functions of each affine coordinate on the finite fibers. They are single-valued holomorphic functions and extend meromorphically across the exceptional values by the removable-singularity and pole alternatives. Meromorphic functions on $\mathbf P^1$ are rational. The resulting monic polynomial relations are homogeneous algebraic equations cutting out the original curve, first over the regular locus and then everywhere by closure.

Apply this lemma to the graph of a meromorphic function

$$
\Gamma_h\subset X\times\mathbf P^1.
$$

It is a closed analytic curve in a projective variety and hence algebraic. Projection $\Gamma_h\to X$ is proper and has one-point fibers, so it is finite; since it is birational and $X$ is normal, it is an isomorphism. The second projection is therefore a rational function on $X$ equal to $h$. Dividing a meromorphic differential by a nonzero algebraic differential reduces the assertion for differentials to the function case.

It follows that a holomorphic map between smooth projective complex curves is algebraic. If nonconstant, it induces an inclusion of meromorphic function fields of finite degree; the graph is the normalization of the corresponding algebraic relation. If constant, its image is a complex point and is algebraic. This elementary curve form of algebraic--analytic equivalence will also be used in Riemann existence.

### 5.2 Coherent comparison in dimension one

**Coherent comparison theorem for curves.** If $\mathcal F$ is an algebraic vector bundle on a projective complex curve $X$, analytification induces isomorphisms

$$
H^q(X,\mathcal F)\xrightarrow{\sim}
H^q(X^{\mathrm{an}},\mathcal F^{\mathrm{an}}),
\qquad q=0,1. \tag{5.2}
$$

**Proof strategy.** We compare line-bundle sections by algebraizing meromorphic quotients, compare their first cohomology by an explicit analytic duality argument, and then filter a vector bundle by a line subbundle. This mirrors the residue proof of duality in Book 9 and avoids importing a higher-dimensional comparison theorem.

**Proof.** We first record the analytic input rather than hide it in the word “comparison.” On a compact Riemann surface $M$, Dolbeault cohomology identifies

$$
H^1(M,L)\simeq
\frac{\mathcal A^{0,1}(L)}
{\bar\partial\mathcal A^{0,0}(L)}.
$$

Integration of the product gives a pairing with $H^0(M,K_M\otimes L^{-1})$. It is perfect. Choose Hermitian metrics and take the harmonic representative of a Dolbeault class. The formal-adjoint identity identifies harmonic $L$-valued $(0,1)$-forms with the conjugate duals of holomorphic $K_M\otimes L^{-1}$-valued sections. If the pairing with every such section is zero, the harmonic representative has zero norm; the class is zero. The same argument in the other variable proves perfection. This is analytic Serre duality, normalized by integration.

Adding a point and using

$$
0\to L\to L(p)\to L(p)|_p\to0
$$

shows that $\chi(L(p))=\chi(L)+1$. For sufficiently large degree, analytic duality and negative-degree vanishing kill $H^1$. Descending by points gives

$$
\chi(L)=\deg L+1-h^1(M,\mathcal O_M).
$$

Taking $L=\mathcal O_M$ identifies $h^1(\mathcal O_M)$ with $h^0(K_M)$. This proves the analytic Riemann--Roch formula in exactly the form used here.

Now let $L$ be algebraic. A nonzero algebraic meromorphic section $e$ identifies every analytic section with $he$ for a meromorphic function $h$. Section 5.1 makes $h$ algebraic, so comparison on $H^0$ is always an isomorphism. Algebraic Serre duality from Book 9 and the analytic duality just proved identify the two $H^1$ dimensions, because Section 5.1 also algebraizes holomorphic differentials and hence the relevant dual sections. Thus comparison is an isomorphism for line bundles in both degrees.

For a point $p$, compare

$$
0\to L\to L(p)\to L(p)|_p\to0 \tag{5.3}
$$

with its analytic counterpart. The quotient is the same one-dimensional complex vector space, and the connecting maps are both described by the same principal part. This exact-sequence comparison also shows that the analytic duality trace agrees with the algebraic residue trace: both send the local pair $z^{-1}$ and $dz$ to $1$.

We argue by rank for a vector bundle $\mathcal F$. A nonzero vector in its generic fiber spans a rational line. Clear its finitely many poles to obtain a line subsheaf and saturate it. The quotient is torsion-free; over the discrete valuation ring at every point, a finite torsion-free module is free. There is therefore an exact sequence

$$
0\longrightarrow L\longrightarrow\mathcal F
\longrightarrow\mathcal F'\longrightarrow0
$$

with $L$ a line bundle and $\mathcal F'$ a vector bundle of rank one less. Analytification preserves this exact sequence because the local holomorphic ring is flat over the algebraic local ring. Comparison holds for $L$, and induction gives it for $\mathcal F'$. The two long exact sequences and the five lemma finish the proof. $\square$

The theorem also holds for coherent sheaves: split off the finite-length torsion, which is unchanged by analytification, and resolve the torsion-free quotient by vector bundles. We need only $\mathcal O_X$ and $\Omega^1_X$ below.

### 5.3 Algebraic de Rham comparison

**Algebraic de Rham comparison theorem for curves.** For a smooth projective curve $X/\mathbf C$, the natural inclusion of algebraic forms into smooth complex-valued forms induces functorial isomorphisms

$$
\operatorname{comp}_{\mathrm{dR},B}:
H^n_{\mathrm{dR}}(X/\mathbf C)
\xrightarrow{\sim}H^n_B(X^{\mathrm{an}},\mathbf C)
\qquad(n=0,1,2). \tag{5.4}
$$

It respects cup products.

**Proof.** Analytification gives a morphism of two-term complexes

$$
[\mathcal O_X\xrightarrow d\Omega^1_X]^{\mathrm{an}}
\longrightarrow
[\mathcal A^0_{X^{\mathrm{an}}}\xrightarrow d
\mathcal A^1_{X^{\mathrm{an}}}\xrightarrow d\mathcal A^2_{X^{\mathrm{an}}}]. \tag{5.5}
$$

The coherent comparison theorem identifies the hypercohomology of the source with algebraic de Rham cohomology. To compare the analytic holomorphic de Rham complex with smooth forms, use the decomposition $d=\partial+\bar\partial$. The local holomorphic Poincaré lemma says a holomorphic closed one-form has a local holomorphic primitive. The Dolbeault lemma resolves each sheaf of holomorphic $p$-forms by smooth $(p,q)$-forms. The resulting double complex has total complex the smooth de Rham complex. Filtering by $q$ shows that the inclusion of holomorphic de Rham into the total Dolbeault complex is a quasi-isomorphism. Finally the analytic de Rham theorem identifies the target with singular cohomology.

Every arrow is induced by inclusion or integration and respects wedge products up to the cochain homotopy of (4.4), so the induced isomorphism is multiplicative. $\square$

In degree one, the map has the concrete formula

$$
\operatorname{comp}_{\mathrm{dR},B}([\omega])([\gamma])
=\int_\gamma\omega \tag{5.6}
$$

when the class is represented by a global algebraic one-form. A general hypercohomology class has a Čech function component as well; integrating the glued smooth representative gives the same map.

The same theorem holds for every smooth complex algebraic curve, and the boundary argument is short enough in dimension one to include. If $U$ is not proper, let $j:U\hookrightarrow X$ be its smooth projective compactification and let $D=X\setminus U$ with the reduced structure. The nonempty divisor $D$ is ample on the proper curve, so $U$ is affine and $j$ is an affine morphism. Consequently the de Rham hypercohomology of $U$ is computed on $X$ by the direct-image complex below, with no higher direct-image term. On $X$ consider the logarithmic complex

$$
\Omega_X^\bullet(\log D)
=\bigl[\mathcal O_X\xrightarrow d\Omega_X^1(D)\bigr].
$$

The inclusion into the meromorphic complex

$$
\bigl[\mathcal O_X(*D)\xrightarrow d\Omega_X^1(*D)\bigr]
=j_*\Omega_U^\bullet
$$

is a quasi-isomorphism. This is local at a point of $D$. With parameter $z$, every term $z^{-m}dz$ with $m\ne1$ is the derivative of
$z^{-m+1}/(-m+1)$, while the single surviving class is $dz/z$. A meromorphic function whose derivative has at most a simple pole is regular, so degree zero also agrees. Characteristic zero is used exactly in dividing by $m-1$.

The identical Laurent-series calculation proves that the analytic logarithmic complex is quasi-isomorphic to the holomorphic de Rham complex on $U^{\mathrm{an}}$. Coherent comparison applies termwise to $\mathcal O_X$ and $\Omega_X^1(D)$, so it compares the algebraic and analytic logarithmic hypercohomology. The analytic de Rham theorem then gives

$$
H^n_{\mathrm{dR}}(U/\mathbf C)
\xrightarrow{\sim}H^n_B(U^{\mathrm{an}},\mathbf C).
\tag{5.7}
$$

The construction is functorial: after replacing compactifications by the normalization of the graph of a map, pullback preserves logarithmic forms and the resulting map is independent of that replacement because both sides identify with the intrinsic complexes on the open curves. This proves the nonproper comparison rather than extrapolating it from the projective case.

### 5.4 Functoriality and base field extension

If $f:X\to Y$ is a morphism of smooth projective complex curves, pullback commutes with analytification, exterior differentiation, and integration:

$$
\int_\gamma f^*\omega=\int_{f_*\gamma}\omega.
$$

Therefore (5.4) is functorial. For a finite map, the analytic transfer is adjoint to pullback. On the complement of the branch points, trace of a differential is the sum over inverse branches, so change of variables gives

$$
\int_\gamma f_*\eta=\int_{f^!\gamma}\eta, \tag{5.8}
$$

where $f^!$ is the homological transfer. Both sides extend across branch points by local degree. Thus comparison also commutes with cohomological trace.

Now let $X/K$ with $K\subseteq\mathbf C$. Book 46 proves arbitrary base change for de Rham cohomology of smooth proper curves, so

$$
H^n_{\mathrm{dR}}(X/K)\otimes_K\mathbf C
\simeq H^n_{\mathrm{dR}}(X_{\mathbf C}/\mathbf C). \tag{5.9}
$$

Composing (5.9) with (5.4) proves (1.1). If $K\hookrightarrow\mathbf C$ is changed, the Betti surface can change by conjugating the coefficients and complex structure; the algebraic $K$-space remains fixed. Thus the embedding is part of the comparison datum.

## 6. Periods, Hodge theory, and rational structures

Comparison turns algebraic differential classes into functionals on integral cycles. Their values are periods. The same construction reveals the Hodge decomposition and shows precisely how a $K$-vector space, a rational lattice, and a complex filtration coexist without being canonically split over $K$.

### 6.1 The period pairing

Define

$$
\operatorname{per}:H_1(X^{\mathrm{an}},\mathbf Z)
\times H^1_{\mathrm{dR}}(X/\mathbf C)\longrightarrow\mathbf C,
\qquad(\gamma,\xi)\longmapsto
\langle\operatorname{comp}_{\mathrm{dR},B}(\xi),\gamma\rangle. \tag{6.1}
$$

For a holomorphic form this is ordinary path integration. The pairing is perfect after tensoring the first variable with $\mathbf C$. Indeed the universal coefficient theorem identifies $H^1_B(X,\mathbf C)$ with the dual of $H_1(X,\mathbf C)$, and comparison is an isomorphism.

The integral period map

$$
H_1(X,\mathbf Z)\longrightarrow H^1_{\mathrm{dR}}(X/\mathbf C)^\vee
$$

is injective: a homology class with zero period against every de Rham class is zero after tensoring with $\mathbf C$, and $H_1$ is torsion-free. Its image is discrete and is a full lattice in its real span. It is not cocompact in the entire complex dual, whose real dimension is $4g$. Projection to the dual of $H^{1,0}$ produces the rank-$2g$ full lattice in a $g$-dimensional complex vector space used for the Jacobian in Chapter 12.

For $X/K$, the period matrix depends on both a $K$-basis of $H^1_{\mathrm{dR}}(X/K)$ and a $\mathbf Z$-basis of homology. Changing these bases multiplies the matrix on the left by a matrix over $K$ and on the right by a matrix in $\operatorname{GL}_{2g}(\mathbf Z)$. Individual periods are not intrinsic; the comparison isomorphism is.

### 6.2 Hodge decomposition in degree one

On a compact Riemann surface, smooth complex one-forms split as

$$
\mathcal A^1=\mathcal A^{1,0}\oplus\mathcal A^{0,1}.
$$

Choose any Hermitian metric. Every de Rham class has a unique harmonic representative: elliptic theory gives the orthogonal decomposition

$$
\mathcal A^1=\mathcal H^1\oplus d\mathcal A^0\oplus d^*\mathcal A^2.
$$

On a complex curve the Laplacian preserves type, and a harmonic $(1,0)$-form is holomorphic. The Kähler identity $\Delta_d=2\Delta_{\bar\partial}$ makes harmonicity force $\bar\partial\omega=0$; conversely a holomorphic one-form has $\partial\omega=0$ for dimension reasons and is closed and co-closed. Complex conjugation exchanges the two types. Hence

$$
H^1_B(X,\mathbf C)=H^{1,0}(X)\oplus H^{0,1}(X), \tag{6.2}
$$

where

$$
H^{1,0}(X)=H^0(X,\Omega^1_X),
\qquad
H^{0,1}(X)=\overline{H^{1,0}(X)}\simeq H^1(X,\mathcal O_X). \tag{6.3}
$$

The last identification is Dolbeault cohomology. Algebraic coherent comparison identifies it with algebraic $H^1(\mathcal O_X)$, and Book 9's Serre duality shows both summands have dimension $g$. This proves that the topological genus of Section 3.2 equals the algebraic genus.

The decomposition is not defined over $\mathbf Q$ in general. Complex conjugation interchanges the summands, so neither can contain a nonzero real class: if a real class lies in $H^{1,0}$, it also lies in $H^{0,1}$, and the direct sum forces it to vanish.

### 6.3 The Hodge filtration and the rational lattice

Under de Rham comparison, Book 46's Hodge exact sequence becomes

$$
0\to H^{1,0}(X)\to H^1_B(X,\mathbf C)
\to H^{0,1}(X)\to0, \tag{6.4}
$$

with

$$
F^1=H^{1,0},\qquad F^0=H^1_B(X,\mathbf C),
\qquad F^2=0. \tag{6.5}
$$

The rational Betti structure is the subspace $H^1_B(X,\mathbf Q)$ whose complexification is the middle term. Thus degree one carries a pure rational Hodge structure of weight one:

$$
H^1_B(X,\mathbf C)=H^{1,0}\oplus H^{0,1},
\qquad \overline{H^{p,q}}=H^{q,p},
\qquad p+q=1. \tag{6.6}
$$

If $X/K$, the de Rham filtration is already defined over $K$, but its complement is not. This distinction is essential. Degeneration of the Hodge-to-de Rham spectral sequence supplies the filtration and its graded pieces; it does not supply a canonical $K$-linear decomposition.

The rational structure transported to de Rham cohomology is

$$
H^1_{\mathrm{dR}}(X/\mathbf C)_{\mathbf Q}
=\operatorname{comp}_{\mathrm{dR},B}^{-1}
H^1_B(X,\mathbf Q). \tag{6.7}
$$

It depends on the chosen embedding into $\mathbf C$. It rarely equals the scalar extension of an evident $\mathbf Q$-basis of algebraic differentials; the mismatch is measured by periods.

### 6.4 Period matrices and the bilinear relations

Choose a symplectic homology basis $a_1,\ldots,a_g,b_1,\ldots,b_g$ and a basis $\omega_1,\ldots,\omega_g$ of holomorphic differentials. Let

$$
A_{ij}=\int_{a_j}\omega_i,
\qquad B_{ij}=\int_{b_j}\omega_i. \tag{6.8}
$$

No nonzero holomorphic form can have all $a$-periods zero. If it did, (4.8) applied to $\omega$ and $\bar\omega$ would give

$$
i\int_X\omega\wedge\bar\omega=0,
$$

whereas locally $\omega=f(z)dz$ gives

$$
i\omega\wedge\bar\omega=2|f(z)|^2dx\wedge dy,
$$

which has positive integral unless $\omega=0$. Hence $A$ is invertible. Replacing the form basis by $A^{-1}\omega$, assume $A=I_g$ and put $\tau=A^{-1}B$.

Because $\omega_i\wedge\omega_j=0$ on a complex curve, (4.8) gives

$$
\tau=\tau^t. \tag{6.9}
$$

Applying (4.8) to $\omega=\sum c_i\omega_i$ and $\bar\omega$ gives

$$
i\int_X\omega\wedge\bar\omega
=2\,\bar c^{\,t}(\operatorname{Im}\tau)c>0
\qquad(c\ne0). \tag{6.10}
$$

Thus $\operatorname{Im}\tau$ is positive definite. Symmetry and positivity are the Riemann bilinear relations. They are consequences of cup product, complex orientation, and Hodge type, not extra conditions imposed on the period matrix.

## 7. Finite étale covers and Riemann existence

The de Rham bridge used integration. The étale bridge begins with covering spaces. A finite étale morphism has no analytic ramification, while a finite topological cover of a compact Riemann surface carries a unique complex structure. Compactness then algebraizes it. This is the geometric core of Betti--étale comparison.

### 7.1 Analytification of an étale map

Let $f:Y\to X$ be finite étale over $\mathbf C$. At a point $y$, étaleness says that the completed local parameter of $X$ pulls back to a local parameter of $Y$ with nonzero derivative. The complex inverse-function theorem therefore makes $f^{\mathrm{an}}$ a local biholomorphism. Finiteness makes it proper with finite fibers. A proper local homeomorphism with finite fibers is a finite covering map: choose disjoint local inverse neighborhoods over each point in the fiber and shrink their common image.

Conversely, if a finite algebraic map of smooth complex curves analytifies to a local homeomorphism, its ramification index at every point is one. In local parameters it has the form $t\mapsto u t^e$ with $u$ a unit; local injectivity forces $e=1$. Hence the algebraic map is étale.

Analytification preserves fiber products and deck transformations. It therefore defines a functor

$$
\{\text{finite étale covers of }X\}
\longrightarrow
\{\text{finite topological covers of }X^{\mathrm{an}}\}. \tag{7.1}
$$

### 7.2 Algebraizing finite topological covers

Let $p:T\to X^{\mathrm{an}}$ be a finite topological covering. Give $T$ the unique complex structure for which $p$ is locally biholomorphic: pull back holomorphic charts along every local sheet. Transition maps are those of $X$, so they are holomorphic. Since $p$ is finite and $X^{\mathrm{an}}$ compact, $T$ is a compact Riemann surface, possibly disconnected.

Each connected component of $T$ is algebraic. A direct proof uses meromorphic functions. Riemann--Roch on a compact Riemann surface supplies a nonconstant meromorphic function $u:T\to\mathbf P^1$. Choose another meromorphic function $v$ separating the finitely many generic points in a fiber of $u$. The functions $u,v$ satisfy an irreducible polynomial relation $F(u,v)=0$, and the map to the projective plane has generically one-point fibers. Normalizing the projective closure of $F=0$ recovers $T$. Thus $T\simeq Y^{\mathrm{an}}$ for a unique smooth projective algebraic curve $Y$.

The holomorphic map $p:T\to X^{\mathrm{an}}$ is algebraic by Section 5.1. Since it is locally biholomorphic, the resulting $Y\to X$ is finite étale. Uniqueness follows because a holomorphic map between compact algebraic curves is algebraic. This proves essential surjectivity and full faithfulness of (7.1).

### 7.3 The Riemann existence theorem

**Riemann existence theorem for curves.** For a smooth projective complex curve $X$, analytification is an equivalence between finite étale covers of $X$ and finite topological covering spaces of $X^{\mathrm{an}}$. It preserves connected covers, fiber products, degrees, automorphism groups, and traces on finite fibers.

**Proof.** Sections 7.1 and 7.2 construct quasi-inverse functors. Starting with an algebraic cover, the complex structure pulled back from $X$ is its original analytic structure by uniqueness of holomorphic charts. Starting with a topological cover, analytification of its algebraization is the same local cover by construction. Morphisms are preserved because a map over $X$ is determined sheetwise and every resulting holomorphic map is algebraic. Products, degrees, and automorphisms are categorical and therefore preserved. Trace on a finite locally constant function is the sum over a fiber on both sides. $\square$

Choose a geometric point $x\in X(\mathbf C)$. Finite covering theory identifies finite covers with finite sets carrying an action of the profinite completion of $\pi_1^{\mathrm{top}}(X^{\mathrm{an}},x)$. Étale covering theory identifies them with finite continuous sets for $\pi_1^{\mathrm{\acute et}}(X,x)$. The equivalence therefore yields a canonical isomorphism

$$
\pi_1^{\mathrm{\acute et}}(X,x)
\xrightarrow{\sim}
\widehat{\pi_1^{\mathrm{top}}(X^{\mathrm{an}},x)}. \tag{7.2}
$$

The isomorphism depends on the common base point only up to inner automorphism, as both fundamental groups do.

### 7.4 Local systems and fundamental groups

A finite locally constant sheaf $\mathcal F$ on either side is equivalent to a finite module $M$ with continuous monodromy. Under (7.2), analytification sends the étale stalk and its monodromy action to the topological stalk and action. Hence finite local systems correspond exactly, including tensor products and duals.

For an open smooth complex curve $U$, finite étale covers still correspond to finite topological covers of $U^{\mathrm{an}}$. To prove essential surjectivity, compactify $U$ to a smooth projective $X$. A finite topological cover has finite monodromy around each puncture. Filling each punctured disc by the map $z\mapsto z^e$ gives a branched cover of compact Riemann surfaces; algebraize it as above and then remove the points above the boundary. The restriction is étale. The integers $e$ record tame topological monodromy, which over characteristic zero is all local monodromy.

Riemann existence alone compares covers and $H^1$ torsors. Higher cohomology requires a cohomological argument. The next chapter supplies it and shows that the equivalence respects products, compact support, and traces.

## 8. Finite-coefficient Betti--étale comparison

Both sites have the same finite local systems, but derived global sections could in principle differ. On a curve one can compare them by finite covers, Čech descent, and the local acyclicity of small discs. This chapter proves the comparison before taking any inverse limit.

### 8.1 The comparison morphism

Analytification sends an étale map $V\to X$ to a local biholomorphism $V^{\mathrm{an}}\to X^{\mathrm{an}}$. Pulling an étale sheaf through this functor gives a sheaf on the analytic topology. The identity on global sections yields a natural morphism in derived cohomology

$$
R\Gamma_{\mathrm{\acute et}}(X,\mathcal F)
\longrightarrow
R\Gamma(X^{\mathrm{an}},\mathcal F^{\mathrm{an}}). \tag{8.1}
$$

For a finite constant ring $A$ and a finite locally constant $A$-sheaf $\mathcal F$, we orient the comparison as

$$
c_{B,\mathrm{\acute et}}:
H^n_B(X^{\mathrm{an}},\mathcal F^{\mathrm{an}})
\longrightarrow H^n_{\mathrm{\acute et}}(X,\mathcal F), \tag{8.2}
$$

the inverse of the cohomology map induced by (8.1). This orientation agrees with (1.2). Natural transformations are easier to construct in the reverse direction; the theorem justifies taking their inverses.

### 8.2 Proof for finite local systems

**Finite-coefficient comparison theorem.** Let $X$ be a smooth complex algebraic curve, not necessarily proper, and let $\mathcal F$ be a finite locally constant abelian sheaf. Then (8.1) is a quasi-isomorphism. Equivalently,

$$
H^n_{\mathrm{\acute et}}(X,\mathcal F)
\simeq H^n_B(X^{\mathrm{an}},\mathcal F^{\mathrm{an}}) \tag{8.3}
$$

naturally in $X$ and $\mathcal F$.

**Proof strategy.** Trivialize $\mathcal F$ on a finite cover, compare the resulting descent complexes, and reduce their terms to constant coefficients on open Riemann surfaces.

**Proof.** By Riemann existence there is a finite étale Galois cover $p:Y\to X$, with group $G$, on which $\mathcal F$ becomes constant with fiber $M$. Its Čech nerve has terms

$$
Y_r=\underbrace{Y\times_X\cdots\times_XY}_{r+1\text{ factors}},
$$

and analytification preserves this nerve. Refining $Y$ by affine étale opens, one obtains a hypercover whose connected terms are smooth affine curves carrying constant coefficients. Such a curve has the homotopy type of a finite graph: after compactification, remove small disjoint discs around the missing points and cut the remaining surface along $2g$ arcs to a polygon. Hence its topological cohomology vanishes above degree one.

On the étale side, Book 21 proves the matching prime-to-characteristic cohomological-dimension-one statement for smooth affine curves. Degree zero agrees because connected components agree. Degree one with a constant finite abelian group $M$ classifies $M$-torsors; Riemann existence identifies those torsors, including their Baer sums. Thus constant-coefficient cohomology agrees on every connected term of the refined nerve.

The two hypercover spectral sequences have identical $E_1$ pages and identical face maps, because fiber products, restriction, and trace over sheets are preserved. They are bounded in the curve direction and in each total degree, so the comparison theorem for spectral sequences gives an isomorphism on their abutments. Descent for $\mathcal F$ is effective on both sites, and the common $G$-action on $M$ gives the same descent differential. This proves (8.3). $\square$

The argument also proves compatibility with cup products: choose the common hypercover and use the same Alexander--Whitney product on its double complex. Connecting morphisms agree because they arise from the same short exact sequence of coefficient complexes.

### 8.3 Constant coefficients on a proper curve

For a smooth proper genus-$g$ curve and a finite ring $A$, comparison and Chapter 3 give

$$
H^0_{\mathrm{\acute et}}(X,A)=A,\qquad
H^1_{\mathrm{\acute et}}(X,A)=A^{2g},\qquad
H^2_{\mathrm{\acute et}}(X,A)=A, \tag{8.4}
$$

after identifying the top Tate twist with the constant coefficient over $\mathbf C$. The groups vanish above degree two. This recovers the computation of Book 21 from topology, but the comparison proof did not use the rank-$2g$ étale computation; it used only affine cohomological dimension and torsor classification, so there is no circularity.

For $A=\mathbf Z/n\mathbf Z$, there is a canonical comparison with twisted coefficients

$$
H^2_B(X,\mu_n(\mathbf C))
\xrightarrow{\sim}
H^2_{\mathrm{\acute et}}(X,\mu_n). \tag{8.5}
$$

The Betti trace evaluates a class on $[X]$ and then uses the coefficient identification already present in $\mu_n(\mathbf C)$. The étale trace sends a point class to $1\in\mathbf Z/n\mathbf Z$. Section 10.1 will show these normalizations agree via the positively oriented boundary circle around a point.

### 8.4 Compact supports and punctures

Let $j:U\hookrightarrow X$ be a smooth compactification with finite complement $Z$. Analytification commutes with extension by zero on finite local systems: the stalk is the given stalk on $U$ and zero at $Z$ on both sides. We need a small extension of Section 8.2 because $j_!\mathcal F$ is constructible rather than lisse on $X$.

Every finite constructible sheaf on a smooth curve is lisse on a dense open set. Add the missing points one at a time. The open--closed exact sequence separates extension by zero on the open stratum from a sheaf supported at the new point. Point-supported cohomology is its stalk in degree zero on both sites. The connecting local cohomology is computed on a punctured strict disc étale-theoretically and on a punctured analytic disc topologically. Riemann existence identifies both with the cohomology of the same finite inertia action, since the tame generator is the positive loop around the puncture. The two localization long exact sequences therefore agree. Induction on the number of strata and the five lemma extend finite comparison to constructible sheaves on a complex curve.

Apply this constructible comparison to $j_!\mathcal F$. Since the compactification is proper, it gives

$$
H^n_{c,\mathrm{\acute et}}(U,\mathcal F)
\simeq H^n_c(U^{\mathrm{an}},\mathcal F^{\mathrm{an}}). \tag{8.6}
$$

One can also prove (8.6) from the two localization sequences. Point-supported cohomology agrees in degree zero, and purity identifies its shifted local term with the cohomology of a small oriented circle. The boundary sends a local Kummer cover $w^n=z$ to its winding number $1$ on both sides. The five lemma then compares the middle terms.

For constant $A$ and $r=|Z|>0$, the result gives

$$
H^0_c(U,A)=0,\qquad
H^1_c(U,A)\simeq A^{2g+r-1},\qquad
H^2_c(U,A)\simeq A. \tag{8.7}
$$

The $r-1$ additional degree-one directions are boundary paths subject to the single relation that the sum of oriented boundary circles is zero. This is exactly the residue relation in both de Rham and étale localization.

## 9. Passage to integral and rational ℓ-adic cohomology

Finite comparison becomes ℓ-adic comparison only after controlling inverse limits. On proper smooth curves the integral Betti groups are free and finite, while the finite étale groups satisfy compatible surjective reduction. These facts eliminate the derived-limit ambiguity emphasized in Book 21.

### 9.1 Inverse limits without hidden terms

For a compact finite CW complex $T$, define

$$
H^n_B(T,\mathbf Z_\ell)=\varprojlim_m
H^n_B(T,\mathbf Z/\ell^m\mathbf Z).
$$

Because $H_n(T,\mathbf Z)$ is finitely generated and, for a surface, torsion-free, the universal coefficient theorem gives

$$
H^n_B(T,\mathbf Z/\ell^m\mathbf Z)
=H^n_B(T,\mathbf Z)\otimes\mathbf Z/\ell^m\mathbf Z.
$$

The transition maps are surjective. Therefore

$$
H^n_B(T,\mathbf Z_\ell)
=H^n_B(T,\mathbf Z)\otimes\mathbf Z_\ell. \tag{9.1}
$$

On the étale side, Book 21 defines continuous cohomology by a derived inverse limit and supplies the Milnor sequence

$$
0\to\varprojlim{}^1 H^{n-1}_{\mathrm{\acute et}}(X,\mathbf Z/\ell^m)
\to H^n_{\mathrm{\acute et}}(X,\mathbf Z_\ell)
\to\varprojlim H^n_{\mathrm{\acute et}}(X,\mathbf Z/\ell^m)\to0. \tag{9.2}
$$

Finite comparison identifies the transition system with the surjective Betti system, so $\varprojlim^1=0$. Thus no class appears or disappears at the limit.

### 9.2 The integral comparison isomorphism

Taking the inverse limit of (8.3) gives

$$
c_{B,\mathrm{\acute et},\ell}:
H^n_B(X^{\mathrm{an}},\mathbf Z_\ell)
\xrightarrow{\sim}
H^n_{\mathrm{\acute et}}(X,\mathbf Z_\ell). \tag{9.3}
$$

The isomorphism is canonical, functorial, compatible with cup products, and compatible with reduction modulo every $\ell^m$. For a genus-$g$ proper curve,

$$
H^0\simeq\mathbf Z_\ell,\qquad
H^1\simeq\mathbf Z_\ell^{2g},
\qquad H^2\simeq\mathbf Z_\ell(-1) \tag{9.4}
$$

on the étale side. In (9.4), the top twist is canonical; an untwisted Betti presentation chooses a generator of $\mathbf Z_\ell(1)$.

The integral lattice is important. A rational isomorphism alone would not control reductions, integral projectors, or whether a correspondence preserves a chosen lattice. Here the lattice is not selected after the fact: it is the completion of $H^1_B(X,\mathbf Z)$ and equals étale integral cohomology under (9.3).

### 9.3 Rational coefficients and lattices

Tensoring (9.3) with $\mathbf Q_\ell$ yields

$$
H^n_B(X,\mathbf Q_\ell)
\xrightarrow{\sim}
H^n_{\mathrm{\acute et}}(X,\mathbf Q_\ell). \tag{9.5}
$$

For a finite-dimensional lisse $\mathbf Q_\ell$-local system, choose a stable $\mathbf Z_\ell$-lattice, compare its finite locally constant reductions, take the derived inverse limit, and invert $\ell$. Such a lattice exists because the continuous monodromy image is compact and every compact subgroup of $\operatorname{GL}_r(\mathbf Q_\ell)$ stabilizes a lattice. At every finite level the cohomology groups are finite, so their inverse system is Mittag--Leffler and the Milnor $\varprojlim^1$ term vanishes even when the transition maps are not surjective. Two stable lattices are commensurable, so the rational comparison is independent of the choice. The full monodromy need not be finite; only each reduction has finite image.

If $X$ descends to $K\subset\mathbf C$, the group on the right for $X_{\bar K}$ carries an action of $G_K$. Choosing an embedding $\bar K\hookrightarrow\mathbf C$ identifies the underlying vector space with Betti cohomology, but the Galois action is additional arithmetic structure; $X^{\mathrm{an}}$ alone does not produce it. A different extension of the embedding changes the comparison by the corresponding Galois element.

### 9.4 What comparison does and does not identify

The full degree-one picture is

$$
\begin{aligned}
H^1_{\mathrm{dR}}(X/K)\otimes_K\mathbf C
&\simeq H^1_B(X,\mathbf Q)\otimes\mathbf C,\\
H^1_{\mathrm{\acute et}}(X_{\bar K},\mathbf Q_\ell)
&\simeq H^1_B(X,\mathbf Q)\otimes\mathbf Q_\ell,
\end{aligned} \tag{9.6}
$$

after choosing $\bar K\hookrightarrow\mathbf C$ in the second line. Both are scalar extensions of one rational Betti space, but along different fields. There is no canonical diagonal arrow between the left sides of (9.6).

What is common is exact algebraic linear data defined over $\mathbf Q$: dimensions, ranks of rational correspondence operators, characteristic polynomials of operators preserving the rational lattice, tensor identities, adjointness, and idempotent decompositions whose denominators are invertible in the chosen coefficient ring. What is not common without further theory is a comparison of the Hodge filtration with an ℓ-adic filtration, or a direct identification of complex periods with ℓ-adic numbers. Keeping this boundary explicit is part of a correct comparison theorem.

### 9.5 The coefficient-prime Hodge--Tate bridge

The preceding comparison is geometric over an algebraic closure. Arithmetic applications also
restrict the Galois action to a decomposition group at the same prime as the coefficient field.
This is a different problem. Let $L$ be a finite extension of $\mathbf Q_p$, let $C/L$ be a
smooth, proper, geometrically connected curve, and put

$$
V_C=H^1_{\mathrm{\acute et}}(C_{\overline L},\mathbf Q_p).
$$

Write $\mathbf C_p$ for the completed algebraic closure of $L$. With the convention that
$\mathbf Q_p(1)$ has Hodge--Tate weight $-1$, the required coefficient-prime comparison is

$$
\boxed{(\mathrm{HT}_{\mathrm{curve}})\qquad
V_C\otimes_{\mathbf Q_p}\mathbf C_p
\simeq
\bigl(H^1(C,\mathcal O_C)\otimes_L\mathbf C_p\bigr)
\oplus
\bigl(H^0(C,\Omega^1_{C/L})\otimes_L\mathbf C_p(-1)\bigr).}
\tag{9.7}
$$

The isomorphism is required to be $G_L$-equivariant and functorial for maps and algebraic
correspondences. Formula (9.7) is the degree-one smooth-proper Hodge--Tate comparison theorem.
It does not require good reduction: properness and smoothness concern the generic fiber over
$L$. Replacing it by crystalline comparison would therefore lose precisely the bad-reduction
coefficient places which a uniform packet argument must retain.

There is a useful abelian reduction, with one important qualification. If
$J=\operatorname{Pic}^0_{C/L}$, Abel--Jacobi and the canonical principal polarization identify
$V_C$ with the corresponding rational Tate realization of $J$ and identify the two de Rham
Hodge terms. Thus the Hodge--Tate theorem for abelian varieties implies (9.7). When $J$ has
good reduction, that theorem can in turn be expressed as the Hodge--Tate exact sequence for
the $p$-divisible group of its abelian model over $\mathcal O_L$. For arbitrary reduction,
$J[p^\infty]$ over the characteristic-zero field $L$ is not such an integral model: all of its
finite levels over $L$ are etale, and its Lie terms do not recover the Hodge filtration.
One must instead use a general proper-smooth theorem or extend the good-reduction exact
sequence through semistable uniformization. This distinction matters here because (9.7) is
required without a good-reduction hypothesis.

The assumption $(\mathrm{HT}_{\mathrm{curve}})$ is understood to carry with it the
Tate--Sen apparatus in which the comparison is used below, since (9.7) by itself is a
statement about the single representation $V_C$ and says nothing about its subquotients.
Explicitly, we assume in addition that every continuous finite-dimensional $\mathbf Q_p$-linear
representation $U$ of $G_L$ carries labeled Sen operators $\Theta_\tau(U)$, one for each
embedding $\tau$ of $L$ into the coefficient field, which are functorial in $U$, compatible
with $G_L$-stable subspaces, quotients, and extension of the coefficient field, and which
detect the Hodge--Tate condition: $U$ is Hodge--Tate exactly when every $\Theta_\tau(U)$ is
semisimple with integer eigenvalues, and those eigenvalues are then the labeled weights of $U$.
Constructing these operators requires the completion $\mathbf C_p$, the continuous Galois
cohomology of $\mathbf C_p$, and a decompletion argument along a Lubin--Tate or cyclotomic
tower; no volume of this library develops any of that, so the apparatus is assumed here
alongside (9.7) and is recorded in the list of required work below.

The exact consequence needed for curve-carried packet factors is nevertheless formal once
$(\mathrm{HT}_{\mathrm{curve}})$ is supplied in this form.

**Proposition 9.1 (Hodge--Tate inheritance for curve factors).** Assume
$(\mathrm{HT}_{\mathrm{curve}})$. Let $E/\mathbf Q_p$ be finite, and let $W$ be an $E$-linear
subquotient of

$$
V_C\otimes_{\mathbf Q_p}E
$$

cut out after coefficient extension by maps commuting with $G_L$; this includes a
correspondence summand, a Hecke multiplicity factor, and every Jordan--Hölder constituent of
either. Then $W$ is Hodge--Tate. After any finite extension of $E$, every one-dimensional
Jordan--Hölder constituent of $W$ is Hodge--Tate, with weights among $0$ and $1$ in the
normalization of (9.7).

**Proof.** By the Sen-operator clause of $(\mathrm{HT}_{\mathrm{curve}})$, the Hodge--Tate
condition is equivalent to the assertion that the labeled Sen operators are semisimple with
integral eigenvalues, here $0$ and $1$. A $G_L$-stable subspace
is stable under every Sen operator. Restricting commuting semisimple operators to an invariant
subspace, and then passing to the induced operators on a quotient, preserves semisimplicity and
keeps the eigenvalues among those of the original space. Scalar extension does the same. Hence
every displayed subquotient is Hodge--Tate with the asserted weights. Functoriality in (9.7)
ensures that correspondence and Hecke projectors act on both summands, but no integral projector
is needed for this rational conclusion. $\square$

The Sen-operator formulation is important. The class of arbitrary representations admitting
some filtration is not automatically closed under subquotients; what makes the argument work
is the semisimple integral Sen operator attached to the actual Hodge--Tate decomposition by
the assumed apparatus.
Nor does semisimplifying $V_C$ before applying (9.7) prove a statement about a raw local
monodromy operator. Proposition 9.1 supplies Hodge--Tate one-dimensional factors; a separate
global irreducibility argument is what can then identify a raw packet representation with its
semisimplification.

The proof of (9.7) is not contained in the Betti--de Rham--étale arguments of this volume or
in the crystalline theory of Book 49. The exact audit is as follows.

- Books 18--20 construct finite and adic etale cohomology, proper/smooth base change, and
  duality only in their stated coefficient-invertible range. They produce the vector space
  $V_C$ but no $\mathbf C_p$ period map at a coefficient-prime decomposition group.
- Books 35--36 identify curve $H^1$ with the Jacobian Tate realization and transport maps,
  correspondences, duality, and the principal polarization. Book 46 constructs the two
  de Rham Hodge terms. These results reduce and normalize (9.7); they do not prove it.
- Books 48--55 develop crystalline, Fontaine--Laffaille, finite-flat, Dieudonne, and
  $p$-divisible-group deformation theory over their unramified, small-weight, or
  $p$-nilpotent bases. They contain no $\mathbf C_p$ period theory and do not prove even the
  good-reduction Hodge--Tate exact sequence. Crystalline comparison would in any event not
  cover a Jacobian of arbitrary reduction without another theorem.
- Books 59--61 construct rigid/formal curve geometry, Raynaud uniformization, one-motives,
  and potential semistable reduction. Their Tate-realization calculations are explicitly
  prime to the residue characteristic. They provide the geometric reduction needed by a
  semistable proof, but no coefficient-prime Hodge--Tate realization of the torus, lattice,
  and bounded abelian parts.

Thus no theorem in Books 18--20, 35--36, 46--55, or 59--61 is an alias for
$(\mathrm{HT}_{\mathrm{curve}})$. A source-closed proof must add at least the following
reusable package.

1. The entire $\mathbf C_p$ and Tate--Sen foundation, the rank-one case included: completed
   tensor products and continuous $G_L$-cohomology, Tate twists and labeled embeddings, the
   normalized-trace or almost ramification estimates which compute the relevant invariants and
   make the period maps exact, the decompletion argument along a Lubin--Tate tower, and the
   labeled Sen operators together with their functoriality and their characterization of the
   Hodge--Tate condition. No volume of this library supplies any part of this, at any rank.
   Book 24a, _Tate--Sen Theory and $\mathbf C_\ell$ Period Foundations_, is the volume that
   will carry it.
2. The functorial Hodge--Tate map and its dual for $p$-divisible groups over valuation rings,
   together with the good-reduction exact sequence, dimension calculation, Cartier duality,
   polarizations, isogenies, and finite base change. Merely constructing the map by invariant
   differentials is not enough; injectivity, cokernel, and the $\mathbf C_p$ Galois action are
   the theorem.
3. A passage from good reduction to arbitrary abelian reduction. In the narrow route needed
   here this means extending Books 60--61's Raynaud one-motive to its coefficient-prime
   Hodge--Tate realization, proving the torus and period-lattice terms and exactness, and then
   descending from a finite semistable extension. The broader alternative is the full
   smooth-proper Hodge--Tate comparison via an almost-purity or pro-etale primitive comparison
   theorem.
4. Functoriality for homomorphisms, duality, finite base change, and algebraic
   correspondences. Books 36 and 46 then identify the resulting abelian statement with
   (9.7), after which Proposition 9.1 supplies every Hecke-stable subquotient consequence.

This package is too large to insert as another proof inside this comparison volume. The
restricted abelian/curve route is coherent as one substantial future volume on Hodge--Tate
theory for $p$-divisible groups and semistable abelian varieties, reusing the Jacobian and
uniformization books. Developing general perfectoid spaces, the pro-etale site, and
smooth-proper comparison would be a broader multi-volume expansion and is unnecessary for
the FLT dependency chain. Until the restricted volume or an accepted external theorem is
supplied, $(\mathrm{HT}_{\mathrm{curve}})$, in the strengthened form fixed above, remains the
exact gap here, and that form now includes the Tate--Sen apparatus as well as (9.7). Once both
are available, Proposition 9.1 closes every geometric-subquotient step used by the packet
applications. The further rank-one passage from Hodge--Tate to local algebraicity is not
available from any earlier volume: Book 6, Section 11.5 builds the $\ell$-adic avatar of an
algebraic Hecke character out of local algebraicity and expressly defers the converse to
Book 24a, so that passage belongs to item 1 above rather than to anything already proved.

## 10. Cycle classes, twists, and trace normalizations

Comparison maps become useful only after their normalizations have been tested on geometric generators. On a curve, closed points generate the top cohomology, so one local calculation controls traces, first Chern classes, and all duality pairings. It also explains why $2\pi i$ appears on the de Rham side and a Tate twist appears on the étale side.

### 10.1 Divisors in the three theories

Let $p\in X(\mathbf C)$. In a holomorphic coordinate disc $D$ centered at $p$, with coordinate $z$, the punctured disc $D^*=D\setminus\{p\}$ has positively oriented generator $|z|=\varepsilon$. The relative group

$$
H^2(D,D^*;\mathbf Z)\simeq\mathbf Z
$$

maps its positive Thom class to the global Betti class $\operatorname{cl}_B(p)\in H^2_B(X,\mathbf Z)$. By construction

$$
\langle\operatorname{cl}_B(p),[X]\rangle=1. \tag{10.1}
$$

Algebraically, the divisor $p$ defines $\mathcal O_X(p)$. Its de Rham first Chern class is represented on an overlap by $d\log z=dz/z$. Its étale class modulo $n$ is the boundary of the Kummer cover $w^n=z$. Going once positively around $z=0$ sends $w$ to $e^{2\pi i/n}w$. Thus Riemann existence sends the local Kummer generator to the positive topological generator. Consequently

$$
c_{B,\mathrm{\acute et},n}
(\operatorname{cl}_B(p)\otimes e^{2\pi i/n})
=\operatorname{cl}_{\mathrm{\acute et}}(p) \tag{10.2}
$$

in twisted cohomology. Additivity gives the same compatibility for every divisor $D=\sum n_pp$.

Principal divisors map to zero in all three theories. Betti-theoretically the sum of winding numbers of a meromorphic function on a compact surface is zero. De Rham-theoretically this is the global residue theorem of Book 9. Étale-theoretically it is exactness of the Kummer sequence. The comparison identifies these three forms of the same reciprocity law.

### 10.2 The factor $2\pi i$

The loop integral

$$
\int_{|z|=\varepsilon}\frac{dz}{z}=2\pi i \tag{10.3}
$$

determines the de Rham normalization. The connecting class of $dz/z$ in relative de Rham cohomology maps under integration to $2\pi i$ times the positive Thom class. Therefore

$$
\operatorname{comp}_{\mathrm{dR},B}
(c_1^{\mathrm{dR}}(L))
=2\pi i\,c_1^B(L) \tag{10.4}
$$

for every line bundle $L$ on $X$. In particular,

$$
\langle\operatorname{comp}_{\mathrm{dR},B}(u),[X]\rangle
=2\pi i\operatorname{Tr}_{\mathrm{dR}}(u). \tag{10.5}
$$

There are two legitimate conventions. One may retain the algebraic class $d\log g_{ij}$ and the factor $2\pi i$ in comparison, as we do. Or one may define a normalized analytic Chern class using $(2\pi i)^{-1}d\log$. Mixing these conventions would make point classes and polarization forms disagree by $2\pi i$.

For $\alpha,\beta\in H^1_{\mathrm{dR}}(X/\mathbf C)$, multiplicativity of comparison and (10.5) give

$$
Q_B(\operatorname{comp}\alpha,\operatorname{comp}\beta)
=2\pi i\operatorname{Tr}_{\mathrm{dR}}(\alpha\smile\beta). \tag{10.6}
$$

Combining this with (4.8) recovers the de Rham form of the Riemann bilinear relation.

### 10.3 Trace and Poincaré pairings

For $A=\mathbf Z/n\mathbf Z$, use the coefficient local system $\mu_n(\mathbf C)$ on the Betti side. Evaluation on $[X]$, followed by the winding-number identification of the oriented local generator, gives

$$
\operatorname{Tr}_B:H^2_B(X,\mu_n(\mathbf C))
\longrightarrow\mathbf Z/n\mathbf Z. \tag{10.7}
$$

Equation (10.2) shows that finite comparison intertwines (10.7) with Book 21's étale trace

$$
\operatorname{Tr}_{\mathrm{\acute et}}:
H^2_{\mathrm{\acute et}}(X,\mu_n)
\longrightarrow\mathbf Z/n\mathbf Z. \tag{10.8}
$$

Both send a point to $1$, and top cohomology is cyclic generated by a point, so this proves equality on every class.

Cup-product compatibility now identifies the Poincaré pairings:

$$
\begin{array}{ccc}
H^i_B(X,A)\times H^{2-i}_B(X,A(1))&\longrightarrow&A\\
\downarrow&&\Vert\\
H^i_{\mathrm{\acute et}}(X,A)\times
H^{2-i}_{\mathrm{\acute et}}(X,A(1))&\longrightarrow&A.
\end{array} \tag{10.9}
$$

Passing to inverse limits gives the integral ℓ-adic version. On de Rham cohomology, the corresponding square commutes after the top trace is multiplied by $2\pi i$, exactly as in (10.6).

### 10.4 The first Chern class of a line bundle

Let $L$ have transition functions $g_{ij}$. The three first Chern classes arise from the same gluing defect:

$$
\begin{array}{ccl}
c_1^B(L)&:&\text{winding numbers of }g_{ij},\\
c_1^{\mathrm{dR}}(L)&:&\text{the Čech cocycle }d\log g_{ij},\\
c_1^{\mathrm{\acute et}}(L)&:&\text{the Kummer boundary of }(g_{ij}).
\end{array} \tag{10.10}
$$

To prove compatibility for every $L$, choose a nonzero meromorphic section $s$. Its divisor $D=\operatorname{div}(s)$ satisfies $L\simeq\mathcal O_X(D)$ by Book 9. Chern classes are additive, so the point calculation proves

$$
\operatorname{comp}_{\mathrm{dR},B}(c_1^{\mathrm{dR}}(L))
=2\pi i\,c_1^B(L), \tag{10.11}
$$

and

$$
c_{B,\mathrm{\acute et},n}
(c_1^B(L)\bmod n)=c_1^{\mathrm{\acute et}}(L), \tag{10.12}
$$

with the coefficient twist understood. Since $H^2$ of a connected curve is rank one, all these classes depend only on $\deg L$ in top cohomology. Degree-zero line bundles remain visible in their Kummer $H^1$ torsors and in Jacobian geometry, not in $c_1$ on the curve.

## 11. Maps, correspondences, and Hecke operators

Algebraic correspondences are the principal reason to demand compatibility beyond vector-space isomorphisms. Their action mixes contravariant pullback with covariant trace. We prove that both operations compare, then composition, transpose, and Hecke actions follow formally and with the correct variance.

### 11.1 Pullback and transfer

For any morphism $f:X\to Y$, the comparison squares for pullback commute because all comparison maps arise from functorial morphisms of complexes or sites. If $f$ is finite of degree $d$, each theory also has $f_*$ and satisfies

$$
f_*f^*=d,
\qquad
f_*(f^*a\smile b)=a\smile f_*b. \tag{11.1}
$$

For Betti cohomology, $f_*$ is dual to the homological transfer described in Section 2.5. For de Rham cohomology, it is trace on functions and differentials, with residue compatibility from Book 9 and the construction in Book 46. For étale cohomology, it is the trace of Book 21.

The comparison of $f_*$ is most safely deduced from adjointness. In Betti, de Rham, and étale cohomology, $f_*$ is the unique map satisfying

$$
\operatorname{Tr}_Y(f_*x\smile y)
=\operatorname{Tr}_X(x\smile f^*y)
$$

in complementary degrees. The pairings are perfect, comparison commutes with $f^*$ and cup product, and Chapter 10 has already matched the three top traces, including the factor $2\pi i$ and the Tate twist. Transporting the displayed identity through either comparison therefore characterizes the transported map as $f_*$. Hence

$$
\operatorname{comp}\circ f_*=f_*\circ\operatorname{comp} \tag{11.2}
$$

in both comparison theories.

### 11.2 Finite correspondences and variance

Let $\Gamma\subset X\times Y$ be an integral curve finite and surjective over both factors, and let $\Gamma^\nu$ be its normalization. Define

$$
\Gamma_*=(p_2)_*p_1^*:H^1(X)\longrightarrow H^1(Y). \tag{11.3}
$$

Extend linearly to finite correspondences. If $\Gamma$ is the graph of $f:X\to Y$, then $\Gamma_*=f_*$. Its transpose acts by $f^*$. This test fixes the direction.

Because comparison commutes separately with $p_1^*$ and $(p_2)_*$, it commutes with $\Gamma_*$. Thus one algebraic cycle induces a single rational endomorphism whose complex de Rham matrix, integral Betti matrix, and ℓ-adic matrix are scalar extensions of one another whenever source and target coincide.

Vertical or horizontal components factor through the cohomology of a point and act trivially on $H^1$. They can be included in a larger cycle group without changing degree-one operators. For nonconstant coefficient local systems, a correspondence does not act until a morphism between the two pulled-back coefficient systems is supplied; constant coefficients need no such additional datum.

### 11.3 Composition and transpose

If $\Gamma:X\dashrightarrow Y$ and $\Delta:Y\dashrightarrow Z$, their composite is the intersection product in $X\times Y\times Z$ pushed to $X\times Z$. At nontransverse points, local intersection multiplicity counts the length of the local tensor product. Pullback, trace, and the projection formula give

$$
(\Delta\circ\Gamma)_*=\Delta_*\Gamma_*. \tag{11.4}
$$

To prove it, first assume the fiber product of normalized correspondences is reduced and transverse. Then both sides sum pullback over the same composable sheets and trace to $Z$. In general, deform locally to the transverse case or filter the finite local algebra by residue-field factors; additivity of trace counts each factor with its length, exactly the intersection multiplicity. This proves (11.4) in every realization.

Transpose is adjoint for the degree-one pairing:

$$
\langle\Gamma_*x,y\rangle_Y
=\langle x,({}^t\Gamma)_*y\rangle_X. \tag{11.5}
$$

Expand the left side using (11.3), move $(p_2)_*$ across the pairing by the projection formula, and then move $p_1^*$ back by adjointness. This yields the right side. Comparison preserves every step, including the $2\pi i$ de Rham normalization and the étale twist.

One must not infer $f^*f_*=d$ from (11.1). The operator $f^*f_*$ can mix sheets and is represented by the fiber correspondence $X\times_YX$; only $f_*f^*$ on the target is multiplication by $d$.

### 11.4 Hecke actions and common characteristic polynomials

A Hecke operator on a curve is, for present purposes, a finite algebraic correspondence $T$. Its action is the pull--push operator (11.3). If $T$ is defined over $K\subseteq\mathbf C$, it preserves the rational Betti structure because it is induced by maps and integral transfers on singular chains. Hence

$$
P_T(t)=\det(t-T\mid H^1_B(X,\mathbf Q))\in\mathbf Q[t] \tag{11.6}
$$

is also the characteristic polynomial on $H^1_{\mathrm{dR}}(X/K)$ after extension to $\mathbf C$ and on every $H^1_{\mathrm{\acute et}}(X_{\bar K},\mathbf Q_\ell)$. If $T$ is an integral cycle, it preserves $H^1_B(X,\mathbf Z)$, so $P_T(t)\in\mathbf Z[t]$.

If $T={}^tT$, then (11.5) makes it self-adjoint for the polarization pairing. If $T$ and $S$ are correspondences whose geometric cycles commute under composition, their operators commute in all realizations. A rational idempotent $e$ cuts out corresponding direct summands over $\mathbf Q$, $\mathbf C$, and $\mathbf Q_\ell$. It cuts the integral ℓ-adic lattice only when the denominators of $e$ are ℓ-adic units. This denominator condition is indispensable in integral applications.

## 12. Polarizations and Jacobian period lattices

The alternating pairing on $H^1$ is not merely perfect. Together with the Hodge decomposition it is positive in the precise sense needed to construct the Jacobian. The resulting principally polarized complex torus packages period integrals, divisor classes of degree zero, and the common polarization in all realizations.

### 12.1 The analytic Jacobian

Let $V=H^0(X,\Omega^1_X)^\vee$. Integration sends a homology class to the functional

$$
\gamma\longmapsto\left(\omega\mapsto\int_\gamma\omega\right).
$$

Its image $\Lambda\subset V$ is a lattice of real rank $2g$. Discreteness follows from the normalized period matrix $(I_g\ \tau)$ and positive definiteness of $\operatorname{Im}\tau$: a bounded set in $\mathbf C^g$ contains only finitely many vectors $m+\tau n$ with $m,n\in\mathbf Z^g$. Define

$$
J(X)^{\mathrm{an}}=V/\Lambda. \tag{12.1}
$$

This compact complex torus is the analytic Jacobian.

Fix $p_0\in X(\mathbf C)$. The Abel--Jacobi map is

$$
\operatorname{AJ}_{p_0}:X^{\mathrm{an}}\to J(X)^{\mathrm{an}},
\qquad p\longmapsto
\left(\omega\mapsto\int_{p_0}^p\omega\right)\bmod\Lambda. \tag{12.2}
$$

Changing the path adds a period, so the map is well defined. Differentiating (12.2) shows that its cotangent map is the identity on holomorphic differentials. Extending additively to divisors of degree zero gives a homomorphism $\operatorname{Div}^0(X)\to J(X)^{\mathrm{an}}$.

If $D=\operatorname{div}(f)$, cut the surface along a symplectic basis of loops and along paths from $p_0$ to the points in $D$. A branch of $\log f$ exists on the cut surface. Apply Stokes' theorem to $d(\log f\,\omega)=d\log f\wedge\omega$; the latter vanishes because it has holomorphic type $(2,0)$ on a curve. The small boundary circles contribute $2\pi i$ times the Abel sum of $D$, while paired sides of the symplectic cuts contribute periods. Hence the Abel sum is in $\Lambda$ and is zero in the torus.

For the converse, use the analytic exponential sequence

$$
0\longrightarrow\mathbf Z\longrightarrow\mathcal O_X
\xrightarrow{\exp(2\pi i\,\cdot)}\mathcal O_X^\times
\longrightarrow1. \tag{12.3}
$$

Its long exact sequence identifies the kernel of degree on $\operatorname{Pic}(X)$ with

$$
H^1(X,\mathcal O_X)/H^1(X,\mathbf Z).
$$

Serre duality identifies $H^1(X,\mathcal O_X)$ with $H^0(X,\Omega^1_X)^\vee$, and a Čech calculation with local equations of a divisor identifies the image of $\mathcal O_X(D)$ with the Abel integral of $D$. Therefore zero Abel--Jacobi image means that $\mathcal O_X(D)$ is trivial. A trivializing meromorphic section has divisor $D$, so $D$ is principal. Thus

$$
\operatorname{Pic}^0(X)\simeq J(X)^{\mathrm{an}}. \tag{12.4}
$$

This is Abel's theorem; the decisive obstruction is exactly the period functional.

### 12.2 The principal Riemann form

Transport the intersection form on $H_1(X,\mathbf Z)$ to $\Lambda$. It is an integral alternating form $E:\Lambda\times\Lambda\to\mathbf Z$. In normalized coordinates $\Lambda=\mathbf Z^g+\tau\mathbf Z^g$, set

$$
E(m+\tau n,m'+\tau n')=m^tn'-n^tm'. \tag{12.5}
$$

This is the matrix $J$ of Section 3.3 and is unimodular. Symmetry of $\tau$ shows

$$
E(iv,iw)=E(v,w),
$$

and positivity of $\operatorname{Im}\tau$ shows $E(v,iv)>0$ for nonzero $v$ in the underlying real vector space, with the sign fixed by our orientation. Thus $E$ is a positive Riemann form.

A positive integral Riemann form determines an ample line bundle on a complex torus. In this case one constructs its factors of automorphy explicitly from (12.5): for $\lambda=m+\tau n$,

$$
j_\lambda(z)=
\exp\bigl(-\pi i\,n^t\tau n-2\pi i\,n^tz\bigr).
$$

The identity

$$
j_{\lambda+\mu}(z)=j_\lambda(z+\mu)j_\mu(z)
$$

uses the integrality and symmetry in (12.5), so these factors descend the trivial line bundle on $V$ to a line bundle $\Theta$ on $V/\Lambda$. The convergence and positivity assertions can be seen directly from the theta series

$$
\vartheta(z,\tau)=
\sum_{r\in\mathbf Z^g}
\exp\bigl(\pi i\,r^t\tau r+2\pi i\,r^tz\bigr).
$$

Positive definiteness of $\operatorname{Im}\tau$ makes the series and all its derivatives converge normally on compact sets. Reindexing $r$ proves the transformation laws

$$
\vartheta(z+m,\tau)=\vartheta(z,\tau),
$$

$$
\vartheta(z+\tau n,\tau)
=\exp\bigl(-\pi i\,n^t\tau n-2\pi i\,n^tz\bigr)
\vartheta(z,\tau).
$$

Thus $\vartheta$ is a holomorphic section of $\Theta$. For $\Theta^{\otimes k}$, use the theta series with characteristics
$(a,b)\in(k^{-1}\mathbf Z^g/\mathbf Z^g)^2$ and the corresponding corrected exponential factors. Their Fourier expansions have distinct characters modulo $k\mathbf Z^g$. Fourier orthogonality shows that, for $k\geq3$, their common values separate two distinct points; differentiating the expansions shows that their first derivatives separate every nonzero tangent vector. They therefore give a holomorphic embedding of the compact torus into projective space. Hence $\Theta$ is ample.

The first Chern form of $\Theta$ has imaginary part $E$. Unimodularity says that the homomorphism

$$
\Lambda\longrightarrow\operatorname{Hom}(\Lambda,\mathbf Z),
\qquad \lambda\longmapsto E(\lambda,-),
$$

is an isomorphism, so the induced homomorphism from the torus to its dual has degree one and is an isomorphism. This proves, rather than merely names, the canonical principal polarization of the Jacobian.

### 12.3 Comparison with cup-product polarizations

The Betti polarization on $H^1_B(X,\mathbf Z)$ is $Q_B$ from (3.4). The de Rham pairing is

$$
Q_{\mathrm{dR}}(\alpha,\beta)
=\operatorname{Tr}_{\mathrm{dR}}(\alpha\smile\beta), \tag{12.6}
$$

and Book 46 proves that it is perfect alternating with the Hodge subspace Lagrangian. Equation (10.6) states the precise comparison:

$$
Q_B(\operatorname{comp}\alpha,\operatorname{comp}\beta)
=2\pi iQ_{\mathrm{dR}}(\alpha,\beta). \tag{12.7}
$$

The étale polarization is

$$
Q_\ell:H^1_{\mathrm{\acute et}}(X,\mathbf Z_\ell)
\times H^1_{\mathrm{\acute et}}(X,\mathbf Z_\ell)
\longrightarrow\mathbf Z_\ell(-1), \tag{12.8}
$$

obtained by cup product followed by the canonical identification
$H^2_{\mathrm{\acute et}}(X,\mathbf Z_\ell)\simeq\mathbf Z_\ell(-1)$. Equivalently, without moving a twist across the pairing, it is

$$
H^1_{\mathrm{\acute et}}(X,\mathbf Z_\ell)
\times H^1_{\mathrm{\acute et}}(X,\mathbf Z_\ell(1))
\longrightarrow\mathbf Z_\ell.
$$

Finite comparison of trace identifies this second form with the Betti cup pairing with coefficients in $\mathbf Z_\ell(1)$.

Positivity belongs to the Betti--Hodge pair, not to the ℓ-adic vector space by itself. The ℓ-adic comparison transports the alternating form and its unimodularity, but $\mathbf Q_\ell$ has no complex conjugation giving the inequality (6.10). This is an example of a structure compatible across realizations whose positivity is meaningful only in one realization.

### 12.4 Isogenies and denominators

An arbitrary comparison theorem for higher-dimensional abelian varieties is not needed here. What the curve package does control is the denominator behavior of operators on a Jacobian period lattice and of isogenies between the resulting complex tori.

Let $u:V/\Lambda\to V'/\Lambda'$ be an isogeny of $g$-dimensional complex tori, of topological degree $d$. It is a finite covering. Pullback on singular degree-one cohomology is injective with finite cokernel, and transfer gives

$$
u_*u^*=d\,\operatorname{id}. \tag{12.9}
$$

Thus $d^{-1}u_*$ is the rational inverse. After tensoring with $\mathbf Z_\ell$, it preserves the integral inverse lattice precisely when $\ell\nmid d$; over $\mathbf Q_\ell$ it is always defined.

For an operator actually induced by a curve correspondence, Chapter 11 transports this rational inverse and its denominator condition to the de Rham and étale realizations of the curve. Its adjoint is induced by the transpose correspondence. This is the precise cross-realization assertion available here; no comparison for the cohomology of an unrelated abelian variety has been assumed. Positivity of the associated Rosati form belongs to the polarized Betti--Hodge realization constructed above.

## 13. Families, horizontal periods, and monodromy

A single curve gives a static comparison. In a smooth family, cycles move locally constantly while differential forms vary holomorphically. Their period integrals therefore turn the topological local system into the horizontal sections of the Gauss--Manin connection. This explains the geometric meaning of the connection constructed algebraically in Book 46.

### 13.1 The Betti local system

Let $f:X\to S$ be a smooth proper family of geometrically connected complex curves, with $S$ a smooth complex algebraic variety. Analytically, $f^{\mathrm{an}}$ is locally a differentiable fiber bundle. To see this, choose a Hermitian metric, take the orthogonal complement to the vertical tangent bundle, and integrate horizontal vector fields over a sufficiently small neighborhood in $S$. Properness ensures their flows exist uniformly on the compact fibers. Hence all nearby fibers are diffeomorphic.

The groups

$$
\mathbb H_{\mathbf Z}=R^1f^{\mathrm{an}}_*\mathbf Z
$$

form a local system of free rank $2g$ abelian groups. Parallel transport along a path gives an isomorphism of fiber cohomologies; a loop gives monodromy. Cup product and the oriented fundamental class are preserved by orientation-preserving transport, so $\mathbb H_{\mathbf Z}$ is a symplectic local system.

Tensoring with $\mathcal O_{S^{\mathrm{an}}}$ gives a holomorphic bundle

$$
\mathcal H_B=\mathbb H_{\mathbf Z}\otimes\mathcal O_{S^{\mathrm{an}}}
$$

with its flat connection $\nabla_B$: in a locally constant basis, differentiate only the coefficient functions. Its horizontal sections are exactly $\mathbb H_{\mathbf C}$.

### 13.2 Gauss--Manin as the differential of periods

Book 46 constructs the algebraic bundle

$$
\mathcal H_{\mathrm{dR}}=R^1f_*\Omega^\bullet_{X/S}
$$

with its integrable Gauss--Manin connection. Fiberwise de Rham comparison glues to an isomorphism of analytic bundles

$$
(\mathcal H_{\mathrm{dR}}^{\mathrm{an}},\nabla_{\mathrm{GM}})
\xrightarrow{\sim}(\mathcal H_B,\nabla_B). \tag{13.1}
$$

To prove horizontality, let $\gamma_s$ be a locally transported cycle and let $\omega_s$ be a relative de Rham class. Lift $\gamma_s$ to the horizontal cylinder swept out by transport. Stokes' theorem on that cylinder gives

$$
d\left(\int_{\gamma_s}\omega_s\right)
=\int_{\gamma_s}\nabla_{\mathrm{GM}}\omega_s. \tag{13.2}
$$

Algebraically, the right side is obtained by lifting a relative form to an absolute form and retaining its component with one base differential, exactly the filtered-complex construction of Gauss--Manin. Thus (13.2) proves (13.1), not merely equality on each fiber.

In particular, a de Rham class is horizontal precisely when all of its periods against locally constant cycles are locally constant. The Picard--Fuchs equation of a family is the scalar differential equation obtained by expressing (13.2) in a frame and eliminating the other period functions.

### 13.3 Hodge variation and polarization

The Hodge subbundle

$$
F^1=f_*\Omega^1_{X/S}\subset\mathcal H_{\mathrm{dR}}
$$

analytifies to the holomorphic subbundle with fiber $H^{1,0}(X_s)$. It is generally not horizontal. Book 46 proves Griffiths transversality

$$
\nabla F^1\subseteq\Omega^1_S\otimes\mathcal H_{\mathrm{dR}},
$$

and identifies its quotient component with cup product by the Kodaira--Spencer class. In degree one there is only one possible downward Hodge step, so this is the complete infinitesimal variation.

The cup-product pairing is horizontal. Indeed transport preserves the topological intersection form, while Book 46 proves the same statement from the product rule and horizontal trace. Differentiating the isotropy of $F^1$ makes its second fundamental form symmetric. Fiberwise positivity from (6.10) therefore varies smoothly and gives a polarized variation of weight-one Hodge structures.

The integral local system is essential here. A flat complex bundle plus a Hodge subbundle does not remember which monodromies are integral. The lattice $\mathbb H_{\mathbf Z}$ records exactly the rational structure from which the Jacobian family is reconstructed.

### 13.4 Correspondences in families

Suppose a relative correspondence is presented by a smooth proper curve $Z/S$ and finite locally free $S$-morphisms

$$
X\xleftarrow{p_1}Z\xrightarrow{p_2}X.
$$

Then $\Gamma_*=(p_2)_*p_1^*$ is defined on every fiber and commutes with base change. Pullback and trace commute with Gauss--Manin because they arise from morphisms of the filtered absolute de Rham complexes. Hence $\Gamma_*$ is horizontal. A cycle whose normalization is not smooth over $S$ requires a separate relative trace construction and is not included in this assertion.

Topologically, the same operator is a morphism of local systems: on a local differentiable trivialization it sums lifts over the finite sheets. Finite-coefficient comparison makes its reductions the corresponding étale operators. Thus the following structures commute simultaneously:

$$
\begin{array}{ccc}
\text{monodromy}&\longleftrightarrow&\text{correspondence action}\\
\downarrow&&\downarrow\\
\text{Gauss--Manin connection}&\longleftrightarrow&\text{horizontal endomorphism}.
\end{array} \tag{13.3}
$$

If $\Gamma$ is self-transpose, its action is self-adjoint fiberwise. If a rational idempotent is built from such correspondences, it cuts out a subvariation and the corresponding ℓ-adic sub-local system wherever its denominators are invertible.

## 14. Worked realizations

Concrete curves test the general normalizations. The examples below are not detachable decorations: each isolates a feature that can otherwise be obscured by formalism—top degree and $2\pi i$, a nontrivial period lattice, the genus count, and the asymmetry of pullback and trace.

### 14.1 The projective line and the punctured line

For $X=\mathbf P^1_\mathbf C$,

$$
H^0_B(X,\mathbf Z)=\mathbf Z,\qquad H^1_B(X,\mathbf Z)=0,
\qquad H^2_B(X,\mathbf Z)=\mathbf Z.
$$

Algebraic de Rham cohomology has the same dimensions. The top class is not represented by a global algebraic two-form, since a curve has none; it is the hypercohomology class of the Čech cocycle $dz/z$ for the cover by the two standard affine lines. Its de Rham trace is $1$, while integration around the equator gives $2\pi i$. This is the model for (10.5).

For $U=\mathbf G_m$, the class $dz/z$ lies in $H^1_{\mathrm{dR}}(U)$ and

$$
\int_{|z|=1}\frac{dz}{z}=2\pi i.
$$

Thus $H^1_B(U,\mathbf Z)=\mathbf Z$ and $H^1_{\mathrm{dR}}(U)=\mathbf C[dz/z]$. The cover $w^n=z$ represents the generator of $H^1_{\mathrm{\acute et}}(U,\mu_n)$ and has topological monodromy $e^{2\pi i/n}$. All three generators therefore agree with the conventions of Chapter 10.

### 14.2 A complex elliptic curve

Let $E_\tau=\mathbf C/(\mathbf Z+\tau\mathbf Z)$ with $\operatorname{Im}\tau>0$. The form $dz$ descends and has periods

$$
\int_a dz=1,\qquad\int_b dz=\tau.
$$

Hence the analytic Jacobian is $E_\tau$ itself. The Hodge decomposition is

$$
H^1_B(E_\tau,\mathbf C)=\mathbf C[dz]\oplus\mathbf C[d\bar z].
$$

The bilinear identity gives

$$
\int_{E_\tau}dz\wedge d\bar z=\bar\tau-\tau,
\qquad
i\int_{E_\tau}dz\wedge d\bar z=2\operatorname{Im}\tau>0. \tag{14.1}
$$

If $E$ is given algebraically by $y^2=4x^3-g_2x-g_3$, its invariant differential $dx/y$ pulls back to a nonzero scalar multiple of $dz$. The scalar and the pair of lattice periods encode the de Rham--Betti comparison. At every $\ell$, $H^1_{\mathrm{\acute et}}(E,\mathbf Z_\ell)$ is the completion of the same rank-two Betti lattice, while its arithmetic Galois action appears only when the equation descends to a smaller field.

### 14.3 A hyperelliptic curve

Let

$$
X:y^2=f(x)
$$

with $f\in\mathbf C[x]$ squarefree of degree $2g+1$ or $2g+2$. The double map $X\to\mathbf P^1$ is branched at $2g+2$ points, counting infinity when necessary. Riemann--Hurwitz gives

$$
2-2g(X)=2\cdot2-(2g+2),
$$

so the topological and algebraic genus is $g$. A basis of holomorphic differentials is

$$
\omega_j=\frac{x^{j-1}dx}{y},\qquad1\leq j\leq g. \tag{14.2}
$$

At finite branch points, $x-a=t^2$ makes $dx/y$ regular. At infinity, the degree bound $j\leq g$ is exactly what prevents a pole. Linear independence is clear from their distinct powers of $x$, and dimension $g$ proves they form a basis.

Choosing branch cuts produces $g$ pairs of symplectic cycles. Their integrals of (14.2) form the matrices $A,B$ of (6.8); the topology of the cuts makes the intersection matrix $J$, while (6.9)--(6.10) force $A^{-1}B$ to be symmetric with positive imaginary part. The finite étale comparison then gives $H^1_{\mathrm{\acute et}}(X,\mathbf Z/\ell^m)\simeq(\mathbf Z/\ell^m)^{2g}$ without making any choice of branch cuts in the final isomorphism.

### 14.4 A correspondence sanity check

Let $f:X\to Y$ be finite of degree $d$. The graph $\Gamma_f$ acts from $X$ to $Y$ by $f_*$, while its transpose acts from $Y$ to $X$ by $f^*$. Therefore

$$
(\Gamma_f\circ{}^t\Gamma_f)_*=f_*f^*=d
\quad\text{on }H^1(Y). \tag{14.3}
$$

In the other order,

$$
({}^t\Gamma_f\circ\Gamma_f)_*=f^*f_*
\quad\text{on }H^1(X), \tag{14.4}
$$

which need not be scalar. For example, if $f$ is a nontrivial Galois cover with group $G$, then

$$
f^*f_*=\sum_{\sigma\in G}\sigma^*. \tag{14.5}
$$

It is $d$ times the projector onto the invariant part after $d$ is inverted, and it vanishes on many nontrivial isotypic components. Equations (14.3)--(14.5) hold identically in Betti, de Rham, and étale cohomology. They are a decisive test of correspondence variance.

## 15. The comparison package

We can now state the result in the form needed for later arithmetic geometry. Every arrow has been constructed, every normalization has been tested on a point, and every compatibility follows at chain, complex, or site level rather than from a dimension count.

### 15.1 The simultaneous theorem

**Simultaneous comparison theorem for curves.** Let $K\subseteq\mathbf C$, let $X/K$ be a smooth, proper, geometrically connected curve of genus $g$, and let $\ell$ be a prime. Then:

1. Integration gives a functorial multiplicative isomorphism

   $$
   H^n_{\mathrm{dR}}(X/K)\otimes_K\mathbf C
   \xrightarrow{\sim}H^n_B(X^{\mathrm{an}},\mathbf Q)\otimes\mathbf C.
   $$

2. Analytification gives functorial multiplicative isomorphisms

   $$
   H^n_B(X^{\mathrm{an}},\mathbf Z/\ell^m)
   \xrightarrow{\sim}
   H^n_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Z/\ell^m)
   $$

   and, after inverse limit and scalar extension,

   $$
   H^n_B(X^{\mathrm{an}},\mathbf Z_\ell)
   \xrightarrow{\sim}H^n_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Z_\ell),
   \qquad
   H^n_B(X^{\mathrm{an}},\mathbf Q_\ell)
   \xrightarrow{\sim}H^n_{\mathrm{\acute et}}(X_{\mathbf C},\mathbf Q_\ell).
   $$

3. The degree-one groups have rank or dimension $2g$. The Betti lattice is unimodular symplectic; its complexification has Hodge decomposition

   $$
   H^1_B(X,\mathbf C)=H^{1,0}\oplus H^{0,1},
   $$

   and the transported filtration agrees with the algebraic de Rham Hodge filtration.

4. The comparisons commute with pullback, finite trace, cup product, divisor and first Chern classes, finite correspondences, composition, and transpose. Point classes fix the trace normalization. The de Rham top trace differs from integration by $2\pi i$, while étale top duality uses the Tate twist.

5. The intersection pairing polarizes the weight-one Hodge structure and gives the canonical principal polarization of the Jacobian. Under comparison it becomes the de Rham cup--trace pairing, scaled as in (12.7), and the Tate-twisted étale pairing.

6. Any algebraic correspondence defined over $K$ acts through one rational Betti operator. Its de Rham and ℓ-adic characteristic polynomials are obtained by scalar extension. Transpose is adjoint in every realization.

**Proof.** Statements 1 and 3 are the comparison isomorphism (5.4), the decomposition (6.2), and the integral surface calculation of Chapter 3. Statement 2 is the finite comparison theorem of Section 8.2 together with the vanishing of the Milnor term in Section 9.1. Point and Kummer calculations in Chapter 10 prove every trace and cycle normalization; multiplicativity then gives the pairings. Chapter 11 proves correspondence compatibility. The Riemann bilinear relations and the construction of Chapter 12 prove the polarization statement. Each cited result has the displayed hypotheses, so their composition proves all six assertions. $\square$

If $X$ is smooth but not proper, the logarithmic-boundary argument of Section 5.3 and the finite-coefficient argument of Chapter 8 give the de Rham, finite, and ℓ-adic comparisons. Compact supports enter where duality requires them. The pure weight-one polarization and compact Jacobian statement are proper phenomena and are not asserted for an open curve.

### 15.2 Hypothesis and normalization audit

The hypotheses have distinct roles.

- Smoothness makes $X^{\mathrm{an}}$ a manifold, makes algebraic differentials locally free, and identifies finite unramified maps with covering maps. Singular curves require intersection cohomology, normalization terms, or dualizing complexes and are outside this comparison statement.

- Hypothesis (T) of Chapter 2—the finite triangulability of every Riemann surface occurring here, classically the theorem of Radó plus surface triangulability—is a standing geometric input that this book does not prove. It is consumed once, in fixing the simplicial model of Section 2.1 from which all Betti groups, products, dualities, and relative groups are then derived combinatorially; dropping it suspends the integral lattice itself, not any later step.

- Properness makes $X^{\mathrm{an}}$ compact, algebraizes finite analytic covers without boundary data, gives ordinary Poincaré duality, and makes the Jacobian compact. Open curves use compact support and boundary monodromy.

- Geometric connectedness makes $H^0$ and top cohomology rank one and gives a single fundamental class. For a disconnected curve, every statement applies componentwise.

- The embedding $K\subseteq\mathbf C$ is necessary to form the analytic curve. The de Rham $K$-structure and the Betti rational structure are different structures joined only after scalar extension.

- Finite étale comparison over $\mathbf C$ has no restriction on $\ell$. Over a field of positive characteristic, comparison with a complex surface is unavailable and étale coefficients must be prime to the characteristic in the theory used here.

- The factor $2\pi i$ belongs to the unnormalized algebraic $d\log$ convention. The Tate twist belongs to the canonical étale trace. Removing either without making a choice changes the theorem.

- Integral direct summands cut out by correspondences require integral projectors. A rational projector with denominator divisible by $\ell$ need not preserve the $\mathbf Z_\ell$ lattice.

- When the coefficient prime equals the residue characteristic of a decomposition group, the
  Betti--étale comparison does not identify the Hodge filtration. Section 9.5 isolates the
  additional smooth-proper Hodge--Tate theorem. Its subquotient consequence is formal, but the
  comparison theorem itself is not proved by the complex or crystalline arguments here.

These are genuine boundaries, not presentational cautions. Dropping them changes examples: a punctured curve has boundary classes, a nodal curve is not a surface at the node, a purely rational idempotent need not act integrally, and an untwisted étale trace is not canonical.

### 15.3 Conclusion

A complex algebraic curve now carries one cohomological object seen through three coefficient worlds. The finite triangulation supplies the integral lattice, orientation, and intersection form as combinatorial data. Algebraic differential forms provide the $K$-structure and Hodge filtration. Finite étale covers and inverse limits provide the ℓ-adic lattice and, after descent, its arithmetic action. Integration and Riemann existence prove that these are realizations of the same geometry rather than parallel groups with matching dimensions.

The comparison is structural. A point determines compatible cycle classes and fixes every trace. A line bundle has winding, logarithmic, and Kummer Chern classes. A finite map has the same pullback and transfer. A correspondence has the same pull--push action, the same transpose adjoint, and the same characteristic polynomial. The cup product is simultaneously the surface intersection form, the de Rham residue pairing, and the Tate-twisted étale pairing. Its Hodge positivity constructs the principally polarized Jacobian.

Thus the reusable chain is

$$
\text{integral cycles}
\longleftrightarrow\text{periods and the Hodge filtration}
\longleftrightarrow\text{finite covers and ℓ-adic classes},
$$

with rational structures, polarizations, Hecke correspondences, and traces preserved throughout. This is the complete comparison package for smooth proper curves over subfields of the complex numbers.
