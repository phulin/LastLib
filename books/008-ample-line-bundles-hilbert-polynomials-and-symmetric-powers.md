# Ample Line Bundles, Hilbert Polynomials, and Symmetric Powers

## Contents

1. [Projective geometry over a base](#1-projective-geometry-over-a-base)
   - [Why relative projective geometry](#11-why-relative-projective-geometry)
   - [Graded algebras and homogeneous localization](#12-graded-algebras-and-homogeneous-localization)
   - [The construction of relative Proj](#13-the-construction-of-relative-proj)
   - [Standard opens and base change](#14-standard-opens-and-base-change)
   - [Twisting sheaves](#15-twisting-sheaves)
   - [Veronese algebras and presentations](#16-veronese-algebras-and-presentations)
2. [Projective space and its universal meaning](#2-projective-space-and-its-universal-meaning)
   - [Projective bundles](#21-projective-bundles)
   - [Invertible quotients](#22-invertible-quotients)
   - [Sections without common zeros](#23-sections-without-common-zeros)
   - [Closed subschemes from homogeneous ideals](#24-closed-subschemes-from-homogeneous-ideals)
3. [Projective and quasi-projective morphisms](#3-projective-and-quasi-projective-morphisms)
   - [Definitions that survive change of base](#31-definitions-that-survive-change-of-base)
   - [Elementary permanence properties](#32-elementary-permanence-properties)
   - [Separatedness, finite type, and properness](#33-separatedness-finite-type-and-properness)
   - [What projectivity does not mean](#34-what-projectivity-does-not-mean)
4. [Very ample and ample invertible sheaves](#4-very-ample-and-ample-invertible-sheaves)
   - [The evaluation map and global generation](#41-the-evaluation-map-and-global-generation)
   - [Very ampleness as separation](#42-very-ampleness-as-separation)
   - [The affine-open definition of ampleness](#43-the-affine-open-definition-of-ampleness)
   - [Serre's criteria](#44-serres-criteria)
   - [Tensor powers and operations](#45-tensor-powers-and-operations)
5. [Base change and descent](#5-base-change-and-descent)
   - [Pullback of positivity](#51-pullback-of-positivity)
   - [Faithfully flat descent of very ampleness](#52-faithfully-flat-descent-of-very-ampleness)
   - [Descent of ampleness and projectivity](#53-descent-of-ampleness-and-projectivity)
   - [Necessary hypotheses and failures](#54-necessary-hypotheses-and-failures)
6. [Serre vanishing and projective cohomology](#6-serre-vanishing-and-projective-cohomology)
   - [The projective-space calculation](#61-the-projective-space-calculation)
   - [Vanishing and generation in high degree](#62-vanishing-and-generation-in-high-degree)
   - [Relative finiteness](#63-relative-finiteness)
   - [Regularity and uniform bounds](#64-regularity-and-uniform-bounds)
7. [Hilbert functions and Hilbert polynomials](#7-hilbert-functions-and-hilbert-polynomials)
   - [From dimensions to a polynomial](#71-from-dimensions-to-a-polynomial)
   - [The polynomial of a projective scheme](#72-the-polynomial-of-a-projective-scheme)
   - [Degree, dimension, and examples](#73-degree-dimension-and-examples)
   - [Dependence on the polarization](#74-dependence-on-the-polarization)
8. [Hilbert polynomials in families](#8-hilbert-polynomials-in-families)
   - [Fiberwise Euler characteristics](#81-fiberwise-euler-characteristics)
   - [Flatness forces constancy](#82-flatness-forces-constancy)
   - [Flattening strata](#83-flattening-strata)
   - [Constancy and the flatness boundary](#84-constancy-and-the-flatness-boundary)
9. [Projective embeddings of curves and abelian schemes](#9-projective-embeddings-of-curves-and-abelian-schemes)
   - [Embedding projective curves](#91-embedding-projective-curves)
   - [Uniform embeddings in families](#92-uniform-embeddings-in-families)
   - [Polarized abelian schemes](#93-polarized-abelian-schemes)
   - [Uniform very ampleness](#94-uniform-very-ampleness)
10. [Finite flat families and effective divisors](#10-finite-flat-families-and-effective-divisors)
    - [Families of length $d$](#101-families-of-length-d)
    - [Relative effective Cartier divisors](#102-relative-effective-cartier-divisors)
    - [Divisors on smooth relative curves](#103-divisors-on-smooth-relative-curves)
    - [Norms and addition](#104-norms-and-addition)
    - [Descent along finite locally free covers](#105-descent-along-finite-locally-free-covers)
    - [Descent of morphisms into a quasi-projective target](#106-descent-of-morphisms-into-a-quasi-projective-target)
11. [Symmetric powers](#11-symmetric-powers)
    - [Quotients by permutation](#111-quotients-by-permutation)
    - [Sheaf quotients and orbit functors](#112-sheaf-quotients-and-orbit-functors)
    - [Configuration spaces](#113-configuration-spaces)
    - [The universal divisor on a smooth curve](#114-the-universal-divisor-on-a-smooth-curve)
    - [Symmetric powers and base change](#115-symmetric-powers-and-base-change)
12. [The Hilbert functors needed here](#12-the-hilbert-functors-needed-here)
    - [Precise functors](#121-precise-functors)
    - [The Grassmannian construction](#122-the-grassmannian-construction)
    - [Representability with fixed polynomial](#123-representability-with-fixed-polynomial)
    - [The finite-length Hilbert scheme](#124-the-finite-length-hilbert-scheme)
    - [Curves: Hilbert scheme equals symmetric power](#125-curves-hilbert-scheme-equals-symmetric-power)
13. [Universal constructions for later geometry](#13-universal-constructions-for-later-geometry)
    - [Graphs and spaces of morphisms](#131-graphs-and-spaces-of-morphisms)
    - [Closed loci inside parameter spaces](#132-closed-loci-inside-parameter-spaces)
    - [Projective parameter spaces for curve families](#133-projective-parameter-spaces-for-curve-families)
    - [Boundary distinctions](#134-boundary-distinctions)
14. [Synthesis](#14-synthesis)
    - [The three dictionaries](#141-the-three-dictionaries)
    - [The reusable theorem package](#142-the-reusable-theorem-package)
    - [Conclusion](#143-conclusion)

## 1. Projective geometry over a base

### 1.1 Why relative projective geometry

Affine geometry encodes a space by functions. Projective geometry instead encodes directions, one-dimensional quotients, and homogeneous equations. Over a field this distinction is already useful; over a varying base it becomes indispensable. A family of plane curves, for example, is not one curve with coefficients in a large field. Its coefficients are functions on the base, its fibers may specialize, and every construction must commute with replacing the base.

The device that controls all of this is relative Proj. It turns a graded algebra over a scheme $S$ into an $S$-scheme whose affine charts are obtained by homogeneous localization. The grading simultaneously remembers a line bundle. That line bundle is the source of projective embeddings, eventually makes coherent sheaves generated by sections, and converts dimensions of spaces of sections into Hilbert polynomials.

All schemes in this book are ordinary schemes, and all morphisms are morphisms of schemes. A line bundle means an invertible $\mathcal O_X$-module; it is a sheaf, not the total space of a geometric bundle. We write $\mathcal L^n=\mathcal L^{\otimes n}$ for $n\geq0$, $\mathcal L^{-n}=(\mathcal L^\vee)^n$, and $X_T=X\times_S T$. Unless a stronger hypothesis is stated, bases need not be fields, reduced, connected, or noetherian.

Two earlier volumes supply all of the homological input used below, and it is worth listing what
is taken from them, because everything cohomological in this book is a consequence of those
statements rather than of an unproved formalism. Book 7a supplies derived categories, derived
functors, hypercohomology, the machinery of spectral sequences, the Leray spectral sequence
(Book 7a, Chapter 8), and the recognition of a complex of acyclic sheaves as a model for
$R\Gamma$ (Book 7a, Section 7.4). Book 7b supplies the cohomology of quasi-coherent sheaves on
schemes, in the following form:

- the affine dictionary $M\mapsto\widetilde M$, an exact equivalence between $A$-modules and
  quasi-coherent sheaves on $\operatorname{Spec}A$ (Book 7b, Theorem 2.3 and Corollary 2.4), the
  extension of sections from a principal open after multiplication by a power (Corollary 2.5), and
  the fact that quasi-coherence may be tested on any one affine open cover (Corollary 2.6);
- permanence of quasi-coherence under kernels, cokernels, extensions, colimits, tensor products
  and pullback (Book 7b, Theorems 2.7 and 2.8), under pushforward along a quasi-compact
  quasi-separated morphism (Theorem 2.10), and the exhaustion of a quasi-coherent sheaf on a
  noetherian scheme by its coherent subsheaves (Theorem 2.11);
- Serre's affine vanishing theorem $H^p(\operatorname{Spec}A,\mathcal F)=0$ for $p>0$ over an
  arbitrary ring (Book 7b, Theorem 3.9), the acyclicity of affine opens (Corollary 3.10), and the
  cohomological invisibility of affine morphisms, in particular of closed immersions
  (Corollary 3.11);
- the finite alternating Čech model: on a quasi-compact separated scheme with a finite affine open
  cover of $n$ members, a complex of length at most $n-1$ represents $R\Gamma$ (Book 7b,
  Theorem 4.2), a short exact sequence of quasi-coherent sheaves gives a short exact sequence of
  such complexes and hence a long exact cohomology sequence (Corollary 4.4), and Mayer–Vietoris
  (Theorem 4.3);
- quasi-coherence of $R^pf_*$ for $f$ quasi-compact and quasi-separated, together with its
  computation $R^pf_*\mathcal F|_V=\widetilde{H^p(f^{-1}V,\mathcal F)}$ over an affine open
  (Book 7b, Theorem 4.7), the vanishing $H^p=0$ for $p\geq n$ on a separated scheme covered by $n$
  affines and the corresponding vanishing of $R^pf_*$ (Corollary 4.8), and Leray with its
  degeneration over an affine base (Corollary 4.9);
- derived coefficient change for a flat quasi-coherent sheaf on a quasi-compact separated
  $A$-scheme, $R\Gamma(X,\mathcal F)\otimes^L_AM\simeq R\Gamma(X,\mathcal F\otimes_AM)$ and
  $B\otimes^L_AR\Gamma(X,\mathcal F)\simeq R\Gamma(X_B,\mathcal F_B)$ (Book 7b, Theorem 5.2),
  underived flat base change without flatness of the sheaf (Theorem 5.3, Corollary 5.4),
  compatibility of cohomology with filtered colimits (Propositions 5.5–5.7), and Grothendieck
  vanishing above the dimension of a noetherian space (Theorem 5.8, Corollary 5.9);
- the complete computation of $H^\bullet(\mathbf P^r_A,\mathcal O(n))$ over an arbitrary ring
  (Book 7b, Theorem 6.5), the freeness of all these modules, the compatibility of their formation
  with every ring map, the Euler characteristic $\binom{n+r}{r}$ over a field (Corollary 6.6), and
  the perfect top pairing (Theorem 6.7);
- Hilbert's syzygy theorem for finite graded modules over a polynomial ring in $r+1$ variables
  over a field, with resolutions of length at most $r+1$ by finite sums of shifts, stable under
  field extension (Book 7b, Theorem 7.4, Corollary 7.5), and generic freeness over a noetherian
  domain in its plain, graded, and complex-spreading-out forms (Theorem 7.6, Corollaries 7.7
  and 7.8).

These are used freely, and cited at each point where they enter. No further cohomological or
graded-algebra input is assumed anywhere in this book.

### 1.2 Graded algebras and homogeneous localization

Let $A=\bigoplus_{n\geq0}A_n$ be a nonnegatively graded ring. Multiplication satisfies $A_mA_n\subseteq A_{m+n}$. Its irrelevant ideal is

$$
A_+=\bigoplus_{n>0}A_n.
$$

A prime ideal $\mathfrak p$ is homogeneous when it is generated by homogeneous elements. Define

$$
\operatorname{Proj}A=
\{\mathfrak p: \mathfrak p\text{ homogeneous prime and }A_+\not\subseteq\mathfrak p\}.
$$

If $f\in A_d$ is homogeneous of positive degree, localize at $1,f,f^2,\ldots$. The localization $A_f$ is graded by $\deg(a/f^r)=\deg(a)-rd$, and its degree-zero part is denoted $(A_f)_0$. The standard open

$$
D_+(f)=\{\mathfrak p:f\notin\mathfrak p\}
$$

will be $\operatorname{Spec}(A_f)_0$. These opens cover because the points under consideration do not contain $A_+$. Moreover

$$
D_+(f)\cap D_+(g)=D_+(fg),
$$

and localization identifies the corresponding rings. Affine gluing therefore supplies the scheme structure.

Two warnings explain the definition. First, using every prime of $A$ would retain the vertex of the affine cone, whereas projective geometry records directions away from that vertex. Second, $(A_f)_0$, not all of $A_f$, gives the chart: multiplying homogeneous coordinates by a common scalar must not change a projective point.

For $A=k[x_0,\ldots,x_r]$ with every variable in degree one, the chart $D_+(x_i)$ has coordinate ring

$$
k[x_0/x_i,\ldots,\widehat{x_i/x_i},\ldots,x_r/x_i],
$$

so the construction recovers $\mathbf P^r_k$. If $A_+=0$, Proj is empty. If $A=k[x]$ with $\deg x=2$, Proj is $\operatorname{Spec}k$: the grading affects twists even when the underlying scheme is unchanged.

### 1.3 The construction of relative Proj

Let $S$ be a scheme and

$$
\mathcal A=\bigoplus_{n\geq0}\mathcal A_n
$$

a quasi-coherent graded $\mathcal O_S$-algebra. We normally assume $\mathcal A_0=\mathcal O_S$. Over an affine open $U=\operatorname{Spec}R$, the affine dictionary (Book 7b, Corollary 2.4), applied in each degree, identifies $\mathcal A|_U$ with the sheaf associated to a graded $R$-algebra $A(U)$. The schemes $\operatorname{Proj}A(U)$ agree on overlaps, since restriction to $D(h)\subset U$ is degreewise localization at $h\in R=A_0$. They glue to

$$
\pi:\operatorname{Proj}_S\mathcal A\longrightarrow S.
$$

The construction is local on $S$, but not merely fiberwise: it retains the way the fibers are attached. If $\mathcal A$ is generated by finitely many positive-degree sections over $\mathcal O_S$, then $\pi$ is of finite type. If it is generated in degree one by a finite-type module, Proj is locally a closed subscheme of a finite projective space.

A graded ideal sheaf $\mathcal I\subseteq\mathcal A$ gives a closed immersion

$$
\operatorname{Proj}_S(\mathcal A/\mathcal I)
\hookrightarrow \operatorname{Proj}_S\mathcal A.
$$

Different ideals can define the same closed subscheme. The reason is saturation: components supported at the irrelevant ideal never meet Proj. Explicitly, the saturation consists locally of homogeneous $a$ for which $A_+^N a\subset I$ for some $N$. Passing from $I$ to its saturation leaves Proj unchanged.

### 1.4 Standard opens and base change

Suppose $U=\operatorname{Spec}R\subseteq S$ and $f\in\mathcal A_d(U)$ with $d>0$. Then

$$
D_+(f)=\operatorname{Spec}(A(U)_f)_0.
$$

Thus relative Proj has an explicit affine cover. This is the decisive local calculation behind almost every compatibility theorem.

Let $g:T\to S$. Degreewise pullback gives a graded algebra $g^*\mathcal A$, with multiplication understood after tensoring. There is a canonical isomorphism

$$
\operatorname{Proj}_T(g^*\mathcal A)
\simeq \operatorname{Proj}_S(\mathcal A)\times_S T.
$$

To prove it, reduce to rings $R\to R'$. On $D_+(f)$ both sides have coordinate ring

$$
(A_f)_0\otimes_R R'\simeq ((A\otimes_R R')_{f\otimes1})_0.
$$

The equality is checked on homogeneous fractions and the chart isomorphisms agree on intersections. Notice that no flatness is required. This unconditional base-change theorem is one reason relative Proj is the correct construction.

Fibers are the special case $T=\operatorname{Spec}\kappa(s)$:

$$
(\operatorname{Proj}_S\mathcal A)_s
\simeq\operatorname{Proj}_{\kappa(s)}(\mathcal A\otimes\kappa(s)).
$$

### 1.5 Twisting sheaves

For a graded $A$-module $M$, let $M(n)$ be the shifted module with $M(n)_q=M_{n+q}$. On $D_+(f)$ define

$$
\widetilde M(n)(D_+(f))=(M(n)_f)_0.
$$

These modules localize correctly, so on each chart $D_+(f)=\operatorname{Spec}(A_f)_0$ they define
the quasi-coherent sheaf associated with the $(A_f)_0$-module $(M(n)_f)_0$ (Book 7b,
Corollary 2.4), and these glue to a quasi-coherent sheaf on $\operatorname{Proj}A$, quasi-coherence
being testable on one affine open cover (Book 7b, Corollary 2.6). Taking $M=A$ gives $\mathcal O(n)$. Relative Proj has the same construction. For $A=A_0[x_0,\ldots,x_r]$ with the standard grading this is the construction of $\mathbf P^r_{A_0}$ and of its twisting sheaves given in Book 7b, Proposition 6.1 and Lemma 6.2; the charts, the gluing data, and the identification $\Gamma(U_I,\mathcal O(n))=(A_{x_I})_n$ are the same.

If $A$ is generated by $A_1$ over $A_0$, then $\mathcal O(1)$ is invertible. On $D_+(f)$ for $f\in A_1$, multiplication by $f$ trivializes it. Consequently

$$
\mathcal O(m)\otimes\mathcal O(n)\simeq\mathcal O(m+n),
\qquad \mathcal O(n)^\vee\simeq\mathcal O(-n).
$$

For a grading not generated in degree one, $\mathcal O(1)$ need not be invertible. If generators have degrees dividing $d$, then $\mathcal O(d)$ is invertible on the charts generated by degree-$d$ elements. Weighted projective space exhibits the distinction: its natural $\mathcal O(1)$ can fail to be locally free near quotient singularities. One must never infer invertibility from the notation alone.

There is a natural map from a graded module to twisted global sections,

$$
M\longrightarrow\bigoplus_{n\in\mathbf Z}
\Gamma(\operatorname{Proj}A,\widetilde M(n)).
$$

It need not be an isomorphism in small degrees; saturation again intervenes. If $A$ is a noetherian standard graded algebra and $M$ is finitely generated, the map is an isomorphism in all sufficiently high degrees. More general finite gradings reduce to this statement after passing to a suitable Veronese algebra.

### 1.6 Veronese algebras and presentations

For $d>0$, the $d$th Veronese algebra is

$$
A^{(d)}=\bigoplus_{n\geq0}A_{nd}.
$$

Homogeneous localization gives a canonical isomorphism

$$
\operatorname{Proj}A\simeq\operatorname{Proj}A^{(d)}.
$$

Under it, $\mathcal O_{A^{(d)}}(1)$ corresponds to $\mathcal O_A(d)$. If $A$ is finitely generated over $A_0$, then for sufficiently divisible $d$, $A^{(d)}$ is generated in degree one. The proof chooses finitely many homogeneous generators and takes $d$ divisible enough that every monomial of degree a multiple of $d$ can be grouped into blocks of degree $d$. This reduces general finite graded algebras to the degree-one case without changing Proj.

If $A$ is generated in degree one by $r+1$ elements, there is a graded surjection

$$
A_0[x_0,\ldots,x_r]\twoheadrightarrow A.
$$

Relative Proj turns it into a closed immersion into $\mathbf P^r_{A_0}$. Thus a finite graded presentation is precisely a system of homogeneous equations in projective space.

## 2. Projective space and its universal meaning

### 2.1 Projective bundles

Let $\mathcal E$ be a quasi-coherent $\mathcal O_S$-module. We use the quotient convention

$$
\mathbf P_S(\mathcal E)=
\operatorname{Proj}_S(\operatorname{Sym}\mathcal E).
$$

When $\mathcal E$ is locally free of rank $r+1$, this is a projective-space bundle with fiber $\mathbf P^r$. There is a canonical surjection

$$
\pi^*\mathcal E\twoheadrightarrow\mathcal O_{\mathbf P(\mathcal E)}(1).
$$

The convention matters. Some accounts use lines in $\mathcal E$ and write the symmetric algebra of $\mathcal E^\vee$. Here points are rank-one quotients of $\mathcal E$, so formulas should be read accordingly.

For $\mathcal E=\mathcal O_S^{r+1}$ we write $\mathbf P^r_S$. It is covered by $r+1$ standard affine spaces. On the $i$th chart the image of the $i$th basis vector generates the universal invertible quotient, and the transition functions divide the other coordinates by that generator, exactly as over a field.

### 2.2 Invertible quotients

The universal property turns coordinates into geometry.

**Projective-bundle theorem.** Let $\mathcal E$ be quasi-coherent on $S$. For every $T\to S$, morphisms $u:T\to\mathbf P_S(\mathcal E)$ correspond naturally to equivalence classes of pairs

$$
(\mathcal L,q),\qquad
q:\mathcal E_T\twoheadrightarrow\mathcal L,
$$

where $\mathcal L$ is invertible and two pairs are equivalent if an isomorphism of their line bundles carries one quotient to the other. Under the correspondence, $\mathcal L=u^*\mathcal O(1)$ and $q$ is the pullback of the universal quotient.

The proof is local on $T$. Where one image $q(e_i)$ generates $\mathcal L$, trivialize $\mathcal L$ by it; the ratios $q(e_j)/q(e_i)$ define a map to the $i$th standard chart. A change of trivialization multiplies all coordinates by one unit and changes no ratios. Conversely, the standard charts carry compatible quotients. The constructions are inverse and commute with base change.

If $\mathcal E$ is finite locally free, the functor is represented by a scheme projective and finitely presented over $S$. For an arbitrary infinite module the same universal property remains meaningful, but the resulting projective bundle need not be of finite type.

### 2.3 Sections without common zeros

Let $f:X\to S$, let $\mathcal L$ be invertible on $X$, and choose sections $s_0,\ldots,s_r\in\Gamma(X,\mathcal L)$ which generate every stalk. Equivalently, the evaluation map

$$
\mathcal O_X^{r+1}\longrightarrow\mathcal L,
\qquad (a_i)\longmapsto\sum a_is_i
$$

is surjective. The projective-bundle theorem gives a unique $S$-morphism

$$
\varphi_s:X\longrightarrow\mathbf P^r_S
$$

such that $\varphi_s^*\mathcal O(1)\simeq\mathcal L$ and the coordinate sections pull back to the $s_i$.

The phrase “without common zeros” means stalkwise generation, not merely that no ordinary closed point is a common zero. Over a non-Jacobson scheme, closed points need not detect every stalk. Scheme-theoretic generation is the correct condition and is stable under every base change.

On the open $X_{s_i}$ where $s_i$ generates $\mathcal L$, the map is affine-coordinate-wise

$$
x\longmapsto
(s_0/s_i,\ldots,\widehat{s_i/s_i},\ldots,s_r/s_i).
$$

This formula will test whether $\varphi_s$ is an immersion: the ratios must generate the relevant coordinate algebras.

### 2.4 Closed subschemes from homogeneous ideals

Let $S=\operatorname{Spec}R$ and $I\subset R[x_0,\ldots,x_r]$ be a homogeneous ideal. The closed subscheme $V_+(I)$ is $\operatorname{Proj}(R[x_0,\ldots,x_r]/I)$. Its $T$-points are not simply tuples satisfying the equations: they are invertible quotients

$$
\mathcal O_T^{r+1}\twoheadrightarrow\mathcal L
$$

for which each homogeneous $F\in I_d$ evaluates to zero as a section of $\mathcal L^d$. This formulation works over rings with nilpotents and glues without choosing coordinates.

As an example, for $d\geq1$ the degree-$d$ Veronese map arises from all monomials of degree $d$:

$$
\nu_d:\mathbf P^r_S\longrightarrow
\mathbf P^{\binom{r+d}{d}-1}_S.
$$

On each standard chart its coordinate ring map contains the original affine coordinates among ratios of monomials, so it is a closed immersion. Its pullback of $\mathcal O(1)$ is $\mathcal O(d)$. The homogeneous quadratic relations among monomials describe its image.

## 3. Projective and quasi-projective morphisms

### 3.1 Definitions that survive change of base

A morphism $f:X\to S$ is **projective** if there are a finite locally free $\mathcal E$ on $S$ and a closed immersion

$$
X\hookrightarrow\mathbf P_S(\mathcal E)
$$

over $S$. It is **quasi-projective** if the immersion is locally closed. After trivializing
$\mathcal E$, this is an immersion into some $\mathbf P^r$ over each open of the base; the global
finite locally free $\mathcal E$ retains the gluing data.

Projectivity may also be considered locally on the base, but local embeddings do not by themselves
come with compatible hyperplane bundles. Here “projective” always includes the displayed global
finite-rank projective bundle. Whenever local projective embeddings are globalized below, the
compatible relatively ample line bundle that performs the globalization is stated explicitly.

A closed immersion is projective, and an open immersion into a projective $S$-scheme is quasi-projective but usually not projective. Affine space is quasi-projective via

$$
\mathbf A^r_S=D_+(x_0)\subset\mathbf P^r_S.
$$

### 3.2 Elementary permanence properties

Projective and quasi-projective morphisms are stable under arbitrary base change because projective bundles, closed immersions, and locally closed immersions are. Products are handled by the Segre immersion

$$
\mathbf P_S(\mathcal E)\times_S\mathbf P_S(\mathcal F)
\hookrightarrow\mathbf P_S(\mathcal E\otimes\mathcal F),
$$

whose universal quotient is the tensor product of the two universal quotients. On coordinates, its entries are $x_iy_j$; the $2\times2$ minors express rank one and cut out the image.

Under the finite-presentation and local noetherian hypotheses used for the parameter spaces in this
book, composites of projective morphisms are projective. Indeed, after embedding $X$ into a
projective bundle over $Y$ and $Y$ into one over $S$, twist the finitely presented coefficient
sheaf of the first embedding by a sufficiently high pullback of $\mathcal O_Y(1)$. Locally on
$S$, Serre generation extends a finite set of generators from $Y$ to its ambient projective
space. The local constructions are induced by the same tensor product of the two hyperplane
bundles, so they glue; a Segre-Veronese embedding then puts the result in one projective bundle
over $S$. The same argument with locally closed immersions proves the quasi-projective version.

This proof is sometimes hidden behind a permanence slogan. The twisting step is decisive: coefficients varying on $Y$ do not automatically become homogeneous coordinates over $S$.

### 3.3 Separatedness, finite type, and properness

If $\mathcal E$ has finite rank, $\mathbf P_S(\mathcal E)\to S$ is finitely presented, separated, and proper. Finite presentation and separatedness follow from its finite affine cover and the closed diagonal. Properness can be proved by the valuative criterion. Given a valuation ring $V$ with fraction field $K$, a $K$-point is a one-dimensional quotient of $K\otimes_VE$. Multiply a representing vector of coefficients by a scalar so that all coefficients lie in $V$ and at least one is a unit. The normalized tuple gives a unique $V$-point. Uniqueness follows because two primitive tuples differing by a $K$-scalar differ by a $V$-unit.

A closed subscheme of a proper scheme is proper. Hence a projective morphism is proper, separated, and of finite type. It is finitely presented when the defining closed immersion is finitely presented, as happens over a locally noetherian base. A quasi-projective morphism is separated and locally of finite type; if it is also quasi-compact, it is of finite type, and it is finitely presented under the analogous finite-presentation hypotheses. It need not be proper because points may escape through the omitted boundary.

The converse “proper implies projective” is false in general. It is true for many curves and for abelian schemes, but its proof requires special geometry. Projectivity is properness together with enough homogeneous functions to embed the object.

### 3.4 What projectivity does not mean

Projective is relative. The affine line over a field is not proper over that field, yet $\mathbf A^1_S\to S$ may occur as an open part of a projective family. A scheme projective over $S$ need not be projective over a smaller base unless $S$ is itself projective there.

Nor does every fiberwise projective morphism become projective. Fiberwise embeddings can require ranks and degrees that vary without a uniform bound, and their line bundles may fail to glue. Under finite presentation over a noetherian quasi-compact base, a single relatively ample line bundle supplies the needed uniformity; without it, fiberwise information is too weak.

Finally, a proper morphism may possess a line bundle whose restriction to every fiber is ample while the bundle is not relatively ample if the needed finite-presentation and uniformity conditions are abandoned. Relative positivity is a uniform statement near points of the base, not a collection of unrelated fiberwise statements.

## 4. Very ample and ample invertible sheaves

### 4.1 The evaluation map and global generation

Let $f:X\to S$ and $\mathcal L$ be invertible. It is **generated by relative global sections** if the adjunction evaluation

$$
f^*f_*\mathcal L\longrightarrow\mathcal L
$$

is surjective. Over an affine open $U\subseteq S$, this says that sections on $X_U$ generate every stalk. If $X\to S$ is quasi-compact, finitely many sections suffice locally on $S$.

Generation gives a morphism to projective space, but not necessarily an embedding. On $\mathbf P^1_k$, $\mathcal O$ is generated by $1$ and gives the constant map. On the other hand, $\mathcal O(1)$ gives the identity embedding after choosing a basis of its sections.

For a coherent sheaf $\mathcal F$, saying $\mathcal F\otimes\mathcal L^n$ is relatively generated means the same evaluation map is surjective. The power of ampleness is that this eventually holds for every coherent $\mathcal F$, not only for $\mathcal O_X$.

### 4.2 Very ampleness as separation

The line bundle $\mathcal L$ is **very ample relative to $S$** if there are a finite locally free $\mathcal E$ and an immersion

$$
i:X\hookrightarrow\mathbf P_S(\mathcal E)
$$

such that $\mathcal L\simeq i^*\mathcal O(1)$. If $f$ is proper, the immersion is automatically closed: a proper immersion is closed. Thus on proper families relative very ampleness gives a projective embedding.

Over a field, finite-dimensional sections $V\subseteq H^0(X,\mathcal L)$ define an immersion precisely when they separate geometric points and tangent directions. Scheme-theoretically, this means that after every field extension $K/k$, for every length-two closed subscheme $Z\subseteq X_K$, the restriction

$$
V\otimes_kK\longrightarrow H^0(Z,\mathcal L_K|_Z)
$$

is surjective. Two distinct reduced points test separation of points; a doubled point tests tangent directions. This formulation also catches nilpotents, which a set-theoretic injectivity test misses.

**Immersion criterion.** Suppose $X$ is of finite type over a field and $V$ generates $\mathcal L$. The associated map $X\to\mathbf P(V)$ is a locally closed immersion if the restriction map above is onto after every field extension for every length-two subscheme. If $X$ is proper, it is a closed immersion.

To see the mechanism, work where $s_0\in V$ trivializes $\mathcal L$. Separation of tangent vectors says the ratios $s_i/s_0$ generate cotangent spaces; separation of points makes the resulting map radicial. The cotangent criterion makes it unramified, and the affine-coordinate maps identify local rings. Finite type then gives an immersion. Properness closes the image.

### 4.3 The affine-open definition of ampleness

Very ampleness depends on one embedding. Ampleness records the ability of high tensor powers to create embeddings. An invertible sheaf $\mathcal L$ on $X$ is **ample relative to $S$** if $S$ has an affine open cover $U$ such that $X_U$ is covered by opens

$$
X_s=\{x:s_x\text{ generates }\mathcal L_x^n\},
$$

where $n>0$, $s\in\Gamma(X_U,\mathcal L^n)$, and every $X_s$ is affine.

Allowing $n$ to depend on $s$ makes the definition local and robust. If $X\to S$ is quasi-compact and of finite type, one may choose finitely many $s$ and replace their powers by a common multiple. The resulting sections define a quasi-projective immersion. Conversely, the standard opens of projective space are affine, so a very ample bundle is ample.

The trivial bundle on an affine morphism is ample: the section $1$ has affine nonvanishing locus all of $X$. Thus ampleness is relative and does not mean numerical positivity on an absolute variety. On a proper positive-dimensional variety over a field, the trivial bundle is not ample because the only nonvanishing locus of a constant section is the nonaffine whole variety.

### 4.4 Serre's criteria

The geometric definition has two indispensable algebraic forms.

**Serre generation criterion.** Let $f:X\to S$ be quasi-compact and separated, with $S$ affine, and let $\mathcal L$ be invertible. The following are equivalent.

1. $\mathcal L$ is $f$-ample.
2. For every finite-type quasi-coherent $\mathcal F$, there is $n_0$ such that $\mathcal F\otimes\mathcal L^n$ is generated by global sections for all $n\geq n_0$.
3. The same assertion holds for every coherent ideal sheaf when $X$ is noetherian.

For $(1)\Rightarrow(2)$, choose finitely many affine opens $X_{s_i}$. On each, finitely many local generators of $\mathcal F$ have denominators which become powers of $s_i$; multiplying clears the denominators and extends them to global twisted sections. A common power works on the finite cover. For $(3)\Rightarrow(1)$, apply generation to ideal sheaves cutting out complements of chosen affine neighborhoods. A section equal to a suitable power of a local generator has a nonvanishing locus contained in that neighborhood; an affine communication lemma shows these loci are affine and cover.

**Serre vanishing criterion.** If $f$ is projective over a noetherian affine scheme and $\mathcal L$ is ample, then for every coherent $\mathcal F$,

$$
H^i(X,\mathcal F\otimes\mathcal L^n)=0
\quad(i>0, n\gg0).
$$

Conversely, under the same projective morphism over a noetherian affine base, if this vanishing
and eventual generation hold for all coherent ideals, then $\mathcal L$ is ample. For the forward
implication, replace $\mathcal L$ by a very ample power and separate the finitely many residue
classes of twists. After a projective embedding, a coherent sheaf has a finite surjection from a
sum of $\mathcal O(-a)$; its coherent kernel has another such surjection. The relevant cohomology
is computed by the alternating Čech complex of the standard cover of $\mathbf P^r_A$ by its $r+1$
charts, which is legitimate because that cover is a finite affine open cover of a separated scheme
(Book 7b, Proposition 6.1 and Theorem 4.2); in particular $H^i$ vanishes for $i\geq r+1$
(Book 7b, Corollary 4.8(1)), so only the $r+1$ degrees $0\leq i\leq r$ occur. Each short exact
sequence of coherent sheaves gives a long exact cohomology sequence (Book 7b, Corollary 4.4), and
the terms involving $\mathcal O(n)$ are evaluated by the Laurent-monomial calculation
$H^i(\mathbf P^r_A,\mathcal O(n))=0$ for $i>0$ and $n\geq0$ (Book 7b, Theorem 6.5(2)–(4), the
hypothesis $n\geq0$ making part (3) vanish as well). Descending through this finite list
of kernels proves vanishing, and the first surjection proves eventual generation. Thus the
criterion is proved here; Section 6 only records the calculation in greater detail.

### 4.5 Tensor powers and operations

If $\mathcal L$ is ample, every positive power $\mathcal L^d$ is ample: replace each defining section by a power. Conversely, if $\mathcal L^d$ is ample for one $d>0$, then $\mathcal L$ is ample because sufficiently large powers in each residue class modulo $d$ are obtained by tensoring with one of finitely many fixed powers.

If $S$ is quasi-compact, $f:X\to S$ is quasi-compact and separated, $\mathcal L$ is $f$-ample, and $\mathcal M$ is invertible, then $\mathcal L^n\otimes\mathcal M$ is $f$-ample for all sufficiently large $n$. Apply the generation criterion on a finite affine cover of $S$ to the finitely many twists needed to generate $\mathcal M$ and its inverse. In particular, in this quasi-compact relative context ampleness is insensitive to a bounded twist at high degree.

If $S$ is quasi-compact and $X\to S$ is of finite type and quasi-compact, all sufficiently large
powers of an ample $\mathcal L$ are relatively very ample. If $X\to S$ is proper, each such power
gives a closed immersion, hence $X\to S$ is projective. The proof chooses finitely many affine
nonvanishing charts, then enough sections to generate their coordinate algebras and to distinguish
overlaps. Clearing their finitely many denominator bounds packages the functions as ratios of
homogeneous sections. Tensoring with the finitely many remaining powers of $\mathcal L$ and
clearing those bounds as well shows that every exponent beyond one bound works, not merely the
multiples of one exponent. This is the fundamental passage from local affine control to one global
embedding. Without quasi-compactness of the base, the assertion remains local on $S$ and there
need not be one exponent valid everywhere.

If $\mathcal L$ and $\mathcal M$ are ample relative to $S$, then $\mathcal L\otimes\mathcal M$ is ample. One can either refine their affine nonvanishing covers and tensor the corresponding sections, or use eventual generation. Pullback along a finite morphism preserves ampleness; along an arbitrary morphism it need not, as the pullback to a positive-dimensional fiber of a constant map may become trivial.

## 5. Base change and descent

### 5.1 Pullback of positivity

Let $g:T\to S$. If $\mathcal L$ is very ample for $X\to S$, then $\mathcal L_T$ is very ample for $X_T\to T$: base change the chosen immersion. If $\mathcal L$ is ample, then $\mathcal L_T$ is ample. For the latter statement, an affine nonvanishing open over an affine base open remains affine after pullback to an affine open of $T$, and the pulled-back sections cover.

These claims require no flatness. They should be distinguished from cohomological base change, where flatness or vanishing hypotheses matter. Positivity is visible on explicit affine charts and therefore survives arbitrary scalar extension.

Projectivity and quasi-projectivity likewise survive arbitrary base change. Consequently every fiber of a projective family is projective and every restriction of a relatively ample bundle is ample. The converses are subtler because fiberwise data need not be uniform.

### 5.2 Faithfully flat descent of very ampleness

The useful converse requires an actual faithfully flat cover of the base.

**Descent theorem.** Let $f:X\to S$ be of finite presentation and quasi-separated, let $\mathcal L$ be invertible, and let $g:S'\to S$ be faithfully flat and quasi-compact. If $\mathcal L_{S'}$ is very ample relative to $S'$, then $\mathcal L$ is very ample relative to $S$. If $f$ is proper, the descended immersion is closed.

Here the line bundle already lives on $X$; only its property is being tested. This is not a claim that an arbitrary line bundle on $X_{S'}$ descends without descent data.

The proof is local on $S$, so take $S=\operatorname{Spec}A$. Quasi-compactness lets us replace
$S'$ by a finite disjoint union of affine opens $\operatorname{Spec}A'$ which is still faithfully
flat over $S$. Flat base change for degree-zero sections on a quasi-compact quasi-separated scheme gives

$$
\Gamma(X,\mathcal L^n)\otimes_A A'
\simeq\Gamma(X_{S'},\mathcal L_{S'}^n).
$$

A finite family of sections on $X_{S'}$ supplies affine standard opens and generates their coordinate algebras by ratios. Each section and each finite relation involves only finitely many coefficients. Faithfully flat descent converts the relevant finite submodules and surjections to data over $A$ after enlarging the family if necessary. Surjectivity descends because a cokernel vanishing after faithful tensor product was already zero. The property that the associated morphism is an immersion also descends: its diagonal condition and its affine chart ring maps can be checked faithfully flatly. The descended finite linear system therefore realizes $\mathcal L$ as the pullback of $\mathcal O(1)$.

Finite presentation is used twice: it reduces the immersion test to finitely many chart generators
and relations, and it makes those data descend from a finite stage. For proper $f$, the resulting
immersion is proper and hence closed. Dropping finite presentation can destroy this finite-stage
argument, so no unrestricted descent assertion for very ampleness is being made here.

### 5.3 Descent of ampleness and projectivity

Under the same quasi-compact and quasi-separated hypotheses, relative ampleness is fpqc-local on the base:

$$
\mathcal L\text{ is }f\text{-ample}
\quad\Longleftrightarrow\quad
\mathcal L_{S'}\text{ is }f_{S'}\text{-ample}.
$$

Only the reverse implication needs proof. Quasi-compactness gives a common power of $\mathcal L_{S'}$ that is very ample on finitely many pieces. Descent of the affine nonvanishing cover, or equivalently the generation criterion plus faithful descent of surjectivity, proves ampleness below.

Projectivity descent cannot be proved merely by choosing an embedding line bundle after a
faithfully flat base change: an arbitrarily chosen bundle upstairs need not carry descent data.
The form needed in this curriculum retains the polarization and is therefore the following safe
statement.

**Projectivity descent with a polarization.** Let $S$ be quasi-compact, let $f:X\to S$ be proper and of finite presentation, and let $\mathcal L$ be a line bundle on $X$. If some fpqc base change makes $\mathcal L$ relatively ample, then $\mathcal L$ is relatively ample and $f$ is projective.

This polarized form records the datum used in moduli problems and avoids concealing an obstruction
in the Picard group.

### 5.4 Necessary hypotheses and failures

Faithfulness cannot be dropped. Restricting to an open subset of $S$ may erase a bad fiber, so positivity over that open says nothing at omitted points. Flatness cannot be replaced by a merely surjective map: nilpotent thickenings can make module surjections and immersion conditions invisible.

Quasi-compactness provides finite linear systems. An infinite disjoint union may be fiberwise embeddable with unbounded projective dimension but admit no one finite-rank ambient bundle. Quasi-separatedness is what makes sections commute with flat base change in the form used above.

Finally, “very ample after taking a power” descends to ampleness, but it need not show that the original bundle is very ample if only the power is known upstairs. For example, on an elliptic curve a line bundle of degree $2$ is not very ample, whereas its square has degree $4$ and is very ample. Tensor roots do not inherit separation automatically.

## 6. Serre vanishing and projective cohomology

### 6.1 The projective-space calculation

Hilbert polynomials arise from an asymmetry: positive twists acquire many sections while their higher cohomology eventually disappears. We begin where the calculation is visible.

The calculation itself was carried out in the previous volume and we recall it in the exact form
in which it will be used. Cover $\mathbf P^r_A$ by the charts $U_i=D_+(x_i)$; every nonempty finite
intersection $U_I$ is affine and $\mathbf P^r_A$ is separated (Book 7b, Proposition 6.1), so the
alternating Čech complex of this cover, of length $r$, computes the cohomology of every
quasi-coherent sheaf (Book 7b, Theorem 4.2). For $\mathcal O(n)$ its terms are the degree-$n$ parts
$(A[x_0,\ldots,x_r]_{x_I})_n$ of localizations of the polynomial ring (Book 7b, Lemma 6.2(2)).
Sorting Laurent monomials by the set of variables carrying a negative exponent and contracting the
resulting simplicial complexes is the proof of Book 7b, Theorem 6.5, whose statement reads

$$
H^i(\mathbf P^r_A,\mathcal O(n))=0
\quad\text{for }0<i<r
$$

and, in particular,

$$
H^i(\mathbf P^r_A,\mathcal O(n))=0
\quad(i>0,\ n\geq0).
$$

Moreover

$$
H^0(\mathbf P^r_A,\mathcal O(n))
\simeq A[x_0,\ldots,x_r]_n
$$

for $n\geq0$, a free $A$-module of rank $\binom{n+r}{r}$, and zero for $n<0$. If $r\geq1$, then for $n\leq-r-1$ the top cohomology
$H^r(\mathbf P^r_A,\mathcal O(n))$ is the free $A$-module with basis the Laurent monomials
$x_0^{a_0}\cdots x_r^{a_r}$ for which every $a_i<0$ and $\sum_i a_i=n$, of rank
$\binom{-n-1}{r}$; it is zero for
$n\geq-r$. Finally $H^i=0$ for $i>r$, the cover having $r+1$ members (Book 7b,
Corollary 4.8(1)). All four assertions are Book 7b, Theorem 6.5, parts (1)–(4); for $r=0$ one has
$\mathbf P^0_A=\operatorname{Spec}A$, $H^0(\mathcal O(n))=A\cdot x_0^n$ and no higher cohomology.

Three further features of that computation are used constantly below and are recorded in Book 7b,
Corollary 6.6. Every $H^i(\mathbf P^r_A,\mathcal O(n))$ is a _free_ $A$-module of finite rank with
an explicit monomial basis; the formation of these modules commutes with every ring map $A\to B$,

$$
H^i\bigl(\mathbf P^r_A,\mathcal O(n)\bigr)\otimes_AB
\xrightarrow{\ \sim\ }H^i\bigl(\mathbf P^r_B,\mathcal O(n)\bigr),
$$

with no hypothesis whatever on $B$, because the Čech complex is defined over $\mathbf Z$ and the
contracting homotopies have coefficients $0,\pm1$; and over a field,

$$
\chi(\mathbf P^r_k,\mathcal O(n))=\binom{n+r}{r}
$$

for every integer $n$, the binomial expression being read as the polynomial
$(n+r)(n+r-1)\cdots(n+1)/r!$. The last identity is the seed of every Hilbert polynomial in this
book, and the base-change statement is what allows the same complex to be used over residue
fields, over rings with nilpotents, and over nonnoetherian rings alike. Book 7b, Theorem 6.7
supplies in addition the perfect pairing
$H^0(\mathcal O(n))\times H^r(\mathcal O(-n-r-1))\to A$; it is not used below, but it explains why
cohomology is concentrated in the two extreme degrees and why the two answers are indexed by
complementary sets of monomials.

### 6.2 Vanishing and generation in high degree

**Serre vanishing theorem.** Let $A$ be noetherian and let $\mathcal F$ be coherent on $\mathbf P^r_A$. There is $n_0$ such that

$$
H^i(\mathbf P^r_A,\mathcal F(n))=0
\quad(i>0,\ n\geq n_0),
$$

and $\mathcal F(n)$ is generated by finitely many global sections for $n\geq n_0$.

The proof is given here, and all of its inputs are the recalled facts of Section 6.1. The strategy
is to replace $\mathcal F$ by finitely many twists of $\mathcal O$. Choose a surjection
$\bigoplus_j\mathcal O(-a_j)\twoheadrightarrow\mathcal F$, possible because $\mathcal F$ is
coherent and $\mathcal O(1)$ is ample; its kernel $\mathcal K$ is coherent because $A$ is
noetherian. The associated short exact sequence gives a long exact cohomology sequence (Book 7b,
Corollary 4.4, applicable since all three sheaves are quasi-coherent on the quasi-compact
separated scheme $\mathbf P^r_A$), and a segment of it reads

$$
H^i\Bigl(\bigoplus_j\mathcal O(n-a_j)\Bigr)\longrightarrow H^i(\mathcal F(n))
\longrightarrow H^{i+1}(\mathcal K(n)).
$$

The left term vanishes for $i>0$ as soon as $n\geq\max_ja_j$, by Book 7b, Theorem 6.5 (cohomology
commutes with the finite direct sum because the Čech complex does). So vanishing for $\mathcal F$
in degree $i$ is reduced to vanishing for the kernel one degree higher. The descending induction
starts at $i=r$ and terminates there because $H^{r+1}$ of any quasi-coherent sheaf on
$\mathbf P^r_A$ vanishes, the standard cover having $r+1$ members (Book 7b, Corollary 4.8(1)).
Taking the maximum of the finitely many bounds produced along the way gives one $n_0$. The same
surjection, twisted far enough that $H^1(\mathcal K(n))=0$, makes
$H^0(\bigoplus_j\mathcal O(n-a_j))\to H^0(\mathcal F(n))$ surjective, and the source generates
$\bigoplus_j\mathcal O(n-a_j)$ for $n\geq\max_ja_j$; hence $\mathcal F(n)$ is globally generated by
finitely many sections.

If $i:X\hookrightarrow\mathbf P^r_A$ is closed and $\mathcal G$ coherent on $X$, then $i_*\mathcal G$ is coherent, cohomology is unchanged because a closed immersion is affine and affine morphisms are cohomologically invisible (Book 7b, Corollary 3.11; quasi-coherence of $i_*\mathcal G$ is Book 7b, Theorem 2.10), and $i_*\mathcal G(n)=i_*(\mathcal G\otimes i^*\mathcal O(n))$ by the projection formula (Book 7a, Section 4.4), which for an invertible twisting sheaf is immediate on a trivializing open. Hence the theorem holds on every projective noetherian $A$-scheme. For an ample $\mathcal L$, replace it by a very ample power $\mathcal L^d$ and treat the finitely many residue classes of exponents modulo $d$.

### 6.3 Relative finiteness

Let $f:X\to S$ be projective with $S$ locally noetherian, and let $\mathcal F$ be coherent. The
question is local on $S$, so let $U=\operatorname{Spec}A$ be affine with $A$ noetherian and embed
$X_U$ as a closed subscheme of some $\mathbf P^r_A$. Pushing $\mathcal F$ forward along that closed
immersion changes no cohomology (Book 7b, Corollary 3.11) and produces a coherent sheaf
(Book 7b, Theorem 2.10, together with finiteness of the module over the quotient ring), so we may
assume $X_U=\mathbf P^r_A$. Since $\mathbf P^r_A$ is separated and covered by
the $r+1$ standard charts, $H^i(X_U,\mathcal F)$ is the $i$th cohomology of the alternating Čech
complex of that cover (Book 7b, Theorem 4.2), a complex of $A$-modules of length $r$; in
particular it vanishes for $i>r$ (Book 7b, Corollary 4.8(1)). Finiteness of each $H^i(X_U,\mathcal
F)$ over $A$ follows by the same descending induction as in Section 6.2: resolve $\mathcal F$ by
sums of twists, use the long exact sequence (Book 7b, Corollary 4.4), and use that the modules
$H^i(\mathbf P^r_A,\mathcal O(n))$ are finite free (Book 7b, Theorem 6.5), the induction being
finite because it starts at $i=r$. Finally $R^if_*\mathcal F$ is quasi-coherent with
$R^if_*\mathcal F|_U=\widetilde{H^i(X_U,\mathcal F)}$ (Book 7b, Theorem 4.7), hence coherent.

If $\mathcal L$ is an $f$-ample line bundle, then for $n\gg0$,

$$
R^if_*(\mathcal F\otimes\mathcal L^n)=0\quad(i>0).
$$

Indeed, over an affine open of $S$ the sheaf $R^if_*$ is the tilde of $H^i(X_U,\mathcal
F\otimes\mathcal L^n)$ (Book 7b, Theorem 4.7), which vanishes for $n\gg0$ by the Serre vanishing
theorem of Section 6.2.

If $\mathcal F$ is flat over $S$, then after increasing $n$ locally on $S$, $f_*(\mathcal F(n))$ is locally free and commutes with arbitrary base change. Vanishing turns degree-zero cohomology into a kernel in a finite complex; flatness and fiberwise vanishing make kernel and image commute with tensor product. Thus

$$
f_*(\mathcal F(n))\otimes\kappa(s)
\simeq H^0(X_s,\mathcal F_s(n)).
$$

We record exactly which finite complex is meant, since it will later be applied after a
nonnoetherian base change. Over any ring $A$, a finitely presented $A$-flat sheaf $\mathcal G$
on $\mathbf P^r_A$ admits, Zariski-locally on $\operatorname{Spec}A$, a finite cohomology
complex $K^\bullet(\mathcal G)$ of finite free $A$-modules such that

$$
H^i(K^\bullet(\mathcal G)\otimes_A B)
\simeq H^i(\mathbf P^r_B,\mathcal G_B) \tag{6.1}
$$

for every $A\to B$. Here is the finite replacement construction. Descend the finitely many
coefficients of a presentation of $\mathcal G$ to a noetherian subring $A_0$; finite-presentation
flatness descends after enlarging $A_0$ once. Let $C^\bullet$ be the alternating Čech complex of
the standard cover of $\mathbf P^r_{A_0}$ with coefficients in the descended sheaf $\mathcal G_0$;
it has $r+1$ terms and computes $H^\bullet(\mathbf P^r_{A_0},\mathcal G_0)$ (Book 7b,
Theorem 4.2). Its terms are flat $A_0$-modules, since each is a module of sections of $\mathcal
G_0$ over an affine chart and $\mathcal G_0$ is $A_0$-flat, so by Book 7b, Theorem 5.2 the complex
$C^\bullet\otimes_{A_0}B$ computes $H^\bullet(\mathbf P^r_B,\mathcal G_{0,B})$ for every
$A_0$-algebra $B$ — this is the precise sense in which it "computes cohomology after every scalar
extension", and it is where flatness of $\mathcal G$ is used. Its cohomology modules are finite by
the previous paragraph.

We use the following elementary perfect-complex lemma. Over a noetherian ring, a bounded complex
of flat modules with finite cohomology is, locally on the base, quasi-isomorphic to a bounded
complex of finite free modules. Indeed, choose finite free modules mapping onto the cohomology and
cycles successively from the right. This constructs a bounded-above finite-free resolution. The
original complex has a fixed finite flat amplitude, so after enough steps its last syzygy is flat:
vanishing of the next homology after tensoring with every module is exactly the local flatness
criterion. That syzygy is also finitely presented, hence locally projective, and the resolution
can be truncated there. Notice that this argument does **not** assert that the individual cycles
of the original Čech complex are flat; cohomology can jump even in a flat family.

Apply the lemma to $C^\bullet$ and call the resulting finite free complex
$K^\bullet(\mathcal G_0)$. Both complexes are bounded complexes of flat modules, hence are K-flat
and compute their own derived tensor products (Book 7a, Sections 3.3 and 3.8). Their quasi-isomorphism therefore remains a quasi-isomorphism
after every $A_0\to B$. Base-changing first to $A$ gives (6.1). Thus the noetherian subring is
only a construction device, and every matrix of $K^\bullet$ is fixed before the arbitrary scalar
extension $A\to B$.

The complex has no negative cohomology after any base change, so its negative part splits
successively from the left. If all residue-field cohomology above degree zero vanishes and the
fiber Euler characteristic is locally constant, elementary row and column operations split its
positive part successively from the right; the constant rank makes the last relevant minor a
unit. What remains in degree zero is finite projective, and the split complex remains split after
every tensor product. This proves both local freeness and arbitrary cohomological base change
without applying Nakayama to an infinite Čech localization.

The bound is globally uniform when $S$ is quasi-compact.

### 6.4 Regularity and uniform bounds

A coherent sheaf $\mathcal F$ on $\mathbf P^r_A$ is **$m$-regular** if

$$
H^i(\mathbf P^r_A,\mathcal F(m-i))=0
\quad\text{for every }i>0.
$$

The Castelnuovo--Mumford argument shows that $m$-regular implies $(m+1)$-regular, that $\mathcal F(m)$ is globally generated, and that

$$
H^0(\mathcal F(n))\otimes_AH^0(\mathcal O(1))
\twoheadrightarrow H^0(\mathcal F(n+1))
\quad(n\geq m).
$$

These implications are valid over the ring $A$ itself. Use the exact Koszul complex of the
surjection

$$
\mathcal O(-1)^{r+1}\xrightarrow{(x_0,\ldots,x_r)}\mathcal O
$$

and its exterior powers. After tensoring by $\mathcal F(n)$, the defining vanishings kill the
higher-cohomology terms in the associated finite hypercohomology diagram — the hypercohomology
spectral sequence of a bounded complex of quasi-coherent sheaves, available from Book 7a,
Section 7.3, its $E_1$ terms being the groups $H^j(\mathbf P^r_A,\mathcal F(n-i)\otimes\wedge^i)$
of the Koszul terms and its abutment vanishing because the Koszul complex is exact. Its edge maps
are exactly the evaluation map and the displayed multiplication map; shifting the same diagram by
one proves persistence of regularity. This argument is defined over $\mathbf Z$, so it needs no
choice of a hyperplane and works over finite residue fields and general base rings alike. Over an
infinite field it is equivalent to the familiar proof by choosing a hyperplane away from the
associated points and inducting on $r$. Regularity packages all high-degree behavior into one
integer. No uniform bound for varying ideals is used in this section.

## 7. Hilbert functions and Hilbert polynomials

### 7.1 From dimensions to a polynomial

Let $X$ be projective over a field $k$, $\mathcal L$ ample, and $\mathcal F$ coherent. Its Hilbert function is

$$
h_{\mathcal F}(n)=\dim_kH^0(X,\mathcal F\otimes\mathcal L^n).
$$

For large $n$, this equals the Euler characteristic

$$
\chi(X,\mathcal F\otimes\mathcal L^n)
=\sum_i(-1)^i\dim_kH^i(X,\mathcal F\otimes\mathcal L^n).
$$

**Hilbert polynomial theorem.** There is a unique $P_{\mathcal F,\mathcal L}(t)\in\mathbf Q[t]$ such that

$$
P_{\mathcal F,\mathcal L}(n)
=\chi(X,\mathcal F\otimes\mathcal L^n)
=h_{\mathcal F}(n)
$$

for all sufficiently large $n$. It is integer-valued on integers.

There is a small point hidden by the phrase “embed by a power”: polynomiality for the
subsequence $n=dm$ does not by itself rule out different polynomials in the residue classes
modulo $d$. We prove the stronger Euler-characteristic statement directly.

**Euler-characteristic polynomial lemma.** If $X$ is proper over $k$, $\mathcal M$ is invertible,
and $\mathcal F$ is coherent with support of dimension at most $d$, then

$$
n\longmapsto\chi(X,\mathcal F\otimes\mathcal M^n)
$$

is a numerical polynomial of degree at most $d$ for every $n\in\mathbf Z$.

Filter the Grothendieck group of coherent sheaves by the dimension of support. On a component of
maximal dimension, a rational trivialization of $\mathcal M$ is regular and invertible on some
dense open. It identifies $\mathcal F$ and $\mathcal F\otimes\mathcal M$ there. Inside their
common sheaf of rational sections, take a coherent subsheaf agreeing with both on that open.
The kernels and cokernels of its maps to the two sheaves are supported on a closed subset of
smaller dimension. Additivity in the Grothendieck group therefore shows that

$$
[\mathcal F\otimes\mathcal M]-[\mathcal F]
$$

lies one step lower in the support filtration. Repeating $d+1$ times makes the class zero. Since
Euler characteristic is additive in short exact sequences, the $(d+1)$st forward difference of
$\chi(\mathcal F\otimes\mathcal M^n)$ vanishes. An integer-valued function on $\mathbf Z$ with
vanishing $(d+1)$st difference is an integral linear combination of
$\binom n0,\ldots,\binom nd$, hence is a numerical polynomial of degree at most $d$.

Apply the lemma with $\mathcal M=\mathcal L$. The Serre vanishing theorem of Section 6.2 identifies its value with $h^0$ for
all large $n$, giving the asserted Hilbert polynomial without a residue-class gap. Uniqueness
follows because a polynomial vanishing at all large integers is zero. When $\mathcal L$ itself is
very ample, a finite graded resolution gives the familiar equivalent expression as an integral
linear combination of $\binom{t+r-a}{r}$.

### 7.2 The polynomial of a projective scheme

For $Z\subseteq\mathbf P^r_k$ closed, its Hilbert polynomial is that of $\mathcal O_Z$. The Hilbert polynomial of $\mathbf P^r_k$ itself is $\binom{n+r}{r}$ by Book 7b, Corollary 6.6(3). The ideal sequence gives

$$
P_Z(n)=\binom{n+r}{r}-P_{\mathcal I_Z}(n).
$$

If $Z$ is a hypersurface cut out by a nonzero homogeneous equation of degree $e>0$, then

$$
P_Z(n)=\binom{n+r}{r}-\binom{n+r-e}{r}.
$$

For a plane curve this is $en+1-(e-1)(e-2)/2$. No smoothness is involved.

Exact sequences give exact equalities of Hilbert polynomials. Nilpotents therefore count: a doubled point has polynomial $2$, although its reduced support has polynomial $1$. The polynomial measures scheme-theoretic size, not merely geometric points.

### 7.3 Degree, dimension, and examples

If $\operatorname{Supp}\mathcal F$ has dimension $d$ and $\mathcal F\neq0$, then $P_{\mathcal F}$ has degree $d$ and leading term

$$
\frac{\deg_{\mathcal L}(\mathcal F)}{d!}t^d
$$

for a positive integer $\deg_{\mathcal L}(\mathcal F)$. A hyperplane with defining section $\ell$ gives the exact sequence

$$
0\to(0:_{\mathcal F}\ell)(n-1)\to\mathcal F(n-1)
\xrightarrow{\ell}\mathcal F(n)\to\mathcal F|_H(n)\to0,
$$

and hence the finite-difference relation

$$
P_{\mathcal F}(n)-P_{\mathcal F}(n-1)
=P_{\mathcal F|_H}(n)-P_{(0:_{\mathcal F}\ell)}(n-1).
$$

After extending an arbitrary ground field if necessary, one may choose $\ell$ to avoid the associated points of the top-dimensional support; the kernel term is then supported in lower dimension. Hilbert polynomials and their leading terms are unchanged by field extension. Induction ends with the total length of a zero-dimensional sheaf, proving both assertions.

Thus a finite scheme of length $d$ has constant polynomial $d$. A projective curve has $P(n)=en+c$, with $e$ its degree in the chosen embedding. Projective space has polynomial $\binom{n+r}{r}$. For a union one computes by the exact sequence

$$
0\to\mathcal O_{Y\cup Z}\to\mathcal O_Y\oplus\mathcal O_Z
\to\mathcal O_{Y\cap Z}\to0.
$$

### 7.4 Dependence on the polarization

The polynomial belongs to $(\mathcal F,\mathcal L)$. For $q\geq1$, replacing $\mathcal L$ by $\mathcal L^q$ replaces $P(t)$ by $P(qt)$. Different ample bundles can produce different leading coefficients, or polarized degrees; the polynomial degree remains the support dimension. A moduli problem must therefore fix an embedding or polarization before specifying a Hilbert polynomial.

Dimension is independent of the polarization. For an integral projective curve $C$, the linear coefficient of $P_{\mathcal O_C,\mathcal L}$ is $\deg_C\mathcal L$; for a locally free sheaf of rank $r$ it is $r\deg_C\mathcal L$, and in general it is the corresponding one-dimensional multiplicity. For finite schemes the constant polynomial is total length and is independent of any polarization. This explains why length-$d$ Hilbert functors have an intrinsic meaning even when a projective embedding is used to construct them.

## 8. Hilbert polynomials in families

### 8.1 Fiberwise Euler characteristics

Let $f:X\to S$ be projective and finitely presented, with $S$ locally noetherian, choose an $f$-ample $\mathcal L$, and let $\mathcal F$ be coherent. For $s\in S$, set

$$
P_s(n)=\chi(X_s,\mathcal F_s\otimes\mathcal L_s^n).
$$

The polynomial can jump: specialization may create torsion, embedded components, or extra length. Flatness prevents these surprises. For $n\gg0$ locally on $S$, higher cohomology vanishes on nearby fibers and, when $\mathcal F$ is $S$-flat, $f_*\mathcal F(n)$ is locally free with fiber $H^0(X_s,\mathcal F_s(n))$.

### 8.2 Flatness forces constancy

**Constancy theorem.** Under the preceding hypotheses, if $\mathcal F$ is flat over $S$, then $s\mapsto P_s$ is locally constant.

Choose $d+1$ large consecutive integers, where $d$ bounds fiber dimensions. Each value $P_s(n)$ is the rank of a locally free pushforward and hence locally constant. These values determine a polynomial of degree at most $d$. Thus the entire polynomial is constant on connected components.

For a failure, over $S=\operatorname{Spec}k[t]$ let $Z\subset\mathbf A^1_S$ be cut out by $(tx,x^2)$. Away from $t=0$ the fiber is one reduced point; at $0$ it is doubled. Fiber length jumps from $1$ to $2$, reflecting nonflatness.

### 8.3 Flattening strata

We begin with the finite algebra which makes the theorem effective. If $M$ is a finitely
presented module over a ring $A$, the functor of maps $A\to B$ for which $M\otimes_A B$ is
locally free of rank $q$ is represented by

$$
V(\operatorname{Fitt}_{q-1}M)\setminus V(\operatorname{Fitt}_{q}M),
$$

with $\operatorname{Fitt}_{-1}M=0$. Choose a finite presentation
$A^a\xrightarrow{D}A^b\to M\to0$. The Fitting ideals are generated by minors of $D$ and
therefore commute with every scalar extension. Where a suitable
$(b-q)\times(b-q)$ minor is invertible, row and column operations split off an identity block.
Vanishing of the next minors makes the remaining block zero, leaving a free cokernel of rank
$q$; the converse is immediate from a presentation of a free module.

The projective step is the following finite-detection lemma. Its proof is deliberately phrased
in terms of graded pieces: a degree-zero localization is usually an infinite filtered colimit,
not a localization that becomes stationary after finitely many multiplication maps.

**Graded flatness lemma.** Let $A$ be noetherian, let
$W=A[x_0,\ldots,x_r]$, and let $M$ be a finite graded $W$-module. Fix a numerical
polynomial $P$ that is nonnegative in large degree. There are integers $N$ and $b\geq0$ such that, for every $A$-algebra $B$, the
following are equivalent:

1. $\widetilde{M\otimes_A B}$ is $B$-flat and all its geometric fibers have Hilbert
   polynomial $P$;
2. $M_n\otimes_A B$ is finite locally free of rank $P(n)$ for
   $N\leq n\leq N+b$.

The finite range can be chosen so that condition 2 forces the same assertion for every
$n\geq N$. When the conditions hold, for $n\geq N$ the natural map

$$
M_n\otimes_A B\longrightarrow
H^0(\mathbf P^r_B,\widetilde{M\otimes_A B}(n))
$$

is an isomorphism, higher cohomology vanishes, and these sections commute with every further
base change.

**Proof.** First choose one bound $N$ valid on every fiber of $\operatorname{Spec}A$. We give
the finite argument, since upper semicontinuity in one degree would not by itself give a bound
for the infinite tail. The following elementary relative-resolution lemma is the input.

**Finite fiber-resolution lemma.** If $A$ is noetherian and $M$ is a finite graded module over
$W=A[x_0,\ldots,x_r]$, then $\operatorname{Spec}A$ has a finite partition by locally closed
reduced subschemes $S_\alpha$ and, for each $\alpha$, a bounded complex

$$
F_{\alpha,r+1}\longrightarrow\cdots\longrightarrow F_{\alpha,0}
\longrightarrow M_{S_\alpha}\longrightarrow0, \tag{8.1a}
$$

where every $F_{\alpha,i}$ is a finite sum of graded shifts of $W_{S_\alpha}$ and (8.1a)
remains exact after passage to every residue field of $S_\alpha$.

To construct it, start at the generic point $\eta$ of an irreducible component of the reduced
base; replacing $A$ by the corresponding quotient, we may assume $A$ is a noetherian domain with
fraction field $\kappa(\eta)$. Hilbert's syzygy theorem over $\kappa(\eta)$ — Book 7b,
Theorem 7.4, applied to the finite graded $\kappa(\eta)[x_0,\ldots,x_r]$-module $M_\eta$ — gives a
graded free resolution

$$
0\longrightarrow F_{r+1}\longrightarrow\cdots\longrightarrow F_0
\longrightarrow M_\eta\longrightarrow0
$$

of length at most $r+1$ in which every $F_i$ is a finite direct sum of shifts. This is exactly the
shape demanded by (8.1a), so no reindexing is needed. Choose homogeneous bases and clear the
finitely many
denominators in all its matrices and in the augmentation to $M$. The resulting finite complex
over some dense open $\operatorname{Spec}A_g$ has homology finite over the polynomial ring and zero at $\eta$; one more
localization kills every homology module, so over some $\operatorname{Spec}A_{g'}$ we have an exact
complex

$$
0\longrightarrow G_{r+1}\longrightarrow\cdots\longrightarrow G_0
\longrightarrow M_{g'}\longrightarrow0
$$

of finite graded $A_{g'}[x_0,\ldots,x_r]$-modules whose terms are finite sums of shifts of the
polynomial ring. Now apply Book 7b, Corollary 7.8 to this exact complex over the noetherian
domain $A_{g'}$: there is a nonzero $f$ such that, after inverting it, $M$ and all the cycle
modules $Z_i=\ker(G_i\to G_{i-1})$ become free over the base, and the complex stays exact after
_every_ base change of the base ring, in particular after passage to every residue field. That
corollary is proved there from generic freeness (Book 7b, Theorem 7.6) applied successively to
$M,Z_0,\ldots,Z_r$, and its mechanism is exactly the one wanted here: the short exact sequences

$$
0\longrightarrow Z_i\longrightarrow G_i\longrightarrow Z_{i-1}\longrightarrow0,
\qquad Z_{-1}=M,
$$

have flat right-hand terms and therefore remain exact after every scalar extension. Remove this open and repeat on the reduced closed complement. Noetherian induction
terminates after finitely many steps, which proves the lemma. Notice that only the finitely many
matrices of (8.1a) and their finitely many cycle modules are being made flat; no infinite
collection of cohomology maps is hidden here. It is worth recording which hypotheses of Book 7b,
Corollary 7.8 are being met: the base ring is a noetherian domain after passing to an integral
component of a stratum, the complex is exact and consists of finite graded modules over a
polynomial ring, and the conclusion is universal exactness after base change — precisely the three
items used.

On a residue field $k$ of the stratum, sheafify (8.1a) and twist. The individual terms become
finite sums of $\mathcal O(n-a)$ on $\mathbf P^r_k$, whose cohomology is completely known
(Book 7b, Theorem 6.5): the higher cohomology of $\mathcal O(m)$ vanishes for $m\geq-r$ and its
global sections are the degree-$m$ monomials for $m\geq0$. Descending through the $r+1$ syzygies
by the long exact sequences of Book 7b, Corollary 4.4 supplies, from the largest
shift occurring in (8.1a), a bound $N_\alpha$ for higher-cohomology vanishing and for the
comparison

$$
(M\otimes_A k)_n\longrightarrow
H^0(\mathbf P^r_k,\widetilde{M\otimes_A k}(n)) \tag{8.1}
$$

over every residue field $k$ on that stratum. Take the maximum of the finitely many
$N_\alpha$. Enlarge it once more so that $P(n)\geq0$ for $n\geq N$. The complexes remain
exact after extending a residue field — this is Book 7b, Corollary 7.5, and also a special case of
the universal exactness supplied by Book 7b, Corollary 7.8 — and the shifts occurring in them do
not change, so the same bound works over every field receiving a map
from $A$. This establishes the required uniformity without using flattening stratification.

Suppose first that $\mathcal F_B=\widetilde{M\otimes_A B}$ is flat with polynomial $P$.
The fiberwise bound and the finite-Čech-complex cohomology-and-base-change argument of
Section 6.3 show that
$H^0(\mathcal F_B(n))$ is locally free of rank $P(n)$ for $n\geq N$ and commutes with base
change. That argument uses finite presentation and flatness, and therefore applies to the
possibly nonnoetherian ring $B$. The comparison map from $M_n\otimes_A B$ is an isomorphism on every residue fiber by
(8.1). Its cokernel is finite and hence zero by Nakayama. Locally the resulting surjection
onto a free module splits; its kernel has zero residue fibers and is therefore zero as well.
Thus $M_n\otimes_A B$ is locally free of rank $P(n)$ for every $n\geq N$.

Conversely, suppose those graded pieces are flat of the prescribed ranks for every $n\geq N$.
On the standard affine chart the sections of $\mathcal F_B$ are the degree-zero part of the
localized graded module, by the construction of Section 1.5 together with the affine dictionary
(Book 7b, Corollary 2.4):

$$
\Gamma(D_+(x_i),\mathcal F_B)
=(M\otimes_A B)_{x_i,0}
=\mathop{\operatorname{colim}}_{q}
   (M\otimes_A B)_q,
\qquad u\longmapsto x_i u. \tag{8.2}
$$

The tail with $q\geq N$ is cofinal. A filtered colimit of flat $B$-modules is flat, so
$\mathcal F_B$ is flat on every standard chart. On a residue fiber, (8.1) identifies the
eventual section dimensions with $P(n)$, proving that the fiber polynomial is $P$.

It remains to show that the infinitely many rank conditions just used are genuinely finite.
For a finite $A$-module $E$, the functor on which $E$ becomes locally free of rank $q$ is
the locally closed Fitting locus displayed above. Impose the conditions for
$n=N,\ldots,N+d$, where $d=r$ for $P=0$ and $d=\max(r,\deg P)$ otherwise. Since a fiber Hilbert polynomial has degree at
most $r$, these values select
the underlying locus on which the polynomial is $P$. On that noetherian locally closed locus,
for every $n>N+d$ the open half of the rank-$P(n)$ Fitting condition is already the whole
underlying space; the remaining condition is the vanishing of
$\operatorname{Fitt}_{P(n)-1}(M_n)$. The increasing sequence of ideals obtained by summing
these Fitting ideals stabilizes. Hence finitely many degrees, contained in
$[N,N+b]$ after enlarging $b$, impose all of them. This is equality of ideals, rather than
equality of their radicals, so it survives arbitrary scalar extension, including extension to
a ring with nilpotents. This proves finite detection and the asserted universal base-change
statements. $\square$

For a minimal nilpotent check, take $C=k[\epsilon]/(\epsilon^2)$ and
$E=C/(\epsilon)$. Its sole geometric fiber has dimension one, but
$\operatorname{Fitt}_0(E)=(\epsilon)\neq0$, so the identity of $\operatorname{Spec}C$ does not
factor through the rank-one locus. Passing to the radical would incorrectly accept it.

**Flattening-stratification theorem.** Let $S$ be noetherian, let $f:X\to S$ be projective and
finitely presented, fix a relatively very ample $\mathcal L$, and let $\mathcal F$ be coherent.
For every numerical polynomial $P$ there is a unique locally closed subscheme
$S_P\hookrightarrow S$ such that for every $g:T\to S$,

$$
g\text{ factors through }S_P
\quad\Longleftrightarrow\quad
\mathcal F_T\text{ is }T\text{-flat with fiber polynomial }P.
$$

The construction commutes with arbitrary base change. The subsets $|S_P|$ are disjoint and
cover $|S|$, and only finitely many meet a quasi-compact open.

**Proof.** If $P$ is not eventually nonnegative, no fiber can have polynomial $P$ and $S_P$ is
empty. Otherwise work over an affine open and push $\mathcal F$ forward along a projective embedding,
obtaining the sheaf of a finite graded module $M$. Apply the graded flatness lemma and intersect
the finitely many rank loci for $M_N,\ldots,M_{N+b}$. Their equations are Fitting ideals, so the
intersection is locally closed and has the asserted universal property for every affine test
scheme, not only for reduced or noetherian ones. Affine tests cover an arbitrary $T$, and the
loci agree on overlaps by uniqueness; hence they glue to $S_P$.

Every point belongs to the stratum indexed by its fiber polynomial. On a quasi-compact open,
the uniform bound in the proof and the finitely many possible ranks of the modules
$M_N,\ldots,M_{N+r}$ show that only finitely many polynomials occur. Finally, two candidate
strata factor through one another when tested on themselves, proving uniqueness. $\square$

### 8.4 Constancy and the flatness boundary

**Numerical flatness criterion.** Let $S$ be reduced and locally noetherian, let $f:X\to S$ be
projective, and let $\mathcal F$ be coherent. Then $\mathcal F$ is $S$-flat if and only if its
fiber Hilbert polynomial is locally constant.

The forward implication is Section 8.2. For the converse, work on an open-and-closed locus where
the polynomial is $P$. Every point lies on the flattening stratum $S_P$ just constructed, so
$S_P\hookrightarrow S$ has all of $S$ as underlying image and is cut out by a nilpotent ideal.
Reducedness kills that ideal, hence the identity factors through $S_P$ and $\mathcal F$ is flat.

Reducedness matters. On $\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ there is only one
topological fiber. The module $k$ has constant one-point fiber but is not flat.

## 9. Projective embeddings of curves and abelian schemes

### 9.1 Embedding projective curves

Let $C$ be a proper curve over a field and $\mathcal L$ ample. Serre's criterion makes $\mathcal L^n$ very ample for $n\gg0$. Concretely, for a length-two subscheme $Z\subset C$, the sequence

$$
0\to\mathcal I_Z\otimes\mathcal L^n
\to\mathcal L^n\to\mathcal L^n|_Z\to0
$$

and vanishing of $H^1$ show that sections separate $Z$. Uniformity is not obtained by choosing a
different exponent for every $Z$: the finite affine-chart argument in Section 4.5 simultaneously
generates the coordinate algebras and their first-order relations. It gives one exponent separating
all points and tangent vectors. The resulting immersion is closed because $C$ is proper.

Smooth proper curves have ample bundles, and this can be proved without anticipating
Riemann--Roch. We first record the finiteness fact needed in the argument.

**Finite-normalization lemma for curves.** The normalization of an integral curve of finite type
over a field is finite.

It is enough to work with an affine coordinate ring $A$. Noether normalization supplies
$k[t]\subseteq A$ with $A$ finite over $k[t]$, so
$K=\operatorname{Frac}(A)$ is finite over $k(t)$. The integral closure $B$ of $k[t]$ in $K$ is a
finite $k[t]$-module. Here is the one-dimensional lattice argument. After clearing denominators,
choose a field basis of the maximal separable subextension consisting of elements integral over
$k[t]$. The trace pairing places every integral element in the dual of the lattice spanned by
that basis, after multiplication by its nonzero discriminant. A submodule of this finite free
$k[t]$-module is finite because $k[t]$ is noetherian. For the remaining purely inseparable
extension in characteristic $p$, choose a finite $p$-basis and clear denominators in the finitely
many monomials of exponents below their inseparability degrees; the same bounded-lattice argument
applies. Thus $B$ is finite. Since $A$ is integral over $k[t]$, an element of $K$ is integral over
$A$ exactly when it is integral over $k[t]$. Hence $B$ is also the normalization of $A$, and its
finite set of $k[t]$-generators generates it over $A$.

Now suppose $C$ is connected, hence integral because it is regular. Choose a nonempty affine open
$U\subset C$ and a closed immersion $U\hookrightarrow\mathbf A^N_k$. Let $\overline U$ be its
closure in $\mathbf P^N_k$, and normalize $\overline U$. The lemma makes the normalization finite,
so the resulting normal curve $C'$ is projective and has the same function field as $C$.

The inverse of the common identification over $U$ is a rational map $C'\dashrightarrow C$. At a
missing closed point, the local ring of $C'$ is a discrete valuation ring; properness of $C$
extends the map uniquely across that point by the valuative criterion. Thus one obtains a proper
birational morphism $C'\to C$. Its fibers are zero-dimensional: a positive-dimensional fiber
would contain the sole one-dimensional irreducible component of $C'$ and make the map constant.
The morphism is therefore finite. Since $C$ is normal, a finite birational morphism to $C$ is an
isomorphism. Hence $C$ is projective. A smooth proper curve has finitely many open-and-closed
connected components, so applying the argument componentwise and taking the disjoint union of
their embeddings proves the general case. Pulling back $\mathcal O(1)$ supplies the desired ample
bundle, and Section 4.5 supplies all sufficiently high embeddings.

### 9.2 Uniform embeddings in families

Let $f:C\to S$ be a projective flat finitely presented family of curves over a noetherian quasi-compact scheme, and $\mathcal L$ relatively ample. There is one $n_0$ such that for $n\geq n_0$ the module

$$
E_n=f_*\mathcal L^n
$$

is locally free, commutes with every base change, and evaluation gives a closed immersion

$$
C\hookrightarrow\mathbf P_S(E_n).
$$

Its fiber ambient dimensions are constant on connected components because $\operatorname{rank}E_n=P_{C_s}(n)$. Without flatness the ranks can jump and the complete linear system need not form a vector bundle.

### 9.3 Polarized abelian schemes

Let $a:A\to S$ be an abelian scheme: a smooth proper group scheme with geometrically connected
fibers. The embedding statement needed in this book is polarized: $A$ is equipped with a
relatively ample line bundle $\mathcal L$. A line bundle is rigidified when
$e^*\mathcal L\simeq\mathcal O_S$, and symmetric when
$[-1]^*\mathcal L\simeq\mathcal L$. Tensoring by the pullback of $e^*\mathcal L^{-1}$ supplies a
rigidification without changing relative ampleness.

This formulation deliberately keeps the line bundle in the data. A homomorphism-valued
polarization may exist or descend even when a particular inducing bundle does not. Constructing
the dual abelian scheme and comparing those two notions belongs to the later theory of relative
Picard schemes; no such construction is being used as an input here.

### 9.4 Uniform very ampleness

**Polarized abelian embedding theorem.** Let $S$ be noetherian and quasi-compact, let
$a:A\to S$ be an abelian scheme, and let $\mathcal L$ be relatively ample. There is $n_0$ such
that, for every $n\geq n_0$,

$$
E_n=a_*\mathcal L^n
$$

is finite locally free and commutes with arbitrary base change, and the evaluation quotient gives
a closed immersion

$$
A\hookrightarrow\mathbf P_S(E_n).
$$

All ingredients have already been proved. Smoothness makes $\mathcal O_A$, and hence every
$\mathcal L^n$, flat over $S$. Relative Serre vanishing and cohomological base change as
established in Section 6.3 therefore
make $E_n$ finite locally free and base-change compatible for all large $n$. The affine-open
criterion and Serre generation make $\mathcal L^n$ very ample for all large $n$, uniformly
because $S$ is quasi-compact. The evaluation quotient is the corresponding immersion, and
properness of $A$ makes it closed.

Rigidifications and symmetries are compatible extra data on this embedding: they give specified
isomorphisms along the identity and inversion and can be imposed as equations in a later
parameter problem. They are not needed to prove the embedding itself. On a non-quasi-compact
base the same theorem holds locally, but one exponent need not work on every component. No sharp
universal exponent is asserted here; the later moduli constructions require only a sufficiently
high power.

## 10. Finite flat families and effective divisors

### 10.1 Families of length $d$

Fix an integer $d\geq0$.
A closed subscheme $Z\subseteq X_T$ is a family of length $d$ over $T$ if $Z\to T$ is finite locally free of rank $d$. If $d>0$, every geometric fiber is zero-dimensional of scheme-theoretic length $d$. If $d=0$, finite local freeness of rank zero forces $Z$ to be the empty subscheme; in particular there are no nonempty fibers to which a dimension should be assigned. Rank is stronger than counting points: one nonreduced point can have length $d$.

If $X\to S$ is separated, these families form a set-valued functor: an isomorphism between two closed subschemes over $X_T$ is unique. A tuple of sections produces the disjoint union of their graphs only while the graphs remain disjoint. When points collide, the reduced union loses points; the scheme-theoretic union may acquire a thickening and retain rank, but it need not remain flat. A length-$d$ family must retain the scheme structure and satisfy finite local freeness over the base.

### 10.2 Relative effective Cartier divisors

An effective Cartier divisor $D\subset C$ has invertible ideal locally generated by a non-zero-divisor. Its line bundle is $\mathcal O_C(D)=\mathcal I_D^{-1}$, with a canonical section vanishing exactly on $D$.

A relative effective Cartier divisor of degree $d$ on $C\to T$ is an effective Cartier divisor finite locally free of rank $d$ over $T$. If $C\to T$ is flat and finitely presented and an effective Cartier divisor $D$ is proper over $T$, with its restriction to every fiber an effective Cartier divisor of length $d$, then it is finite locally free: finite presentation and zero-dimensional fibers make $D\to T$ quasi-finite, properness makes it finite, and the fiberwise regularity of its equation lets the local flatness criterion apply to

$$
0\to\mathcal O_C(-D)\to\mathcal O_C\to\mathcal O_D\to0.
$$

On a singular curve, finite does not imply Cartier. The ideal $(x,y)$ of the node in $k[x,y]/(xy)$ is not principal.

### 10.3 Divisors on smooth relative curves

If $C\to S$ is smooth of pure relative dimension one, every finite locally free closed subscheme $D\subset C_T$ is a relative effective Cartier divisor. This assertion includes nilpotent bases, so a fiberwise slogan is not enough. Work locally at a point of $D$. Write the smooth algebra as $B$ over the local base ring $R$, and let $Q=B/I$ be the finite projective $R$-algebra of the divisor. Since both $B$ and $Q$ are $R$-flat, $I$ is $R$-flat. On the residue fiber, $B\otimes_Rk$ is a regular one-dimensional local ring and $I\otimes_Rk$ is generated by a non-zero-divisor $u$. Lift $u$ to $\widetilde u\in I$. The cokernel of

$$
B\xrightarrow{\,\widetilde u\,}I
$$

vanishes after tensoring with $k$, hence vanishes near the point by Nakayama. Its kernel also
vanishes: after tensoring it is zero because $u$ is regular, and flatness of $I$ gives the needed
injectivity in the local flatness criterion. Thus $I=(\widetilde u)$ with $\widetilde u$ a
non-zero-divisor. Conversely, a relative divisor of degree $d$ is finite locally free by
definition. Hence the two functors agree:

$$
\{\text{length-}d\text{ closed families in }C_T\}
=\{\text{relative effective divisors of degree }d\}.
$$

Smoothness is decisive. At a node the singular point itself is a length-one subscheme but not Cartier.

### 10.4 Norms and addition

Divisors cut out locally by $a$ and $b$ add by multiplication: $D+E$ is cut out by $ab$, has degree $\deg D+\deg E$, and

$$
\mathcal O_C(D+E)\simeq\mathcal O_C(D)\otimes\mathcal O_C(E).
$$

For finite locally free $q:Z\to T$ and invertible $\mathcal M$ on $Z$, define

$$
N_{Z/T}(\mathcal M)
=\det(q_*\mathcal M)\otimes\det(q_*\mathcal O_Z)^{-1}.
$$

Norms commute with base change and tensor products. Applied along a universal divisor, they turn a moving unordered family into a canonical line bundle on the parameter base.

### 10.5 Descent along finite locally free covers

The construction of the universal divisor in Section 11.4 proceeds on charts. Two different
descriptions of the same object — a symmetric power on one side, a divisor functor on the other —
are compared only after a surjective pullback that orders the roots of a monic equation, and the
divisors produced on the individual charts have to be recognized as the restrictions of one divisor
on the quotient. Both steps are descent statements: one must know that an effective Cartier divisor
is _determined_ by its pullback along a faithfully flat cover, and that a divisor given upstairs
whose two pullbacks to the double product agree _comes from_ a divisor downstairs. Neither
statement is formal, and neither follows from invariance under a group action, since the covers in
question are not torsors where the divisors collide.

A general theory of descent, for arbitrary quasi-coherent sheaves, schemes and morphisms, is
developed in a later volume; the present section proves from scratch exactly the special case that
Chapter 11 consumes, and that later theory will subsume it. The archetype to keep in mind is a
finite locally free cover, for instance the map which orders the $d$ roots of a monic polynomial;
the proofs are written for a faithfully flat affine cover, which costs nothing extra and covers the
finitely many affine pieces of an étale covering as well.

We begin with the algebra. Let $R\to R'$ be a ring map. For an $R'$-module $M'$ write
$M'\otimes_RR'$ for the $R'\otimes_RR'$-module in which the _left_ tensor factor acts on $M'$, and
$R'\otimes_RM'$ for the one in which the _right_ factor acts on $M'$. Both are the base changes of
$M'$ along the two coprojections $p_1,p_2:R'\to R'\otimes_RR'$, $p_1(a)=a\otimes1$,
$p_2(a)=1\otimes a$.

**Amitsur exactness lemma.** Let $R\to R'$ be faithfully flat and let $M$ be an $R$-module. Then

$$
0\longrightarrow M\longrightarrow M\otimes_RR'
\xrightarrow{\ \ \delta\ \ }M\otimes_RR'\otimes_RR' \tag{10.1}
$$

is exact, where $\delta(m\otimes a)=m\otimes a\otimes1-m\otimes1\otimes a$.

**Proof.** Suppose first that the structure map admits an $R$-linear retraction
$\sigma:R'\to R$ with $\sigma(1)=1$. Define $h_0:M\otimes_RR'\to M$ by $h_0=\mathrm{id}\otimes\sigma$
and $h_1:M\otimes_RR'\otimes_RR'\to M\otimes_RR'$ by
$h_1(m\otimes a\otimes b)=\sigma(b)\,m\otimes a$. If $x\in M\otimes_RR'$ satisfies $\delta(x)=0$,
then applying $h_1$ gives $x-h_0(x)\otimes1=0$, so $x$ lies in the image of $M$; and if
$m\in M$ maps to zero in $M\otimes_RR'$ then $m=h_0(m\otimes1)=0$. So (10.1) is exact in this case.

In general, base change (10.1) along $R\to R'$. Since $R'$ is flat over $R$, the base-changed
sequence is the sequence (10.1) attached to the ring map $R'\to R'\otimes_RR'$ (the coprojection
$p_1$) and to the $R'$-module $M\otimes_RR'$; here one uses the canonical identifications
$(M\otimes_RR')\otimes_{R'}(R'\otimes_RR')=M\otimes_RR'\otimes_RR'$ and similarly one factor
higher. The ring map $p_1:R'\to R'\otimes_RR'$ is faithfully flat, being a base change of a
faithfully flat map, and it admits the $R'$-linear retraction given by multiplication
$\mu(a\otimes b)=ab$, which sends $1$ to $1$. By the case already treated, the base-changed
sequence is exact. Faithful flatness of $R\to R'$ now returns exactness of (10.1) itself: a
complex of $R$-modules is exact if and only if it becomes exact after $\otimes_RR'$. $\square$

Exactness of (10.1) is already the _uniqueness_ half of descent: an $R$-module is recovered from
its base change as the equalizer of the two maps to the double base change. It is also exactly the
mechanism behind the descent of finite submodules and of surjectivity used in Section 5.2, which is
recorded here in its general form. The existence half
needs the datum that tells how the two pullbacks are to be identified.

**Definition.** Let $R\to R'$ be a ring map. A _descent datum_ on an $R'$-module $M'$ is an
isomorphism of $R'\otimes_RR'$-modules

$$
\varphi:M'\otimes_RR'\xrightarrow{\ \sim\ }R'\otimes_RM' \tag{10.2}
$$

satisfying the cocycle condition on $R'\otimes_RR'\otimes_RR'$: writing $\varphi_{ij}$ for the map
obtained by base change along the coprojection onto the $i$th and $j$th factors, one requires
$\varphi_{13}=\varphi_{23}\circ\varphi_{12}$. A morphism of descent data is an $R'$-linear map
commuting with the $\varphi$'s. Every $R$-module $M$ gives a descent datum on $M'=M\otimes_RR'$,
namely the canonical identification of both sides with $M\otimes_RR'\otimes_RR'$; call it the
_trivial_ datum.

**Descent theorem for modules.** Let $R\to R'$ be faithfully flat. Then

$$
M\longmapsto\bigl(M\otimes_RR',\ \text{trivial datum}\bigr)
$$

is an equivalence from $R$-modules to $R'$-modules equipped with a descent datum. A quasi-inverse
sends $(M',\varphi)$ to

$$
M'^{\varphi}=\bigl\{m\in M'\ :\ \varphi(m\otimes1)=1\otimes m\bigr\}. \tag{10.3}
$$

The equivalence is exact, and $M$ is finitely generated, finitely presented, flat, invertible, or
finite locally free of a given rank $d$ if
and only if $M\otimes_RR'$ is.

**Proof.** _Faithfulness and fullness._ For $R$-modules $M,N$, the map
$\operatorname{Hom}_R(M,N)\to\operatorname{Hom}_{R'}(M\otimes R',N\otimes R')$ is injective because
$N\to N\otimes_RR'$ is injective by (10.1) and $M$ generates $M\otimes R'$. If an $R'$-linear
$u':M\otimes R'\to N\otimes R'$ commutes with the trivial data, then for $m\in M$ the element
$u'(m\otimes1)$ has equal images under the two maps of (10.1) for $N$, hence lies in $N$; the
resulting $R$-linear $u:M\to N$ base-changes to $u'$ because both agree on the generators
$m\otimes1$.

_Effectivity._ Let $(M',\varphi)$ be a descent datum and put $M=M'^{\varphi}$. We must show that
the natural map $c:M\otimes_RR'\to M'$ is an isomorphism. Consider first the case in which the
structure map admits an $R$-algebra section $s:R'\to R$. Let
$\tau=\mathrm{id}_{R'}\otimes s:R'\otimes_RR'\to R'$, $a\otimes b\mapsto a\,s(b)$, an
$R'$-algebra map for the left factor, and note $\tau\circ p_1=\mathrm{id}_{R'}$ and
$\tau\circ p_2=\iota\circ s$ where $\iota:R\to R'$. Base-changing $\varphi$ along $\tau$ therefore
yields an isomorphism of $R'$-modules

$$
\psi:M'\xrightarrow{\ \sim\ }N\otimes_RR',
\qquad N:=M'\otimes_{R',s}R,
$$

where $N$ is an $R$-module. We claim that $\psi$ carries $\varphi$ to the trivial datum on
$N\otimes_RR'$, and this is where the cocycle condition is used. Apply base change along the ring
map

$$
g:R'\otimes_RR'\otimes_RR'\longrightarrow R'\otimes_RR',
\qquad a\otimes b\otimes c\longmapsto a\otimes b\,s(c),
$$

to the identity $\varphi_{13}=\varphi_{23}\circ\varphi_{12}$. One computes
$g\circ p_{12}=\mathrm{id}$, $g\circ p_{13}=p_1\circ\tau$ and $g\circ p_{23}=p_2\circ\tau$, using
that $s(c)$ lies in $R$ and may therefore be moved across the tensor sign. Hence $g^*$ turns
$\varphi_{12}$ into $\varphi$, and $\varphi_{13},\varphi_{23}$ into the base changes of
$\psi=\tau^*\varphi$ along $p_1$ and $p_2$. The cocycle identity becomes

$$
p_1^*\psi=p_2^*\psi\circ\varphi,
$$

which is precisely the condition for $\psi$ to be a morphism from $(M',\varphi)$ to
$N\otimes_RR'$ with its trivial datum. Granting this, the invariants (10.3) of the trivial datum on $N\otimes_RR'$ are
$N$ by the Amitsur exactness lemma, so $\psi$ restricts to an isomorphism $M\to N$ and $c$ is an isomorphism.

For the general case, base-change everything along $R\to R'$. The formation of the invariants
(10.3) commutes with this base change, because $M$ is the kernel of the $R$-linear map
$m\mapsto\varphi(m\otimes1)-1\otimes m$ from $M'$ to $R'\otimes_RM'$ and $R'$ is $R$-flat, so
kernels are preserved. The base-changed datum lives over the ring map
$p_1:R'\to R'\otimes_RR'$, which is faithfully flat and admits the $R'$-algebra section $\mu$; by
the case just treated, the base change of $c$ is an isomorphism. Faithful flatness then makes $c$
itself an isomorphism.

_Exactness._ The functor $-\otimes_RR'$ is exact by flatness, and a sequence of $R$-modules is
exact as soon as its base change is, by faithful flatness. A sequence of descent data is exact
exactly when the underlying sequence of $R'$-modules is; so a sequence of $R$-modules is exact if
and only if the corresponding sequence of descent data is, and both the equivalence and its
quasi-inverse are exact.

_Properties._ If $M$ is finitely generated, finitely presented, flat or invertible, so is
$M\otimes_RR'$; these are stable under base change. Conversely, suppose $M\otimes_RR'$ is finitely
generated. Writing $M$ as the filtered union of its finitely generated submodules $M_i$ and using
flatness, $M\otimes_RR'$ is the filtered union of the $M_i\otimes_RR'$, so finitely many generators
already lie in some $M_i\otimes_RR'$; then $M_i\otimes_RR'\to M\otimes_RR'$ is surjective, and
faithful flatness makes $M_i\to M$ surjective, so $M$ is finitely generated. Given that, choose a
surjection $R^n\to M$ with kernel $K$; if $M\otimes_RR'$ is finitely presented then the kernel
$K\otimes_RR'$ of $R'^n\to M\otimes_RR'$ is finitely generated, hence so is $K$ by the previous
sentence, and $M$ is finitely presented. If $M\otimes_RR'$ is $R'$-flat and $N_1\to N_2$ is an
injection of $R$-modules, then $M\otimes_RN_1\to M\otimes_RN_2$ becomes injective after
$\otimes_RR'$, hence is injective; so $M$ is flat. Finally, a module is invertible exactly when it
is finitely presented, flat, and of rank one at every prime; the first two conditions have just
been shown to descend, and the rank of $M$ at a prime $\mathfrak p$ equals the rank of
$M\otimes_RR'$ at any prime of $R'$ lying over $\mathfrak p$, of which there is at least one by
faithful flatness. The same argument with rank $d$ in place of rank one gives the statement about
finite locally free modules of rank $d$, a module being finite locally free of rank $d$ exactly
when it is finitely presented, flat, and of rank $d$ at every prime. $\square$

We now pass to schemes. Call a morphism $p:V'\to V$ a _finite flat cover_ if it is affine,
faithfully flat and quasi-compact. Two examples exhaust the uses below: a surjective finite locally
free morphism, which is the archetype and the case named in the title of this section, and the
disjoint union of finitely many affine opens of an étale covering, which is how a covering family
is reduced to a single cover. Write $V''=V'\times_VV'$ with projections $q_1,q_2$, and
$V'''=V'\times_VV'\times_VV'$. Since $p$ is flat, so are $q_1$ and $q_2$, and inverse image along
them is exact; consequently, for a quasi-coherent ideal $\mathcal I'\subseteq\mathcal O_{V'}$, both
$q_1^*\mathcal I'$ and $q_2^*\mathcal I'$ are quasi-coherent ideals of $\mathcal O_{V''}$.

The point of restricting attention to ideals is that no descent datum has to be supplied by hand.

**Ideal descent lemma.** Let $p:V'\to V$ be a finite flat cover.

1. If $\mathcal I_1,\mathcal I_2\subseteq\mathcal O_V$ are quasi-coherent ideals whose inverse
   image ideals in $\mathcal O_{V'}$ coincide, then $\mathcal I_1=\mathcal I_2$. Equivalently, two
   closed subschemes of $V$ with the same scheme-theoretic preimage in $V'$ are equal.
2. If $\mathcal I'\subseteq\mathcal O_{V'}$ is a quasi-coherent ideal with
   $q_1^*\mathcal I'=q_2^*\mathcal I'$ as ideals of $\mathcal O_{V''}$, then there is a unique
   quasi-coherent ideal $\mathcal I\subseteq\mathcal O_V$ with $p^*\mathcal I=\mathcal I'$ inside
   $\mathcal O_{V'}$.
3. In the situation of 2, the ideal $\mathcal I$ is invertible if and only if $\mathcal I'$ is;
   that is, the closed subscheme $V(\mathcal I)$ is an effective Cartier divisor if and only if
   $V(\mathcal I')$ is.
4. Suppose the cover arises by base change from a finite flat cover $u:W'\to W$, that is, a
   quasi-compact separated $\pi:V\to W$ is given and $V'=V\times_WW'$. If in the situation of 2 the
   morphism $V(\mathcal I')\to W'$ is finite locally free of rank $d$, then $V(\mathcal I)\to W$ is
   finite locally free of rank $d$.

**Proof.** Assertions 1–3 are local on $V$, so let $V_0=\operatorname{Spec}R\subseteq V$ be
affine. Since $p$ is affine, $p^{-1}(V_0)=\operatorname{Spec}R'$, and $R\to R'$ is faithfully flat
because $p$ is; moreover $q_1,q_2$ restrict over $V_0$ to the two coprojections
$\operatorname{Spec}(R'\otimes_RR')\to\operatorname{Spec}R'$. By the affine dictionary
(Book 7b, Corollary 2.4) quasi-coherent sheaves on these affines are the same thing as modules, so
the first three assertions translate into the algebra just proved. Assertion 4 is local on $W$
instead and is treated at the end.

(1) An ideal $I\subseteq R$ is recovered from $IR'\subseteq R'$: indeed $I=IR'\cap R$ inside $R'$,
because $I\to R\to R'$ has image $IR'$ (flatness makes $I\otimes_RR'\to R'$ injective with image
$IR'$) and the Amitsur exactness lemma applied to $R/I$ shows that $R/I\to R'/IR'$ is injective. Hence
$I_1R'=I_2R'$ forces $I_1=I_2$.

(2) Put $I'=\Gamma(\operatorname{Spec}R',\mathcal I')$. Because $q_1,q_2$ are flat, the two
modules $I'\otimes_RR'$ and $R'\otimes_RI'$ are subsets of $R'\otimes_RR'$, and the hypothesis says
they are the same subset. Let $\varphi$ be the resulting identification; it is an isomorphism of
$R'\otimes_RR'$-modules, and it satisfies the cocycle condition automatically, since all three of
$\varphi_{12},\varphi_{23},\varphi_{13}$ are identifications of submodules of
$R'\otimes_RR'\otimes_RR'$ compatible with those inclusions, and two maps into a module that agree
after composition with a monomorphism agree. Thus $(I',\varphi)$ is a descent datum, and the
inclusion $I'\subseteq R'$ is a morphism from it to the trivial datum on $R'$. By the descent
theorem for modules there is an $R$-module $I$ with $I\otimes_RR'=I'$, and by exactness of the
equivalence the map $I\to R$ obtained from the inclusion is injective; so $I$ is an ideal of $R$
with $IR'=I'$. Uniqueness is (1), and uniqueness also makes the ideals constructed over two
affine opens agree on their intersection, so they glue to $\mathcal I$.

(3) Invertibility of a module descends and ascends along a faithfully flat ring map, by the last
clause of the descent theorem for modules. An invertible ideal is locally generated by one element
$f$ with $R\xrightarrow{\,f\,}I$ bijective, so $f$ is a non-zero-divisor; conversely an ideal
locally generated by a non-zero-divisor is invertible. Hence $V(\mathcal I)$ is an effective
Cartier divisor exactly when $V(\mathcal I')$ is.

(4) The assertion is local on $W$, so assume $W$ affine. Write $D=V(\mathcal I)$ and
$D'=V(\mathcal I')=D\times_WW'$, and put
$\mathcal A=\pi_*(\mathcal O_V/\mathcal I)$, a quasi-coherent $\mathcal O_W$-algebra (Book 7b,
Theorem 2.10). Since $u$ is flat and $\pi$ is quasi-compact and separated, the formation of
$\mathcal A$ commutes with the base change $u$ (Book 7b, Corollary 5.4), so
$u^*\mathcal A=\pi'_*\mathcal O_{D'}$, which is a finite locally free $\mathcal O_{W'}$-module of
rank $d$ by hypothesis. The last clause of the descent theorem for modules therefore makes
$\mathcal A$ finite locally free of rank $d$ over $\mathcal O_W$; this already fixes the degree.
It remains to see that the canonical $W$-morphism $g:D\to Y:=\operatorname{Spec}_W\mathcal A$ is an
isomorphism, for then $D\to W$ is finite locally free of rank $d$. By construction $g$ base-changes
along $u$ to the corresponding morphism $D'\to Y'$, which is an isomorphism because $D'\to W'$ is
affine, so that $D'=\operatorname{Spec}_{W'}\pi'_*\mathcal O_{D'}$. Now $g$ is bijective on points:
the two projections $D'\to D$ and $Y'\to Y$ are surjective, and $D'\to Y'$ is bijective, which
forces $g$ to be surjective and injective. It is a homeomorphism because $D'\to D$ is surjective,
flat and quasi-compact, hence a topological quotient map, and the same for $Y$. Finally, for
$x\in D$ with image $y$, choose $x'\in D'$ over $x$ and let $y'$ be its image; the local
homomorphism $\mathcal O_{Y,y}\to\mathcal O_{D,x}$ becomes an isomorphism after the faithfully flat
local homomorphism $\mathcal O_{Y,y}\to\mathcal O_{Y',y'}$, hence is an isomorphism, bijectivity of
a module map being detected by a faithfully flat base change. A morphism of schemes that is a
homeomorphism and induces isomorphisms on all local rings is an isomorphism. $\square$

Two supplements make the lemma usable in the form Chapter 11 needs. The first is that everything
survives multiplication by a fixed scheme: if $p:V'\to V$ is a finite flat cover and $C\to S$ is
any morphism with $V\to S$ given, then $\mathrm{id}_C\times p:C\times_SV'\to C\times_SV$ is again a
finite flat cover, since affineness, flatness, surjectivity and quasi-compactness are stable under
base change. So divisors on $C\times_SV'$ may be descended to $C\times_SV$.

The second is the passage from a single cover to a covering family.

**Étale gluing corollary.** Let $\{p_\alpha:V_\alpha\to V\}_{\alpha\in A}$ be a jointly surjective
family of flat, locally finitely presented morphisms — for instance an étale covering. Suppose
given quasi-coherent ideals $\mathcal I_\alpha\subseteq\mathcal O_{V_\alpha}$ whose inverse images
to $V_\alpha\times_VV_\beta$ agree for all $\alpha,\beta$. Then there is a unique quasi-coherent
ideal $\mathcal I\subseteq\mathcal O_V$ inducing $\mathcal I_\alpha$ on each $V_\alpha$; it is
invertible as soon as every $\mathcal I_\alpha$ is.

**Proof.** A flat, locally finitely presented morphism is open, so the images of the $p_\alpha$
form an open cover of $V$. Fix an affine open $W\subseteq V$. Choose for each point of $W$ an index
$\alpha$ and an affine open of $V_\alpha$ mapping into $W$ and containing a preimage of that point;
by quasi-compactness of $W$, finitely many such affine opens $W_1,\ldots,W_m$ have images covering
$W$. Then $V'=W_1\sqcup\cdots\sqcup W_m$ is affine, and $V'\to W$ is flat, surjective and
quasi-compact, hence a finite flat cover. The ideals $\mathcal I_\alpha$ restrict to a
quasi-coherent ideal $\mathcal I'$ on $V'$, and the hypothesis gives
$q_1^*\mathcal I'=q_2^*\mathcal I'$ on $V'\times_WV'$, because $W_j\times_WW_k$ is an open
subscheme of $V_{\alpha_j}\times_VV_{\alpha_k}$ and the two inverse images agree there. The ideal
descent lemma produces a unique quasi-coherent ideal on $W$, invertible when $\mathcal I'$ is, and
its inverse image to each $V_\alpha$ is $\mathcal I_\alpha$ over $W$, again by uniqueness applied
on $V_\alpha$. Uniqueness over affine opens makes these ideals glue over $V$. $\square$

Two consequences are worth naming, since they are exactly what Chapter 11 invokes. First,
effective Cartier divisors satisfy _effective descent_ along the covers considered: a divisor on
$V'$ whose two pullbacks to $V''$ coincide is the pullback of a unique divisor on $V$. Second, the
assignment sending $T$ to the set of relative effective Cartier divisors of degree $d$ on $C_T$ is
a sheaf for the topology generated by these covers: gluing is the étale gluing corollary, and
separatedness of the presheaf is clause 1 of the ideal descent lemma. That is the only sense in
which the divisor functor of Section 11.4 is treated as a sheaf. The companion statement about the
other functor compared there — that a morphism into a quasi-projective target may be recognized and
constructed after such a cover — is the subject of the next section.

### 10.6 Descent of morphisms into a quasi-projective target

Descending sheaves and ideals is only half of what Chapter 11 needs. The comparison there is
between two _functors_: the functor of points of the symmetric power and the functor of relative
divisors. A bijection between them is produced first on étale charts, and one then wants the
chartwise bijections to assemble into a bijection over an arbitrary test scheme $T$. Surjectivity
of the assembled map requires manufacturing a morphism $T\to\operatorname{Sym}^d_S(C)$ out of
morphisms defined only after an étale cover of $T$, and injectivity requires knowing that a
morphism is determined by its restriction to such a cover. In other words, one needs the presheaf

$$
T\longmapsto\operatorname{Hom}_S(T,X)
$$

to be a _sheaf_ for the covers of Section 10.5, for the relevant target $X$. This is not a formal
statement: a morphism is a morphism of locally ringed spaces, and there is no reason in general for
the ringed-space data to descend. What makes it true is that the targets occurring here are
quasi-projective, so that a morphism into $X$ is the same as an invertible quotient of a fixed
module subject to a closed condition — and invertible modules with a descent datum have already
been descended in Section 10.5.

We prove the sheaf property in three steps: uniqueness for any separated target, existence for an
affine target (which is Amitsur exactness verbatim), and existence for a quasi-projective target
(which uses the descent theorem for modules and the universal property of a projective bundle). As
in Section 10.5, a _finite flat cover_ is an affine, faithfully flat and quasi-compact morphism;
for $p:T'\to T$ such a cover we write $T''=T'\times_TT'$ with projections $q_1,q_2$ and
$T'''=T'\times_TT'\times_TT'$ with projections $\mathrm{pr}_i$ and $\mathrm{pr}_{ij}$.

The uniqueness half needs no positivity at all, only a closed diagonal.

**Uniqueness lemma for morphisms.** Let $X\to S$ be separated, let $T$ be an $S$-scheme and let
$p:T'\to T$ be a finite flat cover. If $f_1,f_2:T\to X$ are $S$-morphisms with
$f_1\circ p=f_2\circ p$, then $f_1=f_2$.

**Proof.** Let $E$ be the equalizer of $f_1$ and $f_2$, that is, the fiber product of
$(f_1,f_2):T\to X\times_SX$ and the diagonal $\Delta_{X/S}:X\to X\times_SX$. Separatedness makes
$\Delta_{X/S}$ a closed immersion, so $E\to T$ is a closed immersion; let
$\mathcal I\subseteq\mathcal O_T$ be its quasi-coherent ideal. A morphism $Z\to T$ factors through
$E$ exactly when its composites with $f_1$ and $f_2$ agree, so the hypothesis says that $p$
factors through $E$; equivalently, the ideal $\mathcal I$ dies in $\mathcal O_{T'}$, that is
$\mathcal I\cdot\mathcal O_{T'}=0$.

Now the question is local on $T$. Let $V=\operatorname{Spec}R\subseteq T$ be affine; since $p$ is
affine, $p^{-1}(V)=\operatorname{Spec}R'$ with $R\to R'$ faithfully flat, and $\mathcal I$
corresponds to an ideal $I\subseteq R$ with $IR'=0$. Flatness makes $I\otimes_RR'\to R'$ injective
with image $IR'$, so $I\otimes_RR'=0$, and faithful flatness gives $I=0$. Hence $\mathcal I=0$,
$E=T$, and $(f_1,f_2)$ factors through the diagonal, which says exactly $f_1=f_2$. $\square$

Only faithful flatness and quasi-compactness of $p$ entered; affineness was a convenience for
naming $R'$. In particular the lemma applies to any of the covers of Section 10.5, and to their
restrictions over an open subscheme of $T$, since these properties are stable under such
restriction.

Next, existence for an affine target. Here the descent datum is not needed at all: the equality of
the two restrictions to $T''$ is already the equalizer condition of the Amitsur exactness lemma.

**Descent of morphisms into an affine target.** Let $X\to S$ be an affine morphism, let $T$ be an
$S$-scheme and let $p:T'\to T$ be a finite flat cover. Then

$$
\operatorname{Hom}_S(T,X)\xrightarrow{\ \ -\circ p\ \ }\operatorname{Hom}_S(T',X)
\rightrightarrows\operatorname{Hom}_S(T'',X) \tag{10.4}
$$

is an equalizer diagram: composition with $p$ is injective, and its image consists exactly of those
$f':T'\to X$ with $f'\circ q_1=f'\circ q_2$.

**Proof.** Write $X=\operatorname{Spec}_S\mathcal B$ for a quasi-coherent $\mathcal O_S$-algebra
$\mathcal B$, and write $a_T:T\to S$ for the structure morphisms. For every $S$-scheme $Z$,
$S$-morphisms $Z\to X$ correspond naturally to $\mathcal O_S$-algebra homomorphisms
$\mathcal B\to a_{Z*}\mathcal O_Z$. So it suffices to prove that

$$
a_{T*}\mathcal O_T\longrightarrow a_{T'*}\mathcal O_{T'}
\rightrightarrows a_{T''*}\mathcal O_{T''}
$$

is an equalizer of sheaves of $\mathcal O_S$-algebras; the equalizer of two algebra maps is a
subalgebra, so an equalizing algebra map from $\mathcal B$ factors through it uniquely as an
algebra map. Because $a_{T'}=a_T\circ p$ and $a_{T''}=a_T\circ p\circ q_1$, this diagram is
obtained by applying the left exact functor $a_{T*}$ to

$$
\mathcal O_T\longrightarrow p_*\mathcal O_{T'}\rightrightarrows (p\circ q_1)_*\mathcal O_{T''},
$$

so it is enough to know that the latter is an equalizer of sheaves on $T$. That may be checked on
an affine open cover. For $V=\operatorname{Spec}R\subseteq T$ affine we have
$p^{-1}(V)=\operatorname{Spec}R'$ with $R\to R'$ faithfully flat, and
$(p\circ q_1)^{-1}(V)=\operatorname{Spec}(R'\otimes_RR')$; the sequence of sections over $V$ is
then precisely the sequence (10.1) for the module $M=R$, whose exactness is the Amitsur exactness
lemma. $\square$

The target that Chapter 11 needs is not affine but quasi-projective, and for it the argument must
be genuinely geometric. The idea is dictated by the definition of quasi-projectivity. A morphism
into a projective bundle is the same thing as an invertible quotient of a fixed module, by the
projective-bundle theorem of Section 2.2; an invertible module together with the datum identifying
its two pullbacks descends, by the descent theorem for modules of Section 10.5; and the condition
of landing in a locally closed subscheme of the bundle is a condition that can be tested after a
faithfully flat cover. The only point requiring care is that the identification of the two
pullbacks must be produced canonically, since a descent datum is extra structure and the
hypothesis supplies only an equality of morphisms. Surjectivity of the universal quotient is what
makes the identification unique, and uniqueness then gives the cocycle condition for free.

**Descent of morphisms into a quasi-projective target.** Let $X\to S$ be quasi-projective, let $T$
be an $S$-scheme and let $p:T'\to T$ be a finite flat cover. Then

$$
\operatorname{Hom}_S(T,X)\xrightarrow{\ \ -\circ p\ \ }\operatorname{Hom}_S(T',X)
\rightrightarrows\operatorname{Hom}_S(T'',X) \tag{10.5}
$$

is an equalizer diagram. That is, an $S$-morphism $f':T'\to X$ with $f'\circ q_1=f'\circ q_2$ is
$f\circ p$ for a unique $S$-morphism $f:T\to X$.

**Proof.** _Uniqueness_ is the uniqueness lemma for morphisms, a quasi-projective morphism being
separated (Section 3.3).

_Reduction to affine $T$._ Suppose the existence statement is known for affine $T$. In general
cover $T$ by affine opens $T_i$ and put $T'_i=p^{-1}(T_i)$; each $p_i:T'_i\to T_i$ is again a
finite flat cover, and $T'_i\times_{T_i}T'_i$ is the open part of $T''$ lying over $T_i$, so the
restriction $f'_i$ of $f'$ still satisfies the equalizer condition. We obtain
$f_i:T_i\to X$ with $f_i\circ p_i=f'_i$. On an intersection $T_i\cap T_j$, the two morphisms $f_i$
and $f_j$ become equal after composition with the finite flat cover $p^{-1}(T_i\cap T_j)\to
T_i\cap T_j$, since both composites equal the restriction of $f'$; by the uniqueness lemma they
agree. Hence the $f_i$ glue to $f:T\to X$, and $f\circ p=f'$ because this may be checked over the
$T_i$.

So assume $T=\operatorname{Spec}R$; then $T'=\operatorname{Spec}R'$ with $R\to R'$ faithfully flat,
$T''=\operatorname{Spec}(R'\otimes_RR')$ and $T'''=\operatorname{Spec}(R'\otimes_RR'\otimes_RR')$.

_The line bundle and its descent datum._ Fix a locally closed immersion
$\iota:X\hookrightarrow P=\mathbf P_S(\mathcal E)$ over $S$ with $\mathcal E$ finite locally free
on $S$, and factor it as a closed immersion of $X$ into an open subscheme $U\subseteq P$. Put
$g'=\iota\circ f':T'\to P$. By the projective-bundle theorem, $g'$ corresponds to an invertible
quotient

$$
\kappa':\mathcal E_{T'}\twoheadrightarrow\mathcal L',
$$

and, the correspondence commuting with base change, the pullbacks $q_1^*\kappa'$ and $q_2^*\kappa'$
correspond to $g'\circ q_1$ and $g'\circ q_2$. These two morphisms are equal by hypothesis, so the
two quotients of $\mathcal E_{T''}$ — the canonical identifications $q_i^*\mathcal E_{T'}
=\mathcal E_{T''}$ being understood — are equivalent: there is an isomorphism

$$
\varphi:q_1^*\mathcal L'\xrightarrow{\ \sim\ }q_2^*\mathcal L'
\qquad\text{with}\qquad
\varphi\circ q_1^*\kappa'=q_2^*\kappa'. \tag{10.6}
$$

Such a $\varphi$ is unique, because $q_1^*\kappa'$ is surjective and two morphisms out of
$q_1^*\mathcal L'$ agreeing after composition with a surjection onto it agree. Uniqueness
immediately yields the cocycle condition. Indeed, pulling (10.6) back along the three projections
$\mathrm{pr}_{ij}:T'''\to T''$ produces isomorphisms
$\varphi_{ij}:\mathrm{pr}_i^*\mathcal L'\to\mathrm{pr}_j^*\mathcal L'$ each compatible with the
corresponding surjections from $\mathcal E_{T'''}$, since pullback preserves the identity (10.6).
Both $\varphi_{13}$ and the composite $\varphi_{23}\circ\varphi_{12}$ are therefore isomorphisms
$\mathrm{pr}_1^*\mathcal L'\to\mathrm{pr}_3^*\mathcal L'$ compatible with those surjections, and
the uniqueness just proved makes them equal.

_Descending._ Since $T$ is affine, $\mathcal E_T$ is the sheaf attached to an $R$-module $E$ and
$\mathcal E_{T'}$ to $E\otimes_RR'$, while $\mathcal L'$ is the sheaf attached to an invertible
$R'$-module $L'$; the isomorphism $\varphi$ is a descent datum on $L'$ in the sense of (10.2), and
(10.6) says that $\kappa':E\otimes_RR'\to L'$ is a morphism of descent data from the trivial datum
on $E\otimes_RR'$ to $(L',\varphi)$. By the descent theorem for modules there are an $R$-module
$L$ with $L\otimes_RR'\simeq L'$ carrying $\varphi$ to the trivial datum, and an $R$-linear map
$u:E\to L$ whose base change is $\kappa'$. The module $L$ is invertible because $L'$ is, by the
permanence clause of that theorem, and $u$ is surjective because its cokernel vanishes after the
faithfully flat base change $-\otimes_RR'$. Thus $\kappa:\mathcal E_T\twoheadrightarrow\mathcal L$
is an invertible quotient, and the projective-bundle theorem returns an $S$-morphism $g:T\to P$
with $g^*\mathcal O(1)=\mathcal L$. Its restriction $g\circ p$ corresponds to $p^*\kappa=\kappa'$,
hence equals $g'$.

_Factoring through $X$._ It remains to see that $g$ factors through the locally closed subscheme
$X$. Topologically, every point of $T$ is $p(t')$ for some $t'\in T'$ because $p$ is surjective,
and $g(p(t'))=g'(t')\in\iota(X)$. So the set-theoretic image of $g$ lies in $\iota(X)$, in
particular in the open subscheme $U$, and $g$ factors uniquely through $U$. Let
$\mathcal J\subseteq\mathcal O_U$ be the quasi-coherent ideal of the closed subscheme $X\subseteq U$
and let $\mathcal K\subseteq\mathcal O_T$ be the image of $g^*\mathcal J\to\mathcal O_T$. Applying
the right exact functor $p^*$ to the surjection $g^*\mathcal J\twoheadrightarrow\mathcal K$ shows
that the image of $p^*\mathcal K\to\mathcal O_{T'}$ equals the image of
$g'^*\mathcal J\to\mathcal O_{T'}$, which is zero because $g'$ factors through $X$. Flatness of $p$
identifies $p^*\mathcal K$ with its image in $\mathcal O_{T'}$, so $p^*\mathcal K=0$, and faithful
flatness gives $\mathcal K=0$. An ideal pulling back to zero is exactly the condition for $g$ to
factor through the closed subscheme, so $g=\iota\circ f$ for a unique morphism $f:T\to X$. It is an
$S$-morphism because $g$ is one and $\iota$ lies over $S$, and $\iota\circ f\circ p=g'=\iota\circ f'$
with $\iota$ a monomorphism gives $f\circ p=f'$. $\square$

No noetherian or finiteness hypothesis on $T$ or $S$ was used, and the proof never assumed that
$\mathcal E$ is free: only the universal property of $\mathbf P_S(\mathcal E)$ entered, so the same
argument applies verbatim to any $X$ admitting a locally closed immersion into a projective bundle
attached to a quasi-coherent module.

Finally we pass from a single cover to a covering family, exactly as the étale gluing corollary
did for ideals. This is the form in which Chapter 11 uses the theorem.

**Morphism gluing corollary.** Let $X\to S$ be quasi-projective, or more generally affine over $S$,
and let $\{p_\alpha:T_\alpha\to T\}_{\alpha\in A}$ be a jointly surjective family of flat, locally
finitely presented morphisms of $S$-schemes — for instance an étale covering. Then:

1. two $S$-morphisms $f_1,f_2:T\to X$ with $f_1\circ p_\alpha=f_2\circ p_\alpha$ for all $\alpha$
   are equal;
2. if $S$-morphisms $f_\alpha:T_\alpha\to X$ are given whose restrictions to
   $T_\alpha\times_TT_\beta$ agree for all $\alpha,\beta$, then there is a unique $S$-morphism
   $f:T\to X$ with $f\circ p_\alpha=f_\alpha$ for every $\alpha$.

Equivalently, $T\mapsto\operatorname{Hom}_S(T,X)$ is a sheaf for the topology generated by the
covers of this chapter: existence of a morphism and equality of two morphisms are local for that
topology.

**Proof.** As in the étale gluing corollary, a flat locally finitely presented morphism is open, so
for each affine open $W\subseteq T$ one may choose finitely many affine opens
$W_1\subseteq T_{\alpha_1},\ldots,W_m\subseteq T_{\alpha_m}$ mapping into $W$ with images covering
$W$; then $T'_W=W_1\sqcup\cdots\sqcup W_m$ is affine and $p_W:T'_W\to W$ is a finite flat cover.

(1) Restricting $f_1,f_2$ to $W$ and composing with $p_W$ gives equal morphisms, since each $W_j$
is an open subscheme of some $T_\alpha$. The uniqueness lemma for morphisms gives $f_1|_W=f_2|_W$,
and the affine opens $W$ cover $T$.

(2) Fix $W$. The restriction $f'$ of the $f_{\alpha_j}$ to $T'_W$ satisfies the equalizer
condition: $T'_W\times_WT'_W$ is the disjoint union of the $W_j\times_WW_k$, each an open
subscheme of $T_{\alpha_j}\times_TT_{\alpha_k}$, where the hypothesis applies. The descent theorem
just proved — or, for $X$ affine over $S$, the affine-target lemma — produces a unique
$f_W:W\to X$ with $f_W\circ p_W=f'$.

We claim that $f_W$ is already compatible with every index, not only with the finitely many
$\alpha_j$ used to build $T'_W$: for each $\alpha$ one has $f_W\circ p_\alpha=f_\alpha$ on
$p_\alpha^{-1}(W)$. Put $Z=p_\alpha^{-1}(W)\times_WT'_W$. Its first projection to
$p_\alpha^{-1}(W)$ is a finite flat cover, being a base change of $p_W$, and by the definition of
the fiber product $p_\alpha\circ\mathrm{pr}_1=p_W\circ\mathrm{pr}_2$, so

$$
f_W\circ p_\alpha\circ\mathrm{pr}_1=f_W\circ p_W\circ\mathrm{pr}_2=f'\circ\mathrm{pr}_2 .
$$

On the part of $Z$ lying over $W_j$, which is $T_\alpha\times_TW_j$ and hence an open subscheme of
$T_\alpha\times_TT_{\alpha_j}$, the hypothesis of part 2 says that
$f'\circ\mathrm{pr}_2=f_{\alpha_j}\circ\mathrm{pr}_2$ agrees with $f_\alpha\circ\mathrm{pr}_1$.
Hence $f_W\circ p_\alpha$ and $f_\alpha$ agree after composition with the finite flat cover
$Z\to p_\alpha^{-1}(W)$, so they agree by the uniqueness lemma. This proves the claim.

Now let $W$ and $\widetilde W$ be two affine opens. Over $W\cap\widetilde W$ the morphisms $f_W$
and $f_{\widetilde W}$ both satisfy the property just proved, so they become equal after
composition with each member of the family $\{p_\alpha^{-1}(W\cap\widetilde W)\to
W\cap\widetilde W\}$, which is again jointly surjective, flat and locally finitely presented; by
part 1 they agree. The $f_W$ therefore glue to a morphism $f:T\to X$, and $f\circ p_\alpha=f_\alpha$
for every $\alpha$ because this holds over each $W$ and the $p_\alpha^{-1}(W)$ cover $T_\alpha$.
Uniqueness of $f$ is part 1. $\square$

## 11. Symmetric powers

### 11.1 Quotients by permutation

For an integer $d\geq0$, the $d$th power $X^d_S$ parametrizes ordered $d$-tuples. The symmetric group $\mathfrak S_d$ permutes the factors; forgetting order should produce the symmetric power. Quotients by finite groups exist comfortably for quasi-projective schemes.

Throughout this chapter, $S$ is locally noetherian and $X\to S$ is quasi-projective and finitely
presented unless a narrower hypothesis is stated.

**Finite quotient theorem.** Let $S$ be locally noetherian and let a finite group $G$ act on a quasi-projective finitely presented $S$-scheme $Y$. Then there is a categorical quotient

$$
q:Y\longrightarrow Y/G
$$

in $S$-schemes. The map $q$ is integral, finite and surjective. Formation of the quotient commutes with flat base change. It commutes with a particular nonflat base change only when the corresponding invariant algebras commute with that scalar extension.

For an invariant affine open $V=\operatorname{Spec}B$, take $\operatorname{Spec}B^G$. Every
$b\in B$ is integral over $B^G$, since it satisfies $\prod_{g\in G}(T-gb)$. The same finite
algebra generators for $B$ over the noetherian base generate it as a $B^G$-algebra, so integrality
makes $B$ finite over $B^G$; the Artin--Tate argument makes $B^G$ finitely generated over the
base. Quasi-projectivity supplies enough $G$-stable affine neighborhoods: choose an affine
neighborhood of an orbit in a projective embedding and intersect its finitely many translates.
The affine quotients glue because invariant localization agrees on invariant principal opens, and
the categorical property follows affine-locally.

Here is a scheme-theoretic proof of quasi-projectivity which avoids descent of a linearized line
bundle across the generally nonflat quotient. From a locally closed immersion
$Y\hookrightarrow\mathbf P_S(\mathcal E)$ form the product of its $G$-translates. This is a
$G$-equivariant locally closed immersion into a finite product of projective bundles, with $G$
permuting the factors. Its scheme-theoretic closure $\bar Y$ is projective and $G$-stable, and
$Y$ is a $G$-stable open in $\bar Y$. After a Segre--Veronese embedding, write
$\bar Y=\operatorname{Proj}_S R$ for a finite graded algebra with a degree-preserving $G$-action.
The invariant graded algebra $R^G$ is finite type: $R$ is integral and finite over $R^G$ by the
orbit polynomials and the Artin--Tate argument. Invariant standard opens cover $\operatorname{Proj}R$.
Indeed, around any orbit choose a homogeneous section nonzero at all its points; the product of
its translates is invariant and has invariant affine nonvanishing locus. On such an open,
degree-zero localization commutes with invariants, so its quotient is the corresponding standard
open of $\operatorname{Proj}R^G$. Hence

$$
\bar Y/G=\operatorname{Proj}_S R^G.
$$

A sufficiently divisible Veronese of $R^G$ is generated in degree one, proving that this quotient
is projective. The boundary $\bar Y\setminus Y$ is invariant and has closed image under the finite
quotient; its inverse image is the boundary because geometric fibers of a finite-group quotient
are orbits. Therefore $Y/G$ is the complementary open in $\bar Y/G$ and is quasi-projective.
This proof uses invariant graded algebras themselves, so it remains valid over nonreduced bases
and makes no stabilizer-character descent assertion.

In general, invariants do not commute with a nonflat scalar extension when the group order is not invertible. Permuting factors does not remove this obstruction in arbitrary dimension. Thus the quotient of an arbitrary quasi-projective $X$ is asserted here to commute with flat base change only. For smooth relative curves, the divisor interpretation below proves the stronger compatibility with every base change.

Define

$$
\operatorname{Sym}^d_S(X)=X^d_S/\mathfrak S_d.
$$

It is quasi-projective over $S$ when $X$ is. If $X$ is proper, it is proper: after every base
change, the image of a closed subset may be tested after pulling back along the finite surjection
$X^d\to\operatorname{Sym}^d(X)$, so universal closedness descends; separatedness and finite type
are already known. Consequently, if $X$ is projective, its symmetric power is both
quasi-projective and proper. Its locally closed immersion into a projective bundle is then proper,
hence closed, so $\operatorname{Sym}^d(X)$ is projective. This proves projectivity without hiding
an ample-descent assertion inside the phrase “finite image.” For $d=0$ it is $S$, and for $d=1$
it is $X$.

### 11.2 Sheaf quotients and orbit functors

The categorical quotient $\operatorname{Sym}^d(X)$ does not generally represent the presheaf

$$
T\longmapsto X(T)^d/\mathfrak S_d.
$$

A $T$-point of the quotient need not be represented by an ordered tuple over $T$. Even flatness of
the quotient map is not, by itself, enough to identify its fiber relation with the orbit relation.
A sufficient condition is that $X^d\to\operatorname{Sym}^d(X)$ be an fppf cover and that

$$
\coprod_{\sigma\in\mathfrak S_d}X^d
\longrightarrow
X^d\times_{\operatorname{Sym}^d(X)}X^d
$$

be an epimorphism as fppf sheaves. Then the symmetric power is the fppf sheafification of the
orbit presheaf. This condition holds on the free locus. For a general
higher-dimensional $X$, one should retain only the categorical universal property unless an
appropriate sheaf statement has been proved.

For example, a separable degree-$d$ closed point on a smooth curve defines a rational point of its symmetric power, although none of the geometric entries need be rational individually. After a finite separable extension the point splits into an ordered tuple; descent remembers the permutations of its conjugates.

On the open locus where all entries are pairwise distinct, the action is free. The quotient map is then finite étale of degree $d!$:

$$
\operatorname{Conf}_d(X)=
X^d\setminus\bigcup_{i\neq j}\Delta_{ij}
\longrightarrow
\operatorname{UConf}_d(X).
$$

The target classifies finite étale degree-$d$ subschemes of $X_T$ which split as disjoint sections after an étale cover. This is a genuine sheaf statement. It remains valid when $d!$ is not invertible because a free constant finite-group action gives a finite étale torsor.

### 11.3 Configuration spaces

Configuration space is the collision-free part of a symmetric power. If $X\to S$ is smooth of relative dimension $r$, then $\operatorname{Conf}_d(X)\to S$ is smooth of relative dimension $dr$, and so is its finite étale quotient $\operatorname{UConf}_d(X)$. A point is an unordered finite étale subscheme of rank $d$.

Assume $X\to S$ is separated and smooth, and $d\geq2$. The complement is the big diagonal. For
relative dimension one its components are effective Cartier divisors; in relative dimension
$r$, each pairwise diagonal is a regular immersion of codimension $r$, and its finite quotient
has the same codimension. Passing across it permits collisions and creates nonreduced divisors on a curve.

There is a canonical degree-$d$ finite étale family over $\operatorname{UConf}_d(X)$. Start with

$$
\coprod_{i=1}^d\Gamma_{\operatorname{pr}_i}
\subset X\times_S\operatorname{Conf}_d(X).
$$

The graphs are disjoint and the construction is equivariant, so it descends along the torsor. Its fiber is the underlying unordered configuration. This universal family is what arithmetic approximation uses: connectedness of a specialized fiber turns a zero-cycle into one closed point.

### 11.4 The universal divisor on a smooth curve

Let $C\to S$ be a smooth quasi-projective curve. On $C\times_SC^d$, add the $d$ graphs of the coordinate projections as Cartier divisors:

$$
\Delta^{\mathrm{ord}}_d
=\Gamma_1+\cdots+\Gamma_d.
$$

For $d=0$ this means the empty Cartier divisor on $C\times_SS$; all statements below then reduce
to the identity $\operatorname{Sym}^0(C)=S$. Assume $d>0$ in the local calculation.

It is invariant under $\mathfrak S_d$, but invariance alone is not a descent argument when $d!$
is not invertible. We construct common étale charts for the quotient and the divisor functor and
descend there, using the descent statements proved in Sections 10.5 and 10.6 and nothing else.

Let $\operatorname{Div}^d_{C/S}$ be the functor whose value on $T$ is the set of relative
effective Cartier divisors of degree $d$ on $C_T$; by the closing remarks of Section 10.5 it is a
sheaf for the covers used below, its separatedness being clause 1 of the ideal descent lemma and
its gluing the étale gluing corollary. Fix a geometric divisor
$D_0=\sum_jd_jx_j$. After an étale extension of the base, choose pairwise disjoint neighborhoods
$U_j$ of the $x_j$ and étale parameters $z_j:U_j\to\mathbf A^1_S$. Put

$$
A_j=\mathbf A^{d_j}_S=\operatorname{Spec}
\mathcal O_S[a_{j,1},\ldots,a_{j,d_j}]
$$

and let $E_j\subset\mathbf A^1_{A_j}$ be the universal monic divisor

$$
z^{d_j}-a_{j,1}z^{d_j-1}+\cdots+(-1)^{d_j}a_{j,d_j}=0. \tag{11.1}
$$

It is finite free over $A_j$, with basis $1,z,\ldots,z^{d_j-1}$. Define $L_j\to A_j$ to be the
functor of lifts of the map $E_j\to\mathbf A^1$ through $U_j\to\mathbf A^1$. This functor is
represented by the finite Weil restriction

$$
L_j=\operatorname{Res}_{E_j/A_j}
       (U_j\times_{\mathbf A^1}E_j). \tag{11.2}
$$

The required piece of Weil restriction is elementary: on affine charts, write the images of
finitely many algebra generators in the displayed basis of $E_j$ and impose the finitely many
multiplication relations. These affine schemes glue because maps into $U_j$ form a sheaf.
Moreover $L_j\to A_j$ is étale. For a square-zero extension $T_0\hookrightarrow T$, the induced
$E_{j,T_0}\hookrightarrow E_{j,T}$ is square-zero, and formal étaleness of $U_j\to\mathbf A^1$
gives a unique lift. Finite presentation of (11.2) converts this infinitesimal criterion into
étaleness.

The product $L=\prod_jL_j$ maps étale-locally onto the divisor functor. Indeed, a divisor near
$D_0$ has a unique open-and-closed decomposition of ranks $d_j$ in the disjoint $U_j$; after an
étale localization the idempotents of its special finite algebra lift. Nakayama makes
$1,z_j,\ldots,z_j^{d_j-1}$ a basis of each part, so its kernel is the unique monic polynomial
(11.1), and its embedding in $U_j$ is exactly the lift represented by (11.2). Conversely a lift
in (11.2) is a closed immersion because its composite with the separated étale map to
$\mathbf A^1$ is the monic closed immersion $E_j\hookrightarrow\mathbf A^1$; étale-locally its
equation is (11.1), so it is an effective Cartier divisor.

We next compare the same chart with the symmetric quotient without using the divisor functor.
The fundamental theorem on symmetric polynomials gives

$$
\operatorname{Sym}^{d_j}(\mathbf A^1_S)
=\operatorname{Spec}\mathcal O_S[t_1,\ldots,t_{d_j}]^{\mathfrak S_{d_j}}
\simeq A_j, \tag{11.3}
$$

with coordinates the elementary symmetric functions, over $\mathbf Z$ and hence in every
residue characteristic. The following étale symmetric-chart lemma supplies the comparison:
near the cycle $d_jx_j$, the morphism

$$
\operatorname{Sym}^{d_j}(U_j)\longrightarrow
\operatorname{Sym}^{d_j}(\mathbf A^1_S)=A_j \tag{11.4}
$$

is represented, after an étale localization at that cycle, by $L_j\to A_j$.

Here is a proof that includes collisions. Pass to strict henselizations at $x_j$ and $z_j(x_j)$.
An étale morphism identifies their completed local rings. On ordered $d_j$-fold powers this gives
an equivariant identification of completed local rings at the repeated tuple. Taking invariants
still gives an identification: for every ring $R$,

$$
R[[u_1,\ldots,u_{d_j}]]^{\mathfrak S_{d_j}}
=R[[e_1,\ldots,e_{d_j}]], \tag{11.5}
$$

because degreewise the fundamental theorem on symmetric polynomials is integral and taking the
inverse limit over total degree preserves the equalizer defining invariants. Formula (11.5), not
averaging by $d_j!$, identifies the completed strict local quotient with the completed coefficient
space. The chosen branch is precisely a lift of the universal finite algebra through $U_j$, so
its completed local functor is (11.2). Since both sides are finitely presented and formally
étale over $A_j$, equality of their strict local functors yields isomorphic étale neighborhoods.
This proves the symmetric-chart lemma in arbitrary characteristic.

Taking products over $j$ and restricting to the open where the groups of support points remain
disjoint gives common representable étale charts $L$ for
$\operatorname{Sym}^d(C)$ and $\operatorname{Div}^d_{C/S}$. On each chart the monic equations
(11.1) define an effective Cartier divisor $D_L\subset C\times_SL$, finite locally free of degree
$d$ over $L$: its ideal is generated by the single monic polynomial in each factor, and a monic
polynomial is a non-zero-divisor.

It remains to see that these chartwise divisors are the restrictions of one divisor on
$C\times_S\operatorname{Sym}^d_S(C)$. This is precisely where a descent statement is needed, and the
one proved in Section 10.5 is enough. On a double overlap $L\times_{\operatorname{Sym}^d(C)}L'$ the
two divisors become equal after pulling back along the surjective étale map which orders the roots
of the two monic equations, since there both are the sum of the graphs of the ordered roots; by
clause 1 of the ideal descent lemma of Section 10.5 — applied to the finite flat cover obtained
from that surjection, multiplied by $C$ as in the first supplement there — they are therefore
already equal on the overlap itself. The charts $L$ form an étale covering of
$\operatorname{Sym}^d_S(C)$, so multiplying by $C$ gives an étale covering of
$C\times_S\operatorname{Sym}^d_S(C)$, and the étale gluing corollary of Section 10.5 produces a
unique invertible ideal there, that is, a unique effective Cartier divisor

$$
\Delta_d\subset C\times_S\operatorname{Sym}^d_S(C),
$$

restricting to $D_L$ on every chart. It is finite locally free of degree $d$ over
$\operatorname{Sym}^d_S(C)$ by clause 4 of the ideal descent lemma: over a Zariski open of
$\operatorname{Sym}^d_S(C)$ the gluing corollary was applied to one finite flat cover assembled
from finitely many affine opens of the charts, the projection
$C\times_S\operatorname{Sym}^d_S(C)\to\operatorname{Sym}^d_S(C)$ is quasi-compact and separated
because $C\to S$ is quasi-projective, and upstairs the divisor is finite locally free of degree $d$
by the previous paragraph. This construction proves, rather than assumes, descent of the
ordered divisor: no group-averaging and no unproved effective-descent principle enters, only the
faithfully flat descent of modules and of invertible ideals established in Section 10.5.

**Universal-divisor theorem.** For every $T\to S$, pullback of $\Delta_d$ induces a natural bijection

$$
\operatorname{Hom}_S(T,\operatorname{Sym}^d_S(C))
\simeq
\{\text{relative effective Cartier divisors of degree }d
\text{ on }C_T\}.
$$

Write $Y=\operatorname{Sym}^d_S(C)$ and let

$$
\Phi_T:\operatorname{Hom}_S(T,Y)\longrightarrow\operatorname{Div}^d_{C/S}(T),
\qquad
u\longmapsto(\mathrm{id}_C\times u)^*\Delta_d ,
$$

be the indicated map. It is well defined: $\Delta_d$ is finite locally free of degree $d$ over $Y$,
so its pullback is a closed subscheme of $C_T$ finite locally free of degree $d$ over $T$, hence a
relative effective Cartier divisor of degree $d$ by Section 10.3. It is visibly natural in $T$.
Both sides are sheaves for étale coverings: the left-hand side by the morphism gluing corollary of
Section 10.6, applicable because $Y$ is quasi-projective over $S$ (Section 11.1, $C$ being
quasi-projective); the right-hand side by the closing remarks of Section 10.5. The charts supply
the two remaining inputs. First, every divisor becomes a chart divisor after an étale covering: for
$D\in\operatorname{Div}^d_{C/S}(T)$ there are an étale covering $\{T_\alpha\to T\}$ and morphisms
$v_\alpha:T_\alpha\to L^{(\alpha)}$ into charts with $(\mathrm{id}_C\times v_\alpha)^*D_{L^{(\alpha)}}
=D|_{T_\alpha}$; this is the étale-local surjectivity of $L=\prod_jL_j$ onto the divisor functor
established above, the decomposition into the disjoint neighborhoods $U_j$ being unique. Second,
the charts are common charts for the two functors: under the identification furnished by the
symmetric-chart lemma, a $T_0$-point of a chart is the same datum as a divisor of the corresponding
type, so two chart points $v:T_0\to L$ and $v':T_0\to L'$ satisfy
$(\mathrm{id}_C\times v)^*D_L=(\mathrm{id}_C\times v')^*D_{L'}$ if and only if their images in $Y$
coincide. The "if" half is the statement that $\Delta_d$ restricts to $D_L$ on every chart.

Granting these, descent finishes the proof. _Surjectivity._ Given $D$, choose the covering and the
$v_\alpha$ of the first input and put $u_\alpha=\pi_\alpha\circ v_\alpha:T_\alpha\to Y$, where
$\pi_\alpha:L^{(\alpha)}\to Y$ is the chart map; then $\Phi_{T_\alpha}(u_\alpha)=D|_{T_\alpha}$. On
$T_\alpha\times_TT_\beta$ the two restrictions of $u_\alpha$ and $u_\beta$ are again chart points,
and they induce the same divisor, namely the restriction of $D$; by the second input they agree.
The morphism gluing corollary produces a unique $u:T\to Y$ restricting to $u_\alpha$ on each
$T_\alpha$, and $\Phi_T(u)$ restricts to $D|_{T_\alpha}$ for every $\alpha$ by naturality, hence
equals $D$ because the divisor functor is separated for these coverings — clause 1 of the ideal
descent lemma. _Injectivity._ Let $u_1,u_2:T\to Y$ have $\Phi_T(u_1)=\Phi_T(u_2)$. Since the charts
form an étale covering of $Y$, the base changes $T\times_{u_i,Y}L^{(\alpha)}$ form an étale
covering of $T$ for each $i$, and the fiber products of one such covering with the other form an
étale covering $\{T_\beta\to T\}$ over which both $u_1$ and $u_2$ lift to chart points. On each
$T_\beta$ those two chart points induce the same divisor, so they have the same image in $Y$ by the
second input; that is, $u_1$ and $u_2$ agree on every $T_\beta$, whence $u_1=u_2$ by part 1 of the
morphism gluing corollary. Thus $\Phi_T$ is bijective.

Nothing in this argument is assumed: equality of two morphisms into $Y$ and the existence of a
morphism into $Y$ prescribed étale-locally are supplied by Section 10.6, whose proof rests on the
faithfully flat descent of invertible modules from Section 10.5 and on the universal property of a
projective bundle. The construction used finite locally free algebras, their Weil restrictions,
idempotents, and monic equations; all commute with arbitrary base change. The bijection therefore
holds for every test scheme, including nonaffine and nonreduced schemes, and is functorial in $T$.

### 11.5 Symmetric powers and base change

For a smooth quasi-projective curve $C/S$ and every $T\to S$, the universal property yields

$$
\operatorname{Sym}^d_S(C)\times_S T
\simeq\operatorname{Sym}^d_T(C_T).
$$

Addition of divisors gives morphisms

$$
\operatorname{Sym}^d(C)\times_S\operatorname{Sym}^e(C)
\longrightarrow\operatorname{Sym}^{d+e}(C),
$$

which are associative, commutative, and compatible with base change. The disjoint union over
$d\geq0$ is thus a graded commutative monoid scheme. If $S$ is nonempty and $C/S$ has nonempty
geometric fibers, infinitely many components are nonempty; the union is then not quasi-compact
and hence not of finite type, although each component is locally of finite type.

For a nonsmooth curve, $\operatorname{Sym}^d(C)$ still exists if $C$ is quasi-projective. On
geometric points it records effective zero-cycles of degree $d$, rather than all finite flat
embedded subschemes; no general relative cycle functor is asserted here. There may be no universal closed subscheme on $C\times\operatorname{Sym}^d(C)$. At a singularity several nonisomorphic embedded length-$d$ structures can have the same cycle. The Hilbert scheme retains these structures; the symmetric power forgets them.

## 12. The Hilbert functors needed here

### 12.1 Precise functors

Fix a noetherian scheme $S$, a projective finitely presented morphism $X\to S$, and a relatively very ample $\mathcal O_X(1)$. For a numerical polynomial $P\in\mathbf Q[t]$, define the contravariant functor

$$
\operatorname{Hilb}^P_{X/S}:(\operatorname{Sch}/S)^{\mathrm{op}}\to\operatorname{Sets}
$$

by letting $\operatorname{Hilb}^P_{X/S}(T)$ be the set of closed subschemes $Z\subseteq X_T$ such that:

- $Z\to T$ is flat and of finite presentation;
- for every geometric point $\bar t\to T$, the Hilbert polynomial of $Z_{\bar t}$ with respect to $\mathcal O_X(1)$ is $P$.

Pullback is scheme-theoretic inverse image. Flatness ensures that the inverse image remains a family with the same polynomial. Because a closed immersion has no nontrivial automorphisms over its ambient scheme, this is a functor of sets, not a category fibered in groupoids.

For $P=d$ constant, write $\operatorname{Hilb}^d_{X/S}$. Its objects are exactly closed subschemes finite locally free of rank $d$ over $T$. For $d>0$, a projective flat finitely presented family with constant polynomial $d$ has zero-dimensional fibers and is finite, and the constant fiber length is its rank. For $d=0$, the zero Hilbert polynomial forces every fiber, and hence the flat family, to be empty, giving rank zero. Conversely finite locally free rank $d$ has polynomial $d$.

The Hilbert functor does not classify quotients of arbitrary sheaves. It records closed subschemes through quotients $\mathcal O_{X_T}\twoheadrightarrow\mathcal O_Z$ whose kernels are ideals. That multiplicative ideal condition is the narrow feature used here.

### 12.2 The Grassmannian construction

We first construct the parameter space used in the argument.

**Grassmannian lemma.** If $\mathcal V$ is finite locally free of rank $N$ on $S$, the functor of
locally free rank-$q$ quotients

$$
\mathcal V_T\twoheadrightarrow\mathcal Q
$$

is represented by a projective finitely presented scheme
$\operatorname{Gr}(q,\mathcal V)\to S$, carrying a universal quotient.

Locally trivialize $\mathcal V$. A quotient matrix has some invertible $q\times q$ minor.
On the chart where the minor indexed by $I$ is invertible, row operations put the matrix in the
form

$$
\begin{pmatrix}1_q&M\end{pmatrix},
$$

so the chart is affine space of dimension $q(N-q)$ and carries an evident universal quotient.
On overlaps, changing the invertible minor gives the usual matrix-fraction transition; these
transitions satisfy the cocycle identity and glue the charts. Taking the top exterior power of a
quotient gives a line quotient

$$
\bigwedge^q\mathcal V_T\twoheadrightarrow\det\mathcal Q
$$

and hence a morphism to $\mathbf P_S(\bigwedge^q\mathcal V)$. On every chart its coordinates are
the maximal minors. The quadratic Plücker relations say exactly that these coordinates are
decomposable; conversely, where one Plücker coordinate is invertible they recover the matrix
$M$. Thus the glued Grassmannian is the closed subscheme cut out by the Plücker relations.
It is projective and finitely presented, and the chart calculation proves its universal property
over arbitrary test schemes, including those with nilpotents.

Work first over an affine open on which $X\subseteq\mathbf P^r_S$. Put

$$
V_n=H^0(\mathbf P^r_S,\mathcal O(n)),
\qquad N_n=\operatorname{rank}V_n=\binom{n+r}{r}.
$$

For a family $Z$ with polynomial $P$ and $n$ beyond its regularity bound, vanishing and base
change give a quotient of finite locally free modules

$$
V_n\otimes_{\mathcal O_S}\mathcal O_T
\twoheadrightarrow p_*\mathcal O_Z(n),
$$

whose target has rank $P(n)$. It defines a morphism from $T$ to the Grassmannian

$$
G_n=\operatorname{Gr}\!\left(P(n),V_n\right).
$$

One degree alone remembers only a module quotient, not an ideal. Multiplication must be
compatible. The passage from finitely many such compatibility equations to a flat graded quotient
in every degree is the difficult point. In particular, constant dimensions on geometric fibers do
not imply local freeness over a nonreduced base. We therefore prove the exact bounded theorem before
constructing the incidence scheme; a fiberwise Macaulay calculation will not be substituted for
this relative assertion.

### 12.3 Representability with fixed polynomial

The required boundedness is proved next. Its relative part is included because geometric-fiber
calculations alone do not control nilpotent test schemes.

**Theorem 12.A (bounded Macaulay--Gotzmann package).** Fix $r$ and a numerical
polynomial $P$ that occurs as the Hilbert polynomial of a closed subscheme of $\mathbf P^r$.

1. **Compression and equality over fields.** For $n\geq1$, every nonnegative integer $h$ has a
   unique Macaulay expansion (the expansion of $0$ is empty)

   $$
   h=\binom{b_n}{n}+\binom{b_{n-1}}{n-1}+\cdots+\binom{b_j}{j},
   \qquad b_n>b_{n-1}>\cdots>b_j\geq j.
   $$

   Put

   $$
   h^{\langle n\rangle}
   =\binom{b_n+1}{n+1}+\cdots+\binom{b_j+1}{j+1}.
   $$

   Every standard graded quotient $R$ over a field satisfies
   $h_R(n+1)\leq h_R(n)^{\langle n\rangle}$. If equality holds and the defining ideal is
   generated in degrees at most $n$, equality persists in every later degree.

2. **Gotzmann expansion and regularity.** There is a unique expansion

   $$
   P(n)=
   \binom{n+a_1}{a_1}
   +\binom{n+a_2-1}{a_2}
   +\cdots+
   \binom{n+a_s-(s-1)}{a_s}, \tag{12.1}
   $$

   with $r\geq a_1\geq\cdots\geq a_s\geq0$. The zero polynomial has the empty
   expansion and $s=0$. If $I\subset k[x_0,\ldots,x_r]$ is saturated and $W/I$ has
   polynomial $P$, then the associated ideal sheaf is $s$-regular. Moreover

   $$
   H_{W/I}(n)=P(n),\qquad I_{n+1}=W_1I_n\quad(n\geq s), \tag{12.2}
   $$

   and $I$ is generated in degrees at most $s$. In particular
   $P(n+1)=P(n)^{\langle n\rangle}$ for $n\geq\max(s,1)$. (When $P=0$, the
   assertion at degree $0$ is instead the trivial equality $I_1=W_1I_0$.)

3. **Relative persistence and recovery.** Let $A$ be any ring, let
   $W=A[x_0,\ldots,x_r]$, and take $m\geq s$. Suppose
   $K_m\subset W_m$ and $K_{m+1}\subset W_{m+1}$ are locally direct summands of coranks
   $P(m)$ and $P(m+1)$ and

   $$
   W_1K_m\subseteq K_{m+1}. \tag{12.3}
   $$

   Then (12.3) is an equality. If $J$ is the ideal generated by $K_m$, then
   $W_n/J_n$ is finite locally free of rank $P(n)$ for every $n\geq m$, and these quotients
   commute with every ring map $A\to A'$. The sheaf associated to $W/J$ is finitely
   presented and flat over $A$.

   Conversely, if $Z\subset\mathbf P^r_A$ is finitely presented and flat over $A$ and all
   its geometric fibers have polynomial $P$, then for $n\geq m$ the module
   $p_*\mathcal O_Z(n)$ is finite locally free of rank $P(n)$ and commutes with arbitrary
   base change. The kernels of $W_n\to p_*\mathcal O_Z(n)$ satisfy (12.3), and the ideal
   sheaf of $Z$ is recovered from any one of its pieces in degree $m$. These statements are
   local on an arbitrary base scheme; no noetherian or reduced hypothesis on that base is
   required.

**Proof of Theorem 12.A.** Let $\mathcal M_n$ denote the degree-$n$ monomials and, for
$A\subseteq\mathcal M_n$, define the upper shadow

$$
\operatorname{Sh}(A)=\{x_i u:0\leq i\leq r, u\in A\}. \tag{12.4}
$$

The relevant combinatorial statement is the following precise form of compression.

**Macaulay--Gotzmann shadow lemma.** If
$|\mathcal M_n\setminus A|=h$, then

$$
|\mathcal M_{n+1}\setminus\operatorname{Sh}(A)|
\leq h^{\langle n\rangle}. \tag{12.5}
$$

If equality holds, then every iterated shadow has the corresponding extremal complement:

$$
|\mathcal M_{n+q}\setminus\operatorname{Sh}^{q}(A)|
=h^{\langle n,q\rangle}\qquad(q\geq1), \tag{12.6}
$$

where the right side means successive Macaulay transforms in degrees
$n,n+1,\ldots,n+q-1$.

The corresponding vector-space statement includes cancellation: if
$V\subset k[x_0,\ldots,x_r]_n$ has codimension $h$ and
$k[x]_1V$ has codimension $h^{\langle n\rangle}$, then the ideal generated by $V$ has
the ranks prescribed by (12.6) in every later degree.

Here is the complete induction used below. Greedily choose $b_n$ maximal with
$\binom{b_n}{n}\leq h$, subtract, and continue with lower denominators. Pascal's inequality
$\binom c{i}<\binom{c+1}{i+1}$ shows at each step that the next upper entry is smaller than the
preceding one; reversing the first place where two expansions differ proves uniqueness.

Order degree-$n$ monomials by colexicographic order and replace the complement of $A$ by the
initial colex segment $C(h,n)$. To see directly that this cannot increase the complement of the
shadow, slice by the exponent of $x_r$. If the slice complements have sizes
$h_0,h_1,\ldots$, replace each by $C(h_q,n-q)$ and then replace adjacent slices whenever they
are not nested. For adjacent sizes $u,v$, Pascal's identity gives

$$
|\partial C(u,n-q)|+|C(v,n-q-1)|
\geq |\partial C(u',n-q)|+|C(v',n-q-1)|, \tag{12.5a}
$$

where $(u',v')$ is obtained by moving the largest available binomial block from the second
slice to the first. The total size is unchanged and the pair becomes lexicographically larger,
so the process terminates. Inequality (12.5a) is just
$\binom c i+\binom c{i-1}=\binom{c+1}i$ for the moved block; induction on the number of blocks
handles a general pair. Induction on $(r,n)$ now leaves the nested colex slices of $C(h,n)$.
If $h=\sum\binom{b_i}i$, Pascal's identity counts their shadow complement as

$$
|\mathcal M_{n+1}\setminus\operatorname{Sh}(C(h,n))|
=\sum_{i=j}^n\binom{b_i+1}{i+1}.
$$

This proves (12.5). Equality in (12.5a) says that no block move was strict. The resulting nested
slices remain nested after taking a shadow, so the identical argument applies in the next degree.
Induction proves (12.6), including every equality case, not only the colex segment.

We also record the syzygy information carried by equality. Give each monomial in
$\operatorname{Sh}(A)$ the least pair $(x_i,u)$ with $u\in A$ and $x_iu$ equal to that
monomial. A non-owner product $x_ju$ has the same monomial as its owner and gives a linear
overlap $x_je_u-x_ie_v$. In the nested-slice induction above, removing the last binomial block
removes one generator together with precisely its owner multiples. Induction therefore shows
that these linear overlaps generate the kernel of

$$
\bigoplus_{u\in A}k[x](-n)e_u\longrightarrow (A), \qquad e_u\mapsto u. \tag{12.5b}
$$

and that the same owner construction resolves the next kernel. Thus the monomial ideal $(A)$
has an $n$-linear resolution whenever equality holds.

For the vector-space assertion, row-reduce a basis $f_u$ of $V$ so that its leading monomials
are $A$. We always have
$\operatorname{Sh}(A)\subseteq\operatorname{in}(k[x]_1V)$. Equality of codimensions and
(12.5) force equality here. Hence every linear overlap from (12.5b) reduces to zero using the
$f_u$: a nonzero remainder would contribute an additional leading monomial and make the
codimension smaller. Since those overlaps generate the first syzygy module, the monic
Buchberger criterion applies. Explicitly, if a relation among the $f_u$ had a largest uncancelled
term, the corresponding relation among their leading monomials is a combination of the linear
overlaps; subtracting the same combination of the lifted zero reductions lowers that largest
term, and well-ordering terminates. Therefore $\{f_u\}$ is a Gröbner basis of the ideal it
generates and its initial ideal is $(A)$. Formula (12.6) gives every later quotient dimension.
This proves the vector-space equality and persistence statements. Notice the
orientation: $A$ consists of **ideal** monomials. If $r=2,n=1,h=1$, the one standard
monomial may be $x_2$ and the next quotient value is $1$, although the ordinary shadow of
$\{x_2\}$ has three elements. It is the complement of the shadow of the other two, ideal
monomials that (12.5) counts.

Now let $I$ be homogeneous over a field and choose a term order. If $A$ is the set of leading
monomials of $I_n$, then

$$
\operatorname{Sh}(A)\subseteq\operatorname{in}(W_1I_n).
$$

Taking complements proves Macaulay's inequality. If growth is maximal and
$I_{n+1}=W_1I_n$, the vector-space equality statement applied to $I_n$ proves maximal growth
in every later degree. The generation hypothesis is essential: in
$k[x_0,x_1]/(x_0^{n+2})$ growth from degrees $n$ to $n+1$ is maximal, but a new relation in
degree $n+2$ stops persistence.

We next construct (12.1). Induct on the degree of $P$. A general non-zero-divisor hyperplane
on a saturated quotient has Hilbert polynomial $\Delta P(n)=P(n)-P(n-1)$. By induction write
$\Delta P$ in Gotzmann form. Replacing every lower entry $b_i$ in that form by $b_i+1$
integrates it, by Pascal's identity. The difference from $P$ is constant; Macaulay's inequality
in large degree says that this constant is nonnegative, so append that many terms with lower
entry $0$. The constant-polynomial case starts the induction. Conversely, taking a finite
difference deletes the final zero entries and lowers every positive $a_i$ by one. This
recovers all positive entries inductively, and the remaining constant recovers the number of
zeros, proving uniqueness. A hyperplane section has dimension at most $r-1$, so $a_1\leq r$.
For $n\geq\max(s,1)$, symmetry of binomial coefficients rewrites the $i$th summand of (12.1) with
lower entry $n-i+1$. These lower entries are positive and the upper entries strictly decrease,
so this is the Macaulay expansion of $P(n)$. Raising both entries gives (12.1) at $n+1$;
hence

$$
P(n+1)=P(n)^{\langle n\rangle}\qquad(n\geq\max(s,1)). \tag{12.1a}
$$

We record the regularity step, where saturation is indispensable.

**Gotzmann saturation lemma.** Let $I$ be saturated over an infinite field, put $R=W/I$, and
choose a linear form $\ell$ that is a non-zero-divisor on $R$. Such a form exists: saturation
gives $H^0_{W_+}(R)=0$, so the irrelevant ideal is not associated to $R$, and a finite union of
the degree-one parts of the associated primes cannot fill $W_1$. Let $\bar I$ be the image of
$I$ in $W/(\ell)$ and let $J=\bar I^{\mathrm{sat}}$. If the hyperplane polynomial is the
finite difference of a Gotzmann expansion of length $s$ and $J$ is $s$-regular, then

$$
J_n=\bar I_n\quad(n\geq s),\qquad
H_R(n)=P(n)\quad(n\geq s-1), \tag{12.7}
$$

and the ideal sheaf associated to $I$ is $s$-regular. Here $s\geq1$; the empty
Gotzmann expansion is the separate trivial case $I=W$.

Indeed, $J/\bar I$ has finite length and

$$
0\longrightarrow R(-1)\xrightarrow{\ell}R
\longrightarrow (W/(\ell))/\bar I\longrightarrow0. \tag{12.8}
$$

Write $D_n=\dim(J/\bar I)_n$. Sequence (12.8) gives

$$
H_R(n)-H_R(n-1)=H_{(W/(\ell))/J}(n)+D_n. \tag{12.8a}
$$

For large $n$, $D_n=0$ and both Hilbert functions equal their polynomials. Descend on $n$.
Assume $H_R(n)=P(n)$ and $n>s$. Inductive regularity for $J$ gives
$H_{(W/(\ell))/J}(n)=\Delta P(n)$. Hence (12.8a) is the exact numerical identity

$$
H_R(n-1)=P(n-1)-D_n. \tag{12.8b}
$$

If $D_n>0$, Macaulay's inequality and strict monotonicity of the transform give

$$
P(n)=H_R(n)
\leq H_R(n-1)^{\langle n-1\rangle}
\leq(P(n-1)-1)^{\langle n-1\rangle}
<P(n-1)^{\langle n-1\rangle}=P(n),
$$

a contradiction. Strict monotonicity follows directly from the greedy expansion: subtracting
one changes its last nonzero binomial block, and after raising, that block remains strictly
smaller. Thus $D_n=0$ and (12.8b) gives $H_R(n-1)=P(n-1)$. This descends through every
$n>s$. At $n=s>1$, writing out the final block of the Gotzmann expansion gives

$$
(P(s-1)-1)^{\langle s-1\rangle}<P(s),
$$

because subtracting one deletes one terminal unit before the Macaulay raise. Hence positive
$D_s$ gives the same contradiction. When $s=1$, the single block has $P(0)=1$; a proper
standard graded quotient has $H_R(0)=1$, so (12.8b) gives the endpoint directly. Thus
$D_n=0$ for $n\geq s$ and the descent also gives $H_R(s-1)=P(s-1)$, proving (12.7).
For clarity, we include the hyperplane regularity argument. Since $I\cap(\ell)=\ell I$, there is
an exact sequence

$$
0\longrightarrow\mathcal I(n-1)\xrightarrow{\ell}\mathcal I(n)
\longrightarrow\widetilde{\bar I}(n)\longrightarrow0 \tag{12.9}
$$

and its long cohomology sequence (Book 7b, Corollary 4.4); sheafifying $\bar I$ or its saturation $J$ gives the same
hyperplane ideal sheaf. Starting with the Serre vanishing theorem of Section 6.2 in a large twist and descending the twist
in this sequence, the $s$-regularity of $\widetilde J$ gives
$H^i(\mathcal I(s-i))=0$ for $i\geq2$. For $i=1$, the exact sequence

$$
0\to H^0(\mathcal I(s-1))\to W_{s-1}
\to H^0(\mathcal O_{\operatorname{Proj}R}(s-1))
\to H^1(\mathcal I(s-1))\to0
$$

shows what remains. The already established regularity of the hyperplane section kills its
higher cohomology in this twist, so repeated use of (12.8) computes the Euler characteristic of
$\mathcal O_{\operatorname{Proj}R}(s-1)$ as $P(s-1)$. Saturation identifies
$R_{s-1}$ with the image of $W_{s-1}$ in these global sections. Since
$H_R(s-1)=P(s-1)$, source image and target have equal dimension; the displayed map is
surjective and $H^1(\mathcal I(s-1))=0$. Thus $\mathcal I$ is $s$-regular.

Apply the lemma inductively to the finite difference of (12.1). Its Gotzmann length is at
most $s$, so the saturated hyperplane ideal is $s$-regular, and the lemma makes $I$
$s$-regular. Section 6.4 and saturation then give (12.2), while the shadow lemma gives the
displayed Macaulay equality for $P$. Over a finite field, make a purely transcendental field
extension to choose $\ell$ and descend dimensions and cohomology by faithful flatness; the
cohomological half of that step is flat base change, $H^i(X,\mathcal F)\otimes_kK\simeq
H^i(X_K,\mathcal F_K)$ for a field extension $K/k$ (Book 7b, Theorem 5.3). This
proves clauses 1 and 2 over every field.

It remains to prove the relative assertion without discarding nilpotents. If $P=0$ and
$m=0$, then $K_0=W_0$, the generated ideal is $W$, and every assertion is immediate. We
may therefore assume $m\geq1$. For $m\geq s$ define
the truncated Hilbert function

$$
h_m(n)=
\begin{cases}
\binom{n+r}{r},&n<m,\\
P(n),&n\geq m.
\end{cases} \tag{12.10}
$$

Field persistence says that an ideal with this function is generated in degree $m$ and is
determined by degrees $m$ and $m+1$. Its saturation has polynomial $P$ and, by (12.2), the
same degree-$m$ piece. It is therefore the degree-$m$ truncation of an $m$-regular saturated
ideal. In particular, every **monomial** ideal generated in degree $m$ with this function has
an $m$-linear resolution; its monomial syzygies are generated by the overlaps in degree
$m+1$. These facts give the following integral version.

**Finite-support lemma.** For every ring $C$, restriction to degrees $m,m+1$ is a bijection
between

- homogeneous ideals $L\subset C[x_0,\ldots,x_r]$ for which every graded quotient is locally
  free of rank $h_m(n)$; and
- pairs of direct summands $L_m,L_{m+1}$ of the indicated coranks satisfying
  $C[x]_1L_m\subseteq L_{m+1}$.

The extension is the ideal generated by $L_m$, and the bijection commutes with every map
$C\to C'$.

We use a filtered monic form of Buchberger's criterion. It is stated over a noetherian local ring
because that is where the universal incidence scheme is checked; the resulting universal
isomorphism will then be base-changed to arbitrary rings.

**Filtered marked-basis lemma.** Let $(R,\mathfrak m)$ be noetherian local, let $f_u$ be
degree-$m$ rows which reduce modulo $\mathfrak m$ to a row-echelon basis with leading monomials
$A$, and suppose the monomial ideal $M_0=(A)$ has an $m$-linear resolution. If the quotient in
degrees $m$ and $m+1$ is free on the standard monomials, then it is free on the standard
monomials in every degree.

Proof proceeds modulo $\mathfrak m^q$. For $q=1$, the equality-case proof above says that the
linear overlaps generate all syzygies and reduce to zero. Suppose confluence and independence
hold modulo $\mathfrak m^q$. An ambiguity modulo $\mathfrak m^{q+1}$ has leading coefficient in
$\mathfrak m^q/\mathfrak m^{q+1}$, a vector space over the residue field. Express its leading
relation in the linear overlap generators of the $m$-linear resolution. The corresponding lifted
overlaps vanish in the free degree-$(m+1)$ quotient; multiplying them resolves the ambiguity and
lowers the leading monomial. Induction on the monomial order gives confluence modulo
$\mathfrak m^{q+1}$. Thus a relation among standard monomials has every coefficient in
$\mathfrak m^q$ for every $q$. Each fixed graded quotient is a finite $R$-module, and Krull
intersection gives $\bigcap_q\mathfrak m^q=0$, proving independence. Generation follows in each
degree from generation modulo $\mathfrak m$ and Nakayama. This proves the lemma. This filtered
argument is precisely what retains infinitesimal coefficients in nonpivot columns; deleting them
would prove only the reduced statement.

Now represent the pairs in the second bullet over $\mathbf Z$ by the closed incidence subscheme
of the two Grassmannians. Work in a noetherian local ring $(R,\mathfrak m)$ of one of its affine
charts. Row-reduce the universal $L_m$ modulo $\mathfrak m$ and lift the rows; their leading
monomials form a set $A$.
Over the residue field $k$, the actual quotient in degree $m+1$ has dimension $P(m+1)$.
Since

$$
\operatorname{Sh}(A)\subseteq
\operatorname{in}(k[x]_1(L_m\otimes k)),
$$

the shadow inequality and $P(m+1)=P(m)^{\langle m\rangle}$ squeeze both complements to the
same size. Thus the monomial ideal $M_0=(A)$ has Hilbert function $h_m$ and, by the equality
part proved above, an $m$-linear resolution whose first syzygies are the linear overlaps.

The cokernel of the finite map $R[x]_1L_m\to L_{m+1}$ vanishes modulo $\mathfrak m$, hence
vanishes by Nakayama. Therefore $R[x]_1L_m=L_{m+1}$. The standard degree-$(m+1)$ monomials
generate its Grassmannian quotient. Their number is $P(m+1)$, so the resulting surjection between
finite free $R$-modules of the same rank is an isomorphism. Every generating linear overlap of
the lifted rows consequently vanishes in that quotient. The filtered marked-basis lemma shows
that every later quotient is free on the standard monomials, with rank $h_m(n)$. Hence every
local ring of the universal incidence scheme already satisfies every later Fitting condition,
including its nilpotent structure. The universal ideal is uniquely generated by $L_m$.

We have therefore proved over $\mathbf Z$ that the incidence scheme itself represents the full
ideals in the first bullet. Base-changing this scheme-theoretic isomorphism proves the statement
for an arbitrary, even nonnoetherian, ring $C$ and makes compatibility with every $C\to C'$
automatic. Conversely, an ideal with the stated locally free quotients supplies the two direct
summands and the incidence relation. This completes the proof of the finite-support lemma without
passing to radicals and without assuming the test ring is reduced or noetherian.

Apply the finite-support lemma to (12.3). It gives all the asserted locally free quotients and
their arbitrary base change. On a standard projective chart, the degree-zero localization is a
filtered colimit of these flat modules, hence is $A$-flat. Finite degree-$m$ generators make
the associated closed subscheme finitely presented.

Conversely, let $Z$ be a flat family. Its ideal sheaf is also flat, because both
$\mathcal O_{\mathbf P^r_A}$ and $\mathcal O_Z$ are flat over $A$. Every geometric fiber is
$s$-regular by clause 2. The relative cohomology-and-base-change argument of Section 6.3 applied to this
uniform fiberwise regularity gives, for $n\geq m$, locally free pushforwards of ranks $P(n)$,
arbitrary base change, and surjective multiplication in the ideal pieces. This argument uses
only the finite Čech model (Book 7b, Theorem 4.2) and the local flatness criterion, so it remains valid over an
arbitrary base ring. The finite-support lemma then recovers the whole high-degree ideal from
degree $m$. Sheafification forgets only bounded irrelevant torsion, so equality in all high
degrees recovers the original ideal sheaf. This proves clause 3. $\square$

The dual-number test shows why the integral step is necessary. Over
$C=k[\epsilon]/(\epsilon^2)$, the degree-one relations $x-\epsilon z,y$ define a flat point of
$\mathbf P^2_C$ and force the degree-two relation $xz-\epsilon z^2$. Replacing it by $xz$
gives the right dimensions on the sole geometric fiber but leaves the nonzero incidence
remainder $-\epsilon z^2$. The closed incidence equations reject this pair; a calculation on
geometric points would not.

We can now apply Theorem 12.A to the finite construction. Put
$G_i=\operatorname{Gr}(P(i),V_i)$ for $i=m,m+1$. On $G_m\times_SG_{m+1}$ write

$$
0\longrightarrow\mathcal K_i
\longrightarrow V_i\otimes\mathcal O
\longrightarrow\mathcal Q_i\longrightarrow0.
$$

The zero locus of

$$
\mathcal K_m\otimes V_1\longrightarrow
V_{m+1}\otimes\mathcal O\longrightarrow\mathcal Q_{m+1}
$$

is a closed finitely presented incidence scheme $H_P$. The finite-support lemma identifies its
$T$-points, for every test scheme $T$ including nonreduced ones, with compatible homogeneous
ideals having quotient ranks $h_m(n)$ in all degrees. Thus this is scheme-theoretic persistence,
not an inference from the geometric points of $H_P$.

Let $J$ be the graded ideal generated by the universal $\mathcal K_m$. Clause 3 gives finite
locally free quotients $V_n/J_n$ of rank $P(n)$ for all $n\geq m$, compatible with arbitrary base
change. Sheafifying gives a finitely presented closed subscheme
$\mathcal Z\subset\mathbf P^r_{H_P}$ flat over $H_P$, with Hilbert polynomial $P$ on every
geometric fiber.

Conversely, clause 3 sends every flat finitely presented family
$Z\subset\mathbf P^r_T$ with polynomial $P$, for an arbitrary $S$-scheme $T$, to its degree-$m$
and degree-$(m+1)$ quotient bundles and hence to a unique map $T\to H_P$. The recovered ideal
sheaf equals the original one. Indeed, on $D_+(x_i)$ a degree-zero localized element is represented
by $f/x_i^d$; multiplying numerator and denominator by a sufficiently high power of $x_i$ moves
the comparison into a degree at least $m$. Thus agreement of the graded ideals in all high degrees
implies equality of their associated sheaves. The two constructions are inverse and functorial, so
$H_P$ represents the Hilbert functor of $\mathbf P^r_S$.

**Hilbert representability theorem.** Under the
hypotheses of Section 12.1 the functor $\operatorname{Hilb}^P_{X/S}$ is represented by a
projective finitely presented $S$-scheme

$$
\operatorname{Hilb}^P(X/S).
$$

The zero polynomial has the empty Gotzmann expansion and represents the unique empty subscheme,
so $\operatorname{Hilb}^0(X/S)=S$. If a nonzero $P$ has no Gotzmann expansion appropriate to
$\mathbf P^r$, no geometric fiber can occur and the representing scheme is empty. Otherwise use
the construction below.

Embed $X$ as a closed subscheme of a finite projective bundle
$\mathbf P_S(\mathcal E)$. Replace $V_n$ globally by $\operatorname{Sym}^n\mathcal E$ and use
the relative Grassmannians of its rank-$P(n)$ quotients. Multiplication and the incidence map
are intrinsic and recover the preceding construction wherever $\mathcal E$ is trivial. On the
finitely many open-and-closed rank strata of $\mathcal E$, Theorem 12.A supplies the same finite
construction, so the ambient Hilbert scheme is projective and finitely presented over $S$.

It remains to impose containment in $X$. Let $\mathcal I_X$ be its ideal in the projective
bundle and let $\mathcal Z$ be the universal family over the ambient incidence scheme $H_P$.
Containment is equivalent to vanishing of

$$
\mathcal I_X\longrightarrow\mathcal O_{\mathcal Z}. \tag{12.11}
$$

This is a closed condition with its full scheme structure. Indeed, after a sufficiently high
twist, the restriction of $\mathcal I_X$ to $\mathcal Z$ has a finite set of relative
generators, while $p_*\mathcal O_{\mathcal Z}(n)$ is locally free and commutes with arbitrary
base change. Adjunction turns the composites of those generators with (12.11) into a map from
a finite module to that locally free pushforward. Setting all its coefficients equal to zero
defines a closed subscheme of $H_P$. Pullback preserves the generating surjection and the
pushforward, so a test scheme factors through this closed subscheme exactly when (12.11)
vanishes after pullback. Thus containment is imposed on nilpotent test schemes, not just on
geometric fibers. The resulting closed subscheme of the product of relative Grassmannians is
the required projective finitely presented Hilbert scheme.

The universal property is

$$
\operatorname{Hom}_S(T,\operatorname{Hilb}^P(X/S))
\simeq\operatorname{Hilb}^P_{X/S}(T),
$$

naturally in every $S$-scheme $T$. The universal object is a closed subscheme

$$
\mathcal Z_P\subseteq
X\times_S\operatorname{Hilb}^P(X/S)
$$

flat and finitely presented over the second factor. The representing scheme is not the universal family; confusing these two schemes reverses their roles.

### 12.4 The finite-length Hilbert scheme

For $P=d$, representability gives
$\operatorname{Hilb}^d(X/S)$, projective over $S$ when $X$ is. Its universal family is finite
locally free of rank $d$. The construction is independent, up to unique isomorphism, of the
projective embedding because the functor itself mentions only length-$d$ closed subschemes.

If $X\to S$ is merely quasi-projective, choose an open immersion $X\subset\bar X$ with $\bar X$
projective. The locus in $\operatorname{Hilb}^d(\bar X/S)$ where the
universal finite family lies inside $X$ is open: its complement is the image of the intersection
with $\bar X\setminus X$, and that image is closed because the universal family is finite. This
open represents $\operatorname{Hilb}^d(X/S)$. It is quasi-projective and commutes with arbitrary
base change.

Within this Hilbert scheme, for a smooth morphism $X/S$ of relative dimension $r$,
the open locus of reduced geometric fibers is the unordered configuration space. When $r>1$,
the boundary contains many infinitesimal directions. Already
$\operatorname{Hilb}^2(\mathbf A^2)$ records a collision together with a tangent direction,
whereas $\operatorname{Sym}^2(\mathbf A^2)$ records only the doubled cycle. Thus the
Hilbert-to-cycle map is not generally an isomorphism in dimension two.

### 12.5 Curves: Hilbert scheme equals symmetric power

Let $C\to S$ be a smooth quasi-projective curve. Sections 10.3 and 11.4 identify, for every $T$,

$$
\operatorname{Hilb}^d_{C/S}(T)
=\{\text{relative effective divisors of degree }d\}
=\operatorname{Hom}_S(T,\operatorname{Sym}^d_S(C)).
$$

This gives a second, direct construction in the smooth-curve case: the explicitly constructed
symmetric power already represents the length-$d$ Hilbert functor.

By uniqueness of representing objects,

$$
\operatorname{Hilb}^d(C/S)\simeq\operatorname{Sym}^d_S(C).
$$

Under this isomorphism their universal families agree with $\Delta_d$. In particular the symmetric power is smooth over $S$ of relative dimension $d$. The divisor-chart lemma gives étale coordinates over the affine coefficient space with coordinates $a_1,\ldots,a_d$, even when roots collide; it does not require a global parameter on the curve.

For a singular curve, the subfunctor of length-$d$ subschemes supported in the smooth locus is
represented directly by the corresponding open of the symmetric power of the smooth locus. The
full Hilbert scheme agrees with that symmetric power on this open.
Over a singular point, several embedded ideals can have the same multiplicities, so the two
functors differ. No global Hilbert-to-cycle morphism for singular families is needed or asserted
here.

## 13. Universal constructions for later geometry

Theorem 12.A and Section 12.3 supply the Hilbert schemes and universal families used in this
chapter. The arguments below identify the indicated open and closed loci inside those bounded
parameter schemes.

### 13.1 Graphs and spaces of morphisms

If $Y\to S$ is separated, a morphism $u:X_T\to Y_T$ has a closed graph

$$
\Gamma_u\subseteq X_T\times_TY_T.
$$

Suppose $X\to S$ is projective flat and finitely presented and $Y\to S$ is projective. Fix a
Hilbert polynomial $P$ for graphs in a chosen projective embedding of $X\times_SY$. The Hilbert
scheme of that product represents all flat closed families with polynomial
$P$. Write $H$ for this Hilbert scheme. For its universal family $\Gamma$, consider the proper finitely presented
projection
$p:\Gamma\to X\times_S H$.

The locus in the parameter base where $p$ is an isomorphism is open. Indeed, near a parameter
where $p$ is an isomorphism on the fiber, upper semicontinuity of fiber dimension removes the
closed non-quasi-finite locus. The resulting proper quasi-finite morphism is finite. Both
$\Gamma$ and $X\times_S H$ are flat over $H$, so the fiberwise isomorphism criterion for a finite
finitely presented morphism, obtained from the local flatness criterion and Nakayama's lemma
applied to

$$
\mathcal O_{X\times_S H}\longrightarrow p_*\mathcal O_\Gamma.
$$

shows that $p$ is an isomorphism over a neighborhood of that fiber. Equivalently, the non-isomorphism
locus is closed in $X\times_S H$; its image in $H$ is closed because $X$ is proper. Removing that
image makes the algebra map, hence $p$, an isomorphism. Conversely an isomorphism is a graph, and composing its
inverse with $\Gamma\hookrightarrow (X\times_S Y)\times_S H$ gives the unique family of morphisms
$X\times_S H\to Y\times_S H$. Thus this open
subscheme represents morphisms whose graphs have polynomial $P$.

This construction is used only with bounded graph polynomials. There is no single finite-type scheme of all morphisms of arbitrary degree. Fixing degree or Hilbert polynomial is the finiteness datum that makes a parameter space possible.

### 13.2 Closed loci inside parameter spaces

Many moduli conditions become closed conditions on the resulting Hilbert
schemes, provided the displayed properness and finite-presentation hypotheses are retained:

- containment in a fixed closed subscheme is closed;
- invariance under a fixed morphism is closed when the two induced finitely presented ideal maps
  are required to agree;
- incidence with a fixed closed subscheme is closed when the universal family is proper over the parameter space;
- equality of two morphisms from a flat proper universal family to a separated target is closed
  when the equalizer ideal has a finite presentation and its vanishing commutes with base change.

Open conditions include avoiding a fixed closed subset, smoothness of fibers, geometric reducedness, and the graph condition. Locally closed conditions are built by imposing a closed equation and then an open nondegeneracy requirement.

For the last assertion, cover the separated target by affine opens, write the equalizer by the
differences of finitely many coordinate functions, and push the resulting finite coefficient
modules to the proper parameter base. Their zero Fitting loci glue because the target diagonal is
closed. The other closedness statements are proved in the same finite-coefficient fashion.
Thus these assertions concern schemes, not just their points. The phrase “the equation vanishes
on the universal family” means a morphism of coherent sheaves is zero; its coefficient ideal
detects infinitesimal test schemes.

### 13.3 Projective parameter spaces for curve families

Fix $r$ and a polynomial $P(n)=en+c$. The scheme
$\operatorname{Hilb}^P(\mathbf P^r_S/S)$ carries the universal projective flat family. The open
locus on which the fibers are smooth of pure dimension one parametrizes smooth embedded curves
with that polynomial. If one also requires geometric connectedness, this is open in a proper
smooth family. Additional marked effective divisors of degree $d$ are parametrized by the
relative symmetric power of the universal curve.

This is the precise Hilbert apparatus needed for embedded curves: a fixed polynomial, its universal family, open smooth and connected loci, and relative length-$d$ subschemes. Abelian families can likewise be placed in a Hilbert scheme after fixing a polarization type, a relatively very ample power, and the resulting Hilbert polynomial; multiplication, inverse, and identity are morphisms whose graphs live in bounded Hilbert loci, while the two unit laws, inverse laws, associativity, commutativity, and compatibility with the fixed polarization cut out closed loci. Establishing the full moduli problem requires further descent and rigidity, but no broader parameter functor is needed here.

### 13.4 Boundary distinctions

Before using one of these parameter spaces, four distinctions prevent most errors.

First, decide whether the object is an ordered tuple, a cycle, or an embedded finite subscheme. They are represented respectively by $X^d$, $\operatorname{Sym}^d(X)$, and $\operatorname{Hilb}^d(X)$. In degrees zero and one these distinctions disappear. For $d\geq2$, however, $X^d$ remains the ordered parameter space even when $X$ is a smooth relative curve; only its quotient by $\mathfrak S_d$ is $\operatorname{Sym}^d(X)$. On a smooth relative curve it is the last two spaces, $\operatorname{Sym}^d(X)$ and $\operatorname{Hilb}^d(X)$, that agree in every degree. Outside that setting there is no general identification between cycles and embedded finite subschemes.

Second, distinguish a functor from its representing scheme and from its universal family. A $T$-point of a Hilbert scheme is a subscheme of $X_T$; it is not a point of $X$.

Third, state flatness and finite-presentation hypotheses. Constant length on geometric fibers does not detect nilpotent directions of the base. Flatness makes a collection of fibers into a family.

Fourth, record the polarization. A nonconstant Hilbert polynomial has meaning only relative to a chosen ample line bundle. Changing the polarization changes the moduli problem even when the underlying objects are the same.

## 14. Synthesis

### 14.1 The three dictionaries

The first dictionary translates graded algebra into geometry:

$$
\begin{array}{c|c}
\text{graded algebra} & \text{projective geometry}\\
\hline
(A_f)_0 & D_+(f)\\
M(n) & \widetilde M(n)\\
\text{homogeneous quotient} & \text{closed projective subscheme}\\
\text{Veronese algebra} & \text{same Proj, higher twist}
\end{array}
$$

The second translates positivity into asymptotic linear algebra:

$$
\begin{array}{c|c}
\text{geometry} & \text{high tensor powers}\\
\hline
\mathcal L\text{ ample} & \mathcal F\otimes\mathcal L^n\text{ generated}\\
\mathcal L\text{ ample} & H^i(\mathcal F\otimes\mathcal L^n)=0,\ i>0\\
\mathcal L^n\text{ very ample} & X\hookrightarrow\mathbf P(f_*\mathcal L^n)\\
\mathcal F\text{ flat} & P_{\mathcal F_s}\text{ locally constant}
\end{array}
$$

The third translates moving points into parameter schemes:

$$
\begin{array}{c|c}
\text{family} & \text{representing space}\\
\hline
\text{ordered }d\text{-tuple} & X^d\\
\text{permutation quotient; cycles over fields} & \operatorname{Sym}^d(X)\\
\text{length-}d\text{ closed subscheme} & \operatorname{Hilb}^d(X)\\
\text{flat projective subscheme with }P & \operatorname{Hilb}^P(X)
\end{array}
$$

On a smooth relative curve, the last two entries in constant degree coincide with effective divisors, and the universal divisor makes the equality functorial. The first entry remains the ordered cover of the symmetric power (and is generally different for $d\geq2$); passing from it to the divisor parameter space requires quotienting by permutations.

### 14.2 The reusable theorem package

For later use, the conclusions can be read as one chain. Relative Proj commutes with arbitrary base change and carries its twisting sheaf. A finite graded presentation gives a projective embedding. Ample line bundles are characterized by affine nonvanishing opens, eventual generation, and Serre vanishing; a sufficiently high power is very ample. Positivity pulls back under every base change and descends under fpqc covers with the stated quasi-compactness and polarization hypotheses.

For a projective flat family over a locally noetherian base, a coherent sheaf flat over the base
and twisted by high powers of a fixed relatively ample line bundle has locally free pushforward
commuting with base change locally on the base. The fiber Hilbert polynomial is locally
constant. By the flattening-stratification theorem of Section 8.3, the
fixed-polynomial flatness loci are locally closed with the stated universal property over
arbitrary test schemes. By the bounded Macaulay--Gotzmann theorem, over a
noetherian base fixing that polynomial gives a projective finitely presented Hilbert scheme with
a universal flat closed family. Under the same condition, the constant polynomial $d$ gives the
intrinsic space of finite locally free length-$d$ subschemes. For smooth relative curves the
divisor construction gives an independent proof of this constant-polynomial representability.

For a smooth quasi-projective relative curve, this length-$d$ Hilbert scheme is the symmetric power, represents relative effective Cartier divisors, is smooth of relative dimension $d$, and carries a universal finite flat divisor. Its geometrically reduced-fiber open is unordered configuration space with a finite étale universal family. These properties persist under arbitrary base change.

The descent statements of Section 10.5 are also part of the reusable package. Along an affine
faithfully flat quasi-compact cover — in particular along a finite locally free surjection, and
along the finitely many affine pieces of an étale covering — quasi-coherent modules with a descent
datum are effective, quasi-coherent ideals descend without any datum having to be supplied, and
invertibility, finite presentation, flatness and finite local freeness of a given rank descend with
them. Consequently effective Cartier divisors satisfy effective descent, and the functor of
relative effective Cartier divisors of a fixed degree is a sheaf for these covers. Along the same
covers, morphisms into a fixed target descend as well: a morphism into a separated $S$-scheme is
determined by its composite with the cover, and a morphism into a quasi-projective — or affine —
$S$-scheme whose two restrictions to the double product agree comes from a unique morphism
downstairs. Hence the functor of points of a quasi-projective $S$-scheme is a sheaf for these
covers, which is what makes the chartwise comparison of Section 11.4 assemble into a bijection over
every test scheme. A general
descent theory is developed in a later volume and subsumes these statements; they are proved here
because Chapter 11 needs them and nothing earlier supplies them.

An ample bundle embeds a projective curve after a high power. A relatively ample bundle on an
abelian scheme likewise has uniformly very ample high powers, whose section bundles commute with
base change. Thus curves and polarized abelian schemes enter fixed projective spaces, where
Hilbert polynomials and universal parameter schemes can control their variation.

### 14.3 Conclusion

Projective geometry over a base is the art of making choices uniform. A homogeneous coordinate in one fiber becomes a twisting sheaf on the whole family. An embedding chosen point by point becomes one relatively very ample power. A fluctuating dimension becomes the rank of a vector bundle when flatness is present. An unordered collection of points becomes a symmetric power, and a uniformly bounded embedded family becomes a point of a Hilbert scheme.

The hypotheses are part of the geometry. Noetherian finiteness makes equations bounded; properness turns immersions into closed immersions; flatness prevents specialization from changing the polynomial; smoothness of a curve turns finite flat subschemes into Cartier divisors; separatedness makes graphs closed; and quasi-projectivity makes finite quotients exist as schemes. With these boundaries respected, ample bundles, Hilbert polynomials, symmetric powers, and Hilbert schemes form a single coherent language for the projective families used throughout arithmetic geometry.
