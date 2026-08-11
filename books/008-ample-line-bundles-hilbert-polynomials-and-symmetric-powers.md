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
   - [Constancy and the flatness boundary](#83-constancy-and-the-flatness-boundary)
   - [Flattening strata](#84-flattening-strata)
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

so the construction recovers $\mathbf P^r_k$. If $A_+=0$, Proj is empty. If $A=k[x]$ with $\deg x=2$, Proj is still one point: the grading affects twists even when the underlying scheme is unchanged.

### 1.3 The construction of relative Proj

Let $S$ be a scheme and

$$
\mathcal A=\bigoplus_{n\geq0}\mathcal A_n
$$

a quasi-coherent graded $\mathcal O_S$-algebra. We normally assume $\mathcal A_0=\mathcal O_S$. Over an affine open $U=\operatorname{Spec}R$, quasi-coherence identifies $\mathcal A|_U$ with the sheaf associated to a graded $R$-algebra $A(U)$. The schemes $\operatorname{Proj}A(U)$ agree on overlaps, since restriction to $D(h)\subset U$ is degreewise localization at $h\in R=A_0$. They glue to

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

These modules localize correctly and glue to a quasi-coherent sheaf on $\operatorname{Proj}A$. Taking $M=A$ gives $\mathcal O(n)$. Relative Proj has the same construction.

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

It need not be an isomorphism in small degrees; saturation again intervenes. In sufficiently high degrees, finite generation and Serre vanishing will make it behave as expected.

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

For $\mathcal E=\mathcal O_S^{r+1}$ we write $\mathbf P^r_S$. It is covered by $r+1$ standard affine spaces. The transition functions divide coordinates by the chosen nonzero coordinate, exactly as over a field.

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

As an example, the degree-$d$ Veronese map arises from all monomials of degree $d$:

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

Finally, a proper morphism may possess a line bundle whose restriction to every fiber is ample while the bundle is not relatively ample if quasi-compactness or finite-presentation conditions are abandoned. Relative positivity is a uniform statement near points of the base, not a collection of unrelated fiberwise statements.

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

Allowing $n$ to depend on $s$ makes the definition local and robust. If $X$ is quasi-compact, one may choose finitely many $s$ and replace their powers by a common multiple. The resulting sections define a quasi-projective immersion. Conversely, the standard opens of projective space are affine, so a very ample bundle is ample.

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

Conversely, under the same projective morphism over a noetherian affine base, if this vanishing and eventual generation hold for all coherent ideals, then $\mathcal L$ is ample. Chapter 6 proves the forward implication from the standard affine cover of projective space.

### 4.5 Tensor powers and operations

If $\mathcal L$ is ample, every positive power $\mathcal L^d$ is ample: replace each defining section by a power. Conversely, if $\mathcal L^d$ is ample for one $d>0$, then $\mathcal L$ is ample because sufficiently large powers in each residue class modulo $d$ are obtained by tensoring with one of finitely many fixed powers.

If $f:X\to S$ is quasi-compact and separated, $\mathcal L$ is $f$-ample, and $\mathcal M$ is invertible, then $\mathcal L^n\otimes\mathcal M$ is $f$-ample for all sufficiently large $n$. Apply the generation criterion to the finitely many twists needed to generate $\mathcal M$ and its inverse. In particular, in this relative context ampleness is insensitive to a bounded twist at high degree.

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

Let $g:T\to S$. If $\mathcal L$ is very ample for $X\to S$, then $\mathcal L_T$ is very ample for $X_T\to T$: base change the chosen immersion. If $\mathcal L$ is ample, then $\mathcal L_T$ is ample. For the latter statement, base change of an affine nonvanishing open is affine, and the pulled-back sections cover.

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

**Projectivity descent with a polarization.** Let $f:X\to S$ be proper and of finite presentation, and let $\mathcal L$ be a line bundle on $X$. If some fpqc base change makes $\mathcal L$ relatively ample, then $\mathcal L$ is relatively ample and $f$ is projective.

This polarized form records the datum used in moduli problems and avoids concealing an obstruction
in the Picard group.

### 5.4 Necessary hypotheses and failures

Faithfulness cannot be dropped. Restricting to an open subset of $S$ may erase a bad fiber, so positivity over that open says nothing at omitted points. Flatness cannot be replaced by a merely surjective map: nilpotent thickenings can make module surjections and immersion conditions invisible.

Quasi-compactness provides finite linear systems. An infinite disjoint union may be fiberwise embeddable with unbounded projective dimension but admit no one finite-rank ambient bundle. Quasi-separatedness is what makes sections commute with flat base change in the form used above.

Finally, “very ample after taking a power” descends to ampleness, but it need not show that the original bundle is very ample if only the power is known upstairs. For example, on an elliptic curve a line bundle of degree $2$ is not very ample, whereas its square has degree $4$ and is very ample. Tensor roots do not inherit separation automatically.

## 6. Serre vanishing and projective cohomology

### 6.1 The projective-space calculation

Hilbert polynomials arise from an asymmetry: positive twists acquire many sections while their higher cohomology eventually disappears. We begin where the calculation is visible.

Cover $\mathbf P^r_A$ by $U_i=D_+(x_i)$. Every finite intersection is affine, so the alternating Cech complex computes the cohomology of a quasi-coherent sheaf. For $\mathcal O(n)$ its terms are degree-$n$ parts of localizations of $A[x_0,\ldots,x_r]$. Sorting Laurent monomials by the set of variables with negative exponent gives

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

for $n\geq0$, a free $A$-module of rank $\binom{n+r}{r}$. If $r\geq1$, then for $n\leq-r-1$ the top cohomology
$H^r(\mathbf P^r_A,\mathcal O(n))$ is the free $A$-module with basis the Laurent monomials
$x_0^{a_0}\cdots x_r^{a_r}$ for which every $a_i<0$ and $\sum_i a_i=n$; it is zero for
$n\geq-r$. This also proves, over a field,

$$
\chi(\mathbf P^r_k,\mathcal O(n))=\binom{n+r}{r}
$$

for every integer $n$, when the binomial expression is interpreted as a polynomial. Because every differential is defined over $\mathbf Z$, the calculation commutes with extension of scalars.

### 6.2 Vanishing and generation in high degree

**Serre vanishing theorem.** Let $A$ be noetherian and let $\mathcal F$ be coherent on $\mathbf P^r_A$. There is $n_0$ such that

$$
H^i(\mathbf P^r_A,\mathcal F(n))=0
\quad(i>0,\ n\geq n_0),
$$

and $\mathcal F(n)$ is generated by finitely many global sections for $n\geq n_0$.

The strategy is to replace $\mathcal F$ by finitely many twists of $\mathcal O$. Choose a surjection $\bigoplus_j\mathcal O(-a_j)\twoheadrightarrow\mathcal F$. Its kernel is coherent because $A$ is noetherian. The long exact sequence reduces vanishing for $\mathcal F$ to the line-bundle calculation and vanishing one degree higher for the kernel. Descending induction from $i=r$ terminates because the standard cover has $r+1$ terms. The same surjection, twisted far enough, gives generation.

If $i:X\hookrightarrow\mathbf P^r_A$ is closed and $\mathcal G$ coherent on $X$, then $i_*\mathcal G$ is coherent, cohomology is unchanged, and $i_*\mathcal G(n)=i_*(\mathcal G\otimes i^*\mathcal O(n))$. Hence the theorem holds on every projective noetherian $A$-scheme. For an ample $\mathcal L$, replace it by a very ample power $\mathcal L^d$ and treat the finitely many residue classes of exponents modulo $d$.

### 6.3 Relative finiteness

Let $f:X\to S$ be projective with $S$ locally noetherian, and let $\mathcal F$ be coherent. On an affine $U=\operatorname{Spec}A$, embed $X_U$ in projective space. The finite Cech calculation and the noetherian syzygy argument show that each $H^i(X_U,\mathcal F)$ is a finite $A$-module and vanishes above a finite bound. Consequently $R^if_*\mathcal F$ is coherent.

If $\mathcal L$ is an $f$-ample line bundle, then for $n\gg0$,

$$
R^if_*(\mathcal F\otimes\mathcal L^n)=0\quad(i>0).
$$

If $\mathcal F$ is flat over $S$, then after increasing $n$ locally on $S$, $f_*(\mathcal F(n))$ is locally free and commutes with arbitrary base change. Vanishing turns degree-zero cohomology into a kernel in a finite complex; flatness and fiberwise vanishing make kernel and image commute with tensor product. Thus

$$
f_*(\mathcal F(n))\otimes\kappa(s)
\simeq H^0(X_s,\mathcal F_s(n)).
$$

The bound is globally uniform when $S$ is quasi-compact.

### 6.4 Regularity and uniform bounds

A coherent sheaf $\mathcal F$ on $\mathbf P^r_A$ is **$m$-regular** if

$$
H^i(\mathbf P^r_A,\mathcal F(m-i))=0
\quad\text{for every }i>0.
$$

The hyperplane exact sequence shows that $m$-regular implies $(m+1)$-regular, that $\mathcal F(m)$ is globally generated, and that

$$
H^0(\mathcal F(n))\otimes_AH^0(\mathcal O(1))
\twoheadrightarrow H^0(\mathcal F(n+1))
\quad(n\geq m).
$$

One chooses a hyperplane avoiding the relevant associated points and inducts on $r$; over a finite residue field, make a faithfully flat extension to choose the hyperplane and descend the result. Regularity packages all high-degree behavior into one integer. For ideals with a fixed Hilbert polynomial, a uniform regularity bound exists. Chapter 12 proves the bounded form needed to construct the Hilbert scheme.

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

Apply the lemma with $\mathcal M=\mathcal L$. Serre vanishing identifies its value with $h^0$ for
all large $n$, giving the asserted Hilbert polynomial without a residue-class gap. Uniqueness
follows because a polynomial vanishing at all large integers is zero. When $\mathcal L$ itself is
very ample, a finite graded resolution gives the familiar equivalent expression as an integral
linear combination of $\binom{t+r-a}{r}$.

### 7.2 The polynomial of a projective scheme

For $Z\subseteq\mathbf P^r_k$ closed, its Hilbert polynomial is that of $\mathcal O_Z$. The ideal sequence gives

$$
P_Z(n)=\binom{n+r}{r}-P_{\mathcal I_Z}(n).
$$

If $Z$ is a hypersurface of degree $e$, then

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

for a positive integer $\deg_{\mathcal L}(\mathcal F)$. A general hyperplane gives a finite-difference relation

$$
P_{\mathcal F}(n)-P_{\mathcal F}(n-1)=P_{\mathcal F|_H}(n)
$$

up to contributions supported in lower dimension. Induction ends with the total length of a zero-dimensional sheaf, proving both assertions.

Thus a finite scheme of length $d$ has constant polynomial $d$. A projective curve has $P(n)=en+c$, with $e$ its degree in the chosen embedding. Projective space has polynomial $\binom{n+r}{r}$. For a union one computes by the exact sequence

$$
0\to\mathcal O_{Y\cup Z}\to\mathcal O_Y\oplus\mathcal O_Z
\to\mathcal O_{Y\cap Z}\to0.
$$

### 7.4 Dependence on the polarization

The polynomial belongs to $(\mathcal F,\mathcal L)$. Replacing $\mathcal L$ by $\mathcal L^q$ replaces $P(t)$ by $P(qt)$. Different ample bundles can produce different leading coefficients, or polarized degrees; the polynomial degree remains the support dimension. A moduli problem must therefore fix an embedding or polarization before specifying a Hilbert polynomial.

Dimension is independent of the polarization. For curves the linear coefficient is the degree of the chosen bundle. For finite schemes the constant polynomial is total length and is independent of any polarization. This explains why length-$d$ Hilbert functors have an intrinsic meaning even when a projective embedding is used to construct them.

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

### 8.3 Constancy and the flatness boundary

A safe converse is available over a reduced base.

**Numerical flatness criterion.** Let $S$ be reduced and locally noetherian, $f:X\to S$ projective,
and $\mathcal F$ coherent. Then $\mathcal F$ is $S$-flat if and only if its fiber Hilbert polynomial
is locally constant.

The forward implication is the constancy theorem. For the converse, use the flattening theorem of
the next section. Locally on a connected component, let the common polynomial be $P$. Every point
of $S$ then belongs set-theoretically to the flattening stratum $S_P$. Thus the locally closed
immersion $S_P\hookrightarrow S$ has all of $S$ as its underlying image. It is consequently a
closed immersion defined by a nilpotent ideal. Reducedness forces that ideal to vanish, so
$S_P=S$, which is precisely flatness of $\mathcal F$ over $S$. This argument also explains exactly
why reducedness, rather than an associated-point condition, is the boundary.

Reducedness matters. On $\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ there is only one topological fiber. The module $k$ has a constant one-point fiber but is not flat. Fiber polynomials cannot see an infinitesimal direction when the base has no second point in that direction.

### 8.4 Flattening strata

**Flattening theorem.** Let $S$ be noetherian, $f:X\to S$ projective, $\mathcal L$ relatively very ample, and $\mathcal F$ coherent. For every numerical polynomial $P$ there is a locally closed subscheme $S_P\subseteq S$ such that $T\to S$ factors through $S_P$ exactly when $\mathcal F_T$ is flat over $T$ with fiber polynomial $P$. These strata cover the underlying set, and finitely many meet a quasi-compact open.

The construction is local on $S$, so embed $X$ in $\mathbf P^r_S$ over an affine open. A finite
graded presentation of the sheaf module and the noetherian hypothesis give one regularity bound
$m$ for all its fibers on this open. For a finitely presented module $M$ on the base, the locus on
which $M$ is locally free of rank $q$ is represented by

$$
V(\operatorname{Fitt}_{q-1}M)\setminus
V(\operatorname{Fitt}_{q}M).
$$

For $q=0$ use the convention $\operatorname{Fitt}_{-1}M=0$.
Its universal property is scheme-theoretic: a base change factors through this locally closed
subscheme exactly when the pulled-back presentation has constant rank $q$, including over
nilpotent test rings.

Apply this construction to finitely many consecutive terms, beginning in degree $m$ and extending
past the degrees of every generator and relation in a fixed graded presentation of $\mathcal F$,
with prescribed ranks $P(m+i)$. Also impose, by vanishing of minors, that
multiplication by the $r+1$ linear coordinates carries kernels in one degree into the next.
Regularity propagates those kernel and rank conditions to every later degree. The resulting
high-degree graded module is flat degree by degree and commutes with scalar extension.
Sheafification kills only bounded-degree torsion, so the associated sheaf is flat with polynomial
$P$. Conversely, if $\mathcal F_T$ is flat with polynomial $P$, relative vanishing and base
change give exactly these ranks and multiplication relations, forcing $T\to S$ through the same
locus. This proves the universal property and makes the local constructions glue. Noetherian
quasi-compactness also shows that only finitely many different rank profiles, hence polynomials,
occur on a quasi-compact open.

The strata need not be open. Once a finitely presented family is flat, flatness persists on an open neighborhood; forcing an arbitrary family to become flat can impose closed equations.

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
$\mathcal L^n$, flat over $S$. Relative Serre vanishing and cohomological base change therefore
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
A closed subscheme $Z\subseteq X_T$ is a family of length $d$ over $T$ if $Z\to T$ is finite locally free of rank $d$. Every geometric fiber is zero-dimensional of scheme-theoretic length $d$. Rank is stronger than counting points: one nonreduced point can have length $d$.

If $X\to S$ is separated, these families form a set-valued functor: an isomorphism between two closed subschemes over $X_T$ is unique. A tuple of sections produces the disjoint union of their graphs only while the graphs remain disjoint. When points collide, the union loses rank; retaining multiplicity requires an infinitesimal thickening.

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
The affine quotients glue because invariant localization agrees on invariant principal opens. The
categorical property follows affine-locally. Finally, tensoring the translates of a relatively
ample bundle gives an ample bundle with a canonical $G$-linearization. On the fiber over a fixed
point, each stabilizer acts through a character; raising to the $|G|$th power kills every such
character. On an invariant affine chart, the invariant sections of this power form an invertible
$B^G$-module, as may be checked after localizing at every prime and lifting it to $B$.
These modules glue to an ample bundle downstairs: invariant powers of affine nonvanishing charts
remain affine and cover. A high power is therefore very ample and proves that $Y/G$ is
quasi-projective.

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
orbit presheaf. This condition holds on the free locus. For a smooth relative curve, the local
monic-polynomial calculation proves directly that unordered roots give the divisor functor; that
stronger and more useful statement is established in Section 11.4. For a general
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

It is invariant under $\mathfrak S_d$. Locally, if $C=\mathbf A^1_S$ with coordinate $z$ and the entries have coordinates $t_1,\ldots,t_d$, its equation is

$$
\prod_{i=1}^d(z-t_i)
=z^d-e_1z^{d-1}+\cdots+(-1)^de_d.
$$

The coefficients are symmetric, so the divisor descends to

$$
\Delta_d\subset C\times_S\operatorname{Sym}^d_S(C).
$$

It is finite locally free of degree $d$ over the symmetric power. The local polynomial calculation also covers collisions and every residue characteristic: repeated roots give the correct nonreduced divisor, and no division by $d!$ occurs.

**Universal-divisor theorem.** For every $T\to S$, pullback of $\Delta_d$ induces a natural bijection

$$
\operatorname{Hom}_S(T,\operatorname{Sym}^d_S(C))
\simeq
\{\text{relative effective Cartier divisors of degree }d
\text{ on }C_T\}.
$$

The proof must cover divisors with several support points and nilpotent collisions. We use the
following local chart lemma.

**Divisor-chart lemma.** Let $D_0$ be a length-$d$ divisor on a geometric fiber of a smooth curve.
After an étale extension of the base, write its support as distinct sections
$x_1,\ldots,x_r$ with multiplicities $d_1+\cdots+d_r=d$. There are pairwise disjoint
neighborhoods $U_j$ of the sections, étale parameters $z_j:U_j\to\mathbf A^1$, and étale
neighborhoods of $D_0$ in both the divisor functor and $\operatorname{Sym}^d(C)$ mapping to

$$
\prod_{j=1}^r\mathbf A^{d_j},
$$

with coordinates the coefficients of one monic polynomial of degree $d_j$ for each $j$. On both
sides the additional étale datum is the lift of that finite divisor from $\mathbf A^1$ to $U_j$.

To prove the lemma, first split the reduced support by an étale extension and choose the disjoint
smooth parameters. A nearby divisor has a unique open-and-closed decomposition of ranks $d_j$ in
the $U_j$: the idempotents of the special finite algebra lift uniquely after shrinking the base.
For the $j$th piece, its special fiber is $k[z_j]/(z_j^{d_j})$. Hence
$1,z_j,\ldots,z_j^{d_j-1}$ is a basis on the special fiber and remains a basis by Nakayama. The
kernel of the resulting quotient is generated by a unique monic polynomial

$$
z_j^{d_j}-a_{j,1}z_j^{d_j-1}+\cdots+(-1)^{d_j}a_{j,d_j}.
$$

Conversely this polynomial cuts out a finite free Cartier divisor with the displayed basis. An
étale morphism has the unique infinitesimal lifting property, so a chosen lift of the special
divisor to $U_j$ extends uniquely over nilpotent thickenings; this makes the corresponding map of
divisor charts étale. On the ordered power, the same coefficients are the elementary symmetric
functions of the $d_j$ local roots. The fundamental theorem on symmetric polynomials identifies
$\operatorname{Sym}^{d_j}(\mathbf A^1)$ with $\mathbf A^{d_j}$ over $\mathbf Z$; no division by
$d_j!$ is involved. The same unique lifting property shows that
$\operatorname{Sym}^{d_j}(U_j)\to\operatorname{Sym}^{d_j}(\mathbf A^1)$ is étale at the chosen
cycle and carries exactly the same lift datum. Taking the product over $j$ proves the lemma.

Now let $D\subset C_T$ be any relative effective divisor. Apply the chart lemma near every point
of $T$. Its monic coefficients give local morphisms to $\operatorname{Sym}^d(C)$. On overlaps the
morphisms agree because their pullbacks of the monic equations cut out the same divisor; since the
quotient is separated, they glue. This proves surjectivity. Conversely, on every divisor chart the
coefficients are recovered uniquely from the pulled-back divisor, proving injectivity. Every step
uses formation of a finite locally free algebra, idempotents, and monic equations, all of which
commute with arbitrary base change. The result is therefore a natural bijection on all test
schemes, not merely on geometric points.

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

For $P=d$ constant, write $\operatorname{Hilb}^d_{X/S}$. Its objects are exactly closed subschemes finite locally free of rank $d$ over $T$. Indeed, a projective flat finitely presented morphism with zero-dimensional fibers is finite, and the constant fiber length is the rank. Conversely finite locally free rank $d$ has polynomial $d$.

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

One degree alone remembers only a vector-space quotient, not an ideal. Multiplication must be compatible:

$$
I_n\cdot H^0(\mathcal O(m))\subseteq I_{n+m}.
$$

A regularity bound says that for fixed $P$ there is $m(P,r)$ such that every saturated homogeneous
ideal with polynomial $P$ is $m$-regular and is generated from degree $m$ onward. Use two
Grassmannians, $G_m$ and $G_{m+1}$. On their product write

$$
0\longrightarrow\mathcal K_i
\longrightarrow V_i\otimes\mathcal O
\longrightarrow\mathcal Q_i\longrightarrow0
\qquad(i=m,m+1)
$$

for the universal sequences, where $\mathcal Q_i$ has rank $P(i)$. Multiplication followed by the
second universal quotient gives

$$
\mathcal K_m\otimes V_1
\longrightarrow V_{m+1}\otimes\mathcal O
\longrightarrow\mathcal Q_{m+1}.
$$

The vanishing of this composite is a closed condition, defining an incidence subscheme
$H_P\subseteq G_m\times_SG_{m+1}$. At a geometric point it says

$$
V_1K_m\subseteq K_{m+1}.
$$

Macaulay growth gives the reverse dimension inequality. More precisely, the quotient by the ideal
generated by $K_m$ has degree-$(m+1)$ dimension at most $P(m+1)$, while the displayed inclusion
makes that dimension at least $\dim(V_{m+1}/K_{m+1})=P(m+1)$. Equality follows, so
$V_1K_m=K_{m+1}$. Fiberwise surjectivity and Nakayama make this equality valid over the whole
incidence scheme, including its nilpotent directions. Gotzmann persistence then recovers all
degrees above $m$ from this one multiplication step. Thus the second Grassmannian factor is
uniquely determined by the first, but retaining it makes the closed equations and their ranks
completely explicit.

### 12.3 Representability with fixed polynomial

The remaining boundedness input is numerical.

**Gotzmann boundedness theorem.** Every numerical polynomial occurring as the Hilbert polynomial of a closed subscheme of $\mathbf P^r$ has a unique expansion

$$
P(n)=
\binom{n+a_1}{a_1}
+\binom{n+a_2-1}{a_2}
+\cdots+
\binom{n+a_s-(s-1)}{a_s},
$$

with $r\geq a_1\geq\cdots\geq a_s\geq0$. Every saturated ideal sheaf with polynomial $P$ is
$s$-regular.

We recall the combinatorial proof because this is the boundedness input on which representability
rests. Every nonnegative integer $h$ has a unique $n$th Macaulay expansion

$$
h=\binom{b_n}{n}+\binom{b_{n-1}}{n-1}+\cdots+\binom{b_j}{j},
\qquad b_n>b_{n-1}>\cdots>b_j\geq j.
$$

Set

$$
h^{\langle n\rangle}
=\binom{b_n+1}{n+1}+\cdots+\binom{b_j+1}{j+1}.
$$

If $R=k[x_0,\ldots,x_r]/I$ and $h_R(n)=h$, then
$h_R(n+1)\leq h^{\langle n\rangle}$. To see this, replace the degree-$n$ part of $I$ by its
initial monomial space. Among monomial sets of a fixed size, repeatedly compressing a monomial
toward lexicographic order cannot enlarge the complement of its degree-$(n+1)$ shadow. The
lexicographic complement consists of the blocks counted by the displayed binomial expansion, and
its next shadow has exactly $h^{\langle n\rangle}$ elements. This proves the inequality.

If equality holds and the ideal has no generators after degree $n$, every compression step also
has equality. Consequently the next shadow has no gap, the same equality holds in degree $n+1$,
and induction gives it in every later degree. This is Macaulay persistence. Apply finite
differences to the eventual Hilbert function: removing the first lexicographic block lowers the
dimension, and induction yields precisely the displayed Gotzmann expansion. For $n\geq s$ it
satisfies

$$
P(n+1)=P(n)^{\langle n\rangle}.
$$

Persistence says that the saturated ideal is generated from degree $s$ onward, while the
hyperplane exact sequence gives the vanishings defining $s$-regularity. This proves the stated
bound. Every step counts monomials, so the argument is characteristic-free and uses no averaging.

**Hilbert representability theorem.** Under the hypotheses of Section 12.1, $\operatorname{Hilb}^P_{X/S}$ is represented by a projective finitely presented $S$-scheme

$$
\operatorname{Hilb}^P(X/S).
$$

The zero polynomial has the empty Gotzmann expansion and represents the unique empty subscheme,
so $\operatorname{Hilb}^0(X/S)=S$. If a nonzero $P$ has no Gotzmann expansion appropriate to
$\mathbf P^r$, no geometric fiber can occur and the representing scheme is empty. Otherwise use
the construction below.

For projective space, take $m\geq s$ and the closed incidence scheme $H_P$ just constructed. Let
$J$ be the graded ideal generated by its universal $K_m$. The equality
$V_1K_m=K_{m+1}$ and Gotzmann persistence show inductively that every quotient
$V_n/J_n$ for $n\geq m$ is finite locally free of rank $P(n)$ and that multiplication gives the
same result after arbitrary scalar extension. Sheafifying $J$ gives a universal closed subscheme
$\mathcal Z\subseteq\mathbf P^r_{H_P}$. The graded flatness criterion, checked in all degrees
$n\geq m$, makes $\mathcal O_{\mathcal Z}$ flat over $H_P$; its fibers have polynomial $P$.

Conversely, for a flat family $Z/T$, Gotzmann regularity on geometric fibers, relative vanishing,
and base change make the degree-$m$ and degree-$(m+1)$ quotients locally free of the required
ranks. They give a unique map $T\to H_P$. The recovered sheafified ideal is the original ideal
because both are saturated and agree in every degree at least $m$. Families over nonnoetherian
test schemes cause no gap: the family and its finitely many equations descend locally to a
finite-presentation test scheme, where the argument applies, and then base change back. These two
constructions are inverse and functorial.

For a closed $X\subseteq\mathbf P^r_S$ with homogeneous ideal $\mathcal I_X$, increase $m$
locally on $S$ so that this ideal is generated in degrees at most $m$. Write
$I_{X,m}\subseteq V_m$ for its degree-$m$ module of equations. Requiring the composite

$$
I_{X,m}\longrightarrow V_m\longrightarrow\mathcal Q_m
$$

to vanish is then equivalent, by multiplication and regularity, to containment of
$\mathcal I_X$ in the universal ideal. It is a closed condition.
The local constructions agree on overlaps by their universal property and therefore glue to
$\operatorname{Hilb}^P(X/S)$. Projectivity comes from the product of Grassmannians, and finite
presentation from the finite incidence and containment equations.

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

For $P=d$, representability gives $\operatorname{Hilb}^d(X/S)$, projective over $S$ when $X$ is. Its universal family is finite locally free of rank $d$. The construction is independent, up to unique isomorphism, of the projective embedding because the functor itself mentions only length-$d$ closed subschemes.

If $X\to S$ is merely quasi-projective, choose an open immersion $X\subset\bar X$ with $\bar X$ projective. The locus in $\operatorname{Hilb}^d(\bar X/S)$ where the universal finite family lies inside $X$ is open: its complement is the image of the intersection with $\bar X\setminus X$, and that image is closed because the universal family is finite. This open represents $\operatorname{Hilb}^d(X/S)$. It is quasi-projective and commutes with arbitrary base change.

For a smooth morphism $X/S$ of relative dimension $r$, the open locus of reduced geometric fibers is the unordered configuration space. When $r>1$, the boundary contains many infinitesimal directions. Already $\operatorname{Hilb}^2(\mathbf A^2)$ records a collision together with a tangent direction, whereas $\operatorname{Sym}^2(\mathbf A^2)$ records only the doubled cycle. Thus the Hilbert-to-cycle map is not generally an isomorphism in dimension two.

### 12.5 Curves: Hilbert scheme equals symmetric power

Let $C\to S$ be a smooth quasi-projective curve. Sections 10.3 and 11.4 identify, for every $T$,

$$
\operatorname{Hilb}^d_{C/S}(T)
=\{\text{relative effective divisors of degree }d\}
=\operatorname{Hom}_S(T,\operatorname{Sym}^d_S(C)).
$$

By uniqueness of representing objects,

$$
\operatorname{Hilb}^d(C/S)\simeq\operatorname{Sym}^d_S(C).
$$

Under this isomorphism their universal families agree with $\Delta_d$. In particular the symmetric power is smooth over $S$ of relative dimension $d$. The divisor-chart lemma gives étale coordinates over the affine coefficient space with coordinates $a_1,\ldots,a_d$, even when roots collide; it does not require a global parameter on the curve.

For a singular curve, the Hilbert scheme and symmetric power still agree on the open locus of
subschemes supported in the smooth locus, by the theorem just proved there. Over a singular point,
several embedded ideals can have the same multiplicities, so the two functors differ. No global
Hilbert-to-cycle morphism for singular families is needed or asserted here.

## 13. Universal constructions for later geometry

### 13.1 Graphs and spaces of morphisms

If $Y\to S$ is separated, a morphism $u:X_T\to Y_T$ has a closed graph

$$
\Gamma_u\subseteq X_T\times_TY_T.
$$

Suppose $X\to S$ is projective flat and finitely presented and $Y\to S$ is projective. Fix a
Hilbert polynomial $P$ for graphs in a chosen projective embedding of $X\times_SY$. The Hilbert
scheme of that product represents all flat closed families with polynomial $P$. For its universal
family $\Gamma$, consider the proper finitely presented projection
$p:\Gamma\to X$.

The locus in the parameter base where $p$ is an isomorphism is open. Indeed, near a point where
$p$ is an isomorphism on the fiber, upper semicontinuity of fiber dimension removes the closed
non-quasi-finite locus. The resulting proper quasi-finite morphism is finite. It is then controlled
by the map of coherent algebras

$$
\mathcal O_X\longrightarrow p_*\mathcal O_\Gamma.
$$

Its kernel and cokernel vanish on the chosen fiber. Their supports are closed in $X$, and their
images in the parameter base are closed because $X$ is proper. Removing those images makes the
algebra map, hence $p$, an isomorphism. Conversely an isomorphism is a graph, and composing its
inverse with $\Gamma\hookrightarrow X\times Y$ gives the unique morphism $X\to Y$. Thus this open
subscheme represents morphisms whose graphs have polynomial $P$.

This construction is used only with bounded graph polynomials. There is no single finite-type scheme of all morphisms of arbitrary degree. Fixing degree or Hilbert polynomial is the finiteness datum that makes a parameter space possible.

### 13.2 Closed loci inside parameter spaces

Many moduli conditions become closed conditions on a Hilbert scheme, provided the displayed
properness and finite-presentation hypotheses are retained:

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

Fix $r$ and a polynomial $P(n)=en+c$. The scheme $\operatorname{Hilb}^P(\mathbf P^r_S/S)$ carries the universal projective flat family. The open locus on which the fibers are smooth of pure dimension one parametrizes smooth embedded curves with that polynomial. If one also requires geometric connectedness, this is open in a proper smooth family. Additional marked effective divisors of degree $d$ are parametrized by the relative symmetric power of the universal curve.

This is the precise Hilbert apparatus needed for embedded curves: a fixed polynomial, its universal family, open smooth and connected loci, and relative length-$d$ subschemes. Abelian families can likewise be placed in a Hilbert scheme after fixing a polarization type, a relatively very ample power, and the resulting Hilbert polynomial; group laws are morphisms whose graphs live in bounded Hilbert loci, and the identity and associativity equations cut out closed loci. Establishing the full moduli problem requires further descent and rigidity, but no broader parameter functor is needed here.

### 13.4 Boundary distinctions

Before using one of these parameter spaces, four distinctions prevent most errors.

First, decide whether the object is an ordered tuple, a cycle, or an embedded finite subscheme. They are represented respectively by $X^d$, $\operatorname{Sym}^d(X)$, and $\operatorname{Hilb}^d(X)$. Only on a smooth curve do the last two agree.

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

On a smooth relative curve, the last two entries in constant degree coincide with effective divisors, and the universal divisor makes the equality functorial.

### 14.2 The reusable theorem package

For later use, the conclusions can be read as one chain. Relative Proj commutes with arbitrary base change and carries its twisting sheaf. A finite graded presentation gives a projective embedding. Ample line bundles are characterized by affine nonvanishing opens, eventual generation, and Serre vanishing; a sufficiently high power is very ample. Positivity pulls back under every base change and descends under fpqc covers with the stated quasi-compactness and polarization hypotheses.

For a projective flat family over a locally noetherian base, high twisted pushforwards are locally
free and commute with base change locally on the base. The fiber Hilbert polynomial is locally
constant. Over a noetherian base, fixing that polynomial gives a projective finitely presented
Hilbert scheme with a universal flat closed family. The constant polynomial $d$ gives the
intrinsic space of finite locally free length-$d$ subschemes.

For a smooth quasi-projective relative curve, this length-$d$ Hilbert scheme is the symmetric power, represents relative effective Cartier divisors, is smooth of relative dimension $d$, and carries a universal finite flat divisor. Its geometrically reduced-fiber open is unordered configuration space with a finite étale universal family. These properties persist under arbitrary base change.

An ample bundle embeds a projective curve after a high power. A relatively ample bundle on an
abelian scheme likewise has uniformly very ample high powers, whose section bundles commute with
base change. Thus curves and polarized abelian schemes enter fixed projective spaces, where
Hilbert polynomials and universal parameter schemes can control their variation.

### 14.3 Conclusion

Projective geometry over a base is the art of making choices uniform. A homogeneous coordinate in one fiber becomes a twisting sheaf on the whole family. An embedding chosen point by point becomes one relatively very ample power. A fluctuating dimension becomes the rank of a vector bundle when flatness is present. An unordered collection of points becomes a symmetric power, and an embedded family becomes a point of a Hilbert scheme.

The hypotheses are part of the geometry. Noetherian finiteness makes equations bounded; properness turns immersions into closed immersions; flatness prevents specialization from changing the polynomial; smoothness of a curve turns finite subschemes into Cartier divisors; separatedness makes graphs closed; and quasi-projectivity makes finite quotients exist as schemes. With these boundaries respected, ample bundles, Hilbert polynomials, symmetric powers, and the selected Hilbert schemes form a single coherent language for the projective families used throughout arithmetic geometry.
