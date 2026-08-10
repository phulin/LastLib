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
   - [Abelian schemes and ample cubical bundles](#93-abelian-schemes-and-ample-cubical-bundles)
   - [The theorem of the cube and very ampleness](#94-the-theorem-of-the-cube-and-very-ampleness)
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
    - [A boundary checklist](#134-a-boundary-checklist)
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

over $S$. It is **quasi-projective** if the immersion is locally closed. One may equivalently use some $\mathbf P^r_S$ locally on a quasi-compact base; a finite locally free $\mathcal E$ is more intrinsic.

Some authors permit a projective morphism to be locally projective on the base. For quasi-compact $S$ the definitions agree after enlarging the ambient bundle: finitely many local embeddings can be combined using twists and direct sums. Here “projective” always includes a global finite-rank projective bundle unless explicitly prefixed by “locally.”

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

Composites of projective morphisms are projective. Indeed, after embedding $X$ into a projective bundle over $Y$ and $Y$ into one over $S$, twist the coefficients of the first embedding by a sufficiently high pullback of $\mathcal O_Y(1)$. Its finitely many coefficients then extend from $Y$ to the ambient projective space. A Segre-Veronese embedding puts the result in one projective bundle over $S$. The same argument with locally closed immersions proves the quasi-projective version.

This proof is sometimes hidden behind a permanence slogan. The twisting step is decisive: coefficients varying on $Y$ do not automatically become homogeneous coordinates over $S$.

### 3.3 Separatedness, finite type, and properness

If $\mathcal E$ has finite rank, $\mathbf P_S(\mathcal E)\to S$ is finitely presented, separated, and proper. Finite presentation and separatedness follow from its finite affine cover and the closed diagonal. Properness can be proved by the valuative criterion. Given a valuation ring $V$ with fraction field $K$, a $K$-point is a one-dimensional quotient of $K\otimes_VE$. Multiply a representing vector of coefficients by a scalar so that all coefficients lie in $V$ and at least one is a unit. The normalized tuple gives a unique $V$-point. Uniqueness follows because two primitive tuples differing by a $K$-scalar differ by a $V$-unit.

A closed subscheme of a proper scheme is proper. Hence a projective morphism is proper, separated, and of finite type. It is finitely presented when the defining closed immersion is finitely presented, as happens over a locally noetherian base. A quasi-projective morphism is separated and of finite type; it is finitely presented under the analogous finiteness hypothesis. It need not be proper because points may escape through the omitted boundary.

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

Over a field, finite-dimensional sections $V\subseteq H^0(X,\mathcal L)$ define an immersion precisely when they separate points and tangent directions. Scheme-theoretically, this means that for every length-two closed subscheme $Z\subseteq X$, the restriction

$$
V\longrightarrow H^0(Z,\mathcal L|_Z)
$$

is surjective. Two distinct reduced points test separation of points; a doubled point tests tangent directions. This formulation also catches nilpotents, which a set-theoretic injectivity test misses.

**Immersion criterion.** Suppose $X$ is of finite type over a field and $V$ generates $\mathcal L$. The associated map $X\to\mathbf P(V)$ is a locally closed immersion if the restriction map above is onto for every length-two subscheme. If $X$ is proper, it is a closed immersion.

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

Conversely, if this vanishing and eventual generation hold for all coherent ideals, then $\mathcal L$ is ample. Chapter 6 proves the forward implication from the standard affine cover of projective space.

### 4.5 Tensor powers and operations

If $\mathcal L$ is ample, every positive power $\mathcal L^d$ is ample: replace each defining section by a power. Conversely, if $\mathcal L^d$ is ample for one $d>0$, then $\mathcal L$ is ample because sufficiently large powers in each residue class modulo $d$ are obtained by tensoring with one of finitely many fixed powers.

If $\mathcal L$ is ample and $\mathcal M$ is invertible, then $\mathcal L^n\otimes\mathcal M$ is ample for all sufficiently large $n$. Apply the generation criterion to the finitely many twists needed to generate $\mathcal M$ and its inverse. In particular, ampleness is insensitive to a bounded twist at high degree.

On a quasi-compact finite-type $X\to S$, an ample $\mathcal L$ has a power which is relatively very ample. If $X\to S$ is proper, that power gives a closed immersion, hence $X\to S$ is projective. The proof chooses finitely many affine nonvanishing charts, then enough sections to generate their coordinate algebras and to distinguish overlaps. A common tensor power packages the functions as ratios of homogeneous sections. This is the fundamental passage from local affine control to one global embedding.

If $\mathcal L$ and $\mathcal M$ are ample relative to $S$, then $\mathcal L\otimes\mathcal M$ is ample. One can either refine their affine nonvanishing covers and tensor the corresponding sections, or use eventual generation. Pullback along a finite morphism preserves ampleness; along an arbitrary morphism it need not, as the pullback to a positive-dimensional fiber of a constant map may become trivial.

## 5. Base change and descent

### 5.1 Pullback of positivity

Let $g:T\to S$. If $\mathcal L$ is very ample for $X\to S$, then $\mathcal L_T$ is very ample for $X_T\to T$: base change the chosen immersion. If $\mathcal L$ is ample, then $\mathcal L_T$ is ample. For the latter statement, base change of an affine nonvanishing open is affine, and the pulled-back sections cover.

These claims require no flatness. They should be distinguished from cohomological base change, where flatness or vanishing hypotheses matter. Positivity is visible on explicit affine charts and therefore survives arbitrary scalar extension.

Projectivity and quasi-projectivity likewise survive arbitrary base change. Consequently every fiber of a projective family is projective and every restriction of a relatively ample bundle is ample. The converses are subtler because fiberwise data need not be uniform.

### 5.2 Faithfully flat descent of very ampleness

The useful converse requires an actual faithfully flat cover of the base.

**Descent theorem.** Let $f:X\to S$ be quasi-compact and quasi-separated, let $\mathcal L$ be invertible, and let $g:S'\to S$ be faithfully flat and quasi-compact. If $\mathcal L_{S'}$ is very ample relative to $S'$, then $\mathcal L$ is very ample relative to $S$. If $f$ is proper and of finite presentation, the descended immersion is closed and finite-dimensional locally on $S$.

Here the line bundle already lives on $X$; only its property is being tested. This is not a claim that an arbitrary line bundle on $X_{S'}$ descends without descent data.

The proof is local on $S$, so take $S=\operatorname{Spec}A$ and refine $S'$ by finitely many affine opens. Flat base change for degree-zero sections on a quasi-compact quasi-separated scheme gives

$$
\Gamma(X,\mathcal L^n)\otimes_A A'
\simeq\Gamma(X_{S'},\mathcal L_{S'}^n).
$$

A finite family of sections on $X_{S'}$ supplies affine standard opens and generates their coordinate algebras by ratios. Each section and each finite relation involves only finitely many coefficients. Faithfully flat descent converts the relevant finite submodules and surjections to data over $A$ after enlarging the family if necessary. Surjectivity descends because a cokernel vanishing after faithful tensor product was already zero. The property that the associated morphism is an immersion also descends: its diagonal condition and its affine chart ring maps can be checked faithfully flatly. The descended finite linear system therefore realizes $\mathcal L$ as the pullback of $\mathcal O(1)$.

For proper $f$, the immersion is proper and hence closed. Finite presentation ensures that finitely many sections and equations suffice uniformly; without a finiteness condition the first assertion still uses a possibly infinite projective bundle, while the stated finite-dimensional conclusion can fail.

### 5.3 Descent of ampleness and projectivity

Under the same quasi-compact and quasi-separated hypotheses, relative ampleness is fpqc-local on the base:

$$
\mathcal L\text{ is }f\text{-ample}
\quad\Longleftrightarrow\quad
\mathcal L_{S'}\text{ is }f_{S'}\text{-ample}.
$$

Only the reverse implication needs proof. Quasi-compactness gives a common power of $\mathcal L_{S'}$ that is very ample on finitely many pieces. Descent of the affine nonvanishing cover, or equivalently the generation criterion plus faithful descent of surjectivity, proves ampleness below.

Projectivity also descends under a faithfully flat quasi-compact base change for morphisms of finite presentation, provided the descended $X\to S$ is proper. Indeed, the projective base change supplies a relatively ample bundle only if that bundle carries descent data. An embedding line bundle chosen arbitrarily upstairs need not descend. A safe and frequently used statement is therefore:

**Projectivity descent with a polarization.** Let $f:X\to S$ be proper and of finite presentation, and let $\mathcal L$ be a line bundle on $X$. If some fpqc base change makes $\mathcal L$ relatively ample, then $\mathcal L$ is relatively ample and $f$ is projective.

There are broader descent theorems for projective morphisms, but this polarized form records the datum used in moduli problems and avoids concealing an obstruction in the Picard group.

### 5.4 Necessary hypotheses and failures

Faithfulness cannot be dropped. Restricting to an open subset of $S$ may erase a bad fiber, so positivity over that open says nothing at omitted points. Flatness cannot be replaced by a merely surjective map: nilpotent thickenings can make module surjections and immersion conditions invisible.

Quasi-compactness provides finite linear systems. An infinite disjoint union may be fiberwise embeddable with unbounded projective dimension but admit no one finite-rank ambient bundle. Quasi-separatedness is what makes sections commute with flat base change in the form used above.

Finally, “very ample after taking a power” descends to ampleness, but it need not show that the original bundle is very ample if only the power is known upstairs. For example, $\mathcal O_{\mathbf P^1}(2)$ is very ample while $\mathcal O_{\mathbf P^1}(1)$ is also very ample, but on other varieties a square can embed when the original bundle has too few sections. Tensor roots do not inherit separation automatically.

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

for $n\geq0$, a free $A$-module of rank $\binom{n+r}{r}$. The top cohomology for negative twists is generated by Laurent monomials in which every variable has negative exponent. This also proves, over a field,

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

For $n\gg0$,

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

After embedding by a power of $\mathcal L$, a finite graded resolution expresses the Euler characteristic as an integral linear combination of $\binom{t+r-a}{r}$. This is polynomial. Additivity handles the resolution, and uniqueness follows because a polynomial vanishing at all large integers is zero.

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

The polynomial belongs to $(\mathcal F,\mathcal L)$. Replacing $\mathcal L$ by $\mathcal L^q$ replaces $P(t)$ by $P(qt)$. Different ample bundles can produce different leading degrees. A moduli problem must therefore fix an embedding or polarization before specifying a Hilbert polynomial.

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

A safe converse is local over a reduced base.

**Numerical flatness criterion.** Let $S$ be reduced and locally noetherian, $f:X\to S$ projective, and $\mathcal F$ coherent. Assume $\mathcal F$ has no associated point lying over a nowhere-dense closed subset of $S$. Then $\mathcal F$ is $S$-flat if and only if its fiber Hilbert polynomial is locally constant.

Generic flatness gives a dense open of flatness. At a first failure on the boundary, the local flatness criterion produces a nonzero kernel after passage to a residue field. A high twist and Serre vanishing turn that kernel into a positive jump of the Hilbert function. The associated-point hypothesis prevents a vertical submodule with zero generic fiber from escaping this test.

Reducedness matters. On $\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ there is only one topological fiber. The module $k$ has a constant one-point fiber but is not flat. Fiber polynomials cannot see an infinitesimal direction when the base has no second point in that direction.

### 8.4 Flattening strata

**Flattening theorem.** Let $S$ be noetherian, $f:X\to S$ projective, $\mathcal L$ relatively very ample, and $\mathcal F$ coherent. For every numerical polynomial $P$ there is a locally closed subscheme $S_P\subseteq S$ such that $T\to S$ factors through $S_P$ exactly when $\mathcal F_T$ is flat over $T$ with fiber polynomial $P$. These strata cover the underlying set, and finitely many meet a quasi-compact open.

Choose $m$ beyond a regularity bound. The locus where $f_*\mathcal F(m)$ is locally free of rank $P(m)$ is defined by Fitting ideals. Impose the corresponding conditions in enough consecutive degrees and compatibility with multiplication by linear forms. They force the high-degree graded module to be flat, hence the associated sheaf to be flat. The universal property of Fitting ideals supplies the asserted factorization of schemes, including nilpotent test schemes.

The strata need not be open. Once a finitely presented family is flat, flatness persists on an open neighborhood; forcing an arbitrary family to become flat can impose closed equations.

## 9. Projective embeddings of curves and abelian schemes

### 9.1 Embedding projective curves

Let $C$ be a proper curve over a field and $\mathcal L$ ample. Serre's criterion makes $\mathcal L^n$ very ample for $n\gg0$. For a length-two subscheme $Z\subset C$, the sequence

$$
0\to\mathcal I_Z\otimes\mathcal L^n
\to\mathcal L^n\to\mathcal L^n|_Z\to0
$$

and vanishing of $H^1$ show that sections separate $Z$. A regularity bound for all length-two subschemes gives one exponent for points and tangent vectors simultaneously. The resulting immersion is closed because $C$ is proper.

Smooth proper curves have ample bundles. Choose a nonempty finite effective divisor $D$. Its complement is affine, and powers of its canonical section, together with analogous divisors moving through the finitely many remaining points, give an affine nonvanishing cover. Hence $\mathcal O_C(D)$ is ample after enlarging $D$. Every smooth proper curve over a field has a closed point, so it is projective.

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

### 9.3 Abelian schemes and ample cubical bundles

Let $a:A\to S$ be an abelian scheme: a smooth proper group scheme with geometrically connected fibers. Projectivity comes from a polarization, not from properness alone. A line bundle $\mathcal L$ is rigidified when $e^*\mathcal L\simeq\mathcal O_S$, and symmetric when $[-1]^*\mathcal L\simeq\mathcal L$.

An invertible sheaf defines

$$
\lambda_{\mathcal L}:A\to A^\vee,\qquad
x\mapsto t_x^*\mathcal L\otimes\mathcal L^{-1}.
$$

If $\mathcal L$ is relatively ample, this is fiberwise a finite surjective homomorphism, hence a polarization. Conversely a polarization is locally induced by a relatively ample rigidified bundle. When the inducing bundle is included in the data, it supplies a projective embedding after a power.

### 9.4 The theorem of the cube and very ampleness

For a rigidified bundle on $A$, the alternating tensor product of its pullbacks along the seven nonempty partial sums on $A^3$ is canonically trivial. Rigidity proves this: its associated map to the dual vanishes in each variable, while rigidification trivializes it on the coordinate hyperplanes. One consequence is

$$
[m]^*\mathcal L\simeq
\mathcal L^{m(m+1)/2}\otimes[-1]^*\mathcal L^{m(m-1)/2}.
$$

For symmetric $\mathcal L$, this is $[m]^*\mathcal L\simeq\mathcal L^{m^2}$.

**Abelian embedding theorem.** Over a noetherian base, if $\mathcal L$ is relatively ample on an abelian scheme, then $\mathcal L^3$ is relatively very ample. If $\mathcal L$ is symmetric, $\mathcal L^2$ is relatively generated, but it can fail to be very ample.

After a faithfully flat extension, translate effective sections. For distinct geometric points, a translate can vanish at one and not the other; ampleness makes the common translation stabilizer finite, and products of three translates eliminate it. Translated local equations also separate tangent vectors at the identity. The cube identity identifies these products as sections of $\mathcal L^3$. They separate every length-two subscheme; properness closes the immersion, and very ampleness descends. The exponent three works in every characteristic. A symmetric theta bundle may identify $x$ and $-x$, explaining why lower powers are unsafe.

## 10. Finite flat families and effective divisors

### 10.1 Families of length $d$

A closed subscheme $Z\subseteq X_T$ is a family of length $d$ over $T$ if $Z\to T$ is finite locally free of rank $d$. Every geometric fiber is zero-dimensional of scheme-theoretic length $d$. Rank is stronger than counting points: one nonreduced point can have length $d$.

If $X\to S$ is separated, these families form a set-valued functor: an isomorphism between two closed subschemes over $X_T$ is unique. A tuple of sections produces the disjoint union of their graphs only while the graphs remain disjoint. When points collide, the union loses rank; retaining multiplicity requires an infinitesimal thickening.

### 10.2 Relative effective Cartier divisors

An effective Cartier divisor $D\subset C$ has invertible ideal locally generated by a non-zero-divisor. Its line bundle is $\mathcal O_C(D)=\mathcal I_D^{-1}$, with a canonical section vanishing exactly on $D$.

A relative effective Cartier divisor of degree $d$ on $C\to T$ is an effective Cartier divisor finite locally free of rank $d$ over $T$. If $C\to T$ is flat, fiber length $d$ plus the Cartier condition implies finite local freeness by the local flatness criterion applied to

$$
0\to\mathcal O_C(-D)\to\mathcal O_C\to\mathcal O_D\to0.
$$

On a singular curve, finite does not imply Cartier. The ideal $(x,y)$ of the node in $k[x,y]/(xy)$ is not principal.

### 10.3 Divisors on smooth relative curves

If $C\to S$ is smooth of pure relative dimension one, every finite locally free closed subscheme $D\subset C_T$ is a relative effective Cartier divisor. Fiberwise its ideal has codimension one in a regular curve and is generated by a non-zero-divisor. Nakayama lifts the generator, and flatness shows it remains regular. Conversely, a relative divisor of degree $d$ is finite locally free by definition. Hence the two functors agree:

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

The $d$th power $X^d_S$ parametrizes ordered $d$-tuples. The symmetric group $\mathfrak S_d$ permutes the factors; forgetting order should produce the symmetric power. Quotients by finite groups exist comfortably for quasi-projective schemes.

**Finite quotient theorem.** Let a finite group $G$ act on a quasi-projective $S$-scheme $Y$. Then there is a categorical quotient

$$
q:Y\longrightarrow Y/G
$$

in $S$-schemes. The map $q$ is integral, finite and surjective. Formation of the quotient commutes with flat base change. It commutes with arbitrary base change when the relevant invariant algebras do, in particular for permutation quotients of powers of a quasi-projective scheme.

For an invariant affine open $V=\operatorname{Spec}B$, take $\operatorname{Spec}B^G$. Every $b\in B$ is integral over $B^G$, since it satisfies $\prod_{g\in G}(T-gb)$. Quasi-projectivity supplies enough $G$-stable affine neighborhoods: choose an affine neighborhood of an orbit in a projective embedding and intersect its finitely many translates. The affine quotients glue because invariant localization agrees on invariant principal opens. The categorical property follows affine-locally.

In general, invariants do not commute with a nonflat scalar extension when the group order is not invertible. Thus the quotient of an arbitrary quasi-projective $X$ is asserted here to commute with flat base change only. For smooth relative curves, the divisor interpretation below proves the stronger compatibility with every base change.

Define

$$
\operatorname{Sym}^d_S(X)=X^d_S/\mathfrak S_d.
$$

It is quasi-projective over $S$ when $X$ is; it is projective when $X$ is projective, because $X^d$ is projective and a finite image of a projective scheme is projective. For $d=0$ it is $S$, and for $d=1$ it is $X$.

### 11.2 Sheaf quotients and orbit functors

The categorical quotient $\operatorname{Sym}^d(X)$ does not generally represent the presheaf

$$
T\longmapsto X(T)^d/\mathfrak S_d.
$$

A $T$-point of the quotient need not be represented by an ordered tuple over $T$. If the quotient map $X^d\to\operatorname{Sym}^d(X)$ is fppf, then the symmetric power does represent the fppf sheafification of that orbit presheaf: locally one lifts to an ordered tuple, and two lifts differ locally by permutations. This applies on the free locus and, by the local monic-polynomial description, to powers of a smooth relative curve. For a general higher-dimensional $X$, the finite quotient map need not be flat, so one should retain only its categorical universal property unless an appropriate sheaf statement has been proved.

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

Configuration space is the reduced, collision-free part of a symmetric power. If $X\to S$ is smooth of relative dimension $r$, then $\operatorname{Conf}_d(X)\to S$ is smooth of relative dimension $dr$, and so is its finite étale quotient $\operatorname{UConf}_d(X)$. A point is an unordered finite étale subscheme of rank $d$.

The complement is the big diagonal. On a relative curve it is a divisor after suitable hypotheses; in higher dimension it has codimension equal to the relative dimension. Passing across it permits collisions and creates nonreduced divisors on a curve.

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

To prove surjectivity, work étale-locally on $C_T$ with a smooth parameter $z$. A finite flat Cartier divisor has algebra locally free with basis $1,z,\ldots,z^{d-1}$ after shrinking, and its equation is a unique monic polynomial

$$
z^d-a_1z^{d-1}+\cdots+(-1)^da_d.
$$

The coefficients define a map to the affine chart of the symmetric power. Uniqueness makes the local maps glue. Injectivity follows because the monic equation recovers the divisor. The construction commutes with base change and therefore proves the functorial statement, not just a bijection on geometric points.

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

which are associative, commutative, and compatible with base change. The disjoint union over $d\geq0$ is thus a graded commutative monoid scheme, though not one finite-type scheme.

For a nonsmooth curve, $\operatorname{Sym}^d(C)$ still exists if $C$ is quasi-projective, but it represents cycles rather than all finite flat subschemes. There may be no universal closed subscheme on $C\times\operatorname{Sym}^d(C)$. At a singularity several nonisomorphic embedded length-$d$ structures can have the same cycle. The Hilbert scheme retains these structures; the symmetric power forgets them.

## 12. The Hilbert functors needed here

### 12.1 Precise functors

Fix a locally noetherian scheme $S$, a projective finitely presented morphism $X\to S$, and a relatively very ample $\mathcal O_X(1)$. For a numerical polynomial $P\in\mathbf Q[t]$, define the contravariant functor

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

Embed $X\subseteq\mathbf P^r_S$. Suppose first that $S=\operatorname{Spec}A$. For a family $Z$ with polynomial $P$ and $n$ sufficiently large, vanishing gives a quotient of locally free modules

$$
H^0(\mathbf P^r_A,\mathcal O(n))\otimes_A\mathcal O_T
\twoheadrightarrow p_*\mathcal O_Z(n),
$$

whose target has rank $P(n)$. It defines a morphism from $T$ to the Grassmannian

$$
G_n=\operatorname{Gr}\!\left(P(n),
H^0(\mathbf P^r_S,\mathcal O(n))\right).
$$

One degree alone remembers only a vector-space quotient, not an ideal. Multiplication must be compatible:

$$
I_n\cdot H^0(\mathcal O(m))\subseteq I_{n+m}.
$$

A regularity bound says that for fixed $P$ there is $m(P,r)$ such that every saturated homogeneous ideal with polynomial $P$ is $m$-regular and is generated from degree $m$ onward. Therefore the degree-$m$ quotient, together with the single next-degree rank and multiplication condition, recovers the entire saturated ideal.

On $G_m$ let $\mathcal K_m$ be the kernel of the universal quotient. Multiplication gives

$$
\mathcal K_m\otimes H^0(\mathcal O(1))
\longrightarrow H^0(\mathcal O(m+1))\otimes\mathcal O_{G_m}.
$$

Require its image to lie in a subbundle of codimension $P(m+1)$ and require the induced quotient to be locally free of rank $P(m+1)$. Determinantal equations impose these conditions. The resulting closed subscheme carries a universal homogeneous ideal and hence a universal closed subscheme of projective space.

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

with $r\geq a_1\geq\cdots\geq a_s\geq0$. Every saturated ideal with polynomial $P$ is $s$-regular.

The proof repeatedly takes a general hyperplane. Finite differences replace $P$ by the polynomial of the hyperplane section. Macaulay's elementary growth estimate for a graded quotient says that, among spaces of a fixed codimension in degree $n$, the lexicographic monomials have maximal possible next-degree growth. Writing an integer in its unique binomial expansion makes this estimate explicit. Equality at one step forces equality thereafter: the ideal has no new generators beyond that step. Induction on dimension reconstructs the displayed expansion and gives the bound $s$. This proof is characteristic-free because it counts monomials and uses no averaging.

**Hilbert representability theorem.** Under the hypotheses of Section 12.1, $\operatorname{Hilb}^P_{X/S}$ is represented by a projective finitely presented $S$-scheme

$$
\operatorname{Hilb}^P(X/S).
$$

For projective space, take the closed determinantal locus in $G_s$ just constructed. The universal ideal is flat with polynomial $P$ because regularity controls all later degrees and the Grassmannian quotients are locally free with the prescribed ranks. Conversely every family yields its degree-$s$ quotient and lands uniquely in that locus. These constructions are inverse after every base change, proving representability.

For a closed $X\subseteq\mathbf P^r_S$ with ideal $\mathcal I_X$, require the universal ideal of $Z$ to contain $\mathcal I_X$. In degree at least the common regularity bound, containment is the vanishing of a map between finite locally free modules, hence a closed condition. This cuts out $\operatorname{Hilb}^P(X/S)$. Projectivity comes from the Grassmannian, and finite presentation from the finite determinantal equations.

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

Under this isomorphism their universal families agree with $\Delta_d$. In particular the symmetric power is smooth over $S$ of relative dimension $d$. Smoothness can be seen locally from monic coefficients $a_1,\ldots,a_d$, which give affine coordinates even when roots collide.

For singular curves, there is still a proper Hilbert-to-cycle morphism when the curve is projective, and it is an isomorphism over the locus of divisors avoiding singular points. Over a singular point its fiber may contain several embedded ideals with the same multiplicities. The equality above is therefore a theorem about smooth relative curves, not about all one-dimensional schemes.

## 13. Universal constructions for later geometry

### 13.1 Graphs and spaces of morphisms

If $Y\to S$ is separated, a morphism $u:X_T\to Y_T$ has a closed graph

$$
\Gamma_u\subseteq X_T\times_TY_T.
$$

Suppose $X\to S$ is projective flat and finitely presented and $Y\to S$ is projective. Fix a Hilbert polynomial $P$ for graphs in a chosen projective embedding of $X\times_SY$. The Hilbert scheme of that product represents all flat closed families with polynomial $P$. The graph condition is open: projection $\Gamma\to X_T$ must be an isomorphism, and for finitely presented proper morphisms being an isomorphism is open on the base once checked on fibers. Hence a locally finite-type open subscheme represents morphisms whose graphs have polynomial $P$.

This construction is used only with bounded graph polynomials. There is no single finite-type scheme of all morphisms of arbitrary degree. Fixing degree or Hilbert polynomial is the finiteness datum that makes a parameter space possible.

### 13.2 Closed loci inside parameter spaces

Many moduli conditions become closed conditions on a Hilbert scheme:

- containment in a fixed closed subscheme is closed;
- invariance under a fixed morphism is closed when expressed by equality of two maps on the universal family;
- incidence with a fixed closed subscheme is closed when the universal family is proper over the parameter space;
- equality of two morphisms from a flat proper universal family to a separated target is closed when the source has schematically dense fibers.

Open conditions include avoiding a fixed closed subset, smoothness of fibers, geometric reducedness, and the graph condition. Locally closed conditions are built by imposing a closed equation and then an open nondegeneracy requirement.

These assertions concern schemes, not just their points. For instance, “the equation vanishes on the universal family” means a morphism of coherent sheaves is zero; it cuts out a scheme via its coefficient ideal and detects infinitesimal test schemes.

### 13.3 Projective parameter spaces for curve families

Fix $r$ and a polynomial $P(n)=en+c$. The scheme $\operatorname{Hilb}^P(\mathbf P^r_S/S)$ carries the universal projective flat family. The open locus on which the fibers are smooth of pure dimension one parametrizes smooth embedded curves with that polynomial. If one also requires geometric connectedness, this is open in a proper smooth family. Additional marked effective divisors of degree $d$ are parametrized by the relative symmetric power of the universal curve.

This is the precise Hilbert apparatus needed for embedded curves: a fixed polynomial, its universal family, open smooth and connected loci, and relative length-$d$ subschemes. Abelian families can likewise be placed in a Hilbert scheme after choosing a relatively very ample power of a polarization; group laws are morphisms whose graphs live in bounded Hilbert loci, and the identity and associativity equations cut out closed loci. Establishing the full moduli problem requires further descent and rigidity, but no broader parameter functor is needed here.

### 13.4 A boundary checklist

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

For a projective flat family over a locally noetherian base, high twisted pushforwards are locally free and commute with base change. The fiber Hilbert polynomial is locally constant. Fixing that polynomial gives a projective finitely presented Hilbert scheme with a universal flat closed family. The constant polynomial $d$ gives the intrinsic space of finite locally free length-$d$ subschemes.

For a smooth quasi-projective relative curve, this length-$d$ Hilbert scheme is the symmetric power, represents relative effective Cartier divisors, is smooth of relative dimension $d$, and carries a universal finite flat divisor. Its reduced open is unordered configuration space with a finite étale universal family. These properties persist under arbitrary base change.

An ample bundle embeds a projective curve after a high power. A relatively ample bundle on an abelian scheme has a very ample cube, with the theorem of the cube controlling translations and base change. Thus curves and polarized abelian schemes enter fixed projective spaces, where Hilbert polynomials and universal parameter schemes can control their variation.

### 14.3 Conclusion

Projective geometry over a base is the art of making choices uniform. A homogeneous coordinate in one fiber becomes a twisting sheaf on the whole family. An embedding chosen point by point becomes one relatively very ample power. A fluctuating dimension becomes the rank of a vector bundle when flatness is present. An unordered collection of points becomes a symmetric power, and an embedded family becomes a point of a Hilbert scheme.

The hypotheses are part of the geometry. Noetherian finiteness makes equations bounded; properness turns immersions into closed immersions; flatness prevents specialization from changing the polynomial; smoothness of a curve turns finite subschemes into Cartier divisors; separatedness makes graphs closed; and quasi-projectivity makes finite quotients exist as schemes. With these boundaries respected, ample bundles, Hilbert polynomials, symmetric powers, and the selected Hilbert schemes form a single coherent language for the projective families used throughout arithmetic geometry.
