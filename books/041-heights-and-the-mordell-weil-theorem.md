# Heights, Mordell--Weil, and the Faltings--Tate Reduction

## Contents

1. [Arithmetic size and the missing half of descent](#1-arithmetic-size-and-the-missing-half-of-descent)
   - [Why a group quotient is not enough](#11-why-a-group-quotient-is-not-enough)
   - [Standing conventions](#12-standing-conventions)
   - [The architecture of the proof](#13-the-architecture-of-the-proof)
2. [Absolute values and projective height](#2-absolute-values-and-projective-height)
   - [Normalized places and the product formula](#21-normalized-places-and-the-product-formula)
   - [The height of a projective point](#22-the-height-of-a-projective-point)
   - [Change of field and elementary estimates](#23-change-of-field-and-elementary-estimates)
   - [Concrete computations](#24-concrete-computations)
3. [Northcott finiteness](#3-northcott-finiteness)
   - [Why bounded size should be finite](#31-why-bounded-size-should-be-finite)
   - [Algebraic numbers of bounded degree](#32-algebraic-numbers-of-bounded-degree)
   - [Projective Northcott](#33-projective-northcott)
   - [Subvarieties and affine coordinates](#34-subvarieties-and-affine-coordinates)
4. [The Weil height machine](#4-the-weil-height-machine)
   - [Why line bundles replace coordinates](#41-why-line-bundles-replace-coordinates)
   - [Heights from projective embeddings](#42-heights-from-projective-embeddings)
   - [Functoriality, tensor products, and bounded ambiguity](#43-functoriality-tensor-products-and-bounded-ambiguity)
   - [Divisors and local Weil functions](#44-divisors-and-local-weil-functions)
   - [Ample heights and Northcott](#45-ample-heights-and-northcott)
5. [Heights on abelian varieties](#5-heights-on-abelian-varieties)
   - [Translation and addition](#51-translation-and-addition)
   - [Symmetric and antisymmetric parts](#52-symmetric-and-antisymmetric-parts)
   - [The bounded quadratic defect](#53-the-bounded-quadratic-defect)
   - [Polarizations and choices](#54-polarizations-and-choices)
6. [Canonical Néron--Tate heights](#6-canonical-néron--tate-heights)
   - [The limiting construction](#61-the-limiting-construction)
   - [Independence and uniqueness](#62-independence-and-uniqueness)
   - [Quadraticity](#63-quadraticity)
   - [Nonnegativity and the zero locus](#64-nonnegativity-and-the-zero-locus)
   - [Local Néron functions and the global sum](#65-local-néron-functions-and-the-global-sum)
7. [The height pairing](#7-the-height-pairing)
   - [Polarization of a quadratic function](#71-polarization-of-a-quadratic-function)
   - [Bilinearity and Cauchy--Schwarz](#72-bilinearity-and-cauchy--schwarz)
   - [The Euclidean space of rational points](#73-the-euclidean-space-of-rational-points)
   - [Changing the polarization and isogenies](#74-changing-the-polarization-and-isogenies)
8. [Mordell--Weil by height descent](#8-mordell--weil-by-height-descent)
   - [The abstract descent lemma](#81-the-abstract-descent-lemma)
   - [Applying weak Mordell--Weil](#82-applying-weak-mordell--weil)
   - [The Mordell--Weil theorem](#83-the-mordell--weil-theorem)
   - [Torsion, rank, and lattices](#84-torsion-rank-and-lattices)
9. [Examples and diagnostic boundaries](#9-examples-and-diagnostic-boundaries)
   - [Projective space and rational numbers](#91-projective-space-and-rational-numbers)
   - [Elliptic curves](#92-elliptic-curves)
   - [Products](#93-products)
   - [Why the hypotheses matter](#94-why-the-hypotheses-matter)
10. [The finite-generation package for quotients](#10-the-finite-generation-package-for-quotients)
    - [Abelian subvarieties and quotients](#101-abelian-subvarieties-and-quotients)
    - [Base change, trace, and restriction](#102-base-change-trace-and-restriction)
    - [The Eisenstein-quotient input](#103-the-eisenstein-quotient-input)
11. [From point heights to moduli heights](#11-from-point-heights-to-moduli-heights)
    - [The exact downstream question](#111-the-exact-downstream-question)
    - [Why Mordell--Weil does not answer it](#112-why-mordell--weil-does-not-answer-it)
    - [The noncircular proof architecture](#113-the-noncircular-proof-architecture)
12. [The Faltings height and the moduli comparison](#12-the-faltings-height-and-the-moduli-comparison)
    - [The metrized Hodge line](#121-the-metrized-hodge-line)
    - [Base change and stable height](#122-base-change-and-stable-height)
    - [The isogeny formula](#123-the-isogeny-formula)
    - [Theta coordinates and moduli height](#124-theta-coordinates-and-moduli-height)
    - [What the comparison actually proves](#125-what-the-comparison-actually-proves)
13. [The Faltings finiteness gate](#13-the-faltings-finiteness-gate)
    - [The required Shafarevich statement](#131-the-required-shafarevich-statement)
    - [Level fields and integral moduli points](#132-level-fields-and-integral-moduli-points)
    - [The missing arithmetic height bound](#133-the-missing-arithmetic-height-bound)
    - [Why integrality is not a substitute](#134-why-integrality-is-not-a-substitute)
    - [Exact prerequisite ledger](#135-exact-prerequisite-ledger)
14. [From Faltings finiteness to finite isogeny classes](#14-from-faltings-finiteness-to-finite-isogeny-classes)
    - [Good reduction is preserved by isogeny](#141-good-reduction-is-preserved-by-isogeny)
    - [The finite-isogeny-class consequence](#142-the-finite-isogeny-class-consequence)
    - [The precise conditional input](#143-the-precise-conditional-input)
15. [Tate lattices and semisimplicity](#15-tate-lattices-and-semisimplicity)
    - [Stable lattices are isogeny quotients](#151-stable-lattices-are-isogeny-quotients)
    - [Finite isogeny classes give finite lattice type](#152-finite-isogeny-classes-give-finite-lattice-type)
    - [Tate's lattice lemma](#153-tates-lattice-lemma)
    - [Conditional rational Tate-module semisimplicity](#154-conditional-rational-tate-module-semisimplicity)
16. [The exact cohomological export](#16-the-exact-cohomological-export)
    - [Curves and Jacobians](#161-curves-and-jacobians)
    - [Coefficient extension, summands, and multiplicity spaces](#162-coefficient-extension-summands-and-multiplicity-spaces)
    - [The Hom--Tate boundary](#163-the-hom--tate-boundary)
    - [The packet-carrier array](#164-the-packet-carrier-array)
17. [Synthesis](#17-synthesis)
    - [The two logical chains](#171-the-two-logical-chains)
    - [Normalization and dependency ledger](#172-normalization-and-dependency-ledger)
    - [Conclusion](#173-conclusion)

## 1. Arithmetic size and the missing half of descent

Descent reduces rational points modulo multiplication to finitely many classes. It does not, by itself, say that the entire group is generated by finitely many points. The missing ingredient is a notion of size which grows quadratically under multiplication and which admits only finitely many rational points below any fixed bound. This chapter explains why these two properties fit together and fixes the hypotheses under which they will be proved.

### 1.1 Why a group quotient is not enough

Let $A$ be an abelian variety over a number field $K$. Weak Mordell--Weil, established in Book 40, says that

$$
A(K)/mA(K)
$$

is finite for every integer $m\geq 2$. Choose representatives $R_1,\ldots,R_s$. Every $P\in A(K)$ can then be written

$$
P=R_i+mQ. \tag{1.1}
$$

If a size function behaves like a norm and satisfies $\|mQ\|=m\|Q\|$, then (1.1) makes $Q$ smaller than $P$ once $P$ is large. Repeating the operation eventually reaches a bounded region. If that region contains only finitely many rational points, the representatives and the bounded points generate the group.

Both italicized ideas require proof. The additive group $\mathbf Q$ satisfies $\mathbf Q/m\mathbf Q=0$ and is not finitely generated, so the finite quotient alone cannot prevent endless division. An ordinary projective height has the necessary finiteness property but only transforms under multiplication up to a bounded error. The Néron--Tate limiting process removes that error and creates an exact quadratic function.

### 1.2 Standing conventions

Throughout, $K$ is a number field of degree $d=[K:\mathbf Q]$. Its set of places is $M_K$. If $v$ lies over the ordinary place $w$ of $\mathbf Q$, put

$$
n_v=[K_v:\mathbf Q_w].
$$

We use the usual absolute value on $\mathbf R$ and the usual modulus on $\mathbf C$. As described precisely in Section 2.1, a complex place has local degree $2$; we do not instead square its absolute value. At a finite place over $p$, $|p|_v=p^{-1}$. This separates the absolute-value normalization from the local multiplicity and prevents the common factor-of-two error at complex places.

An **abelian variety** is a smooth, proper, geometrically connected group variety. A line bundle $L$ on an abelian variety is **symmetric** if $[-1]^*L\simeq L$. It is ample in the ordinary projective sense. Book 8 provides projective embeddings from high powers of ample bundles; Book 35 provides the theorem of the cube, symmetric ample bundles, and the homomorphism $\lambda_L:A\to A^\vee$ associated with $L$.
The Minkowski lattice and covolume normalization used once in the moduli-field reduction are
those of Book 4. Book 2 supplies finiteness of local extensions of bounded degree.

All heights in this book are logarithmic. Their exponential versions are denoted by $H=e^h$. An equality $h=h'+O(1)$ means that $h-h'$ is bounded on the stated set of algebraic points; the bound may depend on the variety, line bundles, morphisms, and ground field, but not on the varying point.

### 1.3 The architecture of the proof

The Mordell--Weil argument has four genuinely different layers:

$$
\begin{array}{c}
\text{product formula}\Longrightarrow\text{projective height}\Longrightarrow\text{Northcott finiteness},\\
\text{ample line bundle}\Longrightarrow\text{Weil height }h_L\text{, well defined modulo }O(1),\\
[m]^*L\simeq L^{m^2}\Longrightarrow
\widehat h_L([m]P)=m^2\widehat h_L(P),\\
\text{weak Mordell--Weil}+\text{Northcott}+\text{quadraticity}
\Longrightarrow A(K)\text{ finitely generated}.
\end{array}
$$

The first layer is arithmetic and works on projective space. The second transports it to projective varieties. The third uses the special geometry of an abelian variety. The last is a group-theoretic descent whose termination is supplied by the first three. Keeping the layers separate ensures that finite generation is not smuggled into the proof of positivity or finiteness.

The second half of the book asks a different height question. It replaces a point of $A$ by
the moduli point of $A$, replaces the Néron--Tate metric by the metrized Hodge line, and seeks a
uniform height bound from prescribed good reduction. Once Faltings--Shafarevich finiteness is
available, Tate's stable-lattice argument gives rational Tate-module semisimplicity. Chapters
11--16 prove every implication after finite isogeny classes and identify the exact height,
compactification, slope, factor-cancellation, and descent inputs absent from the present
prerequisites; they do not disguise those missing deep inputs as an application of ordinary
Northcott finiteness.

## 2. Absolute values and projective height

Projective coordinates are only defined up to a common scalar. A useful size must therefore be unchanged when every coordinate is multiplied by the same element. The product formula is exactly the cancellation law that makes this possible.

### 2.1 Normalized places and the product formula

For a real embedding $\sigma:K\hookrightarrow\mathbf R$, set $|x|_v=|\sigma(x)|$ and $n_v=1$. For a conjugate pair of complex embeddings, choose one $\sigma:K\hookrightarrow\mathbf C$, set $|x|_v=|\sigma(x)|$, and put $n_v=2$. For a finite place associated with a prime ideal $\mathfrak p$ over $p$, normalize $|p|_v=p^{-1}$ and put $n_v=[K_v:\mathbf Q_p]$. Equivalently,

$$
|x|_v=N\mathfrak p^{-\operatorname{ord}_{\mathfrak p}(x)/n_v}.
$$

With these conventions the product formula is

$$
\sum_{v\in M_K}n_v\log|x|_v=0
\qquad(x\in K^\times). \tag{2.1}
$$

For a finite place, $n_v\log|x|_v=-\operatorname{ord}_{\mathfrak p}(x)\log N\mathfrak p$. Summing this over finite places gives minus the logarithm of the absolute norm of the principal fractional ideal $(x)$. The archimedean sum is the logarithm of $|N_{K/\mathbf Q}(x)|$. These cancel, proving (2.1).

If $L/K$ is finite and $w$ is a place of $K$, then

$$
\sum_{v\mid w}[L_v:K_w]=[L:K]. \tag{2.2}
$$

Together with $[L_v:\mathbf Q_w]=[L_v:K_w][K_w:\mathbf Q_w]$, this identity is what makes absolute heights independent of the field in which coordinates are written.

### 2.2 The height of a projective point

For $P=[x_0:\cdots:x_n]\in\mathbf P^n(K)$ define

$$
h(P)=\frac1d\sum_{v\in M_K}n_v
\log\max_{0\leq i\leq n}|x_i|_v. \tag{2.3}
$$

Only finitely many summands are nonzero after one coordinate is scaled to $1$. Replacing every $x_i$ by $a x_i$ adds

$$
\frac1d\sum_v n_v\log|a|_v=0,
$$

so (2.3) is well defined on projective points.

The height is nonnegative. Choose $j$ with $x_j\ne0$ and scale so that $x_j=1$. Then every local maximum is at least $1$, hence every summand in (2.3) is nonnegative. Its exponential form is

$$
H(P)=\prod_v\max_i|x_i|_v^{n_v/d}\geq1. \tag{2.4}
$$

For $\alpha\in\overline{\mathbf Q}$ we abbreviate

$$
h(\alpha)=h([1:\alpha]).
$$

This is an absolute height: if $P$ is rational over two number fields, compute in a common finite extension and use (2.2). Each old local summand is repeated with total relative degree $[L:K]$, while the denominator also acquires that factor.

### 2.3 Change of field and elementary estimates

The local triangle inequality yields the global estimates that later control morphisms. For algebraic numbers $\alpha,\beta$,

$$
h(\alpha\beta)\leq h(\alpha)+h(\beta),
\qquad h(\alpha^{-1})=h(\alpha), \tag{2.5}
$$

and

$$
h(\alpha+\beta)\leq h(\alpha)+h(\beta)+\log2. \tag{2.6}
$$

At nonarchimedean places the factor $2$ is unnecessary; at each archimedean place it contributes $\log2$, and the normalized archimedean local degrees sum to $1$. Also

$$
h(\alpha^r)=|r|h(\alpha) \qquad(r\in\mathbf Z). \tag{2.7}
$$

Let $F_0,\ldots,F_m$ be homogeneous forms of common degree $e$ in $n+1$ variables, with algebraic coefficients, and suppose they have no common zero on a projective subvariety $X$. Then the morphism

$$
f:X\longrightarrow\mathbf P^m,\qquad
P\longmapsto[F_0(P):\cdots:F_m(P)]
$$

satisfies

$$
h(f(P))\leq e h(P)+C. \tag{2.8}
$$

Indeed each local value $|F_j(x)|_v$ is at most a coefficient-dependent constant times $\max_i|x_i|_v^e$. The ultrametric inequality makes that constant the largest coefficient at finite places; the archimedean triangle inequality adds at most the number of monomials. Summing gives (2.8).

There is also a reverse comparison on $X$. Since the forms have no common zero on $X$, the homogeneous Nullstellensatz gives, for some $r$, identities modulo the homogeneous ideal of $X$,

$$
x_i^r=\sum_jG_{ij}F_j
$$

with $\deg G_{ij}=r-e$. Applying the same local estimate gives

$$
e h(P)\leq h(f(P))+C'. \tag{2.9}
$$

The two inequalities together express functoriality of height for a finite projective presentation. The explicit Nullstellensatz step is important: the absence of a base point, not merely the degree of the coordinate forms, supplies the reverse bound.

Here is the local calculation behind (2.8) in a form that will be reused. For a place $v$, put $\|x\|_v=\max_i|x_i|_v$, and let $\|F\|_v$ be the largest $v$-adic absolute value of all coefficients of all $F_j$. If $N$ is the largest number of monomials occurring in one $F_j$, then

$$
\max_j|F_j(x)|_v
\leq c_v\|F\|_v\|x\|_v^e,
\qquad
c_v=\begin{cases}
1,&v\text{ nonarchimedean},\\
N,&v\text{ archimedean}.
\end{cases} \tag{2.10}
$$

After taking logarithms, the sum of $\log\|F\|_v$ is finite because almost every coefficient is integral and at least one is a unit. The sum of the archimedean $\log c_v$ is bounded after division by $[K:\mathbf Q]$. This proves a constant independent of $P$.

For the reverse estimate, base-point-freeness on $X$ means that the radical of the ideal generated by $I(X)$ and the $F_j$ contains the irrelevant ideal. Thus, for one $r$ and every $i$,

$$
x_i^r\equiv\sum_jG_{ij}F_j\pmod {I(X)},
\qquad \deg G_{ij}=r-e. \tag{2.11}
$$

The local estimate applied to this identity gives

$$
r\log\|x\|_v
\leq(r-e)\log\|x\|_v+\log\max_j|F_j(x)|_v+c'_v.
$$

The constants $c'_v$ again vanish at almost all finite places. Summing and cancelling $(r-e)h(P)$ gives (2.9). This also explains a hidden geometric fact: a morphism presented everywhere by sections of an ample bundle cannot contract a positive-dimensional subvariety, because the pullback of $\mathcal O(1)$ is ample.

### 2.4 Concrete computations

For a rational point $P=[a_0:\cdots:a_n]$ choose primitive integral coordinates, so $\gcd(a_0,\ldots,a_n)=1$. Every finite-place maximum is $1$, and therefore

$$
h(P)=\log\max_i|a_i|. \tag{2.12}
$$

In particular, if $a/b\in\mathbf Q$ is in lowest terms,

$$
h(a/b)=\log\max(|a|,|b|).
$$

For an algebraic integer $\alpha$ of degree $r$ with conjugates $\alpha_1,\ldots,\alpha_r$,

$$
h(\alpha)=\frac1r\sum_{i=1}^r\log\max(1,|\alpha_i|). \tag{2.13}
$$

For a general algebraic number with primitive minimal polynomial

$$
a_0T^r+a_1T^{r-1}+\cdots+a_r
=a_0\prod_{i=1}^r(T-\alpha_i),
$$

Gauss's lemma and the finite-place contribution give

$$
h(\alpha)=\frac1r\left(
\log|a_0|+\sum_{i=1}^r\log\max(1,|\alpha_i|)
\right). \tag{2.14}
$$

Thus height records both denominators and the sizes of all conjugates. Looking at only one chosen complex embedding would miss both and would not be a finiteness measure.

Several quick checks are useful. A root of unity $\zeta$ is an algebraic integer and every conjugate has modulus $1$, so $h(\zeta)=0$. Conversely, if $\alpha\ne0$ has height zero, (2.14) forces its primitive minimal polynomial to be monic and every conjugate to have modulus at most $1$. The constant term shows every conjugate has modulus exactly $1$. The coefficients of the minimal polynomials of the powers $\alpha^n$ are then uniformly bounded; Theorem 3.1's coefficient argument makes the set of powers finite, so $\alpha$ is a root of unity. Thus

$$
h(\alpha)=0
\quad\Longleftrightarrow\quad
\alpha=0\text{ or }\alpha\text{ is a root of unity}. \tag{2.15}
$$

This one-dimensional statement foreshadows the zero-height theorem for abelian varieties: bounded degree plus a multiplication law turns height zero into torsion.

## 3. Northcott finiteness

The descent proof needs a discrete conclusion from a real-valued size: a bounded-height set of rational points must be finite. This is special to global arithmetic. Over an algebraically closed field there are infinitely many constants of height zero, and over a function field the constant field can create the same failure.

### 3.1 Why bounded size should be finite

For rational points, formula (2.12) makes the assertion immediate: only finitely many primitive integer tuples have bounded coordinates. For algebraic points, one must also bound their defining polynomials. Degree controls the number of conjugates; height controls the leading coefficient and the symmetric functions of those conjugates. This reduces the theorem to finiteness of bounded integer coefficient vectors.

### 3.2 Algebraic numbers of bounded degree

**Theorem 3.1 (Northcott for algebraic numbers).** For real $B\geq0$ and integer $D\geq1$, the set

$$
\{\alpha\in\overline{\mathbf Q}:[\mathbf Q(\alpha):\mathbf Q]\leq D,
\ h(\alpha)\leq B\}
$$

is finite.

**Proof strategy.** We bound the coefficients of the primitive minimal polynomial by its Mahler measure, which is exactly the exponential height to the degree.

Let $r\leq D$ and write the minimal polynomial as in (2.14). Its Mahler measure is

$$
M(f)=|a_0|\prod_{i=1}^r\max(1,|\alpha_i|)
=e^{r h(\alpha)}\leq e^{DB}. \tag{3.1}
$$

The coefficient $a_j$ is $a_0$ times the $j$th elementary symmetric function of the roots. Each of its $\binom rj$ terms has absolute value at most $\prod_i\max(1,|\alpha_i|)$. Hence

$$
|a_j|\leq\binom rj M(f)\leq2^D e^{DB}. \tag{3.2}
$$

There are only finitely many integer tuples of length at most $D+1$ satisfying (3.2). Each polynomial has finitely many roots. Taking the finite union over $r\leq D$ proves the theorem. $\square$

The degree hypothesis cannot be removed: all roots of unity have height zero. The height hypothesis cannot be removed either: the rational integers already have unbounded height.

### 3.3 Projective Northcott

**Theorem 3.2 (projective Northcott).** For integers $n,D\geq1$ and $B\geq0$, the set

$$
\{P\in\mathbf P^n(\overline{\mathbf Q}):
[\mathbf Q(P):\mathbf Q]\leq D, h(P)\leq B\}
$$

is finite.

Here $\mathbf Q(P)$ is the residue field generated by all coordinate ratios. To prove the theorem, cover projective space by the $n+1$ charts $x_j\ne0$. On the $j$th chart write $P=[y_0:\cdots:1:\cdots:y_n]$. Each coordinate satisfies

$$
h(y_i)\leq h(P). \tag{3.3}
$$

Indeed $[1:y_i]$ is obtained by selecting two coordinates, and each local maximum can only decrease. Also $[\mathbf Q(y_i):\mathbf Q]\leq[\mathbf Q(P):\mathbf Q]\leq D$. Theorem 3.1 gives finitely many possibilities for each $y_i$, hence finitely many tuples. The finite chart cover completes the proof. $\square$

For the Mordell--Weil theorem we use the fixed-field consequence

$$
\{P\in\mathbf P^n(K):h(P)\leq B\}\quad\text{is finite}. \tag{3.4}
$$

Notice that (3.4) remains true after adding any bounded function to $h$, a fact that lets the Weil height machine tolerate $O(1)$ ambiguity.

There is a useful ideal-theoretic view of the fixed-field case. A point of $\mathbf P^n(K)$ may be represented by a tuple in $\mathcal O_K^{n+1}$ whose coordinate ideal belongs to one of finitely many ideal classes. After multiplying by one fixed representative for that class, the nonarchimedean contribution is controlled. The archimedean part bounds the tuple inside a bounded region of the Minkowski space

$$
K\otimes_{\mathbf Q}\mathbf R\simeq
\mathbf R^{r_1}\times\mathbf C^{r_2}.
$$

The image of a fractional ideal is a lattice, and a bounded region meets a lattice in finitely many points. Units do not create infinitely many projective points because common multiplication changes no point. This proves (3.4) directly and shows how ideal classes and archimedean lattices form the arithmetic content behind the coefficient proof.

### 3.4 Subvarieties and affine coordinates

If $X\hookrightarrow\mathbf P^n$ is a projective variety, then $X(\overline{\mathbf Q})$ is a subset of projective space. Thus the restriction of $h$ has Northcott finiteness with bounded residue degree. No smoothness, irreducibility, or group structure is needed.

By contrast, a naive affine height attached to one coordinate system is not intrinsic. A regular change of affine coordinates is controlled by polynomial estimates such as (2.8), but points approaching the boundary can make the inverse transformation large. Projective compactification and an ample line bundle record the boundary divisor and provide the correct invariant formulation.

## 4. The Weil height machine

A projective variety has many embeddings, while arithmetic arguments must be independent of an arbitrary list of homogeneous coordinates. The Weil height machine attaches a height to a line bundle, uniquely up to a bounded function. The bounded ambiguity is not a defect: the canonical limiting process on an abelian variety will remove precisely that ambiguity.

### 4.1 Why line bundles replace coordinates

An embedding $\iota:X\hookrightarrow\mathbf P^n$ carries the coordinate hyperplane bundle back to $L=\iota^*\mathcal O(1)$. Replacing the basis of coordinate sections changes $h\circ\iota$ only by $O(1)$, because a matrix and its inverse give inequalities of the form (2.8). Replacing an embedding defined by $L$ by its $r$th Veronese embedding multiplies height by $r$ up to a bounded term. These observations show that the geometric datum behind projective height is the line bundle, not the coordinates.

For a projective variety $X/K$, write $\operatorname{Pic}(X)$ additively when discussing classes and multiplicatively for actual line bundles. A **Weil height associated with $L$** is a function

$$
h_L:X(\overline K)\longrightarrow\mathbf R
$$

belonging to the equivalence class described below. We keep actual functions when forming limits, but all preliminary identities are modulo bounded functions.

### 4.2 Heights from projective embeddings

Suppose first that $L$ is very ample. Choose a basis of $H^0(X,L)$, or any base-point-free subspace defining a closed immersion $\iota_L:X\hookrightarrow\mathbf P^n$, and set

$$
h_L(P)=h(\iota_L(P)). \tag{4.1}
$$

Two choices give heights differing by $O(1)$. Here is the comparison without assuming the height machine in advance. Let $V,W\subseteq H^0(X,L)$ be two base-point-free subspaces giving closed immersions $i_V,i_W$. Since $i_V$ is a closed immersion and $i_V^*\mathcal O(1)=L$, Serre generation on $i_V(X)$ shows that, for all sufficiently large $a$, every section of $L^a$ is the restriction of a homogeneous polynomial of degree $a$ in the $V$-coordinates. In particular, the $a$th powers of the $W$-coordinates are such polynomials. Estimate (2.8) then gives

$$
a h(i_W(P))\leq a h(i_V(P))+C.
$$

After division by $a$, this is one bounded comparison. Interchanging $V$ and $W$ gives the reverse comparison. If the two choices are bases of the same space, the simpler matrix estimate and its inverse suffice.

If $L$ is ample, choose $r>0$ for which $L^r$ is very ample and put

$$
h_L=\frac1r h_{L^r}. \tag{4.2}
$$

Different choices of $r$ agree modulo $O(1)$ by passing to the common tensor power. For a general line bundle, choose an ample bundle $M$ so positive that both $M$ and $L\otimes M$ are ample, and define

$$
h_L=h_{L\otimes M}-h_M. \tag{4.3}
$$

If $M'$ is another choice, tensor-product compatibility for ample bundles shows that the two expressions differ by $O(1)$. Thus every line bundle has a height class.

This construction also proves existence rather than merely postulating a list of properties. The only geometric input is that sufficiently high powers of an ample bundle are very ample and that twisting a fixed bundle by a sufficiently high ample power is ample.

Let us justify the independence in (4.3) without circular cancellation in the Picard group. Suppose $M$ and $N$ are ample and so are $L\otimes M$ and $L\otimes N$. For very ample bundles the coordinate identity for the Segre embedding proves additivity of heights directly. Passing to sufficiently high powers and dividing proves the same assertion modulo $O(1)$ for any two ample bundles. Apply it to the ample pairs $(L\otimes M,N)$ and $(L\otimes N,M)$. Since their tensor products are canonically isomorphic, the comparison just proved gives

$$
h_{L\otimes M}+h_N
=h_{L\otimes N}+h_M+O(1).
$$

and hence

$$
h_{L\otimes M}-h_M
=h_{L\otimes N}-h_N+O(1).
$$

The same direct comparison shows that a chosen height for $L^a$ divided by $a$ agrees with one for $L^b$ divided by $b$: both become heights for $L^{ab}$ after multiplication by the complementary exponent. No root of a line bundle is chosen; only real-valued height functions are divided. This proves that (4.2)--(4.3) are independent of every auxiliary choice before the formal properties of the height machine are invoked.

### 4.3 Functoriality, tensor products, and bounded ambiguity

The construction satisfies the following height-machine theorem.

**Theorem 4.1 (Weil height machine).** Let $X,Y$ be projective varieties over a number field, $L,M$ line bundles on $X$, and $f:Y\to X$ a morphism. Heights may be chosen so that, in every case below, any other choices change the equality by $O(1)$:

$$
\begin{aligned}
h_{L\otimes M}&=h_L+h_M+O(1),\\
h_{L^{-1}}&=-h_L+O(1),\\
h_{f^*L}(Q)&=h_L(f(Q))+O(1),\\
h_{\mathcal O_X}&=O(1). \tag{4.4}
\end{aligned}
$$

If $L\simeq M$, then $h_L-h_M=O(1)$.

**Proof.** For very ample bundles, use the Segre embedding to compare the tensor product with the product of coordinate vectors; its local maximum is the product of the two local maxima, so heights add, up to the bounded effect of restricting to $X$. Functoriality follows by writing the composite map in homogeneous coordinates and applying (2.8)--(2.9) on its graph. Passing to positive powers proves the ample case. Expressing arbitrary bundles as differences of ample bundles proves all of (4.4). The trivial bundle is the zero difference, and isomorphic bundles define the same Picard class. $\square$

We spell out the two decisive reductions. If $L$ and $M$ are very ample with coordinate maps $\iota_L$ and $\iota_M$, the product map followed by Segre has coordinates $x_i y_j$. At every place,

$$
\max_{i,j}|x_i y_j|_v
=\left(\max_i|x_i|_v\right)
 \left(\max_j|y_j|_v\right).
$$

The pullback of $\mathcal O(1)$ is $L\otimes M$, so summing the exact local identity proves additivity for this presentation. If the complete tensor system gives a different embedding, the change is bounded by the coordinate comparison of Section 2.3. Taking powers and dividing proves additivity for ample bundles.

For functoriality, first let $L$ be very ample. The sections defining $\iota_L\circ f$ are precisely the pullbacks of the coordinate sections of $L$, and they define $f^*L$. Thus one may choose

$$
h_{f^*L}(Q)=h(\iota_L(f(Q)))=h_L(f(Q)).
$$

If this pullback system is not an embedding, define its height by adjoining a sufficiently positive auxiliary bundle and subtracting the auxiliary height. The two added terms cancel modulo $O(1)$. Differences of ample bundles then prove the assertion for arbitrary $L$. This explains why functoriality remains true when $f$ has positive-dimensional fibers and $f^*L$ is not ample.

These properties also characterize the assignment. Suppose another rule $L\mapsto h'_L$ agrees with projective height for $\mathcal O(1)$ and has additivity and functoriality modulo $O(1)$. If $L$ is very ample, pull back $h_{\mathcal O(1)}$ along its embedding to get $h'_L=h_L+O(1)$. Positive powers handle ample $L$, and writing an arbitrary $L$ as the difference of two ample classes handles the general case. Thus the ambiguity in the height machine is exactly bounded ambiguity; there is no further choice hidden in the construction.

A principal divisor gives a useful special case. If $D=\operatorname{div}(g)$, then $\mathcal O_X(D)\simeq\mathcal O_X$, so

$$
h_D=O(1). \tag{4.4a}
$$

Locally its natural Weil function is $-\log|g|_v$ up to a bounded continuous term. For a rational point away from the zeros and poles, the uncorrected global sum is exactly zero by the product formula. This is the arithmetic reason the global machine factors through $\operatorname{Pic}(X)$ rather than remembering the full divisor group.

For a rational map, functoriality holds on its domain of definition but the error need not remain bounded near the indeterminacy locus. Morphisms, not rational formulas alone, are the safe input to (4.4).

### 4.4 Divisors and local Weil functions

If $D$ is a Cartier divisor and $L=\mathcal O_X(D)$, write $h_D$ for $h_L$. This notation connects the global height to local proximity to the divisor. At a place $v$, a **local Weil function** for $D$ is a function

$$
\lambda_{D,v}:X(\overline K_v)\setminus|D|\longrightarrow\mathbf R
$$

which, on an open set where $D$ has equation $f$, has the form

$$
\lambda_{D,v}(P)=-\log|f(P)|_v+\alpha_v(P), \tag{4.5}
$$

where $\alpha_v$ is continuous and locally bounded. On overlaps, two equations differ by a unit, and its logarithm is continuous, so these local descriptions glue after a continuous correction.

Choose a projective model and metrics on $\mathcal O(D)$ which are integral at all but finitely many places. If $s_D$ is the rational section with divisor $D$, then

$$
\lambda_{D,v}(P)=-\log\|s_D(P)\|_v
$$

has (4.5), and for $P\in X(K)\setminus|D|$,

$$
h_D(P)=\frac1d\sum_{v\in M_K}n_v\lambda_{D,v}(P)+O(1). \tag{4.6}
$$

Only finitely many terms fail to vanish in an integral trivialization. Changing a local equation by a rational function changes the sum by the product formula. Thus linearly equivalent divisors have heights differing by $O(1)$.

The local expression is written only away from $|D|$, whereas the line-bundle height is defined at every algebraic point. For a fixed finite collection of points, one may replace $D$ by a linearly equivalent divisor avoiding those points: take a sufficiently positive auxiliary presentation and choose a section outside the finitely many vanishing hyperplanes. The product formula shows that the resulting global value changes only within the height class. This moving step, rather than assigning a finite value to $-\log0$, is the correct way to evaluate a divisor height at a point on a chosen representative.

Formula (4.6) is useful conceptually: global height is a sum of local distances from a divisor. The Néron--Tate height constructed later is global and canonical. Individual local functions still depend on metrics and additive constants; no unannounced local normalization will be used.

Functoriality has a local form. If $f:Y\to X$ is a morphism whose image is not contained in $|D|$, then

$$
\lambda_{f^*D,v}(Q)=\lambda_{D,v}(f(Q))+O_v(1). \tag{4.7}
$$

If $D,E$ are Cartier divisors, local equations multiply, so

$$
\lambda_{D+E,v}=\lambda_{D,v}+\lambda_{E,v}+O_v(1). \tag{4.8}
$$

The functions denoted $O_v(1)$ can be chosen zero for almost all finite $v$ on integral points of a fixed model. This restrictedness is what permits their sums to be global $O(1)$ terms. An arbitrary unrelated bounded correction at every place would not define a global height.

### 4.5 Ample heights and Northcott

**Theorem 4.2.** If $L$ is ample on a projective variety $X/K$, then:

1. $h_L$ is bounded below on $X(\overline K)$;
2. for every $D\geq1$ and real $B$, the set
   $$
   \{P\in X(\overline K):[K(P):K]\leq D,\ h_L(P)\leq B\}
   $$
   is finite.

**Proof.** Choose $r>0$ and a closed immersion $\iota:X\hookrightarrow\mathbf P^n$ with $L^r\simeq\iota^*\mathcal O(1)$. Then

$$
r h_L(P)=h(\iota(P))+O(1). \tag{4.9}
$$

Projective height is nonnegative, proving the lower bound. A bound on $h_L$ gives a bound on $h(\iota(P))$, and a closed immersion over $K$ preserves residue fields. Moreover $[\mathbf Q(P):\mathbf Q]\leq [K:\mathbf Q]D$ when $[K(P):K]\leq D$. Projective Northcott therefore proves finiteness. $\square$

Ampleness is essential. For the trivial bundle every associated height is bounded; on $\mathbf P^1(K)$ this gives an immediate infinite bounded-height set. A nef bundle pulled back from one factor of a product likewise fails to detect motion in the other factor.

The theorem behaves well under finite maps. If $f:Y\to X$ is finite and $L$ is ample, then $f^*L$ is ample, and

$$
h_{f^*L}(Q)=h_L(f(Q))+O(1). \tag{4.10}
$$

Thus the inverse image of a bounded-height set has bounded height. If the residue degrees of the points of $Y$ are bounded, Northcott makes that inverse image finite. The finiteness of the morphism is essential for positivity of $f^*L$: when $f$ contracts a curve, the pullback has degree zero on that curve and cannot detect motion along it.

More generally, if $L$ and $M$ are ample on the same $X$, each height bounds the other linearly up to a constant. Choose $r,s>0$ so that $L^r\otimes M^{-1}$ and $M^s\otimes L^{-1}$ are ample. Since ample heights are bounded below, additivity gives constants $C_1,C_2$ with

$$
h_M(P)\leq r h_L(P)+C_1,
\qquad
h_L(P)\leq s h_M(P)+C_2. \tag{4.11}
$$

Consequently Northcott finiteness is intrinsic to an ample class and does not depend on which projective embedding was used to prove it.

## 5. Heights on abelian varieties

The height machine becomes much more rigid in the presence of a group law. Translation, inversion, and multiplication pull line bundles through the identities of the square and cube. Those geometric identities become approximate algebraic identities for heights, with bounded error. The next chapter will remove that error.

### 5.1 Translation and addition

Let $A/K$ be an abelian variety, $m:A\times A\to A$ addition, and $p_1,p_2$ the projections. For a line bundle $L$ define

$$
\Delta(L)=m^*L\otimes p_1^*L^{-1}\otimes p_2^*L^{-1}. \tag{5.1}
$$

The theorem of the square says that the translation discrepancy $t_Q^*L\otimes L^{-1}$ is algebraically trivial and varies homomorphically with $Q$. Consequently the height difference

$$
h_L(P+Q)-h_L(P)
$$

is governed by an algebraically trivial bundle once $Q$ is fixed. It need not be bounded uniformly in both $P$ and $Q$; the mixed term is precisely what the height pairing will measure.

For fixed $Q$, functoriality gives

$$
h_L(P+Q)=h_{t_Q^*L}(P)+O(1). \tag{5.2}
$$

This already shows why an ordinary ample height is not a homomorphism: translating the point changes the line bundle by a degree-zero class.

The mixed bundle in (5.1) is not noise. Under duality, its restriction to $A\times\{Q\}$ represents $\lambda_L(Q)\in A^\vee$. Accordingly, its height on $(P,Q)$ becomes bilinear after canonical normalization. The future pairing is therefore already present geometrically in the Poincaré biextension. The limiting argument will recover it without requiring a separate theory of metrized biextensions.

For an algebraically trivial bundle $N$, the square theorem gives $[n]^*N\simeq N^n$. Hence

$$
h_N([n]P)=n h_N(P)+O(1). \tag{5.2a}
$$

This linear growth is smaller than the quadratic growth of an ample symmetric class. It explains why twisting an ample bundle by an algebraically trivial bundle does not change its associated polarization, while a nonsymmetric choice can change the lower-order part of its ordinary height.

### 5.2 Symmetric and antisymmetric parts

Every line bundle has a symmetric and an antisymmetric contribution. Put

$$
L^+=L\otimes[-1]^*L,
\qquad L^-=L\otimes([-1]^*L)^{-1}. \tag{5.3}
$$

Then $[-1]^*L^+\simeq L^+$ and $[-1]^*L^-\simeq(L^-)^{-1}$. The theorem of the cube gives

$$
[n]^*L\simeq
L^{n(n+1)/2}\otimes[-1]^*L^{n(n-1)/2}. \tag{5.4}
$$

Thus for symmetric $L$,

$$
[n]^*L\simeq L^{n^2}, \tag{5.5}
$$

whereas for antisymmetric $L$ the exponent is linear. Heights reflect the same division: symmetric classes produce quadratic heights and antisymmetric classes produce linear canonical heights. Finite generation needs only the positive quadratic part, so from now on $L$ will be symmetric and ample unless explicitly stated otherwise.

Any ample $M$ yields such a bundle $M\otimes[-1]^*M$. Hence the argument does not require a principal polarization. There is a descent point when a polarization $\lambda:A\to A^\vee$ is specified only as a homomorphism. By the definition recalled from Book 35, after a finite extension it is induced by an ample bundle. Pass to a finite Galois extension $F/K$ over which such a bundle $M$ exists. The norm bundle

$$
N_{F/K}(M)=\bigotimes_{\sigma\in\operatorname{Gal}(F/K)}\sigma^*M
$$

has its permutation descent datum and therefore descends to an ample bundle $N$ on $A$. Because $\lambda$ is defined over $K$, additivity and Galois compatibility of $M\mapsto\lambda_M$ give

$$
\lambda_N=[F:K]\lambda.
$$

The bundle $L=N\otimes[-1]^*N$ is symmetric and ample. The identity $\lambda_{[-1]^*N}=\lambda_N$, which follows directly from the square theorem, now gives

$$
\lambda_L=2[F:K]\lambda.
$$

Thus a positive multiple of every polarization is induced over $K$ by a symmetric ample bundle. Scaling the inducing class only scales the eventual height, so this causes no loss.

### 5.3 The bounded quadratic defect

Choose a Weil height $h_L$ for symmetric $L$. From (5.5) and functoriality,

$$
h_L([n]P)=n^2h_L(P)+O(1), \tag{5.6}
$$

where the error is uniform in $P$. In particular, for a fixed integer $q\geq2$ there is $C$ such that

$$
|h_L([q]P)-q^2h_L(P)|\leq C
\qquad(P\in A(\overline K)). \tag{5.7}
$$

The theorem of the cube gives a second bounded defect. For symmetric $L$, its restriction along

$$
A\times A\longrightarrow A^3,\qquad(P,Q)\longmapsto(P,Q,-P)
$$

reduces to the parallelogram line-bundle identity

$$
m^*L\otimes d^*L\simeq p_1^*L^2\otimes p_2^*L^2, \tag{5.8}
$$

where $d(P,Q)=P-Q$. Applying the height machine on $A\times A$ yields

$$
h_L(P+Q)+h_L(P-Q)
=2h_L(P)+2h_L(Q)+O(1), \tag{5.9}
$$

with one bounded error uniform in the pair $(P,Q)$.

The uniformity in (5.7) and (5.9) is decisive. A point-dependent error could accumulate under iteration and destroy the limiting argument.

It is worth locating the source of each error. The line-bundle isomorphisms (5.5) and (5.8) are exact. Error appears only because the height machine sends isomorphic line bundles to functions equal modulo $O(1)$. Thus the error is globally bounded on all algebraic points; it is not an asymptotic statement valid only on $A(K)$ or away from a divisor.

### 5.4 Polarizations and choices

The homomorphism associated with $L$ is

$$
\lambda_L(P)=t_P^*L\otimes L^{-1}:A\longrightarrow A^\vee.
$$

When $L$ is ample, $\lambda_L$ is a polarization. Tensor products add these homomorphisms, and $L^r$ induces $r\lambda_L$. Algebraically trivial twists do not change $\lambda_L$. The canonical quadratic height will similarly depend only on the symmetric Néron--Severi class of $L$, not on a chosen divisor or projective basis. Indeed, if two symmetric bundles have the same Néron--Severi class, their quotient is both algebraically trivial and symmetric. In $\operatorname{Pic}^0(A)$ inversion pulls a class back to its inverse, so this quotient is two-torsion. Its height is bounded and its canonical quadratic height is zero. Additivity therefore identifies the canonical heights of the original bundles.

There is nevertheless no universal numerical normalization independent of $L$. Replacing $L$ by $L^r$ multiplies the height by $r$. On an elliptic curve, using a divisor of degree $d$ multiplies the standard canonical height by $d$. Every statement below records the chosen symmetric ample bundle or polarization so that these scalings remain visible.

## 6. Canonical Néron--Tate heights

An ordinary Weil height is only approximately quadratic because it remembers arbitrary choices of coordinates and metrics. Repeated multiplication magnifies the genuine quadratic term by $q^2$ while the bounded error stays bounded. Dividing by $q^{2r}$ therefore filters out the choices.

### 6.1 The limiting construction

Let $L$ be symmetric and let $q\geq2$. Define

$$
a_r(P)=q^{-2r}h_L([q^r]P).
$$

**Theorem 6.1.** The sequence $a_r(P)$ converges for every $P\in A(\overline K)$, uniformly in $P$. Its limit

$$
\widehat h_L(P)=\lim_{r\to\infty}q^{-2r}h_L([q^r]P) \tag{6.1}
$$

satisfies

$$
|\widehat h_L(P)-h_L(P)|\leq\frac{C}{q^2-1}, \tag{6.2}
$$

where $C$ is any bound in (5.7).

**Proof.** Put $\epsilon(P)=h_L([q]P)-q^2h_L(P)$. Then

$$
a_{r+1}(P)-a_r(P)=q^{-2(r+1)}\epsilon([q^r]P).
$$

Its absolute value is at most $Cq^{-2(r+1)}$. The geometric series converges uniformly, so $(a_r)$ is uniformly Cauchy. Summing from $r=0$ gives

$$
\widehat h_L(P)-h_L(P)
=\sum_{r\geq0}q^{-2(r+1)}\epsilon([q^r]P),
$$

whose absolute value is at most $C/(q^2-1)$. $\square$

Shifting the index immediately gives

$$
\widehat h_L([q]P)=q^2\widehat h_L(P). \tag{6.3}
$$

### 6.2 Independence and uniqueness

The construction is independent of the chosen Weil height in its bounded class. If $h'_L-h_L$ is bounded by $B$, then

$$
q^{-2r}|h'_L([q^r]P)-h_L([q^r]P)|\leq q^{-2r}B\longrightarrow0.
$$

It is also independent of $q$. The clean reason is uniqueness.

**Proposition 6.2.** There is at most one function $H:A(\overline K)\to\mathbf R$ such that

$$
H=h_L+O(1),\qquad H([q]P)=q^2H(P). \tag{6.4}
$$

Indeed if $H_1-H_2$ is bounded by $B$, then

$$
|H_1(P)-H_2(P)|
=q^{-2r}|H_1([q^r]P)-H_2([q^r]P)|
\leq q^{-2r}B,
$$

and letting $r\to\infty$ gives equality. A construction using another integer $q'\geq2$ produces a function boundedly close to $h_L$ and satisfying the $q$-functional equation once full quadraticity is proved in the next section; hence it is the same function.

Additivity in line bundles survives canonically:

$$
\widehat h_{L\otimes M}=\widehat h_L+\widehat h_M \tag{6.5}
$$

for symmetric line bundles $L,M$. Both sides are boundedly close to the appropriate Weil height and obey the same functional equation. Likewise

$$
\widehat h_{f^*L}(P)=\widehat h_L(f(P)) \tag{6.6}
$$

for a homomorphism $f:B\to A$.

The bounded comparison has a useful uniform consequence. Put

$$
B_L=\sup_{P\in A(\overline K)}
|h_L(P)-\widehat h_L(P)|<\infty.
$$

Then for every integer $n$ and every algebraic point $P$,

$$
|h_L([n]P)-n^2\widehat h_L(P)|\leq B_L. \tag{6.6a}
$$

Indeed $\widehat h_L([n]P)=n^2\widehat h_L(P)$ once Section 6.3 is established, and the bounded comparison is applied at the single point $[n]P$. Thus the error in quadratic growth does not increase with $n$. The ordinary height of the multiples of a nontorsion point is a quadratic main term plus one uniformly bounded remainder.

### 6.3 Quadraticity

Apply (5.9) to $[q^r]P$ and $[q^r]Q$, divide by $q^{2r}$, and let $r\to\infty$. The bounded error disappears and gives the exact parallelogram identity

$$
\widehat h_L(P+Q)+\widehat h_L(P-Q)
=2\widehat h_L(P)+2\widehat h_L(Q). \tag{6.7}
$$

Taking $Q=0$ shows $\widehat h_L(0)=0$; taking $P=0$ shows $\widehat h_L(-Q)=\widehat h_L(Q)$. An induction using (6.7) now proves

$$
\widehat h_L([n]P)=n^2\widehat h_L(P)
\qquad(n\in\mathbf Z). \tag{6.8}
$$

For the induction, set $P=nR$, $Q=R$ in (6.7):

$$
\widehat h_L((n+1)R)+\widehat h_L((n-1)R)
=2\widehat h_L(nR)+2\widehat h_L(R).
$$

If the formula is known at $n$ and $n-1$, the right recurrence gives $(n+1)^2\widehat h_L(R)$. Evenness handles negative $n$.

This proves at once that the limit is independent of the initially chosen $q$: every such limit is boundedly close to $h_L$ and satisfies (6.8), so Proposition 6.2 applies.

### 6.4 Nonnegativity and the zero locus

Ampleness now turns the quadratic function into a genuine measure of nontorsion.

**Theorem 6.3.** If $L$ is symmetric and ample, then for every $P\in A(\overline K)$:

$$
\widehat h_L(P)\geq0,
$$

$$
\widehat h_L(P)=0\quad\Longleftrightarrow\quad P\text{ is torsion}. \tag{6.9}
$$

**Proof.** Since $h_L$ is bounded below by $-C_0$,

$$
q^{-2r}h_L([q^r]P)\geq-C_0q^{-2r}.
$$

Taking the limit gives nonnegativity. If $P$ is torsion, choose $n>0$ with $[n]P=0$. Equation (6.8) gives $n^2\widehat h_L(P)=0$.

Conversely suppose $\widehat h_L(P)=0$. Then every multiple satisfies $\widehat h_L([n]P)=0$. Because $h_L-\widehat h_L$ is uniformly bounded, all points $[n]P$ have bounded $h_L$. Their residue fields lie in the one number field $K(P)$, so their degrees are bounded. Northcott finiteness makes the set $\{[n]P:n\geq0\}$ finite. Two multiples are equal, and their difference is a positive multiple killing $P$. $\square$

The role of degree must still be read correctly. Each individual algebraic point and all its multiples lie in one number field, so (6.9) holds for every algebraic point. But the union of all torsion points has canonical height zero and unbounded field degree. Northcott is applied one field at a time, never to all algebraic points at once.

### 6.5 Local Néron functions and the global sum

The name Néron--Tate height reflects a compatible local refinement. The global limit is sufficient for finite generation, but the local construction explains how the exact quadratic normalization interacts with divisors and the product formula.

Let $D$ be a Cartier divisor with $\mathcal O_A(D)\simeq L$. Symmetry gives a rational function $f_q$ satisfying

$$
\operatorname{div}(f_q)=[q]^*D-q^2D. \tag{6.10}
$$

Fix a place $v$ and a local Weil function $\lambda_{D,v}$. On points for which the displayed expressions are initially defined, put

$$
\delta_v(P)=\lambda_{D,v}([q]P)-q^2\lambda_{D,v}(P)
+\log|f_q(P)|_v. \tag{6.11}
$$

The three divisorial singularities cancel by (6.10). More explicitly, functoriality and additivity of local Weil functions show that the first two terms in (6.11) are a local Weil function for $[q]^*D-q^2D$, while $-\log|f_q|_v$ is a local Weil function for the same principal divisor. Their difference is therefore continuous across every local equation. Consequently $\delta_v$ extends to a continuous function on the compact analytic group $A(F)$ for every finite extension $F/K_v$, and is bounded there. Define

$$
u_v(P)=\sum_{r\geq0}q^{-2(r+1)}\delta_v([q^r]P). \tag{6.12}
$$

The series converges uniformly on $A(F)$. The shifted-index identity

$$
u_v([q]P)=q^2u_v(P)-\delta_v(P)
$$

shows that

$$
\widehat\lambda_{D,v}=\lambda_{D,v}+u_v \tag{6.13}
$$

satisfies the exact distribution relation

$$
\widehat\lambda_{D,v}([q]P)
=q^2\widehat\lambda_{D,v}(P)-\log|f_q(P)|_v. \tag{6.14}
$$

It remains a local Weil function for $D$, since $u_v$ is continuous and bounded. The equation is asserted wherever neither side meets the relevant divisor; the Weil-function interpretation extends it across other charts.

There is an additive-constant issue locally. Multiplying $f_q$ by $a\in K^\times$ changes the normalization, and adding a constant to $\widehat\lambda_{D,v}$ changes (6.14) by $(1-q^2)$ times that constant. To make the construction adelic, spread $A,D,f_q$, and the isomorphism (6.10) over the ring of integers with finitely many primes removed. At every remaining finite place, use the model metric; the same integral isomorphism then makes $\delta_v$ zero on integral points. Thus only finitely many places contribute nontrivial correction terms for a fixed algebraic point. The normalized global sum

$$
\frac1{[K:\mathbf Q]}\sum_vn_v\widehat\lambda_{D,v}(P) \tag{6.15}
$$

is then well defined up to the one global normalization dictated by $D$. The terms involving $f_q$ cancel by the product formula, so (6.15) obeys the same quadratic distribution relation as $\widehat h_L$. It is also boundedly close to $h_D$. Uniqueness in Proposition 6.2 therefore identifies (6.15) with $\widehat h_L(P)$ after the compatible global constant is fixed.

If $P$ lies on $D$, choose a linearly equivalent representative $D'$ avoiding $P$ and repeat the local construction for $D'$. This requires avoiding only the point at which the global sum is evaluated, not its entire infinite multiplication orbit: the correction functions $\delta_v$ already extend across their cancelled divisors. The local functions for $D$ and $D'$ differ by logarithms of one rational function wherever both are defined, and its global contribution is zero. Thus the line-bundle height at every algebraic point is obtained from a divisor representative avoiding that point, even though no single expression $-\log|f(P)|_v$ is finite on the support of its own divisor.

Thus the global canonical height is not an unrelated limiting invariant. It is the sum of locally normalized Néron functions, while the product formula is what makes their rational-function corrections disappear globally.

## 7. The height pairing

The parallelogram law says that the canonical height is a quadratic form. Polarization converts it into a bilinear pairing, and positivity converts rational points modulo torsion into a Euclidean space. This language makes the terminating descent both transparent and quantitative.

### 7.1 Polarization of a quadratic function

Define

$$
\langle P,Q\rangle_L
=\frac12\bigl(
\widehat h_L(P+Q)-\widehat h_L(P)-\widehat h_L(Q)
\bigr). \tag{7.1}
$$

The parallelogram law also gives the equivalent expression

$$
\langle P,Q\rangle_L
=\frac14\bigl(\widehat h_L(P+Q)-\widehat h_L(P-Q)\bigr). \tag{7.2}
$$

It is visibly symmetric and satisfies

$$
\langle P,P\rangle_L=\widehat h_L(P). \tag{7.3}
$$

The factor conventions matter. Some authors omit the $1/2$ in (7.1), producing a pairing whose diagonal is $2\widehat h$. Here the diagonal equals the canonical height.

### 7.2 Bilinearity and Cauchy--Schwarz

**Proposition 7.1.** The pairing (7.1) is biadditive and $\mathbf Z$-bilinear.

**Proof.** Let $B(P,Q)$ denote the right side of (7.1), equivalently the right side of (7.2). Evenness of $\widehat h_L$ gives $B(-P,Q)=-B(P,Q)$. Apply the parallelogram identity first to $(P+Q,R)$ and then to $(P-Q,R)$. Subtracting the two results and using (7.2) gives

$$
B(P+R,Q)+B(P-R,Q)=2B(P,Q).
$$

Now interchange $P$ and $R$ in this identity. Since $B(R-P,Q)=-B(P-R,Q)$, the result is

$$
B(P+R,Q)-B(P-R,Q)=2B(R,Q).
$$

Adding the last two displayed equations gives

$$
B(P+R,Q)=B(P,Q)+B(R,Q).
$$

Symmetry gives additivity in the second variable. Integer homogeneity follows by induction. $\square$

Since $\widehat h_L(nP+mQ)\geq0$ for all integers $m,n$, the quadratic polynomial

$$
n^2\widehat h_L(P)+2nm\langle P,Q\rangle_L
+m^2\widehat h_L(Q)
$$

is nonnegative on $\mathbf Z^2$. Approximate a real minimizing ratio by rationals, or extend the form first to $\mathbf Q^2$, to obtain

$$
|\langle P,Q\rangle_L|^2
\leq\widehat h_L(P)\widehat h_L(Q). \tag{7.4}
$$

Consequently

$$
\|P\|_L=\sqrt{\widehat h_L(P)} \tag{7.5}
$$

satisfies the triangle inequality:

$$
\|P+Q\|_L^2
=\|P\|_L^2+2\langle P,Q\rangle_L+\|Q\|_L^2
\leq(\|P\|_L+\|Q\|_L)^2.
$$

### 7.3 The Euclidean space of rational points

The pairing kills torsion, because if $nT=0$ then

$$
n\langle T,P\rangle_L=\langle nT,P\rangle_L=0.
$$

It therefore descends to $A(K)/A(K)_{\mathrm{tors}}$. Theorem 6.3 makes it positive definite there. It extends uniquely by $\mathbf Q$-bilinearity to

$$
A(K)\otimes_{\mathbf Z}\mathbf Q.
$$

At this stage we do not yet know this vector space is finite-dimensional. The height descent will prove that. Once finite generation is known, the image of the free part in the resulting Euclidean space is a lattice, and its Gram determinant is the regulator associated with $L$ and a chosen basis.

Northcott gives a useful discreteness statement even before finite generation:

$$
\{P\in A(K):\|P\|_L\leq R\}
\quad\text{is finite for every }R. \tag{7.6}
$$

Indeed $h_L$ and $\widehat h_L$ differ by a bounded function, so a canonical-height bound is an ample-height bound.

There is consequently a positive height gap on $A(K)$ away from torsion. The set of points with $\widehat h_L(P)\leq1$ is finite. Remove its torsion points and take the least remaining positive height, if any; compare it with $1$ if the set is empty. This gives a number $c(A,K,L)>0$ such that

$$
P\in A(K)\setminus A(K)_{\mathrm{tors}}
\quad\Longrightarrow\quad
\widehat h_L(P)\geq c(A,K,L). \tag{7.7a}
$$

The assertion is qualitative and field-dependent. It does not give a uniform lower bound as $A$, $K$, or the polarization varies. Its role here is to show how Northcott turns positive definiteness into arithmetic discreteness.

### 7.4 Changing the polarization and isogenies

If $L$ and $M$ are symmetric ample bundles on $A$, their heights define equivalent norms on $A(K)\otimes\mathbf R$ after finite generation is established. More intrinsically, ampleness gives positive integers $r,s$ such that $L^r\otimes M^{-1}$ and $M^s\otimes L^{-1}$ are ample. Nonnegativity and additivity yield

$$
\widehat h_M(P)\leq r\widehat h_L(P),
\qquad
\widehat h_L(P)\leq s\widehat h_M(P). \tag{7.7}
$$

Thus bounded sets and the zero locus are independent of the chosen polarization.

For a homomorphism $f:A\to B$ and symmetric ample $M$ on $B$, functoriality (6.6) says

$$
\widehat h_{f^*M}(P)=\widehat h_M(f(P)). \tag{7.8}
$$

If $f$ is an isogeny, $f^*M$ is ample, so heights on isogenous varieties compare in both directions using a quasi-inverse. If $f$ has positive-dimensional kernel, $f^*M$ is not ample and its canonical height vanishes along that kernel; this is exactly the geometry, not a failure of the height machine.

Suppose more explicitly that $f:A\to B$ is an isogeny. Choose a homomorphism $g:B\to A$ and an integer $d>0$ with

$$
gf=[d]_A,
\qquad fg=[d]_B.
$$

For a symmetric ample $M$ on $B$, equations (7.8) and (6.8) give

$$
\widehat h_{f^*M}(P)=\widehat h_M(f(P)),
$$

and, for every $Q\in B(\overline K)$,

$$
\widehat h_{f^*M}(gQ)
=\widehat h_M(fgQ)
=d^2\widehat h_M(Q).
$$

Thus the comparison is exact after pulling the chosen height through $f$ and $g$; comparisons with any other ample heights follow from (7.7). In particular the induced maps

$$
A(K)\otimes\mathbf Q\longleftrightarrow B(K)\otimes\mathbf Q
$$

are inverse up to multiplication by $d$. Once Mordell--Weil is known, they are isomorphisms of finite-dimensional rational vector spaces, proving isogeny invariance of rank. The argument separates two facts: finite cokernel on integral rational points comes from isogeny descent, while equality of rational ranks already follows from the quasi-inverse identities.

## 8. Mordell--Weil by height descent

We now join the algebraic half from weak Mordell--Weil to the analytic-looking but arithmetic height norm. The key group-theoretic lemma is stated separately so that every termination step is visible.

### 8.1 The abstract descent lemma

**Lemma 8.1 (height descent).** Let $G$ be an abelian group and $m\geq2$. Suppose:

1. $G/mG$ is finite;
2. there is a function $\|\cdot\|:G\to\mathbf R_{\geq0}$ with
   $$
   \|mP\|=m\|P\|,\qquad
   \|P+Q\|\leq\|P\|+\|Q\|;
   $$
3. every bounded ball $\{P:\|P\|\leq R\}$ is finite.

Then $G$ is finitely generated.

**Proof strategy.** Choose finitely many residue representatives. Division by $m$ contracts distance up to the largest representative. Iterating an explicit inequality, rather than appealing to a nonexistent well-ordering of real heights, forces entry into one fixed finite ball.

Choose representatives $R_1,\ldots,R_s$ for $G/mG$ and set

$$
C=\max_i\|R_i\|.
$$

Given $P_0\in G$, write successively

$$
P_j=R_{i_j}+mP_{j+1}.
$$

The triangle inequality gives

$$
\|P_{j+1}\|
=\frac1m\|P_j-R_{i_j}\|
\leq\frac{\|P_j\|+C}{m}. \tag{8.1}
$$

Iteration yields

$$
\|P_r\|
\leq m^{-r}\|P_0\|
+\frac{C}{m-1}(1-m^{-r}). \tag{8.2}
$$

Choose any $R>C/(m-1)$. For sufficiently large $r$, (8.2) gives $\|P_r\|\leq R$. Unwinding the identities,

$$
P_0=R_{i_0}+mR_{i_1}+\cdots+m^{r-1}R_{i_{r-1}}+m^rP_r. \tag{8.3}
$$

Thus $G$ is generated by the finitely many $R_i$ and the finite ball of radius $R$. $\square$

The proof does not assume that the set of norm values is discrete. Formula (8.2) is the exact termination mechanism.

For example, with $m=2$ the recurrence is

$$
\|P_{j+1}\|\leq\frac12\|P_j\|+\frac C2,
$$

so after $r$ steps

$$
\|P_r\|\leq2^{-r}\|P_0\|+C(1-2^{-r}).
$$

Every starting point therefore enters any ball of radius strictly larger than $C$. The number of steps depends on the starting point, but the terminal ball and the generating set do not. This distinction is why the argument proves finite generation even though it supplies no uniform bound on the length of all descent expansions.

### 8.2 Applying weak Mordell--Weil

Let $A/K$ be an abelian variety and choose a symmetric ample line bundle $L$. Put

$$
\|P\|=\sqrt{\widehat h_L(P)}
\qquad(P\in A(K)).
$$

Quadraticity gives $\|mP\|=m\|P\|$ for positive $m$. Cauchy--Schwarz gives the triangle inequality. Northcott, together with the bounded difference $h_L-\widehat h_L$, makes every ball finite. Finally Theorem 6.2 of Book 40 gives the finite quotient $A(K)/mA(K)$ for every integer $m\geq2$. Its hypotheses are exactly the present ones: $K$ is a number field and $A/K$ is an abelian variety. No polarization, semistability, or prior finite-generation hypothesis occurs in that theorem.

To recall exactly what is imported in the last sentence, multiplication by $m$ is an isogeny

$$
0\longrightarrow A[m]\longrightarrow A
\xrightarrow{[m]}A\longrightarrow0.
$$

Because $K$ has characteristic zero, $A[m]$ is finite étale, although the descent argument is naturally stated in fppf cohomology. Its Kummer boundary injects

$$
A(K)/mA(K)\hookrightarrow H^1(K,A[m]). \tag{8.4a}
$$

At places of good reduction not dividing $m$, the local Kummer image is the unramified subgroup. Hence every global Kummer class lies in cohomology unramified outside one finite set consisting of the archimedean places, places over $m$, and places of bad reduction. Imposing the finitely many exceptional local Kummer conditions defines the finite group $\operatorname{Sel}_m(A/K)$. The injection (8.4a) factors through it. This is precisely weak Mordell--Weil; it assumes neither finite generation nor finiteness of the entire Tate--Shafarevich group.

One may use any single $m\geq2$. Choosing a larger $m$ changes the finite representatives and the contraction factor, but not the conclusion. In particular the height construction with an auxiliary $q$ and the descent quotient modulo $m$ need not use the same integer. Quadraticity for every integer connects them.

Every hypothesis of Lemma 8.1 is now proved. No finiteness of the full Tate--Shafarevich group is used: weak Mordell--Weil follows from finiteness of the $m$-Selmer group at one fixed level, and height descent handles the infinite iteration.

### 8.3 The Mordell--Weil theorem

**Theorem 8.2 (Mordell--Weil).** If $A$ is an abelian variety over a number field $K$, then $A(K)$ is a finitely generated abelian group.

**Proof.** An abelian variety is projective and possesses an ample line bundle. Symmetrizing it produces a symmetric ample $L$. Section 8.2 verifies the hypotheses of Lemma 8.1, which proves finite generation. $\square$

No polarization needs to be specified in the statement, although choosing one supplies the height. Conversely every polarized abelian variety is an abelian variety, so the theorem applies with the height attached to a positive multiple of its polarization.

By the structure theorem for finitely generated abelian groups,

$$
A(K)\simeq A(K)_{\mathrm{tors}}\oplus\mathbf Z^r \tag{8.4}
$$

for a unique integer $r\geq0$, the **Mordell--Weil rank**. The splitting is not canonical, but the torsion subgroup and rank are.

### 8.4 Torsion, rank, and lattices

Theorem 6.3 identifies torsion intrinsically:

$$
A(K)_{\mathrm{tors}}=\{P\in A(K):\widehat h_L(P)=0\}. \tag{8.5}
$$

Northcott makes this set finite. On the free quotient, the height pairing is positive definite. Choosing a basis $P_1,\ldots,P_r$ identifies the free quotient with a lattice in $\mathbf R^r$, with Gram matrix

$$
(\langle P_i,P_j\rangle_L)_{i,j}.
$$

Its determinant is positive when $r>0$. Replacing the basis multiplies the Gram matrix on both sides by an integral matrix of determinant $\pm1$, so the determinant is basis-independent. Replacing $L$ changes its scale, as it should.

The proof is qualitative. It becomes an enumeration procedure only when one can compute representatives for $A(K)/mA(K)$, evaluate or bound canonical heights, and determine a search radius. Book 40 explains the finite descent data; the present argument proves that a finite generating set exists without claiming that every required bound is practically sharp.

The construction in Lemma 8.1 gives a little more information. Once representatives $R_i$ and a valid radius $R>C/(m-1)$ are known, every group element has an expansion (8.3) ending in the finite set

$$
S_R=\{P\in A(K):\widehat h_L(P)\leq R^2\}.
$$

Thus $S_R\cup\{R_1,\ldots,R_s\}$ is a generating set. If one has only an ordinary height $h_L$, the uniform comparison (6.2) converts the canonical bound $R^2$ into an explicit ordinary-height bound. The logical theorem needs existence of the comparison constant; an effective computation must actually estimate it.

## 9. Examples and diagnostic boundaries

Examples reveal which parts of the proof are formal and which are genuinely arithmetic. They also expose normalization errors that can be hidden in an abstract statement.

### 9.1 Projective space and rational numbers

For $[a:b]\in\mathbf P^1(\mathbf Q)$ with coprime integers $a,b$,

$$
h([a:b])=\log\max(|a|,|b|).
$$

The set of points of height at most $B$ has primitive representatives in the square $[-e^B,e^B]^2$, hence is finite. The maps $z\mapsto z^n$ satisfy

$$
h(\alpha^n)=|n|h(\alpha),
$$

which is linear in $|n|$, not quadratic. Projective space has no abelian group law compatible with this map. Quadratic growth in Mordell--Weil theory comes from $[n]^*L\simeq L^{n^2}$ on an abelian variety, not from height alone.

### 9.2 Elliptic curves

Let $E/K$ be an elliptic curve with identity $O$. The line bundle $L=\mathcal O_E(2[O])$ is symmetric and ample. If $x:E\to\mathbf P^1$ is the $x$-coordinate in a Weierstrass model, then

$$
x^*\mathcal O_{\mathbf P^1}(1)\simeq\mathcal O_E(2[O]),
$$

so

$$
h_L(P)=h(x(P))+O(1). \tag{9.1}
$$

Our normalization therefore gives

$$
\widehat h_L(P)=\lim_{r\to\infty}4^{-r}h(x([2^r]P)). \tag{9.2}
$$

Many elliptic-curve texts call one half of (9.2) the canonical height, because they attach the divisor $[O]$ rather than $2[O]$. Both conventions are valid; the bundle must be stated. With the present $L$, the pairing diagonal is exactly (9.2).

If $P$ is torsion, the multiples $[n]P$ form a finite set and (9.2) is zero. If $P$ is nontorsion, positivity says the values $h(x([n]P))$ grow as

$$
h(x([n]P))=n^2\widehat h_L(P)+O(1).
$$

This growth is what prevents unlimited division inside $E(K)$.

The bounded error can also be seen directly from a Weierstrass equation. The duplication formula writes

$$
x([2]P)=\frac{F_4(x(P))}{G_4(x(P))},
$$

where numerator and denominator are relatively prime homogeneous forms of degree $4$ after the affine coordinate is homogenized. At a place of good integral reduction their local maximum has exactly fourth-degree growth unless both reductions vanish, which coprimality excludes. At the finitely many remaining places, coefficient estimates and the reverse Nullstellensatz bound give a uniform error. Hence

$$
|h(x([2]P))-4h(x(P))|\leq C_E.
$$

The general line-bundle proof is preferable because it is independent of a Weierstrass equation and works in every dimension, but this calculation shows concretely where the bounded defect comes from.

For distinct nontorsion points $P,Q$, the number $\langle P,Q\rangle_L$ need not be zero or positive. Cauchy--Schwarz is the exact constraint. If $Q=nP$, then bilinearity gives

$$
\langle P,Q\rangle_L=n\widehat h_L(P),
$$

and equality holds in Cauchy--Schwarz. Thus the pairing recognizes rational linear dependence in the same way as an ordinary Euclidean inner product once torsion is removed.

### 9.3 Products

Let $A=A_1\times A_2$ and let

$$
L=p_1^*L_1\otimes p_2^*L_2
$$

for symmetric ample $L_i$. Then $L$ is symmetric ample and additivity plus functoriality gives

$$
\widehat h_L(P_1,P_2)
=\widehat h_{L_1}(P_1)+\widehat h_{L_2}(P_2). \tag{9.3}
$$

The pairing is the orthogonal direct sum of the two pairings, and

$$
\operatorname{rank}A(K)
=\operatorname{rank}A_1(K)+\operatorname{rank}A_2(K).
$$

If one omits the second factor and uses $p_1^*L_1$, the bundle is not ample and the height vanishes on $\{0\}\times A_2$. This is the simplest check that positivity cannot be replaced by symmetry alone.

### 9.4 Why the hypotheses matter

Four failures mark the boundary of the theorem.

First, properness is central to Northcott through projective embedding. Finitely generated unit groups over number fields require a different argument; they are not obtained by treating $\mathbf G_m$ as an abelian variety.

Second, a number field is essential. Over $\mathbf C$, an abelian variety has uncountably many points. Over an algebraically closed function field, constant points can all have height zero. Function-field Mordell--Weil statements require a trace term and cannot be copied from this proof unchanged.

Third, symmetry is needed for quadraticity. A general ample $L$ still has Northcott, but $[n]^*L$ contains both quadratic and linear parts as in (5.4). Symmetrization isolates the positive quadratic part.

Fourth, weak Mordell--Weil and height finiteness play different roles. Height balls may be finite while there are infinitely many residue classes modulo $m$; a finite quotient may exist while repeated division never terminates. The theorem needs both.

## 10. The finite-generation package for quotients

Later arithmetic arguments often construct an abelian variety indirectly—as a subvariety, a quotient of a Jacobian, or a member of an isogeny class. Mordell--Weil applies to the resulting abelian variety itself, but it is useful to state precisely what passes through these constructions.

### 10.1 Abelian subvarieties and quotients

Let $A/K$ be an abelian variety and $B\subseteq A$ an abelian subvariety. Then $B(K)$ is a subgroup of the finitely generated group $A(K)$, hence is finitely generated. This conclusion could also be obtained by applying Mordell--Weil directly to $B$.

If $q:A\to C$ is a quotient homomorphism with connected kernel, then $C$ is an abelian variety and $C(K)$ is finitely generated by Theorem 8.2. One should not claim that $A(K)\to C(K)$ is necessarily surjective: its cokernel maps into the torsor group of the kernel. Finite generation of $C(K)$ comes from applying the theorem to $C$, not from unsupported surjectivity on rational points.

If $q$ is an isogeny, the cokernel $C(K)/qA(K)$ is finite by weak Mordell--Weil for the isogeny. Pullback compares canonical heights exactly as in (7.8), so rank is invariant under isogeny. Products add ranks by Section 9.3.

For a smooth projective geometrically connected curve $C/K$ with a rational divisor class of degree one, the Abel--Jacobi map sends

$$
C(K)\longrightarrow J(K),
\qquad P\longmapsto[P-D_0],
$$

where $J$ is the Jacobian. Mordell--Weil says that the ambient group $J(K)$ is finitely generated. This does not by itself prove that $C(K)$ is finite: a finitely generated abelian group can contain infinitely many points, and the image of a curve inside its Jacobian requires further geometry. What the theorem supplies is a finite-rank arithmetic lattice in which later curve arguments can work.

Likewise, if an algebra of correspondences acts on $J$ and an idempotent up to isogeny selects a factor, the image and complementary kernel are abelian subquotients. Their rational points are finitely generated and their ranks are stable under replacing the factor by an isogenous one. None of this requires the correspondence algebra to preserve a chosen line bundle exactly; averaging or pulling back a polarization supplies a comparable canonical height.

### 10.2 Base change, trace, and restriction

For a finite extension $F/K$, inclusion gives $A(K)\subseteq A(F)$. Both groups are finitely generated. If $F/K$ is Galois, then

$$
A(K)=A(F)^{\operatorname{Gal}(F/K)}.
$$

For any finite extension, the trace homomorphism on Weil restrictions sends $P\in A(F)$ to the sum of its conjugates and satisfies

$$
\operatorname{Tr}_{F/K}(P)=[F:K]P
\qquad(P\in A(K)). \tag{10.1}
$$

Thus restriction on $A(K)\otimes\mathbf Q$ is injective and trace is a rational left inverse up to the degree. Canonical heights formed from a $K$-bundle are absolute, so the numerical value of $\widehat h_L(P)$ does not change when computed over the larger field; the local degrees and denominator change compatibly as in Section 2.1.

### 10.3 The Eisenstein-quotient input

The form needed in the Eisenstein-quotient argument is the following direct corollary.

**Corollary 10.1.** Let $J/K$ be a Jacobian over a number field, and let

$$
q:J\longrightarrow A
$$

be a quotient abelian variety defined over $K$. Then

$$
A(K)\simeq A(K)_{\mathrm{tors}}\oplus\mathbf Z^r
$$

for some finite $r$, and every subgroup and every quotient of $A(K)$ is finitely generated.

**Proof.** The quotient $A$ is an abelian variety, hence $A(K)$ is finitely generated by Theorem 8.2. The structure theorem gives the displayed decomposition. Subgroups and quotients of a finitely generated abelian group are finitely generated. $\square$

In particular, over $K=\mathbf Q$, any Eisenstein quotient of a modular Jacobian has a finitely generated group of rational points. Further arguments may show that a particular quotient has rank zero or identify its torsion, but those are additional arithmetic inputs. The conclusion established here is exactly the unconditional finite-generation statement: no claim about the rank or torsion order is hidden in it.

## 11. From point heights to moduli heights

The preceding chapters control points on one fixed abelian variety. A different arithmetic
question asks whether only finitely many abelian varieties can occur when dimension and bad
reduction are fixed. That question is the entrance to the Faltings--Tate theorem. It uses the
same product formula and Northcott principle, but the point whose height must be bounded is now
a point of an abelian-moduli space.

This distinction is load-bearing. The Néron--Tate height proves finite generation of
$A(K)$ after $A$ has been chosen. It does not put a bound on the height of $A$ itself.

### 11.1 The exact downstream question

Let $A/K$ be an abelian variety and let $\ell$ be a rational prime. Write

$$
T_\ell A=\varprojlim_n A[\ell^n](\overline K),
\qquad
V_\ell A=T_\ell A\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
\tag{11.1}
$$

The arithmetic statement needed by the later curve-carrier construction is

$$
\boxed{(\mathrm{TS})_{A,K,\ell}\quad
V_\ell A\text{ is a semisimple }\mathbf Q_\ell[G_K]\text{-module}.}
\tag{11.2}
$$

Semisimple means that every $G_K$-stable subspace has a $G_K$-stable complement. It is not the
semisimplicity of the isogeny category from Book 36. Poincaré reducibility splits an actual
abelian subvariety up to isogeny; a general $G_K$-stable $\mathbf Q_\ell$-subspace has not yet
been shown to arise from an abelian subvariety. Treating it as one would assume the conclusion.

For a smooth projective geometrically connected curve $C/K$ with Jacobian $J$, the comparison
constructed in Book 36 is

$$
T_\ell J\simeq H^1_{\mathrm{et}}
(C_{\overline K},\mathbf Z_\ell(1)).
\tag{11.3}
$$

Consequently $(\mathrm{TS})$ for $J$ gives semisimplicity of
$H^1_{\mathrm{et}}(C_{\overline K},\mathbf Q_\ell)$: duals and Tate twists do not change
semisimplicity. This is the complete ambient input later denoted
$(\mathrm{SS}_{\mathrm{array}})$ when finitely many curve carriers and coefficient primes are
under consideration.

### 11.2 Why Mordell--Weil does not answer it

Mordell--Weil concerns the discrete group $A(K)$. The Tate module records all geometric
$\ell$-power torsion and its continuous Galois action. Neither finite generation of $A(K)$ nor
finiteness of $A(K)/\ell A(K)$ produces invariant complements in (11.1).

There is also no averaging argument. The image of $G_K$ in
$\operatorname{GL}(T_\ell A)$ is compact, but its order is usually divisible by arbitrarily
large powers of $\ell$. A continuous representation of the compact group $\mathbf Z_\ell$
can be unipotent:

$$
x\longmapsto
\begin{pmatrix}1&x\\0&1\end{pmatrix}.
\tag{11.4}
$$

Thus compactness is enough to produce a stable lattice, not enough to split the rational
representation. Polarization is likewise insufficient by itself: a stable subspace may be
degenerate for the alternating form, so its orthogonal need not be a complement.

### 11.3 The noncircular proof architecture

The Faltings--Tate route separates into four implications:

$$
\begin{array}{c}
\text{arithmetic height bound on polarized moduli}
+\text{ Zarhin factor cancellation and }K\text{-descent}
\Longrightarrow \text{Faltings--Shafarevich finiteness},\\
\text{Faltings--Shafarevich finiteness}
\Longrightarrow \text{finiteness of each }K\text{-isogeny class},\\
\text{finite isogeny class}
\Longrightarrow \text{finitely many stable Tate-lattice types},\\
\text{finitely many stable lattice types}
\Longrightarrow (\mathrm{TS}).
\end{array}
\tag{11.5}
$$

The last three arrows are algebraic and are proved completely in Chapters 14--16. The first
arrow contains two parts of the deep Faltings input: the numerical height bound and the
factor-cancellation/descent passage from the stabilized principally polarized objects back to
the original abelian varieties. Chapters 12--13 identify both at theorem level. The distinction prevents a
moduli point that is merely integral outside finitely many primes from being declared to have
bounded height.

## 12. The Faltings height and the moduli comparison

The height of an abelian variety is the Arakelov degree of its Hodge line. Its finite-place
lattice measures integral invariant differentials; its archimedean metric measures their
period volume. The product formula makes the resulting number independent of the differential
used to compute it.

### 12.1 The metrized Hodge line

First suppose that $A/K$ has semiabelian reduction everywhere, and let $\mathcal A^0$ be the
identity component of its Néron model over $\mathcal O_K$. Put

$$
\omega_{\mathcal A}
=e^*\det\Omega^1_{\mathcal A^0/\mathcal O_K}.
\tag{12.1}
$$

This is an invertible $\mathcal O_K$-module inside the one-dimensional $K$-space
$\det H^0(A,\Omega^1_{A/K})$. For an embedding $\sigma:K\hookrightarrow\mathbf C$ and a
top differential $\eta$, use the translation-invariant metric

$$
\|\eta\|_\sigma^2
=\frac{i^{g^2}}{(2\pi)^g}
\int_{A_\sigma(\mathbf C)}\eta\wedge\overline\eta,
\qquad g=\dim A.
\tag{12.2}
$$

Changing the harmless constant $(2\pi)^{-g}$ changes every height in fixed dimension by one
fixed additive constant. Fixing it now makes all later comparisons unambiguous.

Choose $0\ne\eta$ in the generic Hodge line. The Arakelov degree is

$$
\widehat{\deg}(\overline\omega_{\mathcal A})
=\log\#(\omega_{\mathcal A}/\mathcal O_K\eta)
-\sum_{\sigma:K\hookrightarrow\mathbf C}\log\|\eta\|_\sigma,
\tag{12.3}
$$

where a fractional-ideal interpretation is used if $\eta$ does not generate a submodule.
Multiplying $\eta$ by $a\in K^\times$ changes the first term by the finite valuation of $(a)$
and the second by its archimedean norm. The product formula cancels them. Thus

$$
h_F(A/K)=\frac{1}{[K:\mathbf Q]}
\widehat{\deg}(\overline\omega_{\mathcal A})
\tag{12.4}
$$

is well defined. This is the semistable Faltings height in the convention of (12.2).

The formula displays why an ordinary projective height is not enough. At finite places one
needs the particular lattice of invariant differentials, while at infinity one needs a metric
defined by integration on the complex torus. Both pieces enter the product formula.

### 12.2 Base change and stable height

Under an extension $L/K$, the pulled-back Hodge lattice need not equal the Hodge lattice of the
Néron model over $\mathcal O_L$ at places where reduction improves. Their index is the base-change
conductor. Accordingly the naive value $h_F(A/K)$ need not be invariant before semistable
reduction.

If $A$ becomes semistable over $L$, define its stable height by

$$
h_F^{\mathrm{st}}(A)=h_F(A_L/L).
\tag{12.5}
$$

Assume the semistable Hodge-lattice base-change theorem recorded in Section 13.5. Once
semistability holds, that theorem identifies invariant differentials after every further finite
base change, while the archimedean terms repeat with total local degree. Formula (2.2) then
proves that (12.5) is independent of a further extension. Making (12.5) available for every
abelian variety requires both potential semistable reduction and this Hodge-lattice
base-change theorem. Neither is a consequence of the Néron-model construction in Book 38;
both remain among the specialized prerequisites recorded in Section 13.5.

### 12.3 The isogeny formula

The behavior under isogeny explains both the power and the limitation of Faltings height. Let

$$
f:A\longrightarrow B
\tag{12.6}
$$

be a $K$-isogeny between everywhere semistable abelian varieties, and enlarge $K$ once if
necessary so that the relevant finite kernel and semiabelian models have the stated form. Pullback
of invariant differentials gives an injection of Hodge lattices

$$
f^*:\omega_{\mathcal B}\hookrightarrow\omega_{\mathcal A}
\tag{12.7}
$$

with finite cokernel $Q_f$. At a complex embedding, change of variables under the covering
$f:A(\mathbf C)\to B(\mathbf C)$ gives

$$
\|f^*\eta\|_{A,\sigma}^2
=(\deg f)\|\eta\|_{B,\sigma}^2.
\tag{12.8}
$$

Compute both Arakelov degrees with $\eta$ and $f^*\eta$. The finite lattice index contributes
$\log\#Q_f$ and (12.8) contributes one half of $\log\deg f$ at every embedding. Hence

$$
\boxed{
h_F(B)-h_F(A)
=\frac12\log\deg f
-\frac{1}{[K:\mathbf Q]}\log\#Q_f.}
\tag{12.9}
$$

The formula passes the multiplication test. For $f=[n]$, one has
$\deg[n]=n^{2g}$ and $Q_f\simeq\omega_{\mathcal A}/n^g\omega_{\mathcal A}$, whose order is
$n^{g[K:\mathbf Q]}$; the two terms cancel because source and target are the same variety.

Since the second term in (12.9) is nonpositive,

$$
h_F(B)\leq h_F(A)+\frac12\log\deg f.
\tag{12.10}
$$

This inequality does not bound the heights of all varieties isogenous to $A$: the degrees of
the isogenies can be unbounded. Replacing that missing bound by (12.10) is one of the standard
false shortcuts in this argument.

### 12.4 Theta coordinates and moduli height

Fix a dimension $g$, a polarization type, and an integer $N\geq3$ invertible on the base. A
symplectic full level-$N$ structure removes automorphisms and places the polarized abelian
variety on a fine quasi-projective moduli scheme $\mathcal M_{g,d,N}$. A sufficiently high
power of the polarizing bundle has a theta group. Choosing a theta frame gives projective
coordinates for the fiber and, after taking invariant equations, projective coordinates for
the moduli point

$$
x(A,\lambda,\alpha_N)\in\mathcal M_{g,d,N}(K).
\tag{12.11}
$$

Once a projective closure and an ample moduli line are fixed, Chapter 4 gives a Weil height
$h_{\mathrm{mod}}(x)$. Northcott immediately proves:

**Lemma 12.1 (bounded moduli height gives finiteness).** Fix $K,g,d,N$ and a projective
moduli presentation. There are only finitely many $K$-isomorphism classes of triples
$(A,\lambda,\alpha_N)$ whose moduli height is at most a fixed constant.

**Proof.** The points (12.11) have degree one over $K$. Projective Northcott gives finitely
many such points of bounded height. Fine level means that a point represents one isomorphism
class, not merely a geometric orbit. $\square$

To connect this elementary lemma with (12.4), one must compare the projective moduli line with
the Hodge line carrying the $L^2$ metric. Algebraically, determinant-of-cohomology and theta
transformation formulas identify fixed positive tensor powers of the two lines. Metrically, the
comparison asks for uniform estimates on theta norms, including their growth toward the
degeneration boundary. The desired conclusion has the shape

$$
h_{\mathrm{mod}}(x(A,\lambda,\alpha_N))
\leq c_1 h_F^{\mathrm{st}}(A)+c_2+\operatorname{bdry}(A),
\tag{12.12}
$$

with a reverse inequality of the same kind. The boundary term is an arithmetic intersection
with the degeneration divisor; it is not a bounded $O(1)$ on the whole open moduli space.

### 12.5 What the comparison actually proves

If both $h_F^{\mathrm{st}}(A)$ and the boundary contribution in (12.12) are bounded in a
family, Lemma 12.1 proves finiteness. Conversely, a bound for the moduli height controls the
Faltings height by the reverse comparison. This is the useful height/moduli-height bridge.

The bridge alone gives no bound. Good reduction outside a fixed set says that the boundary
intersection is supported on that set, but it does not bound the multiplicity at those primes
or the archimedean contribution. The theorem that supplies a uniform global bound is the deep
arithmetic slope estimate in the next chapter. It cannot be replaced by the ordinary height
machine, by (12.9), or by the quasi-projectivity of the moduli scheme.

## 13. The Faltings finiteness gate

We now state the precise finiteness theorem from which the Tate argument starts and audit the
proof ingredients that are and are not present in the earlier sequence.

### 13.1 The required Shafarevich statement

For a number field $K$, a finite set $S$ of finite places, and an integer $g\geq1$, let

$$
\boxed{
(\mathrm{FS})_{K,S,g}:\quad
\#\{A/K:\dim A=g,\ A\text{ has good reduction outside }S\}/\simeq_K<\infty.}
\tag{13.1}
$$

The polarized version fixes a polarization type and asserts finiteness of polarized
isomorphism classes. The unpolarized statement follows in the full Faltings proof by Zarhin's
trick together with the integral cancellation and descent argument for the resulting factors.
Neither the polarization nor the cancellation may be discarded: an arbitrary abelian variety
need not carry a principal polarization over $K$, and an isogeny-class statement is not an
isomorphism-class statement.

The theorem needed for semisimplicity is weaker than all of (13.1): for one fixed $A/K$, only
the $K$-isomorphism classes in its $K$-isogeny class must be finite. Nevertheless (13.1) is the
standard uniform source, because every member of that isogeny class has the same good-reduction
locus by Section 14.1.

### 13.2 Level fields and integral moduli points

Several reductions toward (13.1) are already formal. We first record the exact elementary
part of Zarhin's trick. Choose a $K$-rational polarization
$\lambda:A\to A^\vee$. If $n$ annihilates $\ker\lambda$, the quotient property of
$\lambda$ factors $[n]_A$ through a map $\mu:A^\vee\to A$; on complex tangent spaces it is
$n\lambda^{-1}$ and is again positive, hence is the dual polarization. Thus

$$
\mu\lambda=[n]_A,
\qquad
\lambda\mu=[n]_{A^\vee}.
$$

Write $n-1=a^2+b^2+c^2+d^2$ and let

$$
Q=
\begin{pmatrix}
a&b&c&d\\
-b&a&-d&c\\
-c&d&a&-b\\
-d&-c&b&a
\end{pmatrix},
\qquad
Q^{\mathsf t}Q=QQ^{\mathsf t}=(n-1)I_4.
$$

On $A^4\times(A^\vee)^4$, the symmetric homomorphism to its dual

$$
\lambda_Z=
\begin{pmatrix}
\lambda I_4&Q\\
Q^{\mathsf t}&\mu I_4
\end{pmatrix}
$$

is an isomorphism: its inverse is obtained by replacing the diagonal blocks by
$\mu I_4,\lambda I_4$ and both off-diagonal blocks by their negatives. At every complex
embedding, the Schur complement of the positive block $\lambda I_4$ is
$\mu I_4-Q^{\mathsf t}\lambda^{-1}Q=\lambda^{-1}I_4>0$. Thus $\lambda_Z$ is a
principal polarization. It is not canonical--it depends on $\lambda$ and on the four-square
matrix--but existence is all that is used below. Consequently Zarhin's construction

$$
Z(A)=(A\times A^\vee)^4
\tag{13.2}
$$

has a $K$-rational principal polarization. For fixed $g$, its dimension is fixed. Choose
$N\geq3$. The field generated by $Z(A)[N]$ has degree bounded by
$|\operatorname{GSp}_{16g}(\mathbf Z/N\mathbf Z)|$. If $A$ has good reduction outside $S$,
this level field is unramified outside $S$ and the primes dividing $N$: at every other place,
$Z(A)$ extends to an abelian scheme and multiplication by $N$ is finite étale, so its torsion
points form an unramified Galois set. Bounded-degree local
extension finiteness and the following lemma therefore leave only finitely many possible level
fields.

**Lemma 13.1 (bounded ramification fields).** Fix a number field $K$, a finite set $T$ of
finite places, and an integer $D$. There are only finitely many $K$-isomorphism classes of
extensions $L/K$ of degree at most $D$ which are unramified outside $T$.

**Proof.** For each $v\in T$, Book 2 gives only finitely many extensions of $K_v$ of degree at
most $D$. Their different exponents therefore have a common bound. The relative discriminant
$\mathfrak d_{L/K}$ is supported on $T$, and its exponent at $v$ is the sum of the local
different exponents weighted by residue degrees. Both the number and the degrees of the local
factors are at most $D$, so $N_{K/\mathbf Q}\mathfrak d_{L/K}$ is bounded in terms of
$K,T,D$. The discriminant tower formula

$$
|d_L|=|d_K|^{[L:K]}
N_{K/\mathbf Q}\mathfrak d_{L/K}
\tag{13.2a}
$$

therefore bounds both $[L:\mathbf Q]$ and $|d_L|$.

We recall why these two bounds give only finitely many fields. In the Minkowski embedding,
$\mathcal O_L$ has covolume $2^{-r_2}|d_L|^{1/2}$. The successive-minima form of the
convex-body argument chooses $n=[L:\mathbf Q]$ independent algebraic integers of uniformly
bounded Euclidean length: the product of their successive minima is bounded by a
dimension-dependent multiple of the covolume, while every nonzero algebraic integer has
Euclidean length bounded below because its norm is a nonzero integer. Their span has uniformly
bounded index, so a Hermite-normal-form adjustment gives an integral basis
$e_1,\ldots,e_n$ whose conjugates are uniformly bounded. The embedding matrix of this basis
has determinant of absolute value $|d_L|^{1/2}$, bounded below by $1$ and above by the fixed
discriminant bound. Cramer's rule therefore bounds the integral structure constants in

$$
e_ie_j=\sum_k c_{ij}^k e_k.
\tag{13.2b}
$$

Only finitely many integer multiplication tables can occur. They determine the ring
$\mathcal O_L$ and hence its fraction field. Thus only finitely many fields $L$ occur. Each
has only finitely many embeddings of the fixed separable field $K$, so only finitely many
$K$-isomorphism classes occur. $\square$

After replacing $K$ by one of these finitely many level fields, (13.2) has full level and
defines a point on the fine moduli scheme.

At a place outside $S\cup\{v:v\mid N\}$, the abelian scheme and its level structure extend
over the valuation ring. The moduli point is consequently integral there. We have reached

$$
x(Z(A),\lambda_Z,\alpha_N)
\in\mathcal M_{8g,1,N}(\mathcal O_{L,S_L}).
\tag{13.3}
$$

This reduction uses bounded extension degree, level rigidity, and extension of good abelian
schemes. It still has not produced a height bound.

### 13.3 The missing arithmetic height bound

The decisive missing height assertion can be expressed in the following sufficient
existential form: for every $A$ in (13.1), one can choose a Zarhin polarization $\lambda_Z$
as above and a full level basis $\alpha_N$ over its level field so that

$$
(\mathrm{FH})_{K,S,g}:
\quad
\sup h_{\mathrm{mod}}
\bigl(x(Z(A),\lambda_Z,\alpha_N)\bigr)<\infty,
\tag{13.4}
$$

where $A$ ranges over the varieties in (13.1), $L$ ranges over the finitely many level fields
from Section 13.2, and the height is normalized by $[L:\mathbf Q]$. After the metric comparison
is established, a standard sufficient route to (13.4) is a joint bound for the stable Faltings
height and the arithmetic boundary term.

Given (13.4), Lemma 12.1 gives finitely many $L$-isomorphism classes of principally polarized
$Z(A)_L$ with level, as $L$ ranges over the finite list in Section 13.2. This stabilized
polarized finiteness is not yet (13.1): one must remove level, descend from $L$ to $K$, and
recover only finitely many $K$-isomorphism classes of the factors $A$. Let
$(\mathrm{ZC})_{K,g}$ denote the integral Zarhin factor-cancellation and descent theorem making
exactly that passage. The formal implication is therefore

$$
(\mathrm{FH})_{K,S,g}+(\mathrm{ZC})_{K,g}
\Longrightarrow(\mathrm{FS})_{K,S,g}
\tag{13.5}
$$

Neither input on the left is proved here. The compactification, metric comparison, and slope
estimates below are needed to establish $(\mathrm{FH})$; factor cancellation and descent are a
separate post-Northcott input.

The height part, (13.4), comes in the Faltings proof from arithmetic intersection
theory on a toroidal compactification of Siegel moduli. One extends the Hodge bundle with its
logarithmic metric, applies arithmetic Riemann--Roch or the equivalent arithmetic
Hilbert--Samuel slope inequality to powers of a theta bundle, and controls every boundary term
by the semistable degeneration data. The product formula then converts local discriminant and
period estimates into a global upper bound. The archimedean theta estimate is essential: an
algebraic extension of the Hodge line without its metric does not control (12.2).

### 13.4 Why integrality is not a substitute

An integral point of a quasi-projective arithmetic scheme need not have bounded height. The
simplest example is

$$
\mathbf G_m(\mathbf Z[1/p])
=\{\pm p^n:n\in\mathbf Z\}.
\tag{13.6}
$$

Every point is integral outside $p$, while

$$
h([1:p^n])=|n|\log p
\tag{13.7}
$$

is unbounded. The same logical issue occurs in (13.3): support of the boundary is controlled,
but its multiplicity can grow. Northcott begins only after a numerical height bound has been
proved.

Nor does the isogeny formula repair the problem. Inequality (12.10) contains
$\log\deg f$, and no preceding theorem bounds the least degree of an isogeny to every member
of the class. Assuming such a bound is another form of assuming isogeny finiteness.

### 13.5 Exact prerequisite ledger

The earlier books provide projective heights and Northcott, quasi-projective PEL moduli with
theta frames, coherent Hodge bundles, abelian schemes and their quotients, Néron models, and
polarizations. They do not provide the following specialized package:

1. potential semistable reduction for arbitrary abelian varieties, with the base-change
   formula for the Hodge lattice;
2. a toroidal or comparably strong arithmetic compactification of Siegel moduli carrying the
   canonical extension of the Hodge and theta bundles;
3. arithmetic intersection theory and arithmetic Riemann--Roch or Hilbert--Samuel in the
   dimension needed on that compactification;
4. the uniform archimedean theta-norm and nonarchimedean boundary estimates which prove
   (12.12) and the slope bound (13.4); and
5. the integral Zarhin factor-cancellation argument passing from the principally polarized
   stabilized objects to unpolarized $K$-isomorphism classes.

These are not general formal foundations such as tensor products, projective embeddings, or
ordinary Riemann--Roch on a curve. Together they are the deep Faltings finiteness proof. None is
proved in Chapters 1--12, and the catalog before this volume contains no source for the package.
Consequently this book does **not** assert (13.4), $(\mathrm{ZC})$, (13.1), or unconditional
Tate-module semisimplicity. The remaining chapters prove every implication after
$(\mathrm{FS})$, and in fact need only $(\mathrm{IF})$. Thus $(\mathrm{IF})$ is the first
irreducible arithmetic hypothesis in the Tate argument. The standard uniform route to it remains
conditional on the two-part Faltings--Shafarevich package in (13.5), rather than on the numerical
height bound alone.

## 14. From Faltings finiteness to finite isogeny classes

This chapter proves the geometric implication needed by Tate's lattice argument. No moduli
height occurs after this point.

### 14.1 Good reduction is preserved by isogeny

**Lemma 14.1.** Let $A$ and $B$ be abelian varieties over $K$ and let
$f:A\to B$ be a $K$-isogeny. At every finite place $v$, $A$ has good reduction if and only if
$B$ has good reduction.

**Proof.** Work first over the valuation ring $R=\mathcal O_{K_v}$. Suppose $A$ extends to an
abelian scheme $\mathcal A/R$. The kernel of $f$ is contained in $A[n]$ for some $n$. Its
schematic closure $\mathcal H$ in the finite flat group scheme $\mathcal A[n]$ is the flat
closure, hence is finite flat over the DVR. The quotient

$$
\mathcal B=\mathcal A/\mathcal H
\tag{14.1}
$$

exists as an abelian scheme by the quotient theorem for finite flat subgroup schemes. Its
generic fiber is $B$, so $B$ has good reduction. A dual isogeny $g:B\to A$ with
$gf=[n]$ gives the converse by the same argument. $\square$

The use of the flat closure matters at residue characteristic dividing $n$. Taking only the
set-theoretic closure of geometric torsion points would not produce a quotient abelian scheme.

### 14.2 The finite-isogeny-class consequence

Fix $A/K$ of dimension $g$, and let $S_A$ be its finite bad-reduction set. Every abelian
variety $B$ that is $K$-isogenous to $A$ has dimension $g$ and, by Lemma 14.1, good reduction
outside $S_A$. Therefore (13.1), if available, gives

$$
\#\{B/K:B\text{ is }K\text{-isogenous to }A\}/\simeq_K<\infty.
\tag{14.2}
$$

Only $K$-isomorphism classes are being counted. Geometric isomorphism is too weak for the
Galois-module argument, while finiteness merely up to isogeny is tautological because the set
being studied is already one isogeny class.

### 14.3 The precise conditional input

For later reuse, name the exact conclusion rather than all of Shafarevich finiteness:

$$
(\mathrm{IF})_{A/K}:
\quad\text{the }K\text{-isogeny class of }A
\text{ contains finitely many }K\text{-isomorphism classes}.
\tag{14.3}
$$

Sections 14.1--14.2 prove

$$
(\mathrm{FS})_{K,S_A,g}\Longrightarrow(\mathrm{IF})_{A/K}.
\tag{14.4}
$$

The Tate argument below uses exactly (14.3). Thus a future source may close the gap either by
proving the full height-and-cancellation package (13.5), by proving Faltings--Shafarevich
finiteness directly, or by proving (14.3) for the particular carrier Jacobians. No stronger
theorem is silently required.

## 15. Tate lattices and semisimplicity

The hard arithmetic geometry has now been compressed into (14.3). The remaining proof is a
short but delicate interaction between isogenies and integral representation theory.

### 15.1 Stable lattices are isogeny quotients

Let $T=T_\ell A$ and $V=V_\ell A$. The quotient $V/T$ is canonically the geometric
$\ell$-primary torsion:

$$
V/T\simeq A[\ell^\infty](\overline K).
\tag{15.1}
$$

Let $L\subset V$ be any full $G_K$-stable $\mathbf Z_\ell$-lattice. Multiplication by a power
of $\ell$ is a $G_K$-module isomorphism from $L$ to a homothetic lattice, so we may arrange

$$
T\subseteq L\subseteq\ell^{-n}T
\tag{15.2}
$$

for some $n$. Then

$$
H=L/T\subset V/T
\tag{15.3}
$$

is a finite $G_K$-stable subgroup of $A[\ell^\infty](\overline K)$. In characteristic zero,
finite torsion group schemes are étale, so Galois descent identifies $H$ with a finite
$K$-subgroup scheme of $A$. Form the quotient isogeny

$$
q_H:A\longrightarrow A_H=A/H.
\tag{15.4}
$$

The rational Tate map $V_\ell(q_H)$ is an isomorphism. Under the resulting identification of
$V_\ell A_H$ with $V$, one has

$$
V_\ell(q_H)^{-1}(T_\ell A_H)=L.
\tag{15.5}
$$

To verify (15.5), reduce modulo $T$. A vector of $V$ maps into the target Tate lattice exactly
when its torsion class is killed in the quotient by $H$, which is exactly the condition that
its class lie in $H=L/T$. This also passes the test $H=A[\ell]$: then $q_H=[\ell]$ and the
preimage of $T$ is $\ell^{-1}T$.

### 15.2 Finite isogeny classes give finite lattice type

**Proposition 15.1.** Assume $(\mathrm{IF})_{A/K}$. Up to isomorphism as
$\mathbf Z_\ell[G_K]$-modules, only finitely many $G_K$-stable full lattices occur in $V$.

**Proof.** Replace a lattice by a homothetic one satisfying (15.2); this does not change its
abstract $G_K$-module isomorphism class. Section 15.1 associates to it a quotient $A_H$ in
the $K$-isogeny class of $A$, and (15.5) identifies the lattice with $T_\ell A_H$. By
$(\mathrm{IF})_{A/K}$ there are only finitely many possible $K$-isomorphism classes of
$A_H$. A $K$-isomorphism induces an isomorphism of Tate lattices. $\square$

The proposition does not claim that two lattices giving isomorphic quotients are equal inside
$V$. Equality is unnecessary; Tate's criterion uses only their abstract integral
representation type.

### 15.3 Tate's lattice lemma

We prove the representation-theoretic engine in a form independent of abelian varieties.

**Lemma 15.2 (Tate's lattice criterion).** Let $k$ be a characteristic-zero nonarchimedean
local field with valuation ring $\mathcal O$, let $G$ be a group, and let $V$ be a
finite-dimensional continuous $k$-representation admitting a stable lattice. If there are only
finitely many isomorphism classes of full $G$-stable $\mathcal O$-lattices in $V$, then $V$ is
semisimple.

**Proof.** Let $R\subseteq\operatorname{End}_k(V)$ be the finite-dimensional $k$-algebra
generated by the image of $G$. Because $R$ acts faithfully on $V$, the representation $V$ is
semisimple exactly when the Jacobson radical $J=\operatorname{rad}R$ is zero. Indeed, if $V$
is semisimple then $J$ kills $V$ and faithfulness gives $J=0$; if $J=0$, the algebra $R$ is
semisimple Artinian and all of its modules are semisimple.

Assume for contradiction that $J\ne0$. Choose $a\geq2$ minimal with $J^a=0$ and put

$$
W=J^{a-1}V\ne0.
\tag{15.6}
$$

Fix a $G$-stable lattice $T$. The image of the $\mathcal O$-algebra $\mathcal O[G]$ inside
$\operatorname{End}_{\mathcal O}(T)$ is a finite $\mathcal O$-module and spans $R$; denote
it by $\Lambda$. Put

$$
I=\Lambda\cap J^{a-1}.
\tag{15.7}
$$

Then $I$ is a two-sided ideal of $\Lambda$, it spans $J^{a-1}$ over $k$, and

$$
IW=0,
\tag{15.8}
$$

because $J^{2a-2}=0$. Let $X=T\cap W$, a full lattice in $W$, and define

$$
T_n=T+\varpi^{-n}X
\qquad(n\geq0),
\tag{15.9}
$$

where $\varpi$ is a uniformizer. Both $T$ and $X$ are $\Lambda$-stable, so every $T_n$ is a
full $G$-stable lattice. Moreover

$$
T_n\cap W=\varpi^{-n}X,
\qquad
IT_n=IT.
\tag{15.10}
$$

The first equality follows by projecting $T_n$ to $V/W$; the second follows from (15.8).
Since $I$ spans $J^{a-1}$, $IT$ is a full lattice in $W$. Thus

$$
\delta(T_n)=
\operatorname{length}_{\mathcal O}
\frac{T_n\cap W}{IT_n}
=n\dim_kW+\delta(T_0).
\tag{15.11}
$$

This length is an isomorphism invariant of the $G$-lattice. A $G$-linear lattice isomorphism
extends to a $k$-linear map commuting with $R$; it therefore preserves the intrinsic subspace
$W=J^{a-1}V$ and carries $IT_n$ to the corresponding $IT_m$. Equation (15.11) shows that the
$T_n$ are pairwise nonisomorphic, contradicting the finiteness hypothesis. Hence $J=0$ and
$V$ is semisimple. $\square$

The growing length (15.11) is the obstruction hidden by a rational semisimplification. In a
nontrivial unipotent extension, rescaling the deepest radical layer creates infinitely many
integral extension depths. A finite isogeny class forbids precisely that phenomenon.

### 15.4 Conditional rational Tate-module semisimplicity

Combining Proposition 15.1 and Lemma 15.2 gives the desired theorem with its exact hypothesis.

**Theorem 15.3 (Tate semisimplicity from isogeny-class finiteness).** Let $A/K$ be an abelian
variety and let $\ell$ be a prime. If $(\mathrm{IF})_{A/K}$ holds, then

$$
V_\ell A\text{ is semisimple as a }\mathbf Q_\ell[G_K]\text{-module}.
\tag{15.12}
$$

In particular,

$$
(\mathrm{FS})_{K,S_A,\dim A}
\Longrightarrow(\mathrm{TS})_{A,K,\ell}
\quad\text{for every }\ell.
\tag{15.13}
$$

**Proof.** Proposition 15.1 supplies finitely many stable lattice types in $V_\ell A$.
Lemma 15.2 supplies semisimplicity. The implication (15.13) uses (14.4). $\square$

No Hom--Tate surjectivity, Frobenius-density theorem, or algebraicity of an arbitrary invariant
subspace occurs in this proof. The geometry is used exactly once, to turn a stable lattice into
an isogenous quotient.

## 16. The exact cohomological export

We now transport Theorem 15.3 through the elementary operations used by the curve-carrier
books. Every statement in this chapter remains conditional on $(\mathrm{IF})$ or on the
Faltings finiteness gate identified in Chapter 13.

### 16.1 Curves and Jacobians

**Corollary 16.1.** Let $C/K$ be a smooth projective geometrically connected curve and let
$J=\operatorname{Jac}(C)$. If $(\mathrm{IF})_{J/K}$ holds, then for every $\ell$,

$$
H^1_{\mathrm{et}}(C_{\overline K},\mathbf Q_\ell)
\quad\text{is semisimple as a }\mathbf Q_\ell[G_K]\text{-module}.
\tag{16.1}
$$

**Proof.** Theorem 15.3 makes $V_\ell J$ semisimple. Formula (11.3) identifies curve
cohomology with a Tate twist of this representation. If a representation is semisimple, so
are its dual and every character twist, because these operations carry direct sums of simple
modules to direct sums of simple modules. $\square$

The conclusion concerns global $G_K$-semisimplicity. It does not say that a local
Weil--Deligne operator is zero, and it does not make an integral packet projector split a Tate
lattice.

### 16.2 Coefficient extension, summands, and multiplicity spaces

Let $V$ be a semisimple $\mathbf Q_\ell[G]$-module and let $E/\mathbf Q_\ell$ be finite. The
image algebra $R$ from Lemma 15.2 is semisimple. Since characteristic zero extensions are
separable, $R\otimes_{\mathbf Q_\ell}E$ is semisimple, so

$$
V\otimes_{\mathbf Q_\ell}E
\tag{16.2}
$$

is semisimple. Every $G$-stable direct summand of (16.2) is semisimple. Therefore a rational
Hecke idempotent, after the finite scalar extension on which it is defined, preserves
semisimplicity of the selected block.

Suppose a Morita evaluation identifies a selected block with

$$
P\otimes_E W,
\tag{16.3}
$$

where $G$ acts trivially on the nonzero finite-dimensional coefficient module $P$ and acts on
$W$. Choose $p\in P$ and $\lambda\in P^\vee$ with $\lambda(p)=1$. The maps

$$
W\xrightarrow{w\mapsto p\otimes w}P\otimes W
\xrightarrow{\lambda\otimes1}W
\tag{16.4}
$$

are $G$-equivariant and their composite is the identity. Thus $W$ is a direct summand of the
ambient block and is semisimple. This proves the coefficient-extension, packet-idempotent, and
multiplicity-space steps without adding an arithmetic hypothesis.

### 16.3 The Hom--Tate boundary

Only faithfulness of the Tate realization is needed above. We prove that comparison and do not
claim the much stronger surjectivity theorem.

**Proposition 16.2 (faithful Hom--Tate comparison).** For abelian varieties $A,B/K$, the map

$$
\operatorname{Hom}_K(A,B)\otimes\mathbf Z_\ell
\longrightarrow
\operatorname{Hom}_{G_K}(T_\ell A,T_\ell B)
\tag{16.5}
$$

is injective.

**Proof.** Put $H=\operatorname{Hom}_K(A,B)$, which is finite free by Book 36. First let
$f\in H$ act trivially on $T_\ell A$. It kills $A[\ell^n]$ for every $n$. Since
$[\ell^n]:A\to A$ is the quotient by that finite subgroup, the quotient universal property
gives $f=f_n\circ[\ell^n]$ for some $f_n\in H$. Hence $f\in\ell^nH$ for every $n$, and
$\bigcap_n\ell^nH=0$ gives $f=0$.

Now let $u\in H\otimes\mathbf Z_\ell$ act trivially. For every $n$, choose $f_n\in H$ whose
class modulo $\ell^nH$ is the class of $u$. The action of $f_n$ on $T_\ell A/\ell^nT_\ell A$
is zero, so $f_n$ kills $A[\ell^n]$. The preceding quotient argument gives
$f_n\in\ell^nH$. Thus $u$ is zero modulo $\ell^n$ for every $n$, hence $u=0$. $\square$

Surjectivity of (16.5) is the full Hom--Tate isogeny theorem. It is not needed for
$(\mathrm{TS})$, for Corollary 16.1, or for the raw-to-global packet passage. Proving it would
require an additional graph-of-a-homomorphism approximation argument resting on the same
Faltings finiteness gate. It is therefore deliberately not cited as though it were an earlier
theorem and not included as an unused stronger conclusion.

### 16.4 The packet-carrier array

Let $\{C_i/K_i\}_{i=1}^r$ be the finite collection of smooth projective curve carriers used in
a packet array, and let $J_i$ be their Jacobians. If

$$
(\mathrm{IF})_{J_i/K_i}\qquad(1\leq i\leq r)
\tag{16.6}
$$

holds, Corollary 16.1 and Section 16.2 prove

$$
\boxed{(\mathrm{SS}_{\mathrm{array}})}
\tag{16.7}
$$

for every relevant coefficient characteristic: each ambient rational $H^1$ is globally
semisimple, and finite coefficient extension, packet projection, and Morita extraction retain
that property. Consequently a raw multiplicity representation equals its global
semisimplification and a locally computed nonzero monodromy operator is not lost merely by
passing to that semisimplification.

The full implication chain, with its unproved initial premises displayed, is

$$
[(\mathrm{FH})+(\mathrm{ZC})]\Longrightarrow(\mathrm{FS})
\Longrightarrow(\mathrm{IF})
\Longrightarrow(\mathrm{TS})
\Longrightarrow(\mathrm{SS}_{\mathrm{array}}).
\tag{16.8}
$$

Every arrow beginning with $(\mathrm{FS})\Rightarrow(\mathrm{IF})$ is proved here. The initial
arrow is available only after the compactification, height comparison, and slope estimates that
produce $(\mathrm{FH})$, and the separate theorem $(\mathrm{ZC})$, have been supplied; neither
input is established by the available prior books. Thus (16.7) remains conditional.
In particular, it would be incorrect to remove the packet-carrier ambient semisimplicity
blocker merely on the strength of the Tate lattice argument.

## 17. Synthesis

This volume contains two height arguments with the same Northcott endpoint but different
inputs. Keeping them side by side makes clear both the completed Mordell--Weil theorem and the
exact unfinished Faltings gate.

### 17.1 The two logical chains

For an abelian variety $A/K$, choose a symmetric ample line bundle $L$ and an integer $m\geq2$.
The unconditional point-height chain is

$$
\begin{array}{c}
\text{product formula}\Rightarrow h_{\mathbf P^n}
\Rightarrow\text{Northcott},\\
L^r\text{ very ample}\Rightarrow h_L\text{ with Northcott},\\
[m]^*L\simeq L^{m^2}\Rightarrow
\widehat h_L=h_L+O(1),\\
\text{cube identity}\Rightarrow
\widehat h_L(P+Q)+\widehat h_L(P-Q)
=2\widehat h_L(P)+2\widehat h_L(Q),\\
\text{weak Mordell--Weil}+\text{contracting height descent}
\Rightarrow A(K)\text{ finitely generated}.
\end{array}
\tag{17.1}
$$

The moduli-height chain is

$$
\begin{array}{c}
\text{metrized Hodge line}+\text{arithmetic boundary estimates}
\Rightarrow(\mathrm{FH}),\\
(\mathrm{FH})+(\mathrm{ZC})+\text{moduli Northcott}
\Rightarrow(\mathrm{FS})\Rightarrow(\mathrm{IF}),\\
(\mathrm{IF})\Rightarrow\text{finitely many stable Tate-lattice types},\\
\text{Tate's radical-length lemma}\Rightarrow(\mathrm{TS})
\Rightarrow(\mathrm{SS}_{\mathrm{array}}).
\end{array}
\tag{17.2}
$$

Every arrow in the last two lines of (17.2) is proved in Chapters 14--16. The first line is the
specialized arithmetic-geometry package absent from the established dependency chain.

### 17.2 Normalization and dependency ledger

The conventions used throughout are:

| Object | Normalization or status |
|---|---|
| finite absolute value over $p$ | $|p|_v=p^{-1}$ |
| complex absolute value | usual modulus, with local degree $n_v=2$ |
| absolute projective height | $[K:\mathbf Q]^{-1}\sum_v n_v\log\max_i|x_i|_v$ |
| canonical height | $\widehat h_L=\lim q^{-2r}h_L\circ[q^r]$ |
| Faltings metric | (12.2), fixed up to one dimension-dependent additive constant |
| stable Faltings height | normalized Arakelov degree after semistable reduction |
| finite isogeny input | $(\mathrm{IF})_{A/K}$ in (14.3) |
| proved Tate output | $(\mathrm{IF})_{A/K}\Rightarrow(\mathrm{TS})_{A,K,\ell}$ |
| unresolved uniform source | $(\mathrm{FH})_{K,S,g}$, $(\mathrm{ZC})_{K,g}$, and the package in Section 13.5 |

Changing $L$ to $L^r$ multiplies the canonical point height by $r$. Extending a field does
not change an absolute projective height, and it does not change the stable Faltings height once
semistability has been reached. These are separate assertions with separate proofs.

### 17.3 Conclusion

Weil height and the Néron--Tate limiting process complete the Mordell--Weil theorem: every
abelian variety over a number field has a finitely generated group of rational points, and the
same holds for every abelian quotient of a Jacobian.

For Tate-module semisimplicity, the reusable algebraic half is also complete. A stable Tate
lattice is the Tate lattice of an isogenous quotient. If the isogeny class has finitely many
$K$-isomorphism classes, only finitely many integral lattice types occur. Tate's
Jacobson-radical construction shows that a nonsemisimple rational representation would create
infinitely many types, a contradiction. Curve cohomology, coefficient factors, and multiplicity
spaces then inherit semisimplicity exactly as required by the packet-carrier array.

The remaining gap is not Hom--Tate linear algebra. The first exact arithmetic input is finite
isogeny classes. The standard uniform source is the Faltings--Shafarevich package: the arithmetic
height bound on Siegel moduli, with its semistable Hodge theory, compactification, metrized
Hodge/theta comparison, and slope and boundary estimates, together with the separate Zarhin
factor-cancellation and $K$-descent theorem. The existing height machine proves what follows
from a bound; it does not prove that bound from $S$-integrality or recover the original factors.
Until that package is supplied by a prior volume or proved here in full,
Faltings--Shafarevich finiteness remains unproved, while rational Tate-module semisimplicity and
$(\mathrm{SS}_{\mathrm{array}})$ are available only conditionally on the finite-isogeny-class
input, not as unconditional conclusions of the present corpus.
