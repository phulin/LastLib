# Heights, Mordell--Weil, and the Faltings--Tate Reduction

## Contents

1. [Why height completes descent](#1-why-height-completes-descent)
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
9. [Examples and scope](#9-examples-and-scope)
   - [Projective space and rational numbers](#91-projective-space-and-rational-numbers)
   - [Elliptic curves](#92-elliptic-curves)
   - [Products](#93-products)
   - [Why the hypotheses matter](#94-why-the-hypotheses-matter)
10. [Mordell--Weil under subvarieties and quotients](#10-mordell--weil-under-subvarieties-and-quotients)
    - [Abelian subvarieties and quotients](#101-abelian-subvarieties-and-quotients)
    - [Base change, trace, and restriction](#102-base-change-trace-and-restriction)
    - [The Eisenstein-quotient input](#103-the-eisenstein-quotient-input)
11. [The boundary of the elementary height method](#11-the-boundary-of-the-elementary-height-method)
    - [The distinct downstream question](#111-the-distinct-downstream-question)
    - [Why Mordell--Weil does not answer it](#112-why-mordell--weil-does-not-answer-it)
    - [The exact conditional chain](#113-the-exact-conditional-chain)
12. [Conditional Faltings height and the moduli comparison](#12-conditional-faltings-height-and-the-moduli-comparison)
    - [The metrized Hodge line](#121-the-metrized-hodge-line)
    - [Potential semistable reduction from curves](#122-potential-semistable-reduction-from-curves)
    - [Ramified semistable Hodge base change](#123-ramified-semistable-hodge-base-change)
    - [Base change and stable height](#124-base-change-and-stable-height)
    - [The isogeny formula](#125-the-isogeny-formula)
    - [Theta coordinates and moduli height](#126-theta-coordinates-and-moduli-height)
    - [What the comparison actually proves](#127-what-the-comparison-actually-proves)
13. [The conditional Shafarevich finiteness gate](#13-the-conditional-shafarevich-finiteness-gate)
    - [The required Shafarevich statement](#131-the-required-shafarevich-statement)
    - [Level fields and integral moduli points](#132-level-fields-and-integral-moduli-points)
    - [The missing arithmetic height bound](#133-the-missing-arithmetic-height-bound)
      - [The cone data](#the-cone-data)
      - [The local degeneration chart](#the-local-degeneration-chart)
      - [The metrized theta--Hodge comparison](#the-metrized-theta--hodge-comparison)
      - [The first remaining numerical theorem](#the-first-remaining-numerical-theorem)
    - [Why integrality is not a substitute](#134-why-integrality-is-not-a-substitute)
    - [The descent half after Northcott](#135-the-descent-half-after-northcott)
    - [Zarhin cancellation and Jordan--Zassenhaus](#136-zarhin-cancellation-and-jordan--zassenhaus)
    - [The exact conditional boundary](#137-the-exact-conditional-boundary)
14. [Finite isogeny classes as the exact conditional input](#14-finite-isogeny-classes-as-the-exact-conditional-input)
    - [Good reduction is preserved by isogeny](#141-good-reduction-is-preserved-by-isogeny)
    - [The finite-isogeny-class consequence](#142-the-finite-isogeny-class-consequence)
    - [The precise conditional input](#143-the-precise-conditional-input)
15. [Stable Tate lattices and conditional semisimplicity](#15-stable-tate-lattices-and-conditional-semisimplicity)
    - [Stable lattices are isogeny quotients](#151-stable-lattices-are-isogeny-quotients)
    - [Finite isogeny classes give finite lattice type](#152-finite-isogeny-classes-give-finite-lattice-type)
    - [Tate's lattice lemma](#153-tates-lattice-lemma)
    - [Conditional rational Tate-module semisimplicity](#154-conditional-rational-tate-module-semisimplicity)
16. [Consequences of isogeny-class finiteness](#16-consequences-of-isogeny-class-finiteness)
    - [Curves and Jacobians](#161-curves-and-jacobians)
    - [Coefficient extension, summands, and multiplicity spaces](#162-coefficient-extension-summands-and-multiplicity-spaces)
    - [The Hom--Tate boundary](#163-the-hom--tate-boundary)
    - [The packet-carrier array](#164-the-packet-carrier-array)
17. [The completed theorem and its boundary](#17-the-completed-theorem-and-its-boundary)
    - [The completed and conditional chains](#171-the-completed-and-conditional-chains)
    - [Normalization and hypothesis ledger](#172-normalization-and-hypothesis-ledger)
    - [Conclusion](#173-conclusion)

## 1. Why height completes descent

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

The theorem promised by the title is completed in Chapters 2--10. Chapter 2 constructs
absolute projective height, Chapter 3 proves Northcott finiteness, Chapters 4--7 pass from Weil
heights to the exact Néron--Tate quadratic form, and Chapter 8 combines that form with weak
Mordell--Weil. Chapters 9--10 then record examples and the forms of finite generation that are
reused for Jacobians and their quotients.

Later applications ask for a separate uniform statement about isogeny classes. Because no
earlier source in the present sequence proves that statement, Chapters 11--16 retain the exact
conditional boundary and every reduction already established beyond it. They are not used in
the proof of Mordell--Weil. Potential semistable reduction, ramified Hodge base change,
toroidal compactification, the metrized theta--Hodge comparison, and two arithmetic slope
certificates remain displayed hypotheses. Finite polarized descent, integral factor
cancellation, and the implication from finite isogeny classes to rational semisimplicity are
proved without feeding any of those conclusions back into the elementary height argument.

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

Several quick checks are useful. A root of unity $\zeta$ is an algebraic integer and every conjugate has modulus $1$, so $h(\zeta)=0$. Conversely, if $\alpha\ne0$ has height zero, (2.14) forces its primitive minimal polynomial to be monic and every conjugate to have modulus at most $1$. The constant term shows every conjugate has modulus exactly $1$. Every power $\alpha^n$ has degree at most $r=[\mathbf Q(\alpha):\mathbf Q]$, and its monic minimal polynomial has coefficients bounded by the binomial coefficients $\binom rj$, because all of its conjugates have modulus $1$. Only finitely many such integer polynomials exist, so only finitely many powers $\alpha^n$ exist. Two powers are equal, and $\alpha$ is a root of unity. Thus

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

and letting $r\to\infty$ gives equality. Independence of the auxiliary integer will follow at
the end of Section 6.3, after the parallelogram identity gives quadraticity for every integer.

Additivity in line bundles survives canonically:

$$
\widehat h_{L\otimes M}=\widehat h_L+\widehat h_M \tag{6.5}
$$

for symmetric line bundles $L,M$. Both sides are boundedly close to the appropriate Weil height and obey the same functional equation. Likewise

$$
\widehat h_{f^*L}(P)=\widehat h_L(f(P)) \tag{6.6}
$$

for a homomorphism $f:B\to A$.

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

The bounded comparison now has a useful uniform consequence. Put

$$
B_L=\sup_{P\in A(\overline K)}
|h_L(P)-\widehat h_L(P)|<\infty.
$$

Then for every integer $n$ and every algebraic point $P$,

$$
|h_L([n]P)-n^2\widehat h_L(P)|\leq B_L. \tag{6.8a}
$$

Indeed (6.8) identifies the quadratic term, and the bounded comparison is applied at the
single point $[n]P$. Thus the error in quadratic growth does not increase with $n$. The
ordinary height of the multiples of a nontorsion point is a quadratic main term plus one
uniformly bounded remainder.

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

## 9. Examples and scope

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

## 10. Mordell--Weil under subvarieties and quotients

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

## 11. The boundary of the elementary height method

The Mordell--Weil theorem and its quotient package are now complete. A separate arithmetic
question asks whether only finitely many abelian varieties can occur when dimension and bad
reduction are fixed. It uses the same product formula and Northcott principle, but the point
whose height must be bounded is now a point of an abelian-moduli space. The remaining chapters
record this conditional boundary because later applications need its precise input and because
several reductions after that input are already proved.

This distinction is load-bearing. The Néron--Tate height proves finite generation of
$A(K)$ after $A$ has been chosen. It does not put a bound on the height of $A$ itself.

### 11.1 The distinct downstream question

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

### 11.3 The exact conditional chain

The Faltings--Tate route separates into four implications:

$$
\begin{array}{c}
\text{arithmetic height bound on polarized moduli}
+\text{ polarized descent and integral Zarhin factor cancellation}
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

The last three arrows are algebraic and are proved completely in Chapters 14--16. In the first
arrow, Chapters 12--13 prove polarized descent and the integral factor-cancellation passage
from the stabilized principally polarized objects back to the original abelian varieties. The
remaining input is the deep numerical height bound. Its semistable, compactification, and
metric interfaces and the exact certificates needed by its determinant-slope component are
isolated below. This
distinction prevents a
moduli point that is merely integral outside finitely many primes from being declared to have
bounded height.

## 12. Conditional Faltings height and the moduli comparison

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

### 12.2 Potential semistable reduction from curves

Stable height is useful only if every abelian variety reaches the semistable range. This is
not a formal consequence of the existence of a Néron model: its connected special fiber may
have a unipotent radical. We now analyze a proposed internal proof of the required local
theorem; Section 13.7 records the remaining gap. The argument has three independent pieces.
Prime-to-residue-characteristic torsion detects the three
Chevalley ranks and makes semistability invariant under isogeny; a sufficiently positive curve
in an abelian variety produces a Jacobian carrier; and normalization after a carefully chosen
ramified base change makes a prepared curve model reduced and nodal.

Throughout this section, $R$ is a complete discrete valuation ring of characteristic zero,
with fraction field $F$ and perfect residue field $k$ of characteristic $p>0$. This is the
case needed at every finite place of a number field. Write $I_F$ for inertia and, for an
abelian variety $A/F$, write

$$
a(A),\quad t(A),\quad u(A)
\tag{12.2.1}
$$

for the dimensions of the abelian, toric, and unipotent parts of the geometric connected
special fiber of its Néron model. Thus

$$
\dim A=a(A)+t(A)+u(A),
\tag{12.2.2}
$$

and $A$ is semistable precisely when $u(A)=0$.

**Lemma 12.2 (the fixed part from the Néron fiber).** If $\ell\ne p$, then

$$
\operatorname{rank}_{\mathbf Z_\ell}(T_\ell A)^{I_F}
=2a(A)+t(A).                                      \tag{12.2.3}
$$

Consequently semistable reduction is invariant under $F$-isogeny.

**Proof.** Pass to the strict henselization and then complete; neither inertia invariants nor
the geometric special fiber changes. For every $n$, reduction is injective on unramified
$\ell^n$-torsion. Indeed, a torsion section reducing to the identity lies in the formal
group, and $[\ell^n]$ is an automorphism there because its differential is a unit.

Reduction is also surjective onto the $\ell^n$-torsion of the special fiber. Lift a special
point $x$ to a section $\widetilde x$ by smoothness. The section $[\ell^n]\widetilde x$
lies in the formal group. Divide it there uniquely by $\ell^n$ and subtract the quotient
from $\widetilde x$. The result is an $\ell^n$-torsion lift of $x$. Passing to compatible
inverse systems gives the asserted comparison: at each level the set of lifts is a torsor
under the formal $\ell^n$-torsion, which is zero, and the transition maps are therefore
compatible. Hence

$$
(T_\ell A)^{I_F}\simeq T_\ell(\mathcal A_{\bar k}).
\tag{12.2.4}
$$

The finite component group contributes no Tate module. Its prime-to-$\ell$ part has no
$\ell^n$-torsion, while on its finite $\ell$-primary part repeated multiplication by $\ell$
is zero, so a compatible inverse-limit sequence is zero. We may therefore replace
$\mathcal A_{\bar k}$ by its identity component. In its
Chevalley filtration a smooth connected unipotent group has no prime-to-$p$ torsion, a torus
of rank $t$ has Tate module of rank $t$, and an abelian variety of dimension $a$ has Tate
module of rank $2a$. Exactness of prime-to-$p$ torsion in the two smooth extensions proves
(12.2.3).

Now let $f:A\to A'$ be an isogeny and choose a quasi-inverse $h$ with
$hf=[m]_A$ and $fh=[m]_{A'}$. The maps of connected Néron fibers carry affine parts to
affine parts and induce quasi-inverse isogenies between their abelian quotients. Hence
$a(A)=a(A')$. The rational Tate modules are isomorphic, so (12.2.3) gives
$t(A)=t(A')$. Equality of dimensions and (12.2.2) then gives $u(A)=u(A')$, proving the last
assertion even when the isogeny degree is divisible by $p$. $\square$

The use of the rational Tate module in the last paragraph is harmless: an isogeny already
gives its inverse after dividing by $m$. No semisimplicity or Tate homomorphism theorem is
being used.

**Lemma 12.3 (a Jacobian carrier).** After a finite separable extension of $F$, every
positive-dimensional abelian variety $A/F$ is isogenous to an abelian subvariety of the
Jacobian of a smooth proper geometrically connected curve.

**Proof.** For $\dim A=1$, take the curve $A$ itself. Suppose $g=\dim A\ge2$. Choose a
symmetric very ample line bundle and replace it by a high power. Choose points
$P_1,\ldots,P_g$ and tangent vectors $v_i\in T_{P_i}A$ whose translates to the identity form
a basis of $\operatorname{Lie}A$. A high power separates these first-order jets. Bertini,
with those finitely many conditions and after a finite separable extension if rational choices
are needed, gives a smooth geometrically connected complete-intersection curve

$$
C=H_1\cap\cdots\cap H_{g-1}\subset A
\tag{12.2.5}
$$

through the origin and the $P_i$, tangent to $v_i$ at $P_i$.

For clarity, the Bertini assertion here is the elementary jet-incidence form. At each $P_i$
choose $g-1$ independent conormals with common kernel $Fv_i$. Surjectivity of the evaluation
map to the finitely many first-jet spaces makes the tuples of sections with those prescribed
values and differentials a nonempty affine space. For a point away from the $P_i$, failure of
transversality imposes at least one more independent linear condition; the incidence of bad
tuples with such a point therefore has smaller dimension than the parameter space. The same
calculation on each successive intersection gives a nonempty open of smooth tuples. The
generic member of a base-point-free linear system on a geometrically integral variety is
geometrically integral: on an affine trivializing chart this follows because the universal
linear polynomial is prime in the function field with independent coefficient variables; the
property spreads to an open of the parameter space. The finitely many imposed first jets do
not change that argument away from their base points. Applying it successively makes the
complete intersection geometrically connected. The ground field is infinite, so the
nonempty parameter open has a closed point with finite separable residue field. Passing to
that field supplies the asserted tuple.

If an invariant differential restricts to zero on $C$, it vanishes on every $v_i$; translating
to the identity shows that it is zero. Thus restriction of invariant differentials

$$
H^0(A,\Omega^1_A)\longrightarrow H^0(C,\Omega^1_C)
\tag{12.2.6}
$$

is injective. The based inclusion induces $q:J(C)\to A$. The dual of $dq$ is (12.2.6), so
$dq$ is surjective. The image of a homomorphism of abelian varieties is an abelian
subvariety; its tangent space has dimension $g$, hence $q$ is surjective.

Let $D=(\ker q)^0$. Pull a polarization on $J(C)$ back to $D$ and choose a quasi-inverse to
the resulting isogeny $D\to D^\vee$. As in Poincaré reducibility this produces a retraction
$r:J(C)\to D$ whose restriction to $D$ is $[n]$. If $D'=(\ker r)^0$, then
$D\cap D'$ is finite and addition is an isogeny

$$
D\times D'\longrightarrow J(C).
\tag{12.2.7}
$$

The restriction $D'\to A$ has finite kernel and equal-dimensional source and target, hence is
an isogeny. Thus $A$ is an isogeny factor of $J(C)$. $\square$

We next analyze the curve theorem rather than cite stable reduction. A **prepared model** is a
regular proper flat model whose reduced special fiber is a strict normal-crossings divisor.
Books 11 and 12 construct a regular proper model and resolve a divisor on a regular arithmetic
surface by point blowups. Applied to the reduced special fiber, this gives a prepared model.
The field extension in the next lemma is what removes its multiplicities; ordinary resolution
alone cannot do so.

**Lemma 12.4 (ramified saturation of a curve model; proof incomplete).** Let $X/F$ be a smooth
proper geometrically connected curve. After a finite separable extension $F'/F$, the curve $X_{F'}$
has a regular proper model over $R'$ whose geometric special fiber is a reduced strict
normal-crossings curve. In particular it is semistable.

**Proof attempt.** Start with a prepared model $\mathcal X/R$ and write

$$
\mathcal X_k=\sum_i m_iE_i.
\tag{12.2.8}
$$

Choose a positive integer $e$ divisible by all $m_i$ and a totally ramified separable
extension of ramification index divisible by $e$. Such an extension exists in characteristic
zero by an Eisenstein polynomial; call the first field $F_1$. Normalize over $F_1$ as in the
local calculation below. It has only finitely many component constant fields, intersection
fields, tangent branches, and coefficient algebras. Choose one further finite extension
$F'/F_1$ over which their reduced normalizations are geometrically split. Its residue part is
separable because $k$ is perfect, and every generic coefficient extension is separable because
$F$ has characteristic zero. Put $e'=e(F'/F)$; it is still divisible by every $m_i$. We may
normalize the direct base change to $F'$: normalization in a tower is transitive.

We check the first normalization locally. At a geometric point of the prepared divisor the
completed equation has the form

$$
\pi=u x_1^{m_1}\cdots x_r^{m_r},
\qquad r\in\{1,2\},\quad u\in\widehat{\mathcal O}^{\times}.
\tag{12.2.9}
$$

After replacing the base uniformizer by $\varpi$, with $\pi=u'\varpi^{e'}$, normalize the
resulting monomial algebra. Its exponent monoid is the saturation of

$$
m_1[x_1]+\cdots+m_r[x_r]=e'[\varpi].
\tag{12.2.10}
$$

Here is the elementary normalization check. If a positive multiple of a monomial lies in the
original monoid algebra, that monomial satisfies a monic equation and is integral. Conversely,
the divisorial valuations of the coordinate branches are nonnegative on every integral
monomial, so its exponent lies in the saturated cone. Thus the normalized ring is precisely
the saturated monoid algebra after taking the reduced normalization of its finite coefficient
algebra. The latter is among the finitely many extensions split in the preceding paragraph.

On the ray above $E_i$, the primitive generator has vertical height

$$
\frac{m_i}{\gcd(m_i,e')}=1.                         \tag{12.2.11}
$$

Every normalized vertical component is therefore reduced. When $r=1$ the normalized chart is
regular at the generic point of that component. When $r=2$, the two primitive height-one rays
bound a two-dimensional cone. If their lattice determinant is $d$, the completed chart is

$$
R'[[x,y]]/(xy-v\varpi^d),\qquad v\in R'^\times.
\tag{12.2.12}
$$

Indeed both sides have the same saturated exponent monoid; rescaling $x$ after strict
henselization removes $v$. Subdivide the height-one segment between the two boundary rays at
all of its lattice points. Adjacent rays then have determinant one, so the associated
normalized monomial blowups are regular. All new rays still have vertical height one. Thus
the special fiber stays reduced and its only intersections are transverse double points.

The normalized blowups are projective and glue because they are defined by the monomial ideals
of the boundary. Normalization is finite over the excellent surface, properness is preserved,
and torsion-freeness over the DVR gives flatness. The generic fiber is unchanged. The final
model would be regular with reduced strict normal-crossings special fiber if the unresolved
normalization and closed-point assertions identified in Section 13.7 were supplied.

It is important that the subdivisions in this proof use height-one rays. Blowing up an
arbitrary point of a reduced special fiber can introduce an exceptional component of larger
multiplicity and would undo (12.2.11).

**Lemma 12.5 (semistable curve implies semistable Jacobian).** If $X/F$ has a regular
semistable model, then $J(X)$ has semistable reduction.

**Proof.** Over an algebraic closure of the residue field, normalize the special fiber and
write $\Gamma$ for its dual graph. A degree-zero line bundle consists of line bundles on the
normalized components and one gluing scalar at each node, modulo one rescaling on each
component. Consequently the connected separated relative Picard group fits into

$$
0\longrightarrow T_\Gamma\longrightarrow
\operatorname{Pic}^{0,\mathrm{sep}}_{\mathcal X/R,\bar k}
\longrightarrow\prod_vJ(\widetilde X_v)\longrightarrow0,
\tag{12.2.13}
$$

where $X^*(T_\Gamma)=H_1(\Gamma,\mathbf Z)$. Books 25 and 38 prove that the separated Picard
group is the identity component of the Néron model of $J(X)$. Its connected special fiber is
therefore an extension of an abelian variety by a torus and has no unipotent radical. $\square$

**Theorem 12.6 (potential semistable reduction; conditional here).** Every abelian variety over a completion of
a number field acquires semistable reduction after a finite separable extension.

**Proof.** Conditional on Lemma 12.4, the zero-dimensional case is immediate. Otherwise, after a finite separable
extension, Lemma 12.3 supplies a curve $C$ and an isogeny
factor $D'\to A$ in $J(C)$. After a further finite separable extension, Lemma 12.4 gives a
semistable model of $C$. Lemma 12.5 makes $J(C)$ semistable, products are semistable exactly
when their factors are, and Lemma 12.2 transports semistability first through (12.2.7) and then
through $D'\to A$. $\square$

For later reference, $({\rm PSR})$ denotes the combined local assertion

$$
\boxed{({\rm PSR})\quad
\begin{gathered}
\text{every abelian variety over a completion of a number field becomes semistable}\\
\text{over a finite separable extension, and remains semistable after every further finite extension.}
\end{gathered}}
\tag{12.2.14}
$$

Conditional on Lemma 12.4, Theorem 12.6 gives the existence half, with one geometric field
independent of an auxiliary prime. The persistence half, needed to compare two choices of
semistable field, remains conditional on the proposed integral formal calculation in the next
section.

### 12.3 Ramified semistable Hodge base change

The remaining local issue is not the component group. It is the lattice of invariant
differentials. The useful integral object is the bounded formal identity group inside the
Raynaud covering group. The following attempt isolates the part of that theory needed for
cotangent spaces; its missing formal and rigid steps are listed in Section 13.7.

**Lemma 12.7 (formal semiabelian identity; proof incomplete).** Let $A/F$ be semistable, with
connected Néron model $\mathcal A^0/R$. There are an abelian scheme $\mathcal B/R$, a torus $\mathcal T/R$,
and a semiabelian extension

$$
0\longrightarrow\mathcal T\longrightarrow\mathcal E
\longrightarrow\mathcal B\longrightarrow0                 \tag{12.3.1}
$$

such that the formal completions of $\mathcal E$ and $\mathcal A^0$ at the identity are
canonically isomorphic. Here "at the identity" means the $\pi$-adic formal open generated by
the connected special fiber, with its distinguished identity section; it is not completion
only at the closed identity point. The construction commutes with every finite extension of complete
DVRs. After such an extension, the identity component of the new Néron model has the
base-changed formal completion. In particular semistability persists.

**Proof attempt.** We give the infinitesimal construction, since merely naming a Raynaud extension
would move the gap. Make one finite unramified extension to split the torus in the geometric
connected special fiber; descent at the end is unique. Write $X=X^*(T)$ and $R_n=R/\pi^{n+1}$.
Over $R_0$, the special semiabelian group is classified character by character by a map

$$
c_0:X\longrightarrow B_0^\vee(k).                         \tag{12.3.2}
$$

Pushout by a character is the complement of the zero section in a rigidified algebraically
trivial line bundle on $B_0$.

Assume the torus and quotient have been lifted through $R_n$. Across the square-zero extension
$R_{n+1}\to R_n$, lift a basis of characters on affine formal charts. Their possible failure
to respect addition is a homomorphism from a diagonalizable group to the additive vector group
defined by the square-zero ideal. It is zero: on Hopf algebras a primitive Laurent polynomial
has every coefficient zero. The same calculation proves uniqueness, and affineness of the
torus kills the Čech gluing obstruction. Quotienting by the lifted torus on these charts
gives a smooth proper group $B_{n+1}/R_{n+1}$; properness lifts over a nilpotent thickening and
connectedness follows from the special fiber. Thus $B_{n+1}$ is an abelian scheme.

Characterwise pushout gives rigidified algebraically trivial line bundles on $B_{n+1}$. The
Poincaré biextension identifies them with a unique lift
$c_{n+1}:X\to B_{n+1}^\vee(R_{n+1})$ and reconstructs the extension. Induction and formal
existence algebraize the proper system $B_n$ to $\mathcal B$. Here is the needed
algebraization argument. Restrict a high symmetric power of a polarization of $A$ to the
bounded formal group and take its character-zero descent to $B_n$; the cube rigidification
makes these ample bundles compatible in $n$. After one further fixed power, relative Serre
vanishing makes their section modules finite free and makes reduction

$$
H^0(B_{n+1},L_{n+1}^q)\longrightarrow H^0(B_n,L_n^q)
$$

surjective for the finite set of degrees generating the section algebra. Choose compatible
bases and compatible homogeneous relations in those degrees. Their inverse limits are
elements and equations over the complete ring $R$; relative Proj of the resulting finite
graded algebra is a projective $R$-scheme whose reductions are the $B_n$. Smoothness and the
group law descend from the compatible reductions, so this scheme is $\mathcal B$. Twist each
of the finitely many character line bundles belonging to a basis of $X$ by a sufficiently high
power of $L_n$. The same section-and-relation argument algebraizes those bundles and their
biextension multiplication maps. Taking the relative spectrum of the resulting $X$-graded
invertible algebra algebraizes the extension to (12.3.1). Its formal identity group is
the one with which we started. Uniqueness at every infinitesimal level shows that the
construction descends from the unramified splitting field.

Every step--characters, Poincaré bundles, square-zero lifting, quotient, and inverse
limit--commutes with finite flat base change. Hence $\widehat{\mathcal E}_{R'}$ is the formal
semiabelian identity constructed after extension. Translating the common formal identity
chart on the analytic generic fiber gives a local isomorphism onto $A_{F'}^{\mathrm{an}}$; its
kernel is discrete because distinct translates of a sufficiently small identity chart are
disjoint. Properness of $A_{F'}$ makes the image all of $A_{F'}^{\mathrm{an}}$: the image is
an open subgroup, and its cosets cannot disconnect a geometrically connected proper analytic
space. Its tropical image has full rank. Otherwise an integral functional annihilating its
real span supplies a cocharacter ray escaping every translate of the bounded chart; its image
in the proper analytic quotient would fail the valuative criterion. Choose a rational
parallelotope for the resulting full discrete kernel in the toric
valuation space and subdivide all of its translates into rational simplices. The monoid
algebras of the dual cones, twisted by the character line bundles on $\mathcal B$, glue along
faces; only finitely many cells remain modulo the kernel. The positive quadratic form supplied
by an ample symmetric bundle on $A$ is a strictly convex periodic support function after one
subdivision, so relative Proj is intended to algebraize the quotient to a proper polyhedral
model used in the following valuative argument.

The union $\mathcal G$ of the translated integral identity charts is a smooth separated
model. To check the Néron property, let $X/R'$ be smooth and let $X_{F'}\to A_{F'}$ be a
morphism. The closure of its graph in that proper polyhedral compactification extends the map at
every codimension-one point of the regular scheme $X$. Translate the image of each such point
into the bounded identity chart; the defining toric characters then have nonnegative valuation,
so they are regular in the corresponding local ring. The induced generic map to $B_{F'}$
extends over $X$ because the good-reduction abelian scheme $\mathcal B_{R'}$ is its Néron
model. On an affine torsor chart the remaining character functions extend across codimension
at least two by normality of $X$. They are intended to glue uniquely because $\mathcal G$ is
separated. This would give the unique extension $X\to\mathcal G$ and the Néron mapping
property. Uniqueness of Néron models would then identify its identity component with
$\mathcal A'^0$, whose formal identity would be $\widehat{\mathcal E}_{R'}$. The missing rigid
uniformization, full-lattice, algebraization, and Néron-property steps are recorded in
Section 13.7.

The last paragraph uses translations only to identify the smooth identity model. It does not
assert that the entire Néron model, whose component group can grow under ramification, is a
base change.

**Theorem 12.8 (semistable Hodge base change; conditional here).** Let $R'/R$ be a finite
extension of complete DVRs. If $A/F$ is semistable and $\mathcal A,\mathcal A'$ are the two Néron models, then the
canonical map

$$
h_e^*:e'^*\Omega^1_{\mathcal A'/R'}
\longrightarrow e^*\Omega^1_{\mathcal A/R}\otimes_RR'
\tag{12.3.3}
$$

is an isomorphism.

**Proof.** Conditional on Lemma 12.7, cotangent space at the identity depends only on formal
completion. Lemma 12.7 identifies the two sides with

$$
e^*\Omega^1_{\mathcal E/R}\otimes_RR'
\quad\text{and}\quad
e'^*\Omega^1_{\mathcal E_{R'}/R'},
$$

respectively. Smooth differentials commute with arbitrary base change, so these modules are
canonically equal. The equality agrees on the generic fiber with pullback by the canonical
Néron base-change map; separatedness therefore identifies it with (12.3.3). $\square$

The preceding sketches identify the geometric content of potential semistable reduction and
the ramified nonproper case of semistable Hodge base change. Section 13.7 records why they do
not yet constitute proofs from the results established earlier in this volume.

### 12.4 Base change and stable height

Under an extension $L/K$, the pulled-back Hodge lattice need not equal the Hodge lattice of the
Néron model over $\mathcal O_L$ at places where reduction improves. Their index is the base-change
conductor. Accordingly the naive value $h_F(A/K)$ need not be invariant before semistable
reduction.

The comparison can be stated without any ambiguity about lattices. Let $R'/R$ be a finite
extension of discrete valuation rings, let $\mathcal A$ and $\mathcal A'$ be the Néron models
of $A/K$ and $A_{K'}/K'$, and let

$$
h:\mathcal A\times_RR'\longrightarrow\mathcal A'
$$

be the canonical base-change morphism of Book 38. Pullback at the identity is a map between
free $R'$-modules of the same rank,

$$
h_e^*:e'^*\Omega^1_{\mathcal A'/R'}
\longrightarrow
e^*\Omega^1_{\mathcal A/R}\otimes_RR'. \tag{12.4a}
$$

It is an isomorphism on generic fibers, hence injective, and its finite cokernel measures the
failure of invariant differentials to commute with ramified base change. Taking determinants
gives the exact comparison needed in (12.3). The required integral statement is

$$
\boxed{(\mathrm{SHB})\quad
A/K\text{ semistable }\Longrightarrow h_e^*\text{ in (12.4a) is an isomorphism}
\text{ for every finite }K'/K.} \tag{12.4b}
$$

Two endpoint checks help locate the content of the theorem. If $A$ extends
to an abelian scheme $\mathcal B/R$, then $\mathcal B_{R'}$ is again an abelian scheme. By the
good-reduction theorem for Néron models it is the Néron model of $A_{K'}$. Relative
differentials of a smooth morphism commute with arbitrary base change, so

$$
e'^*\Omega^1_{\mathcal B_{R'}/R'}
\simeq e^*\Omega^1_{\mathcal B/R}\otimes_RR'. \tag{12.4c}
$$

Consequently (12.4b) is proved at every good place, including for ramified $R'/R$. The
unramified case is also formal, without a reduction hypothesis. If $R'/R$ is finite étale,
$\mathcal A_{R'}$ has the Néron mapping property over $R'$. Indeed, a smooth $R'$-scheme is
smooth over $R$; extend its generic-fiber map uniquely to $\mathcal A$ over $R$, and pair
that extension with its structural map to $\operatorname{Spec}R'$ to obtain the unique map to
$\mathcal A_{R'}$. Hence $\mathcal A_{R'}\simeq\mathcal A'$, and (12.4a) is an isomorphism.

The genuinely unresolved case in $(\mathrm{SHB})$ is ramified base change in the semiabelian, nonproper
range. Book 38's component-group calculation cannot supply it: the whole Néron model can
change while its formal cotangent lattice remains unchanged.

If $A$ becomes semistable over $L$, define its stable height by

$$
h_F^{\mathrm{st}}(A)=h_F(A_L/L).
\tag{12.5}
$$

Assume $(\mathrm{PSR})$ in (12.2.14) and $(\mathrm{SHB})$ in (12.4b). Once
semistability holds, (12.4b) identifies the finite-place determinant lattices after every
further finite base
change, while the archimedean terms repeat with total local degree. Formula (2.2) then proves
that (12.5) is independent of a further extension. If $L_1$ and $L_2$ are two semistable
fields, apply the same argument over a common finite extension. This proves independence of
the original choice as well.

There is no hidden globalization step in that argument. Only finitely many places are bad.
Choose a finite Galois local extension giving semistable reduction at each of them. Book 2,
Theorem 14.1 realizes these as selected completions of one number-field extension; after taking
its Galois closure, every completion over each selected place contains an isomorphic copy of
the prescribed local field. Persistence then gives one global semistable field. Thus
$(\mathrm{PSR})$ supplies the local fields, $(\mathrm{SHB})$ supplies equality of the local lattices, and the
local-degree formula supplies invariance of the normalized Arakelov degree.

### 12.5 The isogeny formula

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

### 12.6 Theta coordinates and moduli height

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

**Lemma 12.9 (bounded moduli height gives finiteness).** Fix $K,g,d,N$ and a projective
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

### 12.7 What the comparison actually proves

If both $h_F^{\mathrm{st}}(A)$ and the boundary contribution in (12.12) are bounded in a
family, Lemma 12.9 proves finiteness. Conversely, a bound for the moduli height controls the
Faltings height by the reverse comparison. This is the useful height/moduli-height bridge.

The bridge alone gives no bound. Good reduction outside a fixed set says that the boundary
intersection is supported on that set, but it does not bound the multiplicity at those primes
or the archimedean contribution. The theorem that supplies a uniform global bound is the deep
arithmetic slope estimate in the next chapter. It cannot be replaced by the ordinary height
machine, by (12.9), or by the quasi-projectivity of the moduli scheme.

## 13. The conditional Shafarevich finiteness gate

We now state the precise finiteness theorem from which the Tate argument starts and distinguish
the ingredients proved earlier from the hypotheses that remain open at this point in the sequence.

### 13.1 The required Shafarevich statement

For a number field $K$, a finite set $S$ of finite places, and an integer $g\geq1$, let

$$
\boxed{
(\mathrm{FS})_{K,S,g}:\quad
\#\{A/K:\dim A=g,\ A\text{ has good reduction outside }S\}/\simeq_K<\infty.}
\tag{13.1}
$$

The polarized version fixes a polarization type and asserts finiteness of polarized
isomorphism classes. Once the required moduli-height bound is supplied, the unpolarized
statement follows here by Zarhin's trick, polarized descent, and integral cancellation for the
resulting factors.
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

We first record the desired compactification and metric comparison and the proposed
constructions. Their unresolved geometric, integral, and analytic steps are kept separate from
the numerical deduction later in this section and are summarized in Section 13.7. Work over

$$
R_N=\mathbf Z[1/N,\zeta_N],\qquad N\geq3,                 \tag{13.3a}
$$

so that a symplectic full level structure has a fixed value of its Weil pairing. Every level
field in Section 13.2 contains the required cyclotomic field after one harmless fixed
enlargement.

#### The cone data

A rank-$r$ cusp is represented by a primitive isotropic summand $U$ of the standard symplectic
lattice. Put

$$
S_U=\operatorname{Sym}^2U,
\qquad
C_U=\{q\in\operatorname{Sym}^2(U_{\mathbf R}^{\vee}):q>0\},
\tag{13.3b}
$$

and let $C_U^+$ be the cone obtained by adjoining positive-semidefinite forms with rational
radical. A rational polyhedral cone $\sigma\subset C_U^+$ gives the affine torus embedding

$$
\operatorname{Spec}R_N[\sigma^\vee\cap S_U].              \tag{13.3c}
$$

Faces give open immersions. If the primitive ray generators extend to a basis of $S_U^\vee$,
the chart is regular and its toric boundary is a strict normal-crossings divisor.

We need these cones compatibly for every cusp. There is a collection $\Sigma=(\Sigma_U)_U$
with the following properties: it is invariant under the integral symplectic group, compatible
with inclusions and quotients of isotropic summands, covers every $C_U^+$, has finitely many
orbits, and every cone is smooth. Here is the reduction argument establishing existence.
Take the convex hull in $\operatorname{Sym}^2(U_{\mathbf R}^{\vee})$ of the rank-one forms
$v v^{\mathsf t}$ for primitive $v\in U^\vee$. The cones over its faces cover $C_U$.
Normalize a positive form so that its least nonzero value on $U$ is one. Successively choose a
shortest primitive vector and project to its orthogonal complement. The covolume identity for
that projection and induction give a basis whose lengths are bounded in terms of $r$; this is
the elementary compactness argument written out later in Lemma 13.6. Consequently only
finitely many integral vectors can be minimal and only finitely many face types occur up to
$\operatorname{GL}(U)$. Semidefinite faces are obtained from the same construction on the
quotient by the rational radical. Intersect the decompositions arising from all cusp maps.
This preserves rationality, coverage, and finite orbit type. Finally order the finitely many
orbits of nonsmooth cones. For a nonsmooth simplicial cone, its half-open fundamental
parallelepiped contains a nonzero lattice point; choose one of least positive coefficient sum
and perform the equivariant stellar subdivision through its primitive ray. Every new maximal
cone has strictly smaller lattice index. Induction on the index, followed by barycentric
subdivision to make the face choices compatible, produces a smooth refinement. A stellar
subdivision is the normal fan of the blowup of one monomial ideal and is therefore projective;
the sum, after scaling, of the finitely many associated support functions is an integral
strictly convex support function for the final refinement.

#### The local degeneration chart

The chart attached to $U$ lies over the moduli space of principally polarized abelian schemes
of dimension $g-r$, together with $r$ points on the dual abelian scheme. Let $\mathcal B$ be
the universal lower-dimensional abelian scheme and let $\mathcal B_U$ denote the corresponding
$r$-fold fiber product over that moduli space. The Poincaré biextension associates to every
$m\in S_U$ an invertible sheaf $\mathcal P_m$ on $\mathcal B_U$, and its multiplication law gives

$$
\mathcal P_m\otimes\mathcal P_{m'}\simeq\mathcal P_{m+m'}.
\tag{13.3d}
$$

Thus (13.3c) has the twisted relative form

$$
\mathcal X_\sigma=
\operatorname{Spec}_{\mathcal B_U}
\left(\bigoplus_{m\in\sigma^\vee\cap S_U}\mathcal P_m\right).
\tag{13.3e}
$$

On its open torus, the same biextension data define an extension of $\mathcal B$ by the torus
with character group $U$. To extend the universal abelian variety, choose the periodic
polyhedral decomposition of $U_{\mathbf R}$ dual to $\sigma$. For each cell, take the graded
algebra generated by the corresponding Poincaré line bundles. Face localizations glue these
relative toric charts. Translation by $U$ changes the grading by (13.3d), so the biextension
cocycle identifies translated charts and satisfies the cocycle condition on triple overlaps.
The quotient has a smooth open group whose special fibers are extensions

$$
0\longrightarrow T_U\longrightarrow G_U\longrightarrow\mathcal B\longrightarrow0.
\tag{13.3f}
$$

A strictly convex integral support function on a sufficiently fine subdivision is intended to
give a relatively ample bundle on this quotient and allow Relative Proj to algebraize the
formal quotient. Equations (13.3e)--(13.3f) are the proposed local inputs to the required
Mumford construction; they are not by themselves its global construction.

If $\tau$ is a face of $\sigma$, localization of the monoid algebra identifies the $\tau$-chart
with the required open of the $\sigma$-chart. A change of cusp acts on $S_U$, the Poincaré
bundles, and the periodic cells, so these identifications are equivariant. Fine level makes
the action free on the generic moduli problem. Local finiteness of the fan says that a
quasi-compact open in one chart meets only finitely many translates of another. Hence the
change-of-cusp equivalence relation is represented locally by a finite disjoint union of open
immersions. Its quotient is obtained by ordinary Zariski gluing after choosing orbit
representatives; on a triple overlap the equality is precisely the Poincaré biextension
cocycle (13.3d). Galois acts on the finite level framing and on the chart algebra, and the
same cocycle is intended to give effective affine descent over $R_N$. Representability and
global compatibility of this quotient are among the steps retained in Section 13.7.

**Theorem 13.2 (arithmetic toroidal Siegel compactification; proof incomplete).** For the
smooth admissible fan $\Sigma$ there is a proper normal scheme

$$
\overline{\mathcal M}^{\,\Sigma}_{g,1,N}/R_N             \tag{13.3g}
$$

containing $\mathcal M_{g,1,N}$ as a dense open, with the following properties.

1. Its boundary $D_\Sigma$ is a relative Cartier divisor and, on the smooth charts above, a
   strict normal-crossings divisor.
2. The universal abelian scheme extends over the formal completion along every stratum to the
   semiabelian group (13.3f).
3. The Hodge line has the canonical extension
   $$
   \lambda_\Sigma=\det e^*\Omega^1_{G_U/\overline{\mathcal M}^{\Sigma}}.
   \tag{13.3h}
   $$
4. A fixed sufficiently divisible power of the symmetric theta bundle, with its cubical and
   level linearizations, extends to the Mumford family and its determinant of sections extends
   to an invertible theta-coordinate line $\Theta_\Sigma$.
5. Refining $\Sigma$ pulls back these lines and the semiabelian family. All constructions
   commute with scalar extension from $R_N$.

**Proof attempt.** Construction and regularity are intended to follow from the monoid
calculations (13.3c)--(13.3f).
The valuative criterion is intended to prove properness. Indeed, after finite extension a principally
polarized abelian variety over a fraction field is semistable by $(\mathrm{PSR})$. Its toric
period pairing is positive semidefinite with rational radical: evaluating a character on a
period gives the entries, symmetry comes from the polarization biextension, and positivity
from ampleness on the generic fiber. Hence it belongs to some cone of the covering fan and
the monoid inequalities extend the moduli map to that chart.

We must descend from the semistable field. Take it finite Galois. Each conjugate extension
has the conjugate period form and therefore lands in the conjugate cone, which belongs to
$\Sigma$ by equivariance. On the normalization of the pairwise fiber product of valuation
rings, two conjugate extensions agree on the generic fiber. Their period monomials have the
same valuations, so both maps factor through the chart for the common face of their cones and
agree there by separatedness of the torus embedding. These equalities satisfy the cocycle
condition because they do on the generic fiber. Finite faithfully flat descent gives an
extension over the original valuation ring if the asserted global quotient and its descent
data have first been constructed. This would prove existence in the valuative criterion; the
same common-face argument would prove uniqueness.

Quasi-compactness needs the finite-orbit assertion, not merely local charts. Choose one cone
from each orbit and finitely many affine opens on its lower-dimensional abelian base. Their
translates cover every cusp chart, while the interior moduli scheme is already of finite type.
Thus the proposed glued space would be of finite type. The common-face calculation is intended
to prove separatedness, and the conditional valuative argument above would then make the
finite-type separated morphism proper.

Invariant differentials of (13.3f) give (13.3h); exactness of differentials for a torus
extension shows that it is locally free of rank $g$. The required $(\mathrm{SHB})$ comparison
would identify it with the Néron Hodge lattice on every trait. For the theta line, a support function clears the
translation denominators, and the cubical identity makes the translated graded algebras
agree. Relative Proj and determinant of cohomology commute with base change. A complete
Mumford construction and arithmetic quotient/descent argument would then prove independence
under common refinement. The missing steps are recorded in Section 13.7.

The compactification is not unique; its pullback class on a common refinement is. Once a line
bundle, metric, and projective presentation have been fixed, the associated height is defined
up to a bounded function. Heights attached to different ample combinations are only comparable
after passage to a common refinement, not equal up to a bounded function in general.
In Theorem 13.3, $h_{\mathrm{mod}}$ denotes the height of the fixed theta-coordinate
presentation; comparison with another fixed ample moduli height only changes the displayed
multiplicative and additive constants.

#### The metrized theta--Hodge comparison

At an archimedean point choose a period matrix $\tau=X+iY$ in a Siegel reduction domain. If
$dz=dz_1\wedge\cdots\wedge dz_g$, direct integration over the period parallelepiped gives

$$
\|dz\|_{L^2}^2=(2\pi)^{-g}2^g\det Y.                 \tag{13.3i}
$$

Theta sections have the convergent expansion

$$
\theta\!\begin{bmatrix}a\\ b\end{bmatrix}(z,\tau)
=\sum_{n\in\mathbf Z^g}
\exp\!\left(\pi i(n+a)^{\mathsf t}\tau(n+a)
+2\pi i(n+a)^{\mathsf t}(z+b)\right).               \tag{13.3j}
$$

The translation-invariant norm is not the raw absolute value of this function. If
$z=x+iy$, its exponential factor is

$$
\|\theta[a,b](z,\tau)\|_{\mathrm{th}}
=(\det Y)^{1/4}
\exp\!\bigl(-\pi y^{\mathsf t}Y^{-1}y\bigr)
|\theta[a,b](z,\tau)|.                                \tag{13.3j'}
$$

The automorphy factors under $z\mapsto z+m+\tau n$ cancel in (13.3j'), so it descends to the
theta bundle. Reduction theory gives $Y\geq c_g I$ after the standard triangular change of
basis. Completing the square in the real exponent of each summand of (13.3j) bounds (13.3j')
and all derivatives needed for a fixed theta embedding by a convergent Gaussian series whose
constant depends only on $g$ and the fixed level. Toward a rank-$r$ cusp, split $n$ into
degenerating and bounded coordinates.
Collecting equal powers of
$q^m=\exp(2\pi i\operatorname{tr}(m\tau))$ gives the Fourier--Jacobi expansion. Its least
exponent is exactly the value of the support function used in the Mumford extension; after
dividing by that monomial, the remaining Gaussian series is bounded above and, on the chart
where the corresponding theta coordinate is chosen, bounded away from zero. Therefore the
logarithm of the quotient of the theta norm and a fixed power of the $L^2$ Hodge norm has only
the prescribed linear logarithms of boundary parameters, plus logarithmic growth in
$1+\operatorname{tr}Y$.

Algebraically the same calculation compares automorphy factors. For
$\gamma=\left(\begin{smallmatrix}A&B\\C&D\end{smallmatrix}\right)$ the theta transformation
law contains

$$
\kappa(\gamma)\det(C\tau+D)^{1/2}
\exp\!\bigl(\pi i z^{\mathsf t}(C\tau+D)^{-1}Cz\bigr),
$$

where $\kappa(\gamma)$ has finite order. In the determinant of a complete theta frame the
quadratic exponential cancels by symmetry of the characteristics. The Hodge frame transforms
by $\det(C\tau+D)^{-1}$. Clearing the half-power, the finite character, and one fixed common
denominator therefore gives an isomorphism of two tensor powers on the open moduli scheme. Their
ratio is a rational section on the normal compactification and is nowhere zero on the open, so
its divisor is supported on the finitely many boundary components. Its order along $D_\rho$ is the least
Fourier--Jacobi exponent paired with the primitive generator of $\rho$. This gives integers
$a,b>0$ and $c_\rho\in\mathbf Z$, depending only on $g,N$ and the chosen theta presentation,
such that

$$
\Theta_\Sigma^{\,a}
\simeq\lambda_\Sigma^{\,b}\otimes
\mathcal O\!\left(\sum_{\rho\in\Sigma(1)}c_\rho D_\rho\right).
\tag{13.3k}
$$

The required uniform Fourier--Jacobi estimate would say that, if $\varphi$ denotes the
isomorphism (13.3k), then

$$
|\log\|\varphi\||
\leq C_0+C_1\log(1+\operatorname{tr}Y).
\tag{13.3l}
$$

The integral comparison must prove that away from $N$ there is no unrecorded finite-place
error and that the least Fourier--Jacobi monomials are precisely the Cartier equations of the
$D_\rho$ in (13.3e). At the finitely many places
over $N$ the chosen integral theta frame need not extend. For such a place $w$, make the fixed
theta-coordinate tuple primitive and compare its determinant lattice with the Hodge tensor
lattice in the common generic line. If these two rank-one lattices are
$\Lambda_{\mathrm{th}}$ and $\Lambda_{\mathrm H}$, define

$$
\delta_w(x)=\operatorname{length}_{\mathcal O_{L,w}}
\frac{\Lambda_{\mathrm{th}}+\Lambda_{\mathrm H}}
{\Lambda_{\mathrm{th}}\cap\Lambda_{\mathrm H}}.
$$

This definition is independent of common rescaling and, when the two lattices are base changed,
its length scales by the ramification index.

For a semistable moduli point $x$ over a number field $L$, choose at each complex embedding a
period matrix in the fixed Siegel reduction domain. Properness extends $x$ to a section
$\bar x$ over $\mathcal O_L[1/N]$; let

$$
\bar x^*D_\rho=\sum_{w\nmid N}m_{w,\rho}[w],\qquad m_{w,\rho}\geq0,
\tag{13.3m}
$$

and define the total boundary size

$$
\beta_\Sigma(x)=\frac1{[L:\mathbf Q]}
\left(
\sum_{w\nmid N,\rho}m_{w,\rho}\log Nw
+\sum_{w\mid N}\delta_w(x)\log Nw
+\sum_{\sigma:L\hookrightarrow\mathbf C}
\log(1+\operatorname{tr}Y_\sigma)
\right).                                             \tag{13.3n}
$$

Two reduced representatives meeting the same compactified chart differ by one of finitely many
side-pairing transformations; the determinant estimates above show that they change the
archimedean summand by at most a constant. Changing a cusp chart likewise changes
$\beta_\Sigma$ by at most a constant because only finitely many chart orbits occur.

**Theorem 13.3 (metrized Hodge--theta comparison; proof incomplete).** For fixed
$g,N,\Sigma$ and theta presentation there are positive constants $r_1,r_2$ and $C_1,C_2$ such that every semistable
principally polarized point with level satisfies

$$
\begin{aligned}
h_{\mathrm{mod}}(x)&\leq r_1h_F(A)+C_1\beta_\Sigma(x)+C_2,\\
h_F(A)&\leq r_2h_{\mathrm{mod}}(x)+C_1\beta_\Sigma(x)+C_2.
\end{aligned}                                         \tag{13.3o}
$$

The constants are unchanged by finite extension of $L$.

**Proof attempt.** If the integral identity (13.3k) and its stated norm bounds hold, evaluate
it on the section $x$. At finite places its divisor is exactly
(13.3m) away from $N$, while $\delta_w(x)$ bounds the lattice discrepancy at $w\mid N$; at
infinity use (13.3i)--(13.3l). Sum over all places and divide by
$[L:\mathbf Q]$. The product formula cancels changes of trivialization. The resulting
equality, with the logarithmic remainder bounded by (13.3n), gives the first inequality.
Solve the same equality for $h_F$ and bound the absolute values of its finitely many boundary
coefficients by a fixed multiple of $\beta_\Sigma$ to obtain the second. Local degrees
repeat under field extension, $(\mathrm{SHB})$ preserves the Hodge lattice, and normalized
valuations multiply by ramification indices; hence the constants and normalized inequalities
are absolute. The missing integral identity and uniform Fourier--Jacobi estimates are recorded
in Section 13.7.

Theorems 13.2 and 13.3 state the compactification and metric interfaces denoted
$(\mathrm{SC})$ and $(\mathrm{MC})$; Section 13.7 records the missing construction and
integral-comparison steps. Even after those interfaces are supplied, they do not bound either
term on the right of the first inequality in (13.3o).

#### The first remaining numerical theorem

Return now to dimension-$g$ varieties $A/K$ and their dimension-$8g$ Zarhin stabilizations.
Fix the preceding data with $\Sigma=\Sigma_{8g}$ on $\mathcal M_{8g,1,N}$. Let $\mathscr L$
be the finite list of level fields supplied by Lemma 13.1, and enlarge the bad
set in each of them by the places over $N$. To evaluate the quantities below, pass from a
field of definition $L_0\in\mathscr L$ to any finite field $L/L_0$ over which the variety is
semistable. Assuming $(\mathrm{PSR})$, $(\mathrm{SHB})$, $(\mathrm{SC})$, and $(\mathrm{MC})$,
their persistence, construction, and base-change clauses, together with the ramification
scaling in (13.3m)--(13.3n), make the normalized Hodge and boundary values independent of this
auxiliary $L$ when the cusp charts and period representatives are pulled back compatibly.
Other allowed reduced representatives change the boundary value by the uniform bounded term
already noted after (13.3n). Northcott will still be applied to the point defined over $L_0$.
The desired numerical conclusion is

**Statement $(\mathrm{SB})$ (arithmetic determinant slope).** There is a
constant $C(K,S,g,N)$ such that, for every dimension-$g$ abelian variety $A/K$ with good
reduction outside $S$, one can choose the Zarhin principal polarization and full level basis of
Section 13.2 so that

$$
\boxed{
(\mathrm{SB})_{K,S,g,N}:\quad
\max\{h_F^{\mathrm{st}}(Z(A)),0\}+\beta_\Sigma
\bigl(x(Z(A),\lambda_Z,\alpha_N)\bigr)
\leq C(K,S,g,N)
}                                                       \tag{13.3p}
$$

Subject to the persistence and base-change hypotheses just stated, the normalizations in
(12.4) and (13.3n) make the assertion independent of the auxiliary semistable extension of
$L_0\in\mathscr L$. We next prove the arithmetic linear-algebra
implication which produces this statement from a finite Hilbert determinant certificate. This
replaces the opaque instruction ``apply a slope lemma'' by the exact finite, level-prime, and
archimedean assertions which still have to be checked on the Mumford family.

Equip a fixed cubical theta power $\mathcal L$ on that family with its translation-invariant
metric and, in the range where higher cohomology vanishes, put

$$
E_m=\pi_*\mathcal L^m,
\qquad \operatorname{rank}E_m=\chi(\mathcal L)m^{8g}.   \tag{13.3q}
$$

For a principal theta line $\chi(\mathcal L)=1$; for the fixed sufficiently divisible theta
power used above, this constant must be retained. Formula (13.3q) is used only for sufficiently
large $m$. Book 35 supplies polarization Riemann--Roch and the rank in (13.3q), Book 8
supplies uniform regularity for a fixed Hilbert locus, and Book 15 then makes the pushforward
locally free and compatible with base change on the abelian locus. None of these books asserts
local freeness on the proposed Mumford boundary. That extension is part of the certificate
below and therefore still depends on $(\mathrm{SC})$.

We first give the arithmetic calculation independently of moduli. A **Hermitian
$\mathcal O_L$-lattice** $\overline E$ is a finite projective $\mathcal O_L$-module $E$ with
a Hermitian norm on $E\otimes_\sigma\mathbf C$ for every embedding
$\sigma:L\hookrightarrow\mathbf C$, compatible with conjugation. If $E$ has rank $r$, choose
$0\ne s\in\det E$ for which $\mathcal O_Ls\subseteq\det E$ has finite quotient and define

$$
\widehat{\deg}\,\overline E
=\log\#(\det E/\mathcal O_Ls)
-\sum_\sigma\log\|s\|_{\det,\sigma}.                 \tag{13.3q1}
$$

The product formula makes this independent of $s$. For a nonzero saturated submodule
$F\subseteq E$, use the restricted norms and put

$$
\widehat\mu_{\max}(\overline E)
=\sup_F\frac{\widehat{\deg}\,\overline F}{\operatorname{rank}F}.
                                                               \tag{13.3q2}
$$

The value is finite by the ordinary Minkowski lattice bound after embedding $E$ in its fixed
archimedean space. No Harder--Narasimhan filtration is needed below; only the defining
inequality for each saturated $F$ is used.

**Lemma 13.3A (determinant and saturation).** Let
$u:\overline F\to\overline E$ be a map of Hermitian $\mathcal O_L$-lattices which has generic
rank $k=\operatorname{rank}F$. Let $I=E\cap u(F_L)$ be the saturation of $u(F)$ in $E$ and put
$Q=I/u(F)$. Then

$$
\widehat{\deg}\,\overline F+\log\#Q
=\widehat{\deg}\,\overline I
+\sum_\sigma\log
\|\det(u_\sigma):\det F_\sigma\to\det I_\sigma\|,
                                                               \tag{13.3q3}
$$

and consequently

$$
\widehat{\deg}\,\overline F+\log\#Q
\leq k\widehat\mu_{\max}(\overline E)
+\sum_\sigma\log\|\mathop{\bigwedge}\nolimits^ku_\sigma\|.
                                                               \tag{13.3q4}
$$

**Proof.** Over each $\mathcal O_{L,w}$, elementary divisors give

$$
\operatorname{length}_w(\det I/\det u(F))
=\operatorname{length}_w(I/u(F)).
$$

Multiplying the residue-field cardinalities shows that the inclusion $u(F)\subseteq I$
changes the determinant lattice by the finite index $\#Q$. At an archimedean embedding,
transporting the metric from $F$ to $u(F)$ changes the determinant norm by the displayed
determinant of $u_\sigma$. Substitution in (13.3q1) proves (13.3q3), including its signs.
Saturation makes $I$ an admissible submodule in (13.3q2), and the determinant norm is at most
the exterior-power operator norm. This proves (13.3q4). $\square$

This formula is where finite lattice defects belong. They occur on the left with a positive
sign; discarding them weakens an upper bound. In particular, a denominator at a level prime
cannot be hidden in an archimedean $O(1)$.

There is a useful finite criterion for the upper slope in (13.3q4). A **Pl\"ucker frame** for a
rank-$r$ Hermitian lattice $T$ consists, for each $1\leq k\leq r$, of finitely many integral
maps

$$
q_{k,\nu}:\mathop{\bigwedge}\nolimits^kT\longrightarrow M_{k,\nu} \tag{13.3q5}
$$

to Hermitian lines such that the corresponding linear Pl\"ucker sections have empty common
zero scheme on $\operatorname{Gr}(k,T_L)$. In particular, every $k$-dimensional $L$-subspace
of $T_L$ has nonzero image under at least one $q_{k,\nu}$. This is not merely a statement
about a preferred basis.

**Lemma 13.3B (finite upper-slope criterion).** Suppose a Pl\"ucker frame satisfies

$$
\widehat{\deg}\,\overline M_{k,\nu}
+\sum_\sigma\log\|q_{k,\nu,\sigma}\|
\leq kU[L:\mathbf Q]                                      \tag{13.3q6}
$$

for every $k,\nu$. Then

$$
\widehat\mu_{\max}(\overline T)\leq U[L:\mathbf Q].       \tag{13.3q7}
$$

**Proof.** Let $F\subseteq T$ be saturated of rank $k$. Choose $q_{k,\nu}$ nonzero on
$\det F$. Apply (13.3q3) to the resulting map from the line $\det F$ to $M_{k,\nu}$; because
the map is generically nonzero, its saturation is the whole target line. Its finite
saturation index is nonnegative, and its archimedean determinant norm is at most the operator
norm in (13.3q6). Hence
$\widehat{\deg}\,\overline F\leq kU[L:\mathbf Q]$. Taking the supremum proves (13.3q7).
$\square$

Here $\overline\lambda_x$ denotes the metrized Néron Hodge lattice: away from $N$ it is the
pullback of (13.3h), at the places over $N$ it is the lattice of (12.1), and at infinity it
carries the metric (12.2). We now put all three kinds of degeneration into one line. For a
semistable point $x$ over $L$, set

$$
\begin{aligned}
\mathfrak a_\partial(x)
 &=\prod_{w\nmid N}\mathfrak p_w^{\sum_\rho m_{w,\rho}},\\
\mathfrak a_N(x)
 &=\prod_{w\mid N}\mathfrak p_w^{\delta_w(x)},
\end{aligned}                                             \tag{13.3q8}
$$

and let $\overline{\mathscr D}_x$ have underlying fractional ideal
$(\mathfrak a_\partial(x)\mathfrak a_N(x))^{-1}$ and metric

$$
\|1\|_{\mathscr D,\sigma}
=(1+\operatorname{tr}Y_\sigma)^{-1}.                     \tag{13.3q9}
$$

The definition of $\delta_w$ in (13.3n) is a length, so the exponents in (13.3q8) are
integers. Directly from (13.3q1),

$$
\widehat{\deg}\,\overline{\mathscr D}_x
=\sum_{w\nmid N,\rho}m_{w,\rho}\log Nw
+\sum_{w\mid N}\delta_w(x)\log Nw
+\sum_\sigma\log(1+\operatorname{tr}Y_\sigma).          \tag{13.3q10}
$$

This identity fixes every sign. Under a finite extension $L'/L$, boundary orders and
level-lattice lengths multiply by $e(w'/w)$, while

$$
\sum_{w'\mid w}e(w'/w)\log Nw'
=\sum_{w'\mid w}e(w'/w)f(w'/w)\log Nw
=[L':L]\log Nw.
$$

With the period representatives pulled back compatibly, archimedean embeddings repeat
$[L':L]$ times. Hence both sides of (13.3q10) multiply by the field degree.

Here is the exact remaining application-specific input. It is deliberately split into an
arithmetic Hilbert determinant assertion and an upper-slope assertion.

**Required logarithmic Hilbert certificate $(\mathrm{AHS}_{\log})$.** There are fixed
integers $a,b_0,b_1>0$ and a fixed finite list of sufficiently large degrees $m$. Fixed
tensor, exterior-power, kernel, saturated-image, and determinant constructions applied to the
multiplication maps among the $E_m$ on the proposed compactification over $R_N$ produce
generic tensor maps of fixed ranks. For every relevant semistable $x/L$, pull them back over
$\mathcal O_L[1/N]$; at $w\mid N$, equip them with the explicitly cleared lattices required
below. The result must be Hermitian lattices $T_{0,x},T_{1,x}$ and nonzero integral maps

$$
\begin{aligned}
\Phi_{0,x}:&\ \overline{\mathscr D}_x^{\,b_0}
                 \longrightarrow\overline T_{0,x},\\
\Phi_{1,x}:&\ \overline\lambda_x^{\,a}
                 \otimes\overline{\mathscr D}_x^{\,b_1}
                 \longrightarrow\overline T_{1,x}.       \tag{13.3q11}
\end{aligned}
$$

The word **fixed** permits one list on each of the finitely many cusp-cone orbits of $\Sigma$
and then takes their finite union. The constructions, including their subspace and quotient
metrics and their rules at the level primes, are fixed before $x$ is chosen and commute with
finite base change. After the boundary monomials and level lattices already inserted in
$\overline{\mathscr D}_x$ are removed, there are constants $V_j\geq0$, independent of $x$,
$L$, and the auxiliary semistable extension, such that

$$
\sum_\sigma\log\|\Phi_{j,x,\sigma}\|
\leq V_j[L:\mathbf Q].                                   \tag{13.3q12}
$$

This is required for $j=0,1$.

The word **integral** in (13.3q11) has exact local content. At $w\nmid N$, the lowest
Fourier--Jacobi monomial must be the Cartier boundary monomial with the stated order and no
additional vertical divisor. At $w\mid N$, after the fixed clearing used to define the target
lattice, the resulting determinant vector must be divisible by
$\mathfrak p_w^{b_j\delta_w(x)}$ relative to that lattice. Indeed, the local source contributed
by $\overline{\mathscr D}_x^{\,b_j}$ is
$\mathfrak p_w^{-b_j\delta_w(x)}$; a mere upper bound on a denominator has the opposite sign
and does not by itself give the integral map in (13.3q11). At infinity, (13.3q12) must hold
after the cusp metric in (13.3q9) is inserted. Finally, the determinant character calculation
must give the two positive channels in (13.3q11), including $a>0$; generic nonvanishing alone
does not determine any of these signs or orders.

Equivalently, the required determinant-of-cohomology or arithmetic Hilbert--Samuel
calculation must produce determinant lines whose finite Cartier and archimedean degree
contributions are exactly $b_0\widehat{\deg}\,\overline{\mathscr D}_x$ and
$a\widehat{\deg}\,\overline\lambda_x+b_1\widehat{\deg}\,\overline{\mathscr D}_x$, with no
unlisted vertical or metric correction.
Formula (13.3q) computes only ranks; it does not establish this intersection identity or the
metric estimate (13.3q12).

**Required theta upper-slope certificate $(\mathrm{US}_\theta)$.** Each $T_{j,x}$ has a
Pl\"ucker frame, obtained by pullback from a fixed finite list of the same universal
multiplication minors and equipped with their induced metrics, for which

$$
\widehat{\deg}\,\overline M_{j,k,\nu}
+\sum_\sigma\log\|q_{j,k,\nu,\sigma}\|
\leq kU_j[L:\mathbf Q]                                   \tag{13.3q13}
$$

for every $j,k,\nu$, with $U_j\geq0$ independent of $x$, $L$, and the auxiliary semistable
extension. After specializing the universal expressions to each $x$, the no-common-zero
condition is required on $\operatorname{Gr}(k,T_{j,x,L})$; nonvanishing only at the generic
moduli point does not bound the slope at every $x$. No separate no-common-zero assertion on
each residue fiber is used in Lemma 13.3B: integrality of the maps and the favorable saturation
term account for finite-place defects.

These two certificates are finite. Book 8 explains the boundedness mechanism: on a fixed
Hilbert locus one regularity bound controls generation and relations in finitely many degrees.
Exterior powers of the resulting finite multiplication matrices therefore give a finite
candidate list for (13.3q11)--(13.3q13). Book 8 proves this algebraic boundedness; it does not
select universal minors having the required determinant characters and no-common-zero
property, or prove their primitivity over $\mathcal O_L$, their Fourier--Jacobi boundary
orders, their required level-prime divisibility, or their Hermitian norm bounds. In particular,
the certificates require fixed universal expressions and cannot be manufactured pointwise
after the degree in (13.3r) is known.

**Proposition 13.3C (logarithmic Hilbert--slope inequality).** Assuming
$(\mathrm{AHS}_{\log})+(\mathrm{US}_\theta)$, one has

$$
\max\{\widehat{\deg}\,\overline\lambda_x,0\}
+\sum_{w\nmid N,\rho}m_{w,\rho}\log Nw
+\sum_{w\mid N}\delta_w(x)\log Nw
+\sum_\sigma\log(1+\operatorname{tr}Y_\sigma)
\leq C(K,S,g,N)[L:\mathbf Q].                           \tag{13.3r}
$$

**Proof.** Put $d=\widehat{\deg}\,\overline\lambda_x$ and
$B=\widehat{\deg}\,\overline{\mathscr D}_x\geq0$. Lemma 13.3B and (13.3q13) give

$$
\widehat\mu_{\max}(\overline T_{j,x})\leq U_j[L:\mathbf Q].
$$

Formula (13.3q1) is additive on tensor products of Hermitian lines, so the two source degrees
in (13.3q11) are $b_0B$ and $ad+b_1B$, respectively. Apply Lemma 13.3A to the two maps in
(13.3q11), and discard their nonnegative finite
saturation lengths. Using (13.3q12) gives

$$
b_0B\leq(U_0+V_0)[L:\mathbf Q],\qquad
ad+b_1B\leq(U_1+V_1)[L:\mathbf Q].                       \tag{13.3q14}
$$

These are the arithmetic Hilbert--Samuel/upper-slope inequalities: their finite correction is
the saturation length in Lemma 13.3A, while all boundary, level-prime, and cusp contributions
are the single degree $B$ in (13.3q10).

If $d<0$, the first inequality bounds
$\max\{d,0\}+B=B$. If $d\geq0$, the second bounds $d+B$, since

$$
\min(a,b_1)(d+B)\leq ad+b_1B.
$$

Together with (13.3q10), this is (13.3r), with for example

$$
C=\max\left\{
\frac{U_0+V_0}{b_0},
\frac{U_1+V_1}{\min(a,b_1)}
\right\}.
$$

All discarded finite terms have the favorable sign, so the argument remains valid when a
determinant map is not saturated. $\square$

For the semistable model over $L$, (12.4) identifies
$d/[L:\mathbf Q]$ with $h_F(Z(A)_L/L)$, and (13.3q10) identifies
$B/[L:\mathbf Q]$ with $\beta_\Sigma(x)$. Proposition 13.3C itself uses only the two
certificates once these Hermitian lattices and the defect line have been fixed. Subject also to
$(\mathrm{PSR})+(\mathrm{SHB})+(\mathrm{SC})+(\mathrm{MC})$, the first value is the stable
height, the second is the compactified boundary value, and both are independent of the
auxiliary semistable field. Dividing (13.3r) then proves (13.3p), while the comparison
inequality in $(\mathrm{MC})$ converts the bounded values into a bound for
$h_{\mathrm{mod}}$. Thus the arithmetic content of $(\mathrm{SB})$ is no longer used as an
unexplained broad premise: once the semistable Hodge lattice and compactified boundary objects
are available, it follows from the two exact certificates above. Those certificates are not
proved here. In particular, $(\mathrm{SC})$ only supplies the proposed
extensions and $(\mathrm{MC})$ only compares their metrized lines; neither proves the positive
determinant characters, the absence of extra vertical divisors, the required level-prime
divisibility, or the Pl\"ucker inequalities (13.3q13). The Gaussian estimate in Theorem 13.3 controls a norm
after a lowest boundary monomial has been identified; it does not identify that monomial or
prove that the determinant minors have no common zero integrally.

Subject to the four geometric/metric interfaces and the two arithmetic certificates, Theorem
13.3 gives a uniform upper bound for $h_{\mathrm{mod}}$. Consequently

$$
[(\mathrm{PSR})+(\mathrm{SHB})+(\mathrm{SC})+(\mathrm{MC})
+(\mathrm{AHS}_{\log})+(\mathrm{US}_\theta)]
\Longrightarrow
(\mathrm{FH})_{K,S,g}.                                \tag{13.3s}
$$

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

Given (13.4), Lemma 12.9 gives finitely many $L$-isomorphism classes of principally polarized
$Z(A)_L$ with level, as $L$ ranges over the finite list in Section 13.2. This stabilized
polarized finiteness is not yet (13.1). There are two subsequent questions, and they should
not be conflated. First, do finitely many polarized objects over the finitely many level fields
give finitely many polarized objects over $K$? Section 13.5 proves that they do. Second, does
finiteness of the stabilized varieties $Z(A)$ imply finiteness of their direct factors $A$?
Section 13.6 proves that integral cancellation statement by establishing the required lattice
theorem over the order $\operatorname{End}_K(Z(A))$.

Once $(\mathrm{PSR})$, $(\mathrm{SHB})$, $(\mathrm{SC})$, and $(\mathrm{MC})$ are supplied,
Proposition 13.3C makes the deduction of (13.3p) from the application-specific certificates
$(\mathrm{AHS}_{\log})$ and $(\mathrm{US}_\theta)$ numerical and exact. Those certificates
must still provide the integral boundary and level-prime orders, the determinant characters,
and the cusp-normalized Pl\"ucker estimates. The comparison inequality in $(\mathrm{MC})$
then converts (13.3p) into the moduli-height bound (13.4); no further descent, cancellation,
or Northcott step would remain.

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

### 13.5 The descent half after Northcott

Northcott produces objects over the level fields. Returning the stabilized polarized objects
to $K$ is not the difficult cancellation step. We prove that descent finiteness now.

**Lemma 13.4 (finite polarized automorphism group).** If $(B,\lambda)$ is a polarized abelian
variety over a number field $L$, then

$$
\operatorname{Aut}_L(B,\lambda)
=\{u\in\operatorname{Aut}_L(B):u^\vee\lambda u=\lambda\}
\tag{13.8}
$$

is finite.

**Proof.** It is enough to prove finiteness after an algebraic closure. Choose an ample line
bundle inducing $\lambda$. Twisting it by a suitable element of $\operatorname{Pic}^0(B)$
makes it symmetric: the required element exists because multiplication by two on the dual
abelian variety is surjective. Rigidify the result at the identity and call it $L_0$. Any
other symmetric rigidified line bundle inducing the same polarization differs from $L_0$ by a
symmetric element of
$\operatorname{Pic}^0(B)$. In $\operatorname{Pic}^0(B)$, pullback by $[-1]$ is inversion, so
such a difference is two-torsion. The possible differences therefore form the finite group
$B^\vee[2]$. The group in (13.8) permutes this finite set of inducing bundles, and it is enough
to show that the stabilizer of $L_0$ is finite.

Choose $n$ so that $L_0^n$ is very ample. A group automorphism preserving $L_0$ acts
faithfully through a projective transformation of the resulting embedded copy of $B$: if the
projective transformation is the identity on the complete linear system, it is the identity
on $B$. These transformations form a closed finite-type subgroup $H$ of the projective
linear group, cut out by preserving the homogeneous ideal of the embedded $B$ and fixing its
identity point.
An infinitesimal element of $H$ gives a global vector field on $B$ vanishing at the identity.
Translation trivializes the tangent bundle of an abelian variety, so every global vector
field is translation invariant and is determined by its value at the identity. The vector
field is therefore zero. Thus $H$ has zero-dimensional tangent space at the identity. In
characteristic zero a finite-type group scheme with this property is zero-dimensional, and a
zero-dimensional closed subgroup of a projective linear group is finite. Hence the stabilizer
of $L_0$, and then the full group (13.8), is finite. $\square$

**Proposition 13.5 (finite polarized descent).** Let $M/K$ be a finite extension and let
$\mathscr P$ be a finite set of polarized abelian varieties over $M$. Up to polarized
$K$-isomorphism, only finitely many polarized abelian varieties $(B,\lambda)/K$ have
$(B,\lambda)_M$ isomorphic to a member of $\mathscr P$.

**Proof.** Replacing $M$ by its Galois closure only enlarges the field over which the
isomorphism is required, so assume that $M/K$ is Galois with group $G$. Fix one member of
$\mathscr P$. If it has no $K$-form there is nothing to count; otherwise choose one form
$(B_0,\lambda_0)/K$. For another form $(B,\lambda)$ and an $M$-isomorphism

$$
\psi:(B,\lambda)_M\xrightarrow{\sim}(B_0,\lambda_0)_M,
$$

comparison of $\psi$ with its $G$-conjugates gives a nonabelian cocycle

$$
c_\sigma=\psi\,{}^\sigma\!\psi^{-1}
\in\operatorname{Aut}_M((B_0,\lambda_0)_M),
\qquad
c_{\sigma\tau}=c_\sigma\,{}^\sigma c_\tau. \tag{13.9}
$$

Changing $\psi$ changes the cocycle by a coboundary. Conversely, if two such cocycles are
cohomologous, the corresponding adjusted $M$-isomorphism is $G$-invariant and therefore
descends coefficient by coefficient to a polarized $K$-isomorphism. Thus the set of forms
injects into the nonabelian cohomology set

$$
H^1\bigl(G,\operatorname{Aut}_M((B_0,\lambda_0)_M)\bigr).
$$

The automorphism group is finite by Lemma 13.4, and $G$ is finite, so even the set of all maps
from $G$ to that automorphism group is finite. Hence the cocycle set and its quotient are
finite. Taking the finite union over $\mathscr P$ proves the proposition. $\square$

Apply this to the output of $(\mathrm{FH})$. There are finitely many level fields. Over each
one, Northcott gives finitely many triples $(Z,\lambda_Z,\alpha_N)$, and forgetting level gives
finitely many polarized pairs. Proposition 13.5 therefore proves

$$
(\mathrm{FH})_{K,S,g}\Longrightarrow
\left\{
\begin{array}{c}
\text{only finitely many polarized $K$-isomorphism classes}\\
\text{among the stabilized pairs $(Z(A),\lambda_Z)$}
\end{array}
\right\}. \tag{13.10}
$$

This removes the level and level-field descent issue completely. It does not recover $A$ from
$Z(A)$.

### 13.6 Zarhin cancellation and Jordan--Zassenhaus

For an abelian variety $B/K$, define the exact remaining assertion

$$
(\mathrm{FC})_{B/K}:\quad
\#\{A/K:\text{there is a $C/K$ with }B\simeq_K A\times C\}/\simeq_K<\infty.
\tag{13.11}
$$

If (13.10) gives stabilized varieties $B_1,\ldots,B_r$, then every original $A$ is a direct
factor of one $B_i$, because

$$
Z(A)=A\times\bigl(A^3\times(A^\vee)^4\bigr).
$$

Consequently

$$
(\mathrm{FH})_{K,S,g}
+(\mathrm{FC})_{B_i/K}\text{ for }1\leq i\leq r
\Longrightarrow(\mathrm{FS})_{K,S,g}. \tag{13.12}
$$

Write $(\mathrm{ZC})_K$ for the assertion that $(\mathrm{FC})_{B/K}$ holds for every abelian
variety $B/K$. For the dimension-$g$ Shafarevich problem only the stabilized varieties of
dimension $8g$ are needed. Notice that this is about actual products and actual
$K$-isomorphism classes. Poincaré reducibility supplies complements only up to isogeny and
therefore does not prove (13.11).

There is an exact algebraic reduction of (13.11). Put

$$
\Gamma=\operatorname{End}_K(B),
\qquad E=\Gamma\otimes_{\mathbf Z}\mathbf Q.
\tag{13.13}
$$

Book 36 proves that $\Gamma$ is finite free over $\mathbf Z$ and that $E$ is a
finite-dimensional semisimple $\mathbf Q$-algebra. If $B\simeq A\times C$, then

$$
P_A=\operatorname{Hom}_K(B,A)
$$

is a direct summand of the regular right $\Gamma$-module $\Gamma$; the right action is
precomposition. Moreover $A\mapsto P_A$ is fully faithful on direct factors of $B$. To verify
this rather than cite Morita language, choose inclusion and projection maps
$i_A:A\to B$ and $p_A:B\to A$. If

$$
\varphi:P_A\longrightarrow P_{A'}
$$

is right $\Gamma$-linear, put $f=\varphi(p_A)i_A:A\to A'$. Every $h:B\to A$ satisfies

$$
h=p_A(i_Ah),
$$

and hence

$$
\varphi(h)=\varphi(p_A)(i_Ah)=fh.
$$

Thus $\varphi$ is postcomposition by the unique map $f$. An isomorphism of the modules
$P_A$ and $P_{A'}$ therefore gives a $K$-isomorphism $A\simeq A'$.

After tensoring with $\mathbf Q$, the modules $P_A\otimes\mathbf Q$ are direct summands of the
regular semisimple $E$-module. There are only finitely many possible rational isomorphism
types, because each simple constituent occurs with multiplicity bounded by its multiplicity
in $E$. The exact remaining arithmetic assertion is therefore

$$
\boxed{(\mathrm{DS})_\Gamma:\quad
\text{the regular right $\Gamma$-module has only finitely many
direct-summand isomorphism types}.} \tag{13.14}
$$

This condition is equivalent to $(\mathrm{FC})_{B/K}$. We have proved the implication from
$(\mathrm{DS})_\Gamma$ to $(\mathrm{FC})_{B/K}$. Conversely, a direct summand of the regular
module is $e\Gamma$ for an idempotent $e\in\Gamma$. The abelian subvarieties $e(B)$ and
$(1-e)(B)$ give an actual product decomposition: the maps

$$
B\longrightarrow e(B)\times(1-e)(B),\qquad x\longmapsto(ex,(1-e)x),
$$

and addition are inverse. Under the fully faithful functor above, $e(B)$ corresponds to
$e\Gamma$. Thus finiteness of the factors gives finiteness of all direct summand types.

We now prove a stronger theorem from which (13.14) follows. The only geometric input is the
elementary compactness of normalized Euclidean lattices. We record the precise form needed in
the argument.

**Lemma 13.6 (normalized lattice compactness).** Fix a Euclidean space $V$ of dimension $n$
and a number $\epsilon>0$. Let $\Lambda_j\subset V$ be full lattices of covolume one such
that every nonzero $x\in\Lambda_j$ has $\lVert x\rVert\geq\epsilon$. After passing to a
subsequence, each $\Lambda_j$ has a basis

$$
b_{j,1},\ldots,b_{j,n}
$$

for which every sequence $b_{j,i}$ converges and the limiting vectors form a basis of $V$.

**Proof.** We first prove, by induction on $n$, that such a lattice has a basis all of whose
vectors have norm at most a constant $M(n,\epsilon)$. A volume-pigeonhole argument gives a
dimension-dependent upper bound for the length of a shortest vector when the covolume is one.
Indeed, in fixed orthonormal coordinates the box $[-1,1]^n$ has volume $2^n>1$. Any
measurable set of volume greater than the covolume has two points with the same image modulo
$\Lambda$: cut it by translates of a fundamental parallelepiped and compare total volumes.
Their difference is a nonzero lattice vector in $[-2,2]^n$, of norm at most $2\sqrt n$.
Thus a shortest vector $v$ has

$$
\epsilon\leq a=\lVert v\rVert\leq c_n.
$$

The vector $v$ is primitive, since otherwise dividing it by a nontrivial integer would give a
shorter lattice vector. Let $\pi:V\to v^\perp$ be orthogonal projection. Then $\pi\Lambda$ is
a lattice of covolume $1/a$: extend the primitive vector $v$ to a basis of $\Lambda$ and
compute the volume after orthogonal projection. If $0\ne y\in\pi\Lambda$, choose a lift
$z\in\Lambda$ and
subtract an integral multiple of $v$ so that the component of $z$ along $v$ has absolute
value at most $a/2$. Minimality of $v$ gives $\lVert z\rVert\geq a$, whence

$$
\lVert y\rVert^2\geq a^2-\frac{a^2}{4}=\frac{3a^2}{4}.
$$

After scaling $\pi\Lambda$ by $a^{1/(n-1)}$, it has covolume one and shortest-vector length
at least

$$
\frac{\sqrt3}{2}\epsilon^{\,n/(n-1)}.
$$

The induction hypothesis gives a uniformly bounded basis of the scaled projected lattice.
Undo the scaling and lift each basis vector to $\Lambda$, again choosing its component along
$v$ in the interval $[-a/2,a/2]$. Together with $v$, these lifts form a basis because
$\Lambda\cap\mathbf Rv=\mathbf Zv$. The bounds on $a$ give the required uniform bound on
all its vectors. The case $n=1$ is immediate.

Choose these bounded bases for the $\Lambda_j$ and write their vectors as the columns of
matrices in one fixed orthonormal basis of $V$. A bounded sequence of matrices has a convergent
subsequence. Every determinant has absolute value one, so the limiting determinant also has
absolute value one. Its columns are therefore a basis, which proves the lemma. $\square$

The stronger order-lattice assertion is

$$
\boxed{(\mathrm{JZ})_\Gamma:\quad
\begin{array}{l}
\text{for every fixed finite-dimensional right $E$-module $W$, there are only finitely}\\
\text{many isomorphism classes of right $\Gamma$-lattices $P$ with
$P\otimes\mathbf Q\simeq W$.}
\end{array}} \tag{13.15}
$$

Here a $\Gamma$-lattice in $W$ means a full free $\mathbf Z$-submodule stable under the right
action of $\Gamma$.

**Theorem 13.7 (Jordan--Zassenhaus).** Let $\Gamma$ be an order in a finite-dimensional
semisimple $\mathbf Q$-algebra $E$. Then $(\mathrm{JZ})_\Gamma$ holds.

**Proof.** Choose an $E$-isomorphism from the rationalization of each lattice to $W$; its
image is a $\Gamma$-stable lattice inside the one fixed rational vector space $W$. It is
therefore enough to count embedded lattices up to abstract $\Gamma$-module isomorphism.

We first treat a simple right $E$-module $W$. Fix an inner product on
$W_{\mathbf R}=W\otimes_{\mathbf Q}\mathbf R$, and let $n=\dim_{\mathbf R}W_{\mathbf R}$.
Choose a $\mathbf Z$-basis $\gamma_1,\ldots,\gamma_s$ of $\Gamma$. For every nonzero
$y\in W$ the simplicity of $W$ gives $yE=W$, so $y\Gamma$ is a full lattice in $W$.
The same holds for $x=ty$ with $t>0$. Among the vectors $x\gamma_i$ one can then choose $n$
which are linearly independent. Hadamard's determinant bound, applied to the finitely many
possible choices, gives one constant $C$ such that

$$
\operatorname{covol}(x\Gamma)\leq C\lVert x\rVert^n
\qquad(x=ty, t>0, 0\ne y\in W).
$$

More explicitly, the chosen $n$ vectors generate a sublattice of $x\Gamma$, so the covolume
of $x\Gamma$ is no larger than their parallelepiped volume; each of their norms is at most a
fixed operator-norm constant times $\lVert x\rVert$.

Suppose, toward a contradiction, that $L_j\subset W$ are pairwise nonisomorphic
$\Gamma$-lattices. Multiply $L_j$ by a positive real scalar $t_j$ so that
$\Lambda_j=t_jL_j$ has covolume one. If $x=t_jy$ is a nonzero shortest vector of
$\Lambda_j$, then $x\Gamma\subseteq\Lambda_j$ is a full sublattice. Hence

$$
1\leq[\Lambda_j:x\Gamma]
=\operatorname{covol}(x\Gamma)
\leq C\lVert x\rVert^n.
$$

Thus all nonzero vectors of all $\Lambda_j$ have norm at least $C^{-1/n}$. Lemma 13.6 gives,
after passage to a subsequence, bases $b_{j,1},\ldots,b_{j,n}$ converging to a basis of
$W_{\mathbf R}$. For each $\gamma_i$, the matrix of right multiplication by $\gamma_i$ in
the $j$-th basis has integral entries. These matrices converge, because the basis matrices
and their inverses converge. A convergent sequence of integral matrices is eventually
constant; after one further subsequence, this holds simultaneously for all $\gamma_i$.

Write $b_{j,r}=t_j\ell_{j,r}$. Then $\ell_{j,1},\ldots,\ell_{j,n}$ is a basis of $L_j$, and
the action matrices of every $\gamma_i$ in these bases are the same. Sending
$\ell_{j,r}$ to $\ell_{k,r}$ is therefore an isomorphism of right $\Gamma$-modules. This
contradicts the choice of the $L_j$ and proves (13.15) when $W$ is simple.

We pass to general $W$ by induction on $\dim_{\mathbf Q}W$. The zero and simple cases are
settled. Otherwise choose a nonzero proper $E$-submodule $U\subset W$. For a
$\Gamma$-lattice $L\subset W$, put

$$
N=L\cap U,
\qquad Q=L/N\subset W/U.
$$

Clearing denominators in bases shows that $N$ and $Q$ are full $\Gamma$-lattices in $U$ and
$W/U$. Both rational modules have smaller dimension, so induction leaves only finitely many
possibilities for the isomorphism classes of $N$ and $Q$.

It remains to show that fixed lattices $N$ and $Q$ have only finitely many extension classes.
Choose a surjection $F=\Gamma^m\twoheadrightarrow Q$ and write $R$ for its kernel. The ring
$\Gamma$ and the modules $F,R,N,Q$ are finite free over $\mathbf Z$; in particular, $R$ is
finitely generated. Pulling an extension of $Q$ by $N$ back to the free module $F$ makes it
split. The component in the original middle module of a chosen splitting, restricted to
$R$, lands in $N$ because $R$ maps to zero in $Q$. It identifies the extension class with an
element of

$$
\operatorname{Hom}_\Gamma(R,N)\big/
\operatorname{res}\operatorname{Hom}_\Gamma(F,N).
$$

Conversely, pushing out $R\hookrightarrow F$ along a homomorphism $R\to N$ constructs the
extension, and changing the chosen splitting adds a restricted map from $F$. Thus this quotient
is exactly the set of extension classes, with its usual abelian-group law. It is a finitely
generated abelian group because both Hom groups are.

After tensoring with $\mathbf Q$, the sequence

$$
0\longrightarrow R_{\mathbf Q}\longrightarrow E^m
\longrightarrow Q_{\mathbf Q}\longrightarrow0
$$

splits: $E$ is semisimple. Every $E$-linear map
$R_{\mathbf Q}\to N_{\mathbf Q}$ therefore extends to $E^m$. Clearing denominators shows
that some nonzero integer multiple of every map $R\to N$ is the restriction of a
$\Gamma$-linear map $F\to N$. The displayed quotient is consequently torsion. A finitely
generated torsion abelian group is finite, so there are only finitely many possible middle
modules $L$. This completes the induction and the proof. $\square$

**Corollary 13.8 (integral Zarhin cancellation).** For every abelian variety $B/K$,
$(\mathrm{FC})_{B/K}$ holds. Consequently $(\mathrm{ZC})_K$ holds and

$$
(\mathrm{FH})_{K,S,g}\Longrightarrow(\mathrm{FS})_{K,S,g}.
$$

**Proof.** The regular semisimple $E$-module has only finitely many rational direct-summand
types. Applied to each one, Theorem 13.7 proves $(\mathrm{DS})_\Gamma$. Its equivalence with
$(\mathrm{FC})_{B/K}$ proves the first assertion for every $B/K$. Proposition 13.5 and
Northcott then give the displayed implication through (13.10)--(13.12). $\square$

### 13.7 The exact conditional boundary

Sections 12.2--13.3 identify the desired constructions, but they do not remove the
conditional boundary. Lemma 12.4 checks saturated monomials and generic
component points, but it does not control the full normalization with wild coefficient units or
prove regularity at every resulting closed point. Lemma 12.7 then invokes analytic generic
fibers, a full tropical period lattice, polyhedral algebraization, and the Néron mapping
property without constructing those rigid-analytic interfaces from the earlier books. Thus
the combined potential-semistability-and-persistence interface $(\mathrm{PSR})$ and ramified
semistable Hodge base change $(\mathrm{SHB})$ remain hypotheses here.
Invoking unsupplied Raynaud machinery under different terminology would not prove these steps
from the earlier results.

Likewise, the local monoid chart (13.3e) does not by itself construct the global arithmetic
toroidal quotient, its Mumford family, or its integral Hodge and theta extensions. The complex
theta transformation formula does not by itself prove the integral line-bundle identity
(13.3k), exclude vertical divisors away from $N$, or give the asserted uniform
Fourier--Jacobi lower bounds. The compactification interface $(\mathrm{SC})$ and metrized
comparison $(\mathrm{MC})$ therefore remain inputs as well.

Once $(\mathrm{PSR})$, $(\mathrm{SHB})$, $(\mathrm{SC})$, and $(\mathrm{MC})$ are supplied,
the remaining arithmetic inputs are the two finite certificates
$(\mathrm{AHS}_{\log})$ and $(\mathrm{US}_\theta)$ in Section 13.3. Lemma 13.3A proves the
determinant-and-saturation identity, Lemma 13.3B proves the finite Pl\"ucker upper-slope
criterion, and Proposition 13.3C proves from those certificates the numerical estimate
$(\mathrm{SB})$ in (13.3p), equivalently (13.3r). Thus the abstract slope deduction is no
longer a missing theorem. The unproved application checks are precisely the positive Hodge
and boundary determinant characters, primitivity and absence of extra vertical divisors away
from $N$, the required level-prime divisibility, the cusp-normalized operator norms, and
integral Pl\"ucker maps with generic-fiber no-common-zero at every $x$.

Ordinary Riemann--Roch on a curve, coherent base change, or algebraic Hilbert polynomials do
not supply those certificates: none measures both integral covolumes and archimedean operator
norms. Nor does $S$-integrality bound the integers $m_{w,\rho}$, as Section 13.4 emphasizes.
Book 8 reduces the relevant section algebra to finitely many degrees, but it does not prove
the local primitivity, Fourier--Jacobi, determinant-character, or Hermitian estimates in those
degrees.

Everything after a bound is proved: level-field reduction, moduli Northcott, finite polarized
$K$-descent, the full Jordan--Zassenhaus theorem (13.15), and integral factor cancellation
$(\mathrm{ZC})_K$. Consequently this book does **not** assert $(\mathrm{FH})$, (13.1), or
unconditional Tate-module semisimplicity. The remaining chapters prove every implication
after $(\mathrm{FS})$, and in fact need only $(\mathrm{IF})$.

For reference, the complete conditional chain proved by the reductions in this chapter is

$$
[(\mathrm{PSR})+(\mathrm{SHB})+(\mathrm{SC})+(\mathrm{MC})
+(\mathrm{AHS}_{\log})+(\mathrm{US}_\theta)]
\Longrightarrow(\mathrm{FH})
\Longrightarrow(\mathrm{FS}). \tag{13.16}
$$

The first implication is Proposition 13.3C followed by Theorem 13.3; the second, including
moduli Northcott, is Corollary 13.8. The six displayed inputs are separate gates in the
conditional chain: the two arithmetic certificates are formulated on the objects proposed by
$(\mathrm{SC})$ and use the same fixed Hodge, theta, and cusp metrics that occur in
$(\mathrm{MC})$. Neither geometric/metric interface contains those certificates, and the
certificates do not prove $(\mathrm{PSR})$ or
$(\mathrm{SHB})$. Thus no descent or direct-factor theorem remains hidden after a valid
height theorem.

## 14. Finite isogeny classes as the exact conditional input

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

The Tate argument below uses exactly (14.3). Thus it is enough to supply the six unresolved
inputs isolated in Section 13.7, to prove Faltings--Shafarevich finiteness directly, or to
prove (14.3) for the particular carrier Jacobians. No stronger theorem is silently required.

## 15. Stable Tate lattices and conditional semisimplicity

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

## 16. Consequences of isogeny-class finiteness

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

The full implication chain, with its one unproved initial premise displayed, is

$$
(\mathrm{FH})\Longrightarrow(\mathrm{FS})
\Longrightarrow(\mathrm{IF})
\Longrightarrow(\mathrm{TS})
\Longrightarrow(\mathrm{SS}_{\mathrm{array}}).
\tag{16.8}
$$

Every displayed arrow is proved here. The first is Corollary 13.8; in particular, its descent
and cancellation components are unconditional. What
the available prior books do not establish is the premise $(\mathrm{FH})$, which still requires
the six inputs listed in Section 13.7. Thus (16.7)
remains conditional.
In particular, it would be incorrect to remove the packet-carrier ambient semisimplicity
blocker merely on the strength of the Tate lattice argument.

## 17. The completed theorem and its boundary

The main argument of this volume is the completed passage from projective height to
Mordell--Weil. The retained conditional chain begins only after that theorem and identifies the
extra uniform input needed for later isogeny-class applications. Keeping the chains separate
makes clear that the second neither strengthens nor qualifies the first.

### 17.1 The completed and conditional chains

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
(\mathrm{FH})+\text{proved Northcott, descent, and cancellation}
\Rightarrow(\mathrm{FS})\Rightarrow(\mathrm{IF}),\\
(\mathrm{IF})\Rightarrow\text{finitely many stable Tate-lattice types},\\
\text{Tate's radical-length lemma}\Rightarrow(\mathrm{TS})
\Rightarrow(\mathrm{SS}_{\mathrm{array}}).
\end{array}
\tag{17.2}
$$

Every arrow in the last two lines of (17.2) is proved in Chapters 14--16. In the first line,
potential semistability, Hodge base change, compactification, and metric comparison remain
unproved, as do the concrete logarithmic Hilbert and theta upper-slope certificates. The
Hermitian determinant/saturation and Pl\"ucker-slope deduction from those certificates to
(13.3r) is Proposition 13.3C.

### 17.2 Normalization and hypothesis ledger

The conventions used throughout are:

| Object                         | Normalization or status                                                                                |
| ------------------------------ | ------------------------------------------------------------------------------------------------------ |
| finite absolute value over $p$ | $                                                                                                      |
| complex absolute value         | usual modulus, with local degree $n_v=2$                                                               |
| absolute projective height     | $[K:\mathbf Q]^{-1}\sum_v n_v\log\max_i                                                                |
| canonical height               | $\widehat h_L=\lim q^{-2r}h_L\circ[q^r]$                                                               |
| Faltings metric                | (12.2), fixed up to one dimension-dependent additive constant                                          |
| stable Faltings height         | normalized Arakelov degree, conditional here on $(\mathrm{PSR})+(\mathrm{SHB})$                        |
| finite isogeny input           | $(\mathrm{IF})_{A/K}$ in (14.3)                                                                        |
| proved Tate output             | $(\mathrm{IF})_{A/K}\Rightarrow(\mathrm{TS})_{A,K,\ell}$                                               |
| proved factor theorem          | Jordan--Zassenhaus in Theorem 13.7 and $(\mathrm{ZC})_K$ in Corollary 13.8                             |
| unresolved uniform source      | $(\mathrm{PSR})+(\mathrm{SHB})+(\mathrm{SC})+(\mathrm{MC})+(\mathrm{AHS}_{\log})+(\mathrm{US}_\theta)$ |

Changing $L$ to $L^r$ multiplies the canonical point height by $r$. Extending a field does
not change an absolute projective height. Subject to $(\mathrm{SHB})$, it does not change the
stable Faltings height once semistability has been reached. The projective statement is proved
in Section 2.2.

### 17.3 Conclusion

Absolute projective height, Northcott finiteness, the Weil height machine, and the
Néron--Tate limiting process fit into one terminating descent. Weak Mordell--Weil supplies
finitely many residue classes modulo multiplication; the canonical height contracts division
and makes every terminal ball finite. Consequently every abelian variety over a number field
has a finitely generated group of rational points, as does every abelian quotient of a
Jacobian. The height pairing identifies torsion as the zero locus and turns the free quotient
into an arithmetic lattice.

Beyond that completed theorem, the reusable conditional algebraic half is also complete. A
stable Tate lattice is the Tate lattice of an isogenous quotient. If the isogeny class has finitely many
$K$-isomorphism classes, only finitely many integral lattice types occur. Tate's
Jacobson-radical construction shows that a nonsemisimple rational representation would create
infinitely many types, a contradiction. Curve cohomology, coefficient factors, and multiplicity
spaces then inherit semisimplicity exactly as required by the packet-carrier array.

The remaining gap is not Hom--Tate linear algebra. The first exact arithmetic input is finite
isogeny classes. The standard uniform source is the Faltings--Shafarevich package: the arithmetic
height bound on Siegel moduli. The semistable Hodge theory, compactification, and metrized
Hodge/theta comparison remain unresolved, as do the two concrete arithmetic certificates in
Section 13.3. Proposition 13.3C proves the determinant/saturation and upper-slope implication
from those certificates to the required slope-and-boundary estimate.
Proposition 13.5 proves descent of
the finitely many stabilized polarized objects from the level fields to $K$, while Theorem
13.7 and Corollary 13.8 prove integral Zarhin factor cancellation. The existing height machine
proves what follows from a bound; it does not prove that bound from $S$-integrality. Until the
remaining interfaces are supplied or proved here in full,
Faltings--Shafarevich finiteness remains unproved, while rational Tate-module semisimplicity and
$(\mathrm{SS}_{\mathrm{array}})$ are available only conditionally on the finite-isogeny-class
input, not as unconditional conclusions of this volume.
