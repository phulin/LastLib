# Adeles and Ideles

## Contents

1. [One field, all of its local shadows](#1-one-field-all-of-its-local-shadows)
   - [The local--global problem](#11-the-local--global-problem)
   - [Number fields and their integers](#12-number-fields-and-their-integers)
   - [Archimedean embeddings and the Minkowski space](#13-archimedean-embeddings-and-the-minkowski-space)
   - [Approximation in a Dedekind domain](#14-approximation-in-a-dedekind-domain)
   - [Ideal lattices and discriminants](#15-ideal-lattices-and-discriminants)
2. [Places and normalized local size](#2-places-and-normalized-local-size)
   - [Why places, rather than primes alone](#21-why-places-rather-than-primes-alone)
   - [The global normalization](#22-the-global-normalization)
   - [The rational model for all normalizations](#23-the-rational-model-for-all-normalizations)
   - [Local integers and local units](#24-local-integers-and-local-units)
   - [Extension and local norms](#25-extension-and-local-norms)
   - [Local degrees over a rational place](#26-local-degrees-over-a-rational-place)
3. [Restricted products](#3-restricted-products)
   - [The algebraic construction](#31-the-algebraic-construction)
   - [The restricted-product topology](#32-the-restricted-product-topology)
   - [Local compactness and compact opens](#33-local-compactness-and-compact-opens)
   - [Mapping properties](#34-mapping-properties)
   - [Restricted products as increasing unions](#35-restricted-products-as-increasing-unions)
   - [Completeness, countability, and quotients](#36-completeness-countability-and-quotients)
   - [Dependence on the distinguished subgroups](#37-dependence-on-the-distinguished-subgroups)
4. [Finite and full adeles](#4-finite-and-full-adeles)
   - [The finite adele ring](#41-the-finite-adele-ring)
   - [The full adele ring](#42-the-full-adele-ring)
   - [Neighborhoods as local specifications](#43-neighborhoods-as-local-specifications)
   - [Scalar extension](#44-scalar-extension)
   - [The finite principal-parts quotient](#45-the-finite-principal-parts-quotient)
   - [Adelic trace](#46-adelic-trace)
   - [Linear algebra over the adele ring](#47-linear-algebra-over-the-adele-ring)
5. [Diagonal arithmetic and approximation](#5-diagonal-arithmetic-and-approximation)
   - [The diagonal embedding](#51-the-diagonal-embedding)
   - [Density in the finite adeles](#52-density-in-the-finite-adeles)
   - [Discreteness in the full adeles](#53-discreteness-in-the-full-adeles)
   - [A local--global warning](#54-a-local--global-warning)
   - [Weak approximation at arbitrary places](#55-weak-approximation-at-arbitrary-places)
6. [The compact additive quotient](#6-the-compact-additive-quotient)
   - [Why compactness is the central additive theorem](#61-why-compactness-is-the-central-additive-theorem)
   - [Principal parts at finite places](#62-principal-parts-at-finite-places)
   - [A compact fundamental set](#63-a-compact-fundamental-set)
   - [A quotient model with integral gluing](#64-a-quotient-model-with-integral-gluing)
   - [The rational fundamental domain](#65-the-rational-fundamental-domain)
   - [Additive Haar measure and covolume](#66-additive-haar-measure-and-covolume)
   - [Consequences and boundaries](#67-consequences-and-boundaries)
   - [Adelic lattices and finite intersections](#68-adelic-lattices-and-finite-intersections)
7. [Ideles and their topology](#7-ideles-and-their-topology)
   - [Why nonzero adeles are not enough](#71-why-nonzero-adeles-are-not-enough)
   - [The idele group](#72-the-idele-group)
   - [Additive and multiplicative information](#73-additive-and-multiplicative-information)
   - [Open subgroups and local factorization](#74-open-subgroups-and-local-factorization)
   - [Principal ideles](#75-principal-ideles)
   - [Convergence of ideles](#76-convergence-of-ideles)
8. [Ideals inside ideles](#8-ideals-inside-ideles)
   - [From local valuations to a fractional ideal](#81-from-local-valuations-to-a-fractional-ideal)
   - [Recovering the ideal class group](#82-recovering-the-ideal-class-group)
   - [Finiteness revisited topologically](#83-finiteness-revisited-topologically)
   - [Lattices and finite ideles](#84-lattices-and-finite-ideles)
   - [What ideals forget](#85-what-ideals-forget)
   - [Ordinary and narrow ideal classes](#86-ordinary-and-narrow-ideal-classes)
   - [The divisor sequence in one view](#87-the-divisor-sequence-in-one-view)
9. [The idele module and compactness](#9-the-idele-module-and-compactness)
   - [The global module](#91-the-global-module)
   - [Dirichlet's unit lattice](#92-dirichlets-unit-lattice)
   - [Compactness of the norm-one class group](#93-compactness-of-the-norm-one-class-group)
   - [Structure of the full idele class group](#94-structure-of-the-full-idele-class-group)
   - [The compact kernel over the ideal class group](#95-the-compact-kernel-over-the-ideal-class-group)
   - [Compactness criteria and finite quotients](#96-compactness-criteria-and-finite-quotients)
   - [The module as a Haar modulus](#97-the-module-as-a-haar-modulus)
10. [Norms across extensions](#10-norms-across-extensions)
    - [The local norm as a multiplicative determinant](#101-the-local-norm-as-a-multiplicative-determinant)
    - [The adelic norm](#102-the-adelic-norm)
    - [Compatibility with principal ideles](#103-compatibility-with-principal-ideles)
    - [Local conditions versus a global norm](#104-local-conditions-versus-a-global-norm)
    - [Examples of norm behavior](#105-examples-of-norm-behavior)
    - [Norms and congruence depth](#106-norms-and-congruence-depth)
11. [Congruence subgroups and ray classes](#11-congruence-subgroups-and-ray-classes)
    - [Why ideals need local unit data](#111-why-ideals-need-local-unit-data)
    - [Local congruence groups](#112-local-congruence-groups)
    - [The ideal-theoretic description](#113-the-ideal-theoretic-description)
    - [Finiteness of ray class groups](#114-finiteness-of-ray-class-groups)
    - [Open compact subgroups](#115-open-compact-subgroups)
    - [Conductors at the elementary level](#116-conductors-at-the-elementary-level)
    - [Computing elementary ray quotients](#117-computing-elementary-ray-quotients)
12. [Explicit adelic portraits](#12-explicit-adelic-portraits)
    - [The rational field](#121-the-rational-field)
    - [The Gaussian field](#122-the-gaussian-field)
    - [A real quadratic field](#123-a-real-quadratic-field)
    - [A nonprincipal ideal as an idele](#124-a-nonprincipal-ideal-as-an-idele)
    - [Split places and norm components](#125-split-places-and-norm-components)
    - [Quadratic splitting as an adelic product](#126-quadratic-splitting-as-an-adelic-product)
13. [The local--global architecture](#13-the-local--global-architecture)
    - [Two restricted products, two kinds of gluing](#131-two-restricted-products-two-kinds-of-gluing)
    - [Exact hypotheses and durable consequences](#132-exact-hypotheses-and-durable-consequences)
    - [What has not been asserted](#133-what-has-not-been-asserted)
    - [Conclusion](#134-conclusion)

## 1. One field, all of its local shadows

### 1.1 The local--global problem

A number field is simultaneously visible through many inequivalent notions of nearness. At one prime, two numbers are close when their difference is highly divisible by that prime; at a real embedding, they are close in the ordinary metric. Completion isolates one such view. Arithmetic, however, rarely permits us to forget all the others. A rational equation may have to be solved at every place, an integral condition may be imposed away from a finite set, and a global element must satisfy all these demands at once.

The first temptation is to take the product of all completions. That product is too large. An arbitrary family may have denominators at infinitely many primes, whereas a single algebraic number has only finitely many prime divisors in its denominator. The opposite temptation, the direct sum, is too small: it excludes the family whose component is $1$ everywhere, and therefore has no multiplicative identity. The restricted product occupies the precise middle ground. It permits arbitrary local behavior at finitely many places and requires integrality at the rest.

This book develops that construction first additively and then multiplicatively. The additive object makes approximation and compact quotients transparent. The multiplicative object remembers valuations, ideals, units, and norms. Their resemblance is useful, but their topologies are not interchangeable. A recurring theme will be that the chosen compact local subgroups are part of the construction, not cosmetic constraints.

We assume the valuation, completion, and nonarchimedean topology developed in the preceding volume. We briefly recall the notation needed here and supply the global algebraic-number-theoretic framework.

### 1.2 Number fields and their integers

A **number field** is a finite extension $K/\mathbf Q$. Its degree is denoted $n=[K:\mathbf Q]$. An element of $K$ is an **algebraic integer** if it satisfies a monic polynomial in $\mathbf Z[X]$; the algebraic integers form the ring $\mathcal O_K$. It is a free abelian group of rank $n$, and it is a Dedekind domain. Thus every nonzero fractional ideal has a unique factorization

$$
\mathfrak a=\prod_{\mathfrak p}\mathfrak p^{n_{\mathfrak p}},
$$

where $\mathfrak p$ ranges over nonzero prime ideals, the exponents are integers, and all but finitely many vanish. We write $I_K$ for the group of nonzero fractional ideals and $P_K$ for the subgroup of principal fractional ideals.

The **absolute norm** of a nonzero integral ideal is

$$
N\mathfrak a=|\mathcal O_K/\mathfrak a|.
$$

It is multiplicative and satisfies $N\mathfrak p=|k(\mathfrak p)|$, where $k(\mathfrak p)=\mathcal O_K/\mathfrak p$. For $a\in K^\times$,

$$
N((a))=|N_{K/\mathbf Q}(a)|
$$

when the ideal norm is extended multiplicatively to fractional ideals. Unique factorization gives an additive order

$$
\operatorname{ord}_{\mathfrak p}:K^\times\longrightarrow\mathbf Z,
\qquad
(a)=\prod_{\mathfrak p}\mathfrak p^{\operatorname{ord}_{\mathfrak p}(a)}.
$$

The localization $\mathcal O_{K,\mathfrak p}$ is a discrete valuation ring with this valuation. Its completion has fraction field $K_{\mathfrak p}$ and valuation ring $\mathcal O_{\mathfrak p}$. We denote its maximal ideal by $\mathfrak p\mathcal O_{\mathfrak p}$, often simply $\mathfrak p_v$, and its residue field still by $k(\mathfrak p)$. The compactness of $\mathcal O_{\mathfrak p}$ follows from completeness, discreteness, and finiteness of the residue field.

Two finiteness results will be used throughout.

We first recall the geometric lemma behind them. If $\Lambda\subset\mathbf R^n$ is a full lattice of covolume $\Delta$ and $B$ is a convex, centrally symmetric measurable set with volume greater than $2^n\Delta$, then $B$ contains a nonzero point of $\Lambda$. Indeed, the half-sized set $\frac12B$ has volume greater than one fundamental parallelotope. Translating its pieces into that parallelotope forces two distinct points $x,y\in\frac12B$ to have the same image modulo $\Lambda$. Then $0\ne x-y\in\Lambda$, and convexity plus central symmetry gives $x-y\in B$. This is Minkowski's convex-body theorem in the form needed below.

**Theorem 1.1 (finiteness of ideal classes).** The quotient

$$
\operatorname{Cl}(K)=I_K/P_K
$$

is finite.

**Proof strategy.** Embed ideals as lattices in a Euclidean space. A convex-body argument finds a small nonzero element in every ideal. Applied to the inverse of an ideal, it produces an equivalent integral ideal of uniformly bounded norm. There are only finitely many such ideals.

**Proof.** Let $r_1$ be the number of real embeddings and $r_2$ the number of conjugate pairs of complex embeddings, so $n=r_1+2r_2$. Under the Minkowski embedding introduced below, an integral ideal $\mathfrak a$ is a full lattice whose covolume is $2^{-r_2}|d_K|^{1/2}N\mathfrak a$. Minkowski's convex-body theorem, applied to a suitably chosen symmetric box, gives a nonzero $x\in\mathfrak a$ such that

$$
|N_{K/\mathbf Q}(x)|\leq
\left(\frac4\pi\right)^{r_2}\frac{n!}{n^n}|d_K|^{1/2}N\mathfrak a.
$$

Apply this to an integral multiple of $\mathfrak a^{-1}$. After cancellation, the class of $\mathfrak a$ contains an integral ideal $\mathfrak b$ with norm at most the constant on the right that is independent of the class. An integral ideal of norm at most $B$ contains the integer $(m)$ for some bounded $m$: since $|\mathcal O_K/\mathfrak b|\leq B$, the exponent of that finite group is at most $B$, so $m\mathcal O_K\subseteq\mathfrak b$ for some $m\leq B$. For each $m$ there are only finitely many subgroups between $m\mathcal O_K$ and $\mathcal O_K$. Hence there are finitely many possible $\mathfrak b$. $\square$

The exact Minkowski constant is less important here than the uniform bound. Its conclusion will later become a finite decomposition of the idele class group.

### 1.3 Archimedean embeddings and the Minkowski space

Every embedding $K\hookrightarrow\mathbf C$ has image in $\mathbf R$ or occurs in a conjugate pair. Choose all $r_1$ real embeddings and one member from each of the $r_2$ complex pairs. The **Minkowski space** is

$$
K_\infty=\prod_{v\mid\infty}K_v
\cong \mathbf R^{r_1}\times\mathbf C^{r_2}.
$$

The diagonal map sends $a$ to its chosen conjugates. Its image of $\mathcal O_K$ is a full lattice. To see discreteness directly, fix an integral basis $e_1,\ldots,e_n$. The real-linear map from $\mathbf R^n$ to $K_\infty$ sending the standard basis to the images of the $e_i$ is invertible: its determinant is nonzero because the trace pairing is nondegenerate in characteristic zero. It carries $\mathbf Z^n$ to $\mathcal O_K$. A fundamental parallelotope is therefore compact and covers $K_\infty$ under translations by $\mathcal O_K$.

For later measure normalizations, identify a complex coordinate with $\mathbf R^2$ and use ordinary Lebesgue measure. With this convention multiplication by $z\in\mathbf C^\times$ scales area by $|z|_{\mathrm{usual}}^2$, not by $|z|_{\mathrm{usual}}$.

The lattice statement has two consequences worth separating. First, a bounded subset of $K_\infty$ meets $\mathcal O_K$ in finitely many points. Second, the quotient $K_\infty/\mathcal O_K$ is compact. The first will prove discreteness of $K$ inside the adeles; the second is half of the compactness proof for the adelic quotient.

### 1.4 Approximation in a Dedekind domain

Restricted products are useful only if global elements can be fitted to finitely many local demands. The algebraic engine is the Chinese remainder theorem.

**Proposition 1.2 (finite approximation).** Let $S$ be a finite set of finite primes. Given $x_{\mathfrak p}\in K_{\mathfrak p}$ and integers $m_{\mathfrak p}$ for $\mathfrak p\in S$, there exists $a\in K$ such that

$$
\operatorname{ord}_{\mathfrak p}(a-x_{\mathfrak p})\geq m_{\mathfrak p}
\quad(\mathfrak p\in S),
$$

and $a$ is integral at every finite prime outside $S$ at which a denominator has not explicitly been allowed. More precisely, one may choose a fractional ideal $\mathfrak d$ supported on $S$ with $a\in\mathfrak d^{-1}$.

**Proof.** Choose integers $r_{\mathfrak p}\geq0$ so large that every target belongs locally to $\mathfrak p^{-r_{\mathfrak p}}\mathcal O_{\mathfrak p}$, and set

$$
M=\prod_{\mathfrak p\in S}\mathfrak p^{-r_{\mathfrak p}}.
$$

This fractional ideal is integral at every prime outside $S$. Inside the lattice $M$, the required neighborhoods are cosets modulo $M\cap\mathfrak p^{m_{\mathfrak p}}\mathcal O_{K,\mathfrak p}$. After multiplying all modules by one nonzero integer, the ordinary Chinese remainder theorem for pairwise coprime prime powers supplies an element $a\in M$ in all prescribed cosets. Membership in $M$ gives the asserted integrality away from $S$. $\square$

A particularly important form concerns a finite adele $(x_v)$: there exists $a\in K$ with

$$
x_v-a\in\mathcal O_v
$$

at every finite place $v$. Indeed, only finitely many $x_v$ are nonintegral; approximate those with enough precision, and integrality elsewhere follows from the controlled denominator construction. This is sometimes called the principal-parts form of approximation.

Approximation has a limit. Asking for arbitrary conditions at infinitely many primes is generally impossible. For example, a nonzero $a\in K$ has $\operatorname{ord}_{\mathfrak p}(a)=0$ for almost all $\mathfrak p$, so no global number can have positive valuation at every prime. The phrase “almost all” is therefore the arithmetic boundary between global plausibility and an overdetermined fantasy.

### 1.5 Ideal lattices and discriminants

The lattice argument used above deserves a more explicit form because it will reappear in every compactness proof. Choose an integral basis $e_1,\ldots,e_n$ of $\mathcal O_K$. Form the matrix of its conjugates, taking both members of each complex pair, and define

$$
d_K=\det(\operatorname{Tr}_{K/\mathbf Q}(e_ie_j)).
$$

This integer is the discriminant of $K$. It is nonzero because number fields are separable over $\mathbf Q$. In the coordinates $\mathbf R^{r_1}\times\mathbf C^{r_2}$ with ordinary planar area on each complex factor, the covolume of $\mathcal O_K$ is

$$
2^{-r_2}|d_K|^{1/2}.
$$

To verify the formula, compare the real embedding matrix, in which a complex row is replaced by its real and imaginary parts, with the full conjugate matrix. Each conjugate pair changes the absolute determinant by a factor $2$, while the square of the full determinant is the discriminant.

If $\mathfrak a\subseteq\mathcal O_K$ is a nonzero integral ideal, then its additive index in $\mathcal O_K$ is $N\mathfrak a$. Passing from a lattice to a sublattice multiplies covolume by the index, so

$$
\operatorname{covol}(\mathfrak a)
=2^{-r_2}|d_K|^{1/2}N\mathfrak a.
$$

For a fractional ideal the same formula holds with the multiplicatively extended norm. This identity connects three kinds of size: an algebraic index, a finite product of prime powers, and Euclidean volume at infinity. The compactness of adelic quotients is possible because these measurements are compatible rather than independent.

## 2. Places and normalized local size

### 2.1 Why places, rather than primes alone

Prime ideals capture nonarchimedean size, but the embeddings into $\mathbf R$ and $\mathbf C$ are equally necessary. The equation $x^2+1=0$ is solvable in every $\mathbf Q_p$ for many primes and fails over $\mathbf R$; inequalities and signs are invisible to finite primes. A **place** packages one equivalence class of nontrivial absolute values and places the archimedean and finite worlds in one index set.

Two absolute values are equivalent if they define the same topology, equivalently if one is a positive real power of the other. For a number field, the places are exactly:

- a finite place $v=\mathfrak p$ for each nonzero prime ideal of $\mathcal O_K$;
- a real place for each real embedding;
- a complex place for each conjugate pair of nonreal embeddings.

We write $v<\infty$ and $v\mid\infty$ for the two kinds. The completion at $v$ is $K_v$. At a complex place the two conjugate embeddings give canonically isomorphic topological fields, so choosing one causes no arithmetic ambiguity.

### 2.2 The global normalization

Equivalent absolute values have the same topology but not the same product. Global arguments require one representative at each place.

For $v=\mathfrak p<\infty$, define

$$
|x|_v=(N\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}(x)}.
$$

For a real place associated to $\sigma:K\hookrightarrow\mathbf R$, put $|x|_v=|\sigma(x)|_{\mathrm{usual}}$. For a complex place, put

$$
|x|_v=|\sigma(x)|_{\mathrm{usual}}^2.
$$

The square is essential: a complex place represents two conjugate embeddings. It also makes multiplication on $\mathbf C$ scale additive Haar measure by $|z|_v$.

**Theorem 2.1 (product formula).** For every $a\in K^\times$,

$$
\prod_v|a|_v=1,
$$

and all but finitely many factors equal $1$.

**Proof.** The finite part is

$$
\prod_{v<\infty}|a|_v
=\prod_{\mathfrak p}(N\mathfrak p)^{-\operatorname{ord}_{\mathfrak p}(a)}
=|N_{K/\mathbf Q}(a)|^{-1},
$$

by the norm formula for the principal fractional ideal $(a)$. The archimedean part is

$$
\prod_{v\mid\infty}|a|_v
=\prod_{\sigma\ \mathrm{real}}|\sigma(a)|
\prod_{\{\sigma,\bar\sigma\}}|\sigma(a)|^2
=|N_{K/\mathbf Q}(a)|.
$$

Multiplication gives $1$. Finite support follows from the factorization of $(a)$. $\square$

If the complex absolute value were not squared, the formula would require local degree exponents. Either convention can be made consistent; mixing them cannot.

### 2.3 The rational model for all normalizations

Before continuing over $K$, it helps to see the complete list over $\mathbf Q$. Every nontrivial absolute value on $\mathbf Q$ is equivalent either to the usual real absolute value or to a $p$-adic absolute value for one prime $p$. This classification is the reason that the index set of places has no missing exotic members.

Here is the central argument. If an absolute value is archimedean, some positive integer has size greater than $1$. Comparing base-$m$ expansions and powers shows that the absolute value is a positive power of the usual one. If it is nonarchimedean and nontrivial, every integer has size at most $1$, and some prime $p$ has size below $1$. Two distinct primes cannot both have size below $1$, because Bézout would make $1$ have size below $1$. Every integer prime to $p$ then has size $1$, and multiplicativity shows that the absolute value is a positive power of $p^{-v_p(\cdot)}$.

Our chosen representatives are

$$
|x|_\infty=|x|_{\mathrm{usual}},
\qquad
|x|_p=p^{-v_p(x)}.
$$

The familiar identity

$$
|a|_\infty\prod_p|a|_p=1
$$

for $a\in\mathbf Q^\times$ is the prototype of Theorem 2.1. For a number field, restricting a normalized place to $\mathbf Q$ may introduce its local degree, but summing those local degrees over the places above a rational place recovers $[K:\mathbf Q]$.

### 2.4 Local integers and local units

At a finite place set

$$
\mathcal O_v=\{x\in K_v:|x|_v\leq1\},\qquad
\mathfrak p_v=\{x:|x|_v<1\}.
$$

Then $\mathcal O_v$ is the completed discrete valuation ring, $\mathfrak p_v$ its maximal ideal, and

$$
\mathcal O_v^\times=\{x\in K_v^\times:|x|_v=1\}.
$$

If $\pi_v$ is a uniformizer and $q_v=|\mathcal O_v/\mathfrak p_v|$, then $|\pi_v|_v=q_v^{-1}$ and

$$
K_v^\times=\pi_v^{\mathbf Z}\times\mathcal O_v^\times
$$

after a choice of uniformizer. The integer factor is canonical through $\operatorname{ord}_v$; the displayed splitting is not.

The sets $\mathfrak p_v^m$ form a neighborhood basis of $0$. They are compact and open. Similarly $1+\mathfrak p_v^m$ is an open subgroup of $\mathcal O_v^\times$ for $m\geq1$. These compact open subgroups are the local pieces from which the global topology will be assembled.

At an archimedean place there is no analogous open compact integer ring. The closed unit interval or disk is compact but not a subgroup under addition, and its unit circle is not open in $\mathbf C^\times$. This difference explains why restrictedness is imposed only at finite places.

### 2.5 Extension and local norms

Let $L/K$ be a finite extension, let $v$ be a place of $K$, and let $w$ run through places of $L$ above $v$. Completion separates the branches:

$$
L\otimes_KK_v\cong\prod_{w\mid v}L_w.
$$

Our normalizations satisfy the especially clean identity

$$
|N_{L_w/K_v}(y)|_v=|y|_w
\qquad(y\in L_w^\times).
$$

At finite places, $\operatorname{ord}_v(Ny)=f(w/v)\operatorname{ord}_w(y)$ and $q_w=q_v^{f(w/v)}$, proving the formula. At archimedean places it is immediate except for $\mathbf C/\mathbf R$, where $N(z)=z\bar z$ and the square in the complex normalization gives exactly the same equality.

For an element $(y_w)_{w\mid v}$ of the product algebra, its norm is the product of the field norms, hence

$$
\left|\prod_{w\mid v}N_{L_w/K_v}(y_w)\right|_v
=\prod_{w\mid v}|y_w|_w.
$$

This compatibility will make the global idele norm commute with extension norms without correction exponents.

### 2.6 Local degrees over a rational place

Let $p$ be a rational prime. Factoring $p\mathcal O_K$ as

$$
p\mathcal O_K=\prod_{\mathfrak p\mid p}\mathfrak p^{e_{\mathfrak p}}
$$

gives local degrees

$$
[K_{\mathfrak p}:\mathbf Q_p]
=e_{\mathfrak p}f_{\mathfrak p},
\qquad
\sum_{\mathfrak p\mid p}e_{\mathfrak p}f_{\mathfrak p}=n.
$$

The residue field at $\mathfrak p$ has $p^{f_{\mathfrak p}}$ elements. If $a\in\mathbf Q_p^\times$ is viewed in $K_{\mathfrak p}$, then

$$
|a|_{\mathfrak p}=|a|_p^{[K_{\mathfrak p}:\mathbf Q_p]}.
$$

Indeed, $\operatorname{ord}_{\mathfrak p}(a)=e_{\mathfrak p}v_p(a)$ and $N\mathfrak p=p^{f_{\mathfrak p}}$. Multiplying over $\mathfrak p\mid p$ gives $|a|_p^n$.

At infinity the same accounting holds with local degrees $1$ for $\mathbf R/\mathbf R$ and $2$ for $\mathbf C/\mathbf R$. Consequently a rational number embedded in $K$ satisfies

$$
\prod_{v\text{ over a fixed place }u\text{ of }\mathbf Q}|a|_v=|a|_u^n.
$$

This formula reconciles the normalization internal to $K$ with the rational one. It also explains why scalar extension raises the idele module to the global degree while the norm map does not.

## 3. Restricted products

### 3.1 The algebraic construction

Let $(G_i)_{i\in I}$ be topological groups, and choose a subgroup $H_i\subseteq G_i$ for all but finitely many $i$. The **restricted product** is

$$
\prod_i' (G_i,H_i)
=\left\{(g_i)\in\prod_iG_i:g_i\in H_i\text{ for almost all }i\right\}.
$$

It is a group under componentwise operations. For every finite set $S$ containing the exceptional indices, define the stage

$$
G(S)=\prod_{i\in S}G_i\times\prod_{i\notin S}H_i.
$$

Then the restricted product is the increasing union of the $G(S)$.

This definition retains the identity family and every diagonal global element whose local components lie in $H_i$ almost everywhere. It excludes families with infinitely many denominators. For additive local fields we will take $H_v=\mathcal O_v$; for multiplicative local fields, $H_v=\mathcal O_v^\times$. The change from integers to units is forced: a nonzero global number has valuation zero, not merely nonnegative valuation, at almost every prime.

### 3.2 The restricted-product topology

Assume each $H_i$ is open in $G_i$. A basic open set in the restricted product is

$$
\prod_iU_i,
$$

where every $U_i\subseteq G_i$ is open and $U_i=H_i$ for all but finitely many $i$. Translates of such sets form a basis. Equivalently, each $G(S)$ has its ordinary product topology and is declared to be an open subgroup; these requirements determine the topology on the union.

The equivalence deserves proof. A basic product belongs to some $G(S)$ and is open there. Conversely, an open subset of a stage is a union of products restricting only finitely many coordinates; because the stage itself is open, these products are open in the union. Intersections are again basic: outside the union of two finite exceptional sets, both factors equal $H_i$.

This topology is not the subspace topology inherited from the unrestricted product. In the unrestricted product, a neighborhood restricts only finitely many coordinates and leaves every other coordinate equal to all of $G_i$. In the restricted product, every unmentioned coordinate is constrained to $H_i$. The distinction is the source of local compactness.

### 3.3 Local compactness and compact opens

**Proposition 3.1.** If every $G_i$ is locally compact and every distinguished $H_i$ is compact open, then the restricted product is locally compact. The product $\prod_iH_i$ is compact open.

**Proof.** Tychonoff's theorem makes $\prod_iH_i$ compact; it is open by the definition of the restricted topology. Its translates are compact neighborhoods. More generally, choose compact neighborhoods in finitely many exceptional factors and use $H_i$ elsewhere. Their product is a compact neighborhood of any specified point. $\square$

The unrestricted product of the $K_v$ is also locally compact only in special finite situations; in our infinite arithmetic product it has no compact neighborhood of zero. Indeed, a product neighborhood leaves infinitely many whole noncompact factors unrestricted. The direct sum has other defects and does not contain the diagonal identity. Restricted products are therefore not a convenient compromise but the construction selected by topology and arithmetic simultaneously.

### 3.4 Mapping properties

The stage description gives a practical universal property. A map $F$ from a restricted product to a topological space is continuous if and only if every restriction $F|_{G(S)}$ is continuous. This is the final-topology property of the open union. For a homomorphism it is enough to check continuity on one open neighborhood of the identity in each stage.

There is also a coordinatewise functoriality statement. Suppose $f_i:G_i\to G_i'$ are continuous homomorphisms and $f_i(H_i)\subseteq H_i'$ for almost all $i$. Then

$$
(g_i)\longmapsto(f_i(g_i))
$$

defines a continuous homomorphism between restricted products. On a basic target neighborhood, only finitely many coordinates demand more than membership in $H_i'$, and coordinatewise continuity handles those. If $f_i^{-1}(H_i')=H_i$ for almost all $i$, the preimage of the standard compact open has the expected form.

An infinite product of scalar-valued functions generally does **not** follow from this property. It is defined only when almost every factor is $1$, or when a separate convergence argument is supplied. The idele norm works because local units have absolute value $1$.

### 3.5 Restricted products as increasing unions

Fix an exhaustion $S_1\subseteq S_2\subseteq\cdots$ of a countable set of places by finite subsets. Then

$$
\prod_i'(G_i,H_i)=\bigcup_mG(S_m).
$$

Each inclusion $G(S_m)\hookrightarrow G(S_{m+1})$ is open. A compact subset need not lie in an arbitrary member of an arbitrary open cover, but it does lie in some stage: the stages form an increasing open cover, so compactness gives finitely many stages and the largest suffices. This observation often reduces compactness arguments to finite products.

One must not confuse this union topology with an algebraic direct limit in a category that forgets the specified open embeddings. The topology remembers both unrestricted exceptional factors and the infinite compact tail. That tail is where simultaneous integrality lives.

### 3.6 Completeness, countability, and quotients

When the index set is countable and each local group is metrizable, a restricted product is metrizable. One may choose an exhaustion $S_m$ and compatible bounded metrics, penalizing departure from $H_i$ increasingly strongly outside $S_m$. In the number-field case the places are countable and the local fields are second countable, so the adele and idele groups are second countable and $\sigma$-compact.

They are also complete for their natural uniform structures. A Cauchy net is eventually contained, after translation, in a fixed neighborhood whose tail lies in $\prod H_i$; coordinatewise completeness supplies its limit, and completeness of the compact tail ensures that the limiting family remains restricted. For sequences, the same idea is concrete: sufficiently late differences are integral, or multiplicative quotients are units, outside one finite set, and each coordinate converges locally.

Closed subgroups of locally compact groups are locally compact, and quotients by closed normal subgroups are locally compact and Hausdorff. These facts justify the topological claims about $K$, $K^\times$, $\mathbf A_K/K$, and $C_K$ once diagonal closedness has been established. Second countability ensures that sequences suffice for many later arguments, although none of the definitions depends on that convenience.

### 3.7 Dependence on the distinguished subgroups

The notation $\prod'G_i$ is incomplete until the $H_i$ are specified. If one changes $H_i$ at only finitely many indices, neither the underlying restricted product nor its topology changes: those indices can simply be absorbed into every exceptional set. This is why finitely many ramified primes or finitely many poorly chosen integral bases cause no difficulty.

An infinite change can alter the object. In $\prod_p\mathbf Q_p$, compare the conditions $x_p\in\mathbf Z_p$ almost everywhere and $x_p\in p\mathbf Z_p$ almost everywhere. The identity family belongs to the first restricted product and not the second. Although $p\mathbf Z_p$ and $\mathbf Z_p$ are commensurable at every individual prime, pointwise commensurability is not enough to make infinitely many simultaneous changes harmless.

For finite-dimensional vector spaces over $K$, an $\mathcal O_K$-lattice gives a compact open lattice at every finite completion. Two global lattices become equal locally outside the finite set of primes dividing their index. Their adelic restricted products are therefore canonically the same. This is the mechanism behind basis independence in the scalar-extension result of Section 4.4.

The lesson is categorical as well as practical: a restricted product is a family of local groups together with an almost-everywhere integral model. Arithmetic supplies that model canonically through $\mathcal O_K$ or through a global lattice.

## 4. Finite and full adeles

### 4.1 The finite adele ring

The additive restricted product over finite places is the **finite adele ring**

$$
\mathbf A_{K,f}=\prod_{v<\infty}'(K_v,\mathcal O_v).
$$

Thus $x=(x_v)$ is a finite adele when $x_v\in\mathcal O_v$ for almost every $v$. Addition and multiplication are coordinatewise. Multiplication is continuous: near $(x,y)$, choose a finite set containing every place where either coordinate is nonintegral; outside it, products remain integral, while continuity at the remaining finitely many coordinates is ordinary local continuity. Hence $\mathbf A_{K,f}$ is a locally compact topological ring.

Its standard compact open subring is

$$
\widehat{\mathcal O}_K=\prod_{v<\infty}\mathcal O_v.
$$

The hat here denotes the product of all finite local integer rings. It agrees canonically with the profinite completion $\varprojlim_{\mathfrak a}\mathcal O_K/\mathfrak a$. Indeed, reduction of a compatible local family modulo an ideal uses only its finitely many prime divisors, and the Chinese remainder theorem reconstructs the family from the finite quotients.

For $K=\mathbf Q$,

$$
\mathbf A_{\mathbf Q,f}=\prod_p'(\mathbf Q_p,\mathbf Z_p),
\qquad
\widehat{\mathbf Z}=\prod_p\mathbf Z_p.
$$

The family $(1/p)_p$ does not define a finite adele: it is nonintegral at every coordinate. The family with $p$th component $1/p$ at one fixed prime and $0$ elsewhere does. So does the diagonal family associated to any rational number.

### 4.2 The full adele ring

Archimedean places are finite in number and need no restriction. The **adele ring** is

$$
\mathbf A_K=K_\infty\times\mathbf A_{K,f}
=\prod_v'(K_v,\mathcal O_v),
$$

where the notation in the last expression imposes $\mathcal O_v$ only for $v<\infty$. It is a locally compact topological ring. A typical basic open set is

$$
\prod_{v\in S}U_v\times\prod_{v\notin S,\,v<\infty}\mathcal O_v,
$$

where $S$ is finite and contains all archimedean places, and each $U_v$ is open in $K_v$.

There is no distinguished compact open subring of the full adele ring because $K_\infty$ has no compact open additive subgroup. Sets of the form

$$
C_\infty\times\widehat{\mathcal O}_K
$$

with $C_\infty$ compact are compact neighborhoods only when $C_\infty$ contains an open neighborhood, and then they are neighborhoods but not subgroups. This minor-looking distinction becomes important whenever one passes between finite and full adeles.

### 4.3 Neighborhoods as local specifications

A basic neighborhood of $x\in\mathbf A_K$ says three things:

1. at finitely many places, $y_v$ must approximate $x_v$ to explicitly chosen precision;
2. at every other finite place, $y_v-x_v$ must be integral;
3. at archimedean places, ordinary open conditions apply.

Thus adelic openness encodes finitely many delicate local requirements plus a uniform almost-everywhere boundedness requirement. Merely taking the product topology on the same underlying set would omit the third ingredient at almost all finite coordinates.

For example, in $\mathbf A_{\mathbf Q,f}$ the subgroups

$$
m\widehat{\mathbf Z}=\prod_p p^{\operatorname{ord}_p(m)}\mathbf Z_p
$$

are compact open for nonzero integers $m$. More generally, every fractional ideal $\mathfrak a$ has a completion

$$
\widehat{\mathfrak a}=\prod_{v<\infty}\mathfrak p_v^{\operatorname{ord}_v(\mathfrak a)},
$$

a compact open additive subgroup of $\mathbf A_{K,f}$. Allowing independently chosen exponents at finitely many primes gives the same collection. These subgroups form a neighborhood basis of $0$ up to imposing finer open subgroups in finitely many coordinates.

### 4.4 Scalar extension

For a finite extension $L/K$, the local decomposition from Section 2.5 assembles to a topological isomorphism

$$
L\otimes_K\mathbf A_K\cong\mathbf A_L.
$$

To justify a tensor product statement that appears infinite, choose a $K$-basis of $L$. Both sides are then finite-dimensional $\mathbf A_K$-modules. Locally, $L\otimes_KK_v$ is the product of the $L_w$ over $v$. At almost every finite $v$, integral closure is unramified and the chosen integral lattice identifies with the product of the $\mathcal O_w$; only finitely many primes divide the discriminant or denominators of the basis. Therefore the local isomorphisms preserve the distinguished compact subgroups almost everywhere and assemble by restricted-product functoriality.

This formula says that forming all completions commutes with finite extension, provided all branches over every place are retained. It is the adelic version of the completed product theorem.

### 4.5 The finite principal-parts quotient

Because $\widehat{\mathcal O}_K$ is open, the additive quotient

$$
\mathbf A_{K,f}/\widehat{\mathcal O}_K
$$

is discrete. It records only the finitely many negative local digits of an adele. There is a natural map

$$
K/\mathcal O_K\longrightarrow
\mathbf A_{K,f}/\widehat{\mathcal O}_K.
$$

It is injective because a global element integral at every finite prime lies in $\mathcal O_K$. It is surjective by the principal-parts approximation of Section 1.4. Hence

$$
K/\mathcal O_K\cong
\mathbf A_{K,f}/\widehat{\mathcal O}_K.
$$

This identity is the additive counterpart of the idele-to-ideal exact sequence, but its right side is not an ideal group. Addition permits cancellation among principal parts, and $K/\mathcal O_K$ is generally a torsion group rather than a free abelian group on primes.

For $\mathbf Q$, the class of a finite adele with components $p^{-2}+p^{-1}$ at $p$, $q^{-1}$ at a different prime $q$, and integral components elsewhere is represented by

$$
\frac1{p^2}+\frac1p+\frac1q
$$

modulo $\mathbf Z$, after correcting the terms at the other primes by the Chinese remainder theorem if necessary. The correction matters: a rational summand chosen to match one $p$-adic principal part can create unit-level changes elsewhere, but those changes vanish in the quotient by local integers.

### 4.6 Adelic trace

The additive companion to the idele norm is the trace. For a finite extension $L/K$, define

$$
(\operatorname{Tr}_{L/K}^{\mathbf A}y)_v
=\sum_{w\mid v}\operatorname{Tr}_{L_w/K_v}(y_w).
$$

At almost every finite place every $y_w$ is integral, and the trace of an integral element is integral. Hence this formula defines a continuous $\mathbf A_K$-linear map

$$
\operatorname{Tr}_{L/K}^{\mathbf A}:\mathbf A_L\longrightarrow\mathbf A_K.
$$

For a principal adele $a\in L$, the result is the principal adele associated to $\operatorname{Tr}_{L/K}(a)$. This follows because the trace of multiplication on $L\otimes_KK_v$ is the sum of the traces on its field factors.

Trace is transitive in towers and is compatible with the scalar-extension isomorphism $\mathbf A_L\cong L\otimes_K\mathbf A_K$. Unlike the norm, it is additive and may annihilate nonzero elements. In characteristic zero the global trace pairing on $L/K$ is nondegenerate, but surjectivity on integral local rings can fail at ramified primes. Thus one should distinguish field-level nondegeneracy from integrality properties.

The trace and norm are the additive and multiplicative shadows of the same finite-dimensional algebra: trace is the trace of multiplication, norm its determinant. Their adelic definitions work because both preserve integral structures at almost all places.

### 4.7 Linear algebra over the adele ring

For a finite-dimensional $K$-vector space $V$, choose an $\mathcal O_K$-lattice $M\subset V$ and define

$$
V(\mathbf A_K)=V\otimes_K\mathbf A_K
\cong V(K_\infty)\times
\prod_{v<\infty}'(V\otimes_KK_v,M\otimes_{\mathcal O_K}\mathcal O_v).
$$

The preceding section shows that this topology is independent of $M$: any two lattices contain nonzero integral multiples of one another, so their localizations agree outside finitely many primes. After choosing a basis, $V(\mathbf A_K)$ is topologically $\mathbf A_K^{\dim V}$, but the lattice formulation is basis-free.

Every $K$-linear map $T:V\to W$ extends continuously to adelic points. Indeed, after multiplying one lattice by a nonzero integer, $T$ carries it into a lattice of $W$, so the local maps preserve the distinguished integral subgroups almost everywhere. Kernels commute with this extension because finite-dimensional scalar extension is exact. Images of invertible maps are open and closed, as they are coordinatewise isomorphisms.

This modest piece of adelic linear algebra is the reason matrices with entries in $\mathbf A_K$ can later act coherently at all places. It also clarifies why a global integral structure, even when suppressed from notation, underlies every restricted product of vector spaces.

## 5. Diagonal arithmetic and approximation

### 5.1 The diagonal embedding

Every $a\in K$ determines an adele $(a)_v$. At almost every finite place $a$ is a unit or zero, so certainly integral. Thus there is a ring homomorphism

$$
K\longrightarrow\mathbf A_K,\qquad a\longmapsto(a)_v.
$$

It is injective because every completion map is injective. We henceforth identify $K$ with its diagonal image. The same map into $\mathbf A_{K,f}$ is also injective, but it behaves topologically very differently: $K$ is dense in the finite adeles and discrete in the full adeles.

The contrast is not paradoxical. Finite approximation can meet any finite collection of nonarchimedean conditions, so the finite diagonal is dense. Adding even one archimedean factor supplies a size constraint that prevents denominators and numerators from escaping simultaneously.

### 5.2 Density in the finite adeles

**Theorem 5.1.** The diagonal image of $K$ is dense in $\mathbf A_{K,f}$.

**Proof.** Let $x=(x_v)$ and let $U=\prod U_v$ be a basic neighborhood of $x$. There is a finite set $S$ such that $U_v=x_v+\mathcal O_v$ outside $S$, while for $v\in S$ the set $U_v$ contains $x_v+\mathfrak p_v^{m_v}$ for some integer $m_v$. Finite approximation supplies $a\in K$ satisfying these finitely many congruences and integral-difference conditions elsewhere. Then the diagonal adele $a$ belongs to $U$. $\square$

The theorem fails for the full adeles. Indeed, a discrete nontrivial subgroup cannot be dense in a nondiscrete Hausdorff group. More concretely, finite congruences can force a rational number into a desired residue class, but simultaneously confining all its archimedean conjugates to a tiny box may leave no lattice point.

### 5.3 Discreteness in the full adeles

**Theorem 5.2.** The diagonal copy of $K$ is a discrete closed subgroup of the additive group $\mathbf A_K$.

**Proof strategy.** Force finite integrality, which reduces a diagonal element to $\mathcal O_K$, and then use a small archimedean neighborhood containing no nonzero lattice point.

**Proof.** Since $\mathcal O_K\subset K_\infty$ is a discrete lattice, choose an open neighborhood $U_\infty$ of $0$ such that

$$
U_\infty\cap\mathcal O_K=\{0\}.
$$

Then

$$
U=U_\infty\times\widehat{\mathcal O}_K
$$

is an open neighborhood of zero in $\mathbf A_K$. If a diagonal $a\in K$ lies in $U$, its finite components are integral at every prime, so $a\in\mathcal O_K$; its infinite component lies in $U_\infty$, so $a=0$. Translates show that every point of $K$ is isolated in $K$.

A discrete subgroup of a Hausdorff topological group need not always be closed without additional care, but here closure follows directly. Choose a smaller symmetric neighborhood $V$ with $V-V\subseteq U$. If a point lay in the closure of $K$, the set of its nearby translates would give two distinct elements of $K$ whose difference lies in $U$, impossible. $\square$

The full set of places is essential. In $\mathbf A_{K,f}$, the neighborhood $\widehat{\mathcal O}_K$ meets $K$ in $\mathcal O_K$, an infinite set.

### 5.4 A local--global warning

The diagonal embedding records compatibility, but it does not assert that every locally solvable equation has a global solution. The conic $x^2+y^2=-1$ fails already over $\mathbf R$, while subtler varieties can have points over every completion and none over $K$. Adeles provide the space in which such obstructions are formulated; they do not erase them.

Even linear approximation needs its hypotheses. Weak approximation concerns finitely many places. Stronger statements that prescribe integrality outside a set require that the omitted set permit denominators. The density theorem above works in the finite adele ring because a basic neighborhood asks only for integral error almost everywhere, not exact equality in infinitely many coordinates.

### 5.5 Weak approximation at arbitrary places

**Theorem 5.3 (weak approximation).** For distinct places $v_1,\ldots,v_r$, the diagonal image of $K$ is dense in

$$
K_{v_1}\times\cdots\times K_{v_r}.
$$

**Proof strategy.** Construct approximate coordinate selectors: global elements close to $1$ at one chosen place and close to $0$ at all the others. A linear combination then approximates arbitrary targets.

**Proof.** Inequivalence of two absolute values supplies an element that is small in one and large in the other. Indeed, if every element small for one were bounded for the other, the two induced topologies would be comparable and hence, for absolute values on a field, equivalent. Taking a suitable power and replacing $z$ by $z/(1+z)$ produces an element close to $1$ at one place and close to $0$ at the other.

For finitely many places, multiply pairwise separators and raise them to large powers to obtain $e_i\in K$ with $e_i$ arbitrarily close to $1$ at $v_i$ and to $0$ at every $v_j$, $j\ne i$. First approximate each desired local target $x_i\in K_{v_i}$ by some $a_i\in K$, using the definition of completion. Then

$$
a=\sum_{i=1}^r e_i a_i
$$

is as close to $x_i$ at $v_i$ as desired. The errors from the other summands are small, and the $i$th summand differs from $a_i$ by the small factor $e_i-1$. $\square$

Weak approximation permits archimedean and nonarchimedean targets together, but it says nothing about uncontrolled places. Adelic density additionally demands an almost-everywhere tail condition. In the finite adeles that condition can be preserved; in the full adeles discreteness prevents density.

## 6. The compact additive quotient

### 6.1 Why compactness is the central additive theorem

Discreteness says global numbers do not cluster adelically. Compactness of the quotient says, conversely, that every adele is uniformly close to some global number. Together they make $K$ a lattice in $\mathbf A_K$.

This is stronger than a formal quotient statement. It supplies compact fundamental regions, makes harmonic analysis possible, and turns global summation into analysis on a locally compact group. The proof cleanly separates finite approximation from the archimedean geometry of numbers.

### 6.2 Principal parts at finite places

**Lemma 6.1.** Every $x_f\in\mathbf A_{K,f}$ can be written

$$
x_f=a+u_f,\qquad a\in K,\quad u_f\in\widehat{\mathcal O}_K.
$$

Equivalently,

$$
\mathbf A_{K,f}=K+\widehat{\mathcal O}_K.
$$

**Proof.** Let $S$ contain the finite places where $x_v\notin\mathcal O_v$. For each $v\in S$, choose $a_v\in K$ sufficiently close to $x_v$ that $x_v-a_v\in\mathcal O_v$. Combining these finitely many residue conditions through Proposition 1.2 gives one $a\in K$ such that $x_v-a\in\mathcal O_v$ for $v\in S$, while the controlled denominator form ensures $a$ is integral outside $S$. There both $x_v$ and $a$ are integral, so their difference is integral. $\square$

For $K=\mathbf Q$, this is the familiar extraction of the finitely many negative $p$-adic digits of an adele and their assembly into one rational number.

### 6.3 A compact fundamental set

Let $D\subset K_\infty$ be a compact fundamental parallelotope for the lattice $\mathcal O_K$. Thus

$$
K_\infty=\mathcal O_K+D.
$$

Consider the compact set

$$
F=D\times\widehat{\mathcal O}_K\subset\mathbf A_K.
$$

**Theorem 6.2.** Every adele is congruent modulo $K$ to a point of $F$. Consequently $\mathbf A_K/K$ is compact.

**Proof.** Write $x=(x_\infty,x_f)$. By Lemma 6.1 choose $a\in K$ with $x_f-a\in\widehat{\mathcal O}_K$. The infinite component $x_\infty-a$ belongs to $K_\infty$. Choose $b\in\mathcal O_K$ such that

$$
x_\infty-a-b\in D.
$$

Because $b$ is integral at every finite place,

$$
x_f-a-b\in\widehat{\mathcal O}_K.
$$

Thus $x-(a+b)\in F$. The quotient map sends the compact set $F$ onto $\mathbf A_K/K$, so the quotient is compact. Since $K$ is closed, the quotient is Hausdorff. $\square$

The two adjustments have distinct roles. The element $a$ removes all finite principal parts but may be archimedeanly large. The algebraic integer $b$ then moves the infinite residue into a bounded lattice cell without spoiling finite integrality.

### 6.4 A quotient model with integral gluing

The proof yields more than compactness. The composite

$$
K_\infty\times\widehat{\mathcal O}_K
\longrightarrow\mathbf A_K\longrightarrow\mathbf A_K/K
$$

is surjective. Its kernel consists exactly of diagonally embedded algebraic integers: if $(x_\infty,u_f)$ is a global diagonal element $a$, then $u_f$ integral everywhere forces $a\in\mathcal O_K$, and the converse is clear. Therefore

$$
\mathbf A_K/K
\cong
\bigl(K_\infty\times\widehat{\mathcal O}_K\bigr)/\mathcal O_K.
$$

The topology on the right is the quotient topology for the diagonal action $a:(x,u)\mapsto(x+a,u+a)$. It is compact even though $K_\infty\times\widehat{\mathcal O}_K$ is not: reduction modulo the lattice bounds the first factor, while the second was compact from the start.

This model also shows why the quotient is not a direct product $(K_\infty/\mathcal O_K)\times\widehat{\mathcal O}_K$. The same algebraic integer translates both factors. Splitting that diagonal action would require a noncanonical and generally discontinuous choice of representatives.

### 6.5 The rational fundamental domain

For $K=\mathbf Q$, take $D=[0,1]$. The theorem says that

$$
[0,1]\times\widehat{\mathbf Z}
$$

surjects onto $\mathbf A_{\mathbf Q}/\mathbf Q$. Boundary points give nonuniqueness, just as $0$ and $1$ represent the same point of $\mathbf R/\mathbf Z$. Away from boundaries one can choose half-open regions to obtain almost-everywhere uniqueness, but a globally continuous choice of representatives does not exist.

The quotient is compact but not finite and not discrete. Its archimedean direction is wrapped by $\mathbf Z$, while its finite directions are already compact after principal parts are removed.

### 6.6 Additive Haar measure and covolume

Every locally compact group admits a nonzero translation-invariant Haar measure, unique up to scaling. On each finite $K_v$, normalize additive measure by

$$
\mu_v(\mathcal O_v)=1.
$$

Use Lebesgue measure at real places and twice ordinary planar measure or ordinary planar measure at complex places according to the desired discriminant normalization. The restricted product measure exists because the distinguished compact opens have measure $1$ almost everywhere.

Multiplication by $a\in K_v^\times$ scales local additive measure by $|a|_v$. At a finite place this follows by decomposing $a$ into a unit and a uniformizer; a uniformizer maps $\mathcal O_v$ onto an index-$q_v$ subgroup. At real and complex places it is the usual Jacobian computation. Globally, diagonal multiplication by $a\in K^\times$ scales by

$$
\prod_v|a|_v=1.
$$

Thus the product formula is exactly the assertion that principal scalars preserve adelic additive volume. No later argument in this book depends on a particular numerical covolume, so we will not impose a global measure normalization beyond these local statements.

### 6.7 Consequences and boundaries

The pair of results

$$
K\subset\mathbf A_K\text{ discrete},
\qquad
\mathbf A_K/K\text{ compact}
$$

is the additive local--global compactness theorem. It remains true for global function fields after replacing the archimedean lattice step by the geometry of a projective curve, but the proof and the role of constants change.

It is false if one omits the archimedean factors for a number field: $K$ is then dense, so the quotient is not Hausdorff. It is also false for the unrestricted product in the intended locally compact sense, because the infinite noncompact tail destroys local compactness. Both failures confirm that the adelic definition has exactly the right size and topology.

### 6.8 Adelic lattices and finite intersections

The same argument applies to $K^m\subset\mathbf A_K^m$. It is discrete and cocompact, with compact covering set $D^m\times\widehat{\mathcal O}_K^m$. More generally, if $V$ is a finite-dimensional $K$-vector space, then $V(K)$ is a discrete cocompact subgroup of $V(\mathbf A_K)$. Choose a basis to reduce to the previous statement; independence of the topology from the basis was established in Section 4.7.

A useful finiteness consequence is that every compact subset $C\subset V(\mathbf A_K)$ meets $V(K)$ in finitely many points. Discreteness alone makes the intersection discrete, and compactness makes an infinite discrete closed subset impossible here: choose a neighborhood isolating $0$, translate it to isolate every rational point, and cover $C$ by finitely many smaller neighborhoods. Equivalently, after bounding denominators at finitely many primes, the finite coordinates place the rational points in one fractional lattice, and the archimedean compact set meets that lattice finitely.

This is the adelic form of the elementary fact that there are only finitely many algebraic integers with all conjugates bounded. It is often the exact finiteness statement needed in counting arguments: local boundedness at every place becomes membership in a compact adelic set, while globality becomes intersection with the diagonal lattice.

One should distinguish a lattice in this locally compact group sense from an $\mathcal O_K$-lattice in a vector space. The former is a discrete subgroup with finite-volume, here compact, quotient; the latter is a finitely generated module spanning the vector space. The Minkowski embedding and the adelic construction turn the second kind into the first.

## 7. Ideles and their topology

### 7.1 Why nonzero adeles are not enough

Multiplicative arithmetic asks for a group. The group of units $\mathbf A_K^\times$ of the adele ring consists of adeles $x=(x_v)$ for which a coordinatewise inverse is again an adele. This condition says

$$
x_v\in\mathcal O_v^\times
\quad\text{for almost all finite }v.
$$

It is therefore the correct underlying set. But the topology inherited from $\mathbf A_K$ is too coarse, because it controls $x_v$ and not $x_v^{-1}$ at the moving exceptional primes.

For a concrete failure, let $p$ run through the rational primes and define $x^{(p)}\in\mathbf A_{\mathbf Q}^\times$ by taking the $p$-component to be $p$ and every other finite component to be $1$, with infinite component $1$. In the subspace topology from $\mathbf A_{\mathbf Q}$, the net $x^{(p)}$ tends to $1$: outside any fixed finite set, $p-1\in\mathbf Z_p$. But its inverse has $p$-component $p^{-1}$, so inversion would not be continuous. A topological group cannot have this topology.

The remedy is to impose unit behavior, rather than mere integrality, almost everywhere in neighborhoods.

### 7.2 The idele group

The **idele group** is

$$
\mathbf A_K^\times
=\prod_v'(K_v^\times,\mathcal O_v^\times),
$$

where restriction is imposed at finite places only. When ambiguity with ring units is possible, the same group is denoted $\mathbf I_K$.

A basic open set has the form

$$
\prod_{v\in S}U_v\times
\prod_{v\notin S,\,v<\infty}\mathcal O_v^\times,
$$

where $S$ contains the archimedean places and finitely many finite places, and $U_v$ is open in $K_v^\times$. Multiplication and inversion are continuous coordinatewise, so this is a locally compact abelian group. Its finite part is

$$
\mathbf A_{K,f}^\times
=\prod_{v<\infty}'(K_v^\times,\mathcal O_v^\times),
$$

with compact open subgroup

$$
\widehat{\mathcal O}_K^\times=\prod_{v<\infty}\mathcal O_v^\times.
$$

There is a useful intrinsic realization:

$$
\mathbf A_K^\times\longrightarrow\mathbf A_K\times\mathbf A_K,
\qquad
x\longmapsto(x,x^{-1}).
$$

The idele topology is exactly the subspace topology on the image of this graph. Indeed, simultaneous adelic control of $x$ and $x^{-1}$ forces $x_v$ to be a unit outside a fixed finite set. This graph description explains both why the topology is natural and why the naive subspace topology fails.

### 7.3 Additive and multiplicative information

An additive adele records local values with bounded denominators almost everywhere. It supports addition even when some components vanish. An idele forbids zero everywhere and demands valuation zero almost everywhere. It therefore supplies a finitely supported integer vector

$$
(\operatorname{ord}_v(x_v))_{v<\infty}.
$$

This vector is invisible if one retains only the additive topology near zero, but it is exactly the datum from which a fractional ideal is built.

Neither construction contains the other as a topological group in a harmless way. The idele group embeds continuously into the additive adele ring, but the induced topology is coarser. The additive group cannot be recovered by adjoining a zero to the ideles: zeros may occur in arbitrary local coordinates, and addition interacts with them in a way no one-point compactification captures.

### 7.4 Open subgroups and local factorization

At a finite place choose a uniformizer $\pi_v$. Then

$$
K_v^\times=\bigsqcup_{n\in\mathbf Z}\pi_v^n\mathcal O_v^\times.
$$

Every coset is open, so $\operatorname{ord}_v:K_v^\times\to\mathbf Z$ is continuous when $\mathbf Z$ is discrete. Globally, the product of these maps takes values in the direct sum:

$$
\operatorname{ord}_f:\mathbf A_{K,f}^\times
\longrightarrow\bigoplus_{v<\infty}\mathbf Z.
$$

It is continuous, because the inverse image of a specified finitely supported vector is a coset of $\widehat{\mathcal O}_K^\times$. It is surjective: choose local uniformizers at the finitely many desired coordinates. Its kernel is precisely $\widehat{\mathcal O}_K^\times$.

This yields an exact sequence of topological groups

$$
1\longrightarrow\widehat{\mathcal O}_K^\times
\longrightarrow\mathbf A_{K,f}^\times
\longrightarrow\bigoplus_{v<\infty}\mathbf Z
\longrightarrow0.
$$

A simultaneous choice of uniformizers splits it as abstract and topological groups, but the splitting is noncanonical. The quotient is discrete; its compact kernel stores all residue and higher-unit information.

### 7.5 Principal ideles

A nonzero $a\in K$ gives the **principal idele** $(a)_v$. Since $a$ is a local unit almost everywhere, the diagonal map

$$
K^\times\longrightarrow\mathbf A_K^\times
$$

is defined. Its image is discrete. One proof uses the graph embedding and discreteness of $K$ in $\mathbf A_K$: a sufficiently small additive adelic neighborhood of $1$ meets $K^\times$ only in $1$. It is therefore closed.

The finite diagonal $K^\times\subset\mathbf A_{K,f}^\times$ is not dense. Valuation vectors of principal ideles are constrained to be principal divisors, and even within the unit kernel residue conditions can encounter global-unit restrictions. This differs sharply from additive finite approximation.

The quotient

$$
C_K=\mathbf A_K^\times/K^\times
$$

is the **idele class group**. It is locally compact and Hausdorff. It is not compact: a positive real size remains. Identifying and removing that size leads to the central multiplicative compactness theorem.

### 7.6 Convergence of ideles

The topology can be recognized without writing a new basic product each time. A sequence $x^{(n)}$ converges to $x$ in $\mathbf A_K^\times$ if and only if two conditions hold:

1. $x_v^{(n)}\to x_v$ in $K_v^\times$ for every place $v$;
2. there is a finite set $S$ such that, for all sufficiently large $n$ and every finite $v\notin S$, the quotient $x_v^{(n)}x_v^{-1}$ lies in $\mathcal O_v^\times$.

Necessity follows by applying the standard neighborhood with unit tail and then projecting to each coordinate. For sufficiency, a basic neighborhood restricts only finitely many coordinates beyond its unit tail. Enlarge $S$ by those coordinates, use coordinatewise convergence there, and use the second condition elsewhere.

For additive adeles the analogous criterion replaces the quotient by the difference $x_v^{(n)}-x_v\in\mathcal O_v$. This makes the discrepancy in Section 7.1 transparent. The moving-prime sequence $x^{(p)}$ has additive differences $p-1\in\mathbf Z_p$ and so converges additively; its multiplicative quotient at the moving prime is $p$, not a unit, so it does not converge idelically.

The graph realization also proves that the underlying set of ideles is precisely the unit group of the adele ring. If $x$ is a ring unit, both $x$ and $x^{-1}$ are adeles, so $x_v$ and $x_v^{-1}$ are integral almost everywhere; hence $x_v$ is a local unit almost everywhere. The converse is immediate. What changes is not the set but the topology: the unit-group topology is the graph topology that makes inversion continuous.

## 8. Ideals inside ideles

### 8.1 From local valuations to a fractional ideal

Define

$$
\mathfrak a(x)=\prod_{v=\mathfrak p<\infty}
\mathfrak p^{\operatorname{ord}_v(x_v)}
$$

for $x\in\mathbf A_{K,f}^\times$. The product is finite because $x_v$ is a unit almost everywhere. This is a surjective homomorphism

$$
\mathfrak a:\mathbf A_{K,f}^\times\longrightarrow I_K
$$

whose kernel is $\widehat{\mathcal O}_K^\times$. We give $I_K$ the discrete topology; then the map is continuous and open.

The sign convention is chosen so that a principal finite idele satisfies

$$
\mathfrak a((a)_v)=(a).
$$

Some sources insert a minus sign so that an idele acts on a lattice by inverse scaling. Both conventions are legitimate, but formulas for ideal norms must follow the choice.

Surjectivity does not assert that every ideal is principal. Given $\prod\mathfrak p^{n_{\mathfrak p}}$, choose $x_{\mathfrak p}=\pi_{\mathfrak p}^{n_{\mathfrak p}}$ at its finite support and $1$ elsewhere. The components need not arise from one global element; that is precisely why ideles see nonprincipal ideals.

### 8.2 Recovering the ideal class group

Archimedean ideles carry no ideal valuation. Extend $\mathfrak a$ by ignoring them. Since principal ideles map to principal ideals, it induces a surjection

$$
C_K\longrightarrow\operatorname{Cl}(K).
$$

Its kernel is represented by ideles whose associated ideal is principal. Dividing by a principal idele makes every finite component a unit. Consequently there is an exact sequence

$$
1\longrightarrow
\frac{K_\infty^\times\widehat{\mathcal O}_K^\times}{\mathcal O_K^\times}
\longrightarrow C_K
\longrightarrow\operatorname{Cl}(K)
\longrightarrow1,
$$

where $\mathcal O_K^\times$ is embedded diagonally in the numerator. Equivalently,

$$
C_K/(K_\infty^\times\widehat{\mathcal O}_K^\times)
\cong\operatorname{Cl}(K).
$$

In the first display, the numerator notation means the product group $K_\infty^\times\times\widehat{\mathcal O}_K^\times$ modulo the diagonal global units; there is no unintended identification between the two factors.

Thus the ideal class group is the coarsest discrete quotient of the idele class group obtained by discarding all archimedean magnitude and all local unit data. Ideles refine ideals in two directions: archimedean components retain continuous geometry, while finite units retain congruence information.

### 8.3 Finiteness revisited topologically

The ideal-class map has open kernel because $K_\infty^\times\widehat{\mathcal O}_K^\times$ is open in $\mathbf A_K^\times$. Hence $\operatorname{Cl}(K)$ is a discrete quotient of $C_K$. Theorem 1.1 says this quotient is finite.

Conversely, once the compactness of the norm-one idele class group is proved, ideal-class finiteness follows immediately: a discrete continuous image of a compact group is finite. To make that argument, restrict the ideal-class map to the norm-one part and note that every ideal class has a representative there after adjusting one archimedean coordinate. This gives an adelic proof of the same finiteness theorem. We retained the geometry-of-numbers proof earlier because it also supplies the global setup used in the compactness argument.

### 8.4 Lattices and finite ideles

A finite idele acts on $K$ through local integrality conditions. Define

$$
L(x)=\{a\in K:a x_v\in\mathcal O_v\text{ for every }v<\infty\}.
$$

Then

$$
L(x)=\mathfrak a(x)^{-1}.
$$

Indeed, the condition is $\operatorname{ord}_v(a)+\operatorname{ord}_v(x_v)\geq0$ at each prime. Multiplying $x$ by a finite unit does not change this lattice. Thus

$$
\mathbf A_{K,f}^\times/\widehat{\mathcal O}_K^\times\cong I_K
$$

may be read as a classification of rank-one fractional $\mathcal O_K$-lattices inside $K$. Dividing further by $K^\times$ identifies homothetic lattices and produces the ideal class group.

### 8.5 What ideals forget

At a prime $\mathfrak p$, the ideal map remembers $\operatorname{ord}_{\mathfrak p}(x_{\mathfrak p})$ but forgets the residue of its unit part. For instance, in $\mathbf Q_p^\times$, the numbers $1$ and $2$ define the same local ideal when $p\ne2$, yet they need not be congruent modulo $p^m$. Ray class groups restore a controlled finite portion of precisely this forgotten data.

At infinity, ideals forget everything. Signs at real places and arguments at complex places disappear. Narrow ideal classes restore real signs; continuous idele characters can also detect complex arguments. This hierarchy explains why ordinary ideal classes suffice for elementary factorization but not for the full language of abelian extensions or automorphic characters.

### 8.6 Ordinary and narrow ideal classes

A principal ideal does not remember which generator was used. If $K$ has real embeddings, however, positivity of a generator can be meaningful. Let $P_K^+$ be the subgroup of principal ideals $(a)$ admitting a generator $a$ that is positive at every real place. The **narrow class group** is

$$
\operatorname{Cl}^+(K)=I_K/P_K^+.
$$

It maps onto $\operatorname{Cl}(K)$. The kernel measures sign patterns not realized by global units. More explicitly, the sign map gives an exact sequence

$$
\mathcal O_K^\times\longrightarrow\{\pm1\}^{r_1}
\longrightarrow\operatorname{Cl}^+(K)
\longrightarrow\operatorname{Cl}(K)\longrightarrow1.
$$

At the idele level, replace each real factor $\mathbf R^\times$ in the subgroup discarded for ordinary classes by $\mathbf R_{>0}$. The quotient retains the signs and produces $\operatorname{Cl}^+(K)$. If there is a unit realizing every sign obstruction needed to change a generator into a totally positive one, ordinary and narrow classes agree. A unit of norm $-1$ is enough in a real quadratic field; in higher degree the full sign image, not merely the norm, must be examined.

This is the first instance of an infinite part of a modulus. It is discrete data arising from a connected-component quotient at the real places, not from an additional valuation.

### 8.7 The divisor sequence in one view

The finite valuation map, the ideal map, and passage to classes fit into the commutative diagram

$$
\begin{array}{ccccccccc}
1&\to&\widehat{\mathcal O}_K^\times&\to&\mathbf A_{K,f}^\times
&\xrightarrow{\mathfrak a}&I_K&\to&1\\
&&\cup&&\cup&&\cup\\
1&\to&\mathcal O_K^\times&\to&K^\times
&\xrightarrow{(\cdot)}&P_K&\to&1.
\end{array}
$$

The bottom row is exact at $K^\times$ and $P_K$; its left kernel statement says that a global number generates the unit ideal exactly when it is a global unit. Taking the quotient of the top row by the bottom one produces the ideal class group together with the archimedean and finite-unit kernel described in Section 8.2.

In divisor language, $\bigoplus_{v<\infty}\mathbf Z$ is the group of finite divisors, the vector $(\operatorname{ord}_v(a))$ is a principal divisor, and $\operatorname{Cl}(K)$ is the divisor class group. The idele is richer than its divisor because it retains a unit at each coordinate. Passing from ideles to divisors is therefore a valuation, not an isomorphism.

One can add archimedean real coefficients $-\log|x_v|_v$ and regard the product formula as saying that a principal extended divisor has total degree zero. This viewpoint anticipates a useful geometric language, but no new quotient is needed for our purposes: the idele module already records the total degree continuously.

## 9. The idele module and compactness

### 9.1 The global module

For an idele $x=(x_v)$ define its **module** or **idele norm** by

$$
|x|_{\mathbf A}=\prod_v|x_v|_v\in\mathbf R_{>0}.
$$

The product is finite: at almost every finite place $x_v\in\mathcal O_v^\times$, so $|x_v|_v=1$, and there are only finitely many archimedean places. It is a continuous surjective homomorphism

$$
|\cdot|_{\mathbf A}:\mathbf A_K^\times\longrightarrow\mathbf R_{>0}.
$$

Continuity follows because on a restricted-product stage only finitely many factors vary outside groups on which the absolute value is $1$. Surjectivity follows by varying one real absolute value; if $K$ is totally imaginary, vary the ordinary modulus at one complex place, whose normalized value ranges over all positive reals.

The **unit ideles** or **norm-one ideles** form

$$
\mathbf A_K^1=\ker|\cdot|_{\mathbf A}.
$$

This phrase must not be confused with the finite unit ideles $\widehat{\mathcal O}_K^\times$. A norm-one idele may have nonzero valuations at several finite primes, balanced by other finite or infinite magnitudes.

By the product formula, $K^\times\subset\mathbf A_K^1$. Hence the module descends to

$$
|\cdot|:C_K\longrightarrow\mathbf R_{>0},
$$

with kernel

$$
C_K^1=\mathbf A_K^1/K^\times.
$$

### 9.2 Dirichlet's unit lattice

Compactness of $C_K^1$ is the multiplicative counterpart of compactness of $\mathbf A_K/K$. Its archimedean ingredient is Dirichlet's unit theorem.

Define the logarithmic map

$$
\lambda:K_\infty^\times\longrightarrow\mathbf R^{r_1+r_2},
\qquad
(x_v)\longmapsto(\log|x_v|_v)_v.
$$

For a global unit $u$, the finite absolute values are all $1$, so the product formula places $\lambda(u)$ in the hyperplane

$$
H=\left\{(t_v):\sum_{v\mid\infty}t_v=0\right\}.
$$

**Theorem 9.1 (Dirichlet unit theorem).** The kernel of $\lambda:\mathcal O_K^\times\to H$ is the finite group $\mu(K)$ of roots of unity in $K$, and its image is a full lattice in $H$. Consequently

$$
\mathcal O_K^\times\cong\mu(K)\times\mathbf Z^{r_1+r_2-1}
$$

noncanonically.

**Proof strategy.** Bounded logarithms give discreteness. For cocompactness, build for every point $t\in H$ an algebraic integer whose logarithmic vector stays a uniformly bounded distance from $t$. Only finitely many principal ideals can arise; dividing by fixed generators then produces a unit uniformly close to $t$.

**Proof.** If $\lambda(u)=0$, every conjugate of $u$ has modulus $1$. The coefficients of the monic minimal polynomial of $u^m$ are bounded independently of $m$, because they are elementary symmetric functions of conjugates of modulus $1$. Only finitely many such integral polynomials exist, so two powers of $u$ agree and $u$ is a root of unity. Conversely every root of unity lies in the kernel.

If $\lambda(u)$ ranges over a bounded set, every archimedean conjugate of $u$ lies in a fixed bounded subset of $K_\infty$. The lattice $\mathcal O_K$ has only finitely many points there. Hence the inverse image of a bounded subset under $\lambda|_{\mathcal O_K^\times}$ is finite, and $\lambda(\mathcal O_K^\times)$ is discrete.

We now prove relative density. For $t=(t_v)\in H$, consider the symmetric convex body $B(t)\subset K_\infty$ given by

$$
|x_v|_{\mathrm{usual}}\leq C e^{t_v}
\quad(v\text{ real}),
$$

and

$$
|x_v|_{\mathrm{usual}}\leq C e^{t_v/2}
\quad(v\text{ complex}).
$$

Its Euclidean volume is a constant multiple of

$$
C^n\exp\left(\sum_vt_v\right)=C^n,
$$

independent of $t$. Choose $C$ once and for all so that this volume is larger than $2^n$ times the covolume of $\mathcal O_K$. Minkowski's convex-body theorem gives a nonzero $a_t\in\mathcal O_K\cap B(t)$.

There are constants $c_v$, independent of $t$, such that

$$
\lambda(a_t)_v-t_v\leq c_v
$$

at every archimedean place. On the other hand,

$$
\sum_v\lambda(a_t)_v
=\log|N_{K/\mathbf Q}(a_t)|.
$$

This is nonnegative because the norm is a nonzero integer, and the coordinatewise upper bounds make it at most $\sum c_v$. Since $\sum t_v=0$, solving for any one coordinate from the sum gives a uniform lower bound as well:

$$
\lambda(a_t)_v-t_v
\geq-\sum_{w\ne v}c_w.
$$

Thus $\lambda(a_t)$ remains within a fixed bounded distance of $t$. The same estimates bound the positive integer $|N_{K/\mathbf Q}(a_t)|$. There are only finitely many integral ideals of bounded norm, so the principal ideals $(a_t)$ belong to a finite list, say $(b_1),\ldots,(b_s)$. For the appropriate $j$, the quotient

$$
u_t=a_t/b_j
$$

is a global unit. Since the finitely many vectors $\lambda(b_j)$ are fixed, $\lambda(u_t)$ remains within a uniform bounded distance of $t$.

We have proved that the discrete subgroup $\lambda(\mathcal O_K^\times)$ is relatively dense in $H$. A discrete relatively dense subgroup of a finite-dimensional real vector space is a full lattice: a compact ball covers a fundamental region, and a maximal linearly independent subset must span the space. It is therefore isomorphic to $\mathbf Z^{\dim H}=\mathbf Z^{r_1+r_2-1}$. Combining this with the finite kernel gives the claimed structure. $\square$

The proof establishes exactly what compactness later needs: every norm-one logarithmic vector can be reduced into one fixed bounded region by a global unit.

### 9.3 Compactness of the norm-one class group

**Theorem 9.2.** The group $C_K^1$ is compact.

**Proof strategy.** Use finitely many ideal-class representatives to reduce all finite valuations to a finite list. The remaining finite-unit part is compact. At infinity, the norm-one logarithms lie in an affine translate of $H$, and global units form a cocompact lattice there. Signs and complex phases contribute only compact factors.

**Proof.** Choose finite ideles $t_1,\ldots,t_h$ whose associated ideals represent all classes in $\operatorname{Cl}(K)$. Let $x\in\mathbf A_K^1$. For some $i$, the ideal $\mathfrak a(x_f)\mathfrak a(t_i)^{-1}$ is principal, say $(a)$. Dividing $x$ by the principal idele $a$ makes its finite valuation vector equal to that of $t_i$. It can therefore be written

$$
x=a\,t_i\,u_f\,x_\infty
$$

with $u_f\in\widehat{\mathcal O}_K^\times$ and $x_\infty\in K_\infty^\times$; here factors are understood in their finite or infinite coordinates.

For fixed $i$, the norm-one condition imposes

$$
\sum_{v\mid\infty}\log|x_v|_v=-\log|t_i|_{\mathbf A}.
$$

Thus $\lambda(x_\infty)$ lies in an affine hyperplane parallel to $H$. Translation identifies it with $H$. Modulo $\lambda(\mathcal O_K^\times)$, this hyperplane has a compact fundamental parallelotope by Dirichlet's theorem. The kernel of $\lambda$ on $K_\infty^\times$ is

$$
\{\pm1\}^{r_1}\times(S^1)^{r_2},
$$

a compact group. Hence a compact subset of $K_\infty^\times$ meets every orbit of $\mathcal O_K^\times$ subject to the displayed norm constraint.

The finite-unit factor $\widehat{\mathcal O}_K^\times$ is compact. Multiplying its compact set by the compact archimedean representatives and by the finite list $t_i$ gives a compact subset of $\mathbf A_K^1$ whose image covers $C_K^1$. Therefore $C_K^1$ is compact. $\square$

Unlike $\mathbf A_K/K$, the quotient $C_K^1$ is generally not connected: finite units contribute profinite structure, and ideal classes contribute finitely many components.

### 9.4 Structure of the full idele class group

There is an exact sequence

$$
1\longrightarrow C_K^1\longrightarrow C_K
\xrightarrow{|\cdot|}\mathbf R_{>0}\longrightarrow1.
$$

It admits a continuous splitting after choosing an archimedean place. At a real place send $t$ to the idele with component $t$ there and $1$ elsewhere. At a complex place choose a positive real component $\sqrt t$, whose normalized absolute value is $t$. Thus, noncanonically,

$$
C_K\cong C_K^1\times\mathbf R_{>0}.
$$

The exact sequence is canonical; the splitting is not. It isolates the sole noncompact direction of the idele class group. In logarithmic coordinates this direction is the sum of all local logarithmic sizes, while the product formula kills it on principal ideles.

### 9.5 The compact kernel over the ideal class group

The ideal-class map restricts to a surjection

$$
C_K^1\longrightarrow\operatorname{Cl}(K).
$$

Surjectivity follows by representing an ideal class with a finite idele and then changing one archimedean component to make the total module $1$. Its kernel has a particularly concrete description. Put

$$
K_\infty^1=
\left\{x_\infty\in K_\infty^\times:
\prod_{v\mid\infty}|x_v|_v=1\right\}.
$$

Then there is an exact sequence

$$
1\longrightarrow
\frac{K_\infty^1\times\widehat{\mathcal O}_K^\times}
{\mathcal O_K^\times}
\longrightarrow C_K^1
\longrightarrow\operatorname{Cl}(K)
\longrightarrow1.
$$

The global unit acts diagonally on the two numerator factors. The left group is compact. Its finite factor is compact; the kernel of the archimedean logarithm is compact; and the remaining logarithmic hyperplane becomes compact modulo the Dirichlet unit lattice. Thus $C_K^1$ is assembled from a connected archimedean torus-like part, a profinite local-unit part, and finitely many ideal classes, with global units gluing the first two.

The description is structural rather than a canonical direct product. Choosing ideal representatives splits the finite set only noncanonically, and choosing fundamental units splits the logarithmic lattice only after choices. The exact sequence retains all canonical information without pretending those choices are natural.

### 9.6 Compactness criteria and finite quotients

Because $C_K^1$ is compact, every continuous homomorphism from it to a discrete group has finite image. This simple observation contains several arithmetic finiteness results. The ideal class group is one. Ray class groups will be another.

The full $C_K$ is never compact for a number field because it surjects onto $\mathbf R_{>0}$. Quotienting only by $K^\times\widehat{\mathcal O}_K^\times$ also leaves the full archimedean magnitude. Any claim that “the idele class group is compact” must therefore include the norm-one condition or a quotient by an appropriate archimedean positive subgroup.

### 9.7 The module as a Haar modulus

The name “module” has a measure-theoretic meaning. Fix additive Haar measure $da$ on $\mathbf A_K$. Multiplication by an idele $x$ is an additive automorphism. Coordinatewise change of variables and the normalization $\mu_v(\mathcal O_v)=1$ give

$$
d(xa)=|x|_{\mathbf A}\,da.
$$

Only finitely many local scaling factors differ from $1$, so no convergence issue occurs. Thus $\mathbf A_K^1$ is exactly the subgroup of ideles acting by volume-preserving additive transformations.

For a principal idele $a\in K^\times$, multiplication carries the lattice $K\subset\mathbf A_K$ to itself. It must preserve the covolume of that lattice, and the product formula says exactly that its scaling factor is $1$. This gives a geometric interpretation of a formula previously proved by ideal norms.

Multiplicative Haar measure is different. Locally it is a scalar multiple of $da_v/|a_v|_v$, and on the restricted product it is normalized so that $\mathcal O_v^\times$ has measure $1$ almost everywhere. We need no global volume computation with this measure; its role here is only to emphasize that additive and multiplicative invariant measures follow the same normalization conventions.

## 10. Norms across extensions

### 10.1 The local norm as a multiplicative determinant

For a finite extension of local fields $E/F$, multiplication by $y\in E$ is an $F$-linear endomorphism of $E$. Its determinant is the field norm $N_{E/F}(y)$. This definition gives

$$
N_{E/F}(yz)=N_{E/F}(y)N_{E/F}(z),
$$

and in a tower $E/F/F_0$,

$$
N_{E/F_0}=N_{F/F_0}\circ N_{E/F}.
$$

For finite nonarchimedean extensions, norms carry $\mathcal O_E$ into $\mathcal O_F$ and $\mathcal O_E^\times$ into $\mathcal O_F^\times$. The latter assertion follows either from determinants on integral lattices or from

$$
\operatorname{ord}_F(N_{E/F}y)=f(E/F)\operatorname{ord}_E(y).
$$

The norm on $E^\times$ is continuous. Its image is not generally all of $F^\times$. Already for $\mathbf C/\mathbf R$, the norm image is $\mathbf R_{>0}$, excluding negative numbers. At a nonarchimedean unramified extension of degree $d$, valuation of a norm is divisible by $d$, although the norm on unit groups is surjective when the residue extension is finite. These are local obstructions that any global norm must satisfy.

### 10.2 The adelic norm

Let $L/K$ be a finite extension. For $y=(y_w)\in\mathbf A_L^\times$, define its $v$-component by

$$
(N_{L/K}^{\mathbf A}y)_v
=\prod_{w\mid v}N_{L_w/K_v}(y_w).
$$

There are finitely many $w$ over each $v$. Almost every $y_w$ is a unit, and local norms carry units to units, so these components form an idele. Restricted-product functoriality proves that

$$
N_{L/K}^{\mathbf A}:\mathbf A_L^\times\longrightarrow\mathbf A_K^\times
$$

is a continuous homomorphism. We usually omit the superscript.

The local normalization of Section 2.5 gives the exact module identity

$$
|N_{L/K}^{\mathbf A}y|_{\mathbf A_K}
=\prod_v\prod_{w\mid v}|y_w|_w
=|y|_{\mathbf A_L}.
$$

Thus adelic norms preserve the module, rather than raising it to the extension degree. This statement concerns the norm map. A different map, scalar extension of an idele $x\in\mathbf A_K^\times$ to all $L_w$, satisfies

$$
|x\text{ viewed over }L|_{\mathbf A_L}
=|x|_{\mathbf A_K}^{[L:K]}.
$$

Confusing norm with scalar extension is another common source of erroneous exponents.

### 10.3 Compatibility with principal ideles

If $a\in L^\times$ is embedded diagonally, then the local determinant decompositions imply

$$
N_{L/K}^{\mathbf A}((a)_w)=(N_{L/K}(a))_v.
$$

Hence the adelic norm carries principal ideles to principal ideles and descends to a continuous map

$$
N_{L/K}:C_L\longrightarrow C_K.
$$

It also carries $C_L^1$ into $C_K^1$ by module compatibility. Norms are transitive on ideles and on idele classes because they are transitive at each local factor.

On associated ideals, the convention of Chapter 8 gives

$$
\mathfrak a(N_{L/K}y)=N_{L/K}(\mathfrak a(y)),
$$

where the ideal norm sends a prime $\mathfrak P$ over $\mathfrak p$ to $\mathfrak p^{f(\mathfrak P/\mathfrak p)}$. Indeed, both sides have $\mathfrak p$-valuation

$$
\sum_{\mathfrak P\mid\mathfrak p}
f(\mathfrak P/\mathfrak p)\operatorname{ord}_{\mathfrak P}(y_{\mathfrak P}).
$$

The adelic norm therefore refines both the field norm and the ideal norm and makes their compatibility tautological.

### 10.4 Local conditions versus a global norm

Suppose $b\in K^\times$ is a global norm from $L^\times$. Then $b$ is a norm from $L_w$ after passing to every completion and multiplying over $w\mid v$. Thus local norm conditions are necessary.

They are not sufficient in arbitrary extensions. The assertion

$$
b\in N_{L/K}(L^\times)
\quad\Longleftrightarrow\quad
b\in N_{L\otimes_KK_v/K_v}((L\otimes_KK_v)^\times)
\text{ for every }v
$$

is a local--global norm principle, not a formal consequence of adelic language. It holds under important additional hypotheses, most famously for cyclic extensions, but fails for general noncyclic extensions. Proving such theorems belongs to global class field theory and its cohomological consequences, not to the construction developed here.

The safe adelic statement is instead that the local norm conditions describe membership of the diagonal idele $(b)_v$ in the subgroup $N_{L/K}(\mathbf A_L^\times)$. Whether this adelic membership lifts to one element of $L^\times$ is a separate global question.

### 10.5 Examples of norm behavior

For $\mathbf C/\mathbf R$, $N(z)=|z|^2$, so a negative real number is never a local norm. Consequently, if a real place of $K$ becomes complex in $L$, every global norm from $L$ is positive at that place.

For an unramified extension $E/F$ of nonarchimedean local fields of degree $d$, the valuation formula shows

$$
N(E^\times)=\pi_F^{d\mathbf Z}\mathcal O_F^\times.
$$

Surjectivity on units can be seen first in the finite residue fields, where the norm is surjective, and then on successive principal-unit quotients, followed by completeness. The missing valuation classes form a cyclic quotient of order $d$.

For a totally ramified extension, the valuation of a norm is unrestricted because $f=1$, while the unit norm may be a proper subgroup. Thus unramified and ramified extensions place their most visible norm obstruction in different parts of $F^\times=\pi_F^{\mathbf Z}\mathcal O_F^\times$.

For $L=\mathbf Q(i)$ over $\mathbf Q$, the infinite norm condition is positivity. The rational number $3$ is positive but is not a norm of a Gaussian rational: in an equality $3=a^2+b^2$ with $a,b\in\mathbf Q$, clearing denominators and using the prime $3\equiv3\pmod4$ yields a parity contradiction in its exponent. Its failure is also visible locally at $3$. This example illustrates agreement of local and global obstruction without suggesting that such agreement is automatic in every extension.

### 10.6 Norms and congruence depth

Norm maps respect sufficiently deep unit neighborhoods, but ramification prevents a universal depth-free formula. Continuity of

$$
N_{L_w/K_v}:L_w^\times\longrightarrow K_v^\times
$$

at $1$ says that for every $n\geq1$ there exists $m\geq1$ such that

$$
N_{L_w/K_v}(1+\mathfrak p_w^m)
\subseteq1+\mathfrak p_v^n.
$$

One can see this algebraically by expanding the determinant of multiplication by $1+z$:

$$
N(1+z)=1+\operatorname{Tr}(z)+\text{terms of degree at least }2.
$$

As $\operatorname{ord}_w(z)$ grows, every nonconstant term acquires arbitrarily large $v$-valuation. The different controls the sharp relation between $m$ and $n$; no sharp formula is needed here.

Globally, only finitely many places occur in a chosen modulus, so one may choose compatible depths place by place. It follows that for every modulus $\mathfrak m$ of $K$ there is a modulus $\mathfrak n$ of $L$ such that

$$
N_{L/K}(U_L(\mathfrak n))\subseteq U_K(\mathfrak m).
$$

At real places, include the appropriate positivity conditions; a complex norm into a real place is automatically positive. Hence the norm induces a map between the corresponding ray quotients after sufficiently deep source level is chosen.

This existence statement is deliberately asymmetric. It does not claim that the norm is surjective on ray groups, nor that the same exponent works through ramified extensions. Such sharper assertions depend on detailed local ramification and, globally, on reciprocity.

## 11. Congruence subgroups and ray classes

### 11.1 Why ideals need local unit data

Ordinary ideal classes identify two ideals when their ratio is generated by any $a\in K^\times$. To study congruence, one should restrict the allowed generators: require $a$ to be close to $1$ at selected finite primes and positive at selected real places. Ideles make this uniform. A congruence becomes membership in an open local unit subgroup, and all unmentioned places retain their full unit groups.

A **modulus** is a formal product

$$
\mathfrak m=\mathfrak m_0\mathfrak m_\infty,
\qquad
\mathfrak m_0=\prod_{\mathfrak p}\mathfrak p^{n_{\mathfrak p}},
$$

where $n_{\mathfrak p}\geq0$ and only finitely many are positive, while $\mathfrak m_\infty$ is a set of real places. Complex places do not occur in the infinite part because $\mathbf C^\times$ is connected and has no sign quotient.

### 11.2 Local congruence groups

For a finite prime define

$$
U_{\mathfrak p}^{(0)}=\mathcal O_{\mathfrak p}^\times,
\qquad
U_{\mathfrak p}^{(n)}=1+\mathfrak p_{\mathfrak p}^n\quad(n\geq1).
$$

At a real place in $\mathfrak m_\infty$, use $\mathbf R_{>0}$; at every other archimedean place use all of $K_v^\times$. Set

$$
U(\mathfrak m)=
\prod_{\mathfrak p\mid\mathfrak m_0}U_{\mathfrak p}^{(n_{\mathfrak p})}
\times
\prod_{\mathfrak p\nmid\mathfrak m_0}\mathcal O_{\mathfrak p}^\times
\times
\prod_{v\in\mathfrak m_\infty}\mathbf R_{>0}
\times
\prod_{v\mid\infty,\,v\notin\mathfrak m_\infty}K_v^\times.
$$

This is an open subgroup of $\mathbf A_K^\times$. Its finite part is compact open. The full group need not be compact because its archimedean factors are not, but those factors deliberately remove continuous magnitude while retaining the requested signs.

The **ray class group modulo $\mathfrak m$** is

$$
\operatorname{Cl}_{\mathfrak m}(K)
=\mathbf A_K^\times/K^\times U(\mathfrak m).
$$

For the trivial modulus this is the ordinary ideal class group. If every real place occurs with exponent one at infinity and $\mathfrak m_0=(1)$, it is the narrow class group.

### 11.3 The ideal-theoretic description

Let $I_K(\mathfrak m_0)$ be the group of fractional ideals prime to $\mathfrak m_0$. Let $P_{K,1}(\mathfrak m)$ consist of principal ideals $(a)$ for which

$$
a\equiv1\pmod{\mathfrak p^{n_{\mathfrak p}}}
\quad\text{for every }\mathfrak p\mid\mathfrak m_0,
$$

interpreted after requiring $a$ to be a local unit there, and $a$ is positive at every $v\in\mathfrak m_\infty$. Then

$$
\operatorname{Cl}_{\mathfrak m}(K)
\cong I_K(\mathfrak m_0)/P_{K,1}(\mathfrak m).
$$

**Proof strategy.** Move all valuations at primes dividing the modulus to zero by a principal idele, then apply the ideal map. The ambiguity in this adjustment is exactly a ray-principal ideal.

**Proof.** Given an idele $x$, finite approximation supplies $a\in K^\times$ such that $ax$ is a unit at every prime dividing $\mathfrak m_0$. The ideal $\mathfrak a(ax)$ is then prime to $\mathfrak m_0$. Changing $x$ by an element of $U(\mathfrak m)$ does not change this ideal. Changing it by a principal idele changes the ideal by a principal factor whose generator, after comparing the two local normalizations, is congruent to $1$ at the finite modulus and positive at the specified real places. This defines the map to the ideal quotient.

Conversely, represent an ideal prime to $\mathfrak m_0$ by local uniformizer powers away from the modulus and by $1$ at its primes. This constructs an idele. Two such representatives have the same idele class precisely when their quotient is generated by an element satisfying the ray conditions. The constructions are inverse. $\square$

This proof also explains why one cannot simply apply the ideal map to an arbitrary idele and demand an ideal prime to $\mathfrak m_0$: the idele may have nonzero valuation at a modulus prime. A preliminary principal adjustment is essential.

### 11.4 Finiteness of ray class groups

**Theorem 11.1.** For every modulus $\mathfrak m$, the ray class group $\operatorname{Cl}_{\mathfrak m}(K)$ is finite.

**First proof.** There is an exact sequence of finite-index type

$$
\mathcal O_K^\times\longrightarrow
(\mathcal O_K/\mathfrak m_0)^\times
\times\{\pm1\}^{\mathfrak m_\infty}
\longrightarrow\operatorname{Cl}_{\mathfrak m}(K)
\longrightarrow\operatorname{Cl}(K)\longrightarrow1.
$$

The first map records residues and signs, and exactness at the ray class group says that a ray class with trivial ordinary ideal class is represented by a principal ideal, with only its residue and sign obstruction remaining. The middle finite group and the ordinary class group are finite, so the ray class group is finite. The displayed sequence may have a kernel at the left; no injectivity is claimed.

**Second proof.** Every coset modulo $U(\mathfrak m)$ has a norm-one representative, because an allowed archimedean positive coordinate can adjust its module. Therefore the ray class group is a quotient of $C_K^1$. Its defining subgroup is open, so the quotient is discrete. A discrete quotient of the compact group $C_K^1$ is finite. $\square$

The second proof displays ray finiteness as a structural consequence of multiplicative compactness; the first makes the finite residue and sign information explicit.

### 11.5 Open compact subgroups

The groups

$$
U_f(\mathfrak m_0)=
\prod_{\mathfrak p\mid\mathfrak m_0}U_{\mathfrak p}^{(n_{\mathfrak p})}
\times\prod_{\mathfrak p\nmid\mathfrak m_0}\mathcal O_{\mathfrak p}^\times
$$

are compact open subgroups of $\mathbf A_{K,f}^\times$ and form a cofinal neighborhood system among subgroups of $\widehat{\mathcal O}_K^\times$. More general compact open subgroups may impose arbitrary open subgroups at finitely many primes, not only principal-unit depth. Every compact open subgroup is contained in a restricted-product stage, and after enlarging a finite exceptional set its tail is the full $\mathcal O_v^\times$.

The additive analogues are products of local fractional ideals, with $\mathcal O_v$ at almost all places. This comparison is instructive: additive depth uses $\mathfrak p_v^n$, while multiplicative depth near $1$ uses $1+\mathfrak p_v^n$. The translation by $1$ is not a group isomorphism, but successive quotients make the two filtrations closely related.

In the full idele group, no subgroup containing an open archimedean neighborhood can be compact when it includes a noncompact magnitude direction. One usually separates a maximal compact archimedean factor,

$$
\{\pm1\}^{r_1}\times(S^1)^{r_2},
$$

from the positive real logarithmic directions.

### 11.6 Conductors at the elementary level

Let $\chi:C_K\to\mathbf C^\times$ be a continuous character of finite order. Its restriction to each finite local unit group has open kernel, so there is a least $n_{\mathfrak p}\geq0$ such that

$$
\chi|_{U_{\mathfrak p}^{(n_{\mathfrak p})}}=1.
$$

Continuity in the restricted product implies $n_{\mathfrak p}=0$ for almost every $\mathfrak p$. At a real place, a finite-order continuous character can only detect the sign; record that place in $\mathfrak m_\infty$ precisely when the sign character occurs. At a complex place every finite-order continuous character is trivial because $\mathbf C^\times$ is connected.

The resulting modulus

$$
\mathfrak f(\chi)=
\prod_{\mathfrak p}\mathfrak p^{n_{\mathfrak p}}
\prod_{v\in\mathfrak m_\infty}v
$$

is the **conductor** of $\chi$. It is the least modulus, ordered by divisibility and inclusion of real places, for which $\chi$ factors through $\operatorname{Cl}_{\mathfrak m}(K)$. Conversely every character of a ray class group gives a finite-order idele class character with conductor dividing $\mathfrak m$.

This is the elementary content of conductors: they measure the smallest local unit neighborhoods on which a global character becomes trivial. No reciprocity map has been defined, and no identification with Galois groups is asserted here.

### 11.7 Computing elementary ray quotients

For $K=\mathbf Q$ and modulus $N\infty$, every ideal prime to $N$ has a unique positive generator up to multiplication by a positive rational congruent to $1$ modulo $N$. Sending that generator to its residue gives

$$
\operatorname{Cl}_{N\infty}(\mathbf Q)
\cong(\mathbf Z/N\mathbf Z)^\times.
$$

For $N=5$, the four classes are represented by $1,2,3,4$. Their characters include the quadratic character distinguishing squares $1,4$ from nonsquares $2,3$; its finite conductor is $5$. If the infinite place is omitted, generators differing by $-1$ are allowed, and the quotient is $(\mathbf Z/N\mathbf Z)^\times/\{\pm1\}$.

Over a general field, computation separates into three finite tasks: determine ordinary ideal classes, compute $(\mathcal O_K/\mathfrak m_0)^\times$, and determine the image of global units together with their real signs. The exact sequence in Section 11.4 then assembles the answer. This is substantially more efficient than attempting to list ideles: the compact open subgroup has already discarded the infinite irrelevant tail.

Increasing an exponent $n_{\mathfrak p}$ replaces $U_{\mathfrak p}^{(n)}$ by a smaller subgroup and produces a surjection from the finer ray class group to the coarser one. Its kernel is controlled by the finite quotient

$$
U_{\mathfrak p}^{(n)}/U_{\mathfrak p}^{(n+1)},
$$

which is an additive copy of the residue field for $n\geq1$ through $1+x\mapsto x$. Thus ray towers reveal one finite layer of the local unit filtration at a time.

## 12. Explicit adelic portraits

### 12.1 The rational field

For $K=\mathbf Q$ there is one real place and one finite place for each prime:

$$
\mathbf A_{\mathbf Q}=\mathbf R\times\prod_p'(\mathbf Q_p,\mathbf Z_p),
\qquad
\mathbf A_{\mathbf Q}^\times
=\mathbf R^\times\times\prod_p'(\mathbf Q_p^\times,\mathbf Z_p^\times).
$$

The additive quotient is covered by $[0,1]\times\widehat{\mathbf Z}$. For ideles, multiply by a positive rational number to cancel every finite valuation, then by $-1$ if necessary to make the real component positive. The resulting representative lies uniquely in

$$
\mathbf R_{>0}\times\widehat{\mathbf Z}^{\times}.
$$

Indeed, a rational number that is a unit at every finite prime is $\pm1$, and positivity removes the remaining ambiguity. Thus

$$
C_{\mathbf Q}\cong\mathbf R_{>0}\times\widehat{\mathbf Z}^{\times},
\qquad
C_{\mathbf Q}^1\cong\widehat{\mathbf Z}^{\times}.
$$

This concrete isomorphism is special: the class number is one and the global unit group is only $\{\pm1\}$.

The representative can be computed directly. For an idele $x$, put

$$
q=\prod_p p^{v_p(x_p)}\in\mathbf Q_{>0}.
$$

This is a finite product. Dividing by the principal idele $q$ makes every finite component a $p$-adic unit. If the real component becomes negative, divide once more by $-1$. The resulting positive real coordinate is

$$
\frac{|x_\infty|}{q}=|x|_{\mathbf A},
$$

while the finite coordinates give an element of $\widehat{\mathbf Z}^\times$. Thus the first coordinate of the displayed decomposition is canonically the idele module, even though the normalization process used principal representatives.

For the modulus $N\infty$, where the real place is included, the ray class group is

$$
\operatorname{Cl}_{N\infty}(\mathbf Q)\cong(\mathbf Z/N\mathbf Z)^\times.
$$

The positivity condition chooses a positive generator, and its residue modulo $N$ is the remaining invariant. Without the infinite place, one further identifies residues differing by $-1$.

### 12.2 The Gaussian field

Let $K=\mathbf Q(i)$. There is one complex place and no real place, so

$$
K_\infty^\times=\mathbf C^\times.
$$

The normalized absolute value is $|z|^2$. The unit group $\mathcal O_K^\times=\{\pm1,\pm i\}$ has rank zero, in agreement with $r_1+r_2-1=0$. Since $\mathbf Z[i]$ has class number one, every idele class has a representative with finite part in $\widehat{\mathbf Z[i]}^\times$. Its norm-one archimedean component lies on $S^1$. Consequently $C_K^1$ is a compact quotient built from

$$
S^1\times\widehat{\mathbf Z[i]}^\times
$$

by the diagonal four-element unit group.

Prime behavior is visible coordinatewise. A rational prime $p\equiv1\pmod4$ splits into two places of $K$, $p\equiv3\pmod4$ remains prime, and $2$ ramifies. Accordingly,

$$
K\otimes_{\mathbf Q}\mathbf Q_p
$$

is $\mathbf Q_p\times\mathbf Q_p$ in the split case and a quadratic field in the inert or ramified case. The adelic scalar-extension isomorphism retains both factors at split primes rather than choosing one.

### 12.3 A real quadratic field

Take $K=\mathbf Q(\sqrt5)$. It has two real places, so

$$
K_\infty^\times=\mathbf R^\times\times\mathbf R^\times.
$$

The logarithmic norm-one hyperplane is the line $t_1+t_2=0$. The unit

$$
\varepsilon=\frac{1+\sqrt5}{2}
$$

has conjugate $(1-\sqrt5)/2$ and norm $-1$. Its logarithmic vector is

$$
(\log\varepsilon,-\log\varepsilon)
$$

after taking absolute values. Powers of this vector form a lattice in the line. Thus the apparently unbounded ratio between the two real sizes becomes a circle-like compact direction after quotienting by global units.

Because a unit of negative norm exists, every sign pattern can be adjusted more freely than in a real quadratic field whose units all have positive norm. This affects the difference between the ordinary and narrow class groups. The finite adelic unit factors remain compact in either case; the distinction lies entirely in the real sign quotient.

### 12.4 A nonprincipal ideal as an idele

Take $K=\mathbf Q(\sqrt{-5})$, whose ring of integers is $\mathbf Z[\sqrt{-5}]$. The ideal

$$
\mathfrak p=(2,1+\sqrt{-5})
$$

has norm $2$ and satisfies $\mathfrak p^2=(2)$. It is not principal: a generator would have absolute norm $2$, but

$$
N(a+b\sqrt{-5})=a^2+5b^2
$$

never equals $2$ for integers $a,b$. Thus $\mathfrak p$ represents a nontrivial class of order two.

Choose a uniformizer $\pi_{\mathfrak p}$ in $K_{\mathfrak p}$ and form the finite idele

$$
x_v=
\begin{cases}
\pi_{\mathfrak p},&v=\mathfrak p,\\
1,&v\ne\mathfrak p.
\end{cases}
$$

Then $\mathfrak a(x)=\mathfrak p$. No principal idele can have exactly the same valuation vector modulo finite units, since that would make $\mathfrak p$ principal. This is the simplest explicit way an idele contains genuinely global information not carried by a single global number.

Nevertheless, after passing to the finite ideal class group only the class of $\mathfrak p$ remains. Varying $x_{\mathfrak p}$ by an element of $\mathcal O_{\mathfrak p}^\times$ changes local congruence data but not the ideal. A ray quotient may detect the change; the ordinary class group cannot.

### 12.5 Split places and norm components

Suppose a place $v$ of $K$ splits completely in a degree-$d$ extension $L$. Then

$$
L\otimes_KK_v\cong K_v^d.
$$

The local component of the adelic norm is simply

$$
(y_1,\ldots,y_d)\longmapsto y_1\cdots y_d.
$$

It is surjective: take $(b,1,\ldots,1)$. At an inert unramified place, by contrast, the local algebra is one field and norm valuations are multiples of $d$. Thus splitting changes not merely the number of coordinates but the local image of the norm. The restricted product records these two behaviors uniformly without pretending they are identical.

### 12.6 Quadratic splitting as an adelic product

Let $K=\mathbf Q(\sqrt d)$ with squarefree $d$. For an odd prime $p\nmid d$, reduction of $X^2-d$ has either two roots or no root modulo $p$. Hensel lifting gives

$$
K\otimes_{\mathbf Q}\mathbf Q_p\cong
\begin{cases}
\mathbf Q_p\times\mathbf Q_p,&d\text{ is a square modulo }p,\\
E_p,&d\text{ is a nonsquare modulo }p,
\end{cases}
$$

where $E_p/\mathbf Q_p$ is the unramified quadratic extension. Primes dividing the field discriminant ramify; the prime $2$ is handled by the integral minimal polynomial and may split, remain inert, or ramify according to $d$. This local trichotomy becomes a single global identity

$$
\mathbf A_K\cong K\otimes_{\mathbf Q}\mathbf A_{\mathbf Q}.
$$

At a split prime the right side contributes two independent $p$-adic coordinates; at an inert or ramified prime it contributes one quadratic local coordinate. Almost everywhere the integral tensor product likewise gives either $\mathbf Z_p\times\mathbf Z_p$ or the integer ring of the unramified quadratic extension.

At infinity, $d>0$ gives two real factors and $d<0$ one complex factor. The normalized complex absolute value counts the latter with degree two, so the product formula is uniform across both signs of $d$. This example is a compact model of the entire adelic philosophy: decomposition varies place by place, while restricted products assemble every local outcome without forcing a global choice of branch.

## 13. The local--global architecture

### 13.1 Two restricted products, two kinds of gluing

The additive and multiplicative constructions solve related but different gluing problems. Additive adeles allow local quantities with integral tails. Their diagonal quotient is compact because principal parts can be removed at finitely many primes and the remaining archimedean vector can be reduced modulo the lattice of algebraic integers.

Ideles allow local nonzero quantities with unit tails. Their valuations assemble into a fractional ideal, while their unit components preserve congruence information. The product formula removes principal ideles from the global module, and Dirichlet's theorem reduces the remaining archimedean ratios modulo a logarithmic unit lattice. The outcome is compactness of $C_K^1$, not of all $C_K$.

These parallels can be summarized as

$$
\begin{array}{c|c|c}
&\text{additive}&\text{multiplicative}\\ \hline
\text{tail condition}&x_v\in\mathcal O_v&x_v\in\mathcal O_v^\times\\
\text{global subgroup}&K&K^\times\\
\text{archimedean lattice}&\mathcal O_K\subset K_\infty&
\lambda(\mathcal O_K^\times)\subset H\\
\text{compact quotient}&\mathbf A_K/K&C_K^1\\
\text{discrete arithmetic quotient}&\text{none canonical}&\operatorname{Cl}(K),\ \operatorname{Cl}_{\mathfrak m}(K).
\end{array}
$$

The analogy is structural, not literal. In particular the idele topology must control inversion, and its compactness theorem needs both ideal-class finiteness and the unit theorem.

### 13.2 Exact hypotheses and durable consequences

The principal conclusions for a number field $K$ are:

- $\mathbf A_K$ is a locally compact topological ring and $\mathbf A_K^\times$ is a locally compact topological group in its restricted-product topology;
- the diagonal $K$ is discrete and cocompact in $\mathbf A_K$;
- the diagonal $K^\times$ is discrete in $\mathbf A_K^\times$;
- the product formula makes $K^\times$ lie in $\mathbf A_K^1$;
- $C_K^1$ is compact, while $C_K/C_K^1\cong\mathbf R_{>0}$;
- finite idele valuations recover fractional ideals, and quotienting by principal ideles recovers the ideal class group after discarding infinite and unit data;
- every ray class group for a finite modulus is finite;
- extension norms are defined coordinatewise, preserve the idele module, respect principal ideles, and refine ideal norms.

The number-field hypothesis enters through finite residue fields, the archimedean decomposition, Minkowski's lattice theory, ideal-class finiteness, and Dirichlet's unit theorem. Restricted products exist far more generally, but these compactness and finiteness conclusions should not be transported without replacing those inputs.

### 13.3 What has not been asserted

No reciprocity homomorphism has been defined. Ray class groups have been constructed as explicit finite adelic quotients, but they have not been identified with Galois groups. Local norm subgroups and the adelic norm have been described, but no general local--global norm principle has been claimed. These are substantive theorems, not consequences hidden in notation.

Likewise, the existence of Haar measure was used only to explain the module and volume scaling. Harmonic analysis on $\mathbf A_K$, Fourier duality, and automorphic representation theory require further structures. What is established here is the topological and algebraic platform on which those theories can be stated without ambiguity.

### 13.4 Conclusion

A number field cannot be reconstructed by treating its completions as unrelated approximations. The arithmetic relation among them is encoded by two restrictions: additive components are integral almost everywhere, and multiplicative components are units almost everywhere. With precisely those restrictions, the local spaces assemble into locally compact global objects.

The diagonal field then exhibits a striking balance. Additively it is sparse enough to be discrete yet large enough to leave a compact quotient. Multiplicatively its absolute values cancel by the product formula; after the one remaining global size direction is removed, ideal classes, finite units, archimedean phases, and logarithmic unit ratios fit into a compact group. Valuations project this group toward ideals, deeper unit neighborhoods project it toward ray classes, and local determinant norms assemble into a global norm compatible with every level.

This is the enduring adelic language: one may impose finitely many precise local conditions, retain uniform control everywhere else, and distinguish cleanly between a compatible family of local data and data arising from one global element. Later reciprocity laws will interpret finite quotients of the idele class group arithmetically, and later automorphic constructions will analyze functions and representations on adelic groups. Their common foundation is already visible here—the restricted product turns all places into one coherent locally compact arithmetic space.
