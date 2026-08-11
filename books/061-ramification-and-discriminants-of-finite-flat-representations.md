# Ramification and Discriminants of Finite-Flat Representations

## Contents

1. [The arithmetic size hidden in a finite representation](#1-the-arithmetic-size-hidden-in-a-finite-representation)
   - [The local-to-global question](#11-the-local-to-global-question)
   - [Standing notation and normalizations](#12-standing-notation-and-normalizations)
   - [What finite flatness contributes](#13-what-finite-flatness-contributes)
   - [The architecture of the argument](#14-the-architecture-of-the-argument)
2. [Cutout fields and integral models](#2-cutout-fields-and-integral-models)
   - [Fields cut out by finite actions](#21-fields-cut-out-by-finite-actions)
   - [Finite-flat models](#22-finite-flat-models)
   - [Faithfulness and upper numbering](#23-faithfulness-and-upper-numbering)
   - [Subobjects, extensions, and composita](#24-subobjects-extensions-and-composita)
3. [The ramification and discriminant ledger](#3-the-ramification-and-discriminant-ledger)
   - [Lower and upper numbering](#31-lower-and-upper-numbering)
   - [The different in upper numbering](#32-the-different-in-upper-numbering)
   - [A cutoff-to-different theorem](#33-a-cutoff-to-different-theorem)
   - [Local and global normalization](#34-local-and-global-normalization)
4. [Integral distance on a finite-flat group](#4-integral-distance-on-a-finite-flat-group)
   - [The augmentation ideal as a metric](#41-the-augmentation-ideal-as-a-metric)
   - [Multiplication near the identity](#42-multiplication-near-the-identity)
   - [The torsion-free congruence ball](#43-the-torsion-free-congruence-ball)
   - [Sharpness of the separation radius](#44-sharpness-of-the-separation-radius)
5. [From integral separation to upper ramification](#5-from-integral-separation-to-upper-ramification)
   - [Congruence clusters](#51-congruence-clusters)
   - [The cluster-counting lemma](#52-the-cluster-counting-lemma)
   - [Proof of the lemma](#53-proof-of-the-lemma)
   - [Why the group structure is essential](#54-why-the-group-structure-is-essential)
6. [The Fontaine--Raynaud upper-break theorem](#6-the-fontaine--raynaud-upper-break-theorem)
   - [The local theorem](#61-the-local-theorem)
   - [Level one and the ramified-base correction](#62-level-one-and-the-ramified-base-correction)
   - [Endpoints, strict inequalities, and optimality](#63-endpoints-strict-inequalities-and-optimality)
   - [Small-height interpretation](#64-small-height-interpretation)
7. [Different and discriminant bounds](#7-different-and-discriminant-bounds)
   - [The local different theorem](#71-the-local-different-theorem)
   - [Refinements from the actual filtration](#72-refinements-from-the-actual-filtration)
   - [Conductors and faithful actions](#73-conductors-and-faithful-actions)
   - [Examples and checks](#74-examples-and-checks)
8. [Change of coefficients and exact constructions](#8-change-of-coefficients-and-exact-constructions)
   - [Forgetting and extending scalars](#81-forgetting-and-extending-scalars)
   - [Coefficient quotients](#82-coefficient-quotients)
   - [Duality, products, and exact middle terms](#83-duality-products-and-exact-middle-terms)
   - [A coefficient-stability theorem](#84-a-coefficient-stability-theorem)
9. [Ground-field change, subfields, and towers](#9-ground-field-change-subfields-and-towers)
   - [Restriction to a larger local field](#91-restriction-to-a-larger-local-field)
   - [Quotient fields and unramified base change](#92-quotient-fields-and-unramified-base-change)
   - [Transitivity of differents](#93-transitivity-of-differents)
   - [Stepwise finite-flat towers](#94-stepwise-finite-flat-towers)
10. [Fontaine--Laffaille realizations](#10-fontaine--laffaille-realizations)
    - [The unramified low-weight range](#101-the-unramified-low-weight-range)
    - [Stable lattices and all finite quotients](#102-stable-lattices-and-all-finite-quotients)
    - [Height two and compatible coefficients](#103-height-two-and-compatible-coefficients)
    - [What the linear classification adds](#104-what-the-linear-classification-adds)
11. [Global root discriminants](#11-global-root-discriminants)
    - [The global localization formula](#111-the-global-localization-formula)
    - [The sharp finite-flat estimate](#112-the-sharp-finite-flat-estimate)
    - [Auxiliary ramification away from the coefficient prime](#113-auxiliary-ramification-away-from-the-coefficient-prime)
    - [Subfields and several representations](#114-subfields-and-several-representations)
12. [Arithmetic examples](#12-arithmetic-examples)
    - [Constant and cyclotomic modules](#121-constant-and-cyclotomic-modules)
    - [Good-reduction abelian varieties](#122-good-reduction-abelian-varieties)
    - [Two-dimensional residual representations](#123-two-dimensional-residual-representations)
    - [A complete numerical example](#124-a-complete-numerical-example)
13. [Level towers and uniformity](#13-level-towers-and-uniformity)
    - [Full-level bounds](#131-full-level-bounds)
    - [Successive degrees](#132-successive-degrees)
    - [What cannot be uniform](#133-what-cannot-be-uniform)
    - [Uniform composita at a fixed level](#134-uniform-composita-at-a-fixed-level)
14. [The finite-flat discriminant package](#14-the-finite-flat-discriminant-package)
    - [The local package](#141-the-local-package)
    - [The global package](#142-the-global-package)
    - [Hypothesis and failure ledger](#143-hypothesis-and-failure-ledger)
    - [Conclusion](#144-conclusion)

## 1. The arithmetic size hidden in a finite representation

### 1.1 The local-to-global question

A finite Galois representation has an algebraic size and an arithmetic size. Its image is a finite group, so matrices bound the degree of the field on which the representation becomes trivial. The discriminant of that field measures something different: how deeply its primes ramify. Fixed degree does not bound this depth. Cyclic extensions of one fixed prime degree can have arbitrarily large discriminant, so no argument based only on the order of a matrix group can provide the estimate needed in arithmetic applications.

Finite flatness supplies the missing information. Suppose that $K$ is a finite extension of $\mathbf Q_\ell$ and that a finite $G_K$-module $M$ is the generic fiber of a finite locally free commutative group over $\mathcal O_K$. The model remembers how distinct generic points approach each other at the closed fiber. The group law and the divisibility of multiplication by $\ell$ prevent nonzero torsion points from entering a sufficiently small congruence ball around the identity. Ramification groups of great depth move every integral element only imperceptibly; they therefore cannot move separated torsion points. This geometric observation becomes a bound on the last upper ramification break.

The passage has four stages:

$$
\text{finite-flat model}
\longrightarrow\text{integral separation of points}
\longrightarrow\text{upper-break cutoff}
\longrightarrow\text{different and root discriminant}.
$$

Every arrow has its own normalization. The separation radius is measured with the valuation of $K$. Upper numbering is the quotient-compatible ramification clock. The different exponent is measured with the normalized valuation upstairs. A root discriminant divides a global discriminant exponent by the absolute degree. Much of this book is devoted to showing why the constants survive these changes of scale without acquiring an unwanted degree or ramification-index factor.

### 1.2 Standing notation and normalizations

Fix a rational prime $\ell$. For the local theory let

$$
K/\mathbf Q_\ell
$$

be finite, let $R=\mathcal O_K$, and normalize

$$
v_K(K^\times)=\mathbf Z,
\qquad e_K=v_K(\ell).
$$

The residue field of $K$ is finite, hence perfect. Choose a separable closure $K^s$ and write $G_K=\operatorname{Gal}(K^s/K)$. Upper ramification groups of $G_K$ are denoted $G_K^u$ for real $u\geq-1$ and are defined by inverse limit from finite Galois quotients. We use the left-continuous convention of the ramification theory volume. Values at isolated endpoints never affect an integral over $u$.

If $L/K$ is finite, write

$$
e(L/K)=e,\qquad f(L/K)=f.
$$

When $L/K$ is separable, its different is

$$
\mathfrak D_{L/K}=\mathfrak m_L^{d(L/K)}.
$$

Its relative discriminant is

$$
\mathfrak d_{L/K}=N_{L/K}(\mathfrak D_{L/K})
=\mathfrak m_K^{\delta(L/K)},
\qquad \delta(L/K)=f\,d(L/K).
$$

Thus $d$ and $\delta$ agree only when $f=1$. The ratio relevant to root discriminants is

$$
\frac{\delta(L/K)}{[L:K]}=\frac{d(L/K)}{e(L/K)}.
\tag{1.1}
$$

A finite continuous $G_K$-module is a finite abelian group with continuous action. For $n\geq1$, it is **killed by $\ell^n$** if $\ell^nM=0$; this does not mean that $n$ is minimal. A **finite-flat model** of $M$ is a finite locally free commutative $R$-group $\mathcal G$ together with an identification

$$
\mathcal G_K(K^s)\simeq M.
$$

Because $K$ has characteristic zero, every finite generic group is étale and geometric points recover it. Coefficient actions will be added explicitly when required, but the ramification bound depends only on the underlying finite group and on its exponent.

### 1.3 What finite flatness contributes

The earlier theory of finite-flat representations establishes the exact generic-to-integral dictionary used here. A stable generic subgroup closes inside a chosen model to a finite-flat subgroup, and the represented quotient is finite flat. Products model direct sums. Cartier duality models the Tate-twisted dual. A compatible finite coefficient action may be installed on a suitable model. These assertions concern existence; a representation at residue-characteristic torsion can have more than one model.

The small-height classification explains what the model remembers. For an order-$\ell$ group over a mixed-characteristic DVR, Oort--Tate parameters have valuations $r$ and $e_K-r$. The endpoints are étale and multiplicative, while intermediate values give local-local special fiber. The generic character sees a tame exponent modulo $\ell-1$, but the integral parameter remembers its position in the full interval $0\leq r\leq e_K$. This extra integral distance is exactly the kind of information absent from matrices.

In the absolutely unramified range, the integral Fontaine--Laffaille equivalence identifies finite-flat torsion modules with low-weight divided filtered modules. Its compatible-quotient theorem proves that all coefficient quotients of a suitable stable lattice remain finite flat. We will use that classification to produce the hypotheses of our ramification theorem, not to prove the ramification theorem itself. The latter is valid over every finite extension of $\mathbf Q_\ell$ and also at $\ell=2$.

### 1.4 The architecture of the argument

Chapters 2 and 3 translate finite actions into fields and recall the exact upper-numbered formula for the different. Chapter 4 extracts a universal separation radius from the Hopf algebra of a finite-flat group. Chapter 5 proves the central cluster-counting lemma that converts this radius into upper numbering. Chapter 6 then proves the Fontaine--Raynaud cutoff

$$
M^{G_K^u}=M
\quad\text{for}\quad
u>e_K\left(n+\frac1{\ell-1}\right)-1,
$$

where the displayed equality means pointwise fixedness.

Chapters 7--10 prove the different bound and its stability under the operations that arise from coefficients, exact sequences, local base change, towers, and Fontaine--Laffaille realization. Chapters 11--13 globalize the local estimate and distinguish full-level growth from genuinely uniform statements. The final chapter packages the results with every hypothesis visible.

## 2. Cutout fields and integral models

### 2.1 Fields cut out by finite actions

Let $F$ be any field with separable closure $F^s$, and let $M$ be a finite continuous $G_F$-module. Its action homomorphism

$$
\rho_M:G_F\longrightarrow\operatorname{Aut}(M)
$$

has open normal kernel. The **field cut out by $M$** is

$$
F(M)=(F^s)^{\ker\rho_M}.
\tag{2.1}
$$

It is finite Galois over $F$, and restriction identifies

$$
\operatorname{Gal}(F(M)/F)\simeq\operatorname{im}\rho_M.
\tag{2.2}
$$

This is the smallest extension over which every element of $M$ is fixed. It is not necessarily generated by one chosen nonzero vector: that vector may have a nontrivial stabilizer.

The construction behaves contravariantly with respect to kernels. If $N$ is a stable submodule or a quotient of $M$, then

$$
F(N)\subseteq F(M).
\tag{2.3}
$$

For two modules,

$$
F(M\oplus N)=F(M)F(N),
\tag{2.4}
$$

because the kernel on a direct sum is the intersection of the two kernels. An exact sequence

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
\tag{2.5}
$$

need not give equality $F(M)=F(M')F(M'')$. Over the compositum on the right, the constituents are trivial, but the middle action can remain

$$
\begin{pmatrix}1&c(\sigma)\\0&1\end{pmatrix}.
$$

The cocycle $c$ can cut out a further extension. Ramification of the full middle term must therefore be controlled integrally; bounds for its graded factors alone do not suffice.

### 2.2 Finite-flat models

Let now $F=K$ be local as in Chapter 1. The finite étale--Galois correspondence attaches to $M$ a finite étale $K$-group $\mathcal E_K(M)$. A marked finite-flat model is a pair

$$
(\mathcal G,\iota),\qquad
\iota:\mathcal G_K\xrightarrow{\sim}\mathcal E_K(M),
$$

where $\mathcal G$ is finite locally free and commutative over $R$. If $\mathcal G=\operatorname{Spec}A$, then $A$ is finite free over $R$. Consequently two morphisms from or to $\mathcal G$ which agree generically agree integrally: their difference lands in an $R$-torsion-free module and vanishes after inverting a uniformizer.

This faithfulness has an immediate consequence. If $\ell^nM=0$, multiplication by $\ell^n$ is zero on $\mathcal G_K$. Hence

$$
[\ell^n]_{\mathcal G}=0
\tag{2.6}
$$

integrally. Thus the exponent of the generic module controls the group law on the entire model, even though the special fiber may be connected or nonreduced.

When $M$ carries an action of a finite commutative coefficient ring $A_0$, a coefficient-linear model includes a homomorphism

$$
A_0\longrightarrow\operatorname{End}_R(\mathcal G)
$$

which realizes the generic action. The bound below does not use freeness of $M$ over $A_0$, nor the cardinality of $A_0$, nor the rank of $M$. It uses only (2.6).

### 2.3 Faithfulness and upper numbering

Let $L=K(M)$. The action of $G=\operatorname{Gal}(L/K)$ on $M$ is faithful by construction. Herbrand's quotient theorem gives, for every real $u\geq-1$, the image identity

$$
\operatorname{im}\bigl(G_K^u\to G\bigr)=G^u.
\tag{2.7}
$$

It follows that

$$
G_K^u\text{ acts trivially on }M
\quad\Longleftrightarrow\quad
G^u=1.
\tag{2.8}
$$

The equivalence is why the field must be cut out by the full module. If one chose a larger extension through which the representation happened to factor, ramification in the kernel would be invisible on $M$. If one chose the field of a single vector, the resulting action might not be faithful.

Upper numbering is also responsible for stability under subfields. If $N$ is a subquotient and $K(N)\subseteq L$, then the upper group of $\operatorname{Gal}(K(N)/K)$ is the image of $G^u$. Thus a cutoff for $M$ automatically descends to $N$. Lower numbering would require a Herbrand reindexing at every quotient and is unsuitable for this operation.

### 2.4 Subobjects, extensions, and composita

Suppose that $M$ has a chosen finite-flat model $\mathcal G$. If $N\subseteq M$ is stable, the schematic closure $\mathcal H$ of $\mathcal E_K(N)$ in $\mathcal G$ is finite flat over the DVR. The quotient $\mathcal G/\mathcal H$ exists and models $M/N$. Hence submodules and quotients inherit both finite flatness and the exponent bound.

If $M_1$ and $M_2$ have models killed by $\ell^{n_1}$ and $\ell^{n_2}$, their product models $M_1\oplus M_2$ and is killed by

$$
\ell^{\max(n_1,n_2)}.
$$

Consequently their compositum field will have the maximum of the two universal cutoffs, not their sum. This maximum principle is stronger than multiplying two independently obtained discriminant bounds.

For (2.5), a model of the middle term gives models of both endpoints by closure and quotient. Conversely, separate models of $M'$ and $M''$ do not supply a model of an arbitrary generic extension. When a faithfully flat exact sequence

$$
0\longrightarrow\mathcal G'\longrightarrow\mathcal G
\longrightarrow\mathcal G''\longrightarrow0
\tag{2.9}
$$

is supplied, the middle term is finite flat and its generic extension class receives the universal bound. This is exactly the hypothesis needed to control the off-diagonal cocycle.

## 3. The ramification and discriminant ledger

### 3.1 Lower and upper numbering

Let $L/K$ be finite Galois, with group $G$, and normalize $v_L(L^\times)=\mathbf Z$. Since the residue field of $K$ is finite, every residue extension is separable. For $\sigma\ne1$, put

$$
i_G(\sigma)=\min_{x\in\mathcal O_L}v_L(\sigma x-x),
$$

and set

$$
G_i=\{\sigma:i_G(\sigma)\geq i+1\}
\qquad(i\geq0),
$$

with $G_{-1}=G$. Thus $G_0$ is inertia and $G_1$ is wild inertia. Extend to real lower indices by the established left-continuous convention. The Herbrand function is

$$
\varphi_{L/K}(t)=\int_0^t\frac{ds}{[G_0:G_s]}
\qquad(t\geq0),
\tag{3.1}
$$

and the upper groups are

$$
G^u=G_{\psi(u)},
\qquad \psi=\varphi^{-1}.
\tag{3.2}
$$

The slope of $\varphi$ on a lower interval where $G_s=H$ is $|H|/|G_0|$. Deep lower intervals are therefore compressed in proportion to the number of surviving automorphisms. Herbrand's theorem says that this compression is exactly what makes upper numbering commute with quotients.

### 3.2 The different in upper numbering

Hilbert's different formula gives

$$
d(L/K)=\sum_{i\geq0}(|G_i|-1).
\tag{3.3}
$$

Let us recall why (3.3) has exactly this indexing. Choose an integral element $\alpha$ which generates $\mathcal O_L$ over $\mathcal O_K$ and has the property

$$
v_L(\sigma\alpha-\alpha)=i_G(\sigma)
\qquad(\sigma\ne1).
$$

Such an element is obtained by adding a lift of a separating residue-field generator to a uniformizer. If $f$ is its minimal polynomial, the monogenic derivative formula gives

$$
d(L/K)=v_L(f'(\alpha))
=\sum_{\sigma\ne1}v_L(\alpha-\sigma\alpha)
=\sum_{\sigma\ne1}i_G(\sigma).
$$

An automorphism with displacement $i_G(\sigma)=r$ belongs to $G_0,G_1,\ldots,G_{r-1}$ and to no later lower group. Counting each automorphism once at every level at which it occurs turns the last sum into (3.3). This proof also explains the isolated tame term below: inertia occupies level zero even when every positive lower group is trivial.

To convert it to upper numbering, isolate $i=0$ and regard the remaining sum as an integral. Since $|G_0|=e(L/K)=e$, the change of variables $u=\varphi(t)$ gives

$$
\begin{aligned}
d(L/K)
&=(e-1)+\int_0^\infty(|G_t|-1)\,dt\\
&=(e-1)+e\int_0^\infty
\left(1-\frac1{|G^u|}\right)du.
\end{aligned}
\tag{3.4}
$$

After dividing by $e$,

$$
\boxed{
\frac{d(L/K)}e
=1-\frac1e+
\int_0^\infty\left(1-\frac1{|G^u|}\right)du.}
\tag{3.5}
$$

The first term is the tame baseline. The integral is the wild excess. Formula (3.5) is exact, insensitive to endpoint conventions, and already normalized for root-discriminant calculations.

### 3.3 A cutoff-to-different theorem

The exact formula immediately turns any last-break theorem into a different theorem.

**Proposition 3.1 (cutoff bound).** Suppose $G^u=1$ for every $u>R$, where $R\geq0$. Then

$$
d(L/K)\leq(e-1)+eR,
\tag{3.6}
$$

and

$$
\frac{d(L/K)}e
\leq1-\frac1e+R<1+R.
\tag{3.7}
$$

**Proof.** In (3.4) the integrand vanishes beyond $R$ and is at most $1$. This gives (3.6) and the weak inequality in (3.7). The final inequality is strict because $1/e>0$. No assertion about the group at the single endpoint $R$ is needed. $\square$

If more of the filtration is known, the integral in (3.5) should be retained. Proposition 3.1 is optimal among bounds that know only the last upper break and no group sizes: on most of $[0,R]$ the order of $G^u$ can be arbitrarily large, making the integrand arbitrarily close to $1$.

### 3.4 Local and global normalization

The local discriminant exponent is $\delta=fd$, so Proposition 3.1 also gives

$$
\delta(L/K)\leq f\bigl((e-1)+eR\bigr).
\tag{3.8}
$$

The factor $f$ must not be dropped. Yet after dividing by the local degree $ef$, it cancels and yields (1.1). This cancellation is the reason $d/e$, not $d$ or $\delta$, is the natural local cost.

For a number field $F$ and a finite Galois extension $L/F$, choose for each finite place $v$ a place $w\mid v$. Put $e_v=e(L_w/F_v)$ and $d_v=d(L_w/F_v)$. There are $g_v$ places above $v$, and the local relative discriminant exponent of the product algebra is $g_vf_vd_v$. Since

$$
[L:F]=g_ve_vf_v,
$$

the contribution of $v$ to the absolute root discriminant is

$$
(Nv)^{d_v/(e_v[F:\mathbf Q])}.
\tag{3.9}
$$

This identity will be proved globally in Chapter 11. It is recorded now to show where every local normalization is headed.

## 4. Integral distance on a finite-flat group

### 4.1 The augmentation ideal as a metric

Let $\mathcal G=\operatorname{Spec}A$ be a finite locally free commutative $R$-group. Its identity section gives an augmentation

$$
\varepsilon:A\longrightarrow R,
\qquad I=\ker\varepsilon.
$$

Extend $v_K$ to $K^s$ with values in $\mathbf Q$. A geometric point $P:A\to\mathcal O_{K^s}$ has **identity depth**

$$
\nu(P)=\inf_{a\in I}v_K(P(a)),
\qquad \nu(0)=+\infty.
\tag{4.1}
$$

Because $I$ is a finite $R$-module, the infimum is a minimum on any finite set of generators. Every point takes integral functions to integral elements: a map from the finite $R$-algebra $A$ to $K^s$ has image integral over $R$, hence in the valuation ring of $K^s$.

Translation by $Q$ identifies the ideal of functions vanishing at $Q$ with $I$. It follows that

$$
\nu(P-Q)
=\inf_{a\in A}v_K(P(a)-Q(a)).
\tag{4.2}
$$

Thus $\nu(P-Q)$ is an intrinsic nonarchimedean distance between points. The finite Galois action preserves it because the algebra and its group law are defined over $R$.

### 4.2 Multiplication near the identity

The key estimate is a Hopf-algebra form of the fact that multiplication by $\ell$ has no terms of degrees $2,\ldots,\ell-1$ modulo $\ell$.

**Proposition 4.1 (augmentation estimate).** For the pullback by multiplication by $\ell$,

$$
[\ell]^*I\subseteq \ell I+I^\ell,
\tag{4.3}
$$

and, more precisely,

$$
[\ell]^*x-\ell x\in \ell I^2+I^\ell
\qquad(x\in I).
\tag{4.4}
$$

**Proof.** Filter $A$ by powers of $I$. The comultiplication satisfies

$$
\Delta(x)\equiv x\otimes1+1\otimes x
\pmod{I\otimes I}
$$

for $x\in I$. Iterating $\Delta$ and then multiplying the $\ell$ tensor factors computes $[\ell]^*x$. Its degree-one part in $\operatorname{gr}_I(A)$ is the sum of $\ell$ identical copies of $x$, hence $\ell x$.

Reduce modulo $\ell$. Over characteristic $\ell$, the multiplication-by-$\ell$ morphism of a commutative group factors as relative Frobenius followed by Verschiebung. On coordinate rings the relative Frobenius sends every element of the augmentation ideal to its $\ell$th power. Consequently

$$
[\ell]^*I\subseteq I^\ell\pmod\ell.
$$

Lifting to $R$ gives (4.3). After subtracting the degree-one term $\ell x$, every remaining term divisible by $\ell$ has degree at least two, while the terms not known to be divisible by $\ell$ lie in $I^\ell$. This is (4.4). $\square$

If $r=\nu(P)>0$, evaluating (4.3) gives

$$
\nu([\ell]P)\geq\min\{e_K+r,\ell r\}.
\tag{4.5}
$$

The two expressions are equal at

$$
r_{\ell,K}=\frac{e_K}{\ell-1}.
\tag{4.6}
$$

This critical radius, rather than the rank or order of $\mathcal G$, governs the separation of torsion points.

### 4.3 The torsion-free congruence ball

**Theorem 4.2 (Raynaud separation).** Suppose $\mathcal G$ is killed by a power of $\ell$. If $P\in\mathcal G(K^s)$ satisfies

$$
\nu(P)>\frac{e_K}{\ell-1},
$$

then $P=0$.

**Proof.** Begin with a point killed by $\ell$. Choose $x_1,\ldots,x_m$ generating $I$ and choose $x=x_j$ for which $v_K(P(x))=\nu(P)=r$. From (4.4),

$$
0=P([\ell]^*x)
=\ell P(x)+\ell P(q)+P(s),
$$

with $q\in I^2$ and $s\in I^\ell$. The three terms have valuations at least

$$
e_K+r,\qquad e_K+2r,\qquad \ell r,
$$

respectively. If $r>e_K/(\ell-1)$, then $e_K+r<\ell r$, and certainly $e_K+r<e_K+2r$. The first term is the unique term of least valuation, so their sum cannot vanish. Hence no nonzero $\ell$-torsion point has such depth.

Now let $P$ be killed by $\ell^n$. Formula (4.5) and $r>e_K/(\ell-1)$ give

$$
\nu([\ell]P)\geq e_K+r>\frac{e_K}{\ell-1}.
$$

Induction on $n$ gives $[\ell]P=0$, and the order-$\ell$ case gives $P=0$. $\square$

Translation turns the result into pairwise separation.

**Corollary 4.3.** If $P\ne Q$ are geometric points, some $a\in A$ satisfies

$$
v_K(P(a)-Q(a))\leq\frac{e_K}{\ell-1}.
\tag{4.7}
$$

The result applies to the whole model because (2.6) shows that a model of a module killed by $\ell^n$ is itself killed by $\ell^n$.

### 4.4 Sharpness of the separation radius

For $\mu_\ell$, take the coordinate $U=T-1$. A primitive $\ell$th root of unity satisfies

$$
v_K(\zeta_\ell-1)=\frac{e_K}{\ell-1}
$$

after extending the normalized valuation. Thus the strict radius in Theorem 4.2 cannot be decreased as a universal statement about models. At the critical value the two leading terms in (4.4) can have equal valuation and cancel.

The constant group gives the opposite extreme: distinct sections are already distinct on the special fiber and have depth zero. The same abstract generic module can sometimes possess models with different distances. The theorem asks for one model and extracts a bound from it; it neither asserts uniqueness nor makes the eventual ramification field depend on the chosen witness.

The Oort--Tate interval makes the contrast concrete. Write a rank-$\ell$ model in a local coordinate as

$$
R[x]/(x^\ell-a x),
\qquad v_K(a)=r,\qquad 0\leq r\leq e_K.
$$

A nonzero generic point satisfies $x^{\ell-1}=a$, so its coordinate depth is

$$
v_K(x)=\frac r{\ell-1}
\leq\frac{e_K}{\ell-1}.
$$

The multiplicative endpoint $r=e_K$ reaches the critical radius; the étale endpoint $r=0$ has depth zero; intermediate models interpolate between them. This calculation does not prove Theorem 4.2 for higher-height groups, because such a group need not admit an order-$\ell$ filtration over $R$. It does show that the universal Hopf-algebra proof has exactly the constant predicted by the complete height-one classification.

## 5. From integral separation to upper ramification

### 5.1 Congruence clusters

The separation theorem is still stated in the valuation of $K$, whereas a ramification group is defined by displacement in a splitting field. A direct comparison would multiply the radius by the ramification index of that splitting field and give a useless bound. The cure is to count whole congruence clusters rather than one pair of points. Equal-sized translates make the ramification index cancel against the slopes of the Herbrand function.

Let $L/K$ be a finite Galois extension splitting the generic points of $\mathcal G$, put

$$
G=\operatorname{Gal}(L/K),\qquad E=e(L/K),
$$

and use $v_L=Ev_K$ on $L$. For $t\geq0$, define

$$
C_t=\{P\in\mathcal G(L):\nu(P)>t\}.
\tag{5.1}
$$

The nonarchimedean inequality and the group law show that $C_t$ is a subgroup. Two points are congruent at depth $t$ precisely when their difference lies in $C_t$, so the congruence classes are the cosets of $C_t$ and all have the same cardinality. The groups $C_t$ decrease only at finitely many rational values and are stable under $G$. The strict sign agrees with Theorem 4.2; replacing it by a weak sign would change the behavior at the critical radius.

For the exponent filtration put

$$
X_j=\mathcal G[\ell^j](L),\qquad
C_{t,j}=C_t\cap X_j
\quad(0\leq j\leq n).
\tag{5.2}
$$

On the generic fiber these are ordinary finite groups. We use only these point groups and their translation partitions. If an integral kernel of $[\ell^j]$ is needed, its schematic closure in $\mathcal G$ is finite flat and has exactly these generic points; no unproved flatness of a raw kernel is being assumed.

### 5.2 The cluster-counting lemma

We isolate the conversion theorem. It is the precise bridge between Raynaud's integral separation and Fontaine's upper ramification estimate.

**Lemma 5.1 (Fontaine cluster lemma).** Let $\mathcal G/R$ be finite locally free, commutative, with étale generic fiber, and suppose $[\ell^n]_{\mathcal G}=0$. Assume that every nonzero geometric point $P$ satisfies $\nu(P)\leq c$. Then

$$
G_K^u\text{ fixes }\mathcal G(K^s)
\quad\text{for every}\quad
u>e_Kn+c-1.
\tag{5.3}
$$

The term $e_Kn$ records $n$ passages through multiplication by $\ell$. The radius $c$ records terminal separation. The $-1$ converts integral displacement, which begins at congruence modulo the maximal ideal, to the upper clock whose tame baseline sits at index zero.

### 5.3 Proof of the lemma

The proof is a finite weighted count. We first isolate the one-layer statement so that the cancellation of the splitting-field ramification index is explicit.

**Weighted-block claim.** Let $X$ be a finite $G$-stable subgroup of $\mathcal G(L)$ and put $Y=[\ell]X$. Assume that every nonzero point of $\ker([\ell]:X\to Y)$ has depth at most $c$. If $b(Z)$ denotes the last upper parameter at which an upper ramification group acts nontrivially on a finite $G$-set $Z$, put $b(Z)=-1$ when inertia acts trivially and $b(Z)=0$ when inertia acts nontrivially but wild inertia acts trivially. Then

$$
b(X)\leq
\max\{b(Y)+e_K,\ e_K+c-1\}.
\tag{5.4}
$$

Here $Y$ carries the induced action, whether or not it equals all points killed by one lower power of $\ell$.

We prove the claim. For a $G$-stable finite group $D$ and a $G$-stable subgroup $C$, the cosets of $C$ form an equal-block system. For a lower group $G_s$, count the pairs $(\sigma,x)$ satisfying $\sigma x-x\in C$. Counting first in $\sigma$ and then in $x$ gives

$$
|C|\sum_{\sigma\in G_s}
\left|\ker\bigl(\sigma-1:D/C\to D/C\bigr)\right|
=\sum_{x\in D}
\left|\operatorname{Stab}_{G_s}(x+C)\right|.
\tag{5.5}
$$

The equality is literal: for fixed $\sigma$, every nonempty solution fiber is a coset of $C$; for fixed $x$, the condition says exactly that $G_s$ stabilizes the block $x+C$. Divide (5.5) by $|G_0||D|$. On an interval where $G_s$ and the block system are constant, orbit--stabilizer identifies the resulting factor with the proportion of a block that has not yet separated. Multiplying by the lower length and summing gives the Herbrand-weighted length

$$
\int\frac{ds}{[G_0:G_s]}.
\tag{5.6}
$$

This is the same finite sum that proves Herbrand's quotient theorem: passing to the action on $D/C$ replaces $G_s$ by its image, while the stabilizer factor in (5.5) accounts for the kernel. Thus upper time during which the quotient blocks move is charged to $D/C$, and only time during which points move inside one block remains to be charged to $C$.

Apply this count to the successive congruence partitions

$$
D/C_t,
\qquad C_t=\{P\in D:\nu(P)>t\}.
\tag{5.7}
$$

There are only finitely many critical $t$. If at one critical value a block of size $h$ splits into $m$ equal subblocks, the stabilizer factor in (5.5) multiplies the continuing charge by $1/m$; the complementary proportion $1-1/m$ becomes the charge of the new quotient blocks. At the next critical value that new quotient charge is the continuing charge. Hence all intermediate terms cancel in the finite sum. This telescoping is orbitwise, so transitivity of the action is not required.

It remains to identify the two boundary charges. Pull the congruence filtration on $Y$ back through $[\ell]:X\to Y$. Proposition 4.1 gives

$$
[\ell]^*I\subseteq \ell I+I^\ell.
\tag{5.8}
$$

In the finite sum over critical congruence depths, the summand $\ell I$ translates every lower threshold by exactly $v_L(\ell)=Ee_K$. The $I^\ell$ summand only refines the current congruence block: its values are products of $\ell$ augmentation values, so its critical depths occur among the intermediate refinements already paired in the telescoping sum. It creates no additional boundary term. Thus pulling the quotient-block clock back from $Y$ to $X$ leaves one new raw boundary interval, of length at most $Ee_K$. In (5.6) the equal-block stabilizer factor divides that interval by the inertia index already accumulated. Since $E=|G_0|$ for a finite Galois extension of local fields with finite residue field, its total upper length is at most $e_K$. This gives the first term $b(Y)+e_K$ in (5.4).

If the image block has already become a point, motion can remain only inside the kernel of $[\ell]$. Its last nonzero difference has depth at most $c$, so after the same $Ee_K$ linear shift the remaining raw terminal interval has length at most $Ec$. In the lower numbering, membership in $G_s$ means displacement valuation at least $s+1$; the first unit interval is therefore the integral-displacement baseline, and it lies where the Herbrand slope is one. Positive upper time starts after upper index $0$, so removing that unit interval subtracts exactly one from the upper clock. The terminal upper charge is consequently

$$
e_K+c-1.
\tag{5.9}
$$

These are the only boundary terms left after telescoping, and (5.4) follows. Notice exactly where the dangerous $E$ disappeared: lower valuation multiplies every raw interval by $E$, while the equal-block stabilizer denominator in the Herbrand sum divides by the same inertia index. Without translation blocks of equal size, the cancellation would be unavailable.

We now prove Lemma 5.1. Take

$$
X_j=\mathcal G[\ell^j](L),\qquad
Y_j=[\ell]X_j\subseteq X_{j-1}.
$$

Write $b_j=b(X_j)$. Since $Y_j$ is a $G$-stable subgroup of $X_{j-1}$,

$$
b(Y_j)\leq b_{j-1}.
\tag{5.10}
$$

The kernel of $X_j\to Y_j$ is contained in $X_1$, and every one of its nonzero points has depth at most $c$. The weighted-block claim gives

$$
b_1\leq e_K+c-1,
\qquad
b_j\leq\max\{b_{j-1}+e_K,e_K+c-1\}
\quad(j>1).
\tag{5.11}
$$

Induction yields

$$
b_j\leq je_K+c-1.
\tag{5.12}
$$

Because $[\ell^n]_{\mathcal G}=0$, all geometric points lie in $X_n$. Thus $G^u$ fixes every point for $u>ne_K+c-1$. Herbrand quotient compatibility makes this independent of the chosen splitting field and identifies it with the assertion for $G_K^u$. This proves the lemma. $\square$

The proof may be remembered as a three-column ledger:

$$
\begin{array}{c|c|c}
\text{source}&\text{raw cost}&\text{upper cost}\\
\hline
\text{terminal point separation}&Ec&c\\
\text{one multiplication layer}&Ee_K&e_K\\
\text{initial displacement interval}&1&1.
\end{array}
$$

Equal translation blocks supply the denominators which cancel $E$. Without them, only the much weaker lower-numbered bound $Ec-1$ would be visible.

### 5.4 Why the group structure is essential

An arbitrary finite flat $R$-algebra can have an étale generic fiber whose conjugate points are very close. Its congruence classes need not be translates, their sizes need not agree, and there is no multiplication-by-$\ell$ filtration. Neither (4.3) nor the equal-block cancellation in the proof of Lemma 5.1 survives. The cluster lemma is therefore a theorem about finite-flat **groups**, not about finite covers of a trait in general.

Commutativity enters Proposition 4.1 through the characteristic-$\ell$ factorization of multiplication by $\ell$ and enters the cluster proof by making the $X_j$ a compatible filtration of normal translation subgroups. There are versions for broader classes of group objects, but no such generalization is needed here.

## 6. The Fontaine--Raynaud upper-break theorem

### 6.1 The local theorem

We can now combine the separation and cluster lemmas.

**Theorem 6.1 (Fontaine--Raynaud upper-break bound).** Let $K/\mathbf Q_\ell$ be finite and put $e_K=v_K(\ell)$. Let $M$ be a finite continuous $G_K$-module killed by $\ell^n$. If $M$ admits a finite-flat model over $\mathcal O_K$, then

$$
\boxed{
G_K^u\text{ acts trivially on }M
\quad\text{for every}\quad
u>c_n(K),}
\tag{6.1}
$$

where

$$
\boxed{
c_n(K)=e_K\left(n+\frac1{\ell-1}\right)-1.}
\tag{6.2}
$$

**Proof.** Choose a model $\mathcal G$. Equation (2.6) gives $[\ell^n]_{\mathcal G}=0$. Theorem 4.2 shows that every nonzero difference of geometric points has depth at most $e_K/(\ell-1)$. Lemma 5.1 therefore gives triviality for

$$
u>e_Kn+\frac{e_K}{\ell-1}-1
=e_K\left(n+\frac1{\ell-1}\right)-1.
$$

Under the generic marking, the geometric points are $M$. $\square$

Let $L=K(M)$. Faithfulness and (2.8) give the field version

$$
\operatorname{Gal}(L/K)^u=1
\quad(u>c_n(K)).
\tag{6.3}
$$

No model is chosen in this conclusion. Any one witness proves the same assertion about the intrinsic cutout field.

### 6.2 Level one and the ramified-base correction

At level one,

$$
c_1(K)=e_K\left(1+\frac1{\ell-1}\right)-1
=\frac{e_K\ell}{\ell-1}-1.
\tag{6.4}
$$

If $K/\mathbf Q_\ell$ is unramified, $e_K=1$ and

$$
c_1(K)=\frac1{\ell-1}.
\tag{6.5}
$$

The equality of (6.5) with the separation radius is special to $e_K=1$. Over a ramified base, the separation radius is $e_K/(\ell-1)$, whereas the upper cutoff also contains $e_K-1$. That correction records the passage from the first integral congruence to positive upper time. Omitting it would give a false base-change rule.

The theorem remains valid for $\ell=2$. It then says $c_n(K)=e_K(n+1)-1$. The low-weight Fontaine--Laffaille classification used later requires $\ell>2$, but the Hopf-algebra and ramification proof above does not.

### 6.3 Endpoints, strict inequalities, and optimality

The assertion is triviality for $u>c_n(K)$, not necessarily at $u=c_n(K)$. Upper filtrations are step functions, and a universal congruence argument cannot in general decide the endpoint. This distinction disappears after integration, because one point has measure zero.

The separation radius is sharp for $\mu_\ell$, but the upper cutoff need not be attained by its cutout field. Over $\mathbf Q_\ell$, the field $\mathbf Q_\ell(\zeta_\ell)$ is tame for odd $\ell$, so its last positive upper break is $0$, while the universal bound is $1/(\ell-1)$. A model may contain points at the critical distance without Galois moving them at the maximal permitted depth.

Rank never appears in (6.2). A direct matrix estimate may bound $[K(M):K]$ by the order of an automorphism group, but it cannot prevent a fixed cyclic subgroup from occurring at arbitrary depth. Finite flatness controls the support of the ramification filtration before its height is counted.

### 6.4 Small-height interpretation

Suppose $M$ has order $\ell$. The small-height classification writes a model by Oort--Tate data with an integral exponent $0\leq r\leq e_K$. Its generic inertia character is tame. Thus the actual positive upper break is zero for the one-dimensional generic character, much smaller than (6.4). The universal theorem becomes essential in higher height and, especially, for nonsplit extensions: their diagonal characters may be tame while an off-diagonal cocycle is wild.

If such a middle representation has a finite-flat model killed by $\ell$, Theorem 6.1 bounds that cocycle by the same $c_1(K)$, independently of the number of successive factors. Without the middle model, extensions of two trivial characters can cut out cyclic degree-$\ell$ extensions with arbitrarily large upper break. The finite-flat hypothesis controls the extension class, not just its constituents.

## 7. Different and discriminant bounds

### 7.1 The local different theorem

**Theorem 7.1 (Fontaine--Raynaud different bound).** In the setting of Theorem 6.1, let

$$
L=K(M),\qquad e=e(L/K),\qquad f=f(L/K),\qquad d=d(L/K).
$$

Then

$$
\boxed{
d\leq e\,e_K\left(n+\frac1{\ell-1}\right)-1,}
\tag{7.1}
$$

$$
\boxed{
\frac de\leq e_K\left(n+\frac1{\ell-1}\right)-\frac1e
<e_K\left(n+\frac1{\ell-1}\right),}
\tag{7.2}
$$

and

$$
\boxed{
\delta(L/K)=fd
\leq f\left(e\,e_K\left(n+\frac1{\ell-1}\right)-1\right).}
\tag{7.3}
$$

**Proof.** By (6.3), the upper groups vanish above

$$
R=e_K\left(n+\frac1{\ell-1}\right)-1.
$$

Proposition 3.1 gives

$$
d\leq(e-1)+eR
=e\,e_K\left(n+\frac1{\ell-1}\right)-1.
$$

Dividing by $e$ gives (7.2), and $\delta=fd$ gives (7.3). $\square$

For $n=1$ and $K=\mathbf Q_\ell$,

$$
\frac de<1+\frac1{\ell-1}=\frac\ell{\ell-1}.
\tag{7.4}
$$

The number $\ell/(\ell-1)$ is not the last upper break. It is the tame baseline, strictly below $1$, plus the positive-depth allowance $1/(\ell-1)$.

### 7.2 Refinements from the actual filtration

The universal estimate discards the sizes of the upper groups. If they are known, use the exact identity

$$
\frac de
=1-\frac1e+
\int_0^{c_n(K)}
\left(1-\frac1{|G^u|}\right)du.
\tag{7.5}
$$

If $L/K$ is unramified, $d=0$. If it is tamely ramified,

$$
d=e-1,
\qquad \frac de=1-\frac1e.
\tag{7.6}
$$

If the image of wild inertia has order at most $H$, then the integrand is at most $1-1/H$ on positive depth, yielding

$$
\frac de\leq1-\frac1e+
\left(1-\frac1H\right)c_n(K).
\tag{7.7}
$$

Such refinements are useful for small matrix images. They are deductions from the actual filtration, not replacements for the finite-flat cutoff.

A weakly ramified extension provides a useful intermediate test. By definition its second lower group is trivial, so

$$
d=(|G_0|-1)+(|G_1|-1).
\tag{7.8}
$$

If it is totally ramified and $|G_1|=w$, then

$$
\frac de=1-\frac1e+\frac{w-1}{e}.
$$

This is normally much smaller than a bound obtained by replacing the entire upper integrand by $1$. It also checks the endpoint convention: the wild group occupies one lower interval beyond inertia, and its contribution is counted exactly once. Whenever a finite-flat torsion field is independently known to be weakly ramified, this exact formula should replace (7.2).

### 7.3 Conductors and faithful actions

For a characteristic-zero representation $V$ of a finite local Galois group, the Swan conductor is

$$
\operatorname{Sw}(V)
=\int_0^\infty\operatorname{codim}V^{G^u}\,du.
\tag{7.9}
$$

If $V$ is faithful and has last positive upper break $R(V)$, then on every interval where $G^u\ne1$ at least one dimension moves. Hence

$$
R(V)\leq\operatorname{Sw}(V)
\leq(\dim V)R(V).
\tag{7.10}
$$

The regular representation of $G=\operatorname{Gal}(L/K)$ is faithful, and its Artin conductor equals the discriminant exponent $\delta(L/K)$. This recovers the conductor--discriminant identity, but it is not the route by which Theorem 7.1 was proved. The torsion module $M$ may have coefficient characteristic dividing $|G|$, so ordinary semisimple character theory is inappropriate on $M$ itself. The safe route is

$$
M\longrightarrow K(M)\longrightarrow
\text{ramification groups}\longrightarrow d(L/K).
$$

Faithfulness is indispensable in (7.10). Inflating a representation through a fixed quotient while enlarging its realization by a deep extension in the kernel leaves its conductor unchanged and makes the larger field discriminant arbitrarily large.

### 7.4 Examples and checks

For the constant group $\mathbf Z/\ell^n\mathbf Z$ with trivial action, $L=K$ and $d=0$. Every bound is strict and very coarse.

For $M=\mu_{\ell^n}(K^s)$ over $K=\mathbf Q_\ell$, the cutout field is cyclotomic. At level one and odd $\ell$ it is tame. At higher levels its normalized different grows linearly with $n$, in agreement with the linear growth of (7.2). This example will be calculated globally in Chapter 12.

As a failure test, take a cyclic degree-$\ell$ extension of $K$ with one upper break $m$. Then

$$
\frac de=(m+1)\left(1-\frac1\ell\right).
\tag{7.11}
$$

Indeed $G^u$ has order $\ell$ for $0<u\leq m$ and is trivial afterward, so (3.5) gives the formula. Letting $m$ grow proves that neither degree $\ell$ nor a unipotent $2\times2$ matrix shape bounds the different. Such an action cannot admit a finite-flat model killed by $\ell$ once $m>c_1(K)$.

## 8. Change of coefficients and exact constructions

### 8.1 Forgetting and extending scalars

Let $A$ be a finite commutative ring acting on $M$. Forgetting some or all of the coefficient action does not change the underlying Galois action, the cutout field, or its ramification. It merely changes which endomorphisms are recorded on a model.

For a homomorphism $A\to B$ of finite commutative rings, suppose $M$ has an $A$-linear finite-flat model. The finite-flat calculus constructs a $B$-linear model of

$$
B\otimes_AM.
\tag{8.1}
$$

Choose a finite free presentation $A^r\twoheadrightarrow B$. Then (8.1) is a quotient of $M^r$. Close the generic relation subgroup inside the product model and take the represented finite-flat quotient. Scalar endomorphisms of the free presentation preserve the relation closure and descend, producing the $B$-action. This construction does not require $B$ to be flat over $A$.

If $\ell^nM=0$, then $\ell^n(B\otimes_AM)=0$. Theorems 6.1 and 7.1 therefore apply with the same $n$. Moreover

$$
K(B\otimes_AM)\subseteq K(M),
$$

because every Galois element acting trivially on $M$ acts trivially after tensoring. Scalar extension can make the action less faithful, but never introduces a new Galois action not already present on $M$. It may nevertheless form a larger compositum than the field of any one selected coefficient constituent. In all cases the ramification cutoff cannot exceed the universal one.

### 8.2 Coefficient quotients

Let $I\subset A$ be an ideal. The quotient

$$
M/IM
\tag{8.2}
$$

is a Galois quotient of $M$, so its cutout field is a subfield of $K(M)$. Integrally, close $IM$ in a chosen model and quotient. This construction is necessary because a raw scheme-theoretic image or kernel of multiplication by $I$ need not be flat.

Upper numbering gives two proofs of stability. The model proof applies Theorem 6.1 directly to (8.2). The field proof observes that upper groups pass to quotients, so a cutoff for $K(M)/K$ descends to $K(M/IM)/K$. The second proof also shows that any sharper cutoff known for $M$ survives coefficient reduction.

For a stable $\mathcal O$-lattice $T$ and an open ideal $I\subset\mathcal O$, choose $n$ with $\ell^n\in I$. Then $T/IT$ is a quotient of $T/\ell^nT$. If the latter is finite flat, so is the former. Its most economical ramification bound uses the least $a$ such that $\ell^a(T/IT)=0$, not the arbitrary $n$ used to present the quotient.

### 8.3 Duality, products, and exact middle terms

Cartier duality carries a model of $M$ to a model of

$$
M^*(1)=\operatorname{Hom}(M,\mu_{\ell^n}(K^s)).
\tag{8.3}
$$

This module is killed by $\ell^n$, so it has the same universal cutoff. Its cutout field need not equal $K(M)$: the constant group and $\mu_\ell$ are dual but have different generic actions. A self-dual pairing can identify the two modules and then identifies their fields, but this is additional structure.

Finite products give the maximum principle. If $M_i$ is killed by $\ell^{n_i}$ and finite flat, then

$$
M=\bigoplus_iM_i
$$

is finite flat and killed by $\ell^n$ for $n=\max_i n_i$. Hence the compositum of all $K(M_i)$ satisfies the single cutoff $c_n(K)$. Applying separate different bounds and multiplying them would count the same ramification depth repeatedly.

Finally, every term in a supplied finite-flat exact sequence inherits the appropriate bound. The converse statement is deliberately absent: finite-flat endpoints do not make every generic middle extension finite flat.

### 8.4 A coefficient-stability theorem

**Theorem 8.1 (stability under coefficient operations).** Let $M$ be a finite-flat $G_K$-module killed by $\ell^n$. The Fontaine--Raynaud upper-break and different bounds with exponent $n$ are preserved under:

1. restriction of coefficient scalars;
2. extension along a homomorphism of finite commutative coefficient rings;
3. coefficient quotients and, more generally, Galois subquotients;
4. finite direct sums, with $n$ replaced by the maximum exponent;
5. Cartier duality;
6. every generic term of a supplied faithfully flat exact sequence of finite-flat models.

**Proof.** Restriction does not change the action. Extension is modeled by products, closure, and quotient as in Section 8.1. Subquotients are modeled by schematic closure and represented quotient. Products and duality preserve finite local freeness and the stated exponents. Exact generic terms are modeled by the given integral sequence. Theorems 6.1 and 7.1 then apply in every case. For subquotients and composita, Herbrand quotient compatibility gives the same statements directly on cutout fields. $\square$

The theorem depends on the exponent, not on coefficient rank, residue-field degree, or the number of summands. This is the precise sense in which the discriminant estimate is stable under change of coefficients.

## 9. Ground-field change, subfields, and towers

### 9.1 Restriction to a larger local field

Let $K'/K$ be finite, with relative ramification index $a=e(K'/K)$. Base change of a finite-flat model from $\mathcal O_K$ to $\mathcal O_{K'}$ models the restricted $G_{K'}$-module. Since

$$
e_{K'}=v_{K'}(\ell)=a e_K,
\tag{9.1}
$$

Theorem 6.1 gives

$$
G_{K'}^u\text{ acts trivially on }M
\quad\text{for}\quad
u>a e_K\left(n+\frac1{\ell-1}\right)-1.
\tag{9.2}
$$

This is a new bound in the upper numbering normalized over $K'$. One should not compare its numerical index to (6.2) without applying the Herbrand function of $K'/K$: restriction to a ramified subgroup changes the upper clock. Formula (9.1) is the correct direct calculation.

If $K'/K$ is unramified, $a=1$. The cutoff is unchanged, inertia is identified, and upper ramification groups at positive indices agree under restriction. If $K'/K$ is ramified, the enlarged valuation ring may admit models which do not descend. Thus finite flatness after ramified base change is only potential finite flatness and gives no downstairs theorem without effective integral descent data.

### 9.2 Quotient fields and unramified base change

Let $L=K(M)$ and let $E$ be an intermediate field which is Galois over $K$. Then $\operatorname{Gal}(E/K)$ is a quotient of $\operatorname{Gal}(L/K)$, so

$$
\operatorname{Gal}(E/K)^u
=\operatorname{im}\bigl(\operatorname{Gal}(L/K)^u\bigr).
\tag{9.3}
$$

Every upper cutoff descends. Applying Proposition 3.1 to $E/K$ gives its own different bound with its actual ramification index. In particular, all cutout fields of subquotients of $M$ inherit the same degree-free normalized ceiling.

Now let $K'/K$ be unramified and choose a field factor $L'$ of $L\otimes_KK'$, equivalently the compositum belonging to one chosen pair of embeddings into a common separable closure. The relative ramification index, lower groups, upper groups, and different exponent are unchanged; only the residue degree can change. This can be proved by taking the maximal unramified and totally ramified parts: unramified scalar extension changes the residue field and leaves a chosen uniformizer and all its conjugate differences unchanged. Hence

$$
d(L'/K')=d(L/K),\qquad e(L'/K')=e(L/K),
\tag{9.4}
$$

provided the displayed $L'$ corresponds to the chosen factor. If the tensor product splits, the assertion is made factor by factor; the discriminant of the full product is the product of their discriminants.

### 9.3 Transitivity of differents

For a tower of finite separable local extensions

$$
K\subseteq E\subseteq L,
$$

trace transitivity gives

$$
\mathfrak D_{L/K}
=\mathfrak D_{L/E}\,
\mathfrak D_{E/K}\mathcal O_L.
\tag{9.5}
$$

Taking $v_L$ yields

$$
d(L/K)=d(L/E)+e(L/E)d(E/K).
\tag{9.6}
$$

**Proof.** The trace-dual lattice of $\mathcal O_L$ over $\mathcal O_K$ is

$$
\operatorname{Hom}_{\mathcal O_K}(\mathcal O_L,\mathcal O_K).
$$

By adjunction and trace transitivity it is the $\mathcal O_E$-dual of $\mathcal O_L$ tensored with the $\mathcal O_K$-dual of $\mathcal O_E$. Identifying these rank-one fractional ideals with inverse differents gives the inverse of (9.5); invert the ideals to obtain (9.5). The valuation of an ideal extended from $E$ is multiplied by $e(L/E)$, giving (9.6). $\square$

Dividing (9.6) by $e(L/K)=e(L/E)e(E/K)$ gives the normalized identity

$$
\frac{d(L/K)}{e(L/K)}
=\frac{d(E/K)}{e(E/K)}
+\frac1{e(E/K)}
\frac{d(L/E)}{e(L/E)}.
\tag{9.7}
$$

This formula is the exact tower ledger. A top-stage cost is discounted by the ramification already accumulated below. Adding two unnormalized local bounds without this factor overcounts.

### 9.4 Stepwise finite-flat towers

Suppose

$$
K=K_0\subset K_1\subset\cdots\subset K_s
\tag{9.8}
$$

and each $K_i/K_{i-1}$ is cut out by a finite-flat module over $\mathcal O_{K_{i-1}}$ killed by $\ell^{n_i}$. Let

$$
e_i=e(K_i/K_{i-1}),\qquad
e_{K_{i-1}}=v_{K_{i-1}}(\ell).
$$

Theorem 7.1 and repeated use of (9.7) give

$$
\frac{d(K_s/K)}{e(K_s/K)}
<\sum_{i=1}^s
\frac{e_{K_{i-1}}}{e(K_{i-1}/K)}
\left(n_i+\frac1{\ell-1}\right).
\tag{9.9}
$$

But $e_{K_{i-1}}=e(K_{i-1}/K)e_K$, so this simplifies to

$$
\frac{d(K_s/K)}{e(K_s/K)}
<e_K\sum_{i=1}^s
\left(n_i+\frac1{\ell-1}\right).
\tag{9.10}
$$

**Proof.** At stage $i$,

$$
\frac{d(K_i/K_{i-1})}{e_i}
<e_{K_{i-1}}\left(n_i+\frac1{\ell-1}\right).
$$

When inserted into the tower identity, this term is divided by $e(K_{i-1}/K)$. Summing proves (9.9), and multiplicativity of absolute ramification indices proves (9.10). $\square$

This stability statement is conditional at every step: the relative action which cuts out $K_i/K_{i-1}$ must itself have a finite-flat group model over the current valuation ring. A base-changed model of a full torsion module does not automatically turn the affine kernel between two torsion levels into such a relative group. Chapter 13 will return to this warning.

Two elementary towers clarify (9.7). If $E/K$ is unramified, then $e(E/K)=1$ and $d(E/K)=0$, so

$$
\frac{d(L/K)}{e(L/K)}
=\frac{d(L/E)}{e(L/E)}.
$$

An unramified layer changes residue degree but costs nothing after normalization. If instead $E/K$ is ramified and $L/E$ is unramified, the top term vanishes and the normalized cost is exactly that of $E/K$. Thus adjoining an unramified layer above or below does not alter the normalized different of the ramified part. By contrast, two genuinely ramified stages both contribute, with the upper stage discounted by the lower ramification index as in (9.7).

There is also a compositum warning. Given two finite-flat fields $L_1/K$ and $L_2/K$ at the same exponent, their compositum is best treated by the product model, which gives one upper cutoff. Applying different transitivity through $L_1L_2/L_1/K$ would require a relative finite-flat hypothesis at the top and can give a worse sum even when it is available. The product argument and the tower argument answer different questions: the former controls simultaneous generic data over one base; the latter controls independently modeled successive data over changing bases.

## 10. Fontaine--Laffaille realizations

### 10.1 The unramified low-weight range

Assume now that

$$
\ell>2,\qquad k\text{ is finite of characteristic }\ell,
\qquad W=W(k),\qquad K_0=W[1/\ell].
\tag{10.1}
$$

Then $e_{K_0}=1$. The integral Fontaine--Laffaille equivalence in weights $[0,1]$ identifies admissible torsion divided filtered modules with finite locally free commutative $\ell$-power-order groups over $W$, with arrows reversed. Generic realization gives exactly the finite-flat torsion representations of $G_{K_0}$.

Consequently every torsion realization $T_{\mathrm{FL}}(D)$ killed by $\ell^n$ satisfies

$$
T_{\mathrm{FL}}(D)^{G_{K_0}^u}=T_{\mathrm{FL}}(D)
\quad\text{pointwise for}\quad
u>n-1+\frac1{\ell-1}.
\tag{10.2}
$$

For $n=1$, the cutoff is $1/(\ell-1)$ and the normalized different is strictly less than $\ell/(\ell-1)$. The filtered description is a classification of the objects satisfying the geometric hypothesis; the proof of (10.2) remains the integral-distance argument of Chapters 4--6.

The logical direction matters. Starting from $D$, essential surjectivity produces a finite-flat group $\mathcal G(D)$ whose geometric generic points are $T_{\mathrm{FL}}(D)$. This is exactly the hypothesis of Theorem 6.1. Starting instead from a finite-flat representation $V$, the anti-equivalence reconstructs a unique divided filtered object $D(V)$. Thus (10.2) applies to all finite-flat torsion representations in this range, not merely to those initially presented by filtered data. Exactness ensures that a stable submodule of $V$ corresponds to a filtered quotient, while a stable quotient corresponds to a filtered subobject; the reversal of arrows does not change the exponent or the ramification conclusion.

The two atomic filtered lines recover the constant and multiplicative examples. Weight zero realizes $\mathbf Z/\ell^n\mathbf Z$; weight one realizes $\mu_{\ell^n}$. Mixed extensions between the two weights give finite-flat nonsplit Galois modules. The upper-break theorem treats these mixed objects without splitting them, which is precisely why it controls ramification invisible on the two atomic factors.

### 10.2 Stable lattices and all finite quotients

Let $T$ be a finite free $\mathbf Z_\ell$-lattice with continuous $G_{K_0}$-action. In the height-two range, the integral equivalence proves that the following data match:

1. a finite free strongly divisible object of weights $[0,1]$;
2. a stable lattice $T$ for which every $T/\ell^nT$ is finite flat;
3. a compatible system of finite-flat models for all levels.

At each fixed level, Theorem 6.1 gives

$$
G_{K_0}^u\text{ acts trivially on }T/\ell^nT
\quad(u>n-1+1/(\ell-1)).
\tag{10.3}
$$

If $\mathcal O$ is the ring of integers in a finite coefficient extension and $I\subset\mathcal O$ is open, choose the least $a(I)$ with $\ell^{a(I)}\in I$. The compatible-quotient theorem supplies a finite-flat model of $T/IT$, and

$$
G_{K_0}^u\text{ acts trivially on }T/IT
\quad(u>a(I)-1+1/(\ell-1)).
\tag{10.4}
$$

Thus the estimate is compatible with arbitrary, possibly nonflat, coefficient reduction.

### 10.3 Height two and compatible coefficients

In rank two and Hodge type $(0,1)$, a perfect alternating pairing identifies the representation with its Tate-twisted dual and forces cyclotomic determinant. Ordinary and local-local special fibers are both allowed. A stable line closes inside the finite-flat model, and the quotient retains the finite-flat property. Therefore the line, quotient, determinant, and full nonsplit middle term all satisfy their applicable bounds.

The full middle term matters most. If a basis makes a residual representation triangular,

$$
\bar\rho(\sigma)=
\begin{pmatrix}
\chi_1(\sigma)&c(\sigma)\\
0&\chi_2(\sigma)
\end{pmatrix},
\tag{10.5}
$$

finite flatness bounds the ramification carried by $c$, not merely the tame inertia of $\chi_1$ and $\chi_2$. Changing coefficient fields, reducing by an ideal, or taking a stable subquotient preserves this control by Theorem 8.1.

### 10.4 What the linear classification adds

The filtered classification adds uniqueness and functorial compatibility in its safe range. Because $e_{K_0}=1<\ell-1$, the generic fiber determines the marked finite-flat model uniquely. Coefficient actions, unramified ground-field base change, duality, stable lines, and compatible quotients can therefore be transported without choosing unrelated models at different levels.

Unramified ground-field extension is particularly clean. If $k\subseteq k'$ is a finite extension of finite fields and $K_0'=W(k')[1/\ell]$, then base change of the divided filtered object and base change of the finite-flat group agree. The restricted representation over $G_{K_0'}$ therefore has the same exponent and the same numerical cutoff because both absolute ramification indices are one. In the reverse direction, descent requires semilinear descent data on the full filtered object or finite-flat group; invariance of the generic isomorphism class alone is not enough.

Coefficient extension has a different variance. On the contravariant filtered side, extending a finite projective coefficient algebra $A$ to $B$ uses the dual module $B^\vee\otimes_A-$ so that generic realization becomes $B\otimes_A-$. For a nonflat coefficient quotient, the correct filtered object is the admissible annihilator characterized by the generic quotient. These constructions explain categorically the model-theoretic closure and quotient procedure of Chapter 8. In either language, the resulting Galois module is still killed by the expected power of $\ell$ and hence receives the same ramification bound.

None of these conclusions extends silently to a ramified base or to $\ell=2$. The general ramification theorem still holds whenever a model exists, but the particular low-weight classification used to produce and compare those models has the hypotheses (10.1). This separation keeps the scope of each theorem exact.

## 11. Global root discriminants

### 11.1 The global localization formula

Let $F$ be a number field and let $L/F$ be finite Galois. The absolute discriminants satisfy

$$
|D_L|=|D_F|^{[L:F]}
N_{F/\mathbf Q}(\mathfrak d_{L/F}).
\tag{11.1}
$$

For a finite place $v$ choose $w\mid v$ and put

$$
e_v=e(L_w/F_v),\qquad
f_v=f(L_w/F_v),\qquad
d_v=d(L_w/F_v),
$$

with $g_v$ places above $v$. The localization of the relative discriminant has exponent

$$
g_vf_vd_v
\tag{11.2}
$$

at $v$, because the completed algebra is the product of $g_v$ conjugate field extensions, each with local discriminant exponent $f_vd_v$.

Define

$$
\operatorname{rd}(E)=|D_E|^{1/[E:\mathbf Q]}.
$$

Taking the $[L:\mathbf Q]$th root of (11.1), using

$$
[L:F]=g_ve_vf_v,
$$

and collecting the $v$-factor proves

$$
\boxed{
\operatorname{rd}(L)
=\operatorname{rd}(F)
\prod_v(Nv)^{d_v/(e_v[F:\mathbf Q])}.}
\tag{11.3}
$$

Only ramified places contribute. Formula (11.3) is the global form of the cancellation $\delta/[L_w:F_v]=d/e$.

### 11.2 The sharp finite-flat estimate

Let $M$ be a finite $G_F$-module killed by $\ell^n$, put $L=F(M)$, and assume:

- for every $v\mid\ell$, the restricted module admits a finite-flat model over $\mathcal O_{F_v}$;
- $L/F$ is unramified away from $\ell$.

Write

$$
e_v^0=v_{F_v}(\ell)=e(F_v/\mathbf Q_\ell),
\qquad Nv=\ell^{f_v^0}.
$$

The local theorem gives

$$
\frac{d_v}{e_v}
<e_v^0\left(n+\frac1{\ell-1}\right).
\tag{11.4}
$$

Substitution in (11.3) shows that the exponent of $\ell$ in the relative root-discriminant factor is less than

$$
\frac1{[F:\mathbf Q]}
\sum_{v\mid\ell}f_v^0e_v^0
\left(n+\frac1{\ell-1}\right)
=n+\frac1{\ell-1},
$$

because

$$
\sum_{v\mid\ell}e_v^0f_v^0=[F:\mathbf Q].
$$

We have proved the central global estimate.

**Theorem 11.1 (finite-flat root-discriminant bound).** Under the preceding hypotheses,

$$
\boxed{
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\,
\ell^{\,n+1/(\ell-1)}.}
\tag{11.5}
$$

At level $\ell$,

$$
\boxed{
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\,
\ell^{\ell/(\ell-1)}.}
\tag{11.6}
$$

The estimate is sharp in its normalization: it retains the strict local term $-1/e_v$, incorporates all primes over $\ell$ through the absolute-degree identity, and keeps ramification already present in $F$ exactly in $\operatorname{rd}(F)$. A ramified base field introduces no extra coefficient-prime factor beyond these terms.

It is useful to see the cancellation one place at a time. The local cutoff at $v$ is

$$
e_v^0\left(n+\frac1{\ell-1}\right)-1.
$$

Adding the tame baseline $1-1/e_v$ gives

$$
e_v^0\left(n+\frac1{\ell-1}\right)-\frac1{e_v}.
\tag{11.7}
$$

The negative final term is the source of strictness. After multiplication by $f_v^0/[F:\mathbf Q]$ and summation, the main terms become exactly $n+1/(\ell-1)$. Dropping the $-1$ from the local upper cutoff before adding the tame term would produce the weaker exponent $n+1+1/(\ell-1)$ and would lose the characteristic Fontaine constant.

### 11.3 Auxiliary ramification away from the coefficient prime

Let $S$ be a finite set of places of $F$ not dividing $\ell$. Suppose $L/F$ is unramified outside $S$ and the places above $\ell$. If the local field at $v\in S$ has upper groups trivial for $u>R_v$, Proposition 3.1 and (11.3) give

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\,
\ell^{\,n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.}
\tag{11.8}
$$

At a tame place the exact contribution is

$$
(Nv)^{(1-1/e_v)/[F:\mathbf Q]},
\tag{11.9}
$$

which is better than inserting $R_v=0$ into the coarse factor. If the full upper filtration is known, replace $1+R_v$ by

$$
1-\frac1{e_v}
+\int_0^{R_v}
\left(1-\frac1{|G_v^u|}\right)du.
\tag{11.10}
$$

Saying only that a representation is ramified at $S$ does not bound its discriminant. One needs tame inertia, a last-break cutoff, or equivalent information at every place in $S$.

### 11.4 Subfields and several representations

If $E$ is a subfield of $L$, then discriminant transitivity gives

$$
\operatorname{rd}(E)\leq\operatorname{rd}(L).
\tag{11.11}
$$

Indeed

$$
|D_L|=|D_E|^{[L:E]}
N_{E/\mathbf Q}(\mathfrak d_{L/E}),
$$

and the norm factor is a positive integer. Thus the Galois field cut out by the full module also bounds every orbit field or fixed subfield.

For finitely many modules $M_1,\ldots,M_s$ of exponent dividing $\ell^n$, form their direct sum. The product of local finite-flat models is finite flat and its global field is the compositum

$$
F(M_1\oplus\cdots\oplus M_s)
=F(M_1)\cdots F(M_s).
$$

If the same ramification hypotheses hold, the compositum satisfies (11.5) once, independently of $s$. This closure under finite composita is indispensable when a discriminant bound is later used to constrain an entire family of torsion fields.

## 12. Arithmetic examples

### 12.1 Constant and cyclotomic modules

The constant module $\mathbf Z/\ell^n\mathbf Z$ with trivial action has the constant finite-flat model. It cuts out no extension and makes every upper group and different exponent zero.

The Cartier-dual example is

$$
M=\mu_{\ell^n}(\overline{\mathbf Q}),
$$

with model $\mu_{\ell^n}$. Its cutout field over $\mathbf Q$ is $\mathbf Q(\zeta_{\ell^n})$. For odd $\ell$, the cyclotomic discriminant formula is

$$
|D_{\mathbf Q(\zeta_{\ell^n})}|
=\ell^{\ell^{n-1}(n\ell-n-1)}.
\tag{12.1}
$$

We recall the calculation. The degree is

$$
\varphi(\ell^n)=\ell^{n-1}(\ell-1).
$$

For a primitive root $\zeta$, differentiating

$$
\Phi_{\ell^n}(X)
=\frac{X^{\ell^n}-1}{X^{\ell^{n-1}}-1}
$$

at $\zeta$ gives

$$
\Phi_{\ell^n}'(\zeta)
=\frac{\ell^n\zeta^{-1}}
{\zeta^{\ell^{n-1}}-1}.
$$

The norm of the denominator is $\ell^{\ell^{n-1}}$: its conjugates group into $\ell^{n-1}$ copies of the nontrivial $\ell$th roots, whose product $\Phi_\ell(1)$ is $\ell$. Taking the norm of the numerator and subtracting the denominator exponent yields (12.1). The root discriminant is therefore

$$
\boxed{
\operatorname{rd}(\mathbf Q(\zeta_{\ell^n}))
=\ell^{\,n-1/(\ell-1)}.}
\tag{12.2}
$$

This lies below the universal finite-flat bound

$$
\ell^{\,n+1/(\ell-1)}.
$$

Both exponents grow linearly with $n$. At $n=1$, (12.2) records a tame extension and has exponent $1-1/(\ell-1)$. The example simultaneously checks the tower growth, the tame baseline, and the impossibility of a level-independent bound.

### 12.2 Good-reduction abelian varieties

Let $A/F$ be an abelian variety of dimension $g$. Suppose $A$ has good reduction at a place $v\mid\ell$. Its abelian scheme over $\mathcal O_{F_v}$ has finite locally free torsion

$$
\mathcal A[\ell^n],
$$

whose generic points are $A[\ell^n]$. Thus the local module is finite flat, has exponent $\ell^n$, and satisfies the cutoff

$$
u>e(F_v/\mathbf Q_\ell)
\left(n+\frac1{\ell-1}\right)-1.
\tag{12.3}
$$

The bound is independent of $g$. Dimension affects the degree through

$$
\operatorname{Aut}(A[\ell^n])
\subseteq\operatorname{GL}_{2g}(\mathbf Z/\ell^n\mathbf Z),
$$

but not the local ramification depth.

At a finite place $v\nmid\ell$ of good reduction, $\mathcal A[\ell^n]$ is finite étale over the valuation ring because $\ell$ is invertible. Its generic module is therefore unramified. Hence, if $A$ has good reduction at every finite place, Theorem 11.1 gives

$$
\operatorname{rd}(F(A[\ell^n]))
<\operatorname{rd}(F)\ell^{\,n+1/(\ell-1)}.
\tag{12.4}
$$

More generally, bad-reduction places must be inserted with their actual tame or upper-break costs. The discriminant of a Weierstrass or polarization equation is not the field discriminant in (12.4); reduction theory connects them only by determining the Galois action.

### 12.3 Two-dimensional residual representations

Let

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(\mathbf F_{\ell^f})
$$

be continuous, finite flat at every $v\mid\ell$, and unramified away from $\ell$. Let $L$ be the fixed field of its kernel. The underlying additive group is killed by $\ell$, regardless of the coefficient degree $f$. Therefore

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{\ell/(\ell-1)}.
\tag{12.5}
$$

Extending the residue coefficient field does not worsen this exponent. Nor does passing to a stable line, quotient, semisimplification, dual, or determinant. If the representation is a nonsplit extension, the bound applies to its full cutout field because the full middle module, not merely its characters, is assumed finite flat.

Suppose instead that ramification away from $\ell$ is tame at one place $q$ with inertia order $m$. Then

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{\ell/(\ell-1)}
(Nq)^{(1-1/m)/[F:\mathbf Q]}.
\tag{12.6}
$$

For a quadratic tame character, the auxiliary exponent is $1/(2[F:\mathbf Q])$.

### 12.4 A complete numerical example

Take $F=\mathbf Q$, $\ell=3$, and a finite $G_{\mathbf Q}$-module $M$ killed by $3$, finite flat at $3$, unramified outside $2$ and $3$, and tamely ramified at $2$ with inertia order $2$. Then

$$
\operatorname{rd}(\mathbf Q(M))
<3^{3/2}2^{1/2}
=3\sqrt6
\approx7.3485.
\tag{12.7}
$$

Every factor has a distinct source. The exponent $3/2$ is $1+1/(3-1)$: tame baseline plus the finite-flat positive depth at the coefficient prime. The exponent $1/2$ at $2$ is the exact normalized cost of quadratic tame inertia. There is no base-field factor because $\operatorname{rd}(\mathbf Q)=1$.

If the action at $2$ is unramified, remove $2^{1/2}$ rather than retaining a harmless-looking overestimate. If the ramification at $2$ is wild with no specified upper cutoff, no numerical discriminant ceiling follows from the stated data. If one passes to a subfield of $\mathbf Q(M)$, (11.11) preserves the bound.

## 13. Level towers and uniformity

### 13.1 Full-level bounds

Let $T$ be a free $\mathbf Z_\ell$-module of rank $r$ with continuous $G_F$-action, and put

$$
M_n=T/\ell^nT,
\qquad F_n=F(M_n).
\tag{13.1}
$$

Assume that for every $v\mid\ell$ and every $n$, the local module $M_n$ has a finite-flat model. Assume also, for simplicity, that $F_n/F$ is unramified away from $\ell$. Then

$$
F_1\subseteq F_2\subseteq\cdots
\tag{13.2}
$$

and Theorem 11.1 gives the levelwise estimate

$$
\boxed{
\operatorname{rd}(F_n)
<\operatorname{rd}(F)\ell^{\,n+1/(\ell-1)}.}
\tag{13.3}
$$

At a place $v\mid\ell$, the local last upper break of $(F_n)_w/F_v$ is at most

$$
e(F_v/\mathbf Q_\ell)
\left(n+\frac1{\ell-1}\right)-1.
\tag{13.4}
$$

No compatibility among arbitrarily chosen models is needed for these fixed-level conclusions. A compatible system, such as torsion in an abelian scheme or a Fontaine--Laffaille lattice, makes the hypotheses natural and makes coefficient maps integral, but the numerical theorem is applied one level at a time.

### 13.2 Successive degrees

Reduction from level $n+1$ to level $n$ gives an injection

$$
\operatorname{Gal}(F_{n+1}/F_n)
\hookrightarrow
\ker\left(
\operatorname{GL}_r(\mathbf Z/\ell^{n+1}\mathbf Z)
\to\operatorname{GL}_r(\mathbf Z/\ell^n\mathbf Z)
\right).
\tag{13.5}
$$

Every element of the kernel has the form

$$
1+\ell^nA\pmod{\ell^{n+1}},
\qquad A\in M_r(\mathbf F_\ell).
$$

Multiplication corresponds to addition of $A$ modulo $\ell$, so the kernel has order $\ell^{r^2}$. Consequently

$$
[F_{n+1}:F_n]\leq\ell^{r^2},
\qquad
[F_n:F_1]\leq\ell^{r^2(n-1)}.
\tag{13.6}
$$

This is a degree statement. It uses the rank of $T$ and no finite-flat geometry.

### 13.3 What cannot be uniform

Three assertions must be distinguished:

1. the rank $r$ is fixed;
2. the successive degrees $[F_{n+1}:F_n]$ are bounded;
3. the root discriminants or last upper breaks are bounded independently of $n$.

The first implies the second by (13.6). Neither implies the third. The cyclotomic lattice $\mathbf Z_\ell(1)$ has rank one and bounded step degrees, while (12.2) shows

$$
\operatorname{rd}(\mathbf Q(\zeta_{\ell^n}))
=\ell^{\,n-1/(\ell-1)}\longrightarrow\infty.
$$

The universal full-level estimate must grow with $n$.

One might try to view $F_{n+1}/F_n$ as a new level-$\ell$ finite-flat extension and apply a uniform step bound. This is valid only if the relative action which cuts out that field has a finite-flat group model over the valuation ring of the current field. The kernel in (13.5) is a finite set of affine lifts, not automatically the geometric points of such a group. Base change of the full model does not prove this additional assertion.

If a relative finite-flat model is independently supplied at every step, Chapter 9 applies. The absolute ramification index of the current base then grows, and the tower normalization (9.7) must be used; replacing it by the original $e_K$ at every unnormalized stage is incorrect.

### 13.4 Uniform composita at a fixed level

Fixed level behaves much better. Let $M_{1,n},\ldots,M_{s,n}$ be modules over the same number field, all killed by $\ell^n$, satisfying the same local finite-flat and auxiliary-ramification hypotheses. Their direct sum has a product model and cuts out the compositum

$$
F(M_{1,n})\cdots F(M_{s,n}).
$$

At each $v\mid\ell$ it has the single cutoff (13.4), and globally it has the single factor $\ell^{n+1/(\ell-1)}$. Thus any finite compositum at one fixed level has a bound independent of the number of representations.

An infinite compositum is not itself a finite number field, so it has no root discriminant in the preceding sense. What remains uniform is that every finite subcompositum satisfies the same ceiling. This is exactly the form required in arguments that compare local upper bounds with global lower bounds degree by degree.

## 14. The finite-flat discriminant package

### 14.1 The local package

The local theory may now be stated as one reusable theorem.

**Theorem 14.1 (local package).** Let $K/\mathbf Q_\ell$ be finite, normalize $v_K(K^\times)=\mathbf Z$, and put $e_K=v_K(\ell)$. Let $M$ be a finite continuous $G_K$-module killed by $\ell^n$ and admitting a finite-flat model over $\mathcal O_K$. Put

$$
L=K(M),\qquad e=e(L/K),\qquad f=f(L/K),\qquad d=d(L/K).
$$

Then:

1. $L/K$ is finite Galois with group the faithful image on $M$.
2. Its upper ramification groups vanish for

   $$
   u>e_K\left(n+\frac1{\ell-1}\right)-1.
   $$

3. Its different and discriminant exponents satisfy

   $$
   d\leq e\,e_K\left(n+\frac1{\ell-1}\right)-1,
   \qquad \delta=fd.
   $$

4. Its normalized local cost satisfies

   $$
   \frac de<e_K\left(n+\frac1{\ell-1}\right).
   $$

5. The same assertions, with the actual exponent, hold for coefficient changes, subquotients, finite direct sums, Cartier duals, unramified ground-field extension, and terms of supplied finite-flat exact sequences.
6. Under a ramified ground-field extension the theorem remains true after base change with the new absolute ramification index. Descent in the reverse direction requires effective integral descent data.

**Proof.** Parts 1--4 are Theorems 6.1 and 7.1. Part 5 is Theorem 8.1 and Section 9.2. Part 6 is Section 9.1. $\square$

### 14.2 The global package

**Theorem 14.2 (global package).** Let $F$ be a number field, let $M$ be a finite $G_F$-module killed by $\ell^n$, and put $L=F(M)$. Assume that $M$ is finite flat at every $v\mid\ell$, unramified outside the places above $\ell$ and a finite set $S$, and that for each $v\in S$ there is $R_v\geq0$ such that the local cutout field has upper groups trivial above $R_v$. Then

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\ell^{\,n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.}
\tag{14.1}
$$

At a tame $v\in S$, its factor may be replaced by

$$
(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

The same ceiling holds for every subfield of $L$. At a fixed exponent it also holds for every finite compositum of fields cut out by modules whose direct sum retains the stated local models and auxiliary cutoffs.

**Proof.** The local package at $v\mid\ell$, Proposition 3.1 at $v\in S$, and the localization identity (11.3) give (14.1). Tame refinement is (7.6). Subfield monotonicity is (11.11), and the compositum assertion follows from product models and (2.4). $\square$

### 14.3 Hypothesis and failure ledger

The chain of reasoning is reliable only when each hypothesis is kept with the step where it is used.

| Assertion | Hypothesis used | What fails without it |
|---|---|---|
| geometric points recover the generic group | characteristic-zero local field | a nonétale generic group can have too few points |
| integral exponent equals generic exponent | finite local freeness over a domain | a morphism can vanish generically but survive as vertical torsion |
| torsion-free congruence ball | commutative group law and $\ell$-power torsion | an arbitrary finite cover has no multiplication estimate |
| radius $e_K/(\ell-1)$ | mixed characteristic and (4.4) | in equal characteristic the linear $\ell$-term vanishes |
| quotient-compatible cutoff | upper numbering | lower numbering changes under every quotient |
| different formula (3.4) | finite Galois local extension with separable residue field | the classical group formula does not cover fierce residue growth |
| discriminant of the represented field | faithful cutout action | ramification hidden in a kernel is uncontrolled |
| coefficient stability | an actual model of the full object or supplied exact sequence | finite-flat endpoints do not control arbitrary extension classes |
| downstairs finite flatness | effective integral descent | potential finite flatness after ramified base change is weaker |
| low-weight linear classification | $\ell>2$ and absolutely unramified base | model uniqueness and the stated filtered category can fail |
| global finite-flat bound | local models at every $v\mid\ell$ and depth data elsewhere | a listed ramified prime can have arbitrarily large exponent |
| fixed-level compositum bound | a finite product model at the same exponent | separate coarse discriminant estimates add unnecessary costs |
| uniform tower bound | additional relative finite-flat models | bounded rank and bounded step degree do not bound depth |

The substantial imported results have now appeared with their hypotheses. Ramification theory supplies Herbrand quotient compatibility, Hilbert's different formula, conductor--discriminant identities, and transitivity. The finite-flat representation theory supplies marked models, schematic closure, represented quotients, coefficient actions, products, and Cartier duality. The small-height theory supplies the Oort--Tate interpretation and explains the ramification boundary. The integral Fontaine--Laffaille theory supplies essential surjectivity, unramified base change, and compatible coefficient quotients in weights zero and one. The new work of this book is the complete passage from integral distance through upper depth to local different and global root discriminant.

### 14.4 Conclusion

Finite flatness turns a qualitative extension property into a quantitative ramification theorem. The augmentation ideal measures how close generic torsion points can be. Multiplication by $\ell$ has a Frobenius-divisible expansion, which excludes nonzero points from the ball of radius $e_K/(\ell-1)$. Translation makes congruence clusters equal, and Herbrand's clock converts their lower displacement into the quotient-compatible cutoff

$$
e_K\left(n+\frac1{\ell-1}\right)-1.
$$

Hilbert's formula then adds the tame baseline and yields the normalized different ceiling

$$
\frac de<e_K\left(n+\frac1{\ell-1}\right).
$$

Every normalization has a role. The $-1$ in the upper cutoff cancels the first unit of the tame different. Residue degrees cancel when a local discriminant is divided by local degree. The absolute ramification indices of the primes over $\ell$ recombine to $[F:\mathbf Q]$. The surviving global statement is therefore

$$
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\ell^{\,n+1/(\ell-1)}
$$

when no other finite prime ramifies, with exact additional factors when auxiliary ramification is present.

The package is stable under the operations demanded by arithmetic representations: subquotients, coefficient change, duality, products, supplied exact sequences, unramified base change, and correctly normalized towers. It is deliberately not a statement that rank bounds depth, that graded factors control extension classes, that potential models descend, or that full torsion towers have bounded root discriminant. With those boundaries explicit, finite-flat integral geometry provides a sharp and reusable bridge from torsion representations to the discriminants of the fields they cut out.
