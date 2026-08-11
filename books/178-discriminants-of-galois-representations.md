# Discriminants of Galois Representations

## Contents

1. [From a finite action to a field](#1-from-a-finite-action-to-a-field)
   - [The arithmetic question](#11-the-arithmetic-question)
   - [Finite continuous modules and representations](#12-finite-continuous-modules-and-representations)
   - [The field cut out by an action](#13-the-field-cut-out-by-an-action)
   - [Several operations and several fields](#14-several-operations-and-several-fields)
2. [Local and global discriminants](#2-local-and-global-discriminants)
   - [Trace duality and the different](#21-trace-duality-and-the-different)
   - [Relative and absolute discriminants](#22-relative-and-absolute-discriminants)
   - [Root discriminants and normalization](#23-root-discriminants-and-normalization)
   - [Localizing the global discriminant](#24-localizing-the-global-discriminant)
3. [Towers, subfields, and composita](#3-towers-subfields-and-composita)
   - [Transitivity formulas](#31-transitivity-formulas)
   - [Root discriminants in towers](#32-root-discriminants-in-towers)
   - [Subfield monotonicity](#33-subfield-monotonicity)
   - [Composita and a useful inequality](#34-composita-and-a-useful-inequality)
4. [Ramification depth and the different](#4-ramification-depth-and-the-different)
   - [The two numberings revisited](#41-the-two-numberings-revisited)
   - [Hilbert's formula and its upper form](#42-hilberts-formula-and-its-upper-form)
   - [Cutoff bounds with exact constants](#43-cutoff-bounds-with-exact-constants)
   - [Tame, weakly ramified, and bounded-depth tests](#44-tame-weakly-ramified-and-bounded-depth-tests)
5. [Conductors and discriminants](#5-conductors-and-discriminants)
   - [The Artin conductor](#51-the-artin-conductor)
   - [Permutation and regular representations](#52-permutation-and-regular-representations)
   - [What a small conductor does and does not bound](#53-what-a-small-conductor-does-and-does-not-bound)
   - [Faithful families and conductor bounds](#54-faithful-families-and-conductor-bounds)
6. [Finite images and module constructions](#6-finite-images-and-module-constructions)
   - [Matrix bounds](#61-matrix-bounds)
   - [Filtrations and successive extensions](#62-filtrations-and-successive-extensions)
   - [Direct sums, subquotients, and fields](#63-direct-sums-subquotients-and-fields)
   - [Lattice quotients and level towers](#64-lattice-quotients-and-level-towers)
7. [Integral geometry and a torsion-free congruence ball](#7-integral-geometry-and-a-torsion-free-congruence-ball)
   - [Why generic matrices lose the decisive information](#71-why-generic-matrices-lose-the-decisive-information)
   - [The augmentation ideal estimate](#72-the-augmentation-ideal-estimate)
   - [Congruence of points](#73-congruence-of-points)
   - [From congruence to upper ramification](#74-from-congruence-to-upper-ramification)
8. [The finite-flat ramification theorem](#8-the-finite-flat-ramification-theorem)
   - [The local theorem](#81-the-local-theorem)
   - [The local different bound](#82-the-local-different-bound)
   - [Strictness, endpoints, and sharpness](#83-strictness-endpoints-and-sharpness)
   - [Why integrality is stronger than a conductor estimate](#84-why-integrality-is-stronger-than-a-conductor-estimate)
9. [Finite-flat constructions](#9-finite-flat-constructions)
   - [Chosen models and inherited models](#91-chosen-models-and-inherited-models)
   - [Cartier duals](#92-cartier-duals)
   - [Direct sums and exact extensions](#93-direct-sums-and-exact-extensions)
   - [Change of coefficients](#94-change-of-coefficients)
   - [Existence warnings](#95-existence-warnings)
10. [Examples at the residue characteristic](#10-examples-at-the-residue-characteristic)
   - [Constant and multiplicative models](#101-constant-and-multiplicative-models)
   - [Cyclotomic modules](#102-cyclotomic-modules)
   - [Good-reduction elliptic curves](#103-good-reduction-elliptic-curves)
   - [A tame auxiliary character](#104-a-tame-auxiliary-character)
11. [Globalization](#11-globalization)
   - [Local contributions to an absolute root discriminant](#111-local-contributions-to-an-absolute-root-discriminant)
   - [The finite-flat global bound](#112-the-finite-flat-global-bound)
   - [Auxiliary ramification away from $\ell$](#113-auxiliary-ramification-away-from-ell)
   - [A worked global estimate](#114-a-worked-global-estimate)
12. [Towers of torsion fields](#12-towers-of-torsion-fields)
   - [Full level and successive kernels](#121-full-level-and-successive-kernels)
   - [What is uniform and what must grow](#122-what-is-uniform-and-what-must-grow)
   - [Composita of several torsion modules](#123-composita-of-several-torsion-modules)
13. [The three-adic torsion-field ledger](#13-the-three-adic-torsion-field-ledger)
   - [The coefficient and exponent ledger](#131-the-coefficient-and-exponent-ledger)
   - [The strict residual field](#132-the-strict-residual-field)
   - [Tame ramification at two](#133-tame-ramification-at-two)
   - [Higher coefficient levels](#134-higher-coefficient-levels)
   - [Residual composita and obstruction fields](#135-residual-composita-and-obstruction-fields)
   - [What the three-adic argument receives](#136-what-the-three-adic-argument-receives)
14. [A theorem package for small ramification](#14-a-theorem-package-for-small-ramification)
   - [Local package](#141-local-package)
   - [Global package](#142-global-package)
   - [Tower package](#143-tower-package)
   - [Boundary with discriminant lower bounds](#144-boundary-with-discriminant-lower-bounds)
15. [Conclusion](#15-conclusion)

## 1. From a finite action to a field

### 1.1 The arithmetic question

A finite Galois representation carries two kinds of size. Its matrix image has a finite cardinality, but the field on which the representation becomes trivial also has an arithmetic size measured by its discriminant. These quantities are related only after ramification depth enters. A cyclic extension of fixed degree can have arbitrarily large discriminant, so group order alone is never enough. Conversely, a bound on depth without a finite image supplies no finite field to measure. The purpose of this book is to keep both ingredients visible and to turn geometric control of ramification into explicit field-theoretic inequalities.

The guiding situation is a number field $F$, a rational prime $\ell$, and a finite continuous representation

$$
\rho:G_F\longrightarrow\operatorname{Aut}_{\Lambda}(M),
$$

where $M$ is finite and $\Lambda$ is a finite coefficient ring. Its kernel cuts out a finite Galois extension $F(M)/F$. At places not dividing $\ell$, ordinary inertial or conductor information often controls the discriminant. At places above $\ell$, the decisive extra hypothesis is frequently that the local module is the generic fiber of a finite-flat group scheme. Integral geometry then constrains how close two distinct torsion points can be, and that congruence constraint forces a small last upper ramification break.

There are three normalization layers that must not be merged. A local different exponent is measured upstairs. A local discriminant exponent is measured downstairs and contains a residue-degree factor. A global root discriminant divides the exponent of every rational prime by the total absolute degree. Every later constant will be checked against these three layers.

The substantial prior inputs are exact. The earlier ramification theory supplies lower and upper numbering, Herbrand's quotient theorem, Hilbert's different formula, conductor--discriminant identities, and transitivity of differents. The earlier finite-flat discriminant theory supplies the closure and represented-quotient calculus for chosen models, the augmentation-ideal estimate, and the weighted cluster lemma that converts integral separation into an upper-break cutoff. We recall the relevant constructions and reproduce the numerical argument because the three-adic ledger depends on its endpoints and constants; no classification theorem or discriminant lower bound is being inserted tacitly.

### 1.2 Finite continuous modules and representations

Let $F$ be a field with separable closure $F^s$ and absolute Galois group $G_F$. A **finite continuous $G_F$-module** is a finite abelian group $M$ with continuous $G_F$-action, the target being discrete. Equivalently, the action homomorphism

$$
\rho_M:G_F\longrightarrow\operatorname{Aut}(M)
$$

has finite image and open kernel. If $M$ is free of rank $r$ over a finite ring $\Lambda$, a basis identifies the target with $\operatorname{GL}_r(\Lambda)$, but neither the kernel nor the field it defines depends on that basis.

More generally, a finite continuous representation on a finite set $X$ gives a homomorphism $G_F\to\operatorname{Perm}(X)$. The module structure is useful for subobjects, quotients, and duality, but the field-cutout construction needs only a finite faithful action.

Continuity is essential. An abstract homomorphism from a profinite group to a finite group need not be continuous if no topology is imposed on its construction. In arithmetic, continuity makes the stabilizers open and therefore makes their fixed fields finite separable extensions.

### 1.3 The field cut out by an action

The **field cut out by $M$** is

$$
F(M):=(F^s)^{\ker\rho_M}.
$$

Because the kernel is open and normal, $F(M)/F$ is finite Galois and restriction gives a canonical isomorphism

$$
\operatorname{Gal}(F(M)/F)\simeq\operatorname{im}\rho_M.
$$

This is the minimal extension over which every element of $M$ is fixed. It is not the field generated by the coordinates of one arbitrarily chosen vector unless that vector has trivial stabilizer. For example, if $M=\mathbf F_\ell^2$ and the image consists of diagonal matrices, the field generated by one coordinate line can miss the character on the other line; adjoining all geometric points recovers $F(M)$.

If $G$ is a finite-flat group scheme over a domain $R$ with fraction field $F$ of characteristic zero, its generic fiber is finite étale. The field $F(G)$ means the field generated by all coordinates of all $F^s$-points of $G_F$; equivalently it is $F(G_F(F^s))$. The chosen generic identification in a finite-flat model ensures that this agrees with the field attached to the represented module.

Three elementary examples distinguish the construction. For the trivial module $\mathbf Z/n\mathbf Z$, the kernel is all of $G_F$ and $F(M)=F$. For $M=\mu_n(F^s)$, the kernel fixes all $n$th roots of unity, so $F(M)=F(\mu_n)$. If $E/F$ is an elliptic curve and $M=E[n](F^s)$, then $F(M)=F(E[n])$ is generated by the coordinates of every $n$-torsion point. The field generated by the $x$-coordinate of one point can be smaller: it identifies $P$ with $-P$ and can retain a nontrivial stabilizer.

The cutout field is unchanged when the representation is replaced by an isomorphic module or a conjugate matrix presentation. Merely viewing the same finite abelian group with fewer scalar labels also leaves the kernel unchanged; a scalar restriction changes the coefficient structure, not the underlying Galois action.

At a nonarchimedean place $v$ of a number field $F$, choose a place $w$ of $F(M)$ above $v$. Then

$$
F(M)_w/F_v
$$

is the local extension cut out by the restriction of $M$ to a decomposition group, after quotienting by the kernel of that local action. Different choices of $w$ give conjugate extensions with the same ramification invariants.

The decomposition group at $w$ is the image of $G_{F_v}$ in the global image. Its inertia and upper ramification groups are the images of the corresponding local subgroups. The latter assertion uses quotient compatibility of upper numbering. It is why a local theorem that $G_{F_v}^u$ acts trivially on $M$ immediately becomes a cutoff for $F(M)_w/F_v$.

### 1.4 Several operations and several fields

Field inclusions run opposite to kernels. If $N$ is a submodule or quotient of $M$, its action is obtained from that on $M$, so

$$
\ker\rho_M\subseteq\ker\rho_N,
\qquad F(N)\subseteq F(M).
$$

For a direct sum,

$$
\ker\rho_{M\oplus N}=\ker\rho_M\cap\ker\rho_N,
\qquad
F(M\oplus N)=F(M)F(N).
$$

These directions are easy to reverse accidentally: a more informative representation has a smaller kernel and cuts out a larger field.

For an exact sequence

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0,
$$

the field $F(M)$ contains the compositum $F(M')F(M'')$, but equality can fail. Over that compositum the diagonal actions are trivial, yet the middle module can retain a nontrivial unipotent extension class. A matrix

$$
\begin{pmatrix}1&c(\sigma)\\0&1\end{pmatrix}
$$

illustrates the point: both constituents are trivial while the middle representation cuts out the field detected by the cocycle $c$. Thus successive factors control the semisimplification, not necessarily the whole field.

## 2. Local and global discriminants

### 2.1 Trace duality and the different

Let $K$ be a complete discretely valued field, let $L/K$ be finite separable, and write

$$
A=\mathcal O_K,\qquad B=\mathcal O_L.
$$

Normalize $v_K(K^\times)=v_L(L^\times)=\mathbf Z$, so

$$
v_L|_{K^\times}=e(L/K)v_K.
$$

The trace pairing on $L$ is nondegenerate. Its integral dual lattice is the codifferent

$$
B^\vee=\{x\in L:\operatorname{Tr}_{L/K}(xB)\subseteq A\},
$$

and the **different** is its inverse fractional ideal

$$
\mathfrak D_{L/K}=(B^\vee)^{-1}=\mathfrak m_L^{d(L/K)}.
$$

The exponent $d(L/K)$ is measured by $v_L$. It records the failure of $B$ to be self-dual for trace. In an unramified extension it is zero; in a tamely ramified extension with separable residue extension it is $e-1$.

The relative discriminant ideal is the norm

$$
\mathfrak d_{L/K}=N_{L/K}(\mathfrak D_{L/K})
=\mathfrak m_K^{\delta(L/K)},
$$

where

$$
\boxed{\delta(L/K)=f(L/K)d(L/K).}
$$

The factor $f$ is indispensable. The equality $d=\delta$ is special to the totally ramified case.

When $B=A[\alpha]$ and $g(T)$ is the monic minimal polynomial of $\alpha$, the different is generated by $g'(\alpha)$. This gives the practical formula

$$
d(L/K)=v_L(g'(\alpha)).
$$

The hypothesis $B=A[\alpha]$ cannot be replaced by $L=K(\alpha)$. If $A[\alpha]$ is a proper order, the polynomial discriminant contains an index correction:

$$
(\operatorname{disc}g)
=\mathfrak d_{L/K}\,[B:A[\alpha]]^2.
$$

Thus a poorly chosen primitive element can make a polynomial appear more ramified than the field. The trace-dual definition avoids this dependence.

For an Eisenstein equation $g(T)=T^m-\pi_K$ with residue characteristic prime to $m$, one has

$$
g'(\alpha)=m\alpha^{m-1},
$$

and $m$ is a unit. Hence $d=m-1$, the tame baseline. When the residue characteristic divides $m$, the factor $m$ contributes extra valuation and the same derivative calculation displays wild excess.

### 2.2 Relative and absolute discriminants

For number fields $L/K$, the relative different $\mathfrak D_{L/K}$ is an ideal of $\mathcal O_L$ and the relative discriminant $\mathfrak d_{L/K}$ is an ideal of $\mathcal O_K$. The **absolute discriminant** is the integer

$$
D_L=\left|\operatorname{disc}(\mathcal O_L/\mathbf Z)\right|.
$$

Applying the discriminant formula to $\mathbf Q\subseteq K\subseteq L$ gives

$$
\boxed{D_L=D_K^{[L:K]}N_{K/\mathbf Q}(\mathfrak d_{L/K}).}
$$

Thus the base field contributes once for every relative degree. A relative discriminant estimate that omits $D_K$ is not an absolute estimate.

This identity follows by applying the relative tower formula to

$$
\mathbf Z\subseteq\mathcal O_K\subseteq\mathcal O_L.
$$

The trace pairing of $L/\mathbf Q$ factors through that of $L/K$ and $K/\mathbf Q$. On determinants, the latter appears once in each of the $[L:K]$ relative basis directions, while the former is normed from $K$ to $\mathbf Q$. The same reasoning works for any tower of Dedekind domains and shows that the formula is structural, not a feature of a selected integral basis.

If $\mathfrak p$ is a prime of $K$ and $\mathfrak P$ a prime of $L$ over it, write $L_{\mathfrak P}/K_{\mathfrak p}$ for the completion. Then the exponent of $\mathfrak p$ in $\mathfrak d_{L/K}$ is

$$
v_{\mathfrak p}(\mathfrak d_{L/K})
=\sum_{\mathfrak P\mid\mathfrak p}
f(\mathfrak P/\mathfrak p)d(L_{\mathfrak P}/K_{\mathfrak p}).
$$

When $L/K$ is Galois, all summands are equal. If $g$ is the number of primes above $\mathfrak p$, and $e,f,d$ are their common invariants, this becomes $gfd$; since $[L:K]=gef$,

$$
\frac{v_{\mathfrak p}(\mathfrak d_{L/K})}{[L:K]}=\frac d e.
$$

This ratio is the local contribution naturally seen by a root discriminant.

### 2.3 Root discriminants and normalization

The **root discriminant** is

$$
\operatorname{rd}(L)=D_L^{1/[L:\mathbf Q]}.
$$

It is stable under repeating a field contribution through a tower. From the absolute tower formula,

$$
\boxed{
\operatorname{rd}(L)
=\operatorname{rd}(K)
N_{K/\mathbf Q}(\mathfrak d_{L/K})^{1/[L:\mathbf Q]}.
}
$$

Suppose $L/K$ is Galois. Expanding the norm prime by prime gives

$$
\operatorname{rd}(L)
=\operatorname{rd}(K)
\prod_{\mathfrak p}
N\mathfrak p^{\,d_{\mathfrak p}/(e_{\mathfrak p}[K:\mathbf Q])},
$$

where $d_{\mathfrak p}$ and $e_{\mathfrak p}$ refer to one completion above $\mathfrak p$. The exponent contains $[K:\mathbf Q]$ because $N\mathfrak p$ is already an absolute norm. Equivalently, grouping primes of $K$ above a rational prime $p$ gives a power of $p$ weighted by their residue degrees.

For $K=\mathbf Q$ and a Galois extension ramified only at $p$, the formula reduces to

$$
\operatorname{rd}(L)=p^{d/e}.
$$

This simple test will expose every missing factor later.

### 2.4 Localizing the global discriminant

The global product formula is not merely a formal factorization. It says that the arithmetic cost of a finite representation is a sum of local depth costs. For $E=F(M)$,

$$
\log\operatorname{rd}(E)
=\log\operatorname{rd}(F)
+\frac1{[F:\mathbf Q]}
\sum_{v<\infty}
\frac{d(E_w/F_v)}{e(E_w/F_v)}\log Nv.
$$

Only ramified places occur. At a place where the local action on $M$ is unramified, the completion is unramified and $d=0$. At a tamely ramified place, $d/e=1-1/e<1$. At a wild place, a bound on the last upper break controls the excess over this tame baseline.

This formula also clarifies a common ambiguity. Saying that a representation is “ramified only at $S$” identifies the primes that can occur, but gives no bound on their exponents. To bound a discriminant one needs, at every $v\in S$, either the full filtration, an Artin-conductor package strong enough to detect the field, or an upper-break cutoff.

Here is a direct check of the completion formula. Localize the trace-dual lattice at a prime $\mathfrak p$ of $K$. The integral closure decomposes after completion as

$$
\mathcal O_L\otimes_{\mathcal O_K}\mathcal O_{K_{\mathfrak p}}
\simeq\prod_{\mathfrak P\mid\mathfrak p}
\mathcal O_{L_{\mathfrak P}}.
$$

The trace pairing is the orthogonal product of the local trace pairings. Its determinant ideal is consequently the product of the local discriminant ideals after norming their residue fields to $K_{\mathfrak p}$. This produces the factor $f(\mathfrak P/\mathfrak p)$ in

$$
v_{\mathfrak p}(\mathfrak d_{L/K})
=\sum_{\mathfrak P\mid\mathfrak p}f(\mathfrak P/\mathfrak p)d_{\mathfrak P}.
$$

If one records only the exponent $d_{\mathfrak P}$ at a single completion and forgets both the number of primes and the residue degree, the global ideal is generally wrong.

For example, let $L/K$ be unramified of residue degree $f>1$. Then $d=0$ and the discriminant is a unit despite the increased local degree. By contrast, take the compositum of this unramified extension with a totally tamely ramified extension of index $e$. The top local different exponent remains $e-1$, but the discriminant exponent downstairs is $f(e-1)$. This is the smallest example in which $d$ and $\delta$ visibly differ.

## 3. Towers, subfields, and composita

### 3.1 Transitivity formulas

For a tower of finite separable extensions of complete discretely valued fields

$$
K\subseteq M\subseteq L,
$$

trace transitivity gives

$$
\mathfrak D_{L/K}
=\mathfrak D_{L/M}\mathfrak D_{M/K}\mathcal O_L,
$$

and hence

$$
\boxed{d(L/K)=d(L/M)+e(L/M)d(M/K).}
$$

Norming down gives

$$
\mathfrak d_{L/K}
=\mathfrak d_{M/K}^{[L:M]}
N_{M/K}(\mathfrak d_{L/M}).
$$

Globally the identical ideal formula holds. These identities show why lower-stage ramification is repeated: every basis direction at the top carries the trace defect already present below.

After division by the total ramification index, the local formula becomes

$$
\frac{d(L/K)}{e(L/K)}
=\frac{d(M/K)}{e(M/K)}
+\frac1{e(M/K)}\frac{d(L/M)}{e(L/M)}.
$$

The second term is discounted by the ramification already accumulated below. This normalized form is particularly useful in towers of torsion fields.

### 3.2 Root discriminants in towers

For number fields $K\subseteq M\subseteq L$,

$$
\operatorname{rd}(L)
=\operatorname{rd}(M)
N_{M/\mathbf Q}(\mathfrak d_{L/M})^{1/[L:\mathbf Q]}.
$$

Thus root discriminants are nondecreasing in a tower. Equality holds precisely when $L/M$ is unramified at every finite prime. Infinite places affect signature but not the absolute discriminant ideal in this formula.

The monotonicity direction matters: passing to a larger field cannot improve a root-discriminant upper bound unless one separately proves that the new relative discriminant contribution is small. Conversely, every subfield $M\subseteq L$ satisfies

$$
\operatorname{rd}(M)\leq\operatorname{rd}(L).
$$

### 3.3 Subfield monotonicity

The preceding inequality is an immediate consequence of the tower formula, but its use requires care. If $M$ is a subfield of $L$, an upper bound for $\operatorname{rd}(L)$ does imply the same bound for $M$. An upper bound for $\operatorname{rd}(M)$ says nothing about $L$ without control of $\mathfrak d_{L/M}$.

Locally, quotienting a Galois group produces a subfield and upper numbering behaves exactly under that quotient. Hence a last-upper-break bound descends to every Galois subextension. This is stronger and more structural than merely invoking root-discriminant monotonicity.

As a counterexample to the reverse inference, start with an unramified $M/K$ and choose over $M$ a cyclic extension of fixed degree with arbitrarily deep wild ramification. The lower field has no discriminant cost, while the top root discriminant is unbounded.

### 3.4 Composita and a useful inequality

Let $L_1/K$ and $L_2/K$ be finite separable extensions in a common separable closure, and put $L=L_1L_2$. Discriminants do not multiply exactly because ramification can overlap. The safe inequality is

$$
\boxed{
\mathfrak d_{L/K}\mid
\mathfrak d_{L_1/K}^{[L:L_1]}
\mathfrak d_{L_2/K}^{[L:L_2]}.
}
$$

When $L_1$ and $L_2$ are linearly disjoint, one can see this by comparing the integral closure of $\mathcal O_K$ in $L$ with the tensor order $\mathcal O_{L_1}\otimes_{\mathcal O_K}\mathcal O_{L_2}$. Its discriminant is the displayed product, and passing to the larger integral closure divides the discriminant by the square of an index. Without linear disjointness the tensor algebra need not be an order in the field $L$. In that case one first removes the common intersection, or equivalently applies the local different inequality successively in the two towers. This gives the same divisibility without treating a noninjective tensor map as an inclusion of orders.

Taking absolute norms and degree roots gives

$$
\operatorname{rd}(L)
\leq
\frac{\operatorname{rd}(L_1)\operatorname{rd}(L_2)}{\operatorname{rd}(K)}.
$$

The denominator removes the base contribution counted twice. Iterating, for $L=L_1\cdots L_s$,

$$
\operatorname{rd}(L)
\leq
\operatorname{rd}(K)^{1-s}
\prod_{j=1}^s\operatorname{rd}(L_j).
$$

This inequality is often convenient but deliberately coarse. If two fields have the same ramification, the product overcounts it. Upper ramification of the product representation can give a sharper common cutoff.

A particularly transparent case is when $L_1/K$ is unramified and $L_2/K$ is totally ramified. If the two are linearly disjoint, their compositum has the same ramification index and different exponent as $L_2/K$, while its residue degree is multiplied by $[L_1:K]$. The normalized ratio $d/e$, and hence the relative root-discriminant contribution, does not change. The general compositum inequality allows this but does not display the equality; the local decomposition does.

At the opposite extreme, take $L_1=L_2$. Then the compositum is just $L_1$, whereas the product bound counts its relative contribution twice. This is why direct sums of representations should be analyzed through their common upper cutoff whenever possible, rather than by multiplying two already-coarse root-discriminant bounds.

## 4. Ramification depth and the different

### 4.1 The two numberings revisited

Let $L/K$ be finite Galois with group $G$, and assume the residue extension is separable. For normalized $v_L$, define

$$
i_G(\sigma)=\min_{x\in\mathcal O_L}v_L(\sigma x-x),
$$

with $i_G(1)=+\infty$, and

$$
G_i=\{\sigma:i_G(\sigma)\geq i+1\}
\quad(i\geq0),\qquad G_{-1}=G.
$$

Thus $G_0=I$ and $G_1$ is wild inertia. Following the established left-continuous convention, for real $t>0$ put $G_t=G_{\lceil t\rceil}$. The Herbrand function is

$$
\varphi(t)=\int_0^t\frac{ds}{[G_0:G_s]},
$$

with inverse $\psi$, and the upper groups are $G^u=G_{\psi(u)}$. Lower numbering is exact for subgroups; upper numbering is exact for quotients. Since a field cut out by a representation is obtained by quotienting the absolute Galois group, upper numbering is the natural scale for this book.

A statement $G^u=1$ for $u>R$ permits a break at $u=R$. A statement $G^u=1$ for $u\geq R$ forbids it. Endpoints have measure zero in the integral formula for the different, but they matter in field-cutout and quotient statements. We will retain the strict inequality supplied by the geometric argument.

### 4.2 Hilbert's formula and its upper form

Hilbert's different formula says

$$
d(L/K)=\sum_{i\geq0}(|G_i|-1).
$$

The isolated $i=0$ term is the tame baseline. Changing variables from lower to upper numbering gives

$$
\boxed{
d(L/K)
=(e-1)+e\int_0^\infty
\left(1-\frac1{|G^u|}\right)du,
}
$$

where $e=|G_0|$. Unramified automorphisms do not occur; they change $f$ but not $d$. The integral begins immediately to the right of zero, so a tame extension has zero integral and $d=e-1$.

For a global Galois field, division by $e$ yields the exact local root contribution

$$
\frac de
=1-\frac1e
+\int_0^\infty
\left(1-\frac1{|G^u|}\right)du.
$$

This is the central numerical identity of the book. The height of the integrand is controlled by group size; its support is controlled by ramification depth.

### 4.3 Cutoff bounds with exact constants

Suppose $G^u=1$ for every $u>R$, with $R\geq0$. Then

$$
d(L/K)\leq(e-1)+eR
$$

and

$$
\boxed{
\frac de\leq1-\frac1e+R<1+R
}
$$

for a nontrivial ramified extension. If one knows $|G^u|\leq h(u)$ on subintervals, the sharper estimate is

$$
\frac de
\leq1-\frac1e+
\int_0^R\left(1-\frac1{h(u)}\right)du.
$$

For example, if wild inertia has order at most $w$ throughout positive depth, then

$$
\frac de\leq1-\frac1e+R\left(1-\frac1w\right).
$$

The coarser $1+R$ is independent of degree and is therefore ideal for root-discriminant arguments. The sharper versions matter when small inertia is known.

### 4.4 Tame, weakly ramified, and bounded-depth tests

If $L/K$ is tame, $G^u=1$ for $u>0$ and

$$
d=e-1,\qquad d/e=1-1/e.
$$

A totally tamely ramified cyclic extension of degree $m$ checks the constant exactly.

An extension is **weakly ramified** when $G_2=1$. Then only $G_0$ and $G_1$ contribute in lower numbering:

$$
d=(e-1)+(|G_1|-1).
$$

If $G_1\ne1$, its last positive upper break is

$$
R=\varphi(1)=\frac{|G_1|}{|G_0|},
$$

and the upper formula gives

$$
(e-1)+eR\left(1-\frac1{|G_1|}\right)
=(e-1)+(|G_1|-1),
$$

so every normalization agrees.

If $G_1=1$, the extension is tame: there is no positive upper break, and the correct cutoff is $R=0$. Although $\varphi(1)=1/|G_0|$ in that case, this number is not a break because the positive upper groups are already trivial. This edge case is why a value of the Herbrand function should be called a break only after checking that the group actually drops there.

For a totally ramified cyclic extension of order $p$ with one lower and upper break $m>0$,

$$
d=(m+1)(p-1),\qquad
\frac de=(m+1)\left(1-\frac1p\right).
$$

The crude cutoff bound gives $d/e<1+m$ and loses exactly $(m+1)/p$. This example shows both the usefulness and the intentional coarseness of replacing the integrand by $1$.

Two mixed-characteristic checks are worth making. For $L=\mathbf Q_2(\sqrt2)$, the minimal polynomial derivative is $2\sqrt2$, so $d=3$. The nontrivial automorphism lies in $G_0,G_1,G_2$ and not in $G_3$. Thus

$$
d=(2-1)+(2-1)+(2-1)=3.
$$

The unique lower and upper break is $2$, and the normalized upper formula gives

$$
\frac de=\frac12+2\left(1-\frac12\right)=\frac32.
$$

The coarse cutoff bound is $d/e<3$; the exact integrand remembers that the group has only two elements and recovers $3/2$.

For $L=\mathbf Q_p(\zeta_p)$ with odd $p$, the extension is tame of degree $p-1$. Hence

$$
d=p-2,
\qquad
\frac de=1-\frac1{p-1}.
$$

Although $v_L(p)=p-1$ is positive and the roots of unity coalesce in the special fiber, the positive upper groups are trivial. Torsion-point congruence and wild ramification are related through the integral group law, but they are not the same invariant.

Finally, in equal characteristic $p$, the extensions

$$
y^p-y=t^{-m},\qquad (m,p)=1,
$$

all have degree $p$ and unique break $m$, with

$$
d=(m+1)(p-1).
$$

Letting $m$ grow supplies a permanent counterexample to any proposed discriminant bound depending only on the matrix image. The finite-flat theorem avoids this counterexample not because its image is smaller, but because mixed-characteristic integral geometry supplies a bound on $m$.

## 5. Conductors and discriminants

### 5.1 The Artin conductor

Let $V$ be a characteristic-zero representation of a finite local Galois quotient $G$. Its Artin conductor exponent is

$$
a_K(V)=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i}.
$$

It separates as

$$
a_K(V)=\operatorname{codim}V^{G_0}
+\operatorname{Sw}_K(V),
$$

where

$$
\operatorname{Sw}_K(V)
=\int_0^\infty\operatorname{codim}V^{G^u}\,du.
$$

This conductor measures only directions visible in $V$. It is additive in direct sums and, because characteristic-zero finite-group representations are semisimple, in short exact sequences. It is unchanged by duality and by unramified twists.

A finite module in coefficient characteristic $\ell$ is not itself being assigned this semisimple conductor formula. Instead, its finite image $G$ has canonical characteristic-zero permutation representations, and those will recover the discriminant. When modular conductors are used, additional definitions are required; none are hidden here.

### 5.2 Permutation and regular representations

Let $M/K$ be finite separable. The absolute Galois group acts on the $K$-embeddings of $M$ into a separable closure. For the associated permutation representation

$$
\mathbf 1_M^K=\operatorname{Ind}_{G_M}^{G_K}\mathbf1,
$$

the conductor--discriminant identity is

$$
\boxed{a_K(\mathbf1_M^K)=\delta(M/K).}
$$

If $L/K$ is Galois with group $G$, this is the regular representation $\mathbf C[G]$. Indeed,

$$
\dim\mathbf C[G]^{G_i}=\frac{|G|}{|G_i|},
$$

and therefore

$$
\begin{aligned}
a_K(\mathbf C[G])
&=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\left(|G|-\frac{|G|}{|G_i|}\right)\\
&=\frac{|G|}{|G_0|}\sum_{i\geq0}(|G_i|-1)\\
&=f(L/K)d(L/K)=\delta(L/K).
\end{aligned}
$$

This exact equality is the cleanest answer to the title of the book: the discriminant of the field cut out by a finite action is the Artin conductor of the regular representation of its image. It is usually not the conductor of the original representation.

For an abelian $G$, decomposing the regular representation into its characters gives

$$
\delta(L/K)=\sum_{\chi\in\widehat G}a_K(\chi).
$$

For nonabelian $G$, each irreducible character occurs with multiplicity its dimension:

$$
\delta(L/K)=\sum_{\chi\in\operatorname{Irr}(G)}
(\dim\chi)a_K(\chi).
$$

The regular representation is forced by the field, not selected for convenience. The trace form on $\mathcal O_L$ compares all $K$-embeddings simultaneously; after a Galois closure those embeddings form precisely the regular $G$-set. A single faithful $r$-dimensional representation can compress this action drastically, and its conductor can therefore be much smaller than $\delta(L/K)$.

In a tame cyclic extension of degree $e$, all $e-1$ nontrivial characters have conductor $1$, while the trivial character has conductor $0$. Their sum is $e-1=d$. In a cyclic degree-$p$ extension with one break $m$, each nontrivial character has conductor $m+1$, so

$$
\delta=(p-1)(m+1).
$$

These examples verify both the multiplicities and the shift from Swan conductor $m$ to Artin conductor $m+1$.

For a nongalois extension $M/K$, the same principle uses the permutation action on embeddings rather than the regular action of a nonexistent group of order $[M:K]$. Passing to a Galois closure and using its regular discriminant would generally overcount. The permutation conductor is intrinsic and equals the discriminant exponent of $M/K$ itself.

### 5.3 What a small conductor does and does not bound

If $V$ is faithful, every nontrivial $G^u$ moves some vector. Hence

$$
G^u\ne1\quad\Longrightarrow\quad
\operatorname{codim}V^{G^u}\geq1.
$$

It follows that the last positive upper break $R(V)$ satisfies

$$
R(V)\leq\operatorname{Sw}(V)\leq a(V).
$$

Combined with Chapter 4, this gives

$$
\frac de<1+a(V).
$$

This is useful when a small conductor is known for a faithful characteristic-zero representation. It is much weaker when $a(V)$ grows with dimension or level.

Faithfulness cannot be omitted. Inflate a tame character through a quotient and append an arbitrarily deep wild extension acting trivially on it. The character conductor stays fixed while the discriminant of the larger cutting field grows without bound. Even a faithful representation of the quotient does not see ramification killed before reaching that quotient; the field must be exactly the one cut out by the faithful action under discussion.

A numerical conductor bound alone also hides why the bound holds. Finite-flat geometry gives a cutoff uniform in the rank of the module, while estimating a conductor by dimension typically introduces a factor of that rank.

To make the comparison quantitative, suppose $V$ is faithful of dimension $r$ and has last upper break $R$. Since

$$
1\leq\operatorname{codim}V^{G^u}\leq r
$$

whenever $G^u$ is nontrivial, one has

$$
R\leq\operatorname{Sw}(V)\leq rR.
$$

The right inequality can be far from equality if large fixed spaces persist. A conductor bound $a(V)\leq A$ therefore yields $R\leq A$, but a crude proof of that conductor bound often first establishes $A\leq r(1+R)$ and gains nothing. By contrast, the finite-flat proof obtains $R\leq e_K(1+1/(\ell-1))-1$ at level $\ell$ before the rank $r$ appears at all. When the local base is unramified, this is $1/(\ell-1)$.

### 5.4 Faithful families and conductor bounds

Suppose $V_1,\ldots,V_s$ are finite-image characteristic-zero representations of $G_K$ and their direct sum is faithful on a finite quotient $G$. Then

$$
R(G)\leq\sum_{j=1}^s\operatorname{Sw}(V_j).
$$

Indeed, while $G^u$ is nontrivial, at least one summand has a positive fixed-space defect; integrating gives the result. If each $V_j$ is trivial on $G_K^u$ for $u>R_j$, the sharper and simpler bound is

$$
R(G)\leq\max_jR_j.
$$

The second formula illustrates the advantage of upper cutoffs: direct sums take a maximum, whereas conductor estimates add. Since $F(V_1\oplus\cdots\oplus V_s)$ is the compositum of the individual fields, this maximum rule is often sharper than the general compositum discriminant inequality.

## 6. Finite images and module constructions

### 6.1 Matrix bounds

Let $M$ be free of rank $r$ over $\mathbf Z/\ell^n\mathbf Z$. Then

$$
[F(M):F]=|\operatorname{im}\rho_M|
\leq|\operatorname{GL}_r(\mathbf Z/\ell^n\mathbf Z)|,
$$

and

$$
|\operatorname{GL}_r(\mathbf Z/\ell^n\mathbf Z)|
=\ell^{r^2(n-1)}
\prod_{j=0}^{r-1}(\ell^r-\ell^j)
<\ell^{r^2n}.
$$

For a finite field $\mathbf F_q$, the analogous exact formula is

$$
|\operatorname{GL}_r(\mathbf F_q)|
=\prod_{j=0}^{r-1}(q^r-q^j).
$$

These bounds control degree and possible inertia size. They do not control depth. Artin--Schreier extensions of fixed degree already show that no discriminant estimate follows from the displayed inequalities alone.

If a last upper break $R$ is known as separate input and the inertia order is at most $H$, Chapter 4 yields

$$
\frac de\leq1-\frac1e+R\left(1-\frac1H\right)
<1+R.
$$

Thus a matrix estimate refines the height of the ramification integral, while geometry or conductor theory bounds its support.

There is a useful two-parameter formulation. Suppose $|I|\leq H$ and $G^u=1$ for $u>R$. Since every positive upper group lies in wild inertia, one may replace $H$ in the positive-depth term by a bound $W$ for the wild inertia order:

$$
d\leq(e-1)+eR\left(1-\frac1W\right).
$$

For a representation on $(\mathbf Z/\ell^n\mathbf Z)^r$, one can always take $H<\ell^{r^2n}$. At a place of residue characteristic $p$, one may take $W$ to be the order of the wild inertia image, hence a $p$-power dividing the $p$-part of the matrix image. Only at a place above $\ell$ is this the $\ell$-part. If $W=1$, the extension is tame and the second term vanishes. If no information beyond the matrix group is known, $1-1/W$ is often close to $1$ and the improvement is small; the principal gain still comes from $R$.

For a number field representation ramified at a finite set $S$, these local estimates combine to

$$
\operatorname{rd}(F(M))
\leq\operatorname{rd}(F)
\prod_{v\in S}(Nv)^{B_v/[F:\mathbf Q]},
$$

where one may take

$$
B_v=1-\frac1{e_v}
+R_v\left(1-\frac1{W_v}\right).
$$

This version is useful when an image computation shows that wild inertia is cyclic of order $\ell$ or has only one small graded layer.

### 6.2 Filtrations and successive extensions

Suppose a finite module has a $G_F$-stable filtration

$$
0=M_0\subset M_1\subset\cdots\subset M_s=M.
$$

The image on the associated graded controls the diagonal part. The kernel of

$$
\operatorname{im}(G_F\to\operatorname{Aut}M)
\longrightarrow
\prod_j\operatorname{Aut}(M_j/M_{j-1})
$$

is a group of filtration-lowering automorphisms. If all factors are killed by $\ell^n$, this kernel is an $\ell$-group; when every factor is killed by $\ell$, repeated products of $s$ strictly filtration-lowering operators vanish, giving an explicit nilpotence-length bound.

This yields useful degree estimates, but not a depth estimate. A nontrivial extension of two trivial characters can be wildly and deeply ramified. To control its discriminant, one must bound the cocycles defining the successive extensions or exhibit one integral finite-flat middle model. The fact that the two endpoints separately possess models is insufficient.

When a chosen finite-flat model of the middle term exists, its stable submodules close inside it and its quotients inherit finite-flat models. The direction from middle to subquotients is automatic; the reverse extension problem remains genuine integral data.

The image size can nevertheless be bounded from the filtration alone. Suppose $M$ is an $\mathbf F_\ell$-vector space and the graded dimensions are

$$
r_j=\dim_{\mathbf F_\ell}(M_j/M_{j-1}).
$$

After choosing a basis adapted to the filtration, the image lies in a block upper-triangular group. Its diagonal image has order at most

$$
\prod_j|\operatorname{GL}_{r_j}(\mathbf F_\ell)|,
$$

and its strictly upper-block kernel has order at most

$$
\ell^{\sum_{i<j}r_ir_j}.
$$

Hence

$$
|\operatorname{im}\rho_M|
\leq
\ell^{\sum_{i<j}r_ir_j}
\prod_j|\operatorname{GL}_{r_j}(\mathbf F_\ell)|.
$$

If every graded action is trivial, this reduces to a purely unipotent $\ell$-group bound. Yet its ramification can still be deep. For a two-step extension of trivial lines the image has order at most $\ell$, while the cocycle can cut out cyclic degree-$\ell$ extensions with arbitrarily large break when no integral condition is imposed. This example precisely locates what filtration counting cannot supply.

When each extension layer comes with an explicit upper cutoff $R_j$ and the full action on $M$ is known to become trivial above $R$, the discriminant bound uses $R$. The separate cutoffs of the graded pieces only show that the image above $\max R_j$ is unipotent; they do not force it to vanish. Bounding the off-diagonal cocycles is therefore an indispensable part of any successive-extension argument.

### 6.3 Direct sums, subquotients, and fields

For $M=M_1\oplus M_2$,

$$
F(M)=F(M_1)F(M_2),
$$

and the local last upper break is the maximum of the two cutoffs. If $N$ is a subquotient of $M$, then $F(N)\subseteq F(M)$ and every upper-break cutoff for $M$ descends to $N$.

The converse is false twice over. The fields of the subquotients need not recover the extension class, and a finite-flat model for a subquotient does not identify which model it inherits unless an ambient model has been chosen. This distinction will matter when Cartier duality and exact sequences enter.

### 6.4 Lattice quotients and level towers

Let $T$ be a free $\mathbf Z_\ell$-module of rank $r$ with continuous $G_F$-action, and set

$$
M_n=T/\ell^nT,\qquad F_n=F(M_n).
$$

Then $F_n\subseteq F_{n+1}$ and

$$
\operatorname{Gal}(F_{n+1}/F_n)
\hookrightarrow
1+\ell^nM_r(\mathbf Z/\ell^{n+1}\mathbf Z).
$$

For $n\geq1$ the right side is an elementary abelian $\ell$-group of order at most $\ell^{r^2}$. Consequently

$$
[F_{n+1}:F_n]\leq\ell^{r^2},
\qquad [F_n:F_1]\leq\ell^{r^2(n-1)}.
$$

The step-degree bound is uniform in $n$. The absolute root discriminants need not be. The cyclotomic tower $\mathbf Q(\mu_{\ell^n})$ is a decisive counterexample: its ramification depth and root discriminant grow with $n$. Uniform degree of successive kernels must never be mistaken for uniform ramification depth.

## 7. Integral geometry and a torsion-free congruence ball

### 7.1 Why generic matrices lose the decisive information

Let $K/\mathbf Q_\ell$ be finite, normalize $v_K(K^\times)=\mathbf Z$, and write

$$
e_K=v_K(\ell).
$$

Let $\mathcal G=\operatorname{Spec}A$ be a finite locally free commutative group scheme over $R=\mathcal O_K$, with étale generic fiber. Its augmentation

$$
\varepsilon:A\longrightarrow R
$$

has ideal $I=\ker\varepsilon$. A geometric point $P:A\to\mathcal O_{\overline K}$ is close to the identity precisely when every $P(a)$ with $a\in I$ has large valuation.

The generic module remembers the points and their permutations but not these integral distances. The augmentation ideal remembers them without choosing coordinates. This is the source of the improvement: multiplication by $\ell$ has a constrained expansion near the identity that an arbitrary matrix representation does not possess.

Extend $v_K$ to $\overline K$ with value group in $\mathbf Q$. For a point $P$, define its identity depth

$$
\nu(P)=\inf_{a\in I}v_K(P(a)).
$$

The augmentation splitting $A\simeq R\oplus I$ makes $I$ a finite $R$-module, so the infimum is attained on any finite set of $R$-module generators. We put $\nu(0)=+\infty$. Translation gives

$$
\nu(P-Q)=\inf_{a\in A}v_K(P(a)-Q(a)).
$$

The equality is intrinsic: translating functions by $Q$ carries the augmentation ideal to the ideal of functions vanishing at $Q$.

### 7.2 The augmentation ideal estimate

The crucial calculation occurs before any ramification group is mentioned.

**Proposition 7.1 (multiplication estimate).** For a finite locally free commutative $R$-group with augmentation ideal $I$,

$$
[\ell]^*I\subseteq \ell I+I^\ell.
$$

More precisely, for every $x\in I$ one has

$$
[\ell]^*x-\ell x\in\ell I^2+I^\ell.
$$

**Proof strategy.** Reduce the Hopf algebra modulo $\ell$. In characteristic $\ell$, the sum of $\ell$ copies of a commutative group has no homogeneous terms of degrees $1,\ldots,\ell-1$ at the identity. Integrally, the missing coefficients are divisible by $\ell$; the linear term is exactly $\ell$ times the identity.

Choose generators $x_1,\ldots,x_m$ of $I$. Iterated comultiplication expresses $[\ell]^*x_j$ as a polynomial in the $\ell$ tensor slots. Its linear contribution is

$$
x_j\otimes1\otimes\cdots\otimes1+\cdots+
1\otimes\cdots\otimes x_j,
$$

which becomes $\ell x_j$ after the diagonal multiplication of coordinate rings. Modulo $\ell$, commutativity makes the degree-$d$ contributions for $1\leq d<\ell$ occur in orbits whose multinomial coefficients are divisible by $\ell$. Equivalently, multiplication by $\ell$ in characteristic $\ell$ factors through the relative Frobenius, whose pullback sends the augmentation ideal into its $\ell$th power. Lifting back to $R$ gives

$$
[\ell]^*x_j=\ell x_j+\ell q_j+r_j,
\qquad q_j\in I^2,\quad r_j\in I^\ell.
$$

This proves both assertions. Notice that no classification of finite-flat groups, not even of groups of order $\ell$, has entered. $\square$

We now extract the valuation constant. If $P$ is a geometric point and $r=\nu(P)>0$, the displayed expansion gives

$$
\nu([\ell]P)\geq\min\{e_K+r,\ell r\}.
$$

When $r>e_K/(\ell-1)$, the first quantity is strictly smaller than the second. If $P$ is killed by $\ell$, choose a generator whose value attains the minimum after passing to a finite field of definition. In the equation $[\ell]^*x_j(P)=0$, the term $\ell x_j(P)$ has valuation $e_K+r$, while $\ell q_j(P)$ has valuation at least $e_K+2r$ and $r_j(P)$ has valuation at least $\ell r$. A unique term of least valuation cannot sum to zero. Therefore $P=0$.

In fact the same congruence ball contains no nonzero point of any $\ell$-power order.

**Theorem 7.2 (torsion-free congruence ball).** If $\mathcal G$ is killed by a power of $\ell$, then

$$
\boxed{
\nu(P)>r_{\ell,K}:=\frac{e_K}{\ell-1}
\quad\Longrightarrow\quad P=0.
}
$$

Indeed, the assertion for points killed by $\ell$ was just proved. If $P$ has order dividing $\ell^n$ and $\nu(P)>r_{\ell,K}$, then

$$
\nu([\ell]P)\geq e_K+\nu(P)>r_{\ell,K}.
$$

Induction on $n$ gives $[\ell]P=0$, and the order-$\ell$ case then gives $P=0$. The independence from $n$ is genuine: higher cyclotomic points approach the identity less closely, not more closely.

### 7.3 Congruence of points

Translation turns Theorem 7.2 into a separation theorem.

**Corollary 7.3 (congruence of points).** Let $P,Q\in\mathcal G(\overline K)$ for a group killed by a power of $\ell$. If

$$
v_K(P(a)-Q(a))>\frac{e_K}{\ell-1}
\quad\text{for every }a\in A,
$$

then $P=Q$. Equivalently, two distinct points can be separated by some integral function $a\in A$ satisfying

$$
v_K(P(a)-Q(a))\leq\frac{e_K}{\ell-1}.
$$

The strict sign is important. At the critical radius the two leading terms in the multiplication equation can have equal valuation and cancel. The argument proves no assertion with $>$ replaced by $\geq$.

For $\mu_\ell$, take $u=T-1$. A nontrivial root $\zeta_\ell$ satisfies

$$
v_K(\zeta_\ell-1)=\frac{e_K}{\ell-1},
$$

after extending $v_K$ to the cyclotomic field. Thus the radius is optimal as a universal congruence statement, even though the cyclotomic field itself is only tamely ramified at level $\ell$.

For the constant group $\underline{\mathbf Z/\ell\mathbf Z}$, distinct points are already separated modulo the maximal ideal and have depth zero. The same generic abstract group may therefore admit models with very different integral distances. The theorem depends on a chosen model, while its eventual ramification conclusion depends only on the existence of at least one model.

### 7.4 From congruence to upper ramification

We need one bridge from integral separation to quotient-compatible ramification. We state it in the form required here and prove the mechanism.

**Lemma 7.4 (ramification--congruence lemma).** Let $\mathcal G=\operatorname{Spec}B$ be a finite locally free commutative $R$-group with étale generic fiber, killed by $\ell^n$. Suppose $c\geq0$ and that for every pair of distinct geometric points $P,Q$ there is $b\in B$ with

$$
v_K(P(b)-Q(b))\leq c.
$$

Then $G_K^u$ acts trivially on $\mathcal G(\overline K)$ for every

$$
u>e_Kn+c-1.
$$

**Proof strategy.** Pass to a finite Galois field splitting all points. Filter point differences both by congruence depth and by their $\ell$-power order. Translation makes every congruence class a coset and hence gives equal block sizes. A finite orbit--stabilizer count then supplies exactly the denominators in Herbrand's function: it cancels the ramification index of the splitting field. One multiplication layer costs at most $e_K$ units of upper time, while the terminal order-$\ell$ layer costs $e_K+c-1$. Iteration gives the stated constant.

Let $L/K$ split $\mathcal G$, let $G=\operatorname{Gal}(L/K)$, and put $E=e(L/K)$. Thus $v_L=Ev_K$ on $L$. For $t\geq0$, set

$$
C_t=\{P\in\mathcal G(L):\nu(P)>t\}.
$$

The nonarchimedean inequality and the group law make $C_t$ a $G$-stable subgroup. The points congruent to $P$ at depth $t$ form the coset $P+C_t$, so every congruence block has cardinality $|C_t|$. Only finitely many values of $t$ change this partition.

We first prove the one-layer estimate used in the induction. Let $X$ be a finite $G$-stable subgroup of $\mathcal G(L)$, put $Y=[\ell]X$, and suppose every nonzero point of $\ker([\ell]:X\to Y)$ has depth at most $c$. For a finite $G$-set $Z$, let $b(Z)$ be the last upper parameter at which the action is nontrivial; put $b(Z)=-1$ when inertia is already trivial. Then

$$
\boxed{
b(X)\leq\max\{b(Y)+e_K,\ e_K+c-1\}.}
\tag{7.1}
$$

Here is the weighted count behind (7.1). If $D$ is a finite $G$-stable group and $C\subseteq D$ is $G$-stable, then for every lower group $G_s$,

$$
|C|\sum_{\sigma\in G_s}
\left|\ker\bigl(\sigma-1:D/C\to D/C\bigr)\right|
=\sum_{x\in D}|\operatorname{Stab}_{G_s}(x+C)|.
\tag{7.2}
$$

Both sides count pairs $(\sigma,x)$ with $\sigma x-x\in C$: for fixed $\sigma$, a nonempty solution fiber has $|C|$ elements over each fixed coset, while for fixed $x$ the admissible $\sigma$ form the stabilizer of $x+C$. Divide (7.2) by $|G_0||D|$ and multiply by the length of a lower interval on which $G_s$ and the block system are constant. Orbit--stabilizer turns the resulting coefficient into the proportion of the block action that has not yet separated. Summing over the lower intervals gives

$$
\int\frac{ds}{[G_0:G_s]},
$$

the upper-time increment in the Herbrand function. Thus time during which quotient blocks move is charged to $D/C$; only time during which points move inside a block is charged to $C$.

Apply this identity successively to the partitions by the subgroups $C_t\cap D$. At a critical depth, every block splits into the same number of subblocks. The continuing part of the charge is multiplied by the reciprocal of that number, and the complementary part becomes the charge of the new quotient blocks. At the next critical depth it is precisely the continuing charge, so the intermediate terms telescope. This is the same finite weighted sum as in Herbrand's quotient theorem, now applied to translation blocks rather than field cosets.

Pull the congruence filtration on $Y$ back to $X$. The augmentation estimate

$$
[\ell]^*I\subseteq\ell I+I^\ell
\tag{7.3}
$$

shows that the linear term translates a raw $v_L$-threshold by
$v_L(\ell)=Ee_K$. Values of the $I^\ell$ term only create intermediate refinements: they are products of $\ell$ augmentation values and therefore occur among the critical depths already paired in the telescoping sum. Hence they add no boundary interval. The raw interval $Ee_K$ is divided by the inertia index in the Herbrand weight; since $E=|G_0|$, its total upper length is at most $e_K$. This proves the alternative $b(X)\leq b(Y)+e_K$.

If the image block has already become a point, motion remains in the order-$\ell$ kernel. Its last nonzero difference has depth at most $c$, and (7.3) gives the same $Ee_K$ linear shift. The terminal raw separation budget is $Ec$. Passing from displacement valuation to lower index removes the first unit interval: membership in $G_s$ means displacement at least $s+1$, while positive upper time begins immediately after index $0$. After Herbrand weighting, the terminal boundary is therefore $e_K+c-1$. These are the only two boundary terms left by the telescoping count, proving (7.1).

Now put

$$
X_j=\mathcal G[\ell^j](L),
\qquad Y_j=[\ell]X_j\subseteq X_{j-1},
\qquad0\leq j\leq n.
$$

If a scheme-theoretic kernel is not flat, its schematic closure in $\mathcal G$ has the same generic points; the point count above is unchanged. Write $b_j=b(X_j)$. The separation hypothesis applies to the kernel of $X_j\to Y_j$, and $b(Y_j)\leq b_{j-1}$. Formula (7.1) gives

$$
b_1\leq e_K+c-1,
$$

and, for $j>1$,

$$
b_j\leq\max\{b_{j-1}+e_K,e_K+c-1\}
\leq je_K+c-1.
$$

All geometric points lie in $X_n$ because $\mathcal G$ is killed by $\ell^n$. Thus $G^u$ fixes every point when $u>e_Kn+c-1$. Finally, upper numbering is compatible with the quotient from any larger splitting field, so the conclusion is intrinsic to $G_K$. $\square$

The group law is decisive. For an arbitrary finite flat algebra, congruence classes need not be translates of one another, their sizes need not be uniform, and the weighted argument does not give this conclusion.

## 8. The finite-flat ramification theorem

### 8.1 The local theorem

We can now combine the Hopf-algebra calculation with ramification theory.

**Theorem 8.1 (finite-flat upper-break bound).** Let $K/\mathbf Q_\ell$ be finite, let $e_K=v_K(\ell)$, and let $M$ be a finite continuous $G_K$-module killed by $\ell^n$. Assume that the finite étale group attached to $M$ is the generic fiber of a finite locally free commutative group scheme over $\mathcal O_K$. Then

$$
\boxed{
G_K^u\text{ acts trivially on }M
\quad\text{for every }
u>e_K\left(n+\frac1{\ell-1}\right)-1.
}
$$

**Proof.** Choose one finite-flat model $\mathcal G$. Multiplication by $\ell^n$ vanishes on its generic fiber; since the coordinate algebra of $\mathcal G$ is torsion-free over $\mathcal O_K$, equality of morphisms on the generic fiber implies equality integrally. Thus $[\ell^n]_{\mathcal G}=0$. Proposition 7.1 and Theorem 7.2 show that its nonzero geometric points cannot lie in the congruence ball of radius greater than

$$
r_{\ell,K}=\frac{e_K}{\ell-1}.
$$

Translation gives the same separation for every pair of distinct points. Lemma 7.4 then says that $G_K^u$ fixes all geometric generic points for

$$
u>e_Kn+r_{\ell,K}-1
=e_K\left(n+\frac1{\ell-1}\right)-1.
$$

Under the chosen generic identification, those points are $M$. $\square$

The theorem asserts existence of a model, not uniqueness. Different models can have different point distances, but any one model supplies the universal bound. No deformation condition and no classification of finite-flat models is used.

For later reference, write

$$
c_n(K,\ell)=e_K\left(n+\frac1{\ell-1}\right)-1,
$$

or simply $c_n$ when the local base is clear.

For $n=1$, the last upper break is at most

$$
R=e_K\left(1+\frac1{\ell-1}\right)-1
=\frac{e_K\ell}{\ell-1}-1.
$$

This is the small-ramification estimate central to the rest of the book. If $K/\mathbf Q_\ell$ is unramified, it reduces to $1/(\ell-1)$. Over a ramified base, the congruence radius $e_K/(\ell-1)$ and the upper-break cutoff are different: the conversion in Lemma 7.4 contributes the additional $e_K-1$.

### 8.2 The local different bound

Let $L=K(M)$ and assume $L/K$ is the local field cut out by the full module. Its Galois group acts faithfully on $M$, so Theorem 8.1 says its upper groups vanish for $u>c_n$. If $e=e(L/K)$ and $d=d(L/K)$, then

$$
\boxed{
d\leq e\,e_K\left(n+\frac1{\ell-1}\right)-1.
}
$$

Equivalently,

$$
\boxed{
\frac de
\leq e_K\left(n+\frac1{\ell-1}\right)-\frac1e
<e_K\left(n+\frac1{\ell-1}\right).
}
$$

The relative local discriminant exponent is $\delta=fd$, not $d$. Thus

$$
\delta(L/K)
\leq f\left(e\,e_K
\left(n+\frac1{\ell-1}\right)-1\right).
$$

For $n=1$ and $K=\mathbf Q_\ell$ this gives

$$
\frac de<1+\frac1{\ell-1}
=\frac\ell{\ell-1}.
$$

The constant $\ell/(\ell-1)$ is therefore not the upper-break cutoff. Over $\mathbf Q_\ell$, it is the tame baseline $<1$ plus the finite-flat positive-depth cutoff $1/(\ell-1)$. Over a ramified base, the same normalized different estimate comes from cancellation: the $-1$ in $c_n=e_K(n+1/(\ell-1))-1$ absorbs the tame baseline $1$.

### 8.3 Strictness, endpoints, and sharpness

The upper group may be nontrivial at $u=c_n$, because the ramification theorem has a strict inequality. The different integral is unaffected by a single endpoint, so the displayed weak inequality for $d$ is valid. The convenient degree-independent form is strict because

$$
e_K\left(n+\frac1{\ell-1}\right)-\frac1e
<e_K\left(n+\frac1{\ell-1}\right).
$$

For an unramified extension, $e=1$ and $d=0$; the strict coarse bound remains true but is far from equality. For a tame extension, the positive-depth integral vanishes, and the exact value is $d/e=1-1/e$, much stronger than the finite-flat estimate.

The congruence radius is sharp for $\mu_\ell$, but the resulting ramification cutoff need not be achieved. This distinction is natural: the integral geometry estimates every possible model uniformly, while a particular Galois action may have much less ramification.

### 8.4 Why integrality is stronger than a conductor estimate

A general faithful representation gives $R\leq\operatorname{Sw}(V)$. Bounding the Swan conductor by dimension and an a priori depth merely repackages the desired information. Finite flatness instead proves

$$
R\leq e_K\left(1+\frac1{\ell-1}\right)-1
$$

for every $\ell$-torsion module, independently of its rank and image size. The smaller number $e_K/(\ell-1)$ is the torsion-free congruence radius. It equals the ramification cutoff only when $e_K=1$.

The improvement occurs at one precise place: modulo $\ell$, the pullback of the augmentation ideal under multiplication by $\ell$ lies in $I^\ell$, not merely in $I^2$. An arbitrary collection of matrices has no analogue of this Frobenius divisibility. Comparing $\ell x$ with degree $\ell$ gives $e_K/(\ell-1)$; a merely quadratic estimate would give the much worse radius $e_K$. Integral Hopf geometry therefore controls the support of the ramification integral before representation dimension is counted.

## 9. Finite-flat constructions

### 9.1 Chosen models and inherited models

The ramification theorem requires the existence of one finite-flat model. Once such a model $\mathcal G$ of $M$ has been chosen, every $G_K$-stable submodule $N\subseteq M$ has a schematic closure $\mathcal H\subseteq\mathcal G$. Over a DVR, saturation makes $\mathcal H$ finite flat, and the quotient $\mathcal G/\mathcal H$ is finite flat. Thus

$$
0\longrightarrow\mathcal H\longrightarrow\mathcal G
\longrightarrow\mathcal G/\mathcal H\longrightarrow0
$$

models

$$
0\longrightarrow N\longrightarrow M\longrightarrow M/N\longrightarrow0.
$$

Consequently the same finite-flat upper-break bound applies to every submodule and quotient. Field-theoretically this is also clear after the fact: their cutout fields are subfields of $K(M)$, and upper numbering descends through quotients. The model construction is stronger because it retains the integral structure for later operations.

The qualification “inside a chosen model” matters. A module can possess nonisomorphic finite-flat models. The closure is unique inside its ambient model, not among all possible abstract models of the same generic submodule.

### 9.2 Cartier duals

Suppose $M$ is killed by $\ell^n$ and modeled by $\mathcal G$. Cartier duality produces a finite-flat model $\mathcal G^D$ of

$$
M^*(1)=\operatorname{Hom}(M,\mu_{\ell^n}(\overline K)).
$$

The twist is part of the statement. The dual generic action is contragredient on $M$ and cyclotomic on the target. It follows that

$$
G_K^u\text{ acts trivially on }M^*(1)
\quad(u>c_n).
$$

One should not infer that $K(M^*(1))=K(M)$. The dual action can introduce or remove the cyclotomic field. What is unchanged is the universal finite-flat cutoff.

For example, the Cartier dual of the constant group $\underline{\mathbf Z/\ell\mathbf Z}$ is $\mu_\ell$. The first generic module is trivial and cuts out no extension; the second is cyclotomic and can cut out $K(\zeta_\ell)$. Duality preserves finite flatness but not the kernel of the generic action. If a perfect pairing identifies $M$ with $M^*(1)$, then the two fields do agree under that identification; this is additional self-duality data, as in the Weil pairing for a principally polarized elliptic curve.

For an exact model sequence

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0,
$$

duality reverses it:

$$
0\to(\mathcal G'')^D\to\mathcal G^D\to(\mathcal G')^D\to0.
$$

Thus subobjects and quotients remain within the class to which the ramification theorem applies.

### 9.3 Direct sums and exact extensions

Finite direct sums of modules correspond to products of finite-flat group schemes. If $M_1$ and $M_2$ have chosen models killed by $\ell^{n_1}$ and $\ell^{n_2}$, their direct sum has a model killed by $\ell^n$ for $n=\max(n_1,n_2)$. The field is the compositum and its local upper cutoff is

$$
\max\left\{
e_K\left(n_1+\frac1{\ell-1}\right)-1,
e_K\left(n_2+\frac1{\ell-1}\right)-1
\right\}.
$$

For an extension, the correct input is an exact integral sequence. If

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
$$

is faithfully flat exact and the middle group is killed by $\ell^n$, then its generic module $M$ receives the same bound $c_n$. The proof applies directly to the augmentation ideal of $\mathcal G$; it does not add the separate cutoffs for the endpoints. This is another way integrality avoids the overcounting of a conductor argument.

Suppose, for instance, that both endpoint modules are trivial of order $\ell$ but the middle term is a nontrivial extension. If an exact finite-flat middle model is given and is killed by $\ell$, Theorem 8.1 bounds the off-diagonal cocycle by the same $e_K(1+1/(\ell-1))-1$ cutoff as a split two-dimensional module. Without the middle model, cyclic degree-$\ell$ extensions of arbitrarily large break can occur. Integral exactness controls the extension class itself, not only its constituents.

### 9.4 Change of coefficients

Arithmetic representations rarely arrive over their final coefficient ring. One first chooses a
lattice over a discrete valuation ring, then reduces modulo a power of its maximal ideal, enlarges
the residue field, projects to a coefficient factor, or forgets extra scalars. The field cut out by
the resulting module can change under these operations, so a discriminant argument needs more than
the slogan that finite flatness is insensitive to coefficients. It needs a construction of the new
model and an inclusion between the old and new cutout fields.

Begin with restriction of scalars. Let $A_0\to A$ be a homomorphism of finite commutative rings and
let $M$ be an $A$-module with continuous $G_K$-action. Viewing $M$ as an $A_0$-module changes neither
the underlying finite abelian group nor its Galois action. Therefore

$$
K_{A_0}(M)=K_A(M).
$$

If a chosen finite-flat model carries the $A$-action, forgetting endomorphisms gives an
$A_0$-linear model. No ramification invariant changes. This simple operation is important when a
rank-two module over a large residue field is viewed as a higher-dimensional module over its prime
field: the matrix size changes, but the represented field does not.

Extension of coefficients has the opposite flavor. Let $A\to B$ be a homomorphism of finite
commutative rings and form

$$
M_B=B\otimes_A M.
$$

Every element of $G_K$ acting trivially on $M$ acts trivially on $M_B$, so

$$
K(M_B)\subseteq K(M).
\tag{9.1}
$$

The inclusion can be strict: tensoring may kill a coefficient component on which Galois acted
faithfully. It can never reverse, because the new action is obtained functorially from the old one.

The integral construction does not require $B$ to be flat over $A$. Choose a finite presentation

$$
A^s\longrightarrow A^r\longrightarrow B\longrightarrow0.
$$

Tensoring with $M$ presents $M_B$ as the cokernel of a map $M^s\to M^r$. If $\mathcal G$ is an
$A$-linear finite-flat model of $M$, the product groups $\mathcal G^s$ and $\mathcal G^r$ model the
two free terms. Take the schematic closure of the generic image of $M^s$ in $\mathcal G^r$ and
then the represented finite-flat quotient. Its generic fiber is $M_B$.

To install the $B$-action, let $\pi:A^r\twoheadrightarrow B$ be the chosen surjection. For each
$b\in B$, multiplication by $b$ on $B$ lifts to an $A$-linear endomorphism of $A^r$: projectivity
of the free source lifts the map $b\pi:A^r\to B$ through $\pi$. Every such lift preserves
$\ker\pi$, and hence its induced map on $M^r$ preserves the generic relation subgroup. It
therefore preserves the schematic closure and descends to the finite-flat quotient. Different
choices of lifts induce the same quotient endomorphism. Addition, multiplication, and the unit
law for these endomorphisms hold on the generic fiber; they hold integrally because the coordinate
algebras are torsion-free over the DVR. This constructs a $B$-linear finite-flat model.

The exponent is preserved in the direction needed for discriminants. If $\ell^nM=0$, then
$\ell^nM_B=0$. Theorem 8.1 therefore gives the same universal upper cutoff $c_n(K,\ell)$ for
$M_B$, while (9.1) shows that every sharper cutoff already known for $M$ descends to the new
field by upper-numbered quotient compatibility.

Coefficient reduction is the most frequent special case. For an ideal $J\subseteq A$,

$$
M/JM\simeq(A/J)\otimes_A M,
$$

so it has a finite-flat model and

$$
K(M/JM)\subseteq K(M).
\tag{9.2}
$$

One should use the actual exponent of $M/JM$. If $T$ is a lattice over the ring of integers
$\mathcal O$ of a finite extension of $\mathbf Q_\ell$ and $J$ is open, let $a(J)$ be the least
integer such that $\ell^{a(J)}\in J$. Then $T/JT$ is killed by $\ell^{a(J)}$, and the local cutoff
is

$$
e_K\left(a(J)+\frac1{\ell-1}\right)-1.
\tag{9.3}
$$

Choosing a larger power of $\ell$ merely because it also lies in $J$ gives a valid but weaker
bound.

Scalar enlargement and coefficient reduction commute with finite direct sums and with taking
subquotients inside a chosen model. Thus a finite family of coefficient specializations at a fixed
exponent can be modeled simultaneously by a product. Its joint field, the compositum of their
cutout fields, receives one cutoff with the maximum exponent. This is stronger than multiplying
separate discriminant bounds.

It is useful to record the conclusion as a theorem because it is exactly the form used in a
change-of-prime argument.

**Theorem 9.1 (coefficient stability of the discriminant bound).** Let $M$ be a finite continuous
$A[G_K]$-module killed by $\ell^n$, and suppose a chosen $A$-linear finite-flat model over
$\mathcal O_K$ exists. Then restriction of coefficient scalars does not change $K(M)$. Extension
along any homomorphism $A\to B$ of finite commutative rings and reduction by any ideal of $A$
produce finite-flat modules whose cutout fields lie in $K(M)$. Each resulting module satisfies the
Fontaine--Raynaud upper-break and different bounds with its actual $\ell$-power exponent. A finite
direct sum of such modules satisfies the bound once, with the maximum exponent.

**Proof.** Restriction merely forgets endomorphisms. The presentation, closure, and quotient
construction above proves finite flatness after arbitrary extension of coefficients, including a
nonflat quotient. Kernel inclusion proves the field inclusions. Annihilation by the relevant power
of $\ell$ survives tensor products and quotients, so Theorem 8.1 applies. Finally, products model
direct sums and intersections of kernels cut out composita. $\square$

The theorem does not say that extending coefficients enlarges the represented field; it usually
does not. Nor does it say that two unrelated generic coefficient specializations possess compatible
models. Compatibility is obtained here because all of them are constructed from one chosen
ambient model.

### 9.5 Existence warnings

Separate finite-flat models of $M'$ and $M''$ do not prove that every generic extension

$$
0\to M'\to M\to M''\to0
$$

has a finite-flat middle model. The extension class must itself be integrally realizable. Nor does potential finite flatness over a ramified extension descend without effective integral descent data.

These warnings prevent a circular argument in applications. One may use:

- a model already supplied by a finite-flat group scheme;
- a subgroup closure or quotient inside that model;
- a product of chosen models;
- a Cartier dual;
- a faithfully flat exact sequence whose middle model is given.

One may not manufacture a middle model from generic endpoint data alone. Nothing in this book uses an unresolved deformation-theoretic existence statement.

## 10. Examples at the residue characteristic

### 10.1 Constant and multiplicative models

The constant group $\underline{\mathbf Z/\ell\mathbf Z}$ over $\mathcal O_K$ is finite étale. Its generic module is trivial, so its cutout field is $K$ and every positive ramification group acts trivially. Its points are already separated in the special fiber.

The multiplicative group $\mu_\ell$ is finite flat and has generic module $\mathbf F_\ell(1)$. Its points collide in the special fiber. If $K=\mathbf Q_\ell$, the field cut out is $\mathbf Q_\ell(\zeta_\ell)$, a tame extension of degree $\ell-1$ for odd $\ell$. Hence

$$
d=\ell-2,
\qquad
\frac de=\frac{\ell-2}{\ell-1}.
$$

The upper cutoff furnished by finite flatness is $1/(\ell-1)$, while the actual last positive break is $0$. At the same time,

$$
v_K(\zeta_\ell-1)=\frac1{\ell-1},
$$

so the congruence radius is attained. This cleanly separates sharpness of the integral point estimate from sharpness of the ramification estimate.

When $K$ contains $\mu_\ell$, the generic module of $\mu_\ell$ is trivial, just like the constant group. The two models can nevertheless have different special fibers. The field cut out by a representation depends on the generic action; the proof of its ramification bound can depend on which integral model witnesses finite flatness.

### 10.2 Cyclotomic modules

The group $\mu_{\ell^n}$ models $\mathbf Z/\ell^n\mathbf Z(1)$. Over $\mathbf Q_\ell$, the extension $\mathbf Q_\ell(\zeta_{\ell^n})$ is totally ramified of degree

$$
e=\ell^{n-1}(\ell-1)
$$

for odd $\ell$. Its different exponent satisfies

$$
\frac de=n-\frac1{\ell-1}.
$$

Indeed the cyclotomic polynomial derivative, or the standard conductor decomposition of the regular representation, gives

$$
d=\ell^{n-1}(n\ell-n-1).
$$

The finite-flat estimate gives instead

$$
\frac de<n+\frac1{\ell-1}.
$$

It has the correct linear growth in $n$ but is not intended to recover the exact cyclotomic constant. In particular, no root-discriminant bound uniform in $n$ can hold for all finite-flat $\ell^n$-torsion fields.

For $\ell=2$, $\mu_2$ over $\mathbf Q_2$ is split, while higher $2$-power cyclotomic levels ramify. The formula $c_n=e_K(n+1/(\ell-1))-1$ remains meaningful and gives $c_n=n$ over $\mathbf Q_2$. Claims about the exact degree $\ell^{n-1}(\ell-1)$ at the first levels should therefore retain the odd-prime hypothesis.

### 10.3 Good-reduction elliptic curves

Let $E/K$ be an elliptic curve with good reduction, where $K/\mathbf Q_\ell$ is finite. Its Néron model is an elliptic scheme $\mathscr E/\mathcal O_K$, and

$$
\mathscr E[\ell^n]
$$

is finite locally free of rank $\ell^{2n}$. Its generic points are $E[\ell^n]$, so

$$
G_K^u\text{ acts trivially on }E[\ell^n]
\quad\text{for }
u>e_K\left(n+\frac1{\ell-1}\right)-1.
$$

At level $\ell$ this bound is independent of the fact that the module has dimension two and the image can be as large as $\operatorname{GL}_2(\mathbf F_\ell)$. The local field $K(E[\ell])$ therefore satisfies

$$
\frac{d(K(E[\ell])/K)}{e(K(E[\ell])/K)}
<e_K\left(1+\frac1{\ell-1}\right).
$$

Ordinary and supersingular special fibers look quite different: in the ordinary case the special $\ell$-torsion has connected and étale directions, while in the supersingular case it is connected. The same universal bound covers both because the proof uses only finite local freeness, the group law, and annihilation by $\ell$.

Good reduction is a sufficient source of the model. The finite flatness of one torsion module should not be reversed into a good-reduction criterion without an independent theorem.

### 10.4 A tame auxiliary character

Let $q\ne\ell$ be a rational prime and let $\chi:G_F\to\mathbf F_\ell^\times$ be tamely ramified at a place $v\mid q$, with inertial image of order $m$. The local extension cut out by $\chi$ has

$$
d=e-1=m-1,
\qquad \frac de=1-\frac1m,
$$

if it is totally ramified there. For

$$
M=E[\ell]\oplus\mathbf F_\ell(\chi)
$$

assume in addition that $E[\ell]$ is unramified at $v$ and that $E$ has good reduction at every
place above $\ell$. The cutout field is the compositum of the two fields. At $\ell$ it retains the finite-flat cutoff,
provided $\chi$ is unramified there; at $v$ its inertia is exactly the image of $\chi$ and it has
the displayed tame contribution. Thus a tame auxiliary prime costs less than one full power of
$Nv$ in the normalized local discriminant. Without the unramifiedness of $E[\ell]$ at $v$, the
elliptic-curve summand may add its own tame or wild contribution, so the displayed value cannot be
assigned to the direct sum.

This example also shows why “finite flat at $\ell$” is a local statement. It imposes no restriction on ramification at a different residue characteristic. Auxiliary ramification must be listed and bounded separately when globalizing.

## 11. Globalization

### 11.1 Local contributions to an absolute root discriminant

Let $F$ be a number field, let $L/F$ be finite Galois, and for every finite place $v$ choose $w\mid v$. Put

$$
e_v=e(L_w/F_v),\qquad d_v=d(L_w/F_v).
$$

Then

$$
\boxed{
\operatorname{rd}(L)
=\operatorname{rd}(F)
\prod_v(Nv)^{d_v/(e_v[F:\mathbf Q])}.
}
$$

If $G_{F_v}^u$ acts trivially on the local cutting module for $u>R_v$, then

$$
\frac{d_v}{e_v}<1+R_v,
$$

and hence

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)
\prod_{v\text{ ramified}}(Nv)^{(1+R_v)/[F:\mathbf Q]}.
$$

One should use the exact tame value $1-1/e_v$ when available. The coarse $1+R_v$ is valuable because it removes the generally large degree $[L:F]$ from the estimate.

### 11.2 The finite-flat global bound

Let $M$ be a finite $G_F$-module killed by $\ell^n$, let $L=F(M)$, and assume that for every $v\mid\ell$ the restricted module has a finite-flat model over $\mathcal O_{F_v}$. Assume first that $L/F$ is unramified away from $\ell$. Write

$$
e_v^0=v(\ell)=e(F_v/\mathbf Q_\ell),
\qquad Nv=\ell^{f_v^0}.
$$

The local theorem gives

$$
\frac{d_v}{e_v}
<e_v^0\left(n+\frac1{\ell-1}\right).
$$

Therefore the exponent of $\ell$ in the relative root-discriminant factor is less than

$$
\begin{aligned}
&\frac1{[F:\mathbf Q]}
\sum_{v\mid\ell}f_v^0
e_v^0\left(n+\frac1{\ell-1}\right)\\
&=n+\frac1{\ell-1},
\end{aligned}
$$

because $\sum_{v\mid\ell}e_v^0f_v^0=[F:\mathbf Q]$. We obtain the explicit bound

$$
\boxed{
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\,
\ell^{n+1/(\ell-1)}.
}
$$

At level $\ell$,

$$
\boxed{
\operatorname{rd}(F(M))
<\operatorname{rd}(F)\,
\ell^{\ell/(\ell-1)}.
}
$$

This is the characteristic finite-flat root-discriminant estimate. It includes every place above $\ell$, its local ramification index over $\mathbf Q_\ell$, and the base field discriminant.

The cancellation behind this clean exponent is local. At $v$, the upper-break cutoff is

$$
e_v^0\left(n+\frac1{\ell-1}\right)-1,
$$

while Hilbert's formula contributes the tame baseline $1-1/e_v$. Their sum is

$$
e_v^0\left(n+\frac1{\ell-1}\right)-\frac1{e_v},
$$

strictly below the quantity used above. The $-1$ in the ramification cutoff cancels the $1$ in the tame baseline before the primes are globalized. Ramification already present in $F/\mathbf Q$ remains recorded in $\operatorname{rd}(F)$, while the factors $e_v^0f_v^0$ recombine to the absolute degree. This is why ramification of the base field does not introduce an extra power of $\ell$.

If $M$ is unramified at some $v\mid\ell$, its actual contribution is zero and that place should be removed before estimating. If its local cutting field is tame, use $1-1/e_v$ rather than the finite-flat bound. The uniform theorem deliberately assumes no such refinement, but an application should not discard it.

The inequality also applies when $L/F$ is not Galois after replacing $L$ by a field generated by only one orbit of points, provided one uses the permutation conductor or works inside the Galois field $F(M)$ and then invokes subfield monotonicity. The stated version chooses the full module precisely so that every completion has a well-defined Galois filtration and no normal-closure correction is needed.

### 11.3 Auxiliary ramification away from $\ell$

Let $S$ be a finite set of places of $F$ not dividing $\ell$, and suppose $L/F$ is unramified outside $S\cup\{v:v\mid\ell\}$. If the local last upper break at $v\in S$ is at most $R_v$, then

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\,
\ell^{n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.
}
$$

If ramification at $v$ is tame, replace its factor by the sharper

$$
(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

If only an Artin conductor bound $a_v(V)$ is known for a faithful characteristic-zero family cutting out the same local field, one may take $R_v\leq\sum\operatorname{Sw}_v(V)$ and substitute it. The word “faithful” and the phrase “the same local field” are essential.

### 11.4 A worked global estimate

Let $F=\mathbf Q$, let $M$ be killed by $\ell$ and finite flat at $\ell$, and suppose its field $L$ is ramified away from $\ell$ only tamely at a rational prime $q$, with inertia order $m$. Then

$$
\operatorname{rd}(L)
<\ell^{\ell/(\ell-1)}q^{1-1/m}.
$$

If the auxiliary character is quadratic, this becomes

$$
\operatorname{rd}(L)
<\ell^{\ell/(\ell-1)}q^{1/2}.
$$

If there is no auxiliary ramification, the bound is simply

$$
\operatorname{rd}(L)<\ell^{\ell/(\ell-1)}.
$$

For $\ell=3$ this is $3^{3/2}$. The strict sign comes from the local tame baseline $1-1/e<1$, not from excluding a break at $1/(\ell-1)$.

Over a general base $F$, the same example acquires the factor $\operatorname{rd}(F)$ and the absolute norm $Nv$ with exponent divided by $[F:\mathbf Q]$. Replacing these by $q$ and exponent $1$ without checking splitting would overcount or undercount the auxiliary contribution.

## 12. Towers of torsion fields

### 12.1 Full level and successive kernels

Let $T$ be a $G_F$-stable $\mathbf Z_\ell$-lattice and set

$$
M_n=T/\ell^nT,\qquad F_n=F(M_n).
$$

Suppose that at every $v\mid\ell$, each $M_n$ has a finite-flat model over $\mathcal O_{F_v}$. This occurs, for example, when $T$ is the Tate module of an abelian variety with good reduction and the models are its $\ell^n$-torsion group schemes. Then

$$
G_{F_v}^u\text{ acts trivially on }M_n
\quad\text{for }u>
e_v^0\left(n+\frac1{\ell-1}\right)-1.
$$

If $F_n/F$ is unramified away from $\ell$,

$$
\operatorname{rd}(F_n)
<\operatorname{rd}(F)\ell^{n+1/(\ell-1)}.
$$

This full-level statement needs no compatibility among the chosen models beyond existence at each level. Compatible geometric systems supply such models naturally, but the numerical theorem is levelwise.

The relative groups satisfy

$$
[F_{n+1}:F_n]\leq\ell^{r^2}.
$$

This makes the algebraic degree of each step uniform. To obtain a uniform ramification bound for $F_{n+1}/F_n$, however, one needs more: the relative action that cuts out the step must itself be realized by a finite-flat group killed by $\ell$ over the valuation ring of $(F_n)_w$. Base change preserves a given finite-flat model, but it does not automatically turn the affine lifting torsor from level $n$ to level $n+1$ into such a group model.

### 12.2 What is uniform and what must grow

There are three distinct uniformity claims:

1. The rank $r$ of the lattice is fixed.
2. The degree $[F_{n+1}:F_n]$ is bounded by $\ell^{r^2}$.
3. A last-break or root-discriminant bound is independent of $n$.

The first implies the second. Neither implies the third. The cyclotomic lattice $\mathbf Z_\ell(1)$ has step degrees at most $\ell$, yet

$$
\frac{d(\mathbf Q_\ell(\zeta_{\ell^n})/\mathbf Q_\ell)}
{e(\mathbf Q_\ell(\zeta_{\ell^n})/\mathbf Q_\ell)}
=n-\frac1{\ell-1}
$$

grows linearly.

What *is* uniform is the finite-flat cost of one module killed by $\ell$ over a fixed local base: its positive upper depth is at most $e_K(1+1/(\ell-1))-1$, regardless of rank. If every relative step in a tower is independently shown to arise from such a module over its current base, one may apply the local theorem step by step. The ramification index of the current base then appears explicitly and must be normalized through the tower formula; it cannot be silently replaced by the original $e_v^0$.

The safe full-level estimate grows with $n$. Any stronger uniform conclusion must name the extra structural reason that stops the cyclotomic phenomenon.

### 12.3 Composita of several torsion modules

Suppose $M_{1,n},\ldots,M_{s,n}$ are finite-flat modules over the same local bases, each killed by $\ell^n$, and let

$$
M_n=\bigoplus_{j=1}^sM_{j,n}.
$$

The product of the models is finite flat and killed by $\ell^n$. Hence the compositum

$$
F(M_n)=F(M_{1,n})\cdots F(M_{s,n})
$$

has the same upper cutoff $c_n$, not $s c_n$. Globally, if no additional primes ramify,

$$
\operatorname{rd}(F(M_n))
<\operatorname{rd}(F)\ell^{n+1/(\ell-1)}.
$$

Applying the generic compositum inequality separately would multiply $s$ relative bounds and be much worse. The product group scheme is the reason the maximum principle is available.

The same conclusion holds for any finite collection of subquotients of a single modeled module: their joint field is contained in the field of a finite direct sum, itself a subquotient of a finite product. What must remain fixed is an actual collection of models, not merely a list of generic modules asserted to be potentially finite flat.

## 13. The three-adic torsion-field ledger

The general theorem becomes arithmetically useful only after the coefficient exponent, the base
field, and every auxiliary prime have been inserted. The three-adic argument is especially
sensitive to this bookkeeping. Its residual modules are killed by $3$, but its higher coefficient
quotients need not be; tame inertia at $2$ has an exact cost smaller than a full factor of $2$;
and auxiliary first-order modules arising at a high lifting stage may again be killed by $3$ even
though the full quotient at that stage is not. This chapter derives all three bounds from the
preceding theory and records precisely which hypotheses make each one valid.

### 13.1 The coefficient and exponent ledger

Let $E/\mathbf Q_3$ be a finite extension, let $\mathcal O$ be its ring of integers, choose a
uniformizer $\varpi$, and put

$$
e_{\mathcal O}=v_\varpi(3).
$$

Thus $3=u\varpi^{e_{\mathcal O}}$ for a unit $u\in\mathcal O^\times$. Let $T$ be a finite free
$\mathcal O$-module with continuous action of $G_F$, and set

$$
T_n=T/\varpi^nT,
\qquad
L_n=F(T_n).
$$

The first numerical question is not the $\varpi$-level but the exponent of the underlying finite
abelian group. Define

$$
m(n)=\left\lceil\frac{n}{e_{\mathcal O}}\right\rceil.
\tag{13.1}
$$

Then $3^{m(n)}T_n=0$. If $T\ne0$, this is the least such power: the inequality
$e_{\mathcal O}(m(n)-1)<n$ shows that multiplication by $3^{m(n)-1}$ does not kill the class of
a basis vector. Thus the finite-flat theorem must be applied with $m(n)$, not automatically with
$n$. When $\mathcal O/\mathbf Z_3$ is unramified, $e_{\mathcal O}=1$ and $m(n)=n$; a ramified
coefficient ring can package several $\varpi$-levels into one $3$-power exponent.

Fix a place $u\mid3$ of $F$ and write

$$
e_u^0=e(F_u/\mathbf Q_3)=v_{F_u}(3).
$$

Assume $T_n|_{G_{F_u}}$ admits a finite-flat model over $\mathcal O_{F_u}$. Theorem 8.1, with
$\ell=3$ and exponent $m(n)$, gives

$$
G_{F_u}^r\text{ acts trivially on }T_n
\quad\text{for}\quad
r>e_u^0\left(m(n)+\frac12\right)-1.
\tag{13.2}
$$

If $L_{n,w}/F_u$ is the completion cut out by the local action, and $e_{u,n}$ and $d_{u,n}$ are
its ramification index and different exponent, then

$$
d_{u,n}
\leq e_{u,n}e_u^0\left(m(n)+\frac12\right)-1,
\tag{13.3}
$$

and therefore

$$
\boxed{
\frac{d_{u,n}}{e_{u,n}}
<e_u^0\left(m(n)+\frac12\right).}
\tag{13.4}
$$

The proof is worth recalling in one line because it checks the characteristic constant. The last
upper break in (13.2) is at most $e_u^0(m(n)+1/2)-1$; adding the tame baseline
$1-1/e_{u,n}$ gives the right side of (13.4) minus $1/e_{u,n}$. The $-1$ in the break cutoff has
therefore canceled the first unit of the different.

At residual level $n=1$, one always has $m(1)=1$, independently of ramification in the coefficient
field. Consequently

$$
r>\frac{3e_u^0}{2}-1
\quad\Longrightarrow\quad
G_{F_u}^r\text{ fixes }T/\varpi T,
\tag{13.5}
$$

and

$$
\frac{d_{u,1}}{e_{u,1}}<\frac{3e_u^0}{2}.
\tag{13.6}
$$

When $F_u/\mathbf Q_3$ is unramified, the last upper break is at most $1/2$ and the normalized
different is strictly less than $3/2$. The first number is a depth; the second is a
root-discriminant exponent. Keeping them distinct prevents a recurrent half-unit error.

### 13.2 The strict residual field

Let

$$
M=T/\varpi T,
\qquad L=F(M),
$$

and assume that $M$ has a finite-flat model at every $u\mid3$ and is unramified at every finite
place not dividing $3$. The global localization formula and (13.6) give

$$
\operatorname{rd}(L)
<\operatorname{rd}(F)\,3^{3/2}.
\tag{13.7}
$$

Here is the complete calculation. Write

$$
f_u^0=f(F_u/\mathbf Q_3),
\qquad N u=3^{f_u^0}.
$$

The total exponent of $3$ contributed by places above $3$ is strictly less than

$$
\frac1{[F:\mathbf Q]}
\sum_{u\mid3}f_u^0\frac{3e_u^0}{2}
=\frac32,
$$

because

$$
\sum_{u\mid3}e_u^0f_u^0=[F:\mathbf Q].
$$

This proves (13.7). Notice what cancels and what does not. Ramification of $3$ in the base field
is absorbed by the local-degree identity, but ramification already present in $F/\mathbf Q$
remains in $\operatorname{rd}(F)$. The finite-flat models must exist over the actual local rings;
potential finite flatness over larger fields is not enough.

For $F=\mathbf Q$ the bound is the explicit ceiling

$$
\boxed{
\operatorname{rd}(\mathbf Q(M))<3^{3/2}
=3\sqrt3
=5.196152422706632\ldots .}
\tag{13.8}
$$

The strict sign is genuine. It comes from the term $-1/e$ in the local normalized different, not
from a claim that the upper group is trivial at the endpoint $1/2$.

The matrix image supplies the complementary degree bound. If $M$ has rank two over
$k=\mathbf F_{3^f}$, then

$$
[L:F]\leq|\operatorname{GL}_2(k)|
=(3^{2f}-1)(3^{2f}-3^f).
\tag{13.9}
$$

Indeed the first column of an invertible matrix can be any nonzero vector and the second any vector
outside its span. For $k=\mathbf F_3$,

$$
[L:F]\leq(9-1)(9-3)=48.
\tag{13.10}
$$

If $F=\mathbf Q$ and $\det M=\overline\chi_3$, then the determinant field is
$\mathbf Q(\zeta_3)$ whenever the determinant is nontrivial. In the $\mathbf F_3$ case this gives

$$
[L:\mathbf Q(\zeta_3)]\leq|\operatorname{SL}_2(\mathbf F_3)|=24.
$$

These are image bounds, not discriminant bounds. The force of the three-adic package is that
(13.8) and (13.10) hold simultaneously.

No conclusion about the existence or classification of fields below the ceiling is drawn here.
That requires global lower bounds and, after a degree reduction, group and ray-class arguments.
The present result supplies their exact algebraic input.

### 13.3 Tame ramification at two

The controlled non-strict three-adic situation permits ramification at $2$. Because the residue
characteristic there is $2$, every inertia group of odd order is tame. Suppose the completion of a
Galois torsion field at $2$ has inertia of order $3^a$. Then its ramification index is $3^a$, its
positive ramification groups are trivial, and Hilbert's formula gives

$$
d_2=3^a-1,
\qquad
\boxed{\frac{d_2}{e_2}=1-3^{-a}.}
\tag{13.11}
$$

This remains true if an unramified part is present, because it changes the residue degree but not
$e_2$ or $d_2$. Formula (13.11) is exact, not a cutoff estimate.

At residual rank two over $\mathbf F_3$, the $3$-part of
$|\operatorname{GL}_2(\mathbf F_3)|=48$ has order $3$. Thus a nontrivial odd inertia image has
order exactly $3$ and contributes

$$
\frac{d_2}{e_2}=\frac23.
\tag{13.12}
$$

If $M$ is finite flat at $3$, unramified outside $\{2,3\}$, and has this nontrivial tame inertia
at $2$, then

$$
\boxed{
\operatorname{rd}(\mathbf Q(M))
<3^{3/2}2^{2/3}
=8.248377821991616\ldots .}
\tag{13.13}
$$

The factor at $3$ is the strict universal finite-flat bound; the factor at $2$ is the exact tame
cost. If inertia at $2$ is trivial, it must be removed entirely, recovering (13.8).

More generally, let $S_0$ be a finite set of places of a number field $F$, none above $3$, and
suppose the inertia order at $v\in S_0$ is a known tame integer $h_v$. Then the residual field
satisfies

$$
\operatorname{rd}(F(M))
<\operatorname{rd}(F)3^{3/2}
\prod_{v\in S_0}
(Nv)^{(1-1/h_v)/[F:\mathbf Q]}.
\tag{13.14}
$$

If a place is wild but its last upper break is at most $R_v$, the safe replacement is

$$
(Nv)^{(1+R_v)/[F:\mathbf Q]},
$$

or the exact upper-filtration integral when known. Merely naming the place does not bound its
cost.

The distinction between (13.8) and (13.13) is mathematical, not cosmetic. A tame cubic inertia
class at $2$ can survive all the local conditions at $3$, and its factor $2^{2/3}$ is large enough
to change a subsequent degree comparison. Any argument that calls both fields “hardly ramified”
must retain the auxiliary-prime ledger.

### 13.4 Higher coefficient levels

Return to $T_n=T/\varpi^nT$. Assume that every $T_n$ has a finite-flat model at every place above
$3$. If $L_n/F$ is unramified away from $3$, equations (13.1)--(13.4) globalize to

$$
\boxed{
\operatorname{rd}(L_n)
<\operatorname{rd}(F)3^{m(n)+1/2}.}
\tag{13.15}
$$

The proof is the same local-degree sum as at residual level, with $3/2$ replaced by
$m(n)+1/2$. If $F=\mathbf Q$, ramification is allowed at $2$, and the tame inertia there has order
$3^{a_n}>1$, then

$$
\boxed{
\operatorname{rd}(L_n)
<3^{m(n)+1/2}2^{\,1-3^{-a_n}}.}
\tag{13.16}
$$

When inertia is trivial the factor at $2$ is $1$. In applications where the local integral
structure proves $0\leq a_n\leq m(n)$, (13.16) is the complete two-prime ledger. The inequality
$a_n\leq m(n)$ is not a consequence of finite flatness at $3$; it is separate local information
at $2$ and must be proved by the chosen representation.

For $\mathcal O=\mathbf Z_3$, formula (13.15) reads

$$
\operatorname{rd}(\mathbf Q(T/3^nT))<3^{n+1/2}.
$$

The dependence on $n$ cannot be removed. The rank-one cyclotomic quotient gives

$$
\operatorname{rd}(\mathbf Q(\zeta_{3^n}))=3^{n-1/2},
$$

which already tends to infinity. Thus the residual ceiling $3^{3/2}$ is a fixed-exponent theorem,
not a bound for the entire three-adic torsion tower.

There is also no automatic uniform estimate for the relative steps $L_{n+1}/L_n$. The kernel of
coefficient reduction is a finite $3$-group of bounded matrix rank, but bounded order does not
bound its ramification depth. If a relative finite-flat group over the valuation ring of $L_n$ is
independently supplied, the tower formula applies; otherwise one must use the full-level estimate
(13.15).

To see the tower normalization explicitly, let $K\subseteq L_n\subseteq L_{n+1}$ be local
completions. Then

$$
\frac{d(L_{n+1}/K)}{e(L_{n+1}/K)}
=\frac{d(L_n/K)}{e(L_n/K)}
+\frac1{e(L_n/K)}
\frac{d(L_{n+1}/L_n)}{e(L_{n+1}/L_n)}.
\tag{13.17}
$$

The top-stage cost is discounted by the ramification already present below. Adding two normalized
bounds without this factor is incorrect, while applying a level-one bound to the top step without
a relative model is unjustified.

### 13.5 Residual composita and obstruction fields

Although the full tower has growing cost, every finite collection of exponent-three modules can be
controlled at the residual constant. Let $M_1,\ldots,M_s$ be finite $G_F$-modules killed by $3$,
each supplied at every $u\mid3$ with a finite-flat model, and assume they are all unramified away
from $3$. Their direct sum is killed by $3$, its product model is finite flat, and

$$
F(M_1\oplus\cdots\oplus M_s)
=F(M_1)\cdots F(M_s).
$$

Consequently every finite compositum satisfies

$$
\operatorname{rd}\bigl(F(M_1)\cdots F(M_s)\bigr)
<\operatorname{rd}(F)3^{3/2}.
\tag{13.18}
$$

If all modules have the same tame inertia condition at $2$, the corresponding exact factor from
(13.11) is inserted once, using the inertia order of the direct sum. One must not multiply the
individual root-discriminant ceilings: that would count the same depth repeatedly.

This fixed-exponent principle is particularly useful for first-order difference modules. Suppose
two coefficient-level representations agree modulo an ideal and their difference is encoded over a
finite coefficient algebra of characteristic $3$, for example a dual-number algebra
$k[\epsilon]/(\epsilon^2)$. The underlying additive module is killed by $3$. If an actual
finite-flat model of this full difference representation is constructed, its affine cutout field
again satisfies (13.7), or (13.13) with the recorded tame inertia at $2$, regardless of the high
level at which the difference arose.

There are two indispensable qualifications. First, the diagonal residual constituents alone do
not model the off-diagonal cocycle; the full difference module must have a finite-flat witness.
Second, the conclusion concerns the field cut out by that faithful affine action, not an arbitrary
larger field through which it factors. Under these hypotheses, however, one can repeatedly return
to the residual discriminant ceiling while lifting through a high coefficient tower. This is the
precise mechanism by which fixed-exponent discriminant arguments coexist with the unavoidable
growth in (13.15).

### 13.6 What the three-adic argument receives

We can now package the numerical output without importing any global lower bound or classification
theorem.

**Theorem 13.1 (three-adic torsion-field package).** Let $F$ be a number field, let $T$ be a finite
free module over the integers $\mathcal O$ of a finite extension of $\mathbf Q_3$, and put
$T_n=T/\varpi^nT$ and $L_n=F(T_n)$. Let $m(n)$ be as in (13.1). Assume that $T_n$ admits a
finite-flat model at every place above $3$ and is unramified away from those places and a finite
set $S_0$. Partition $S_0=S_{\mathrm t}\sqcup S_{\mathrm b}$. Assume that inertia at
$v\in S_{\mathrm t}$ is tame of known order $h_{v,n}$, and that the last upper break at
$v\in S_{\mathrm b}$ is at most a known number $R_{v,n}$.

Then

$$
\operatorname{rd}(L_n)
<\operatorname{rd}(F)3^{m(n)+1/2}
\prod_{v\in S_{\mathrm t}}
(Nv)^{(1-1/h_{v,n})/[F:\mathbf Q]}
\prod_{v\in S_{\mathrm b}}
(Nv)^{(1+R_{v,n})/[F:\mathbf Q]}.
\tag{13.19}
$$

At residual level $n=1$, the coefficient-prime factor is always $3^{3/2}$. For $F=\mathbf Q$,
rank two over $\mathbf F_3$, and no auxiliary ramification, one has simultaneously

$$
[L_1:\mathbf Q]\leq48,
\qquad
\operatorname{rd}(L_1)<3^{3/2}.
\tag{13.20}
$$

If the only auxiliary ramification is nontrivial tame inertia of order $3$ at $2$, then

$$
[L_1:\mathbf Q]\leq48,
\qquad
\operatorname{rd}(L_1)<3^{3/2}2^{2/3}.
\tag{13.21}
$$

The same residual ceilings apply to every finite compositum of modeled exponent-three modules and
to every modeled characteristic-three first-order difference module.

**Proof.** The annihilator calculation gives the exponent $m(n)$. At a place above $3$, the local
finite-flat theorem gives (13.4). Summing the local norm exponents uses
$\sum_{u\mid3}e_u^0f_u^0=[F:\mathbf Q]$ and produces $3^{m(n)+1/2}$. At a tame auxiliary place,
Hilbert's formula gives the exact exponent $1-1/h_{v,n}$; at a bounded-depth place, the upper
integral gives the strict coarse exponent $1+R_{v,n}$. Multiplication of the local factors proves
(13.19). The matrix count proves the degree bound in (13.20) and (13.21). Products of finite-flat
models prove the final compositum assertion. $\square$

The data handed to a later discriminant comparison must therefore include $F$, its root
discriminant and signature, the actual residual image or degree bound, the coefficient exponent,
the chosen local finite-flat models, and every auxiliary local contribution. The phrase “small
discriminant” loses exactly the information that distinguishes (13.8), (13.13), and (13.15).

## 14. A theorem package for small ramification

### 14.1 Local package

The preceding work can be assembled into a reusable local statement.

**Theorem 14.1 (local discriminant package).** Let $K/\mathbf Q_\ell$ be finite, normalize $v_K(K^\times)=\mathbf Z$, and put $e_K=v_K(\ell)$. Let $M$ be a finite continuous $G_K$-module killed by $\ell^n$, admitting a finite-flat model over $\mathcal O_K$. Let $L=K(M)$, $e=e(L/K)$, $f=f(L/K)$, and $d=d(L/K)$. Then:

1. $L/K$ is finite Galois with group $\operatorname{im}(G_K\to\operatorname{Aut}M)$.
2. Its upper ramification groups satisfy
   $$
   \operatorname{Gal}(L/K)^u=1
   \quad\text{for }u>
   e_K\left(n+\frac1{\ell-1}\right)-1.
   $$
3. Its different and discriminant exponents satisfy
   $$
   d\leq e\,e_K\left(n+\frac1{\ell-1}\right)-1,
   $$
   $$
   \delta=fd.
   $$
4. Its normalized local root contribution satisfies
   $$
   \frac de<e_K\left(n+\frac1{\ell-1}\right).
   $$
5. Every submodule, quotient, finite direct sum, Cartier dual, and generic term of a given faithfully flat exact model sequence satisfies the corresponding bound with its actual exponent.

The fifth clause does not assert that arbitrary generic extensions of finite-flat endpoints are finite flat.

**Proof.** The kernel of the finite action is open and normal, proving the first clause. Theorem
8.1 and faithfulness of the action on $K(M)$ prove the upper cutoff. Substitution in the exact
upper-numbered different formula gives

$$
d\leq(e-1)+e\left(
e_K\left(n+\frac1{\ell-1}\right)-1\right)
=e\,e_K\left(n+\frac1{\ell-1}\right)-1.
$$

The identity $\delta=fd$ follows by norming the different, and division by $e$ gives the strict
normalized bound. Schematic closure and represented quotients treat submodules and quotients,
products treat direct sums, Cartier duality treats twisted duals, and the supplied integral middle
group treats exact extensions. Each operation preserves its actual annihilating exponent.
$\square$

### 14.2 Global package

The local theorem becomes a global statement only after the places above $\ell$ are summed with
their residue degrees. This section packages that cancellation and keeps every auxiliary place
visible.

**Theorem 14.2 (global root-discriminant package).** Let $F$ be a number field and $M$ a finite $G_F$-module killed by $\ell^n$. Assume:

- for every $v\mid\ell$, $M|_{G_{F_v}}$ admits a finite-flat model;
- outside the places above $\ell$ and a finite set $S$, the module is unramified;
- for each $v\in S$, the local field cut out by $M$ has last upper break at most $R_v$.

Then for $L=F(M)$,

$$
\boxed{
\operatorname{rd}(L)
<\operatorname{rd}(F)\,
\ell^{n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.
}
$$

At tame $v\in S$, the corresponding factor may be replaced by

$$
(Nv)^{(1-1/e_v)/[F:\mathbf Q]}.
$$

If sharper inertia-size information is available, the integral

$$
1-\frac1{e_v}+
\int_0^{R_v}\left(1-\frac1{|G_v^u|}\right)du
$$

may replace $1+R_v$. Thus the theorem is a package, not an instruction to discard known local data.

**Proof.** At $v\mid\ell$, Theorem 14.1 gives

$$
\frac{d_v}{e_v}
<e(F_v/\mathbf Q_\ell)
\left(n+\frac1{\ell-1}\right).
$$

Since $Nv=\ell^{f(F_v/\mathbf Q_\ell)}$ and

$$
\sum_{v\mid\ell}
e(F_v/\mathbf Q_\ell)f(F_v/\mathbf Q_\ell)
=[F:\mathbf Q],
$$

the product of all coefficient-prime contributions is strictly less than
$\ell^{n+1/(\ell-1)}$. At $v\in S$, the cutoff-to-different bound gives
$d_v/e_v<1+R_v$. Insert these inequalities in the global localization formula. If $v$ is tame,
Hilbert's formula gives the exact replacement $d_v/e_v=1-1/e_v$. Retaining the full upper
integral instead of bounding its integrand by $1$ gives the final refinement. $\square$

### 14.3 Tower package

Coefficient towers mix two independent phenomena: bounded matrix kernels and increasing
ramification depth. The next theorem records both without using the former as a substitute for the
latter.

**Theorem 14.3 (level tower package).** Let $T$ be a rank-$r$ $\mathbf Z_\ell$-lattice with continuous $G_F$-action, put $M_n=T/\ell^nT$ and $F_n=F(M_n)$, and assume each $M_n$ satisfies the local finite-flat hypotheses at $v\mid\ell$. Then:

$$
F_1\subseteq F_2\subseteq\cdots,
\qquad [F_{n+1}:F_n]\leq\ell^{r^2},
$$

and at every $v\mid\ell$ the last upper break of $(F_n)_w/F_v$ is at most

$$
e_v^0\left(n+\frac1{\ell-1}\right)-1.
$$

If ramification away from $\ell$ is controlled by a fixed set $S$ with fixed local cutoffs, then

$$
\operatorname{rd}(F_n)
<\operatorname{rd}(F)\,
\ell^{n+1/(\ell-1)}
\prod_{v\in S}(Nv)^{(1+R_v)/[F:\mathbf Q]}.
$$

The degree step is uniform; the displayed full-level root bound grows with $n$. A uniform bound for a selected subtower requires an additional argument controlling its relative ramification, and the theorem deliberately does not conceal that requirement.

**Proof.** Reduction $M_{n+1}\twoheadrightarrow M_n$ gives
$F_n\subseteq F_{n+1}$. An element of the relative Galois group acts on $M_{n+1}$ by a matrix

$$
1+\ell^nA\pmod{\ell^{n+1}},
\qquad A\in M_r(\mathbf F_\ell).
$$

The map to $A$ is injective and the target has $\ell^{r^2}$ elements, proving the step-degree
bound. Theorem 8.1 applied to $M_n$ at $v\mid\ell$ gives the displayed last-break bound. Applying
Theorem 14.2 at each fixed $n$ gives the root-discriminant inequality. Nothing in this proof
constructs a relative finite-flat model over $F_n$, which is why no level-independent relative
ramification conclusion is included. $\square$

### 14.4 Boundary with discriminant lower bounds

The results above are entirely algebraic. They turn finite image, local upper cutoffs, and finite-flat integral geometry into explicit upper bounds for root discriminants. They do not decide whether a number field of a given degree and root discriminant can exist. That is a different problem, involving global lower bounds and signature.

The package is designed so that such a comparison can begin without revisiting local normalization. The input handed forward is:

- an exact field $F(M)$ defined by a kernel;
- a degree or image bound;
- a finite ramification set;
- explicit local upper cutoffs, with strict endpoints recorded;
- an absolute root-discriminant upper bound including $\operatorname{rd}(F)$;
- stability under the modeled subquotients, duals, sums, and tower levels actually used.

No analytic lower bound is assumed or proved here.

## 15. Conclusion

A finite representation becomes arithmetic when its kernel is read as a field. The discriminant of that field is exactly the Artin conductor of the regular representation of its finite image, while Hilbert's formula expresses the same quantity as accumulated ramification depth. Upper numbering is the indispensable scale: it passes to quotient fields and turns a last-break estimate into a degree-independent root-discriminant bound.

Finite-flat geometry supplies the unusually strong estimate at the residue characteristic. The augmentation ideal sees multiplication by $\ell$ as a competition between the linear term $\ell x$ and terms of degree $\ell$. That competition creates the torsion-free congruence radius $e_K/(\ell-1)$. Converting integral congruence to upper numbering contributes $e_K-1$, and passing through the preceding $n-1$ multiplication layers adds $(n-1)e_K$. The resulting upper cutoff is $e_K(n+1/(\ell-1))-1$. Hilbert's formula adds the tame baseline, whose $1$ cancels that terminal $-1$. At level $\ell$ over $\mathbf Q_\ell$, the final normalized exponent is therefore $\ell/(\ell-1)$.

The global formula preserves every normalization: residue degrees enter local discriminants, local ramification indices disappear only after division by total degree, primes above $\ell$ recombine through $\sum e_vf_v=[F:\mathbf Q]$, and the base field remains as $\operatorname{rd}(F)$. Auxiliary tame or bounded-depth ramification contributes its own explicit factor. Subfields improve root discriminants, composita require care, and compatible finite-flat products often give a maximum cutoff where a naive compositum estimate would add costs.

For the three-adic argument this general mechanism has now been reduced to a concrete ledger. A
modeled residual rank-two module over $\mathbf F_3$, unramified outside $3$, cuts out a field of
degree at most $48$ and root discriminant strictly below

$$
3^{3/2}.
$$

If its only additional ramification is tame cubic inertia at $2$, the exact replacement is

$$
3^{3/2}2^{2/3}.
$$

At coefficient level $\varpi^n$, the exponent is governed by
$m(n)=\lceil n/v_\varpi(3)\rceil$ and the coefficient-prime factor becomes
$3^{m(n)+1/2}$. Residual direct sums and modeled characteristic-three difference modules return to
the first ceiling, whereas the full torsion tower necessarily has growing root discriminant.
These distinctions are the numerical content required from the phrase “hardly ramified.”

The resulting theorem package is ready for towers arising from torsion and change-of-prime arguments. It states exactly which bounds are uniform, which grow with level, and which constructions preserve a chosen integral model. The next stage may compare these algebraic upper bounds with global lower bounds. Here the durable conclusion is already complete: integral geometry controls the last local break, ramification theory converts the break into a different, and the global product formula turns those local differents into an explicit bound on the field cut out by the representation.
