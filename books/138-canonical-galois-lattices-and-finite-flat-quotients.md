# Canonical Galois Lattices and Finite-Flat Quotients

## Contents

1. [The integral problem](#1-the-integral-problem)
   - [From a rational packet to an integral object](#11-from-a-rational-packet-to-an-integral-object)
   - [The three meanings of canonical](#12-the-three-meanings-of-canonical)
   - [Standing notation and conventions](#13-standing-notation-and-conventions)
   - [The proof architecture](#14-the-proof-architecture)
2. [Saturation and lattices over a coefficient DVR](#2-saturation-and-lattices-over-a-coefficient-dvr)
   - [Why intersection is the correct operation](#21-why-intersection-is-the-correct-operation)
   - [Saturated submodules](#22-saturated-submodules)
   - [Rational subspaces and primitive lattices](#23-rational-subspaces-and-primitive-lattices)
   - [Sums, intersections, and index defects](#24-sums-intersections-and-index-defects)
   - [Dual lattices and perfectness](#25-dual-lattices-and-perfectness)
3. [Integral Hecke localization](#3-integral-hecke-localization)
   - [The faithful integral Hecke image](#31-the-faithful-integral-hecke-image)
   - [Localization and congruence blocks](#32-localization-and-congruence-blocks)
   - [Branch specialization without an integral projector](#33-branch-specialization-without-an-integral-projector)
   - [Freeness over the coefficient ring](#34-freeness-over-the-coefficient-ring)
   - [A two-branch calculation](#35-a-two-branch-calculation)
4. [Integral multiplicity extraction](#4-integral-multiplicity-extraction)
   - [The Morita problem](#41-the-morita-problem)
   - [Split orders and projective generators](#42-split-orders-and-projective-generators)
   - [The integral evaluation theorem](#43-the-integral-evaluation-theorem)
   - [The canonical multiplicity lattice](#44-the-canonical-multiplicity-lattice)
   - [The denominator ledger](#45-the-denominator-ledger)
5. [The canonical curve lattice](#5-the-canonical-curve-lattice)
   - [The cohomological construction](#51-the-cohomological-construction)
   - [Galois and Hecke stability](#52-galois-and-hecke-stability)
   - [Freeness and rank two](#53-freeness-and-rank-two)
   - [Fine and coarse levels](#54-fine-and-coarse-levels)
   - [Comparison with an abelian quotient](#55-comparison-with-an-abelian-quotient)
6. [Pairings, coefficient involutions, and Cartier duality](#6-pairings-coefficient-involutions-and-cartier-duality)
   - [The integral adjoint pairing](#61-the-integral-adjoint-pairing)
   - [Duality indices](#62-duality-indices)
   - [Coefficient actions on the dual](#63-coefficient-actions-on-the-dual)
   - [Finite-level Cartier duals](#64-finite-level-cartier-duals)
7. [Geometric finite-flat carriers](#7-geometric-finite-flat-carriers)
   - [Good reduction and torsion](#71-good-reduction-and-torsion)
   - [Marked coefficient-linear carriers](#72-marked-coefficient-linear-carriers)
   - [Why kernels of coefficient endomorphisms are delicate](#73-why-kernels-of-coefficient-endomorphisms-are-delicate)
   - [The safe quotient construction](#74-the-safe-quotient-construction)
8. [Every coefficient quotient](#8-every-coefficient-quotient)
   - [Open ideals and generic relation submodules](#81-open-ideals-and-generic-relation-submodules)
   - [Closure and represented quotient](#82-closure-and-represented-quotient)
   - [Coefficient actions](#83-coefficient-actions)
   - [Exact sequences for nested ideals](#84-exact-sequences-for-nested-ideals)
   - [Ranks and flatness](#85-ranks-and-flatness)
9. [Compatible transition systems](#9-compatible-transition-systems)
   - [The quotient functor on ideals](#91-the-quotient-functor-on-ideals)
   - [Principal levels](#92-principal-levels)
   - [Inverse limits and recovery of the lattice](#93-inverse-limits-and-recovery-of-the-lattice)
   - [Uniqueness of the transition maps](#94-uniqueness-of-the-transition-maps)
10. [The absolutely unramified low-weight route](#10-the-absolutely-unramified-low-weight-route)
    - [The exact range](#101-the-exact-range)
    - [From a strongly divisible lattice to all quotients](#102-from-a-strongly-divisible-lattice-to-all-quotients)
    - [From compatible quotients back to the lattice](#103-from-compatible-quotients-back-to-the-lattice)
    - [Nonflat coefficient ideals](#104-nonflat-coefficient-ideals)
    - [The prime two and ramified boundaries](#105-the-prime-two-and-ramified-boundaries)
11. [Base change and descent](#11-base-change-and-descent)
    - [Changing the local ground field](#111-changing-the-local-ground-field)
    - [Unramified base change in the filtered description](#112-unramified-base-change-in-the-filtered-description)
    - [Coefficient extension and the trace dual](#113-coefficient-extension-and-the-trace-dual)
    - [Descent requires integral data](#114-descent-requires-integral-data)
13. [Independence and its limits](#13-independence-and-its-limits)
    - [Projector and presentation independence](#131-projector-and-presentation-independence)
    - [Splitting fields and matrix coordinates](#132-splitting-fields-and-matrix-coordinates)
    - [Integral PEL presentations](#133-integral-pel-presentations)
    - [Isogenies and denominator primes](#134-isogenies-and-denominator-primes)
    - [Carrier independence](#135-carrier-independence)
14. [Failure atlas](#14-failure-atlas)
    - [A rational projector with a nonunit denominator](#141-a-rational-projector-with-a-nonunit-denominator)
    - [A stable lattice with the wrong residual extension](#142-a-stable-lattice-with-the-wrong-residual-extension)
    - [Rational crystallinity without an integral lattice](#143-rational-crystallinity-without-an-integral-lattice)
    - [Flat base change versus descent](#144-flat-base-change-versus-descent)
15. [The canonical-lattice and quotient theorem](#15-the-canonical-lattice-and-quotient-theorem)
    - [The hypothesis ledger](#151-the-hypothesis-ledger)
    - [The curve theorem](#152-the-curve-theorem)
    - [Duality and base-change refinements](#153-duality-and-base-change-refinements)
16. [Dependency audit and conclusion](#16-dependency-audit-and-conclusion)
    - [Exact use of the prerequisites](#161-exact-use-of-the-prerequisites)
    - [What has been proved](#162-what-has-been-proved)
    - [Conclusion](#163-conclusion)

## 1. The integral problem

### 1.1 From a rational packet to an integral object

A weight-two automorphic packet produces a two-dimensional representation over a local coefficient field only after several rational operations. One isolates a characteristic-zero Hecke block, splits its simple algebra, and removes the finite level module by a multiplicity-space construction. The result has the expected Frobenius polynomials and determinant. None of those operations, by itself, selects a lattice.

The missing integral object matters most at the coefficient prime. Let $L_\lambda$ be a finite extension of $\mathbf Q_\ell$, let $\mathcal O_\lambda$ be its ring of integers, and let $V_\lambda$ be a two-dimensional $L_\lambda$-representation. Any continuous action preserves some full $\mathcal O_\lambda$-lattice. Different stable lattices can have different nonsplit residual extensions, however, and an arbitrary one need not arise from a finite-flat group over a place above $\ell$. Existence of a stable lattice is therefore far weaker than the integral statement required in arithmetic applications.

Geometry supplies a preferred ambient lattice: integral degree-one cohomology of a compact Shimura curve. The packet subspace meets that ambient lattice in a saturated lattice. This intersection is canonical relative to the geometric carrier, but it can still have dimension larger than two because it retains the finite Hecke multiplicity. Removing that multiplicity integrally requires a split order and a projective generator, not merely a rational matrix-algebra isomorphism.

At the coefficient prime a second issue appears. Even after a free rank-two lattice $T_\lambda$ has been obtained, the quotients

$$
T_\lambda/I T_\lambda
$$

for open ideals $I\subset\mathcal O_\lambda$ must be generic fibers of finite locally free commutative group schemes, with compatible maps as $I$ varies. A rational crystalline statement does not produce these group schemes. They come either from an actual good-reduction abelian carrier with integral coefficient action, or, in the absolutely unramified small-weight range, from an integral Fontaine--Laffaille lattice.

The purpose of this book is to construct these objects and to delimit their canonicity. The word *canonical* will never mean “determined by the rational representation alone.” It will mean “obtained functorially from a fixed integral geometric and coefficient datum, without a choice of eigenvector, projector formula, basis, or presentation.”

### 1.2 The three meanings of canonical

Three statements must be distinguished.

1. A rational subspace $U\subset M\otimes K$ has a unique saturated intersection $M\cap U$ inside a fixed lattice $M$.
2. A finite Galois submodule has a unique finite-flat closure inside a fixed finite-flat group over a discrete valuation ring.
3. A rational representation has a unique stable lattice up to homothety.

The first two statements are true in the situations used here. The third is false in general. The first is linear algebra over a discrete valuation ring. The second is schematic closure and saturation of a Hopf ideal. Both are relative to an ambient object. Neither says that a different ambient cohomology lattice, a different isogenous abelian variety, or a different integral model yields the same lattice.

There is a further absolute uniqueness theorem in the low-weight unramified range. If $p>2$ and the local base is $W(k)$ for a perfect field $k$ of characteristic $p$, finite-flat $p$-power group schemes are rigid through their marked generic fibers. This makes each finite-level model unique. It still does not make the underlying rational representation choose a stable lattice: the marked generic module must already have been specified.

Our canonicity claims will therefore always name the datum relative to which they hold. This discipline is especially important at primes dividing a projector denominator, the degree of an isogeny, the discriminant of a Hecke order, or the order of a coarse-level deck group.

### 1.3 Standing notation and conventions

Let $\mathcal O$ be a complete discrete valuation ring of characteristic zero with uniformizer $\varpi$, fraction field $L$, and residue field $\kappa$. A **lattice** in a finite-dimensional $L$-space is a finite free $\mathcal O$-submodule spanning that space. For a lattice $M$ and a subspace $U\subset M_L=M\otimes_\mathcal O L$, write

$$
M[U]=M\cap U.
$$

All Hecke algebras are their faithful finite images on the cohomology group under discussion. This removes operators which act as zero and makes localization finite over the coefficient ring. The symbol $\mathfrak m$ denotes a maximal ideal of such an integral Hecke image, and $M_\mathfrak m$ denotes localization.

At a place $u$ above the rational prime $p$, write $K=E_u$, $R=\mathcal O_K$, and $G_K=\operatorname{Gal}(\bar K/K)$. A finite-flat model means a finite locally free commutative $R$-group scheme together with a marking of its generic fiber. Coefficient actions are unital ring homomorphisms into its endomorphism ring.

Cartier duality is denoted by $G^D$. On a finite generic module $M$ killed by $n$, with $n$ invertible in $K$, it realizes

$$
M^*(1)=\operatorname{Hom}(M,\mu_n(\bar K)).
$$

The twist is part of the formula. An ordinary module dual and a Cartier dual are not interchangeable.

For the cohomological representations already constructed, geometric Frobenius and Tate twists use the convention

$$
\Phi_u\mid L(1)=q_u^{-1}.
$$

Nothing in the finite-flat construction will change this convention. When a covariant abelian Tate module is used as a carrier, the comparison with the cohomological normalization will be stated explicitly rather than hidden in a dual or twist.

### 1.4 The proof architecture

The construction proceeds in four layers.

First, saturation turns a rational packet subspace into a primitive lattice inside integral cohomology. This step is insensitive to the formula used for the rational projector.

Second, integral Morita theory removes oldvector multiplicity. It works exactly when the localized Hecke order is split by a projective generator and the evaluation map has no index defect. Under those hypotheses the multiplicity lattice is free of rank two. Without them the saturated packet lattice remains canonical, but a canonical rank-two direct factor is not asserted.

Third, an integral coefficient-prime carrier is supplied. In the geometric route it is the torsion of a good-reduction abelian scheme with integral coefficient action. In the filtered route it is a strongly divisible lattice of weights $[0,1]$ over an absolutely unramified base with $p>2$.

Fourth, every open coefficient quotient is constructed by closing the generic relation submodule inside one finite-flat ambient group and taking the represented quotient. This produces the coefficient action and all transition maps simultaneously. Cartier duality, flat base change, and nested-ideal exact sequences then follow from the exact calculus of finite-flat groups.

## 2. Saturation and lattices over a coefficient DVR

### 2.1 Why intersection is the correct operation

A rational idempotent $e$ produces a subspace $U=eM_L$. Applying $e$ to $M$ is generally unsafe: if $e$ has a nonunit denominator, then $eM$ need not lie in $M$. Multiplying $e$ by a denominator produces a submodule, but its index depends on the chosen denominator. Intersection avoids both defects.

The lattice

$$
M[U]=M\cap U
$$

depends only on $M$ and $U$. It contains every integral vector lying in the packet subspace and no vector supported on a different rational block. It is therefore the largest submodule of $M$ with rational span contained in $U$.

This construction remembers congruences. If $U$ and a complementary rational block fail to split integrally, $M[U]$ is still primitive, but the sum of the two intersections can have finite index in $M$. That index is not an inconvenience to be discarded: it is the integral trace of congruent Hecke branches.

### 2.2 Saturated submodules

A submodule $N\subset M$ is **saturated** if $M/N$ is torsion-free. Since $\mathcal O$ is a DVR, the following conditions are equivalent:

$$
\begin{aligned}
&M/N\text{ is torsion-free};\\
&\varpi m\in N\Longrightarrow m\in N;\\
&N=M\cap N_L\text{ inside }M_L.
\end{aligned} \tag{2.1}
$$

**Lemma 2.1.** Every saturated submodule of a finite free $\mathcal O$-module is finite free and is a direct summand as an $\mathcal O$-module.

**Proof strategy.** Torsion-freeness over a DVR gives freeness; the quotient is then free, so its short exact sequence splits linearly.

Let $N\subset M$ be saturated. Both $N$ and $M/N$ are finite torsion-free $\mathcal O$-modules and hence finite free. Since a free module is projective, the surjection $M\to M/N$ admits an $\mathcal O$-linear section. Thus $M\simeq N\oplus N'$ as modules. The complement $N'$ is not canonical and need not be stable under Galois or Hecke. $\square$

The last sentence is essential. Saturation proves freeness and primitive embedding, not an equivariant direct-summand theorem.

**Lemma 2.2.** If a group $\Gamma$ and an $\mathcal O$-algebra $A$ preserve $M$ and the rational subspace $U$, then they preserve $M[U]$.

**Proof.** For $x\in M\cap U$, both actions send $x$ into $M$ by integrality and into $U$ by rational stability. Hence they send it into the intersection. $\square$

### 2.3 Rational subspaces and primitive lattices

**Proposition 2.3 (primitive-intersection theorem).** Let $M$ be a lattice in $V$ and let $U\subset V$ be an $L$-subspace. Then:

1. $M[U]$ is a saturated lattice in $U$;
2. it is the unique largest submodule $N\subset M$ satisfying $N_L\subset U$;
3. for every flat extension of DVRs $\mathcal O\to\mathcal O'$ with fraction field $L'$, one has

   $$
   M[U]\otimes_\mathcal O\mathcal O'
   =(M\otimes\mathcal O')[U\otimes_LL']; \tag{2.2}
   $$

4. if $f:M\to M'$ is integral and $f_L(U)\subset U'$, then

   $$
   f(M[U])\subset M'[U'].
   $$

**Proof strategy.** The quotient embeds into the vector-space quotient $V/U$, which proves saturation. Flat base change preserves the saturated exact sequence.

The composite $M\to V\to V/U$ has kernel $M[U]$. Therefore $M/M[U]$ embeds in an $L$-vector space and is torsion-free. This proves saturation. Since $M[U]$ spans $U$—clear after choosing a basis of $M$ and clearing denominators in a basis of $U$—it is a lattice in $U$.

If $N_L\subset U$, then every $n\in N$ lies in $M\cap U$, proving maximality and uniqueness. Tensor the exact sequence

$$
0\longrightarrow M[U]\longrightarrow M\longrightarrow M/M[U]\longrightarrow0
$$

with the flat module $\mathcal O'$. Its cokernel remains torsion-free and its generic kernel is $U\otimes_LL'$. The characterization by contraction in (2.1) gives (2.2). Functoriality is immediate from the definition. $\square$

Thus the saturated packet lattice is independent of an interpolation polynomial representing the packet idempotent. It depends only on the rational packet subspace.

### 2.4 Sums, intersections, and index defects

Let $V=U\oplus W$ rationally. The natural map

$$
M[U]\oplus M[W]\longrightarrow M \tag{2.3}
$$

is injective with finite cokernel, but need not be surjective. To see finiteness, tensor with $L$: it becomes the isomorphism $U\oplus W\simeq V$. Its cokernel is therefore torsion. The length

$$
\delta_M(U,W)=operatorname{length}_\mathcal O
M/(M[U]+M[W]) \tag{2.4}
$$

is the **splitting defect**. It vanishes exactly when the rational decomposition is integral.

Suppose $U$ is the eigenspace for $T$ with eigenvalue $a$ and $W$ is the eigenspace with eigenvalue $b$. If $a-b$ is a unit, the Lagrange projector

$$
\frac{T-b}{a-b}
$$

is integral and (2.3) splits. If $a-b\in(\varpi)$, the denominator can create a positive defect. This elementary observation is the local algebra behind congruence modules and explains why a rational packet projector cannot be treated as an integral endomorphism without checking its denominator.

Raw intersections of images can also fail to be saturated. The safe operations are

$$
N_1\wedge N_2=M\cap(N_{1,L}\cap N_{2,L}),
$$

and

$$
N_1\vee N_2=M\cap(N_{1,L}+N_{2,L}).
$$

They are the saturated meet and join inside the fixed ambient lattice. Their ranks satisfy the ordinary dimension formula, while the difference between raw and saturated operations is measured by finite-length modules.

Smith normal form makes the defect concrete. Choose bases of $M$ and of the sublattice $M[U]+M[W]$. The inclusion is represented by a diagonal matrix

$$
\operatorname{diag}(\varpi^{a_1},\ldots,\varpi^{a_r}),
\qquad a_i\ge0. \tag{2.5}
$$

Then

$$
\delta_M(U,W)=\sum_i a_i. \tag{2.6}
$$

The rational decomposition is integral exactly when every $a_i=0$. Under a flat extension of coefficient DVRs of ramification index $e'$, the valuation-normalized defect scales by $e'$. Under an unramified coefficient extension the exponents are unchanged. This is why enlarging the residue field does not repair a projector denominator, while ramified scalar extension can alter its measured length without making the original splitting canonical.

The same elementary divisors control the map from a lattice to the sum of its rational packet branches. A congruence prime is precisely a place where at least one exponent is positive. Saturating each branch removes torsion from its individual quotient, but it does not make the branches sum to the ambient lattice.

### 2.5 Dual lattices and perfectness

Let $M^\vee=\operatorname{Hom}_\mathcal O(M,\mathcal O)$ and let $\langle, ,,\rangle:V\times V'\to L$ be a perfect pairing. For a lattice $M\subset V$, define

$$
M^\#=\{y\in V':\langle M,y\rangle\subset\mathcal O\}. \tag{2.7}
$$

Then $M^\#$ is a lattice and $(M^\#)^\#=M$. If $N\subset M$ is saturated, restriction

$$
M^\vee\longrightarrow N^\vee \tag{2.8}
$$

is surjective because $M/N$ is free. Its kernel is the annihilator of $N$ and is saturated.

A pairing on $M$ is **perfect** if the induced map $M\to M^\vee$ is an isomorphism. Rational nondegeneracy only says that this map has finite cokernel. Its length, or equivalently the valuation of its determinant, is the duality defect. Multiplying a rational pairing by a scalar shifts this defect. Consequently a polarization which is unique only up to a nonunit scalar does not canonically make a lattice self-dual.

These module facts are the linear shadow of Cartier duality. At finite-flat level, a saturated subgroup has a finite-flat annihilator and the quotient dual is that annihilator. The scheme-theoretic result will be used only after the relevant groups have been constructed.

## 3. Integral Hecke localization

### 3.1 The faithful integral Hecke image

Let $X/E$ be one of the smooth projective geometric carriers and let

$$
M=H^i_{\mathrm{et}}(X_{\bar E},\mathcal O)/\text{torsion}
$$

in degree one. For a curve in degree one there is no torsion. Let $\mathbb T$ be the image in $\operatorname{End}_\mathcal O(M)$ of the integral Hecke correspondences which are defined on the selected component union. Then $\mathbb T$ is a finite torsion-free $\mathcal O$-algebra.

The word “image” has three advantages. It makes $\mathbb T$ finite, makes its action faithful, and ensures that every equality in $\mathbb T$ is an equality of actual integral endomorphisms. Galois commutes with $\mathbb T$ because pullback and proper trace are defined over $E$.

If $\mathfrak m\subset\mathbb T$ is maximal, localization gives

$$
M_\mathfrak m=M\otimes_\mathbb T\mathbb T_\mathfrak m. \tag{3.1}
$$

Since localization is exact and $M$ is finite free over $\mathcal O$, $M_\mathfrak m$ is a finite torsion-free, hence free, $\mathcal O$-module. It remains Galois stable and carries the faithful local Hecke action relevant to a congruence class.

### 3.2 Localization and congruence blocks

After tensoring with $L$, the finite semisimple Hecke image decomposes into simple blocks. A maximal ideal $\mathfrak m$ can meet several characteristic-zero blocks whose systems of eigenvalues are congruent modulo $\varpi$. Thus

$$
M_\mathfrak m\otimes L
=\bigoplus_{\theta\equiv\mathfrak m}M(\theta) \tag{3.2}
$$

can have more than one summand. Localization is integral and canonical; selecting one branch $\theta$ is rational.

This is precisely why the localized lattice should not be called an eigenspace. It contains congruence extensions between rational branches. Those extensions can be arithmetically useful, and a nonintegral projector should not erase them before the problem has been stated.

**Proposition 3.1.** The lattice $M_\mathfrak m$ is independent of a generating set of Hecke correspondences, provided the generating sets have the same faithful image on $M$.

**Proof.** Both constructions are localization of the same finite subalgebra of $\operatorname{End}_\mathcal O(M)$. A presentation of that algebra by generators and relations is irrelevant to the tensor product (3.1). $\square$

### 3.3 Branch specialization without an integral projector

Let $\theta:\mathbb T_\mathfrak m\to\mathcal O'$ be a homomorphism to the ring of integers of a finite extension $L'/L$. The naive branch quotient is

$$
C_\theta=M_\mathfrak m\otimes_{\mathbb T_\mathfrak m,\theta}\mathcal O'. \tag{3.3}
$$

It can have $\mathcal O'$-torsion because tensoring along $\theta$ need not be flat. Define its primitive quotient by

$$
C_\theta^{\mathrm{tf}}=C_\theta/C_\theta[\varpi^\infty]. \tag{3.4}
$$

This construction is canonical and does not require an integral packet projector. Its generic fiber is the $\theta$-specialization of the localized rational cohomology. It can still contain an oldvector multiplicity, which will be removed in Chapter 4.

The same lattice can be described as the image of $C_\theta$ in its generic fiber. This description makes functoriality immediate: every integral Galois- or Hecke-equivariant map between localized cohomology modules induces a map between the torsion-free specializations.

It also has a useful universal property. Let $N$ be a torsion-free $\mathcal O'$-module on which $\mathbb T_\mathfrak m$ acts through $\theta$. Every $\mathbb T_\mathfrak m$-linear map $M_\mathfrak m\to N$ factors uniquely through $C_\theta$ by the tensor universal property. Since $N$ has no torsion, the factor kills the torsion of $C_\theta$ and therefore factors uniquely through $C_\theta^{\mathrm{tf}}$. Thus (3.4) is the maximal torsion-free branch quotient of the localized lattice.

This quotient description and the saturated-intersection description serve different purposes. Suppose the rational $\theta$-block is a quotient $q_L:M_{\mathfrak m,L}\to H_\theta$. The image

$$
q_L(M_\mathfrak m)\subset H_\theta \tag{3.5}
$$

is a lattice, and its saturation inside any specified ambient lattice of $H_\theta$ is the primitive branch lattice. If $q_L$ is induced by an integral quotient with torsion-free target, (3.5) is already the universal quotient (3.4). If $q_L$ uses a rational idempotent, the two can differ by the projector denominator. Naming whether the packet is realized as a subspace or a quotient prevents an implicit switch between intersection and image lattices.

**Lemma 3.3 (branch comparison).** Assume a rational branch is both a direct summand $U\subset M_L$ and a quotient of $M_L$, and suppose the rational inclusion and quotient are adjoint with composite the identity on $U$. If both maps preserve the chosen integral lattices, then the saturated intersection $M[U]$ and the torsion-free branch quotient are canonically isomorphic. If their composite is multiplication by a nonzero $c\in\mathcal O$, their cokernels are killed by $c$, but equality need not hold when $c$ is a nonunit.

**Proof.** In the first case the integral quotient restricts to a map from $M[U]$ to the branch quotient, and the integral inclusion gives its inverse. The identities hold rationally and hence integrally because the modules are torsion-free. In the second case the same composites equal $c$; kernel vanishes after rationalization and each cokernel is annihilated by $c$. A nonunit $c$ permits a positive finite length. $\square$

This lemma is the linear form of many pullback--trace and isogeny comparisons used later.

### 3.4 Freeness over the coefficient ring

**Theorem 3.2 (coefficient freeness).** The modules $M_\mathfrak m$ and $C_\theta^{\mathrm{tf}}$ are finite free over their respective coefficient DVRs. Their ranks are the dimensions of their generic fibers.

**Proof strategy.** Both modules are finite and torsion-free over a DVR.

Localization makes $M_\mathfrak m$ a finite $\mathcal O$-module. It embeds into its rationalization, so it is torsion-free. Hence it is free. The quotient (3.4) is finite and torsion-free over $\mathcal O'$, hence free. Tensoring either with the fraction field preserves rank and identifies it with the corresponding vector-space dimension. $\square$

This theorem proves freeness over the coefficient ring, not over the local Hecke algebra. Freeness of rank two over $\mathbb T_\mathfrak m$ is a much stronger multiplicity-one assertion and is not a formal consequence of cohomological torsion-freeness.

### 3.5 A two-branch calculation

Let

$$
\mathbb T=\{(a,b)\in\mathcal O\times\mathcal O:a\equiv b\pmod\varpi\}
$$

act on $M=\mathcal O\times\mathcal O$. Rationally there are two idempotents $(1,0)$ and $(0,1)$, but neither lies in $\mathbb T$. The two saturated branch lattices are the coordinate axes, and their sum is all of $M$ as an $\mathcal O$-module. The local Hecke algebra nevertheless does not split as a product: the congruence is stored in its multiplication.

If instead one chooses the lattice

$$
M'=\{(x,y)\in\mathcal O^2:x\equiv y\pmod\varpi\},
$$

then the intersections with the two rational axes are $\varpi\mathcal O\times0$ and $0\times\varpi\mathcal O$. Their sum has index $|\kappa|$ in $M'$. The rational projectors are unchanged, but the integral splitting defect is nonzero.

The example demonstrates two independent facts. A rational block has a canonical saturated intersection once the ambient lattice is fixed, and changing the ambient lattice can change that intersection. It also demonstrates why independence from *integral choices* must be proved through a canonical geometric identification, not inferred from equality of rational Hecke eigenvalues.

## 4. Integral multiplicity extraction

### 4.1 The Morita problem

The rational curve block has the form

$$
P_L\otimes_L V_L, \tag{4.1}
$$

where $P_L$ is the simple finite Hecke module and $V_L$ is the two-dimensional Galois multiplicity space. At old level $P_L$ can have dimension greater than one. A lattice in the entire block therefore has rank $2\dim P_L$, not rank two.

Over $L$, the simple Hecke algebra acting on $P_L$ is a matrix algebra after a splitting field has been chosen. The functor

$$
H\longmapsto\operatorname{Hom}_A(P,H) \tag{4.2}
$$

then recovers the multiplicity space. Over $\mathcal O$, this formula is valid only if an integral order $\mathcal A$, an integral lattice $\mathcal P$, and the evaluation map have the appropriate projectivity. A rational identity $A_L\simeq M_d(L)$ does not make every order in $A_L$ Morita equivalent to $\mathcal O$.

The integral problem is thus not to choose a basis of oldforms. It is to show that the level module is a projective generator for the localized order and that evaluation loses no finite index.

### 4.2 Split orders and projective generators

Let $\mathcal A$ be an $\mathcal O$-order in $M_d(L)$. An **integral split Morita datum** consists of a finite projective left $\mathcal A$-module $\mathcal P$, free of rank $d$ over $\mathcal O$, such that

$$
\mathcal A\xrightarrow{\sim}\operatorname{End}_\mathcal O(\mathcal P). \tag{4.3}
$$

Then $\mathcal P$ is a projective generator and its right dual

$$
\mathcal P^\vee_{\mathcal A}
=\operatorname{Hom}_{\mathcal A}(\mathcal P,\mathcal A)
$$

implements the inverse Morita functor. The model example is $\mathcal A=M_d(\mathcal O)$ and $\mathcal P=\mathcal O^d$.

An arbitrary order need not satisfy (4.3). At primes dividing its discriminant, it can fail to be maximal or Azumaya. Even for a maximal order in a nonsplit central simple algebra, a rank-$d$ module over $\mathcal O$ does not exist until the algebra has been split. These are genuine integral obstructions, not artifacts of coordinates.

### 4.3 The integral evaluation theorem

**Theorem 4.1 (integral Morita evaluation).** Assume $(\mathcal A,\mathcal P)$ is an integral split Morita datum. For every left $\mathcal A$-module $H$ which is finite free over $\mathcal O$, put

$$
W(H)=\operatorname{Hom}_{\mathcal A}(\mathcal P,H). \tag{4.4}
$$

Then $W(H)$ is finite free over $\mathcal O$, and evaluation is an isomorphism

$$
\mathcal P\otimes_\mathcal O W(H)
\xrightarrow{\sim}H. \tag{4.5}
$$

If a group $\Gamma$ acts on $H$ and commutes with $\mathcal A$, it acts on $W(H)$ by $(\gamma f)(p)=\gamma f(p)$, and (4.5) is $\Gamma$-equivariant.

**Proof strategy.** Work locally with matrix units, exactly as over a field; projectivity guarantees that the resulting decomposition is integral.

Using (4.3), choose matrix units $E_{ij}$ after an $\mathcal O$-basis of $\mathcal P$ has been chosen. Put $e=E_{11}$. The map

$$
\mathcal P\otimes_\mathcal O eH\longrightarrow H,
\qquad e_i\otimes h\longmapsto E_{i1}h
$$

has inverse

$$
h\longmapsto\sum_i e_i\otimes E_{1i}h.
$$

The matrix identities prove that the composites are the identity. An $\mathcal A$-linear map $\mathcal P\to H$ is determined by the image of $e_1$, and that image can be any element of $eH$. Hence $W(H)\simeq eH$. Since $e$ is an idempotent, $eH$ is a direct summand of the free module $H$, and is finite free. This proves (4.5). The formula for $\Gamma$ is well typed because the two actions commute, and equivariance follows by evaluation. $\square$

The proof uses matrix coordinates, but the isomorphism class of $W(H)$ does not. It is defined by the intrinsic Hom functor. Conjugating one matrix presentation into another transports $\mathcal P$ and yields the same functor up to the unique natural isomorphism supplied by Morita theory.

### 4.4 The canonical multiplicity lattice

Let $H_L\subset M_L$ be a rational isotypic packet block, let

$$
H=M[H_L], \tag{4.6}
$$

and suppose the integral Hecke action on $H$ contains an integral split Morita datum $(\mathcal A,\mathcal P)$ for the full finite level algebra. Define

$$
T^{\mathrm{coh}}=\operatorname{Hom}_{\mathcal A}(\mathcal P,H). \tag{4.7}
$$

This is the **canonical cohomological multiplicity lattice relative to $(M,H_L,\mathcal A,\mathcal P)$**. Its rationalization is the multiplicity space extracted from the packet, and it is stable under Galois.

If the rational packet multiplicity is two, Theorem 4.1 gives

$$
\operatorname{rank}_\mathcal O T^{\mathrm{coh}}=2. \tag{4.8}
$$

It also gives an integral evaluation isomorphism

$$
\mathcal P\otimes_\mathcal O T^{\mathrm{coh}}
\xrightarrow{\sim}H. \tag{4.9}
$$

This statement is stronger than freeness of the saturated packet lattice. It says that the finite level multiplicity has been removed without an index defect.

Sometimes one has a projective $\mathcal P$ but only a rational evaluation isomorphism. Then define $T^{\mathrm{raw}}$ by (4.7) and let $H^{\mathrm{ev}}$ be the image of evaluation. Both are torsion-free, but $H/H^{\mathrm{ev}}$ may have finite length. Saturating the image repairs the ambient packet lattice, not the claim that evaluation is an isomorphism. In that situation there is a natural stable rank-two lattice in the rational Hom space, but its asserted canonicity is only that of the Hom construction; an integral tensor factorization is absent.

### 4.5 The denominator ledger

Four independent denominators can obstruct (4.9).

- A **packet-projector denominator** appears when conjugate or congruent characteristic-zero packets are separated.
- A **coarse-level denominator** appears when descent from a fine cover is split by averaging over a deck group.
- A **Hecke-order denominator** appears in the discriminant of the integral order inside its rational matrix algebra.
- An **evaluation denominator** is the finite index of the image of (4.9) when the chosen integral type lattice is not a projective generator for the actual order.

A fifth denominator can appear later: the degree of an isogeny comparing the cohomological factor with an abelian quotient. Inverting one denominator says nothing about the others.

The safe conclusion at every prime is the saturated lattice (4.6). The rank-two conclusion (4.7)--(4.9) is made only when the Morita and evaluation hypotheses are verified at that prime. This is the precise integral form of the distinction between a rational packet and an integral localized packet.

There are two important regimes in which the Morita hypotheses simplify.

At minimal level the finite packet module is a line. Then $d=1$, $\mathcal A=\mathcal O$, and $\mathcal P=\mathcal O$. Evaluation is the identity. The saturated packet lattice itself is already the rank-two multiplicity lattice. No order discriminant or oldvector evaluation defect remains, although packet-projector and coarse-level denominators can still occur in forming the saturated branch.

At a genuinely old level with a verified full matrix order $M_d(\mathcal O)$, the standard column module is a projective generator and Theorem 4.1 applies. The adjective *full* matters. If one retains only spherical operators acting by scalars on all oldvectors, the integral algebra is merely $\mathcal O$ on a module of rank $2d$; its Hom multiplicity still has rank $2d$. Level operators are not decorative additions to the Hecke algebra. They are what identify the $d$ oldvectors as one simple module and expose the rank-two commutant.

One can test the evaluation hypothesis without choosing matrix units. The natural map (4.9) is a map between finite free modules which is a rational isomorphism. Its cokernel is finite, and its zeroth Fitting ideal is generated by the determinant of evaluation in any pair of bases. Evaluation is integral precisely when that Fitting ideal is the unit ideal. This criterion is basis independent and localizes well. It is often the clearest way to audit an integral level-change calculation.

## 5. The canonical curve lattice

### 5.1 The cohomological construction

Let $C_K/E$ be a compact quaternionic Shimura curve in the established weight-two range. Fix a coefficient place $\lambda\mid\ell$ and put

$$
M_\lambda=H^1_{\mathrm{et}}(C_{K,\bar E},\mathcal O_\lambda). \tag{5.1}
$$

This is finite free, carries a continuous $G_E$-action, and is stable under every integral Hecke correspondence defined on the selected component union. Let $H_{\Pi,\lambda}\subset M_\lambda\otimes L_\lambda$ be the rational packet block constructed from the full finite Hecke image. Define

$$
M_{\Pi,\lambda}=M_\lambda[H_{\Pi,\lambda}]. \tag{5.2}
$$

The lattice (5.2) is canonical once the curve, component union, level, integral coefficient ring, and rational packet block are fixed. It is not obtained by applying a rational projector to $M_\lambda$.

If the packet is considered through a congruence maximal ideal $\mathfrak m$, the primary integral object is instead the localized lattice $(M_\lambda)_\mathfrak m$. The individual branch lattice (5.2) is its saturated intersection with one rational branch. Keeping both objects visible distinguishes the congruence family from the chosen characteristic-zero constituent.

### 5.2 Galois and Hecke stability

**Proposition 5.1.** The lattice $M_{\Pi,\lambda}$ is saturated, finite free, Galois stable, and stable under every integral Hecke operator preserving the rational packet block. Formation of it commutes with flat extension of coefficient DVRs.

**Proof.** Saturation, freeness, and base change are Proposition 2.3. Galois commutes with the rational packet projector because the defining correspondences descend to $E$, so it preserves $H_{\Pi,\lambda}$ and the ambient lattice. Integral Hecke stability is identical. Lemma 2.2 gives the two stability claims. $\square$

This proof uses actual descended correspondences. Equality of good Hecke eigenvalues alone would not prove that the packet subspace is Galois stable.

### 5.3 Freeness and rank two

Let $(\mathcal A_{\Pi,\lambda},\mathcal P_{\Pi,\lambda})$ be an integral split Morita datum for the full finite Hecke action on $M_{\Pi,\lambda}$. Put

$$
T^{\mathrm{coh}}_{\Pi,\lambda}
=\operatorname{Hom}_{\mathcal A_{\Pi,\lambda}}
(\mathcal P_{\Pi,\lambda},M_{\Pi,\lambda}). \tag{5.3}
$$

**Theorem 5.2 (canonical curve lattice).** If integral evaluation is an isomorphism and the rational automorphic multiplicity is two, then $T^{\mathrm{coh}}_{\Pi,\lambda}$ is finite free of rank two over $\mathcal O_\lambda$, is continuously $G_E$-stable, and satisfies

$$
\mathcal P_{\Pi,\lambda}\otimes T^{\mathrm{coh}}_{\Pi,\lambda}
\xrightarrow{\sim}M_{\Pi,\lambda}. \tag{5.4}
$$

Its generic fiber is the rank-two representation extracted from curve cohomology.

**Proof.** Apply Theorem 4.1 to $H=M_{\Pi,\lambda}$. The Galois action commutes with the full Hecke image, hence descends to the Hom lattice. Rationalizing (5.4) recovers the established multiplicity-space evaluation. Since the rational multiplicity has dimension two, coefficient freeness gives rank two. Continuity follows because the Hom lattice is a closed $\mathcal O_\lambda$-submodule of a finite product of the continuous ambient cohomology module. $\square$

No eigenvector, matrix basis, or formula for a rational idempotent occurs in (5.3). The integral datum is the projective Hecke module itself.

In the minimal multiplicity-one case, Theorem 5.2 is unconditional after saturation: $\mathcal P=\mathcal O$ and (5.4) is the identity. More generally, it is enough to verify the Morita datum after localizing at the packet maximal ideal. Indeed all modules and maps in (5.4) are finite over $\mathcal O$, and the packet question has no support at other Hecke maximal ideals. This localization does not mean that a characteristic-zero branch has become an integral direct summand; saturation remains necessary if several branches lie over the same maximal ideal.

The rank calculation deserves emphasis. Rational automorphic decomposition gives

$$
\dim_{L_\lambda}H_{\Pi,\lambda}
=2\dim_{L_\lambda}P_{\Pi,\lambda}. \tag{5.5}
$$

Saturation preserves this dimension as $\mathcal O$-rank. Integral evaluation gives

$$
\operatorname{rank}_\mathcal O M_{\Pi,\lambda}
=\operatorname{rank}_\mathcal O\mathcal P_{\Pi,\lambda}
\cdot\operatorname{rank}_\mathcal O T^{\mathrm{coh}}_{\Pi,\lambda}. \tag{5.6}
$$

Comparing (5.5) and (5.6) gives rank two without assuming that reduction modulo $\varpi$ has a two-dimensional eigenspace. The residual generalized eigenspace can be larger because congruent branches remain in the localization.

### 5.4 Fine and coarse levels

Suppose $C_{K'}\to C_K$ is a finite fine-level cover with deck group $\Delta$. Pullback and trace satisfy

$$
\operatorname{Tr}\circ\operatorname{pullback}=|\Delta|. \tag{5.7}
$$

If $|\Delta|$ is a unit in $\mathcal O_\lambda$, the normalized trace splits pullback integrally. The invariant lattice upstairs identifies with the downstairs lattice, and saturation shows that the packet and multiplicity constructions agree.

If $\ell\mid|\Delta|$, equation (5.5) splits only rationally. The downstairs cohomology remains the canonical carrier, but it need not be the invariant direct summand of the upstairs lattice. Any claim of independence from fine level must then use a direct integral comparison, not averaging.

**Proposition 5.3.** Under a fine-level comparison whose pullback and trace maps are integral and whose degree is a coefficient unit, the canonical packet and multiplicity lattices are identified uniquely.

**Proof.** The normalized trace is an inverse to pullback on the selected rational block. Both maps preserve the ambient integral lattices and the full Hecke modules. Proposition 2.3 transports saturated intersections, and functoriality of Hom transports the Morita lattice. The two composites are the identity generically and hence integrally because the targets are torsion-free. $\square$

### 5.5 Comparison with an abelian quotient

The Jacobian of a smooth projective curve is the natural covariant finite-flat carrier at the coefficient prime. Let $A_\Pi$ be an abelian quotient or subquotient selected by the packet, and suppose:

1. $A_\Pi$ is defined over $E$ and has good reduction at the place under consideration;
2. the coefficient order acts on its good-reduction abelian scheme;
3. the rational comparison with the cohomological rank-two representation is induced by algebraic correspondences;
4. those correspondences are integral at $\lambda$, or their degrees are $\lambda$-adic units;
5. the covariance, dual, and Tate-twist normalization in the comparison is stated explicitly.

Under these hypotheses, the cohomological lattice and the corresponding Tate lattice are identified in the stated normalization. The proof is not a comparison of characteristic polynomials. Algebraic correspondences give maps between the two integral lattices; the composite is multiplication by the degree or polarization scalar. If that scalar is a unit, the maps are inverse. Saturation then removes any dependence on the chosen representative of the rational correspondence.

If the scalar is not a unit, only a rational isomorphism follows. Two isogenous abelian varieties can then supply nonhomothetic lattices. The rational packet remains unchanged, but a claim that its finite-flat lattice is independent of the isogeny is false without additional integral information.

There is also a normalization issue. For a smooth proper curve, degree-one étale cohomology is naturally the linear dual of the covariant Tate module of its Jacobian. A polarization introduces a Tate twist when it identifies the Tate module with its Cartier-twisted dual. Therefore a statement such as “the cohomological lattice is the Tate lattice” is ill typed until the dual and twist have been specified. In this book the coefficient-prime hypothesis includes that specification. The finite-flat group is attached to the covariant generic module supplied by the abelian scheme; Cartier duality then transports the result to any cohomological normalization which is actually related by the corresponding twisted duality. An arbitrary negative twist is not declared finite flat.

When the comparison is a coefficient-linear isomorphism

$$
T_{\Pi,\lambda}\xrightarrow{\sim}T_\lambda A_\Pi, \tag{5.8}
$$

the quotient $T_{\Pi,\lambda}/IT_{\Pi,\lambda}$ is modeled directly by the coefficient quotient of $\mathcal A_\Pi[p^m]$. When the comparison instead has the form

$$
T_{\Pi,\lambda}\xrightarrow{\sim}
(T_\lambda A_\Pi)^*(1), \tag{5.9}
$$

the model is the Cartier dual of that coefficient quotient. Both are valid because (5.9) retains the twist produced by Cartier duality. A comparison with $(T_\lambda A_\Pi)^*$ without the twist does not follow from the finite-flat duality theorem.

## 6. Pairings, coefficient involutions, and Cartier duality

### 6.1 The integral adjoint pairing

Poincare duality pairs the packet with its adjoint packet. On the ambient curve lattice it is perfect:

$$
M_\lambda\times M_\lambda
\longrightarrow\mathcal O_\lambda(-1). \tag{6.1}
$$

The Hecke involution $a\mapsto a^\dagger$ is characterized by

$$
\langle ax,y\rangle=\langle x,a^\dagger y\rangle. \tag{6.2}
$$

Consequently $M_{\Pi,\lambda}$ pairs with $M_{\Pi^\dagger,\lambda}$. Under split integral Morita data on the two blocks, factoring the pairing through a perfect pairing of level modules leaves a pairing

$$
T^{\mathrm{coh}}_{\Pi,\lambda}
\times T^{\mathrm{coh}}_{\Pi^\dagger,\lambda}
\longrightarrow\mathcal O_\lambda(-1). \tag{6.3}
$$

The target acquires the finite component character when the adjoint packet is identified with a twist of $\Pi$. This recovers the determinant character already known rationally.

Integral perfectness of (6.3) requires more than perfectness of (6.1). The level-module pairing must be perfect, and the evaluation maps must be integral isomorphisms. A discriminant in either factor appears inversely in the other. Thus the rational factorization cannot silently be reduced modulo $\lambda$.

### 6.2 Duality indices

Let

$$
\alpha:T^{\mathrm{coh}}_{\Pi,\lambda}
\longrightarrow
(T^{\mathrm{coh}}_{\Pi^\dagger,\lambda})^\vee(-1) \tag{6.4}
$$

be the adjoint map. It is a rational isomorphism and an integral injection after scaling the rational pairing to be integral. Its cokernel is finite. Define the **duality index**

$$
d_\lambda(\Pi)=\operatorname{length}_{\mathcal O_\lambda}
\operatorname{coker}\alpha. \tag{6.5}
$$

The pairing is perfect precisely when this number is zero. The index receives contributions from the polarization degree, the discriminant of the Hecke order, the pairing on the level module, and the evaluation defect. It is unchanged by replacing a projector formula while keeping the same integral carrier, but it can change under an isogeny of nonunit degree.

When (6.3) is alternating on one self-adjoint rank-two block and perfect, reduction gives the determinant character integrally. If it is not perfect, the rational determinant formula still holds, but reduction of the form may be degenerate. One must then obtain the residual determinant by another integral argument or rescale to a genuinely self-dual lattice when possible.

### 6.3 Coefficient actions on the dual

Let a commutative coefficient ring $A$ act on a finite-flat group $G$. Cartier duality sends $a$ to the transpose endomorphism $a^D$ of $G^D$. Since $A$ is commutative, reversal of composition does not change the ring law, so $G^D$ again carries an $A$-action.

If the pairing is adjoint with respect to an involution $a\mapsto a^\dagger$, the identified self-dual model carries the conjugate action:

$$
\langle ax,y\rangle=\langle x,a^\dagger y\rangle. \tag{6.6}
$$

For an ideal $I\subset A$, the annihilator relevant to the dual quotient is therefore $I^\dagger$, not automatically $I$. If the involution fixes $I$, the same coefficient quotient appears on both sides.

### 6.4 Finite-level Cartier duals

Suppose a finite quotient $T/IT$ has a finite-flat model $G_I$. Cartier duality gives a model

$$
G_I^D
$$

of

$$
(T/IT)^*(1). \tag{6.7}
$$

If $H\subset G_I$ is the closure of a generic submodule, exactness gives

$$
(G_I/H)^D\simeq H^\perp. \tag{6.8}
$$

where $H^\perp$ is the finite-flat closure of the generic annihilator inside $G_I^D$. Formation of (6.8) commutes with flat extension of DVRs.

This is the scheme-theoretic duality used later. It neither identifies $T^*$ with $T^*(1)$ nor turns a rational self-duality into an integral one. The Tate twist and the chosen finite-flat model remain part of the statement.

The interaction with coefficient quotients can be made explicit. Suppose $\mathcal O$ carries an involution $\dagger$ and the perfect pairing identifies $T$ with $T^*(1)$ so that multiplication by $a$ is adjoint to multiplication by $a^\dagger$. For an open ideal $I$, let

$$
I^\dagger=(a^\dagger:a\in I).
$$

A character on $T/IT$ corresponds under the pairing to an element annihilating $IT$, hence to the appropriate $I^\dagger$-torsion quotient on the adjoint lattice. At group-scheme level, exactness and closure give the canonical comparison

$$
\mathcal T_I^D\simeq\mathcal T^{\dagger}_{I^\dagger}. \tag{6.9}
$$

If $I=I^\dagger$ and the packet is self-adjoint with a perfect integral pairing, (6.9) is a self-duality of the quotient system. For $J\subset I$, dualizing (8.6) reverses the transition sequence. Thus the kernel at one side is the annihilator quotient at the other, with no appeal to geometric point counts.

If the pairing has duality index greater than zero, (6.9) can fail integrally even though it holds rationally. One can still dualize each finite-flat quotient that has been constructed, but identifying that dual with a quotient of the original lattice requires control of the index. This is exactly where a nonunit polarization degree or Hecke discriminant enters.

## 7. Geometric finite-flat carriers

### 7.1 Good reduction and torsion

Let $R$ be a DVR of mixed characteristic with fraction field $K$, and let $\mathcal A/R$ be an abelian scheme. Multiplication by every positive integer $n$ is finite locally free, so

$$
\mathcal A[n]=\ker([n]:\mathcal A\to\mathcal A) \tag{7.1}
$$

is a finite locally free commutative group scheme. Its generic fiber is $A[n]$ for $A=\mathcal A_K$. If $K$ has characteristic zero, the generic fiber is finite etale and its geometric points form the usual torsion Galois module.

This elementary geometric fact is the strongest coefficient-prime input in the good-reduction route. It requires neither that $K/\mathbf Q_p$ be unramified nor that $p>2$. It also makes no ordinary assumption. An ordinary special fiber and a supersingular special fiber have different connected--etale structures, but both have finite-flat torsion at every level.

A smooth proper curve model supplies such an abelian scheme canonically. If $\mathscr C/R$ is smooth, proper, and has geometrically connected fibers, the identity component of its relative Picard scheme is an abelian scheme

$$
\mathscr J=\operatorname{Pic}^0_{\mathscr C/R}, \tag{7.2}
$$

whose generic fiber is the Jacobian of $C$. The Abel--Jacobi map identifies degree-one curve cohomology with the corresponding cohomology of $\mathscr J$, and Hecke correspondences induce endomorphisms of $\mathscr J$. Consequently a packet factor which is cut by an integral idempotent in the Jacobian endomorphism algebra has an actual good-reduction abelian carrier. If the packet idempotent is only rational, smoothness of $\mathscr C$ still gives finite-flat torsion for the whole Jacobian, but does not isolate the coefficient factor integrally.

The finiteness and flatness in (7.1) are geometric, not a count of torsion points. Multiplication by $n$ on an abelian scheme is finite locally free of degree $n^{2g}$. Its kernel is the fiber over the zero section, hence is finite locally free of the same degree. This remains true when $p\mid n$, even though the special fiber can be nonreduced. Thus

$$
|\mathcal A[n]|=n^{2g} \tag{7.3}
$$

on every fiber.

Let $T_pA=\varprojlim A[p^n](\bar K)$. Then

$$
T_pA/p^nT_pA\simeq A[p^n](\bar K). \tag{7.4}
$$

and the transition maps come from multiplication on the finite-flat groups. Thus the geometric Tate lattice carries a compatible system before any coefficient factor is isolated.

### 7.2 Marked coefficient-linear carriers

Let $\mathcal O$ be a finite flat local $\mathbf Z_p$-algebra acting on $\mathcal A$ over $R$. Suppose a direct coefficient factor $T$ of $T_pA$ is finite free of rank two over $\mathcal O$. A **marked geometric carrier for $T$** consists of:

1. the abelian scheme $\mathcal A/R$;
2. its integral $\mathcal O$-action;
3. an $\mathcal O[G_K]$-equivariant identification of the chosen generic factor with $T$;
4. when the factor is cut from a larger coefficient algebra, an integral split idempotent or, more generally, an integral closure-and-quotient construction realizing it.

The marking prevents an ambiguity that is harmless rationally but serious integrally. Two isogenous abelian schemes can have isomorphic rational Tate modules and different integral lattices. The carrier identifies which lattice and which coefficient action are meant.

If an idempotent $e$ belongs to the integral coefficient algebra, then $e\mathcal A[p^n]$ is a direct factor and is finite flat. If $e$ exists only after inverting $p$, this argument is unavailable. One must not write $e\mathcal A[p^n]$ as an integral group scheme.

The direct-factor assertion has a short proof. The relations $e^2=e$ and $(1-e)^2=1-e$ hold as endomorphisms of the group scheme, and addition induces mutually inverse maps

$$
e\mathcal A[p^n]\times(1-e)\mathcal A[p^n]
\rightleftarrows\mathcal A[p^n]. \tag{7.5}
$$

Both images are split kernels of complementary idempotents, so their coordinate algebras are direct summands of a finite locally free module and are finite locally free. No raw-image flatness theorem is being assumed.

When the coefficient algebra has no integral idempotent selecting the branch, the safe construction of Section 7.4 still forms a quotient model for a specified generic coefficient module. What it does not do is turn the original abelian scheme into a canonically split product. The quotient is canonical inside the chosen torsion model, not as an abelian subvariety of $\mathcal A$.

An elliptic curve gives the basic complete example. Let $E/K$ have good reduction and let $\mathcal E/R$ be its elliptic scheme. Take $\mathcal O=\mathbf Z_p$ and $T=T_pE$. Then

$$
\mathcal T_{(p^n)}=\mathcal E[p^n] \tag{7.6}
$$

models $T/p^nT$, and multiplication by $p^n$ gives

$$
0\longrightarrow\mathcal E[p^m]
\longrightarrow\mathcal E[p^{m+n}]
\longrightarrow\mathcal E[p^n]
\longrightarrow0. \tag{7.7}
$$

The Weil pairing makes each level Cartier self-dual with its cyclotomic target. If the special fiber is ordinary, its level-one connected--etale sequence has ranks $p$ and $p$; if it is supersingular, the level-one group is local--local. The same generic rank-two lattice construction accommodates both.

Now suppose an order $\mathcal O$ acts on an abelian scheme of larger dimension and $T$ is a rank-two coefficient factor of its Tate module. Choose $m$ with $p^m\in I$. The ambient group $\mathcal A[p^m]$ can have much larger rank than $|\mathcal O/I|^2$. First close the complementary generic coefficient relations or take the marked factor supplied by the datum; then close $IT/p^mT$ inside that factor. Rank comparison after the final quotient proves that exactly the desired factor, and no auxiliary torsion, remains. This two-stage closure is the group-scheme analogue of first removing finite Hecke multiplicity and then reducing coefficients.

### 7.3 Why kernels of coefficient endomorphisms are delicate

For $a\in\mathcal O$, the scheme-theoretic kernel of

$$
a:\mathcal G\longrightarrow\mathcal G
$$

on a finite-flat group $\mathcal G$ is finite, but need not be flat for an arbitrary endomorphism. Flatness is automatic when the map is a finite-flat isogeny of an abelian scheme, and it is automatic for split idempotent factors. It is not a formal property of every map between finite-flat groups.

This matters for an ideal $I=(a_1,\ldots,a_r)$. The raw intersection

$$
\bigcap_j\ker(a_j) \tag{7.8}
$$

can acquire vertical torsion. Even if its generic fiber is the desired coefficient torsion, (7.8) is not a safe definition of the integral model unless flatness has been proved.

The correct construction begins from a finite-flat model of a sufficiently large coefficient quotient, closes the generic relation subgroup, and takes a represented quotient. It uses only operations known to remain in the finite-flat category.

### 7.4 The safe quotient construction

Let $T$ be a finite free $\mathcal O$-lattice with continuous $G_K$-action. Assume that for some open ideal $J\subset\mathcal O$ a coefficient-linear finite-flat group $\mathcal G_J$ models $T/JT$. Let $I\supset J$. Inside the generic module $T/JT$, the subgroup

$$
IT/JT \tag{7.9}
$$

is stable under Galois and $\mathcal O$. Let $\mathcal H_{I,J}\subset\mathcal G_J$ be its schematic closure. Over a DVR, closure is finite flat and is unique inside the fixed ambient group. Define

$$
\mathcal G_I=\mathcal G_J/\mathcal H_{I,J}. \tag{7.10}
$$

The represented quotient is finite flat, and its generic module is

$$
(T/JT)/(IT/JT)\simeq T/IT. \tag{7.11}
$$

Because the generic relation subgroup is coefficient stable, uniqueness of closure makes $\mathcal H_{I,J}$ coefficient stable. The action therefore descends to $\mathcal G_I$ and factors through $\mathcal O/I$.

**Theorem 7.1 (safe coefficient quotient).** Construction (7.10) produces a coefficient-linear finite-flat model of $T/IT$. It is independent, up to unique marked isomorphism inside the supplied compatible system, of the chosen deeper ideal $J$.

**Proof strategy.** Closure and quotient prove existence. Independence follows by comparing both constructions inside a common still deeper model and using successive quotient.

Choose $J'\subset J$. The model $\mathcal G_J$ is the quotient of $\mathcal G_{J'}$ by the closure of $JT/J'T$. The inverse image in $\mathcal G_{J'}$ of the closure of $IT/JT$ is a finite-flat subgroup with generic fiber $IT/J'T$. By uniqueness of closure it is the closure of that generic subgroup. Successive quotient gives

$$
(\mathcal G_{J'}/\overline{JT/J'T})/
(\overline{IT/J'T}/\overline{JT/J'T})
\simeq\mathcal G_{J'}/\overline{IT/J'T}.
$$

The two constructions of $\mathcal G_I$ are therefore canonically isomorphic. The isomorphism respects the marking and coefficient action because it does so generically, and the generic-fiber functor is faithful on fixed finite-flat models. $\square$

## 8. Every coefficient quotient

### 8.1 Open ideals and generic relation submodules

Let $\mathcal O$ now be the ring of integers of a finite extension of $\mathbf Q_p$. Every nonzero ideal is open and contains $p^m$ for some $m$. Suppose a marked geometric carrier realizes $T/p^mT$ inside $\mathcal A[p^m]$ for every $m$. For an open ideal $I$, choose $m$ with $p^m\in I$. Then

$$
IT/p^mT\subset T/p^mT \tag{8.1}
$$

is a well-defined finite $\mathcal O[G_K]$-submodule.

The relation subgroup, not the annihilator, is the correct generic object. Quotienting by (8.1) gives $T/IT$. The set of elements annihilated by $I$ can have a different length over a non-Gorenstein coefficient ring and is contravariantly related to the quotient. Even over a DVR, using relations makes transition maps transparent.

### 8.2 Closure and represented quotient

Let $\mathcal T_m$ be the supplied finite-flat model of $T/p^mT$. Close (8.1) inside $\mathcal T_m$:

$$
\mathcal R_{I,m}
=\overline{IT/p^mT}^{\,\mathcal T_m}. \tag{8.2}
$$

Define

$$
\mathcal T_I=\mathcal T_m/\mathcal R_{I,m}. \tag{8.3}
$$

Because this is the decisive integral step, we recall its algebra. Write $\mathcal T_m=\operatorname{Spec}A$ and let $J_K\subset A_K$ be the Hopf ideal defining the generic relation subgroup. Put

$$
J=A\cap J_K\subset A_K. \tag{8.3a}
$$

The quotient $C=A/J$ embeds in $A_K/J_K$, so it is torsion-free over $R$. It is finite because it is a quotient of the finite $R$-module $A$. A finite torsion-free module over a DVR is free; hence $C$ is finite flat.

It remains to check the group law. Since $C$ is free, the sequence

$$
0\longrightarrow J\longrightarrow A\longrightarrow C\longrightarrow0
$$

splits as $R$-modules. Therefore

$$
\ker(A\otimes_RA\to C\otimes_RC)
=J\otimes_RA+A\otimes_RJ. \tag{8.3b}
$$

For $x\in J$, the image of $\Delta(x)$ in $(C\otimes C)_K$ is zero because $J_K$ is a Hopf ideal. The module $C\otimes C$ is torsion-free, so the image already vanishes over $R$. The counit and antipode conditions descend in the same way. Thus $J$ is a Hopf ideal and $\operatorname{Spec}C$ is a finite-flat closed subgroup.

The construction is unique in the fixed ambient group. Any finite-flat closed subgroup with generic ideal $J_K$ has a saturated ideal $J'$, and saturation gives

$$
J'=A\cap J'_K=A\cap J_K=J. \tag{8.3c}
$$

This proves both flatness and ambient canonicity of (8.2). Notice where the DVR is used: finite torsion-free modules are free. Over a higher-dimensional normal ring the same contraction can be torsion-free without being flat.

The quotient in (8.3) is the represented faithfully flat sheaf quotient. On geometric generic points it is the ordinary module quotient. Its existence cannot be replaced by the presheaf quotient on test-ring points, which can fail to be pointwise surjective even for a faithfully flat morphism.

**Theorem 8.1 (all coefficient quotients).** The group $\mathcal T_I$ is finite locally free and commutative over $R$, its marked generic module is $T/IT$, and its marked isomorphism class is independent of $m$. Formation of $\mathcal T_I$ commutes with flat extension of DVRs.

**Proof.** The contraction argument above makes $\mathcal R_{I,m}$ finite flat. The finite-flat quotient theorem makes (8.3) finite flat and gives a faithfully flat exact sequence. Generic fibers commute with quotient, proving the marking. Independence is Theorem 7.1. Under a flat extension of DVRs, tensoring the saturated exact sequence remains exact, so contraction and closure commute with base change. Represented quotient and the generic marking commute with arbitrary base change. $\square$

This proof works for every open ideal, including ideals not generated by a coefficient uniformizer and quotient maps which are not flat as maps of coefficient rings.

For a concrete coefficient example, let $\mathcal O$ be ramified of degree $e$ over $\mathbf Z_p$ and let $I=(\varpi^a,p^b)$. Since $p^b=u\varpi^{eb}$ for a unit $u$, this ideal is principal in the DVR case, but its presentation by two generators illustrates the construction: one does not intersect the raw kernels of $\varpi^a$ and $p^b$. Choose $m$ with $p^m\in I$, close $IT/p^mT$, and quotient. The answer depends only on the ideal, not on either generating set. For a more general finite local coefficient algebra in the filtered theorem, open ideals need not be principal at all, and the same relation-submodule construction remains valid.

The special fiber of $\mathcal T_I$ is not determined by its rank. If $T$ comes from an ordinary elliptic scheme and $I=(p)$, it can fit into a connected--etale sequence with multiplicative connected part and etale quotient. If it comes from a supersingular elliptic scheme, the entire height-two level can be local--local. Both groups have rank $p^2$, both have the expected generic module, and both are finite flat. Hence finite flatness alone does not imply an ordinary filtration.

### 8.3 Coefficient actions

For $a\in\mathcal O$, the endomorphism $a$ of $\mathcal T_m$ preserves $\mathcal R_{I,m}$. Indeed it preserves the generic submodule $IT/p^mT$, and the image of the closure is a finite-flat subgroup with generic fiber contained in the same submodule. Uniqueness of closure forces containment. Hence $a$ descends to $\mathcal T_I$.

Every element of $I$ acts as zero on the generic fiber of $\mathcal T_I$. Faithfulness of the generic-fiber functor on morphisms between fixed finite-flat groups implies that it acts as zero integrally. Thus the action factors through

$$
\mathcal O/I\longrightarrow\operatorname{End}_R(\mathcal T_I). \tag{8.4}
$$

The ring identities hold because they already hold on $\mathcal T_m$, or equivalently because they hold generically and morphisms extend uniquely when already defined. No generator of $I$ is chosen.

This argument also explains why a generic coefficient action on one arbitrary chosen model need not extend. Here the action is first present on the common ambient group $\mathcal T_m$. Stability of the relation closure lets it descend. If one began with an unrelated model of $T/IT$, generic fullness would not manufacture these endomorphisms. Coefficient linearity is a property of the constructed marked system, not of every model of the same underlying abelian Galois module.

### 8.4 Exact sequences for nested ideals

Let $J\subset I$. There is a natural generic exact sequence

$$
0\longrightarrow IT/JT
\longrightarrow T/JT
\longrightarrow T/IT
\longrightarrow0. \tag{8.5}
$$

Close the first term inside $\mathcal T_J$. The quotient is $\mathcal T_I$ by the independence theorem. Therefore

$$
0\longrightarrow\mathcal K_{I,J}
\longrightarrow\mathcal T_J
\longrightarrow\mathcal T_I
\longrightarrow0 \tag{8.6}
$$

is faithfully flat exact, where $\mathcal K_{I,J}$ models $IT/JT$.

For $K\subset J\subset I$, successive quotient identifies the composite $\mathcal T_K\to\mathcal T_I$ with the quotient first by $JT/KT$ and then by $IT/JT$. Thus the transition maps satisfy strict transitivity. They are not merely maps chosen after independent existence proofs.

### 8.5 Ranks and flatness

Since $\mathcal T_I$ has etale generic fiber corresponding to $T/IT$,

$$
|\mathcal T_I|=|T/IT|. \tag{8.7}
$$

If $T$ is free of rank two over $\mathcal O$, this is

$$
|\mathcal T_I|=|\mathcal O/I|^2. \tag{8.8}
$$

The equality is a rank statement for a finite locally free scheme. At the residue characteristic the special fiber can have fewer geometric points and may be connected.

In (8.6), rank multiplicativity gives

$$
|\mathcal T_J|=|\mathcal K_{I,J}|\,|\mathcal T_I|. \tag{8.9}
$$

This proves the expected length calculation without assuming that a raw kernel of a coefficient endomorphism is flat. Flatness entered through saturated closure and represented quotient.

The same reasoning treats a stable filtration. If

$$
0=T_0\subset T_1\subset\cdots\subset T_r=T/IT
$$

is a filtration by coefficient- and Galois-stable submodules, close every $T_j$ inside $\mathcal T_I$. The closures form a filtration by finite-flat closed subgroup schemes, and each successive represented quotient models $T_j/T_{j-1}$. This proves that the actual extension classes occurring inside the chosen lattice are finite flat. It does not prove that every abstract extension of the same graded pieces is finite flat.

## 9. Compatible transition systems

### 9.1 The quotient functor on ideals

Let $\mathscr I(\mathcal O)$ be the poset of open ideals, ordered by reverse inclusion so that $J\subset I$ gives a map from the finer quotient to the coarser one. The construction above defines a functor

$$
I\longmapsto\mathcal T_I, \tag{9.1}
$$

with faithfully flat transition maps

$$
\mathcal T_J\longrightarrow\mathcal T_I
\qquad(J\subset I). \tag{9.2}
$$

The functor is coefficient linear, compatible with generic markings, and transitive. Its kernels are themselves finite-flat models of the corresponding relation subquotients.

This functorial formulation is what “compatible finite-flat quotients” means. A collection of unrelated models for each $T/IT$ is insufficient: it need not possess transition maps, and even when maps exist generically they need not extend between the chosen models.

### 9.2 Principal levels

For $I=(\varpi^n)$ write $\mathcal T_n$. If $m,n\ge1$, the coefficient sequence is

$$
0\longrightarrow T/\varpi^mT
\xrightarrow{\varpi^n}T/\varpi^{m+n}T
\longrightarrow T/\varpi^nT
\longrightarrow0. \tag{9.3}
$$

Inside $\mathcal T_{m+n}$, close the first generic term. Its quotient is $\mathcal T_n$, and the closed subgroup is canonically isomorphic to $\mathcal T_m$ when the transition system comes from multiplication on one Tate lattice or from the rigid low-weight classification. Thus

$$
0\longrightarrow\mathcal T_m
\longrightarrow\mathcal T_{m+n}
\longrightarrow\mathcal T_n
\longrightarrow0 \tag{9.4}
$$

is finite-flat exact, with the first map corresponding generically to multiplication by $\varpi^n$.

For a general geometric carrier, the marked isomorphism of the kernel with $\mathcal T_m$ is part of the compatibility established from the common ambient $p$-divisible or Tate system. It should not be inferred from equality of generic modules if uniqueness of abstract models is unavailable.

### 9.3 Inverse limits and recovery of the lattice

Taking geometric generic points in (9.2) recovers the inverse system $T/IT$. Along the cofinal sequence $(\varpi^n)$,

$$
T\xrightarrow{\sim}\varprojlim_n\mathcal T_n(\bar K). \tag{9.5}
$$

The map is the usual completeness map. Injectivity follows from $\bigcap_n\varpi^nT=0$, and surjectivity follows by lifting a compatible residue class successively in the complete module $T$.

The integral group schemes themselves need not form a $p$-divisible group unless their orders and multiplication maps satisfy the height and divisibility axioms. An abelian carrier does supply such a group. The general closure-and-quotient system proves exactly finite-flatness and compatibility of coefficient quotients, not a stronger divisibility structure which has not been checked.

### 9.4 Uniqueness of the transition maps

Suppose $f,g:\mathcal T_J\to\mathcal T_I$ are two morphisms with the same generic map. On coordinate algebras their difference vanishes after tensoring with $K$. The target coordinate algebra is finite free over $R$, so the two maps already agree. Therefore every transition map, coefficient action, and comparison map is unique once its integral extension exists.

Existence and uniqueness play different roles. Closure and quotient produce the maps. Torsion-freeness makes them unique. This is why compatible systems must be constructed inside common ambient groups rather than assembled from abstract existence at each level.

## 10. The absolutely unramified low-weight route

### 10.1 The exact range

Assume now

$$
p>2,\qquad k\text{ perfect of characteristic }p,
\qquad R=W(k),\qquad K_0=W(k)[1/p]. \tag{10.1}
$$

The absolute ramification index is one, so $1<p-1$. Integral Fontaine--Laffaille theory in weights $[0,1]$ gives an anti-equivalence between finite-flat commutative $p$-power groups over $R$ and admissible torsion divided filtered modules. At the lattice level it gives an anti-equivalence between finite free strongly divisible $W(k)$-modules of weights $[0,1]$ and stable $\mathbf Z_p$-lattices all of whose finite quotients are finite flat.

Every part of (10.1) matters. Perfectness supplies Witt Frobenius. Absolute unramifiedness supplies the simple divided-Frobenius category and rigidity of marked models. The inequality $p>2$ keeps the interval $[0,1]$ inside the strict small-weight range.

For a free rank-two filtered lattice $L_{\mathrm{FL}}$, Hodge type $(0,1)$ means that its first filtered step and its quotient both have rank one on every coefficient component. Locally choose a decomposition

$$
L_{\mathrm{FL}}=We_0\oplus We_1,
\qquad F^1L_{\mathrm{FL}}=We_1.
$$

Strong divisibility says that the semilinear normal map has an invertible matrix:

$$
\varphi_0(e_0)=ae_0+ce_1,
\qquad
\varphi_1(e_1)=be_0+de_1,
\qquad
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\operatorname{GL}_2(W). \tag{10.2}
$$

The matrix depends on the chosen decomposition; invertibility and the two ranks do not. This is the integral datum which rational Hodge labels fail to specify.

### 10.2 From a strongly divisible lattice to all quotients

Let $\mathcal O$ be a finite flat local $\mathbf Z_p$-algebra and let $L_{\mathrm{FL}}$ be a finite free strongly divisible $W(k)$-module with commuting $\mathcal O$-action and weights $[0,1]$. Let

$$
T=T_p(L_{\mathrm{FL}}) \tag{10.3}
$$

be its stable Galois realization. For every $n$, the torsion object $L_{\mathrm{FL}}/p^n$ corresponds to a finite-flat group whose generic module is $T/p^nT$.

For an arbitrary open ideal $I\subset\mathcal O$, choose $n$ with $p^n\in I$. The quotient $T/IT$ is a quotient of $T/p^nT$. On the filtered side it corresponds contravariantly to the distinguished admissible subobject

$$
(L_{\mathrm{FL}}/p^n)[I]_{\mathrm{adm}}. \tag{10.4}
$$

Equivalently, on the group side it is constructed by closing $IT/p^nT$ and quotienting. The compatible-quotient theorem makes (10.4) independent of $n$ and functorial for nested ideals.

**Theorem 10.1 (filtered construction of all quotients).** Under (10.1), a strongly divisible lattice with commuting finite flat coefficient action produces a unique compatible system $\{\mathcal T_I\}$ of coefficient-linear finite-flat models of every $T/IT$. The construction commutes with Cartier duality and unramified extension of $k$.

**Proof.** Finite-level representability and the integral period comparison produce $\mathcal T_{p^n}$. The compatible-quotient theorem produces the admissible object (10.4), hence its group $\mathcal T_I$. Functoriality gives transition maps. Rigidity of marked finite-flat models in the range $e=1<p-1$ makes every marked comparison unique. Duality and unramified base change commute with the anti-equivalence and with the admissible annihilator construction. $\square$

### 10.3 From compatible quotients back to the lattice

Conversely, let $T$ be finite free over $\mathcal O$ and assume compatible finite-flat groups model all $T/p^nT$. The classification attaches a unique admissible filtered module $M_n$ to each level. Exact sequence (9.4) becomes a strict exact sequence in the reversed direction. Taking inverse limits gives a finite free strongly divisible module $L_{\mathrm{FL}}$ with

$$
T_p(L_{\mathrm{FL}})\simeq T. \tag{10.5}
$$

The decisive point is compatibility. Separate finite-flat existence at every level would not, by itself, supply the strict transition maps needed to form the inverse limit. Here those maps are part of the system.

**Theorem 10.2 (integral criterion).** Under (10.1), the following are equivalent:

1. $T$ is the realization of a finite free strongly divisible lattice of weights $[0,1]$;
2. the quotients $T/p^nT$ are represented by a compatible system of finite-flat groups;
3. every open coefficient quotient $T/IT$ belongs to the compatible system of Theorem 10.1.

**Proof.** Theorem 10.1 gives $1\Rightarrow3\Rightarrow2$. The inverse-limit construction just given proves $2\Rightarrow1$. $\square$

In height two, a perfect alternating pairing supplies a useful rank check. Suppose

$$
T\times T\longrightarrow\mathcal O(1) \tag{10.6}
$$

is perfect and extends through the finite-flat system. Cartier duality identifies every quotient with its twisted dual. On the filtered side duality sends a rank-$r$ Hodge step in a rank-two component to one of rank $2-r$. Self-duality therefore gives

$$
r=2-r,
$$

so $r=1$. Thus the weights are exactly one zero and one one on every label, not merely contained in $[0,1]$. This argument requires the actual perfect integral pairing. The rational determinant character alone cannot rule out a duality defect in the chosen lattice.

The two endpoint examples locate the range. The constant groups $\mathbf Z/p^n\mathbf Z$ correspond to weight zero, and $\mu_{p^n}$ corresponds to weight one. An ordinary height-two group is an extension of these endpoint types; the extension need not split. A local--local height-two group has neither endpoint as a direct factor, but its filtered normal matrix remains invertible. The classification retains both cases and their extension classes.

### 10.4 Nonflat coefficient ideals

The map $\mathcal O\to\mathcal O/I$ is usually not flat, so ordinary tensor product does not preserve a strict filtered presentation. The object (10.4) is not defined as

$$
(L_{\mathrm{FL}}/p^n)\otimes_\mathcal O\mathcal O/I.
$$

It is characterized by its generic realization $T/IT$ and constructed from a finite-flat quotient. This variance is forced by the contravariant classification.

For nested ideals $J\subset I$, the quotient $T/JT\to T/IT$ corresponds to an admissible inclusion

$$
M_I\hookrightarrow M_J. \tag{10.7}
$$

Thus quotient maps on Galois modules become inclusions on filtered modules. Reversing this arrow is a common source of incorrect coefficient formulas.

### 10.5 The prime two and ramified boundaries

At $p=2$, the interval $[0,1]$ reaches the boundary of the small-weight range and the rigidity inequality $e<p-1$ becomes $1<1$. The classification used above is not available. A geometric abelian carrier can still provide finite-flat torsion, but the filtered proof cannot simply be repeated.

For a ramified extension $K/\mathbf Q_p$, even with $p>2$, the valuation ring is not a Witt-vector scalar extension and the divided-Frobenius category used here lacks the ramification data. If $e\ge p-1$, distinct finite-flat models can even have the same generic fiber. Again, an actual abelian scheme can provide the desired system, but rational crystallinity with weights $\{0,1\}$ does not.

These boundaries explain why the two coefficient-prime routes were separated. Geometry is broader when an abelian carrier exists; Fontaine--Laffaille theory is more rigid and canonical in its exact unramified range.

## 11. Base change and descent

### 11.1 Changing the local ground field

Let $K'/K$ be a finite extension of complete discretely valued fields, with valuation rings $R'/R$. The extension $R\to R'$ is finite flat. If $\mathcal T_I/R$ is one of the finite-flat quotient models, then

$$
\mathcal T_{I,R'}=\mathcal T_I\times_RR' \tag{11.1}
$$

models the restricted $G_{K'}$-module $T/IT$. Coefficient actions, exact sequences, Cartier duals, and ranks commute with this base change.

Schematic closure also commutes with the flat extension. Hence the quotient model obtained after base-changing the entire construction is canonically the model obtained by first restricting the generic module and then closing its relation subgroup:

$$
(\overline{IT/p^mT}^{\,\mathcal T_m})_{R'}
=\overline{(IT/p^mT)|_{G_{K'}}}^{\,\mathcal T_{m,R'}}. \tag{11.2}
$$

Thus the geometric construction works over ramified extensions as well as unramified ones in the forward direction.

The converse is false without descent data. A model which appears after ramified extension may use a Hopf lattice unavailable over $R$. Even if its generic representation descends, its integral model need not.

### 11.2 Unramified base change in the filtered description

Retain the hypotheses of (10.1) and let $k'/k$ be a perfect extension. Put $W'=W(k')$. For a strongly divisible module $L_{\mathrm{FL}}$, scalar extension is

$$
L_{\mathrm{FL},W'}=W'\otimes_WL_{\mathrm{FL}}, \tag{11.3}
$$

with the filtration tensor-extended and divided Frobenius made semilinear using Witt Frobenius on $W'$. Integral base change gives

$$
\mathcal G(M)_{W'}\xrightarrow{\sim}
\mathcal G(W'\otimes_WM) \tag{11.4}
$$

at every finite level. Therefore realization restricts to the enlarged local Galois group, and the quotient system satisfies

$$
\mathcal T_{I,W'}\simeq\mathcal T_I(T|_{G_{K'}}). \tag{11.5}
$$

The proof is integral: it compares group schemes before taking geometric points. It does not assume that kernels of Frobenius-fixed-point equations commute formally with tensor product.

### 11.3 Coefficient extension and the trace dual

Changing the coefficient ring is not the same as changing $R$. Let $A\to B$ be a finite flat extension of finite commutative $\mathbf Z_p$-algebras. On Galois modules the desired operation is

$$
T\longmapsto B\otimes_AT. \tag{11.6}
$$

On the contravariant filtered side it corresponds to

$$
B\boxtimes_AM=B^\vee\otimes_AM,
\qquad B^\vee=\operatorname{Hom}_A(B,A). \tag{11.7}
$$

Indeed finite projectivity gives

$$
\operatorname{Hom}_A(B^\vee,T(M))
\simeq B\otimes_AT(M). \tag{11.8}
$$

If $B/A$ is finite etale, the trace pairing canonically identifies $B\simeq B^\vee$ and the familiar tensor formula is correct. For a ramified extension of coefficient DVRs, $B^\vee$ is the inverse different. A choice of generator can identify it with $B$, but that choice changes the integral lattice by a unit and the embedding into the rational space by the different.

The geometric closure-and-quotient construction avoids this variance issue when only finite-flat existence of $B\otimes_AT$ is needed: present $B$ by a finite free $A$-module, form the corresponding product of a model of $T$, close the generic relation subgroup, and quotient. The resulting model is canonical relative to the presentation only up to its marked universal quotient; in the rigid unramified range the filtered formula (11.7) gives the intrinsic comparison.

### 11.4 Descent requires integral data

Suppose $K'/K$ is finite Galois. A finite-flat model $\mathcal H/R'$ of $T|_{G_{K'}}$ descends precisely when it carries semilinear isomorphisms between its conjugates satisfying the cocycle condition, preserving:

- the group law;
- the coefficient action;
- every pairing or polarization used in the construction;
- the generic marking by $T$;
- the transition maps to all coefficient quotients.

Effective faithfully flat descent then produces a unique marked model over $R$. Descent of the generic Galois module alone does not supply these integral isomorphisms.

In the Fontaine--Laffaille range, unramified descent data can be checked equivalently on the finite-flat groups, the filtered modules, or the supplied generic model system. Ramified descent is outside that equivalence. This is a hypothesis boundary rather than a failure of notation.

## 13. Independence and its limits

### 13.1 Projector and presentation independence

Let $e$ and $e'$ be two rational expressions for the same packet idempotent. They define the same rational subspace $H_{\Pi,\lambda}$. Hence

$$
M_\lambda\cap eM_{\lambda,L}
=M_\lambda\cap e'M_{\lambda,L}. \tag{13.1}
$$

This is genuine equality, not merely commensurability. It proves independence from interpolation polynomials, separating Hecke operators, and denominators used to write the rational projector.

Similarly, the branch specialization (3.3) depends only on the algebra homomorphism $\theta$, not on a presentation of the Hecke algebra. For coefficient quotient groups, different finite free presentations of a coefficient algebra yield marked models of the same generic quotient. In the rigid Fontaine--Laffaille range these are uniquely isomorphic; outside it, canonicity is asserted for the closure-and-quotient object inside the specified common ambient carrier.

### 13.2 Splitting fields and matrix coordinates

Enlarging the coefficient field to split a simple Hecke algebra base-changes the saturated packet lattice by Proposition 2.3. If two splitting fields are used, compare both after a common extension. The resulting rational multiplicity spaces are canonically isomorphic as simple-module Hom spaces.

Integrally, the same conclusion requires that the split orders and projective generators base-change compatibly. Under that hypothesis, Morita functoriality gives

$$
T_{\Pi,\lambda}\otimes_\mathcal O\mathcal O'
\xrightarrow{\sim}T_{\Pi,\lambda'}. \tag{13.2}
$$

Changing matrix coordinates conjugates the order and transports the projective generator. Since (5.3) is an intrinsic Hom module, the resulting lattices are canonically isomorphic. Choosing one basis of the simple module merely writes this isomorphism as matrices.

If the rational algebra splits only after a ramified coefficient extension, the trace dual and different described in Section 11.3 must be retained. A rational splitting does not prove that the original integral order was already Morita-split.

### 13.3 Integral PEL presentations

A rational Shimura datum can have two good PEL presentations at a place. If both integral models satisfy the same extension property, the good-model theorem identifies their base schemes uniquely. Their integral cohomology lattices and Hecke correspondences are then identified.

The universal abelian schemes attached to different PEL embeddings need not be isomorphic. They can differ by auxiliary factors or a prime-to-$p$ isogeny. A coefficient-prime Tate factor is independent only when the comparison isogeny and its inverse on the selected factor are integral at $\lambda$. If the isogeny degree is a $\lambda$-adic unit, pullback and the normalized dual isogeny are inverse on Tate lattices. If not, only the rational representations are identified.

Thus presentation independence of the base cohomology is stronger than presentation independence of an auxiliary abelian carrier. The latter must name its integral comparison.

### 13.4 Isogenies and denominator primes

Let $A$ and $A'$ be isogenous abelian varieties with good reduction, and let $f:A\to A'$ have degree $d$. On Tate modules,

$$
T_\lambda f:T_\lambda A\longrightarrow T_\lambda A' \tag{13.3}
$$

is an isomorphism if $d$ is a $\lambda$-adic unit. Indeed the dual isogeny satisfies $f^\vee f=[d]$ after the polarization identifications, so $d^{-1}T_\lambda f^\vee$ is an integral inverse.

If $\lambda\mid d$, the cokernel can be nonzero. Both lattices have finite-flat quotients because both abelian varieties have good reduction, but they need not define the same residual extension or the same finite-flat model. The rational isogeny class therefore contains several legitimate integral carriers.

This is the main limit of absolute canonicity. The construction chooses the lattice supplied by the specified integral quotient or subvariety. It does not declare all isogenous choices equal.

### 13.5 Carrier independence

Suppose two curve multiplicity lattices, or a curve lattice and the Tate lattice of a marked abelian quotient, have rationally isomorphic semisimplifications because their good Frobenius polynomials agree on a dense set. This proves rational carrier independence. It does not identify their integral lattices.

An integral comparison follows only if there is an actual descended correspondence or an integral isogeny comparison carrying one saturated lattice to the other. If the two comparison maps have composites equal to multiplication by a coefficient unit, they are inverse. If their composite is a nonunit, they show only commensurability and measure an index defect.

Therefore the strongest correct statement is:

$$
\begin{array}{c}
\text{rational packet data determine the rational semisimple system;}\\
\text{specified integral correspondences determine the lattice;}\\
\text{specified finite-flat or filtered carriers determine its quotient system.}
\end{array} \tag{13.4}
$$

No line of (13.4) implies the next without the named additional datum.

## 14. Failure atlas

### 14.1 A rational projector with a nonunit denominator

Let $M=\mathcal Oe_1\oplus\mathcal Oe_2$ and let

$$
T=\begin{pmatrix}a&0\\0&b\end{pmatrix},
\qquad a-b\in(\varpi). \tag{14.1}
$$

The rational projector onto $Le_1$ is

$$
e_1(T)=\frac{T-b}{a-b}. \tag{14.2}
$$

Although this operator happens to preserve the displayed diagonal lattice, its formula is not integral in the algebra generated abstractly by $T$. Replace the lattice by

$$
M'=\mathcal O(e_1+e_2)+\mathcal O(\varpi e_2). \tag{14.3}
$$

The same rational operator no longer preserves $M'$. The saturated intersection with $Le_1$ is $\mathcal O\varpi e_1$, while the rational eigenspace is unchanged.

The example prevents three false conclusions: a rational idempotent need not preserve an integral lattice; the saturated intersection need not be a direct summand stable under the complementary projector; and equality of rational packet subspaces does not identify intersections in different ambient lattices.

### 14.2 A stable lattice with the wrong residual extension

Let

$$
\rho(g)=
\begin{pmatrix}
\alpha(g)&c(g)\\
0&\beta(g)
\end{pmatrix}
$$

preserve $T=\mathcal Oe_1+\mathcal Oe_2$. Suppose the reduction of $c$ is nonzero, so $T/\varpi T$ is a nonsplit extension of $\bar\beta$ by $\bar\alpha$. The lattice

$$
T'=\mathcal Oe_1+\mathcal O(\varpi e_2) \tag{14.4}
$$

is also stable, because the upper-right coefficient in the new basis is $\varpi c(g)$. Its reduction is split.

Both lattices span the same rational representation and have the same residual semisimplification. Their residual extension classes differ. If one of them is the Tate lattice of a good-reduction abelian carrier, finite flatness of its residual extension does not automatically transfer to the other. This is why the lattice must be named in every finite-flat statement.

### 14.3 Rational crystallinity without an integral lattice

Assume $K_0/W(k)[1/p]$ is absolutely unramified and $p>2$. Let $V$ be a crystalline two-dimensional rational representation with Hodge labels $\{0,1\}$. This rational condition determines a filtered Frobenius vector space. It does not select a strongly divisible lattice inside it.

Two stable Galois lattices in $V$ can correspond, when they lie in the integral essential image, to different strongly divisible lattices. A third stable lattice need not be strongly divisible at all. Therefore

$$
V\text{ crystalline of weights }\{0,1\}
\centernot\Longrightarrow
T/p^nT\text{ finite flat for an arbitrary }T. \tag{14.5}
$$

The valid implication begins with an integral comparison placing the chosen $T$ in the Fontaine--Laffaille essential image. Theorem 10.2 then supplies all finite quotients.

### 14.4 Flat base change versus descent

Let $R'/R$ be a ramified extension over which two generic points acquire an integral closure with desired equations. The resulting finite-flat group $\mathcal H/R'$ can be conjugated by the Galois group of $R'/R$. If the conjugates are isomorphic but no compatible choice satisfies the cocycle condition, $\mathcal H$ does not descend.

This phenomenon is already familiar for lattices. A rational vector space can possess an $R'$-lattice stable under the restricted Galois group while no stable $R$-lattice has scalar extension equal to it. The obstruction is integral descent data, not generic descent of the vector space.

Consequently potential finite flatness is weaker than finite flatness over $R$. Forward base change in Section 11.1 is unconditional; descent in Section 11.4 is conditional.

The principal invalid inferences and their repairs are now visible in one ledger.

| Invalid inference | Missing datum | Correct repair |
|---|---|---|
| a rational projector cuts an integral summand | denominator is a unit | take saturated intersection |
| a localized generalized eigenspace has rank two | integral multiplicity one | use the full split Hecke order and Morita Hom |
| a rational matrix algebra gives an integral type module | split Azumaya order | exhibit a projective generator and test evaluation |
| a stable lattice is canonical | fixed integral carrier | define the lattice inside cohomology or a Tate module |
| good Frobenius polynomials imply finite flatness at $p$ | coefficient-prime comparison | supply an abelian or strongly divisible carrier |
| crystalline weights $\{0,1\}$ make every lattice finite flat | integral essential-image statement | identify the chosen lattice with a strongly divisible one |
| a raw coefficient kernel is finite flat | flatness of the kernel | close generic relations and take a represented quotient |
| separately chosen finite-flat levels form a system | integral transition maps | construct every level inside common ambient groups |
| rational self-duality is integral self-duality | unit duality index | prove the pairing perfect on the chosen lattice |
| an upstairs model descends | cocycle-compatible integral action | provide effective descent data |
| isogenous abelian factors have the same lattice | isogeny degree is a coefficient unit | compare by integral isogeny and its normalized dual |

Each repair appears in the main theorem as a hypothesis or a construction. The ledger is not a list of technical niceties; each missing datum has an explicit counterexample or index defect in the preceding chapters.

## 15. The canonical-lattice and quotient theorem

### 15.1 The hypothesis ledger

We now collect the exact hypotheses under which the full catalog statement holds. Let $\Pi$ be a noncharacter parallel-weight-two packet, let $\lambda\mid\ell$ be a coefficient place, and let $\mathcal O=\mathcal O_\lambda$. An **integral weight-two packet datum** consists of the following.

**Cohomological carrier.** One has a compact Shimura curve in degree one. The selected component union is Galois and Hecke stable, and the relevant integral cohomology lattice is finite free.

**Rational extraction.** The full finite Hecke image isolates the established packet block, whose rational multiplicity is two.

**Integral extraction.** The localized Hecke order is split by a projective generator, and the integral evaluation map is an isomorphism. At coarse level, every averaging denominator used for comparison is a $\lambda$-adic unit or a direct integral comparison is supplied. The packet pairing factors integrally with its stated component character.

**Coefficient-prime carrier.** At every required place $u\mid\ell$, the resulting rank-two lattice, in a precisely stated covariance, dual, and twist normalization, is supplied either by:

1. a good-reduction abelian scheme with integral $\mathcal O$-action; or
2. when $\ell>2$ and $E_u=W(k)[1/\ell]$ with $k$ perfect, a finite free strongly divisible lattice of weights $[0,1]$ with integral $\mathcal O$-action.

**Comparison.** Every claimed change of curve, level, PEL presentation, or abelian quotient is induced by an integral correspondence whose two composites are coefficient units, or else the corresponding independence claim is omitted.

These hypotheses are not all consequences of rational local--global compatibility. Each supplies a separate integral step.

### 15.2 The curve theorem

**Theorem 15.1 (canonical curve lattice and finite-flat quotients).** Let an integral weight-two packet datum be given in the curve case. Then:

1. the saturated packet lattice

   $$
   M_{\Pi,\lambda}
   =H^1_{\mathrm{et}}(C_{\bar E},\mathcal O)
   \cap H_{\Pi,\lambda}
   $$

   is canonical relative to the integral curve carrier, finite free, saturated, Galois stable, Hecke stable, and compatible with flat coefficient extension;

2. integral Morita extraction gives a canonical finite free rank-two lattice

   $$
   T_{\Pi,\lambda}
   =\operatorname{Hom}_{\mathcal A_{\Pi,\lambda}}
   (\mathcal P_{\Pi,\lambda},M_{\Pi,\lambda});
   $$

3. evaluation is an integral isomorphism and identifies the generic fiber of $T_{\Pi,\lambda}$ with the established rational rank-two representation;

4. for every open ideal $I\subset\mathcal O$, there is a coefficient-linear finite-flat group $\mathcal T_{\Pi,I}/\mathcal O_{E_u}$ with marked generic module

   $$
   T_{\Pi,\lambda}/IT_{\Pi,\lambda};
   $$

5. if $J\subset I$, there is a canonical faithfully flat transition map

   $$
   \mathcal T_{\Pi,J}\longrightarrow\mathcal T_{\Pi,I},
   $$

   and these maps are transitive; their kernels model $IT/JT$;

6. the quotient groups have rank $|\mathcal O/I|^2$, and their coefficient actions factor through $\mathcal O/I$;

7. all assertions are independent of projector formulas, bases, matrix coordinates, and presentations in the senses proved in Chapter 13.

**Proof strategy.** Saturate first, apply integral Morita theory second, and construct every finite quotient inside one common coefficient-prime carrier.

Part 1 is Proposition 5.1. The integral split order, projective generator, and evaluation hypothesis allow Theorem 5.2 to prove parts 2 and 3. The coefficient-prime carrier supplies finite-flat models at the principal $p$-power levels: abelian torsion in the geometric case and Theorem 10.1 in the filtered case. The closure-and-quotient construction of Theorem 8.1 gives part 4 for every open ideal. Section 8.4 and Chapter 9 give part 5. Rank is computed on the generic fiber and preserved by finite flatness, proving part 6. Projector independence is Proposition 2.3; basis and matrix-coordinate independence are Morita functoriality; presentation and carrier comparisons are Chapter 13 under the listed unit hypotheses. $\square$

The theorem deliberately does not say that $T_{\Pi,\lambda}$ is the unique stable lattice in its rational representation. It is the lattice canonically extracted from the named integral packet datum.

**Corollary 15.2 (minimal good-reduction case).** Suppose the packet occurs at fine minimal level, its full finite Hecke module is a line, and its weight-two factor is carried by a good-reduction abelian quotient with integral $\mathcal O$-action. Assume the algebraic comparison between the saturated cohomological branch and the chosen Tate normalization has coefficient-unit degree. Then the saturated branch is already a free rank-two canonical lattice, and every open coefficient quotient is finite flat with the transition system of Theorem 15.1.

**Proof.** At minimal level the integral Morita algebra and module are $\mathcal O$ itself, so evaluation has no defect. Saturation gives a free rank-two lattice. The unit-degree comparison identifies it integrally with the marked abelian Tate factor in the stated duality normalization. Abelian torsion supplies the principal finite-flat levels, and Theorem 8.1 supplies every open-ideal quotient. $\square$

This corollary is the form most often used in the weight-two applications for which no oldvector multiplicity or denominator-prime is present. Its hypotheses also show exactly what must be added at old level or at a congruence prime.

### 15.3 Duality and base-change refinements

**Theorem 15.3.** For the lattice and quotient system of Theorem 15.1:

1. Cartier duality sends $\mathcal T_I$ to a finite-flat model of $(T/IT)^*(1)$ and reverses every transition exact sequence;
2. if a perfect coefficient-adjoint pairing identifies the lattice with its appropriate twisted dual and $I$ is stable under the coefficient involution, this identification descends to the quotient system;
3. finite extension of the local ground field base-changes the entire quotient system;
4. under the hypotheses of Section 11.2, unramified base change agrees with filtered scalar extension;
5. descent is valid exactly when compatible integral descent data are supplied;
6. finite flat coefficient extension is governed on the filtered side by the trace dual $B^\vee$, while nonflat coefficient quotients are governed by admissible annihilators.

**Proof.** Cartier exactness and closure-annihilator compatibility prove parts 1 and 2. Flat base change of closure and quotient proves part 3. Integral Fontaine--Laffaille base change proves part 4. Faithfully flat descent proves part 5. The tensor--Hom calculation (11.7)--(11.8) and the compatible-quotient theorem prove part 6. $\square$

## 16. Dependency audit and conclusion

### 16.1 Exact use of the prerequisites

The argument uses its direct prerequisites in the following forms.

**Finite flat commutative group schemes (Book 46).** The closure of a generic subgroup inside a fixed finite-flat group over a DVR is finite flat, unique, and compatible with flat base change. A finite-flat closed subgroup has a represented faithfully flat quotient, and successive quotient is valid. Torsion of an abelian scheme is finite locally free. We never use a raw kernel or image without proving flatness.

**Cartier duality (Book 47).** Duality commutes with arbitrary base change, reverses faithfully flat exact sequences, and turns the closure of a generic subgroup into the closure of its annihilator in the fixed dual model. On generic modules it gives the Tate-twisted dual. Perfect Weil pairings identify abelian torsion with the torsion of the dual abelian scheme. Every use retains the twist and the coefficient involution.

**Finite-flat Galois representations (Book 48).** A model includes a generic marking; the generic-fiber functor is faithful but not generally full; stable generic submodules close inside a supplied model; coefficient actions can be constructed on an existential model; and arbitrary coefficient quotients are formed by closing generic relations and taking represented quotients. Potential finite flatness is not confused with descent.

**Integral Fontaine--Laffaille equivalence and base change (Book 59).** We use it only for $p>2$, perfect residue field, absolutely unramified base $W(k)$, and weights $[0,1]$. In that range it classifies finite-flat groups, gives uniqueness of marked models, treats Cartier duality and unramified base change, constructs admissible objects for nonflat coefficient quotients, and identifies stable lattices with compatible systems of all finite-flat levels. No statement is extended to $p=2$ or a ramified base.

**Good integral models (Book 130).** At a good PEL place the chosen Shimura curve has a unique smooth projective model under the unramified-order, self-dual-lattice, hyperspecial-level, smooth-local-model, component-stability, neatness, and anisotropy hypotheses. Integral prime-to-residue-characteristic cohomology and Hecke correspondences specialize. Rational idempotents with coefficient-prime denominators are not treated as integral, and the theorem does not itself give a coefficient-prime comparison for the extracted lattice.

**Galois representations from weight-two Shimura cohomology (Book 134).** The curve packet supplies the rational rank-two multiplicity space, its determinant and pairing, and the saturated packet lattice, while recording projector, coarse-level, order, and evaluation denominators. We add integral Morita hypotheses rather than assuming them from the rational extraction.

**Local--global compatibility (Book 136).** Away from the coefficient prime, the established good, semistable, finite-type, and tame-dihedral comparisons are used only under their exact geometric ledgers. At the coefficient prime that theory explicitly supplies no finite-flat conclusion; the present geometric or Fontaine--Laffaille carrier is a separate input.

The hypotheses match in every composition. Schematic closure is used only over a DVR. Fontaine--Laffaille base change is used only for unramified Witt extensions. Integral perfectness is used only after the duality index is shown to vanish. A rational representation is never used to select an integral lattice by itself.

### 16.2 What has been proved

The integral construction can be summarized as a sequence of typed operations:

$$
\begin{array}{c}
\text{integral cohomology and a rational packet subspace}\\
\downarrow\ \text{saturated intersection}\\
\text{primitive packet lattice}\\
\downarrow\ \text{integral Morita Hom}\\
\text{free rank-two Galois lattice}\\
\downarrow\ \text{geometric or filtered coefficient-prime carrier}\\
\text{finite-flat principal levels}\\
\downarrow\ \text{closure of relations and represented quotient}\\
\text{all open-ideal quotients with compatible transitions.}
\end{array} \tag{16.1}
$$

Each arrow has both an existence theorem and a boundary. Saturation needs a fixed ambient lattice. Integral Morita extraction needs a split order, projective generator, and index-one evaluation. The coefficient-prime step needs an actual abelian or strongly divisible carrier. Quotient formation needs the DVR closure theorem. Independence needs integral comparison maps with unit composites.

This is why the resulting lattice is genuinely canonical in the useful sense. It is not chosen by a basis or by one eigenvector. It is functorial in the integral geometry and its full Hecke module, and every finite quotient belongs to one exact system. At the same time, the construction does not conceal its dependence on an isogeny class representative or a denominator prime.

### 16.3 Conclusion

The rational theory of a weight-two packet records traces, determinants, purity, and local parameters. The integral theory begins one level deeper. It asks where the packet sits inside actual cohomology, whether its finite Hecke multiplicity can be removed over the coefficient ring, and whether the resulting rank-two lattice has finite-flat models at the coefficient prime.

Saturation answers the first question without pretending that a rational projector is integral. Integral Morita theory answers the second without choosing an oldvector. A good-reduction abelian factor or an absolutely unramified strongly divisible lattice answers the third. Once one finite-flat ambient system has been supplied, schematic closure of coefficient relations and represented quotients produce every open-ideal quotient, and successive quotient makes all transition maps compatible. Cartier duality retains the Tate twist, reverses these exact sequences, and identifies annihilators inside the fixed dual models.

The curve construction gives rank two directly when the integral Hecke order is split and evaluation is exact. Coefficient-prime finite flatness still requires its own integral carrier. Rational crystallinity, good Frobenius polynomials, and stable-lattice existence do not replace that condition.

The final package is therefore both strong and precise: a free localized cohomological lattice, independent of the harmless integral presentations that have been proved harmless; a finite-flat model for every required coefficient quotient; canonical transition maps, coefficient actions, duals, and allowed base changes; and a complete ledger of the primes and choices at which canonicity legitimately stops.
