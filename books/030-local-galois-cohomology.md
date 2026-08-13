# Local Galois Cohomology

## Contents

1. [The local Galois arena](#1-the-local-galois-arena)
   - [Why local cohomology is unusually computable](#11-why-local-cohomology-is-unusually-computable)
   - [Standing notation and exact field hypotheses](#12-standing-notation-and-exact-field-hypotheses)
   - [Inertia and arithmetic Frobenius](#13-inertia-and-arithmetic-frobenius)
   - [The ramified kernel in three layers](#14-the-ramified-kernel-in-three-layers)
2. [Coefficients and twists](#2-coefficients-and-twists)
   - [Why the coefficient category is part of the theorem](#21-why-the-coefficient-category-is-part-of-the-theorem)
   - [Primary decomposition](#22-primary-decomposition)
   - [Tate twists with exact characteristic restrictions](#23-tate-twists-with-exact-characteristic-restrictions)
   - [Dual modules, without invoking duality](#24-dual-modules-without-invoking-duality)
   - [One-dimensional notation](#25-one-dimensional-notation)
   - [Galois and flat Kummer theory](#26-galois-and-flat-kummer-theory)
3. [Degrees zero and one](#3-degrees-zero-and-one)
   - [Fixed vectors are the first arithmetic calculation](#31-fixed-vectors-are-the-first-arithmetic-calculation)
   - [Cocycles and changes of origin](#32-cocycles-and-changes-of-origin)
   - [Torsors and field equations](#33-torsors-and-field-equations)
   - [Kummer theory](#34-kummer-theory)
   - [Trivial coefficients and reciprocity](#35-trivial-coefficients-and-reciprocity)
   - [One-dimensional characters through reciprocity](#36-one-dimensional-characters-through-reciprocity)
4. [Unramified cohomology and inertia](#4-unramified-cohomology-and-inertia)
   - [The local condition that forgets ramification](#41-the-local-condition-that-forgets-ramification)
   - [Frobenius description](#42-frobenius-description)
   - [A cocycle represented by its Frobenius value](#43-a-cocycle-represented-by-its-frobenius-value)
   - [Prime-to-$p$ inertia cohomology](#44-prime-to-p-inertia-cohomology)
   - [The full prime-to-$p$ calculation](#45-the-full-prime-to-p-calculation)
   - [Unramified is not the same as minimally ramified](#46-unramified-is-not-the-same-as-minimally-ramified)
5. [Explicit finite-module calculations](#5-explicit-finite-module-calculations)
   - [Unramified one-dimensional modules away from $p$](#51-unramified-one-dimensional-modules-away-from-p)
   - [Finite local coefficient rings](#52-finite-local-coefficient-rings)
   - [Roots of unity](#53-roots-of-unity)
   - [Constant cyclic modules](#54-constant-cyclic-modules)
   - [A worked quadratic comparison](#55-a-worked-quadratic-comparison)
   - [What fails in equal characteristic $p$](#56-what-fails-in-equal-characteristic-p)
6. [Cohomological dimension of a local field](#6-cohomological-dimension-of-a-local-field)
   - [What must be proved](#61-what-must-be-proved)
   - [The prime-to-$p$ upper bound](#62-the-prime-to-p-upper-bound)
   - [The equal-characteristic $p$ proof](#63-the-equal-characteristic-p-proof)
   - [The mixed-characteristic $p$ ramification lemma](#64-the-mixed-characteristic-p-ramification-lemma)
   - [Vanishing for arbitrary finite torsion modules](#65-vanishing-for-arbitrary-finite-torsion-modules)
   - [Why torsion in the Galois group is not a contradiction](#66-why-torsion-in-the-galois-group-is-not-a-contradiction)
   - [Uniform bounds and finite extensions](#67-uniform-bounds-and-finite-extensions)
7. [The Brauer group and degree two](#7-the-brauer-group-and-degree-two)
   - [Why the Brauer group is the local obstruction group](#71-why-the-brauer-group-is-the-local-obstruction-group)
   - [Restriction and corestriction of invariants](#72-restriction-and-corestriction-of-invariants)
   - [Computing $H^2(K,\mu_n)$](#73-computing-h2kmu_n)
   - [Symbols and cyclic algebras](#74-symbols-and-cyclic-algebras)
   - [Relative classes and the fundamental class](#75-relative-classes-and-the-fundamental-class)
   - [Finiteness in low degrees](#76-finiteness-in-low-degrees)
8. [The local Euler–Poincaré characteristic](#8-the-local-eulerpoincaré-characteristic)
   - [Additive and multiplicative normalizations](#81-additive-and-multiplicative-normalizations)
   - [Additivity in exact sequences](#82-additivity-in-exact-sequences)
   - [Proof away from the residue characteristic](#83-proof-away-from-the-residue-characteristic)
   - [The mixed-characteristic calculation for the basic module](#84-the-mixed-characteristic-calculation-for-the-basic-module)
   - [Proof for every mixed-characteristic finite module](#85-proof-for-every-mixed-characteristic-finite-module)
   - [Dimension and length consequences](#86-dimension-and-length-consequences)
   - [Checks on Kummer modules](#87-checks-on-kummer-modules)
9. [Changing the local field](#9-changing-the-local-field)
   - [Restriction and corestriction](#91-restriction-and-corestriction)
   - [Kummer classes under extension](#92-kummer-classes-under-extension)
   - [Frobenius and unramified classes](#93-frobenius-and-unramified-classes)
   - [Euler characteristics in extensions](#94-euler-characteristics-in-extensions)
   - [A norm and invariant consistency check](#95-a-norm-and-invariant-consistency-check)
10. [Lattices, limits, and $\ell$-adic representations](#10-lattices-limits-and-ell-adic-representations)
    - [Passing from finite levels](#101-passing-from-finite-levels)
    - [Vector spaces and stable lattices](#102-vector-spaces-and-stable-lattices)
    - [Euler characteristic for vector spaces](#103-euler-characteristic-for-vector-spaces)
    - [Unramified $\ell$-adic cohomology](#104-unramified-ell-adic-cohomology)
    - [One-dimensional $\ell$-adic calculations away from $p$](#105-one-dimensional-ell-adic-calculations-away-from-p)
    - [Two basic $p$-adic lines](#106-two-basic-p-adic-lines)
    - [Finiteness and its limits](#107-finiteness-and-its-limits)
    - [Discrete divisible quotients](#108-discrete-divisible-quotients)
11. [Ramification-shaped local classes](#11-ramification-shaped-local-classes)
    - [Why cohomology needs local subspaces](#111-why-cohomology-needs-local-subspaces)
    - [The unramified subgroup as an extension condition](#112-the-unramified-subgroup-as-an-extension-condition)
    - [Tame classes](#113-tame-classes)
    - [A tame upper-triangular example](#114-a-tame-upper-triangular-example)
    - [Kummer classes and valuation conditions](#115-kummer-classes-and-valuation-conditions)
    - [The unit filtration inside Kummer cohomology](#116-the-unit-filtration-inside-kummer-cohomology)
    - [Finite-flat-shaped classes](#117-finite-flat-shaped-classes)
    - [Stability properties available now](#118-stability-properties-available-now)
12. [Adjoint modules and tangent calculations](#12-adjoint-modules-and-tangent-calculations)
    - [Why conjugation is the coefficient action](#121-why-conjugation-is-the-coefficient-action)
    - [Invariants and the centralizer](#122-invariants-and-the-centralizer)
    - [Ambient tangent dimensions](#123-ambient-tangent-dimensions)
    - [Fixed determinant and trace zero](#124-fixed-determinant-and-trace-zero)
    - [Framed versus unframed first-order parameters](#125-framed-versus-unframed-first-order-parameters)
    - [The unramified tangent space](#126-the-unramified-tangent-space)
    - [A split two-character calculation](#127-a-split-two-character-calculation)
    - [Obstructions stop in degree two](#128-obstructions-stop-in-degree-two)
    - [Tangent and relation ledgers](#129-tangent-and-relation-ledgers)
13. [A reusable local formula collection](#13-a-reusable-local-formula-collection)
    - [The calculation protocol](#131-the-calculation-protocol)
    - [Vanishing and finiteness table](#132-vanishing-and-finiteness-table)
    - [Euler dimension formulas](#133-euler-dimension-formulas)
    - [Prime-to-$p$ unramified line](#134-prime-to-p-unramified-line)
    - [Kummer and constant cyclic formulas](#135-kummer-and-constant-cyclic-formulas)
    - [Restriction and corestriction dictionary](#136-restriction-and-corestriction-dictionary)
    - [Adjoint tangent formulas](#137-adjoint-tangent-formulas)
14. [Conclusion](#14-conclusion)
    - [The two local directions and the exceptional $p$-adic bulk](#141-the-two-local-directions-and-the-exceptional-p-adic-bulk)
    - [What has been established for the next stage](#142-what-has-been-established-for-the-next-stage)

## 1. The local Galois arena

### 1.1 Why local cohomology is unusually computable

Continuous cohomology becomes arithmetic when the profinite group is an absolute Galois group. For a general profinite group, the groups $H^i$ can be large and opaque. For a nonarchimedean local field, valuation theory separates the Galois group into a procyclic residue-field quotient and a ramified kernel, local reciprocity describes its abelianization, and the Brauer invariant supplies the unique degree-two obstruction. Those three facts force most cohomology into degrees zero, one, and two and make its Euler characteristic numerical.

This book carries out that calculation. The continuous-cohomology constructions of Book 24 are assumed: cochains, long exact sequences, restriction, corestriction, inflation–restriction, cup products, and inverse limits. The local-field and reciprocity conventions are those of Books 2--3 and 5, while the flat Kummer comparison and the language of finite-flat torsors come from Book 29. We recall each input where a sign, topology, or coefficient category matters. The aim is not merely to list dimensions. It is to explain why inertia contributes one direction, Frobenius another, and—in mixed characteristic at the coefficient prime—the additive topology of the field contributes $[K:\mathbf Q_p]$ further directions.

The perfect pairings that ultimately identify $H^2(K,M)$ with the dual of a twisted invariant group belong to the next book. Here we establish their inputs: finiteness, cohomological dimension, the Brauer invariant, cup products into it, Euler characteristics, functoriality, and exact low-degree calculations.

### 1.2 Standing notation and exact field hypotheses

Unless a broader hypothesis is stated, $K$ is a **nonarchimedean local field**: a field complete for a nontrivial discrete valuation, with finite residue field. Write

$$
v_K:K^\times\to\mathbf Z,
\qquad \mathcal O_K,
\qquad \mathfrak m_K=(\pi_K),
\qquad k=\mathbf F_q,
$$

and let $p=\operatorname{char}k$. Fix a separable closure $K^s$ and put

$$
G_K=\operatorname{Gal}(K^s/K).
$$

There are two essentially different cases:

1. **mixed characteristic:** $\operatorname{char}K=0$, so $K$ is finite over $\mathbf Q_p$; write $d_K=[K:\mathbf Q_p]$;
2. **equal characteristic:** $\operatorname{char}K=p$, so $K$ is isomorphic, noncanonically, to a finite extension of $\mathbf F_p((t))$.

This distinction is harmless for torsion of order prime to $p$ and decisive for $p$-primary torsion. In equal characteristic, finite $p$-primary coefficients can have infinite $H^1$; consequently the usual finite Euler characteristic is not defined for them.

For a discrete $G_K$-module $M$, we abbreviate

$$
H^i(K,M)=H^i(G_K,M).
$$

For a naturally topological lattice or vector space, $H^i(K,-)$ always means continuous cohomology with its natural topology. No topology will be silently changed.

### 1.3 Inertia and arithmetic Frobenius

Reduction gives the fundamental exact sequence

$$
1\longrightarrow I_K\longrightarrow G_K
\longrightarrow G_k\longrightarrow1,
\qquad
G_k=\operatorname{Gal}(\overline k/k)\simeq\widehat{\mathbf Z}.
$$

The kernel $I_K$ is inertia. We choose the element $\varphi\in G_k$ that acts on $\overline k$ by $x\mapsto x^q$ and call it **arithmetic Frobenius**. A lift of $\varphi$ to $G_K$ will also be denoted $\varphi$ when no ambiguity results. Different lifts differ by inertia, so they induce the same operator on $M^{I_K}$.

This convention agrees with arithmetic local reciprocity:

$$
\operatorname{rec}_K(\pi_K)|_{K^{\mathrm{nr}}}=\varphi.
$$

Geometric Frobenius is $\varphi^{-1}$. Every displayed eigenvalue in this book uses arithmetic Frobenius. Thus a prime-to-$p$ cyclotomic twist has arithmetic Frobenius eigenvalue $q$, not $q^{-1}$.

### 1.4 The ramified kernel in three layers

Inertia has a closed normal wild subgroup $P_K$ and a tame quotient

$$
1\longrightarrow P_K\longrightarrow I_K
\longrightarrow \prod_{r\ne p}\mathbf Z_r(1)\longrightarrow1.
$$

Here $P_K$ is pro-$p$. The notation $(1)$ records conjugation by Frobenius: if $\tau$ is a compatible tame generator, then

$$
\varphi\tau\varphi^{-1}=\tau^q.
$$

The product decomposition is not canonical, but its $r$-primary factor and Frobenius action are intrinsic. For $\ell\ne p$, wild inertia has no positive-degree cohomology on discrete $\ell$-primary modules, while the $\ell$-part of tame inertia behaves like $\mathbf Z_\ell$. This is the structural reason that inertia has $\ell$-cohomological dimension one and $G_K$ has $\ell$-cohomological dimension two.

The slogan “wild inertia is invisible to $\ell$-primary cohomology” must be interpreted correctly. Wild inertia may act nontrivially through a finite $p$-group. Its invariants functor is nevertheless exact because $p$ is invertible on an $\ell$-primary module. Averaging at finite levels kills higher cohomology.

## 2. Coefficients and twists

### 2.1 Why the coefficient category is part of the theorem

Local Galois cohomology uses three coefficient regimes. A **finite Galois module** is a finite abelian group with continuous $G_K$-action and the discrete topology. A **lattice** is a finite free module $T$ over the integers $\mathcal O$ of a finite extension $E/\mathbf Q_\ell$, with its $\mathfrak m_\mathcal O$-adic topology and a continuous action. A finite-dimensional $E$-representation $V$ has its $\ell$-adic topology. After choosing a stable lattice,

$$
A=V/T
$$

is a discrete $\ell$-primary torsion module.

The distinction changes answers. For trivial action,

$$
H^1(\mathbf Z_\ell,\mathbf Z_\ell)\simeq\mathbf Z_\ell
$$

with the profinite topology on the target, whereas the same abstract group declared discrete has no nonzero continuous homomorphism from $\mathbf Z_\ell$. Finite coefficients sit safely in both worlds, but inverse limits require the natural profinite topology.

### 2.2 Primary decomposition

Every finite module decomposes canonically as

$$
M=\bigoplus_\ell M[\ell^\infty].
$$

Continuous cochains commute with finite direct sums, so

$$
H^i(K,M)=\bigoplus_\ell H^i(K,M[\ell^\infty]).
$$

We may therefore calculate one coefficient prime $\ell$ at a time. The branch $\ell\ne p$ is governed by tame inertia. The branch $\ell=p$ is governed by the characteristic of $K$: mixed characteristic gives a two-dimensional theory with finite cohomology for finite modules, while equal characteristic gives cohomological dimension one but often infinite $H^1$. Lower cohomological dimension does not imply smaller groups.

### 2.3 Tate twists with exact characteristic restrictions

Suppose $\ell\ne\operatorname{char}K$. For $n\geq1$, the group of $\ell^n$th roots of unity in $K^s$ is a free rank-one $\mathbf Z/\ell^n\mathbf Z$-module. Define

$$
\mathbf Z/\ell^n\mathbf Z(1)=\mu_{\ell^n},
\qquad
\mathbf Z_\ell(1)=\varprojlim_n\mu_{\ell^n},
\qquad
\mathbf Q_\ell(1)=\mathbf Z_\ell(1)\otimes\mathbf Q_\ell.
$$

For a module $M$, put $M(r)=M\otimes\mathbf Z_\ell(r)$, using the evident finite-level version when $M$ is torsion. Negative twists use the dual of $\mathbf Z_\ell(1)$. The cyclotomic character $\chi_\ell$ is defined by

$$
g(\zeta)=\zeta^{\chi_\ell(g)}.
$$

When $\ell\ne p$, it is unramified and $\chi_\ell(\varphi)=q$. When $\ell=p$ and $K$ has characteristic zero, it is generally ramified, but the same definition is valid. When $K$ has characteristic $p$, the groups $\mu_{p^n}(K^s)$ are trivial: $X^{p^n}-1=(X-1)^{p^n}$. There is therefore no nontrivial étale $p$-adic Tate twist built from Galois modules of roots of unity. This is not a notational inconvenience; Kummer theory at $p$ has genuinely failed.

### 2.4 Dual modules, without invoking duality

Assume $\ell\ne\operatorname{char}K$. For a finite $\ell$-primary module $M$, define its
Pontryagin dual and Tate dual by

$$
M^\vee=\operatorname{Hom}(M,\mathbf Q_\ell/\mathbf Z_\ell),
\qquad
M^*(1)=M^\vee(1),
$$

with $(g f)(m)=g(f(g^{-1}m))$. For a finite-dimensional $E$-representation,

$$
V^*(1)=\operatorname{Hom}_E(V,E)(1).
$$

Evaluation gives a $G_K$-equivariant pairing $M\times M^*(1)\to\mu_{\ell^n}$ at a sufficiently large finite level, and hence cup products into $H^2(K,\mu_{\ell^n})$. We construct the target and its invariant below. In equal characteristic $p$, this construction deliberately excludes $p$-primary $M$: the missing etale $p$-power roots of unity cannot be repaired by notation. We do **not** assert here that the resulting pairings are perfect; that is the central theorem of Book 31.

### 2.5 One-dimensional notation

If $R$ is a finite field, finite local ring, or $\ell$-adic coefficient ring and $\chi:G_K\to R^\times$ is continuous, then $R(\chi)$ denotes the free rank-one $R$-module on which $g$ acts as multiplication by $\chi(g)$. It is unramified precisely when $\chi(I_K)=1$. For an unramified character, write

$$
\alpha=\chi(\varphi).
$$

The value $\alpha$ refers to arithmetic Frobenius. Replacing it by geometric Frobenius replaces $\alpha$ by $\alpha^{-1}$ throughout.

### 2.6 Galois and flat Kummer theory

The phrase “Kummer theory” hides a coefficient choice that becomes visible in residue
characteristic. Over a field $K$, the finite flat group scheme $\mu_n$ is the kernel of the
$n$th-power map on $\mathbf G_m$, and flat cohomology gives, for every $n\geq1$,

$$
H^1_{\mathrm{fppf}}(K,\mu_n)\simeq K^\times/(K^\times)^n. \tag{2.1}
$$

Indeed, the power map is surjective after the finite faithfully flat extension
$K[T]/(T^n-a)$, and every line bundle over a field is trivial. If $n$ is invertible in $K$,
then $\mu_n$ is finite etale, its geometric points form a finite discrete $G_K$-module, and
comparison identifies (2.1) with ordinary Galois cohomology. If
$\operatorname{char}K=p$ and $p\mid n$, the group scheme $\mu_n$ is not etale. Its geometric
$p$-power torsion consists only of the identity, while its flat torsors can be nontrivial.

Consequently there are two coefficient-uniform statements, and they must not be merged:

1. flat Kummer theory computes $K^\times/(K^\times)^n$ for every $n$;
2. Galois Kummer theory computes $H^1(K,\mu_n(K^s))$ by that quotient only when
   $n$ is prime to $\operatorname{char}K$.

The present book concerns absolute Galois groups, so all unqualified groups $H^i(K,M)$ use
discrete Galois modules. We nevertheless keep (2.1) beside the Galois calculation. It explains
exactly where the characteristic-$p$ coefficient fails and prevents the misleading conclusion
that $K^\times/(K^\times)^{p^r}$ vanishes merely because $\mu_{p^r}(K^s)=1$.

## 3. Degrees zero and one

### 3.1 Fixed vectors are the first arithmetic calculation

By definition,

$$
H^0(K,M)=M^{G_K}.
$$

This simple formula already detects rational torsion, invariant lines, and endomorphisms. For example,

$$
H^0(K,\mu_n)=\mu_n(K),
$$

provided $n$ is prime to $\operatorname{char}K$ so that $\mu_n$ is the Galois module of separable $n$th roots. For a representation $W$, $H^0(K,W)$ is the space of equivariant maps from the trivial representation to $W$. For $W=\operatorname{End}(V)$ with conjugation action, it is the centralizer of the image of $G_K$.

The order of $\mu_n(K)$ is easy when $(n,p)=1$: reduction injects prime-to-$p$ roots of unity into $k^\times$ and Hensel lifting is unique, so

$$
|\mu_n(K)|=\gcd(n,q-1).
$$

For $p$-power roots in mixed characteristic, the answer depends on $K$; it must be left as $|\mu_{p^r}(K)|$.

### 3.2 Cocycles and changes of origin

A class in $H^1(K,M)$ is represented by a continuous map $c:G_K\to M$ satisfying

$$
c(gh)=c(g)+g c(h).
$$

Changing $c$ by $g\mapsto gm-m$ changes only its cohomology class. Equivalently, $c$ defines the affine action

$$
g*x=gx+c(g)
$$

on the underlying $M$-space, and a coboundary changes the origin. The class vanishes precisely when this affine action has a fixed point.

This interpretation is useful in deformation problems, where $c(g)$ is the first-order error between two lifts, and in descent, where possible choices form a torsor. It also warns against treating $H^1$ as merely a group of homomorphisms: that simplification is valid only for trivial action.

### 3.3 Torsors and field equations

An $M$-torsor with compatible continuous $G_K$-action determines a class in $H^1(K,M)$ after a geometric point is chosen; a different point changes the cocycle by a coboundary. The torsor has a $K$-rational point exactly when its class is zero.

Assume here that $n$ is prime to $\operatorname{char}K$. For $M=\mu_n$, Galois torsors are equations

$$
X^n=a.
$$

Choosing $b\in K^s$ with $b^n=a$ gives the cocycle

$$
g\longmapsto \frac{g(b)}b\in\mu_n.
$$

Its class is independent of $b$, and it vanishes exactly when $a$ is an $n$th power in $K$. Thus a concrete failure to solve an equation is the same object as an affine descent obstruction.

If $\operatorname{char}K=p$ and $p\mid n$, the same equation defines a flat
$\mu_n$-torsor when $a\in K^\times$, but it is not a torsor under a discrete Galois module:
an $n$th root need not lie in $K^s$. This is exactly the distinction made in Section 2.6.

### 3.4 Kummer theory

Assume $n$ is prime to $\operatorname{char}K$. The separable closure contains all roots of $X^n-a$, and the Kummer sequence is exact:

$$
1\longrightarrow\mu_n\longrightarrow (K^s)^\times
\xrightarrow{x\mapsto x^n}(K^s)^\times\longrightarrow1.
$$

Hilbert 90 gives $H^1(K,(K^s)^\times)=0$. The long exact sequence therefore yields

$$
H^1(K,\mu_n)\simeq K^\times/(K^\times)^n.
$$

The isomorphism is the cocycle construction above. It is valid for $n$ divisible by $p$ in mixed characteristic, because then $\operatorname{char}K=0$. It is not valid for $p\mid n$ in characteristic $p$: the power map is inseparable and not surjective on $(K^s)^\times$.

For $(n,p)=1$, the decomposition into valuation, residue units, and principal units gives

$$
K^\times/(K^\times)^n
\simeq \mathbf Z/n\mathbf Z\oplus k^\times/(k^\times)^n,
$$

because $x\mapsto x^n$ is an automorphism of the pro-$p$ group $U^1$. Hence

$$
|H^1(K,\mu_n)|=n\gcd(n,q-1).
$$

In mixed characteristic, write $n=p^r m$ with $(m,p)=1$. The $p$-adic logarithm on a sufficiently deep unit group and a finite-kernel/cokernel comparison on the remaining layers give

$$
|K^\times/(K^\times)^n|
=n\,\gcd(m,q-1)\,p^{r d_K}|\mu_{p^r}(K)|. \tag{3.1}
$$

Indeed, the valuation contributes $n$, the prime-to-$p$ roots contribute $\gcd(m,q-1)$, and multiplication by $p^r$ on the $d_K$-dimensional $p$-adic Lie group of deep units has cokernel-to-kernel ratio $p^{r d_K}$. Its kernel is precisely the $p$-power roots of unity in the principal units.

Here is the group-theoretic detail behind the last sentence. Choose $s$ deep enough that
logarithm gives an isomorphism

$$
\log:U^s\xrightarrow{\sim}\mathfrak m_K^s.
$$

The additive group on the right is free of rank $d_K$ over $\mathbf Z_p$, so multiplication by
$p^r$ has cokernel of order $p^{rd_K}$ and no kernel. The quotient $U^1/U^s$ is finite. For
any endomorphism $f$ of a finite abelian group $A$,
$|\operatorname{coker}f|=|\ker f|$; applying this to the $p^r$th-power map on the finite
quotient shows that its finite-layer contribution is exactly the size of the kernel that was
removed on passing to $U^s$. That kernel is $\mu_{p^r}(K)$. Hence

$$
|U^1/(U^1)^{p^r}|=p^{rd_K}|\mu_{p^r}(K)|.
$$

Multiplication by $m$ is an automorphism of $U^1$, while the Teichmuller group of order $q-1$
contributes $\gcd(m,q-1)$. Combining these factors with the valuation quotient proves (3.1)
without choosing a noncanonical global decomposition of $U^1$.

### 3.5 Trivial coefficients and reciprocity

If $C$ is a finite abelian group with trivial action, then

$$
H^1(K,C)=\operatorname{Hom}_{\mathrm{cts}}(G_K,C).
$$

Every such homomorphism factors through $G_K^{\mathrm{ab}}$. Arithmetic local reciprocity identifies it with a continuous character of $K^\times$:

$$
H^1(K,C)\simeq\operatorname{Hom}_{\mathrm{cts}}(K^\times,C).
$$

For $C=\mathbf Z/n\mathbf Z$ and $(n,p)=1$, principal units contribute nothing, so

$$
|H^1(K,\mathbf Z/n\mathbf Z)|=n\gcd(n,q-1).
$$

One factor records the image of a uniformizer and the other a character of the cyclic residue-unit group. In mixed characteristic, formula (3.1) also gives the order of this character group: a finite abelian group and its character group into $\mathbf Z/n\mathbf Z$ have the same order when the group is killed by $n$.

### 3.6 One-dimensional characters through reciprocity

A finite-order character $G_K\to A^\times$ corresponds to a character $K^\times\to A^\times$. It is unramified exactly when it is trivial on $\mathcal O_K^\times$, tamely ramified exactly when it is trivial on $U^1$ but not on all units, and wildly ramified when its restriction to $U^1$ is nontrivial. The conductor is the least $a\geq0$ such that the character is trivial on $U^a$.

If $L/K$ is finite separable, restriction of a Galois character corresponds to precomposition
with the norm:

$$
\chi|_{G_L}\quad\longleftrightarrow\quad
\chi_K\circ N_{L/K}:L^\times\to A^\times.
$$

This provides explicit cocycles and characters, but it does not compute $H^1$ for a nontrivial higher-dimensional action. Inertia and inflation–restriction supply that computation next.

## 4. Unramified cohomology and inertia

### 4.1 The local condition that forgets ramification

A degree-one class is **unramified** if it becomes zero on inertia. Define

$$
H^1_{\mathrm{ur}}(K,M)
=\ker\bigl(H^1(K,M)\longrightarrow H^1(I_K,M)\bigr).
$$

This definition is intrinsic and works for any discrete module. It says that the corresponding torsor becomes trivial over the maximal unramified extension. It does **not** mean that the coefficient module itself is unramified. Even when inertia acts on $M$, a class can descend from the residue quotient through the invariant submodule $M^{I_K}$.

The quotient $G_k\simeq\widehat{\mathbf Z}$ has cohomological dimension one on discrete torsion modules. Inflation–restriction therefore begins with the exact sequence

$$
0\longrightarrow H^1(G_k,M^{I_K})
\xrightarrow{\mathrm{inf}}H^1(K,M)
\xrightarrow{\mathrm{res}}H^1(I_K,M)^{G_k}
\longrightarrow0. \tag{4.1}
$$

The last zero follows from $H^2(G_k,M^{I_K})=0$. In particular,

$$
H^1_{\mathrm{ur}}(K,M)\simeq H^1(G_k,M^{I_K}).
$$

### 4.2 Frobenius description

For a discrete torsion module $N$ with continuous $G_k$-action, the procyclic calculation gives

$$
H^0(G_k,N)=\ker(\varphi-1:N\to N),
$$

$$
H^1(G_k,N)=\operatorname{coker}(\varphi-1:N\to N).
$$

Applying this to $N=M^{I_K}$ yields the fundamental formulas

$$
H^0(K,M)=\ker(\varphi-1:M^{I_K}\to M^{I_K}), \tag{4.2}
$$

$$
H^1_{\mathrm{ur}}(K,M)\simeq
M^{I_K}/(\varphi-1)M^{I_K}. \tag{4.3}
$$

The formulas are independent of the lift of $\varphi$, because inertia acts trivially on $M^{I_K}$. For finite $M$, kernel and cokernel of an endomorphism have the same order, so

$$
|H^1_{\mathrm{ur}}(K,M)|=|H^0(K,M)|. \tag{4.4}
$$

For a finite-dimensional coefficient vector space the same statement holds with dimensions.

### 4.3 A cocycle represented by its Frobenius value

Suppose first that $M$ is unramified. An unramified cocycle is zero on $I_K$ and hence descends to $G_k$. It is determined by $m=c(\varphi)$. For $r>0$,

$$
c(\varphi^r)=m+\varphi m+\cdots+\varphi^{r-1}m.
$$

Changing the cocycle by the coboundary attached to $x\in M$ replaces $m$ by $m+(\varphi-1)x$. This gives (4.3) directly. For torsion $M$, the formula extends continuously from the dense cyclic subgroup generated by $\varphi$: after a sufficiently large finite quotient, the required norm sum kills $m$.

If $M$ is ramified, precisely the same calculation takes place in $M^{I_K}$. This explains why one must take inertia invariants before forming the Frobenius cokernel.

### 4.4 Prime-to-$p$ inertia cohomology

Let $M$ be a finite $\ell$-primary module with $\ell\ne p$. Since $P_K$ is pro-$p$, averaging makes

$$
H^j(P_K,M)=0\qquad(j>0),
$$

and passage to $P_K$-invariants is exact. The only possible positive-degree contribution from inertia comes from the $\mathbf Z_\ell(1)$ factor of tame inertia. It follows that

$$
H^j(I_K,M)=0\qquad(j>1). \tag{4.5}
$$

There is a useful explicit form when wild inertia acts trivially. Let $I_K^t$ denote tame inertia and let $\tau$ be an $\ell$-adic tame generator. A cocycle is determined, after the prime-to-$\ell$ factors have been averaged away, by its value at $\tau$. Thus

$$
H^1(I_K,M)\simeq
\bigl(M/(\tau-1)M\bigr)^{I_K/I_{K,\ell}}, \tag{4.6}
$$

where $I_{K,\ell}\simeq\mathbf Z_\ell(1)$ is the pro-$\ell$ tame factor and the superscript records descent under the remaining tame factors. When all inertia acts trivially, this simplifies canonically to

$$
H^1(I_K,M)\simeq\operatorname{Hom}_{\mathrm{cts}}(\mathbf Z_\ell(1),M)\simeq M(-1). \tag{4.7}
$$

Under this identification arithmetic Frobenius acts on $M(-1)$: if it acts on $M$ by $A$, it acts on $H^1(I_K,M)$ by $q^{-1}A$. The inverse factor comes from precomposing a homomorphism with $\varphi^{-1}\tau\varphi=\tau^{q^{-1}}$.

### 4.5 The full prime-to-$p$ calculation

The Hochschild–Serre filtration for

$$
1\to I_K\to G_K\to G_k\to1
$$

has only two nonzero rows and two nonzero columns for finite $\ell$-primary $M$, $\ell\ne p$. Consequently (4.1) is exact and

$$
H^2(K,M)\simeq
H^1\bigl(G_k,H^1(I_K,M)\bigr), \tag{4.8}
$$

$$
H^i(K,M)=0\qquad(i>2). \tag{4.9}
$$

The isomorphism (4.8) is the edge map of the spectral sequence. It is especially concrete when inertia is trivial:

$$
H^2(K,M)\simeq
M(-1)/(\varphi-1)M(-1). \tag{4.10}
$$

Combining (4.1), (4.2), and (4.8) gives a complete algorithm: compute inertia invariants, compute the first inertia cohomology, and then take Frobenius kernels or cokernels. No choice of ramified splitting is involved.

It also gives uniform bounds away from $p$. If $M$ is an $r$-dimensional vector space over a
finite field of characteristic $\ell\ne p$, then $M^{I_K}$ has dimension at most $r$, and the
one-pro-$\ell$-direction calculation gives

$$
\dim H^1(I_K,M)\leq r.
$$

Consequently

$$
h^0(K,M)\leq r,\qquad h^2(K,M)\leq r,
\qquad h^1(K,M)\leq2r. \tag{4.11}
$$

The same argument bounds lengths by the length of $M$ over a finite local coefficient ring.
These estimates are independent of the finite Galois quotient through which the action factors
and of its ramification depth. They are deliberately stated only away from $p$; in mixed
characteristic the principal units add the $d_Kr$ term, and the Euler formula is the correct
uniform statement.

### 4.6 Unramified is not the same as minimally ramified

If inertia acts trivially on $M$, every coefficient vector is unramified, but not every cohomology class is. Formula (4.1) has a second term

$$
H^1(I_K,M)^{\varphi=1}\simeq M(-1)^{\varphi=1},
$$

which consists of tamely ramified classes. For example, with $M=\mathbf F_\ell$ trivial and $q\equiv1\pmod\ell$, one has

$$
\dim H^1(K,M)=2,
\qquad
\dim H^1_{\mathrm{ur}}(K,M)=1.
$$

One line comes from a character of the valuation quotient and one from a tame character of units. Thus an unramified representation may possess ramified extension classes.

## 5. Explicit finite-module calculations

### 5.1 Unramified one-dimensional modules away from $p$

Let $F$ be a finite field of characteristic $\ell\ne p$, and let $M=F(\chi)$ be one-dimensional. First suppose $\chi$ is unramified and put $\alpha=\chi(\varphi)$. Inertia is trivial, so (4.7) identifies $H^1(I_K,M)$ with $M(-1)$, on which $\varphi$ acts by $\alpha q^{-1}$. Write $[P]$ for $1$ if the assertion $P$ holds in $F$ and $0$ otherwise. Then

$$
\dim_F H^0(K,M)=[\alpha=1], \tag{5.1}
$$

$$
\dim_F H^1(K,M)=[\alpha=1]+[\alpha=q], \tag{5.2}
$$

$$
\dim_F H^2(K,M)=[\alpha=q]. \tag{5.3}
$$

The two summands in $H^1$ have different origins: the first is unramified and the second is tame. If $q=1$ in $F$ and $\alpha=1$, the dimensions are $(1,2,1)$. If $\alpha$ equals neither $1$ nor $q$, every cohomology group vanishes.

The same computation is useful in arbitrary rank. Let $M$ be an unramified finite-dimensional
$F$-representation and let $A$ be arithmetic Frobenius. Then

$$
h^0(K,M)=\dim_F\ker(A-1),
$$

$$
h^2(K,M)=\dim_F\operatorname{coker}(q^{-1}A-1)
=\dim_F\ker(A-q),
$$

and the exact sequence (4.1) gives

$$
h^1(K,M)=\dim_F\ker(A-1)+\dim_F\ker(A-q).
$$

The last equality between a cokernel and a kernel uses only that an endomorphism of a finite
dimensional vector space has equal kernel and cokernel dimensions. These formulas do not require
$A$ to be semisimple. For a nontrivial Jordan block with eigenvalue $1$, the contribution is
the dimension of the eigenspace, not the algebraic multiplicity; likewise at eigenvalue $q$.
Thus local cohomology detects the ends of the two exceptional generalized eigenspaces rather than
the full characteristic polynomial.

Now suppose $\chi|_{I_K}$ is nontrivial. Its finite image in $F^\times$ has order prime to $\ell$. Taking invariants under that image is exact, and both $M^{I_K}$ and the descended $H^1(I_K,M)$ vanish. Therefore

$$
H^i(K,F(\chi))=0\quad\text{for every }i\geq0. \tag{5.4}
$$

This last statement uses one-dimensionality and $\ell\ne p$. It is false as a blanket assertion for higher-dimensional ramified modules, which may contain inertia invariants or nontrivial tame coinvariants.

### 5.2 Finite local coefficient rings

Let $R$ be a finite principal local ring of residue characteristic $\ell\ne p$, and let $M=R(\chi)$ be unramified with $\chi(\varphi)=\alpha\in R^\times$. Put $a=\alpha-1$ and $b=\alpha q^{-1}-1$. The same two-row calculation gives

$$
H^0(K,M)=\ker(a:M\to M),
$$

$$
0\longrightarrow\operatorname{coker}(a)\longrightarrow H^1(K,M)
\longrightarrow\ker(b)\longrightarrow0,
$$

$$
H^2(K,M)=\operatorname{coker}(b).
$$

For a finite-length $R$-module, an endomorphism has kernels and cokernels of equal length. Hence

$$
\operatorname{length}_R H^1
=\operatorname{length}_R H^0+
\operatorname{length}_R H^2. \tag{5.5}
$$

The exact sequence for $H^1$ need not split canonically. A dimension formula should not be mistaken for a decomposition of classes.

For example, take $R=\mathbf Z/\ell^r\mathbf Z$ and write

$$
s=\min\{r,v_\ell(\alpha-1)\},\qquad
t=\min\{r,v_\ell(\alpha-q)\}.
$$

Because $q$ is a unit in $R$, multiplication by $b=\alpha q^{-1}-1$ has the same kernel and
cokernel length as multiplication by $\alpha-q$. Hence

$$
\operatorname{length}H^0=s,\qquad
\operatorname{length}H^2=t,\qquad
\operatorname{length}H^1=s+t.
$$

This refines the residual eigenvalue test. A Frobenius eigenvalue merely congruent to $1$ or
$q$ modulo a high power of $\ell$ creates finite integral cohomology even if it is not equal to
either value in characteristic zero. Such congruence classes disappear after inverting $\ell$
but matter at every finite coefficient level.

### 5.3 Roots of unity

Assume $n$ is prime to $\operatorname{char}K$. Kummer theory already gives

$$
H^0(K,\mu_n)=\mu_n(K),
\qquad
H^1(K,\mu_n)=K^\times/(K^\times)^n.
$$

The degree-two calculation will show

$$
H^2(K,\mu_n)\simeq\operatorname{Br}(K)[n]\simeq\mathbf Z/n\mathbf Z. \tag{5.6}
$$

When $(n,p)=1$, their orders are therefore

$$
\bigl(|H^0|,|H^1|,|H^2|\bigr)
=\bigl(\gcd(n,q-1),\ n\gcd(n,q-1),\ n\bigr). \tag{5.7}
$$

The alternating quotient is one. In mixed characteristic, formula (3.1) replaces the middle term and produces the $p$-adic Euler factor.

### 5.4 Constant cyclic modules

Let $C_n=\mathbf Z/n\mathbf Z$ with trivial action and assume $n$ is prime to $\operatorname{char}K$. Then

$$
H^0(K,C_n)=C_n,
\qquad
H^1(K,C_n)=\operatorname{Hom}_{\mathrm{cts}}(K^\times,C_n).
$$

The prime-to-$p$ inertia calculation and, for the mixed-characteristic $p$-part, the
prime-to-$p$ descent calculation of Section 8.4 give

$$
|H^2(K,C_n)|=|\mu_n(K)|. \tag{5.8}
$$

This equality of orders does not yet assert a perfect pairing or a canonical identification with the dual of $\mu_n(K)$. Those stronger statements require local duality.

For $(n,p)=1$ the three orders are

$$
\bigl(n,\ n\gcd(n,q-1),\ \gcd(n,q-1)\bigr). \tag{5.9}
$$

If $\mu_n\subset K$, then a choice of primitive root identifies $C_n$ with $\mu_n$, and (5.6) gives $H^2(K,C_n)\simeq C_n$. Without that choice—and especially when not all roots lie in $K$—one must not identify the two coefficient modules.

### 5.5 A worked quadratic comparison

Assume $p$ is odd and take $n=2$. Since $\mu_2\subset K$, both $\mu_2$ and $C_2$ are the trivial two-element module. The square-class decomposition gives

$$
K^\times/(K^\times)^2\simeq
\langle\pi_K\rangle/\langle\pi_K^2\rangle
\oplus k^\times/(k^\times)^2,
$$

so it has order four. Thus

$$
(h^0,h^1,h^2)=(1,2,1)
$$

over $\mathbf F_2$. One degree-one class is unramified and cuts out the unramified quadratic extension; the other is ramified and is detected on tame inertia. Their sum cuts out the remaining quadratic character. If $p=2$, this computation fails: principal units contribute many square classes, and in mixed characteristic the answer grows with $[K:\mathbf Q_2]$.

### 5.6 What fails in equal characteristic $p$

Let $K=\mathbf F_q((t))$ and use the constant module $\mathbf F_p$. The Artin–Schreier sequence

$$
0\longrightarrow\mathbf F_p\longrightarrow K^s
\xrightarrow{x\mapsto x^p-x}K^s\longrightarrow0
$$

gives

$$
H^1(K,\mathbf F_p)\simeq K/(F-1)K.
$$

This group is infinite. For example, the classes of $t^{-m}$ with $m>0$ and $p\nmid m$ are linearly independent over $\mathbf F_p$ after grouping exponents into orbits under multiplication by $p$: the lowest pole of $x^p-x$ has order divisible by $p$. On the other hand,

$$
H^i(K,\mathbf F_p)=0\qquad(i>1).
$$

Thus equal-characteristic $p$-cohomology is shallow but not finite. Any Euler formula written with cardinalities in this setting is false or meaningless.

## 6. Cohomological dimension of a local field

### 6.1 What must be proved

For a prime $\ell$, $\operatorname{cd}_\ell(G_K)$ is the least $d$ for which $H^i(K,M)=0$ for every discrete $\ell$-primary torsion module $M$ and every $i>d$. Finite modules suffice to test the bound, because every discrete torsion module is a filtered union of finite stable submodules and continuous cohomology commutes with such unions.

The answer is

$$
\operatorname{cd}_\ell(G_K)=
\begin{cases}
2,&\ell\ne p,\\
2,&\ell=p\text{ and }\operatorname{char}K=0,\\
1,&\ell=p\text{ and }\operatorname{char}K=p.
\end{cases} \tag{6.1}
$$

The equal-characteristic entry assumes $K$ is a local field, hence perfect residue field. More general henselian discretely valued fields require residue-field dimension terms.

### 6.2 The prime-to-$p$ upper bound

For $\ell\ne p$, Section 4 already contains the proof. Wild inertia has $\ell$-cohomological dimension zero. Its tame quotient has only one pro-$\ell$ direction, so $\operatorname{cd}_\ell(I_K)=1$. The residue group $G_k\simeq\widehat{\mathbf Z}$ has $\ell$-cohomological dimension one. Hochschild–Serre then gives

$$
\operatorname{cd}_\ell(G_K)\leq2.
$$

To make the two occurrences of “one” precise, pass first through wild inertia. Since every finite
quotient of $P_K$ is a $p$-group, averaging kills its higher cohomology on an
$\ell$-primary module. Next write the tame quotient as

$$
\prod_{r\ne p}\mathbf Z_r(1)
=\mathbf Z_\ell(1)\times\prod_{r\ne p,\ell}\mathbf Z_r(1).
$$

The second factor again has exact invariants on $\ell$-primary modules, while
$\mathbf Z_\ell$ has the two-term continuous complex

$$
N\xrightarrow{\tau-1}N.
$$

Thus inertia contributes rows $j=0,1$ and no others. The residue quotient has the analogous
two-term complex $P\xrightarrow{\varphi-1}P$, so it contributes columns $i=0,1$. The
Hochschild--Serre page is literally a two-by-two square, and total degree cannot exceed two.
This argument works for every finite $\ell$-primary action, not merely an unramified or
semisimple one.

The bound is sharp without changing the field. The Galois module $\mu_\ell$ is defined whether
or not its elements are $K$-rational, and the Brauer calculation gives

$$
H^2(K,\mu_\ell)\simeq\mathbf Z/\ell\mathbf Z\ne0.
$$

Thus the dimension is exactly two.

### 6.3 The equal-characteristic $p$ proof

Assume $\operatorname{char}K=p$. The additive group $(K^s,+)$ is cohomologically trivial: additive Hilbert 90 holds for every finite Galois subextension, and passage to the filtered union gives vanishing in positive degrees. The Artin–Schreier map $F-1:x\mapsto x^p-x$ is surjective on $K^s$, since every polynomial $X^p-X-a$ is separable and has a root in $K^s$. Hence

$$
0\to\mathbf F_p\to K^s\xrightarrow{F-1}K^s\to0
$$

and its long exact sequence imply

$$
H^i(K,\mathbf F_p)=0\qquad(i\geq2).
$$

The same argument works after every finite separable extension of $K$. We use the following
standard open-subgroup criterion: if

$$
H^{d+1}(U,\mathbf F_p)=0
$$

for every open subgroup $U$ of a profinite group $G$, then
$\operatorname{cd}_p(G)\leq d$. This is a dimension-shifting statement, not a claim that an
arbitrary modular representation becomes trivial after a prime-to-$p$ extension. One proof
uses permutation modules $\mathbf F_p[G/U]$ and Shapiro's lemma to test the projective dimension
of the trivial module; dimension shifting then gives vanishing for every finite $p$-primary
module, and filtered unions give it for every discrete $p$-primary module. Applying the
criterion with $d=1$ gives $\operatorname{cd}_p(G_K)\leq1$. Nonzero Artin--Schreier classes show
$H^1(K,\mathbf F_p)\ne0$, so equality holds.

This proof also explains the infinite group in Section 5.6. Surjectivity of $F-1$ over $K^s$ kills degree two, while its large cokernel over $K$ creates many degree-one extensions.

### 6.4 The mixed-characteristic $p$ ramification lemma

The remaining upper bound is the subtle one.

**Ramification lemma.** If $F$ is a finite extension of $\mathbf Q_p$, then

$$
H^i(F,M)=0\qquad(i>2)
$$

for every finite $p$-primary $G_F$-module $M$.

Here is a complete proof route. We include the reduction because simply quoting the prime-to-$p$ inertia argument would be wrong: wild inertia is now visible.

First we need only the following degree-three multiplicative-coefficient lemma. For every finite
extension $E/F$,

$$
H^3(E,(E^s)^\times)=0. \tag{6.2}
$$

Indeed, continuous cohomology with the discrete module $(E^s)^\times$ is the filtered colimit of

$$
H^3(\operatorname{Gal}(L/E),L^\times)
$$

over finite Galois $L/E$. The local fundamental class of Book 5 gives the class-formation
isomorphism

$$
H^3(\operatorname{Gal}(L/E),L^\times)
\simeq H^1(\operatorname{Gal}(L/E),\mathbf Z).
$$

The group on the right is zero: a homomorphism from a finite group to the torsion-free group
$\mathbf Z$ vanishes. Every term in the filtered system is therefore zero, proving (6.2). This
is precisely the multiplicative input needed below; no blanket cohomological-dimension claim for
$(E^s)^\times$ has been smuggled in.

Since $E$ has characteristic zero, apply the Kummer sequence; it is exact whether or not
$\mu_p\subset E$:

$$
1\to\mu_p\to(E^s)^\times\xrightarrow{p}(E^s)^\times\to1.
$$

The degree-three part of its long exact sequence is

$$
\operatorname{Br}(E)\xrightarrow{p}\operatorname{Br}(E)
\longrightarrow H^3(E,\mu_p)
\longrightarrow H^3(E,(E^s)^\times).
$$

The last group vanishes by (6.2), and multiplication by $p$ on
$\operatorname{Br}(E)\simeq\mathbf Q/\mathbf Z$ is surjective. Hence
$H^3(E,\mu_p)=0$.

Finally apply the open-subgroup criterion stated in Section 6.3. Every open subgroup of $G_F$ is
$G_E$ for a finite extension $E/F$. Put $E'=E(\mu_p)$. Its degree over $E$ divides $p-1$, so
restriction on $p$-primary cohomology is injective. Over $E'$, a choice of primitive $p$th root
identifies the trivial module $\mathbf F_p$ with $\mu_p$, and the preceding calculation gives

$$
H^3(E',\mathbf F_p)=0.
$$

Injectivity of restriction gives $H^3(E,\mathbf F_p)=0$. The criterion now proves
$\operatorname{cd}_p(G_F)\leq2$. Finally $H^2(F,\mu_p)\simeq\operatorname{Br}(F)[p]$ is already
nonzero over $F$, whether or not $\mu_p\subset F$, so the bound is sharp. Consequently
$\operatorname{cd}_p(G_F)=2$.

### 6.5 Vanishing for arbitrary finite torsion modules

Combining the primary decomposition with (6.1) gives a uniform statement valid in both characteristics:

**Theorem 6.1.** For every nonarchimedean local field $K$ and every finite discrete $G_K$-module $M$,

$$
H^i(K,M)=0\qquad(i>2).
$$

If $\operatorname{char}K=p$ and $M$ is $p$-primary, the stronger vanishing $H^i(K,M)=0$ for $i>1$ holds. The theorem does not assert finiteness in degrees zero through two; the equal-characteristic $p$ counterexample remains.

### 6.6 Why torsion in the Galois group is not a contradiction

A profinite group containing an element of order $\ell$ has infinite $\ell$-cohomological dimension. Formula (6.1) therefore implies that $G_K$ has no element of order $\ell$ when its $\ell$-dimension is finite. This is consistent even when finite Galois quotients have elements of order $\ell$: a quotient element need not lift to an element of the same finite order. Finite quotient cohomology can be periodic, but its high-degree classes die after inflation to finer quotients. Continuous cohomology records the direct limit, not one quotient in isolation.

### 6.7 Uniform bounds and finite extensions

Cohomological dimension is stable under the finite field changes used in explicit calculations,
but the precise statement has an index condition. If $L/K$ is finite separable, then $G_L$ is open in
$G_K$, and Shapiro's lemma gives

$$
\operatorname{cd}_\ell(G_L)\leq\operatorname{cd}_\ell(G_K).
$$

If $[L:K]$ is prime to $\ell$, restriction followed by corestriction is multiplication by an
$\ell$-adic unit on every $\ell$-primary cohomology group. Restriction is then injective, and
the reverse inequality follows. Thus

$$
\operatorname{cd}_\ell(G_L)=\operatorname{cd}_\ell(G_K)
\qquad\text{if }\ell\nmid[L:K]. \tag{6.3}
$$

This justifies the prime-to-$p$ descent used in Section 6.4. Adjoining $\mu_p$ in mixed
characteristic has degree dividing $p-1$; for $p=2$ the root $-1$ is already present. Thus the
vanishing of $H^3$ for the trivial module may safely be checked after that extension. For any
$\ell\ne\operatorname{char}K$, no extension is needed to prove sharpness:
$H^2(K,\mu_\ell)$ is nonzero by the Brauer invariant even when the roots themselves are not
$K$-rational.

The vanishing bound is also uniform in the coefficient exponent. If $M$ is killed by
$\ell^r$, no constant in Theorem 6.1 depends on $r$, on the size of the finite quotient through
which the action factors, or on the ramification break of that quotient. Ramification changes
the groups in degrees one and two, sometimes dramatically, but cannot create a degree-three
class. This is the form required when one passes through all quotients $T/\varpi^rT$ of a
lattice.

## 7. The Brauer group and degree two

### 7.1 Why the Brauer group is the local obstruction group

Degree two classifies factor sets and descent obstructions. For the multiplicative group of a separable closure, these factor sets classify central simple algebras:

$$
H^2(K,(K^s)^\times)=\operatorname{Br}(K).
$$

Local class field theory computes this group by the invariant isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)\xrightarrow{\sim}\mathbf Q/\mathbf Z. \tag{7.1}
$$

Our normalization is the one fixed in Book 5. If $K_m/K$ is unramified of degree $m$, $\varphi$ is arithmetic Frobenius, and $\pi_K$ is a uniformizer, then the cyclic algebra

$$
(K_m/K,\varphi,\pi_K^a)
$$

has invariant $a/m$. This convention is compatible with arithmetic reciprocity.

### 7.2 Restriction and corestriction of invariants

For a finite separable extension $L/K$ of degree $d$,

$$
\operatorname{inv}_L(\operatorname{res}_{L/K}\beta)
=d\operatorname{inv}_K(\beta), \tag{7.2}
$$

$$
\operatorname{inv}_K(\operatorname{cor}_{L/K}\gamma)
=\operatorname{inv}_L(\gamma). \tag{7.3}
$$

The first formula may be checked by separating $L/K$ into unramified and totally ramified stages. Unramified base change replaces Frobenius by a degree-$f$ power; total ramification replaces $\pi_K$ by a unit times $\pi_L^e$, and units are norms from an unramified splitting field. Both operations multiply the numerator by the relevant degree. The second formula follows from the cyclic-algebra norm construction, or from (7.2) together with $\operatorname{cor}\circ\operatorname{res}=d$.

These formulas determine the direction of every later functorial statement. Restriction multiplies a local invariant; corestriction preserves it.

### 7.3 Computing $H^2(K,\mu_n)$

Assume $n$ is prime to $\operatorname{char}K$. Continue the Kummer long exact sequence past degree one:

$$
0\longrightarrow H^2(K,\mu_n)
\longrightarrow\operatorname{Br}(K)
\xrightarrow{n}\operatorname{Br}(K).
$$

Multiplication by $n$ on $\mathbf Q/\mathbf Z$ is surjective. Therefore

$$
H^2(K,\mu_n)\xrightarrow{\sim}\operatorname{Br}(K)[n]
\xrightarrow{\operatorname{inv}_K}\frac1n\mathbf Z/\mathbf Z. \tag{7.4}
$$

Sending $a/n$ to $a$ identifies the last group with $\mathbf Z/n\mathbf Z$, but the invariant-valued form is more canonical. In particular, $H^2(K,\mu_n)$ is cyclic of order $n$.

If $\operatorname{char}K=p$ and $p\mid n$, there is no such statement for the Galois module of roots of unity: its $p$-primary part is trivial and the Kummer sequence is not exact. Flat cohomology can restore a Kummer sequence for the group scheme $\mu_{p^r}$, but that is a different cohomology theory and is not being used here.

For comparison, flat Kummer theory over the field $K$ has no characteristic restriction.
Because $\operatorname{Pic}(K)=0$, its degree-two segment is

$$
H^2_{\mathrm{fppf}}(K,\mu_n)\simeq\operatorname{Br}(K)[n]
\simeq\frac1n\mathbf Z/\mathbf Z \tag{7.5}
$$

for every $n\geq1$. Thus in characteristic $p$, the flat group
$H^2_{\mathrm{fppf}}(K,\mu_{p^r})$ is cyclic of order $p^r$, whereas the discrete Galois
module $\mu_{p^r}(K^s)$ is trivial and has zero positive-degree Galois cohomology. This is the
degree-two counterpart of Section 2.6 and completes the coefficient-uniform Kummer comparison.

### 7.4 Symbols and cyclic algebras

Assume $n$ is prime to $\operatorname{char}K$. A Kummer class
$a\in K^\times/(K^\times)^n$ and a character
$\chi\in H^1(K,\mathbf Z/n\mathbf Z)$ have a cup product, using the canonical scalar-action
pairing $\mu_n\otimes\mathbf Z/n\mathbf Z\to\mu_n$,

$$
(a)\smile\chi\in H^2(K,\mu_n).
$$

If $\chi$ has exact order $n$, if $L/K$ is the cyclic extension it cuts out, and if $\sigma$
corresponds to $1\in\mathbf Z/n\mathbf Z$, this cup product is represented by the cyclic algebra

$$
(L/K,\sigma,a).
$$

It vanishes precisely when $a$ is a norm from $L^\times$. This follows directly from the factor-set presentation: changing the crossed-product generator by $b\in L^\times$ changes its $n$th power by $N_{L/K}(b)$. Thus cup products already encode norm equations. The next book will prove that these symbols detect every nonzero class on either side.

### 7.5 Relative classes and the fundamental class

For finite Galois $L/K$ of degree $d$,

$$
H^2(\operatorname{Gal}(L/K),L^\times)
\simeq\ker(\operatorname{Br}(K)\to\operatorname{Br}(L))
\simeq\frac1d\mathbf Z/\mathbf Z.
$$

The element of invariant $1/d$ is the local fundamental class. In the unramified cyclic case it is $(L/K,\varphi,\pi_K)$. Its restriction and corestriction compatibilities are precisely those used to construct local reciprocity. Here it also explains why degree two has a single local invariant rather than many independent directions.

### 7.6 Finiteness in low degrees

If $K$ has characteristic zero, $H^i(K,M)$ is finite for every finite $G_K$-module $M$ and every $i$. If $\ell\ne p$, this follows directly from the inertia calculation: invariants, coinvariants, and cohomology of the relevant finite cyclic quotients are finite. For $p$-primary $M$, choose a finite Galois extension $L/K$ acting trivially on $M$ and containing all roots of unity whose orders divide the exponent of $M$. Over $L$, every cyclic composition factor may be identified with a root-of-unity module. Kummer theory gives finite $H^1$, the Brauer calculation gives finite $H^2$, and devissage handles every finite abelian $p$-group. The Hochschild–Serre spectral sequence for $L/K$ has finite group cohomology on its remaining axis and therefore descends finiteness to $K$. Vanishing above degree two completes the argument.

If $K$ has characteristic $p$, the same finiteness holds for modules of order prime to $p$, but not in general for $p$-primary modules. This is the exact boundary needed before defining Euler characteristics.

## 8. The local Euler–Poincaré characteristic

### 8.1 Additive and multiplicative normalizations

Let $M$ be a finite $\ell$-primary $G_K$-module for which all cohomology groups are finite. Define the multiplicative Euler characteristic by

$$
\chi_K^\times(M)
=\prod_{i=0}^2|H^i(K,M)|^{(-1)^i}
=\frac{|H^0(K,M)|\,|H^2(K,M)|}{|H^1(K,M)|}. \tag{8.1}
$$

If $M$ is a finite-length module over the integers $\mathcal O$ of a finite extension of $\mathbf Q_\ell$, with residue field $F$, define

$$
\chi_K(M)
=\sum_{i=0}^2(-1)^i\operatorname{length}_{\mathcal O}H^i(K,M). \tag{8.2}
$$

Then $\chi_K^\times(M)=|F|^{\chi_K(M)}$. The sign is important: $H^1$ occurs in the denominator and with a minus sign.

The theorem is

$$
\chi_K(M)=
\begin{cases}
0,&\ell\ne p,\\
-d_K\operatorname{length}_{\mathcal O}(M),
&\ell=p\text{ and }\operatorname{char}K=0.
\end{cases} \tag{8.3}
$$

Equivalently,

$$
\chi_K^\times(M)=
\begin{cases}
1,&\ell\ne p,\\
|M|^{-d_K},&\ell=p\text{ and }\operatorname{char}K=0,
\end{cases} \tag{8.4}
$$

Indeed, a module of $\mathcal O$-length $r$ has order $|F|^r$, so the two versions are identical
even when the residue degree of the coefficient field is greater than one.

There is no finite-cardinality formula for $p$-primary modules when $\operatorname{char}K=p$; $H^1$ can be infinite. For $\ell\ne p$, formula (8.3) remains valid in either characteristic.

### 8.2 Additivity in exact sequences

Suppose

$$
0\to M'\to M\to M''\to0
$$

is exact and all cohomology groups are finite. The long exact sequence terminates after $H^2$, and the alternating product of the orders in any finite exact sequence is one. Hence

$$
\chi_K(M)=\chi_K(M')+\chi_K(M''). \tag{8.5}
$$

This elementary observation is the main proof engine. It permits devissage by the coefficient-ring length and by composition factors. It also shows why a proof may pass to convenient modules without losing the normalization.

### 8.3 Proof away from the residue characteristic

Let $\ell\ne p$. We prove (8.3) directly from inertia, not by duality. Put

$$
N=M^{I_K},\qquad P=H^1(I_K,M).
$$

The two-row Hochschild–Serre calculation gives

$$
|H^0(K,M)|=|\ker(\varphi-1:N\to N)|,
$$

$$
|H^1(K,M)|=
|\operatorname{coker}(\varphi-1:N\to N)|
\,|\ker(\varphi-1:P\to P)|,
$$

and

$$
|H^2(K,M)|=|\operatorname{coker}(\varphi-1:P\to P)|.
$$

For an endomorphism of a finite group, kernel and cokernel have equal order. Both ratios cancel, giving

$$
\chi_K^\times(M)=1.
$$

This proof works for arbitrary ramified action. It also reveals the mechanism: the Frobenius kernel in one degree is balanced by its cokernel in the next.

### 8.4 The mixed-characteristic calculation for the basic module

Assume $K/\mathbf Q_p$ is finite and put $u=|\mu_p(K)|$, so $u$ is either $1$ or $p$.
Kummer theory, the structure of $K^\times$, and the Brauer calculation give

$$
|H^0(K,\mu_p)|=u,
$$

$$
|H^1(K,\mu_p)|=|K^\times/(K^\times)^p|=p^{d_K+1}u,
$$

$$
|H^2(K,\mu_p)|=p.
$$

The middle equality comes from one valuation direction, $d_K$ deep-unit directions, and the
roots in the kernel of the $p$th-power map. Therefore

$$
\chi_K^\times(\mu_p)=\frac{up}{p^{d_K+1}u}=p^{-d_K}. \tag{8.6}
$$

This calculation neither assumes that $\mu_p\subset K$ nor identifies $\mu_p$ with a constant
module. It explains both the sign and the field-degree factor. The extra $d_K$ dimensions live
in the principal units, not in the unramified quotient.

For the finite-group reduction it is useful to compute the constant module as well, without
using the Euler formula we are trying to prove. Reciprocity and (3.1) give

$$
|H^0(K,\mathbf F_p)|=p,
\qquad
|H^1(K,\mathbf F_p)|=p^{d_K+1}u.
$$

To calculate degree two, put $L=K(\mu_p)$ and $\Delta=\operatorname{Gal}(L/K)$. The order of
$\Delta$ divides $p-1$, so taking $\Delta$-invariants is exact on $p$-groups and
Hochschild--Serre gives

$$
H^2(K,\mathbf F_p)\simeq H^2(L,\mathbf F_p)^\Delta.
$$

A choice of primitive $p$th root identifies $\mathbf F_p$ with $\mu_p$ over $L$, and hence
identifies $H^2(L,\mathbf F_p)$ with the one-dimensional Brauer group
$\operatorname{Br}(L)[p]$. If $\omega:\Delta\to\mathbf F_p^\times$ is the cyclotomic
character, changing the chosen root by $\delta$ multiplies this coefficient identification by
$\omega(\delta)$. Therefore $\Delta$ acts on $H^2(L,\mathbf F_p)$ through
$\omega^{-1}$. Its invariant space has dimension one exactly when $\omega$ is trivial, that is,
exactly when $\mu_p\subset K$. Consequently

$$
|H^2(K,\mathbf F_p)|=u.
$$

We have proved directly that

$$
\chi_K^\times(\mathbf F_p)
=\frac{p\,u}{p^{d_K+1}u}=p^{-d_K}. \tag{8.6a}
$$

The same argument works over every finite extension of $K$, a fact needed in the induction
below.

### 8.5 Proof for every mixed-characteristic finite module

We now explain carefully why the constant calculation determines every finite $p$-primary
module. More generally, for a finite coefficient field $k_0$ of characteristic $p$ and a
finite-dimensional $k_0$-representation $N$, put

$$
e_K(N)=\sum_{i=0}^2(-1)^i\dim_{k_0}H^i(K,N).
$$

This is additive in short exact sequences, is unchanged after extending the finite coefficient
field, and satisfies Shapiro's identity

$$
e_K(\operatorname{Ind}_{G_F}^{G_K}N)=e_F(N) \tag{8.7}
$$

for every finite $F/K$. We shall prove that these properties and (8.6a) force

$$
e_K(N)=-d_K\dim_{k_0}N. \tag{8.7a}
$$

First consider a one-dimensional character $\theta$ of finite order $m$ prime to $p$. After a
finite extension of the coefficient field, all characters of the cyclic group cut out by
$\theta$ are defined. Let $L/K$ be that cyclic extension. For every divisor $a$ of $m$, let
$L_a/K$ be its subextension of degree $a$. The permutation representation decomposes as

$$
\operatorname{Ind}_{G_{L_a}}^{G_K}k_0
=\bigoplus_{\psi^a=1}k_0(\psi).
$$

Shapiro and the already proved trivial calculation over $L_a$ give

$$
\sum_{\psi^a=1}e_K(k_0(\psi))
=e_{L_a}(k_0)=-[L_a:\mathbf Q_p]=-a d_K. \tag{8.7b}
$$

Induction over the divisors of $m$ isolates the sum over characters of exact order $a$.
Automorphisms of the splitting coefficient field act transitively on those characters and do
not change cohomology dimensions. Hence every summand in that exact-order sum has the same Euler
value, and (8.7b) gives

$$
e_K(k_0(\theta))=-d_K. \tag{8.7c}
$$

It remains to pass from lines to an arbitrary modular representation. We record the finite-group
induction fact being used. If $\Gamma$ is finite and the coefficient field splits its
$p$-regular elements, the rational Grothendieck group of finite-dimensional
$k_0[\Gamma]$-modules is spanned by

$$
[\operatorname{Ind}_H^\Gamma\theta],
$$

where $H$ runs through subgroups and $\theta$ through their one-dimensional characters. This is
the modular Brauer induction lemma. A quick proof is to send a module to its Brauer character
on the $p$-regular conjugacy classes. These characters inject the Grothendieck group into the
space of class functions. Induct on the order of the cyclic subgroup generated by a
$p$-regular element: the induced linear characters from its subgroups have a triangular value
matrix, with nonzero diagonal, on the corresponding cyclic-subgroup classes. They therefore
span the class functions over $\mathbf Q$, which proves the stated rational spanning result.

Choose a finite Galois extension through which the action on $N$ factors, with quotient
$\Gamma$. For a term induced from $H\subseteq\Gamma$, let $F$ be the fixed field of $H$.
The character $\theta$ has prime-to-$p$ image, because a finite subgroup of a field's
multiplicative group has order prime to its characteristic. Equations (8.7) and (8.7c), now over
$F$, give

$$
e_K(\operatorname{Ind}_H^\Gamma\theta)
=e_F(\theta)=-d_F=-[\Gamma:H]d_K.
$$

The right side is $-d_K$ times the dimension of the induced representation. Thus the two
additive functions $e_K(-)$ and $-d_K\dim(-)$ agree on a rational spanning set of the
Grothendieck group, and hence agree on $N$. This proves (8.7a) without assuming that $N$ has a
filtration by trivial $G_K$-modules.

For local cohomology, additivity is (8.5), vanishing is Theorem 6.1, and Shapiro's lemma gives

$$
\chi_K(\operatorname{Ind}_{G_L}^{G_K}N)=\chi_L(N).
$$

For a finite $p$-primary abelian module, devissage by the subquotients $p^jM/p^{j+1}M$ gives the
corresponding order formula. For a finite-length module over $\mathcal O$, devissage along powers
of its uniformizer gives (8.3). This proof uses only Kummer theory, the local Brauer invariant,
finite-group induction, Shapiro, and exact sequences; perfect cohomological pairings play no
role.

### 8.6 Dimension and length consequences

Let $F$ be a finite coefficient field of characteristic $\ell$, and set

$$
h^i_K(M)=\dim_F H^i(K,M).
$$

When $\ell\ne p$,

$$
h^1_K(M)=h^0_K(M)+h^2_K(M). \tag{8.8}
$$

When $K/\mathbf Q_p$ is finite and $\ell=p$,

$$
h^1_K(M)=h^0_K(M)+h^2_K(M)+d_K\dim_FM. \tag{8.9}
$$

The analogous formulas hold with $\mathcal O$-length for a finite-length coefficient module. These are often the most useful local dimension formulas because $H^0$ is a centralizer calculation and $H^2$ is the obstruction term to be studied separately.

One must not replace $h^2$ by the dimension of a twisted invariant group in this book. That replacement is a consequence of Tate local duality. Formula (8.9) is valid before that theorem and is one of its principal numerical inputs.

### 8.7 Checks on Kummer modules

Let $n=p^r$ and $K/\mathbf Q_p$ be finite. Put $u=|\mu_n(K)|$. Then

$$
|H^0(K,\mu_n)|=u,
\qquad
|H^1(K,\mu_n)|=n^{d_K+1}u,
\qquad
|H^2(K,\mu_n)|=n.
$$

Thus

$$
\frac{u\cdot n}{n^{d_K+1}u}=n^{-d_K},
$$

as required. For the constant module $C_n$, reciprocity gives $|H^1|=n^{d_K+1}u$, while $|H^0|=n$; the same Euler formula gives $|H^2|=u$, agreeing with the independent descent calculation for $n=p$ in Section 8.4 and then with devissage for general $p$-power exponent.

## 9. Changing the local field

### 9.1 Restriction and corestriction

Let $L/K$ be finite separable, choose compatible separable closures, and regard $G_L$ as an
open subgroup of $G_K$. Restriction is induced by restricting cochains:

$$
\operatorname{res}_{L/K}:H^i(K,M)\to H^i(L,M).
$$

Corestriction is the transfer over right cosets:

$$
\operatorname{cor}_{L/K}:H^i(L,M)\to H^i(K,M).
$$

Their basic relation is

$$
\operatorname{cor}_{L/K}\circ\operatorname{res}_{L/K}
=[L:K]\quad\text{on }H^i(K,M). \tag{9.1}
$$

If $L/K$ is Galois, then in the other order

$$
\operatorname{res}_{L/K}\circ\operatorname{cor}_{L/K}(x)
=\sum_{\sigma\in\operatorname{Gal}(L/K)}\sigma x. \tag{9.2}
$$

These formulas include degree zero: restriction is the inclusion $M^{G_K}\subset M^{G_L}$, while corestriction is the group norm $m\mapsto\sum\sigma m$.

If $[L:K]$ is invertible on an $\ell$-primary coefficient module, (9.1) makes restriction injective and corestriction surjective. Neither conclusion is automatic when $\ell$ divides the degree.

### 9.2 Kummer classes under extension

For $n$ prime to the field characteristic, the Kummer identifications turn restriction into the obvious inclusion

$$
K^\times/(K^\times)^n\longrightarrow L^\times/(L^\times)^n,
$$

and corestriction into the norm

$$
N_{L/K}:L^\times/(L^\times)^n\longrightarrow K^\times/(K^\times)^n. \tag{9.3}
$$

Indeed, if $b^n=a$, the restricted cocycle is the same formula on $G_L$; multiplying its conjugates over cosets gives the Kummer cocycle of $N_{L/K}(a)$. The composite sends $a$ to $a^{[L:K]}$, matching multiplication by the degree in additive cohomological notation.

For Brauer classes, restriction and corestriction obey (7.2) and (7.3). Thus a Kummer class is normed under corestriction while its degree-two invariant is unchanged. The projection formula reconciles these different-looking rules:

$$
\operatorname{cor}(\operatorname{res}x\smile y)=x\smile\operatorname{cor}(y).
$$

### 9.3 Frobenius and unramified classes

Let $f=f(L/K)$ be the residue degree. Arithmetic Frobenius for $L$ maps to $\varphi_K^f$ in the residue quotient of $G_K$. If $M$ is unramified over $K$, restriction on unramified degree-one classes is

$$
\frac{M}{(\varphi-1)M}
\longrightarrow
\frac{M}{(\varphi^f-1)M},
\qquad
m\longmapsto(1+\varphi+\cdots+\varphi^{f-1})m. \tag{9.4}
$$

This is just the cocycle value at $\varphi^f$. Corestriction is characterized by the reverse transfer and by the fact that its composite with (9.4) is multiplication by $[L:K]$; a ramification factor enters corestriction even though the residue quotient sees only $f$.

For ramified $M$, one must replace $M$ by the appropriate inertia invariants. Since $I_L\subseteq I_K$, the space $M^{I_L}$ may be larger than $M^{I_K}$, and new unramified classes can appear after extension. Formula (9.4) is therefore not valid with the old invariant space unless the inertia action is unchanged.

### 9.4 Euler characteristics in extensions

Restriction of a finite module to $G_L$ gives

$$
\chi_L(M)=[L:K]\chi_K(M) \tag{9.5}
$$

in the mixed-characteristic $p$ case, because $[L:\mathbf Q_p]=[L:K]d_K$, and gives zero on both sides for $\ell\ne p$. This scaling is also forced by induction and Shapiro:

$$
\chi_K(\operatorname{Ind}_{G_L}^{G_K}M)=\chi_L(M).
$$

The distinction is worth keeping: restricting a fixed module multiplies the field term, while inducing multiplies the coefficient dimension and then computes over $K$.

### 9.5 A norm and invariant consistency check

Take $x\in H^1(L,\mu_n)=L^\times/(L^\times)^n$ and a character $c\in H^1(K,C_n)$. The projection formula says

$$
\operatorname{inv}_K\bigl(\operatorname{cor}(x\smile\operatorname{res}c)\bigr)
=\operatorname{inv}_K\bigl(N_{L/K}(x)\smile c\bigr).
$$

On the other hand, (7.3) says that taking the invariant after corestriction equals taking the invariant over $L$. This recovers the compatibility between the norm map and restriction of characters in local reciprocity. It is a useful test of all four directions: field extension, Galois subgroup, norm, and cohomological transfer.

## 10. Lattices, limits, and $\ell$-adic representations

### 10.1 Passing from finite levels

Let $\mathcal O$ be the integers of a finite extension $E/\mathbf Q_\ell$, with uniformizer $\varpi$, and let $T$ be a finite free $\mathcal O$-module with continuous $G_K$-action. Its topology and action are recovered from

$$
T\simeq\varprojlim_nT/\varpi^nT.
$$

There is a Milnor exact sequence

$$
0\to\varprojlim{}^1_nH^{i-1}(K,T/\varpi^nT)
\to H^i(K,T)
\to\varprojlim_nH^i(K,T/\varpi^nT)\to0. \tag{10.1}
$$

When the finite-level cohomology groups are finite, their images in any fixed level stabilize, so the systems are Mittag–Leffler and the $\varprojlim^1$ term vanishes. Therefore, if $K$ has characteristic zero, or if $\ell\ne p$ in equal characteristic,

$$
H^i(K,T)\simeq\varprojlim_nH^i(K,T/\varpi^nT). \tag{10.2}
$$

These groups are finitely generated $\mathcal O$-modules for $i=0,1,2$ and vanish for $i>2$. Finite generation follows by choosing finitely many generators modulo $\varpi$, lifting compatibly, and applying the topological Nakayama argument. The hypotheses matter: equal-characteristic $p$-primary finite levels need not be finite, so this proof does not apply.

More explicitly, the coefficient sequence

$$
0\longrightarrow T\xrightarrow{\varpi}T\longrightarrow T/\varpi T\longrightarrow0
$$

shows that $H^i(K,T)/\varpi$ injects into the finite group $H^i(K,T/\varpi T)$.
The inverse-limit description makes $H^i(K,T)$ separated and complete for its
$\varpi$-adic topology. Choose lifts of a finite generating set of the quotient modulo
$\varpi$. Successively subtracting their $\mathcal O$-linear combinations pushes any class
into $\varpi^nH^i$ for every $n$; completeness sums the coefficients and separatedness makes
the remaining class zero. This proves finite generation rather than merely finite generation of
each finite quotient.

### 10.2 Vector spaces and stable lattices

Put $V=T\otimes_{\mathcal O}E$. Under the same standard local-field hypotheses,

$$
H^i(K,V)\simeq H^i(K,T)\otimes_{\mathcal O}E. \tag{10.3}
$$

To prove this, first observe that continuous cochains into $V$ have compact image and hence land in $\varpi^{-r}T$ for some $r$; thus the cochain complex for $V$ is the filtered union of those for $\varpi^{-r}T$. Flatness of $E$ and finite generation then commute cohomology with localization. A different stable lattice is commensurable with $T$, and finite-index changes disappear after tensoring with $E$, so $H^i(K,V)$ is independent of the lattice.

For $A=V/T$, the exact sequence

$$
0\to T\to V\to A\to0
$$

relates compact, vector-space, and discrete torsion cohomology. Continuous local sections of $V\to A$ over compact subsets, or equivalently passage through finite levels, gives the long exact sequence in this setting. It is often used to compare the corank of $H^i(K,A)$ with the rank of $H^i(K,T)$.

### 10.3 Euler characteristic for vector spaces

Write $h^i_K(V)=\dim_EH^i(K,V)$. Taking the leading linear term of the finite-level length formula gives

$$
\sum_{i=0}^2(-1)^ih^i_K(V)=
\begin{cases}
0,&\ell\ne p,\\
-d_K\dim_EV,&\ell=p\text{ and }K/\mathbf Q_p\text{ finite}.
\end{cases} \tag{10.4}
$$

Here is why no hidden torsion term survives. The long exact sequence for multiplication by
$\varpi^n$ on $T$ gives

$$
0\longrightarrow H^i(K,T)/\varpi^n
\longrightarrow H^i(K,T/\varpi^nT)
\longrightarrow H^{i+1}(K,T)[\varpi^n]
\longrightarrow0.
$$

If $H^i(K,T)$ has rank $r_i$, the first term has length $nr_i+O(1)$, while the last term has
bounded length because the torsion subgroup of a finitely generated $\mathcal O$-module is
finite. Divide the finite-level Euler identity by $n$ and let $n$ tend to infinity. The bounded
terms vanish, and $r_i=\dim_EH^i(K,V)$ by (10.3). This proves (10.4).

Thus

$$
h^1_K(V)=
\begin{cases}
h^0_K(V)+h^2_K(V),&\ell\ne p,\\
h^0_K(V)+h^2_K(V)+d_K\dim_EV,&\ell=p.
\end{cases} \tag{10.5}
$$

This formula is invariant under extension of the coefficient field. It is also insensitive to torsion in the chosen lattice, because only $E$-dimensions remain.

### 10.4 Unramified $\ell$-adic cohomology

Define

$$
H^1_{\mathrm{ur}}(K,V)=
\ker\bigl(H^1(K,V)\to H^1(I_K,V)\bigr).
$$

When the action on inertia has finite image—as happens for an unramified representation and more generally for many finite-image examples—inflation–restriction gives

$$
H^1_{\mathrm{ur}}(K,V)\simeq
V^{I_K}/(\varphi-1)V^{I_K}. \tag{10.6}
$$

The formula also holds whenever continuous cohomology of the procyclic quotient is computed by the two-term complex on $V^{I_K}$. In finite dimension,

$$
\dim_EH^1_{\mathrm{ur}}(K,V)
=\dim_EH^0(K,V), \tag{10.7}
$$

because kernel and cokernel of $\varphi-1$ have equal dimension.

At the lattice level the quotient $T^{I_K}/(\varphi-1)T^{I_K}$ can have torsion even when the vector-space dimension is zero. For example, an unramified rank-one lattice with Frobenius eigenvalue $\alpha\ne1$ has

$$
H^1_{\mathrm{ur}}(K,T)=\mathcal O/(\alpha-1)
$$

when $T^{I_K}=T$. This finite congruence group disappears after tensoring with $E$ unless $\alpha=1$.

### 10.5 One-dimensional $\ell$-adic calculations away from $p$

Let $V=E(\chi)$ with $\ell\ne p$. If $\chi$ has nontrivial finite inertia image, then
$H^i(K,V)=0$ in every degree. Indeed, a prime-to-$\ell$ part is removed by averaging. If the
nontrivial part has $\ell$-power order, it lies on the $\mathbf Z_\ell$ tame direction; a tame
generator acts by a root of unity $\zeta\ne1$, and $\zeta-1$ is a nonzero, hence invertible,
scalar in the field $E$. The two-term inertia complex is therefore acyclic. If $\chi$ is
unramified and $\alpha=\chi(\varphi)$, then

$$
h^0=[\alpha=1],
\qquad
h^1=[\alpha=1]+[\alpha=q],
\qquad
h^2=[\alpha=q]. \tag{10.8}
$$

The equality $\alpha=q$ means that $V$ is the unramified cyclotomic line $E(1)$; it is the unique unramified rank-one situation contributing the tame obstruction direction. A character with infinite inertia image requires direct analysis of its inertia cohomology; finite-image averaging no longer applies.

### 10.6 Two basic $p$-adic lines

The trivial and cyclotomic lines show concretely where the $p$-adic bulk in the Euler formula
lives. Assume $K/\mathbf Q_p$ is finite and let $E/\mathbf Q_p$ be a finite coefficient field.
For the trivial line $E$, continuous reciprocity gives

$$
H^1(K,E)=\operatorname{Hom}_{\mathrm{cts}}(K^\times,E).
$$

The valuation factor $\mathbf Z$ supplies one dimension, the finite roots of unity supply none,
and a sufficiently deep principal-unit group is isomorphic to the additive group of
$\mathcal O_K$, which supplies $d_K$ dimensions. Hence

$$
h^0(K,E)=1,\qquad h^1(K,E)=d_K+1.
$$

The Euler formula forces $h^2(K,E)=0$. Thus the trivial $p$-adic line has dimensions

$$
(h^0,h^1,h^2)=(1,d_K+1,0). \tag{10.9}
$$

For the cyclotomic line $E(1)$, inverse-limit Kummer theory identifies

$$
H^1(K,E(1))\simeq
\left(\varprojlim_nK^\times/(K^\times)^{p^n}\right)\otimes_{\mathbf Z_p}E.
$$

The pro-$p$ completion of $K^\times$ has one valuation direction and $d_K$ principal-unit
directions; finite torsion disappears after tensoring with $E$. Therefore $h^1=d_K+1$ again.
There is no nonzero compatible system of $p$-power roots of unity inside a fixed finite extension
$K/\mathbf Q_p$, so $H^0(K,E(1))=0$. The Euler formula now gives $h^2=1$:

$$
(h^0,h^1,h^2)=(0,d_K+1,1). \tag{10.10}
$$

The identical middle dimensions conceal different arithmetic. On the trivial line the valuation
character coexists with fixed vectors; on the cyclotomic line a Brauer direction replaces those
fixed vectors in degree two. No perfect pairing was used: the computation follows from
reciprocity, Kummer theory, and Euler--Poincare.

### 10.7 Finiteness and its limits

For $K/\mathbf Q_p$ finite and any finite-dimensional $E$-representation $V$, the groups $H^i(K,V)$ are finite-dimensional and vanish above degree two. The same holds in equal characteristic when $\ell\ne p$. For $T$, the groups are finitely generated over $\mathcal O$.

In equal characteristic with $\ell=p$, neither the standard $p$-adic Tate twist nor the blanket finiteness theorem is available. One may study continuous $p$-adic representations by other methods, but the finite-module theory already shows that no analogue of (10.4) can be asserted without additional restrictive hypotheses.

### 10.8 Discrete divisible quotients

Many arithmetic representations are presented not by a lattice $T$ or a vector space $V$ but
by the discrete quotient

$$
A=V/T\simeq(E/\mathcal O)^d.
$$

This coefficient is neither finite nor compact, yet it is assembled from finite coefficients:
$A[\varpi^n]\simeq T/\varpi^nT$. The multiplication sequence

$$
0\longrightarrow T/\varpi^nT\longrightarrow A
\xrightarrow{\varpi^n}A\longrightarrow0
$$

is exact as a sequence of discrete $G_K$-modules. Its long exact sequence gives, for every
$i\geq0$,

$$
0\longrightarrow H^{i-1}(K,A)/\varpi^n
\longrightarrow H^i(K,T/\varpi^nT)
\longrightarrow H^i(K,A)[\varpi^n]
\longrightarrow0, \tag{10.11}
$$

where the first term is omitted for $i=0$. Formula (10.11) is often the safest way to pass
between a torsion representation and its finite layers: it records both torsion in the previous
degree and $\varpi^n$-torsion in the current degree.

Under the finiteness hypotheses of Section 10.1, the middle group is finite, so every
$H^i(K,A)[\varpi^n]$ is finite. Moreover $H^i(K,A)=0$ for $i>2$. To see the latter assertion,
write $A$ as the filtered union of its finite submodules $A[\varpi^n]$ and use the finite-module
vanishing theorem together with commutation of continuous cohomology with filtered unions of
discrete torsion modules. The low-degree groups are cofinitely generated over $\mathcal O$:
(10.11), finite generation of $H^i(K,T)$, and the long exact sequence of
$0\to T\to V\to A\to0$ reduce the assertion to the structure theorem for finitely generated
$\mathcal O$-modules.

There is a useful warning in degree zero. Although $H^0(K,A)=A^{G_K}$, it need not equal
$H^0(K,V)/H^0(K,T)$: the next boundary map can contribute torsion coming from $H^1(K,T)$.
Similarly, corank formulas for $A$ must be read from the long exact sequence, not obtained by
blindly replacing dimensions of $V$ with coranks. The finite-level exact sequence (10.11) keeps
that boundary visible.

## 11. Ramification-shaped local classes

### 11.1 Why cohomology needs local subspaces

The full group $H^1(K,M)$ classifies all extensions or torsors with coefficient $M$. Arithmetic problems rarely allow all of them. One may require a class to be unramified, tamely ramified, or to arise from an integral object over $\mathcal O_K$. Each requirement defines, when it behaves well, a subgroup of $H^1$. Later deformation theory turns such subgroups into tangent spaces.

This book calculates only conditions already justified by the preceding arithmetic and finite-flat theory. In particular, we define the unramified subgroup exactly and describe tame restriction. We may identify Kummer classes represented by units and note when an extension of finite Galois modules has an integral finite-flat model. We do not assert a general classification of finite-flat extension classes or a dimension theorem for them; those require the local deformation conditions developed later.

### 11.2 The unramified subgroup as an extension condition

An element of $H^1(K,\operatorname{Hom}(W_2,W_1))$ classifies extensions

$$
0\to W_1\to W\to W_2\to0
$$

when the underlying coefficient sequence is split. The class is unramified exactly when the extension splits as an $I_K$-module. Notice the wording: $W$ itself need not have trivial inertia if $W_1$ and $W_2$ do not. The condition says that no new extension data appear on inertia.

If both $W_1$ and $W_2$ are unramified, choose an inertia-equivariant splitting. The remaining failure of Frobenius equivariance is a map

$$
u:W_2\to W_1,
$$

well defined modulo

$$
u\sim u+\varphi_1x-x\varphi_2.
$$

This is exactly the cokernel formula

$$
H^1_{\mathrm{ur}}(K,\operatorname{Hom}(W_2,W_1))
=\operatorname{coker}\bigl(x\mapsto\varphi_1x\varphi_2^{-1}-x\bigr).
$$

Thus an unramified extension is measured by a failure to conjugate one Frobenius block into a split block form.

### 11.3 Tame classes

For an $\ell$-primary module with $\ell\ne p$, define

$$
H^1_{\mathrm{tame}}(K,M)
=\ker\bigl(H^1(K,M)\to H^1(P_K,M)\bigr).
$$

Since higher $P_K$-cohomology vanishes, inflation identifies this with cohomology of $G_K/P_K$ acting on $M^{P_K}$. It contains the unramified subgroup.

In fact $H^1(P_K,M)=0$ for $\ell\ne p$, so every class in $H^1(K,M)$ is tame in this
cohomological sense. This does not say that wild inertia acts trivially on $M$; it says that the
restriction of an extension class to the pro-$p$ group can be killed by changing its splitting.
The distinction between the action on the coefficient and the ramification of the class is the
same distinction already encountered for unramified cohomology.

The quotient by the unramified subgroup is controlled by the tame generator:

$$
H^1_{\mathrm{tame}}(K,M)/H^1_{\mathrm{ur}}(K,M)
\hookrightarrow H^1(I_K,M)^{\varphi=1}.
$$

Under the exact sequence (4.1), this arrow is an isomorphism onto the Frobenius-invariant tame term. When inertia acts trivially,

$$
H^1_{\mathrm{tame}}/H^1_{\mathrm{ur}}\simeq M(-1)^{\varphi=1}. \tag{11.1}
$$

A nonzero element exists precisely when Frobenius on $M$ has eigenvalue $q$ in the semisimple one-dimensional case. The relation $\varphi\tau\varphi^{-1}=\tau^q$ forces this eigenvalue; it is not an arbitrary convention.

### 11.4 A tame upper-triangular example

Let $F$ have characteristic $\ell\ne p$, and consider

$$
\rho(g)=
\begin{pmatrix}
1&c(g)\bar\chi_\ell(g)\\
0&\bar\chi_\ell(g)
\end{pmatrix},
$$

where $\bar\chi_\ell$ is the mod-$\ell$ cyclotomic character. With this normalization the
upper-right block represents a class in

$$
H^1(K,F(\bar\chi_\ell^{-1})).
$$

With arithmetic Frobenius, the coefficient eigenvalue is $q^{-1}$. Formula (5.2) says that an unramified line occurs if $q^{-1}=1$ in $F$, while a tame line occurs if $q^{-1}=q$, namely $q^2=1$. If instead the extension is written with cyclotomic character in the upper-left and the trivial character below, the coefficient is $F(\bar\chi_\ell)$ and the tame line always occurs through the equality $\alpha=q$. The placement of the characters changes the twist, so visually similar triangular matrices can have different tangent dimensions.

### 11.5 Kummer classes and valuation conditions

For $n$ prime to $\operatorname{char}K$, Kummer theory identifies $H^1(K,\mu_n)$ with
$K^\times/(K^\times)^n$. A tempting but false analogy with constant characters says that the
unramified subgroup should be generated by a uniformizer. Adjoining an $n$th root of $\pi_K$ is
usually ramified: the analogy has confused $\mu_n$ with $\mathbf Z/n\mathbf Z$.

An “unramified class” is a torsor class restricting trivially to inertia, and $\mu_n$ itself
carries a Frobenius action. From (4.3),

$$
H^1_{\mathrm{ur}}(K,\mu_n)\simeq
\mu_n/(\varphi-1)\mu_n,
$$

whose order is $\gcd(n,q-1)$. Under Kummer theory this subgroup is represented by **unit** classes whose residue is compatible with the unramified extension, not in general by $\pi_K$. The class of $\pi_K$ cuts out a totally ramified radical extension when $\mu_n\subset K$.

For $(n,p)=1$ this description can be made exact. The power map is an automorphism of $U^1$,
so reduction gives

$$
\mathcal O_K^\times/(\mathcal O_K^\times)^n
\simeq k^\times/(k^\times)^n,
$$

a group of order $\gcd(n,q-1)$. Every unit becomes an $n$th power over $K^{\mathrm{nr}}$:
its residue acquires an $n$th root in $\overline k$, and Hensel's lemma lifts that root. Hence
the unit quotient lies in $H^1_{\mathrm{ur}}$. Equality of orders proves

$$
H^1_{\mathrm{ur}}(K,\mu_n)
=\mathcal O_K^\times(K^\times)^n/(K^\times)^n.
$$

By contrast, the valuation of an $n$th power in $K^{\mathrm{nr}}$ is still divisible by $n$,
so the uniformizer class cannot become trivial on inertia.

For constant coefficients $C_n$, by contrast, the valuation character

$$
K^\times\xrightarrow{v_K}\mathbf Z\to C_n
$$

is the canonical unramified class and has order $n$. This comparison is an important counterexample to conflating $C_n$ with $\mu_n$ when roots of unity are not fixed.

### 11.6 The unit filtration inside Kummer cohomology

The images

$$
\frac{U^a(K^\times)^n}{(K^\times)^n}
\subseteq H^1(K,\mu_n)
$$

filter Kummer classes by depth. For $(n,p)=1$, the $n$th-power map is an automorphism of $U^1$, so only valuation and residue-unit information survive. Hence there are no wild Kummer classes of prime-to-$p$ exponent.

When $K/\mathbf Q_p$ and $n=p^r$, principal units contribute the $p^{rd_K}$ factor in (3.1). The filtration quotients $U^a/U^{a+1}$ are additive copies of $k$, and the $p$th-power map shifts depth in a way controlled by ramification. This explains the abundance of mixed-characteristic $p$-primary classes. A precise classification by depth depends on the ramification index and roots of unity; the Euler formula needs only the total index and deliberately avoids pretending that all fields have the same layer-by-layer behavior.

### 11.7 Finite-flat-shaped classes

Suppose $K/\mathbf Q_p$ and a finite $p$-primary $G_K$-module $M$ is the generic fiber of a finite flat commutative group scheme over $\mathcal O_K$. An extension of such group schemes whose generic-fiber coefficient sequence is split—for example, an extension of finite-dimensional vector-space representations—gives, after choosing a coefficient splitting, a class in $H^1(K,\operatorname{Hom}(M_2,M_1))$. Changing the splitting changes the cocycle by a coboundary. Without an underlying coefficient splitting, the generic fiber belongs to an $\operatorname{Ext}^1$ group and need not be encoded by this $H^1$ alone. We call a class obtained in the split setting **finite-flat-shaped** only as a reminder of its origin; the intrinsic local condition is the image of the relevant extension group of integral models.

Two cautions are essential. First, a generic-fiber module can have more than one finite flat model, so the image may depend on the chosen integral data unless a uniqueness theorem applies. Second, not every Galois extension class between finite-flat generic fibers extends over $\mathcal O_K$. Cohomological dimension and Euler characteristic calculate the ambient $H^1$, not this integral subspace.

The basic Kummer examples illustrate the boundary. In mixed characteristic the group schemes $\mu_{p^r}$ and the constant étale group $\mathbf Z/p^r\mathbf Z$ have very different special fibers, even when their generic fibers become isomorphic after adjoining roots of unity. Unit Kummer classes often admit integral interpretations, while a valuation class may encode a ramified generic torsor that does not extend in the same finite-flat category. No blanket equality between “unit,” “finite flat,” and “unramified” is valid.

### 11.8 Stability properties available now

The constructions already established imply safe closure statements. Unramified classes form a subgroup, are functorial in coefficients, and are preserved by unramified base change. Tame classes form a subgroup for $\ell\ne p$ and are preserved under arbitrary restriction, though ramification indices change the tame generator. Generic fibers of extensions, subobjects, quotients, and duals of finite flat group schemes retain the corresponding shapes whenever the integral operation exists in the finite-flat category.

Stronger claims—representability of a local deformation condition, formal smoothness, or a formula for its tangent dimension—do not follow from these observations. The present calculations provide the ambient spaces against which those later local conditions will be measured.

## 12. Adjoint modules and tangent calculations

### 12.1 Why conjugation is the coefficient action

Let $F$ be a finite field of characteristic $\ell$, and let

$$
\bar\rho:G_K\to\operatorname{GL}(W)
$$

be a continuous representation on a $d$-dimensional $F$-space. A first-order perturbation has the form

$$
\rho_\varepsilon(g)=(1+\varepsilon c(g))\bar\rho(g),
\qquad \varepsilon^2=0.
$$

Multiplicativity is equivalent to

$$
c(gh)=c(g)+\bar\rho(g)c(h)\bar\rho(g)^{-1}.
$$

Thus $c$ is a cocycle with values in

$$
\operatorname{ad}\bar\rho=\operatorname{End}_F(W),
$$

where $G_K$ acts by conjugation. Conjugating the lift by $1+\varepsilon X$ changes $c$ by a coboundary. Therefore the unframed first-order tangent space is $H^1(K,\operatorname{ad}\bar\rho)$, subject to any imposed local subspace.

### 12.2 Invariants and the centralizer

Degree zero is

$$
H^0(K,\operatorname{ad}\bar\rho)
=\operatorname{End}_{G_K}(W). \tag{12.1}
$$

If $W$ is absolutely irreducible, Schur's lemma gives

$$
h^0_K(\operatorname{ad}\bar\rho)=1.
$$

Absolute irreducibility matters. A representation irreducible over $F$ can acquire extra endomorphisms after extending scalars, and a reducible nonsplit representation can have a centralizer larger or smaller than a naive count of diagonal blocks suggests.

For example, if $\bar\rho=\chi_1\oplus\chi_2$ with distinct characters, the diagonal endomorphisms are fixed, so $h^0=2$. If $\chi_1=\chi_2$, every matrix is fixed and $h^0=4$. If the representation is a nonsplit extension of a character by itself, its centralizer is the two-dimensional algebra generated by the identity and the nilpotent extension operator.

### 12.3 Ambient tangent dimensions

Since $\dim_F\operatorname{ad}\bar\rho=d^2$, the Euler formulas give

$$
h^1_K(\operatorname{ad}\bar\rho)=
h^0_K(\operatorname{ad}\bar\rho)+h^2_K(\operatorname{ad}\bar\rho)
\quad(\ell\ne p), \tag{12.2}
$$

and, when $K/\mathbf Q_p$ and $\ell=p$,

$$
h^1_K(\operatorname{ad}\bar\rho)=
h^0_K(\operatorname{ad}\bar\rho)+h^2_K(\operatorname{ad}\bar\rho)
+d_Kd^2. \tag{12.3}
$$

For an absolutely irreducible two-dimensional representation over $K=\mathbf Q_p$, this becomes

$$
h^1=5+h^2.
$$

The number five is one scalar automorphism plus four principal-unit directions. The unknown $h^2$ is a genuine obstruction contribution; it cannot be discarded without a separate vanishing argument.

### 12.4 Fixed determinant and trace zero

The derivative of determinant at the identity is trace. Hence a fixed-determinant first-order deformation has cocycle values in

$$
\operatorname{ad}^0\bar\rho
=\{X\in\operatorname{End}_F(W):\operatorname{tr}X=0\}.
$$

If $\ell\nmid d$, then

$$
\operatorname{ad}\bar\rho
=F\cdot I\oplus\operatorname{ad}^0\bar\rho. \tag{12.4}
$$

For absolutely irreducible $W$, this gives $H^0(K,\operatorname{ad}^0\bar\rho)=0$. If $\ell\mid d$, the identity matrix has trace zero, the splitting (12.4) fails, and scalar infinitesimal automorphisms remain inside $\operatorname{ad}^0$. Any formula subtracting one from $h^0$ without the hypothesis $\ell\nmid d$ is wrong.

When $\ell\ne p$ and $\ell\nmid d$,

$$
h^1_K(\operatorname{ad}^0\bar\rho)
=h^0_K(\operatorname{ad}^0\bar\rho)
+h^2_K(\operatorname{ad}^0\bar\rho). \tag{12.5}
$$

When $K/\mathbf Q_p$, $\ell=p$, and $\ell\nmid d$,

$$
h^1_K(\operatorname{ad}^0\bar\rho)
=h^0_K(\operatorname{ad}^0\bar\rho)
+h^2_K(\operatorname{ad}^0\bar\rho)
+d_K(d^2-1). \tag{12.6}
$$

For an absolutely irreducible two-dimensional representation with $p\ne2$, this is

$$
h^1_K(\operatorname{ad}^0\bar\rho)=h^2_K(\operatorname{ad}^0\bar\rho)+3d_K.
$$

### 12.5 Framed versus unframed first-order parameters

Before quotienting by infinitesimal conjugacy, cocycles form $Z^1(K,\operatorname{ad}\bar\rho)$. Coboundaries have dimension

$$
\dim_F B^1=d^2-h^0_K(\operatorname{ad}\bar\rho),
$$

because the kernel of $X\mapsto(g\mapsto gX-X)$ is the centralizer. Therefore

$$
\dim_F Z^1
=h^1_K(\operatorname{ad}\bar\rho)+d^2-h^0_K(\operatorname{ad}\bar\rho). \tag{12.7}
$$

This is the framed tangent dimension. In mixed coefficient characteristic $p$, inserting (12.3) gives

$$
\dim_F Z^1=h^2_K(\operatorname{ad}\bar\rho)+(d_K+1)d^2. \tag{12.8}
$$

The centralizer cancels. This cancellation explains why framed deformation problems often have cleaner numerical dimensions even when the residual representation has extra automorphisms.

### 12.6 The unramified tangent space

The tangent space to the unramified condition is

$$
H^1_{\mathrm{ur}}(K,\operatorname{ad}\bar\rho)
=\operatorname{coker}\bigl(\varphi-1:(\operatorname{ad}\bar\rho)^{I_K}\to
(\operatorname{ad}\bar\rho)^{I_K}\bigr).
$$

Consequently

$$
\dim_FH^1_{\mathrm{ur}}(K,\operatorname{ad}\bar\rho)
=h^0_K(\operatorname{ad}\bar\rho). \tag{12.9}
$$

For an absolutely irreducible representation this dimension is one, not because the whole representation is unramified, but because the Frobenius-fixed inertia centralizer equals the full Galois centralizer. With fixed determinant and $\ell\nmid d$, the analogous dimension is

$$
\dim_FH^1_{\mathrm{ur}}(K,\operatorname{ad}^0\bar\rho)
=h^0_K(\operatorname{ad}^0\bar\rho).
$$

Thus it is zero for an absolutely irreducible representation. This is an ambient tangent calculation; whether the corresponding deformation functor is formally smooth requires an obstruction analysis.

### 12.7 A split two-character calculation

Let $\bar\rho=\chi_1\oplus\chi_2$. Then

$$
\operatorname{ad}\bar\rho
\simeq F\oplus F\oplus F(\chi_1\chi_2^{-1})
\oplus F(\chi_2\chi_1^{-1}). \tag{12.10}
$$

The two trivial summands are diagonal; the other two are the upper-right and lower-left extension directions. When $\ell\ne p$ and all characters are unramified, formulas (5.1)–(5.3) compute each summand. If $\alpha=\chi_1(\varphi)\chi_2(\varphi)^{-1}$, then the upper-right term contributes to $H^0$ when $\alpha=1$ and to $H^2$ when $\alpha=q$; the lower-left term uses $\alpha^{-1}$. Coincidences $\alpha=1,q,q^{-1}$ create jumps in tangent dimension.

For a generic ratio different from $1,q,q^{-1}$, the off-diagonal groups vanish and each trivial diagonal line has dimensions $(1,1+[q=1], [q=1])$. This example shows why tangent dimensions are locally constant only away from special Frobenius eigenvalue ratios.

### 12.8 Obstructions stop in degree two

A first-order class lies in $H^1$; attempting to lift it across a small extension produces a $2$-cocycle in the adjoint module. The vanishing theorem ensures there are no higher local cohomology groups for finite torsion coefficients beyond degree two. This does not mean that every obstruction vanishes: $H^2$ may be nonzero, as the cyclotomic examples show. It means that local obstruction theory has one final cohomological stage.

Book 31 will relate this obstruction space to twisted invariants through a perfect pairing. Everything required to formulate that pairing is now present: the Tate dual, cup product, $H^2(K,\mu_n)$, the invariant map, finiteness, and restriction/corestriction compatibility.

### 12.9 Tangent and relation ledgers

The Euler formula becomes most useful in deformation theory when it is rearranged as a balance
between parameters and possible relations. Let $M$ be a finite-dimensional $F$-representation
and put

$$
\epsilon_K(M)=
\begin{cases}
0,&\ell\ne p,\\
d_K\dim_FM,&\ell=p\text{ and }K/\mathbf Q_p\text{ is finite}.
\end{cases}
$$

Then

$$
h^1(K,M)-h^2(K,M)=h^0(K,M)+\epsilon_K(M). \tag{12.11}
$$

For $M=\operatorname{ad}\bar\rho$, $h^1$ counts unframed ambient tangent directions and
$h^2$ is the canonical receptacle for lifting obstructions. Thus the number of tangent
directions left after subtracting the largest cohomologically visible relation count is not
mysterious: it is the centralizer dimension, plus the $p$-adic bulk when the coefficient prime
is the residue prime. For framed deformations, (12.7) gives

$$
\dim_F Z^1(K,\operatorname{ad}\bar\rho)-h^2(K,\operatorname{ad}\bar\rho)
=d^2+\epsilon_K(\operatorname{ad}\bar\rho). \tag{12.12}
$$

The centralizer has disappeared because framing restores the directions lost to conjugation.
For a two-dimensional representation at a $p$-adic place, (12.12) is
$4+4d_K$; with fixed determinant and $p\ne2$, its trace-zero analogue is
$3+3d_K$.

Now let $L_K\subseteq H^1(K,M)$ be a linear local condition, such as the unramified subgroup or
a tangent space obtained from specified integral models. Its **local tangent deficit** is

$$
c_K(L_K)=h^1(K,M)-\dim_FL_K. \tag{12.13}
$$

This is the number of ambient first-order directions excluded by the condition. Combining
(12.11) and (12.13) gives the identity

$$
\dim_FL_K-h^0(K,M)
=h^2(K,M)+\epsilon_K(M)-c_K(L_K). \tag{12.14}
$$

Every term here has already been defined and computed or bounded in this book. Formula (12.14)
is therefore safe even for a hardly ramified condition specified only by a small subspace of
$H^1$: one inserts its actual dimension rather than assuming formal smoothness. In particular,
for the unramified condition,
$\dim H^1_{\mathrm{ur}}=h^0$, so its left side is zero and

$$
c_K(H^1_{\mathrm{ur}})=h^2(K,M)+\epsilon_K(M). \tag{12.15}
$$

Away from $p$, an unramified condition removes exactly the degree-two contribution; at a
$p$-adic coefficient place it additionally removes the $d_K\dim M$ principal-unit directions.
This is the numerical mechanism behind local relation ledgers in minimally or hardly ramified
deformation problems.

These identities do not claim that every element of $H^2$ occurs as an independent equation,
nor that a chosen local condition is representable. Cohomology provides a canonical obstruction
space and hence a bound; equality with a minimal number of defining relations requires a
separate deformation-theoretic argument. Keeping “possible relations” distinct from “actual
minimal relations” prevents a common circular dimension count.

## 13. A reusable local formula collection

### 13.1 The calculation protocol

For a finite $\ell$-primary module $M$, the following order minimizes hidden assumptions.

1. Record $p=\operatorname{char}k$, $q=|k|$, the characteristic of $K$, and whether $\ell=p$.
2. Compute $M^{I_K}$ and the arithmetic Frobenius action on it.
3. Use
   $$
   H^0(K,M)=\ker(\varphi-1\mid M^{I_K})
   $$
   and
   $$
   H^1_{\mathrm{ur}}(K,M)=\operatorname{coker}(\varphi-1\mid M^{I_K}).
   $$
4. If $\ell\ne p$, compute $H^1(I_K,M)$ from tame inertia; then (4.1) gives $H^1$ and (4.8) gives $H^2$.
5. If $\ell=p$ in mixed characteristic, use Kummer theory, reciprocity, exact sequences, or a specific integral description; use Euler–Poincaré to determine the remaining length, not its internal structure.
6. If $\ell=p=\operatorname{char}K$, expect $H^1$ to be infinite and use Artin–Schreier–Witt methods rather than a finite Euler characteristic.

This protocol separates group-theoretic input from arithmetic input and makes every Frobenius convention visible.

### 13.2 Vanishing and finiteness table

For a nonarchimedean local field $K$ with residue characteristic $p$:

| coefficients | cohomological dimension | low-degree finiteness |
|---|---:|---|
| finite $\ell$-primary, $\ell\ne p$ | $2$ | finite in degrees $0,1,2$ |
| finite $p$-primary, $K/\mathbf Q_p$ | $2$ | finite in degrees $0,1,2$ |
| finite $p$-primary, $\operatorname{char}K=p$ | $1$ | $H^1$ can be infinite |

In every row $H^i=0$ for $i>2$; in the last row it already vanishes for $i>1$. For lattices and vector spaces, inverse-limit finiteness follows in the first two rows but not automatically in the last.

For an $r$-dimensional finite-field module away from $p$, the uniform bounds are
$h^0,h^2\leq r$ and $h^1\leq2r$. At $p$ in mixed characteristic, the exact replacement is
$h^1=h^0+h^2+d_Kr$.

### 13.3 Euler dimension formulas

For a finite-dimensional $F$-module $M$ of characteristic $\ell$ with finite cohomology:

$$
h^1=
\begin{cases}
h^0+h^2,&\ell\ne p,\\
h^0+h^2+d_K\dim_FM,&\ell=p, K/\mathbf Q_p.
\end{cases} \tag{13.1}
$$

For a finite-dimensional $E$-representation $V$, the same formula holds with $E$-dimensions. For a finite-length $\mathcal O$-module, replace dimensions by lengths. The sign-equivalent form is

$$
h^0-h^1+h^2=
\begin{cases}
0,&\ell\ne p,\\
-d_K\dim M,&\ell=p.
\end{cases}
$$

No duality theorem is needed for these identities.

### 13.4 Prime-to-$p$ unramified line

For $M=F(\chi)$, $\ell\ne p$, with unramified Frobenius eigenvalue $\alpha$:

| condition | $h^0$ | $h^1$ | $h^2$ |
|---|---:|---:|---:|
| $\alpha\ne1,q$ | $0$ | $0$ | $0$ |
| $\alpha=1\ne q$ | $1$ | $1$ | $0$ |
| $\alpha=q\ne1$ | $0$ | $1$ | $1$ |
| $\alpha=1=q$ | $1$ | $2$ | $1$ |

A nontrivially ramified one-dimensional $F$-character has zero cohomology in all degrees. The table uses arithmetic Frobenius and therefore the obstruction eigenvalue is $q$.

### 13.5 Kummer and constant cyclic formulas

If $(n,p)=1$, put $g=\gcd(n,q-1)$. Then

$$
\begin{array}{c|ccc}
M&|H^0|&|H^1|&|H^2|\\ \hline
\mu_n&g&ng&n\\
\mathbf Z/n\mathbf Z&n&ng&g
\end{array} \tag{13.2}
$$

For $K/\mathbf Q_p$ and $n=p^r$, put $u=|\mu_n(K)|$. Then

$$
\begin{array}{c|ccc}
M&|H^0|&|H^1|&|H^2|\\ \hline
\mu_n&u&n^{d_K+1}u&n\\
\mathbf Z/n\mathbf Z&n&n^{d_K+1}u&u
\end{array}. \tag{13.3}
$$

For general $n=p^rm$ with $(m,p)=1$, combine the primary parts. Formula (13.2) is also valid in equal characteristic because it excludes $p$.

### 13.6 Restriction and corestriction dictionary

For finite $L/K$:

$$
\operatorname{cor}\circ\operatorname{res}=[L:K],
$$

$$
\operatorname{res}:K^\times/(K^\times)^n\to L^\times/(L^\times)^n
\quad\text{is inclusion},
$$

$$
\operatorname{cor}:L^\times/(L^\times)^n\to K^\times/(K^\times)^n
\quad\text{is }N_{L/K},
$$

$$
\operatorname{inv}_L(\operatorname{res}\beta)
=[L:K]\operatorname{inv}_K(\beta),
$$

$$
\operatorname{inv}_K(\operatorname{cor}\gamma)
=\operatorname{inv}_L(\gamma).
$$

If the residue degree is $f$, arithmetic Frobenius for $L$ maps to $\varphi_K^f$. These five lines prevent the most common direction and normalization errors.

### 13.7 Adjoint tangent formulas

For a $d$-dimensional residual representation,

$$
h^0(\operatorname{ad}\bar\rho)=\dim\operatorname{End}_{G_K}(\bar\rho),
$$

$$
h^1(\operatorname{ad}\bar\rho)
=h^0+h^2+\delta_{\ell,p}d_Kd^2,
$$

where the last term is present only in mixed characteristic with coefficient characteristic $p$. The framed cocycle space has

$$
\dim Z^1=h^1+d^2-h^0.
$$

For fixed determinant and $\ell\nmid d$, replace $\operatorname{ad}$ by $\operatorname{ad}^0$ and $d^2$ by $d^2-1$ in the Euler term. The unramified tangent dimension is

$$
\dim H^1_{\mathrm{ur}}(K,\operatorname{ad}\bar\rho)
=h^0(K,\operatorname{ad}\bar\rho).
$$

These are ambient formulas. A smaller ramification or integral condition requires its own tangent-subspace calculation.

## 14. Conclusion

### 14.1 The two local directions and the exceptional $p$-adic bulk

The cohomology of a local Galois group is small because its architecture is small. Away from the residue characteristic, inertia contributes one tame $\mathbf Z_\ell(1)$ direction and the residue field contributes one procyclic Frobenius direction. Their interaction produces degree two, and finite-kernel/cokernel cancellation makes the Euler characteristic zero. The Brauer invariant shows that degree two is genuinely present and gives it a canonical arithmetic coordinate.

At the residue characteristic in mixed characteristic, principal units add $[K:\mathbf Q_p]$ infinitesimal directions. They appear exactly as the term $d_K\dim M$ in $h^1$. In equal characteristic, Artin–Schreier theory collapses the $p$-cohomological dimension to one while allowing $H^1$ to become infinite. These are not variants of one uniform formula; they are different local geometries.

### 14.2 What has been established for the next stage

We now have a complete low-degree local toolkit: fixed vectors, cocycles and torsors, Kummer and reciprocity calculations, unramified and tame restriction, cohomological dimensions, vanishing above degree two, the Brauer invariant, $H^2(K,\mu_n)$, finite and $\ell$-adic coefficient passage, Euler–Poincaré formulas, field-extension functoriality, and adjoint tangent dimensions. The flat and Galois Kummer theories have been compared without conflating them in equal characteristic, and the tangent formulas have been rearranged into the parameter–relation ledgers used by restricted ramification conditions. Every topology, twist, Frobenius direction, and residue-characteristic exception has been kept explicit.

The remaining step is not another size calculation. If $M$ is finite $\ell$-primary, killed by
$n=\ell^r$, with $\ell\ne\operatorname{char}K$, evaluation and cup product already give pairings

$$
H^i(K,M)\times H^{2-i}(K,M^*(1))
\longrightarrow H^2(K,\mu_n)
\xrightarrow{\operatorname{inv}_K}\mathbf Q/\mathbf Z.
$$

This includes $p$-primary modules over mixed-characteristic local fields. It excludes the
equal-characteristic $p$ branch, where the etale Tate twist used in the displayed pairing does
not exist.

What remains is to prove that these pairings are perfect and to identify annihilators of natural local conditions. That theorem will turn the obstruction term $H^2$ into a computable twisted invariant space. The arithmetic developed here ensures that, when duality arrives, it acts on finite groups of the right size, respects restriction and corestriction, and carries exactly the local dimensions required by deformation theory. Local Galois cohomology has thus reduced an infinite profinite symmetry to a finite and reusable calculus of inertia, Frobenius, units, and one final Brauer obstruction.
