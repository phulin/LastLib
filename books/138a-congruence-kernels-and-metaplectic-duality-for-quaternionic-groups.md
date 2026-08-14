# Congruence Kernels and Metaplectic Duality for Quaternionic Groups

## Contents

1. [The rank-two arithmetic problem](#1-the-rank-two-arithmetic-problem)
   - [The two completions](#11-the-two-completions)
   - [Why rank two is the threshold](#12-why-rank-two-is-the-threshold)
   - [The package proved here](#13-the-package-proved-here)
   - [Conventions on coefficients and topology](#14-conventions-on-coefficients-and-topology)
2. [Quaternionic norm-one groups and their arithmetic levels](#2-quaternionic-norm-one-groups-and-their-arithmetic-levels)
   - [Global and local forms](#21-global-and-local-forms)
   - [The omitted set and restricted product](#22-the-omitted-set-and-restricted-product)
   - [Reference integral level](#23-reference-integral-level)
   - [Strong approximation and congruence completion](#24-strong-approximation-and-congruence-completion)
3. [The full congruence kernel](#3-the-full-congruence-kernel)
   - [Full versus congruence topology](#31-full-versus-congruence-topology)
   - [Open-level invariance](#32-open-level-invariance)
   - [Routed levels](#33-routed-levels)
   - [Three false shortcuts](#34-three-false-shortcuts)
4. [The rank-two commutator theorem](#4-the-rank-two-commutator-theorem)
   - [A centrality criterion](#41-a-centrality-criterion)
   - [Quaternionic root charts](#42-quaternionic-root-charts)
   - [The finite-quotient contraction argument](#43-the-finite-quotient-contraction-argument)
   - [Relative generation and the ideal commutator theorem](#44-relative-generation-and-the-ideal-commutator-theorem)
   - [Centrality and the stem property](#45-centrality-and-the-stem-property)
5. [Two extension theories](#5-two-extension-theories)
   - [Continuous finite-coefficient extensions](#51-continuous-finite-coefficient-extensions)
   - [Measurable circle-valued extensions](#52-measurable-circle-valued-extensions)
   - [Automatic continuity](#53-automatic-continuity)
   - [The coefficient comparison theorem](#54-the-coefficient-comparison-theorem)
   - [The finite-cyclic warning](#55-the-finite-cyclic-warning)
6. [From compact transgression to adelic extensions](#6-from-compact-transgression-to-adelic-extensions)
   - [The relative compact multiplier](#61-the-relative-compact-multiplier)
   - [Induction from an open compact subgroup](#62-induction-from-an-open-compact-subgroup)
   - [The perfect congruence--metaplectic pairing](#63-the-perfect-congruence--metaplectic-pairing)
   - [Independence of the reference level](#64-independence-of-the-reference-level)
7. [Local scalar symbols](#7-local-scalar-symbols)
   - [Norm-residue normalization](#71-norm-residue-normalization)
   - [Topological Steinberg symbols](#72-topological-steinberg-symbols)
   - [The all-primary symbol lemma](#73-the-all-primary-symbol-lemma)
8. [Split local multipliers](#8-split-local-multipliers)
   - [Root lifts and the Steinberg relation](#81-root-lifts-and-the-steinberg-relation)
   - [Classification at a split finite place](#82-classification-at-a-split-finite-place)
   - [Commutators and the square](#83-commutators-and-the-square)
   - [Even-primary information](#84-even-primary-information)
9. [Division local multipliers](#9-division-local-multipliers)
   - [Cyclic coordinates and maximal tori](#91-cyclic-coordinates-and-maximal-tori)
   - [Congruence filtration](#92-congruence-filtration)
   - [The division classification theorem](#93-the-division-classification-theorem)
   - [Why restriction--corestriction is insufficient](#94-why-restriction--corestriction-is-insufficient)
10. [Products, cross terms, and restricted products](#10-products-cross-terms-and-restricted-products)
   - [The product decomposition](#101-the-product-decomposition)
   - [Cross-bicharacters](#102-cross-bicharacters)
   - [Diagonal splitting kills cross terms](#103-diagonal-splitting-kills-cross-terms)
   - [Passage to a restricted product](#104-passage-to-a-restricted-product)
11. [Adelic globalization and scalar reduction](#11-adelic-globalization-and-scalar-reduction)
   - [Local invariants of an adelic extension](#111-local-invariants-of-an-adelic-extension)
   - [The scalar class](#112-the-scalar-class)
   - [Injectivity](#113-injectivity)
   - [The global scalar cokernel](#114-the-global-scalar-cokernel)
12. [Totally real fields and routed odd-primary vanishing](#12-totally-real-fields-and-routed-odd-primary-vanishing)
   - [The exponent bound](#121-the-exponent-bound)
   - [Recovering the congruence kernel from its dual](#122-recovering-the-congruence-kernel-from-its-dual)
   - [Every routed spectator level](#123-every-routed-spectator-level)
13. [Examples and failure tests](#13-examples-and-failure-tests)
   - [The rational indefinite example](#131-the-rational-indefinite-example)
   - [A division spectator place](#132-a-division-spectator-place)
   - [Density without continuity](#133-density-without-continuity)
   - [Kernel invariance without centrality](#134-kernel-invariance-without-centrality)
   - [Roots of unity without duality](#135-roots-of-unity-without-duality)
14. [The geometric Ihara corollary](#14-the-geometric-ihara-corollary)
   - [The exact routed family](#141-the-exact-routed-family)
   - [Odd-primary abelian Ihara](#142-odd-primary-abelian-ihara)
   - [The exported corollary](#143-the-exported-corollary)
15. [The reusable rank-two theorem](#15-the-reusable-rank-two-theorem)
   - [Main theorem](#151-main-theorem)
   - [Proof assembly](#152-proof-assembly)
   - [Conclusion](#153-conclusion)

## 1. The rank-two arithmetic problem

An arithmetic group carries two natural finite-quotient topologies. One remembers every finite quotient of the abstract group. The other remembers only reduction modulo ideals, or equivalently the finite quotients visible inside a product of local groups. Their difference is the congruence kernel. For a quaternionic norm-one group with two independent noncompact directions, that difference is exceptionally rigid: it is central, it is dual to an adelic metaplectic kernel, and global reciprocity forces its odd-primary characters to vanish over a totally real field.

Each phrase in that summary hides a possible logical error. Density in a compact group does not make an abstract homomorphism continuous. Equality of kernels at commensurable levels does not make a kernel central in every completion. A bound on roots of unity does not bound the congruence kernel until a perfect duality and an injective scalar reduction have been constructed. Finite discrete coefficients and circle coefficients belong to different cohomological categories. Finally, a central extension of a product can contain cross-bicharacters even when all of its factor restrictions split.

The purpose of this book is to prove the complete rank-two package while keeping these distinctions visible. The result is not tied to one curve or one Hecke localization. It is an arithmetic theorem for norm-one groups of quaternion algebras and all of their open spectator levels.

### 1.1 The two completions

Let $F$ be a number field, let $B$ be a quaternion algebra over $F$, and put

$$
H=\operatorname{SL}_1(B).
$$

Thus for every $F$-algebra $R$,

$$
H(R)=\{x\in (B\otimes_F R)^\times:\operatorname{Nrd}(x)=1\}.
$$

Fix a finite place $v$ at which $B$ is split and put

$$
S=V_\infty(F)\cup\{v\},
\qquad
G^S=H(\mathbf A_F^S)=\prod_{w\notin S}'H(F_w).
\tag{1.1}
$$

The restricted product is taken with respect to the norm-one groups of maximal orders. Let $K\subset G^S$ be compact open and set

$$
\Gamma(K)=H(F)\cap K.
\tag{1.2}
$$

The group $\Gamma(K)$ is given the discrete topology before completion. Its full profinite completion is

$$
\widehat{\Gamma(K)}=\varprojlim_{N\triangleleft_f\Gamma(K)}\Gamma(K)/N,
\tag{1.3}
$$

where $N$ ranges over all normal subgroups of finite index. If $H(F)$ is dense in $G^S$, then $\Gamma(K)$ is dense in $K$ and the inclusion extends uniquely to a continuous surjection

$$
\rho_K:\widehat{\Gamma(K)}\twoheadrightarrow K.
\tag{1.4}
$$

The **full congruence kernel at level $K$** is

$$
C(K)=\ker(\rho_K).
\tag{1.5}
$$

The adjective full is important. We have not first discarded nonnormal finite-index subgroups, restricted to abelian quotients, or completed only at one prime. Every finite abstract quotient of $\Gamma(K)$ occurs in (1.3).

### 1.2 Why rank two is the threshold

For a place $u$, let $\operatorname{rk}_{F_u}H$ denote the dimension of a maximal $F_u$-split torus. A quaternionic norm-one group has local rank one when $B$ is split and rank zero when $B$ is division. Define

$$
\operatorname{rk}_S H=\sum_{u\in S}\operatorname{rk}_{F_u}H.
\tag{1.6}
$$

Our standing arithmetic hypothesis is

$$
\operatorname{rk}_S H\ge 2.
\tag{R2}
$$

In the Shimura-curve case, $F$ is totally real, $B$ is split at one real place $\tau$ and at the changing finite place $v$, and ramified at every other real place. Then the two summands supplied by $\tau$ and $v$ already give (R2).

Rank two is not a cosmetic lower bound. A single split place supplies contraction in one local root direction, but a finite quotient may absorb that contraction into a noncongruence normal subgroup. A second independent split direction lets one move denominators away from the first place and compare opposite root charts. The resulting ideal-commutator theorem is weaker than the congruence subgroup property but strong enough to prove centrality. Its abelian form also proves the stem property needed for perfect transgression.

We will use strong approximation in the precise form proved for simply connected quaternionic norm-one groups in Book 118: if $H$ is noncompact at one place in $S$, then $H(F)$ is dense in $G^S$. The rank-two theorem below needs more than that density. It uses two split members of $S$ in its finite-quotient commutator argument.

### 1.3 The package proved here

Let $\mathbf T=\mathbf R/\mathbf Z$ with its usual compact topology and let $\mathbf D=\mathbf Q/\mathbf Z$ with the discrete topology. Give $H(F)$ the discrete topology when it is used as a subgroup over which an adelic extension must split. Define the Moore metaplectic kernel

$$
M^S(H)=\ker\!\left[
H^2_{\mathrm m}(G^S,\mathbf T)
\longrightarrow
H^2(H(F),\mathbf T)
\right].
\tag{1.7}
$$

Here $H^2_{\mathrm m}$ classifies locally compact central extensions admitting a Borel section; the target is ordinary abstract group cohomology because $H(F)$ is discrete.

The main theorem will establish the following chain without inserting a congruence-subgroup hypothesis:

$$
\begin{array}{c}
\text{rank-two ideal commutators}
\Longrightarrow
C(K^*)\text{ central and stem},\\
\Longrightarrow
C(K^*)^\vee\simeq M^S(H),\\
\Longrightarrow
M^S(H)[n]\hookrightarrow
\operatorname{coker}\!\left[
H^2(F,\mathbf Z/n)\to\displaystyle\bigoplus_wH^2(F_w,\mathbf Z/n)
\right],\\
\Longrightarrow
M^S(H)[n]\hookrightarrow
\operatorname{Hom}(\mu_n(F),\mathbf D).
\end{array}
\tag{1.8}
$$

The last identification is the scalar arithmetic-duality theorem of Book 6. Everything before the last arrow is proved here. In particular, the first injection in the third line is not attributed to Hilbert reciprocity: it requires local multiplier classification, removal of cross terms, and a proof of adelic injectivity.

### 1.4 Conventions on coefficients and topology

For $n\ge1$ put $A_n=\mathbf Z/n\mathbf Z$ with the discrete topology and trivial group action unless another action is displayed. All cochains of a profinite group with values in $A_n$ are continuous. They therefore factor through finite quotients on compact domains, as in Book 24.

A homomorphism from a profinite group to $\mathbf T$ is always required to be continuous. Its image is compact and totally disconnected. A closed totally disconnected subgroup of the circle is finite, because every infinite closed subgroup of the circle is the whole circle. Hence

$$
\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf T)
=\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf D)
\tag{1.9}
$$

for every profinite group $P$. This equality concerns characters, not second cohomology.

For a locally compact second-countable group, a measurable cochain means a Borel cochain modulo equality almost everywhere. We normalize all cocycles at the identity. Every extension in the Moore category is a Hausdorff locally compact group extension with central circle kernel, open quotient map, and a Borel section. At almost all finite places our adelic extensions are split over the distinguished maximal compact subgroup. This restricted-product condition is part of the extension category, not an automatic consequence of listing local restrictions.

## 2. Quaternionic norm-one groups and their arithmetic levels

### 2.1 Global and local forms

The canonical involution of $B$ is denoted $x\mapsto\bar x$, and

$$
\operatorname{Trd}(x)=x+\bar x,
\qquad
\operatorname{Nrd}(x)=x\bar x.
$$

Book 77 gives the local classification. At a finite place $w$ there are exactly two possibilities:

$$
B_w:=B\otimes_FF_w\simeq M_2(F_w),
$$

or $B_w$ is the unique quaternion division algebra over $F_w$ with Brauer invariant $1/2$. Accordingly,

$$
H(F_w)\simeq \operatorname{SL}_2(F_w)
$$

in the split case, while $H(F_w)$ is compact in the division case. The group scheme $H$ is connected, absolutely almost simple, and simply connected of type $A_1$; these structural facts and the split root coordinates are developed in Book 115.

Choose a maximal order $\mathcal O_{B,w}\subset B_w$ at every finite place. At a division place it is unique. At a split place choose an identification with $M_2(F_w)$ carrying the order to $M_2(\mathcal O_w)$. Put

$$
K_w^0=\mathcal O_{B,w}^{1}
=\{x\in\mathcal O_{B,w}^\times:\operatorname{Nrd}(x)=1\}.
\tag{2.1}
$$

For all but finitely many $w$, this is the hyperspecial group $\operatorname{SL}_2(\mathcal O_w)$. Book 82 supplies the maximal-order and radical filtrations used below.

### 2.2 The omitted set and restricted product

For a finite set $S\supset V_\infty(F)$, write

$$
G^S=\prod_{w\notin S}'(H(F_w),K_w^0).
\tag{2.2}
$$

A basic open neighborhood of $1$ has the form

$$
\prod_{w\in T}U_w\times\prod_{w\notin S\cup T}K_w^0,
\tag{2.3}
$$

where $T$ is finite and each $U_w$ is open in $H(F_w)$. By the restricted-product topology of Book 4, $G^S$ is locally compact and second countable. The subgroup

$$
K^0=\prod_{w\notin S}K_w^0
\tag{2.4}
$$

is compact open.

Every compact open subgroup $K\subset G^S$ is commensurable with $K^0$. Indeed, compactness places $K$ inside a set of the form (2.3) with compact local factors, and openness contains a similar product; outside a finite set both equal $K_w^0$. This elementary fact is what permits one reference completion to control all finite spectator changes.

### 2.3 Reference integral level

Fix a finite set $T_0$ of finite places outside $S$ containing every place at which the chosen global maximal order, coefficient datum, or routed construction is not hyperspecial. At $w\in T_0$ choose a compact open $K_w^*\subset H(F_w)$; at all other $w\notin S$ put $K_w^*=K_w^0$. Define

$$
K^*=\prod_{w\notin S}K_w^*,
\qquad
\Gamma^*=H(F)\cap K^*.
\tag{2.5}
$$

We call $K^*$ a **reference integral level**. It can be maximal everywhere, but allowing finitely many fixed factors makes the theorem reusable in the presence of a predetermined tame or central datum. Replacing $K^*$ by a commensurable product changes none of the final groups canonically; this will be proved rather than assumed.

Choose an $S$-integral order $\mathcal O_{B,S}$ whose localization outside $S\cup T_0$ is $\mathcal O_{B,w}$. Then $\Gamma^*$ is commensurable with $\mathcal O_{B,S}^{1}$. For a nonzero ideal $\mathfrak a$ of $\mathcal O_{F,S}$ supported away from $T_0$, put

$$
\Gamma^*(\mathfrak a)
=\{\gamma\in\Gamma^*: \gamma\equiv1\pmod{\mathfrak a\mathcal O_{B,S}}\}.
\tag{2.6}
$$

These groups form a cofinal basis for the topology induced from $K^*$. At the finitely many exceptional factors one inserts an independent fixed open normal filtration. This makes (2.6) notation for the entire congruence basis, not a claim that one ideal describes an arbitrary local level exactly.

### 2.4 Strong approximation and congruence completion

Assume that $H(F_u)$ is noncompact for some $u\in S$. Strong approximation from Book 118 gives density of $H(F)$ in $G^S$. Intersecting an open coset in $G^S$ with $K$ proves density of $\Gamma(K)$ in $K$: if $xU\subset K$ with $U$ open in $G^S$, choose $h\in H(F)\cap xU$; then $h\in K$.

Consequently the congruence completion of $\Gamma(K)$ is exactly $K$. More explicitly,

$$
K\simeq\varprojlim_{U\triangleleft_oK}\Gamma(K)/(\Gamma(K)\cap U),
\tag{2.7}
$$

because density makes the map onto every finite quotient $K/U$ surjective and its kernel is $\Gamma(K)\cap U$. The universal property of the full profinite completion gives (1.4).

The inverse-limit identification can be checked without suppressing the exceptional local factors. Given $U\triangleleft_oK$, choose a finite set $T$ such that

$$
U=K\cap\left(
\prod_{w\in T}U_w\times
\prod_{w\notin S\cup T}K_w^0
\right)
\tag{2.8}
$$

after replacing $U$ by a smaller open normal subgroup. Strong approximation with the displayed local conditions gives every class of $K/U$ a rational representative in $\Gamma(K)$. Conversely, an element of $\Gamma(K)$ maps to the identity precisely when it belongs to every prescribed $U_w$, which is $\Gamma(K)\cap U$. The open normal subgroups of the form (2.8) are cofinal, proving (2.7).

One must keep the omitted set in this argument. If $S$ contained no noncompact place, strong approximation could fail and the closure of $H(F)\cap K$ could be a proper open subgroup of $K$. Then the right side of (2.7) would be that closure, not the nominal level. Likewise, replacing $H$ by $B^\times$ introduces a reduced-norm class group. The simply connected norm-one group and its noncompact omitted direction are both used.

Nothing here proves that (1.4) is injective. Strong approximation compares the congruence topology with the ambient compact topology. It says nothing about a finite quotient of the abstract group whose kernel contains no congruence neighborhood.

## 3. The full congruence kernel

### 3.1 Full versus congruence topology

Let $\mathcal N_f(\Gamma)$ be the normal finite-index subgroups of a discrete group $\Gamma$, and let $\mathcal N_c(\Gamma)$ be the subfamily obtained by intersecting $\Gamma$ with open normal subgroups of its congruence completion. The natural map

$$
\varprojlim_{N\in\mathcal N_f(\Gamma)}\Gamma/N
\longrightarrow
\varprojlim_{N\in\mathcal N_c(\Gamma)}\Gamma/N
\tag{3.1}
$$

has kernel $C(K)$. Thus $C(K)=1$ is the full congruence subgroup property. We neither assume nor need that assertion. The theorem eventually shows only that, in the totally real rank-two case, $C(K)$ has order at most two. That possible double cover is exactly the metaplectic residue one should not erase.

For later use, observe that a finite homomorphism $\chi:\Gamma\to A$ into a finite discrete group is continuous for the full profinite topology by definition. It extends to $K$ if and only if it is continuous for the congruence topology. If $A$ is abelian, the obstruction to extending is detected by the restriction of the unique continuous extension $\widehat\chi:\widehat\Gamma\to A$ to $C(K)$.

### 3.2 Open-level invariance

The following elementary lemma is indispensable.

**Lemma 3.1 (open-level invariance).** Let $K'\subset K$ be compact open subgroups of $G^S$. Under the canonical map $\widehat{\Gamma(K')}\to\widehat{\Gamma(K)}$ one has

$$
\widehat{\Gamma(K')}
\simeq \rho_K^{-1}(K'),
\qquad
C(K')\simeq C(K).
\tag{3.2}
$$

**Proof.** The group $\Gamma(K')$ has finite index in $\Gamma(K)$ because its quotient injects into the finite set $K/K'':$ here $K''$ is the core of $K'$ in $K$. For a finite-index subgroup $\Lambda\subset\Gamma$, the natural map $\widehat\Lambda\to\widehat\Gamma$ is injective with image the closure of $\Lambda$. To see injectivity directly, if $N\triangleleft_f\Lambda$, the core in $\Gamma$ of a finite-index normal subgroup of $\Lambda$ contained in $N$ is finite index in $\Gamma$ and meets $\Lambda$ inside $N$. Thus the full profinite topology on $\Lambda$ is the subspace topology.

The closure of $\Gamma(K')$ in $\widehat{\Gamma(K)}$ maps into $K'$. Conversely, its image in $K$ is the closure of $\Gamma(K')$, which is $K'$. If $x\in\rho_K^{-1}(K')$, choose a net $\gamma_i\in\Gamma(K)$ converging to $x$. Since $K'$ is open, $\rho_K(\gamma_i)$ lies in $K'$ eventually, so $\gamma_i\in\Gamma(K')$ eventually. Hence $x$ lies in its closure. Taking kernels proves (3.2). $\square$

For arbitrary commensurable $K_1,K_2$, apply the lemma to $K_1\cap K_2$. It identifies both kernels with one profinite group, canonically up to the evident transitive identifications through further intersections. We denote this common group by

$$
C^S(H).
\tag{3.3}
$$

This notation records invariance of the kernel as a group. It does not yet record how a larger completion conjugates it.

The transitivity just mentioned is literal. If $K_0\subset K_1\cap K_2\cap K_3$ is open, all identifications are restrictions of the inclusions

$$
\widehat{\Gamma(K_0)}
\longrightarrow\widehat{\Gamma(K_i)}.
\tag{3.3a}
$$

They agree on the dense subgroup $\Gamma(K_0)$ and therefore on its completion. Thus no choice of a chain of intersections changes $C^S(H)$. What can change is the conjugation representation of a containing completion on this fixed group; that is why Section 3.3 retains actual routes.

### 3.3 Routed levels

A **routed level** consists of a compact open $K_r\subset G^S$, an element $a_r\in G^S$, and an inclusion

$$
K_r\subset a_rK^*a_r^{-1}.
\tag{3.4}
$$

A route $r\to r'$ is represented by right translation and a rational component correction whose conjugation carries a common open subgroup of the source into one of the target. Principal levels, ray-trivializing levels, auxiliary neat levels, flag-permutation levels, and their adjoint companions all have this form: away from finitely many places they retain the same maximal compact, and at the exceptional places they replace it by an open subgroup. Conjugation by $a_r$ gives an isomorphism from the completion at $a_r^{-1}K_ra_r$ to the completion at $K_r$ and hence an actual isomorphism of their kernels.

There are therefore two legitimate transports of centrality:

1. downward transport from a completion to an open subgroup of that same completion;
2. transport through an explicit conjugation isomorphism.

Both preserve commutators. Mere equality of the abstract kernels through (3.2) does not.

### 3.4 Three false shortcuts

The first false shortcut is to infer continuity from density. Let $\Gamma$ be a dense subgroup of a profinite group $K$. An abstract map $\Gamma\to A$ to a finite group extends continuously to $K$ exactly when its kernel is open for the induced topology. Density only gives uniqueness of an extension if one exists. It does not give existence.

The second false shortcut is to transport centrality upward. Let $C$ be a finite group and let $Q$ act nontrivially on it. In $E=C\rtimes Q$, the subgroup $C$ is the kernel of $E\to Q$. Its intersection with the preimage of the identity subgroup is the same group $C$, central in that smaller preimage, but it is not central in $E$. This is precisely the shape that open-level invariance alone fails to exclude.

The third false shortcut is to read the order of $C^S(H)$ from $\mu(F)$. Roots of unity bound a scalar cohomological cokernel. They do not act directly on $C^S(H)$. The route from one to the other needs the perfect pairing of Chapter 6 and the injective scalar map of Chapter 11.

## 4. The rank-two commutator theorem

### 4.1 A centrality criterion

Write $\Gamma=\Gamma^*$ and $C=C(K^*)$. The following criterion turns a statement about finite quotients of $\Gamma$ into centrality of $C$.

**Lemma 4.1 (ideal-commutator criterion).** Suppose that for every $N\triangleleft_f\Gamma$ there is a congruence ideal $\mathfrak a$ such that

$$
[\Gamma(\mathfrak a),\Gamma]\subset N.
\tag{4.1}
$$

Then $C$ is central in $\widehat\Gamma$.

**Proof.** Fix $c\in C$, $g\in\widehat\Gamma$, and $N\triangleleft_o\widehat\Gamma$. Replacing $N$ by its core, assume it is normal. Its intersection with $\Gamma$ is a normal subgroup of finite index, still denoted $N$. Choose $\mathfrak a$ as in (4.1). Since $c$ maps to $1$ in $K^*$, it lies in the closure of every congruence subgroup, in particular in $\overline{\Gamma(\mathfrak a)}$. Since $\Gamma$ is dense in $\widehat\Gamma$, continuity of the commutator and (4.1) give

$$
[c,g]\in\overline N=N.
$$

This holds for every open normal $N$, whose intersection is trivial. Thus $[c,g]=1$. $\square$

For the stem property we need the abelian companion.

**Lemma 4.2 (abelian congruence criterion).** Suppose every homomorphism $\Gamma\to A$ to a finite abelian group kills $\Gamma(\mathfrak a)$ for some congruence ideal $\mathfrak a$. Then

$$
C\subset\overline{[\widehat\Gamma,\widehat\Gamma]}.
\tag{4.2}
$$

**Proof.** The quotient $\widehat\Gamma/\overline{[\widehat\Gamma,\widehat\Gamma]}$ is profinite abelian. If the image of some $c\in C$ were nontrivial, a finite continuous character of this quotient would be nontrivial on $c$. Its restriction to $\Gamma$ would be a finite abelian character. By hypothesis it would factor continuously through a congruence quotient and hence extend to $K^*$, so its extension to $\widehat\Gamma$ would kill $C$, a contradiction. $\square$

The rest of the chapter proves both hypotheses from (R2).

### 4.2 Quaternionic root charts

Choose two places $u_0,u_1\in S$ at which $B$ is split. Fix splittings

$$
\iota_i:B\otimes_FF_{u_i}\simeq M_2(F_{u_i})
\qquad(i=0,1).
\tag{4.3}
$$

In each split factor use the usual elements

$$
x(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix},
\quad
y(t)=\begin{pmatrix}1&0\\t&1\end{pmatrix},
\quad
h(a)=\begin{pmatrix}a&0\\0&a^{-1}\end{pmatrix}.
\tag{4.4}
$$

They satisfy

$$
h(a)x(t)h(a)^{-1}=x(a^2t),
\qquad
h(a)y(t)h(a)^{-1}=y(a^{-2}t),
\tag{4.5}
$$

and, whenever $1+st\ne0$,

$$
x(s)y(t)=
y\!\left(\frac{t}{1+st}\right)
h(1+st)
x\!\left(\frac{s}{1+st}\right).
\tag{4.6}
$$

The last identity follows by multiplying the three displayed matrices after writing the middle diagonal term in the standard four-root factorization; equivalently, both sides act identically on the two columns and have determinant one. We shall use it only on a sufficiently small neighborhood where all denominators are units.

Although $H$ need not have an $F$-rational root subgroup, these charts can be approximated by rational points with controlled denominators. The needed form is the following lemma.

**Lemma 4.3 (two-place root approximation).** Let $T$ be a finite set of places disjoint from $\{u_0,u_1\}$, let $W_i\subset H(F_{u_i})$ be an open subset contained in one of the root-chart cells generated by (4.4), and let $L_w\subset H(F_w)$ be compact open for $w\in T$. There is $\gamma\in H(F)$ whose $u_i$-components lie in $W_i$, whose $w$-components lie in $L_w$, and which is integral outside $S\cup T$.

Moreover, if every $W_i$ tends to the identity with root parameters in prescribed fractional ideals, $\gamma$ may be chosen in the corresponding global principal congruence subgroup outside $S$.

**Proof.** The reduced norm equation $\operatorname{Nrd}(z)=1$ is a smooth affine quadric of dimension three. At a split place, the big cell defined by a nonzero chosen matrix entry is rational, with three affine coordinates and one inverse denominator. Apply the integral norm-quadric approximation lemma of Book 118, Section 6.2, simultaneously to the prescribed local cells and integral models. The proof there moves the inverse denominator in an isotropic direction at one split place while preserving the other local conditions. Because we have two split places, use $u_0$ to move denominators introduced while approximating the $u_1$ chart and then reverse the roles; the second pass is taken inside the first prescribed neighborhood. Chinese remaindering preserves the stated principal congruences outside $S$. The process terminates because each pass strictly decreases the norm of the outside-$S$ denominator ideal. $\square$

The final sentence is the point at which rank two enters. With only one split place, the denominator-moving direction and the prescribed contraction direction coincide, so this two-pass argument supplies no independent control.

We also need relative generation.

**Lemma 4.4 (relative root generation).** There is a finite set of rational big cells $\mathcal U_1,\ldots,\mathcal U_m\subset H$ and an integer $d\ge1$ with the following property. For every ideal $\mathfrak a$ prime to a fixed finite set, every element of $\Gamma(\mathfrak a^d)$ is a product of at most $m$ rational points $z_j$ such that, at one of the split places, $z_j$ lies in a root chart with all nonconstant coordinates in $\mathfrak a$, while $z_j$ is integral and congruent to $1$ modulo $\mathfrak a$ outside $S$.

**Proof.** Cover the smooth affine quadric $H$ by the four standard cells obtained by requiring one matrix coordinate to be nonzero after scalar extension to a splitting field. Their coordinate rings descend after adjoining finitely many denominators, which accounts for the fixed exceptional set. On the identity cell, Gaussian elimination is exactly (4.6) and writes a point congruent to $1$ as a bounded word in opposite root parameters and a torus parameter, all lying in the same ideal up to replacing $\mathfrak a$ by a fixed power. A point outside that cell is moved into it by one member of a fixed finite collection of integral rational points; because the original point is congruent to $1$, only the identity cell occurs once $\mathfrak a$ is sufficiently deep. For the finitely many shallow ideals increase $d$.

Descent from the split chart is effected by pairing a coordinate with its conjugate in a quadratic splitting field. The product has coefficients in $F$ and reduced norm one. The trace and norm of an element of $\mathfrak a\mathcal O_L$ lie in $\mathfrak a$ and $\mathfrak a^2$, respectively, so replacing $\mathfrak a$ by $\mathfrak a^d$ makes every descended coordinate lie in $\mathfrak a$. Lemma 4.3 supplies the required integral rational representatives without changing these congruences. $\square$

For clarity, we record the algebra behind the bounded word assertion. Choose a quadratic splitting field $L/F$ with involution $\sigma$ and an $L$-isomorphism $H_L\simeq\operatorname{SL}_{2,L}$. If $g\equiv1$ modulo $\mathfrak a^2$, its upper-left entry $a$ is a unit and Gaussian elimination gives

$$
g=
y(ca^{-1}),h(a),x(a^{-1}b).
\tag{4.6a}
$$

The descent cocycle sends $x(r)$ to a conjugate of either $x(\sigma r)$ or $y(\sigma r)$. Multiply (4.6a) by its descended conjugate and use (4.6) to move unlike roots past one another. Every new denominator is of the form $1+r\sigma(s)$. If $r,s\in\mathfrak a^2$, this is a unit congruent to $1$ modulo $\mathfrak a^2$, and its inverse has the convergent integral expansion

$$
(1+r\sigma(s))^{-1}
=1-r\sigma(s)+(r\sigma(s))^2-\cdots.
\tag{4.6b}
$$

Modulo $\mathfrak a^N$ the series is finite. At the level of the actual $S$-integer order, clear the finitely many denominators of the chosen splitting once; raising the starting ideal to a fixed power absorbs them. The norm-one relation removes the final diagonal coordinate. Thus one obtains a word of bounded length modulo $\mathfrak a^N$, with an error in $\Gamma(\mathfrak a^N)$. Repeating with $N,2N,4N,\ldots$ would normally give only a convergent word in the congruence completion. For Lemma 4.4 one stops after the first stage at which the residual point lies in the identity chart and applies the same exact elimination to that residual point. Its denominators are already units by (4.6b), so the second elimination is exact. This gives a bound depending on the finite cell cover, not on $\mathfrak a$ or $g$.

There is a useful finite-quotient version which avoids any accidental appeal to convergence.

**Lemma 4.4A (finite-quotient root calculus).** Let $q:\Gamma\to Q$ have finite image. There are ideals $\mathfrak a\supset\mathfrak b$ such that:

1. $q(\Gamma(\mathfrak a))=q(\Gamma(\mathfrak b))$;
2. this common subgroup is generated by images of the relative root words in Lemma 4.4 at level $\mathfrak a$;
3. every congruence error produced by (4.6a)--(4.6b) at level $\mathfrak a$ has image in that same subgroup.

**Proof.** For any descending chain of ideals $\mathfrak a_1\supset\mathfrak a_2\supset\cdots$, the finite subgroups $q(\Gamma(\mathfrak a_i))$ eventually stabilize. Choose a chain with $\mathfrak a_{i+1}$ divisible by a sufficiently high fixed power of $\mathfrak a_i$ and stop at two consecutive stable terms $\mathfrak a,mathfrak b$. Perform the elimination above modulo $\mathfrak b$. It writes every member of $\Gamma(\mathfrak a)$ as a bounded relative root word times an element of $\Gamma(\mathfrak b)$. Since the two congruence images agree, repeat on the residual image. Finiteness of $Q$ and bounded word length let one choose a generating set of the stable subgroup consisting entirely of the first-stage relative root images. Every error lies in $q(\Gamma(\mathfrak b))$, which is the same subgroup. $\square$

This lemma is deliberately formulated inside a finite quotient. No limit of rational points is evaluated by $q$.

### 4.3 The finite-quotient contraction argument

Let $q:\Gamma\to Q$ be a homomorphism to a finite group. Put $e=|Q|!$, so $q(g)^e=1$ for every $g\in\Gamma$. Choose at $u_0$ a scalar $a$ with $|a|_{u_0}<1$ and at $u_1$ require the corresponding scalar to be a unit. Lemma 4.3 gives $t\in\Gamma$ whose $u_0$-component is arbitrarily close to $h(a)$, whose $u_1$-component remains in a fixed compact root chart, and which is integral outside $S$.

For a root-chart element $z(r)$ near $1$, conjugation by $t^{e}$ replaces its leading root parameter by $a^{\pm2e}r$ at $u_0$, up to terms of strictly larger $r$-adic order. In the finite quotient, however, $q(t^e)=1$, and hence

$$
q(z(r))=q(t^ez(r)t^{-e}).
\tag{4.7}
$$

Iterating gives the same image for a sequence whose $u_0$-component tends to $1$. Use Lemma 4.3 with the second split place held fixed to replace each term by a rational integral element in a successively deeper congruence subgroup. Since $Q$ is finite, the kernels of all these rational replacements have one common finite-index core. It follows that, for some ideal $\mathfrak b(q)$,

$$
q([z,\gamma])=1
\tag{4.8}
$$

for every $\gamma\in\Gamma$ and every relative root generator $z$ of level $\mathfrak b(q)$.

We spell out the stabilization, because a limit in a local group cannot itself be inserted into an abstract finite quotient. Choose rational replacements $z_j$ with $z_{j+1}=k_jz_jk_j^{-1}e_j$, where $q(k_j)^e=1$ and $e_j\in\Gamma(\mathfrak b_j)$ with $\mathfrak b_j$ strictly increasing. There are only finitely many values of $q(z_j)$, while (4.7) makes them all equal once $q(e_j)=1$. If no such $j$ existed, the descending subgroups $q(\Gamma(\mathfrak b_j))$ would form an infinite strictly descending chain in $Q$. Thus they stabilize. At stabilization, opposite contractions at $u_0$ and $u_1$, combined through (4.6), show that the stable image commutes with the images of both opposite root charts. Those images generate $q(\Gamma)$ by Lemma 4.4 applied to coset representatives. Hence (4.8).

The same argument has an abelian strengthening. If $Q$ is abelian, (4.6) and (4.5) give in $Q$

$$
q(x((a^2-1)r))=1,
\qquad
q(y((a^{-2}-1)r))=1.
\tag{4.9}
$$

Weak approximation chooses the contracting scalar so that $a^2-1$ is a unit at every prime dividing a prescribed congruence modulus outside $S$. Relative root generation then shows that $q$ kills an entire principal congruence subgroup, rather than merely its commutators.

Let us verify the passage from contraction to commutation more explicitly. By Lemma 4.4A, work in a stable congruence image $R\subset Q$. Conjugation by $q(t)$ is an automorphism of the finite group $R$ whose order divides $e$. In a local upper-root coordinate it also carries filtration degree $j$ to degree $j+2e|v_{u_0}(a)|$. Therefore its $e$th power acts both as the identity on $R$ and as a strictly filtration-increasing map on every nonconstant coordinate. If $R_j$ denotes the image of root words of filtration at least $j$, then

$$
R_j=R_{j+2e|v_{u_0}(a)|}.
\tag{4.9a}
$$

The chain $R_j$ is eventually trivial after passing to the quotient by the subgroup generated by commutators with $q(\Gamma)$. Indeed, in that quotient all conjugates coincide, while the relative word calculus expresses a sufficiently deep generator as a product of conjugates whose parameters add to zero. Hence the image of $R_j$ in the coinvariants is zero. Equivalently,

$$
R_j\subset[R,q(\Gamma)].
\tag{4.9b}
$$

Reverse the contracting roles of $u_0$ and $u_1$. The opposite-root factorization (4.6) then puts $[R,q(\Gamma)]$ inside a deeper stable group $R_{j'}$ with the same image. Combining (4.9a) and (4.9b) yields

$$
[R,q(\Gamma)]=1.
\tag{4.9c}
$$

This is (4.8). If $Q$ is abelian, the coinvariant step is unnecessary: (4.9) kills the generators themselves once $a^2-1$ and $a^{-2}-1$ are units at the relevant outside-$S$ primes. The two-place choice makes these unit requirements simultaneous.

### 4.4 Relative generation and the ideal commutator theorem

We now collect the preceding calculation in its durable form.

**Theorem 4.5 (rank-two ideal commutators).** Assume (R2). For every normal subgroup $N\triangleleft_f\Gamma$ there is a nonzero ideal $\mathfrak a$ of $\mathcal O_{F,S}$ such that

$$
[\Gamma(\mathfrak a),\Gamma]\subset N.
\tag{4.10}
$$

If $\Gamma/N$ is abelian, $\mathfrak a$ can be chosen so that

$$
\Gamma(\mathfrak a)\subset N.
\tag{4.11}
$$

The same assertions hold after imposing any fixed finite collection of open integral conditions outside $S$.

**Proof strategy.** Pass to one finite quotient, descend through its finite chain of congruence images, and stop where the image stabilizes. Two independent contractions make the stable image commute with both opposite root charts. Relative root generation then makes it central in the whole quotient. In an abelian quotient the same identities kill the stable image itself.

**Proof.** Apply the contraction construction to $Q=\Gamma/N$. It produces an ideal $\mathfrak b$ for which every level-$\mathfrak b$ relative root generator commutes with $Q$. Lemma 4.4 supplies $d$ such that $\Gamma(\mathfrak b^d)$ is a bounded product of these generators. A product of elements central modulo $N$ is central modulo $N$, proving (4.10) with $\mathfrak a=\mathfrak b^d$.

If $Q$ is abelian, choose the two contracting torus parameters so that the factors $a^{2e}-1$ and $b^{2e}-1$ generate the unit ideal at every outside-$S$ prime not already absorbed into $\mathfrak b$. Equation (4.9) kills both opposite root generators at a deeper level. The torus factor in (4.6) is a product of an upper and a lower root word, so it is killed as well. Relative generation gives (4.11).

Fixed local conditions merely enlarge the exceptional finite set in Lemmas 4.3 and 4.4. The contraction is performed at the two members of $S$, so those extra compact conditions remain unchanged. $\square$

The theorem is not the congruence subgroup property. Formula (4.10) says that a deep congruence subgroup is central in each finite quotient; it does not say that the subgroup vanishes there. Formula (4.11) proves the congruence property only for finite abelian quotients.

### 4.5 Centrality and the stem property

**Theorem 4.6 (reference centrality and stem).** Under (R2), the sequence

$$
1\longrightarrow C
\longrightarrow\widehat\Gamma
\xrightarrow{\rho_{K^*}}K^*
\longrightarrow1
\tag{4.12}
$$

is a central extension, and

$$
C\subset\overline{[\widehat\Gamma,\widehat\Gamma]}.
\tag{4.13}
$$

**Proof.** Theorem 4.5, (4.10), verifies Lemma 4.1, so $C$ is central. Its abelian assertion (4.11) verifies Lemma 4.2, giving (4.13). $\square$

If $K'\subset K^*$ is open, then $\widehat{\Gamma(K')}$ is the open subgroup $\rho_{K^*}^{-1}(K')$ containing $C$. Thus $C$ is central there. If $K'$ is contained in a conjugate $aK^*a^{-1}$, conjugation transports Theorem 4.6 to that reference completion and centrality then descends to $K'$. This proves centrality at every actually routed level of (3.4). We make no claim at this point that centrality ascends to an arbitrary compact open containing such a level; the totally real order bound will settle that larger statement in Chapter 12.

We also need rational commensurators. Every $q\in H(F)$ commensurates $\Gamma$: the compact opens $K^*$ and $qK^*q^{-1}$ have open intersection. Apply Theorem 4.5 after adding to $T_0$ the finitely many denominator places of $q$. Its last sentence permits those fixed local conditions and proves

$$
[q,C]=1
\tag{4.14}
$$

inside the relative completion constructed in Section 6.2. More explicitly, test the commutator in any finite quotient of the group generated by $\Gamma$ and $q$. A deep congruence subgroup is central there by (4.10), and $C$ is its inverse-limit closure. Since finite quotients separate the relative completion, the commutator is one. Thus reference centrality is compatible with every rational route, a fact stronger than the bare isomorphism (3.2).

## 5. Two extension theories

### 5.1 Continuous finite-coefficient extensions

Let $P$ be a profinite group and let $A$ be a finite discrete abelian group with continuous $P$-action. Book 24 defines $H^r_{\mathrm{cont}}(P,A)$ from continuous inhomogeneous cochains. When the action is trivial, a normalized continuous $2$-cocycle $c:P\times P\to A$ defines the profinite central extension

$$
1\longrightarrow A\longrightarrow E_c\longrightarrow P\longrightarrow1,
\qquad
(a,g)(b,h)=(a+b+c(g,h),gh).
\tag{5.1}
$$

Conversely, a profinite extension by $A$ admits continuous local sections. Since $P$ is compact and zero-dimensional, finitely many such sections may be patched across a finite clopen partition to give a global continuous section. Its defect is a continuous cocycle. Changing the section changes the cocycle by a continuous coboundary. Thus $H^2_{\mathrm{cont}}(P,A)$ classifies profinite central extensions with their identified kernel and quotient.

The continuity condition is substantial. A set-theoretic section always exists, but its cocycle need not be continuous. Continuous cochains on a compact profinite domain are locally constant, and therefore factor through a finite quotient after refining finitely many clopen neighborhoods. This finiteness is used repeatedly below.

### 5.2 Measurable circle-valued extensions

Let $L$ be a locally compact second-countable group. A **Moore extension** of $L$ by $\mathbf T$ is an exact sequence of Hausdorff locally compact groups

$$
1\longrightarrow\mathbf T\longrightarrow E\xrightarrow{p}L\longrightarrow1
\tag{5.2}
$$

in which $\mathbf T$ is central, $p$ is open, and $p$ has a Borel section. Equivalence means a continuous extension isomorphism inducing the identity on $\mathbf T$ and $L$. Baer sum makes the equivalence classes an abelian group, denoted $H^2_{\mathrm m}(L,\mathbf T)$.

This extension definition agrees with the measurable-cochain definition. Indeed, a Borel section $s$ gives

$$
c_s(g,h)=s(g)s(h)s(gh)^{-1}\in\mathbf T.
\tag{5.3}
$$

It is Borel and satisfies the cocycle identity by associativity. A second section $b(g)s(g)$ changes $c_s$ by the measurable coboundary $db$. Conversely, suppose a measurable cocycle $c$ represents an extension class which is continuous on some identity neighborhood after a measurable coboundary. Give $\mathbf T\times L$ the unique group topology for which it agrees near $(1,1)$ with the twisted product topology and translate that neighborhood throughout the group. The cocycle identity makes the translated topologies agree. The resulting group is locally compact, the quotient is open, and the evident section is Borel. Any Moore cocycle is cohomologous to one continuous near the identity: average a bounded Borel lift over a compact neighborhood, take the difference of its left translates, and shrink the neighborhood until the resulting defect is continuous. The averaging is performed in $\mathbf R$ after choosing a lift on an arc of length less than one; two choices differ by an integer-valued Borel function and hence by a coboundary. Thus the two constructions are inverse.

For a discrete group $D$, every function is continuous and Borel. Hence $H^2_{\mathrm m}(D,\mathbf T)$ is ordinary group cohomology $H^2(D,\mathbf T)$. This is why the right-hand group in (1.7) is not topologized by the dense embedding $H(F)\subset G^S$.

### 5.3 Automatic continuity

We need two elementary automatic-continuity facts.

**Lemma 5.1.** A Borel homomorphism between locally compact second-countable groups is continuous.

**Proof.** Let $f:L\to L'$ be Borel and let $U'$ be a symmetric identity neighborhood in $L'$. Choose a symmetric $V'$ with $(V')^2\subset U'$. Since $L'$ is second countable, countably many translates of $V'$ cover $L'$, so countably many translates of the Borel set $f^{-1}(V')$ cover $L$. Its intersection with some compact set of positive Haar measure has positive measure. The Steinhaus lemma then says that

$$
f^{-1}(V')^{-1}f^{-1}(V')=f^{-1}((V')^{-1}V')
$$

contains an identity neighborhood. It is contained in $f^{-1}(U')$. Thus $f$ is continuous at $1$, hence everywhere. $\square$

**Lemma 5.2.** Let $P$ be profinite and let

$$
1\to A\to E\to P\to1
\tag{5.4}
$$

be a Moore extension with finite kernel $A$. Then $E$ is profinite and (5.4) represents a class in $H^2_{\mathrm{cont}}(P,A)$.

**Proof.** The identity component $E^\circ$ maps into $P^\circ=1$, hence lies in the finite group $A$ and is trivial. Thus $E$ is totally disconnected. It is compact because it is a finite union of translates of the inverse image of a compact neighborhood in $P$, or directly because both kernel and quotient are compact. A compact totally disconnected Hausdorff group is profinite. The continuous-section argument following (5.1) now applies. $\square$

The circle case has a connected kernel, so the preceding argument does not make the middle group profinite. It does, however, give the finiteness property needed later.

**Lemma 5.2A (torsion over a profinite quotient).** If $P$ is profinite, every class in $H^2_{\mathrm m}(P,\mathbf T)$ has finite order.

**Proof.** Represent the class by a compact extension $1\to\mathbf T\to E\to P\to1$. Compactness of $E$ follows from compactness of kernel and quotient. Its identity component is exactly the embedded circle: the image of $E^\circ$ in $P$ is connected and hence trivial, while the circle is connected and contains the identity.

Choose an identity arc $I\subset\mathbf T$ containing no nontrivial subgroup. The small-normal-subgroup lemma for compact groups gives a closed normal subgroup $N\triangleleft E$ contained in a prescribed identity neighborhood with $N\cap\mathbf T\subset I$ and with $E/N$ a compact Lie group. For completeness, embed $E$ by its finite-dimensional unitary representations into a product of unitary groups. Finitely many matrix coefficients separate the complement of the chosen neighborhood from $1$; the common kernel $N$ of those representations lies in the neighborhood, and the image is a closed subgroup of a finite product of unitary groups, hence a compact Lie group. Since $N\cap\mathbf T$ is a subgroup contained in $I$, it is trivial.

Let $U$ be the image of $N$ in $P$. The quotient $P/U$ embeds in

$$
(E/N)/(\mathbf T N/N).
$$

This is a compact Lie group and is totally disconnected, hence finite. Thus $U$ is open. Because $N\cap\mathbf T=1$, the map $N\to U$ is an isomorphism of topological groups and splits the original extension over $U$.

Replace $U$ by its open normal core. Restriction of the extension class to $U$ is zero. For trivial central coefficients, corestriction followed by restriction is multiplication by $[P:U]$ on $H^2_{\mathrm m}(P,\mathbf T)$; this is checked on an inhomogeneous cocycle by multiplying its translates over a set of coset representatives, exactly as for finite-index group cohomology. Therefore $[P:U]$ kills the class. $\square$

The proof supplies an order for each extension, not one uniform exponent for all extensions of $P$.

### 5.4 The coefficient comparison theorem

Embed $A_n$ in $\mathbf T$ by $a\mapsto a/n$ and use the exact sequence of topological groups

$$
0\longrightarrow A_n\longrightarrow\mathbf T
\xrightarrow{n}\mathbf T\longrightarrow0.
\tag{5.5}
$$

The map $n:\mathbf T\to\mathbf T$ has local continuous sections and a global Borel section. It therefore gives a long exact sequence in Moore cohomology. On a profinite group, the finite terms agree with continuous cohomology by Lemma 5.2.

**Theorem 5.3 (finite-to-circle comparison).** For every profinite group $P$ there is a natural exact sequence

$$
0\longrightarrow
\frac{\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf T)}
{n\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf T)}
\xrightarrow{\delta_n}
H^2_{\mathrm{cont}}(P,A_n)
\xrightarrow{\iota_n}
H^2_{\mathrm m}(P,\mathbf T)[n]
\longrightarrow0.
\tag{5.6}
$$

If $J\subset P$ is a dense abstract subgroup and

$$
M_{A_n}(P,J)=\ker\!\left[
H^2_{\mathrm{cont}}(P,A_n)\to H^2(J,A_n)
\right],
\tag{5.7}
$$

then $\iota_n$ maps $M_{A_n}(P,J)$ onto the subgroup of $H^2_{\mathrm m}(P,\mathbf T)[n]$ whose restriction to $J$ is zero. Its kernel is the intersection of $M_{A_n}(P,J)$ with the Bocksteins $\delta_n(\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf T))$.

**Proof.** The long exact sequence from (5.5) contains

$$
H^1_{\mathrm m}(P,\mathbf T)
\xrightarrow{n}
H^1_{\mathrm m}(P,\mathbf T)
\xrightarrow{\delta_n}
H^2_{\mathrm m}(P,A_n)
\to
H^2_{\mathrm m}(P,\mathbf T)
\xrightarrow{n}
H^2_{\mathrm m}(P,\mathbf T).
$$

Measurable homomorphisms $P\to\mathbf T$ are continuous by Lemma 5.1, and $H^2_{\mathrm m}(P,A_n)=H^2_{\mathrm{cont}}(P,A_n)$ by Lemma 5.2. Exactness gives (5.6), except possibly surjectivity onto the $n$-torsion. That surjectivity can also be seen directly. If a circle cocycle $c$ satisfies $nc=db$, choose a Borel $n$th root $b/n$ and replace $c$ by $c-d(b/n)$. Its values lie in $A_n$. The associated finite-kernel extension is profinite, so the class has a continuous representative by Lemma 5.2.

Restriction commutes with the long exact sequences. A finite class trivial on $J$ plainly maps to a circle class trivial on $J$. Conversely, let a circle class be $n$-torsion and split on $J$. Use the $n$-fold trivialization construction immediately below, normalized on the chosen image of $J$. It produces a profinite $A_n$-subextension containing that image, hence a member of (5.7). Changing the normalized trivialization changes the finite class by the Bockstein of a continuous character of $P$. This gives the relative surjectivity and the stated kernel. $\square$

There is a more concrete extension picture of the surjection in (5.6). Let $E$ represent an $n$-torsion circle extension and choose an isomorphism from its $n$-fold Baer sum to the split extension. On elements this is a continuous function $b:E\to\mathbf T$ satisfying

$$
b(ze)=nz+b(e)
\qquad(z\in\mathbf T).
\tag{5.6a}
$$

The closed subgroup $E[n,b]=\ker b$ meets the central circle in $A_n$ and maps onto $P$. Its kernel and quotient are compact, so Lemma 5.2 makes it a profinite $A_n$-extension. Replacing the trivialization of the $n$-fold Baer sum multiplies $b$ by a continuous character of $P$; the finite extension changes by its Bockstein. This is exactly the first term of (5.6).

If a splitting over a discrete dense subgroup $J$ is fixed, normalize $b$ to vanish on the image of that splitting. The intersection $E[n,b]$ then contains a lift of $J$ and gives a relative finite extension. A different normalization differs by a character of $P$ precisely when it gives the same topological extension. This proves the relative assertion without extending an arbitrary discontinuous character of $J$ to $P$.

The last paragraph is a relative statement about extension classes, not a claim that an arbitrary character of the dense group $J$ extends continuously.

### 5.5 The finite-cyclic warning

Let $P=C_p$ and $A_p=\mathbf Z/p$. The familiar periodic resolution gives

$$
H^2(C_p,A_p)\simeq A_p.
\tag{5.8}
$$

On the other hand $\mathbf T$ is divisible, so for a finite group

$$
H^2(C_p,\mathbf T)\simeq
\operatorname{Hom}(H_2(C_p,\mathbf Z),\mathbf T)=0,
\tag{5.9}
$$

because $H_2(C_p,\mathbf Z)=0$. The nonzero class in (5.8) is the Bockstein of the character sending a generator to $1/p$. Thus (5.6) is exact, while a supposed injection

$$
H^2_{\mathrm{cont}}(P,A_p)\hookrightarrow H^2_{\mathrm m}(P,\mathbf T)
$$

would be false. This small example is the reason the character quotient cannot be omitted from the congruence--metaplectic comparison.

## 6. From compact transgression to adelic extensions

### 6.1 The relative compact multiplier

Return to the central stem extension (4.12). For a finite trivial coefficient group $A$, Book 24's five-term sequence gives

$$
\operatorname{Hom}_{\mathrm{cont}}(\widehat\Gamma,A)
\longrightarrow
\operatorname{Hom}_{\mathrm{cont}}(C,A)
\xrightarrow{\operatorname{tg}}
H^2_{\mathrm{cont}}(K^*,A)
\longrightarrow
H^2_{\mathrm{cont}}(\widehat\Gamma,A).
\tag{6.1}
$$

Because $C$ is central, the invariant superscript normally attached to its character group is unnecessary. Restriction from $\widehat\Gamma$ to the dense subgroup $\Gamma$ identifies the kernel of the last map with

$$
M_A(K^*,\Gamma)
=\ker\!\left[
H^2_{\mathrm{cont}}(K^*,A)\to H^2(\Gamma,A)
\right].
\tag{6.2}
$$

Indeed, pulling an extension back to $\widehat\Gamma$ and then to dense $\Gamma$ loses no continuous finite cocycle: if the latter splitting is a homomorphism on $\Gamma$, its graph is dense in a unique closed complement exactly when the corresponding class on $\widehat\Gamma$ is zero. Equivalently, use the universal property of the profinite completion for the finite quotient extension.

The stem property makes the first arrow in (6.1) zero on $C$. Any continuous homomorphism from $\widehat\Gamma$ to an abelian group kills $\overline{[\widehat\Gamma,\widehat\Gamma]}$, which contains $C$. Hence transgression is an isomorphism

$$
\operatorname{Hom}_{\mathrm{cont}}(C,A)
\xrightarrow{\sim}M_A(K^*,\Gamma).
\tag{6.3}
$$

Neither centrality alone nor kernel invariance alone would prove (6.3).

### 6.2 Induction from an open compact subgroup

Let $K=K^*$ and $\Gamma=\Gamma^*$. Give $H(F)$ the **full $S$-arithmetic topology** whose identity neighborhoods are the finite-index subgroups of groups

$$
H(F)\cap q_1Kq_1^{-1}\cap\cdots\cap q_rKq_r^{-1},
\qquad q_i\in H(F).
\tag{6.4}
$$

Let $\widetilde G^S$ be its Hausdorff completion. Arithmetic linear groups are residually finite, so the map from $H(F)$ into this completion is injective: embed a finitely generated subgroup in integral matrices after inverting finitely many primes and separate a nonidentity matrix by reduction at a prime not dividing one of its nonzero entries. The closure of $\Gamma$ in $\widetilde G^S$ is its full profinite completion $\widehat\Gamma$ and is compact open.

The congruence topology is coarser than the full $S$-arithmetic topology. Hence the diagonal map extends to a continuous homomorphism

$$
\pi:\widetilde G^S\longrightarrow G^S.
\tag{6.5}
$$

It is onto. On the compact open $\widehat\Gamma$ it is $\rho_K$ and maps onto $K$; strong approximation gives $G^S=H(F)K$, while $H(F)$ lies in the image. The induced map on discrete coset spaces

$$
H(F)/\Gamma\longrightarrow G^S/K
\tag{6.6}
$$

is bijective: surjectivity is strong approximation, and $qK=q'K$ for rational $q,q'$ exactly when $q^{-1}q'\in H(F)\cap K=\Gamma$. Therefore every element of $\ker\pi$ lies in $\widehat\Gamma$. We have an exact sequence

$$
1\longrightarrow C
\longrightarrow\widetilde G^S
\xrightarrow{\pi}G^S
\longrightarrow1.
\tag{6.7}
$$

The topology on $\widetilde G^S$ is locally compact because it has the compact open subgroup $\widehat\Gamma$. Equation (4.14) and Theorem 4.6 show that $C$ commutes with both $H(F)$ and $\widehat\Gamma$. These subgroups generate a dense subgroup, so continuity makes $C$ central in all of $\widetilde G^S$.

This relative completion is the correct induction object. A bare quotient of $H(F)\times E_K$ would not automatically respect the extra relations created when $K$ is not normal in $G^S$.

Pushout of (6.7) by a character $\chi:C\to\mathbf T$ gives a Moore extension of $G^S$. It splits over $H(F)$ through the embedded rational subgroup of $\widetilde G^S$.

Conversely, let $E\to G^S$ be a Moore extension with a fixed splitting $s:H(F)\to E$. Pull it back to $\widetilde G^S$. Restriction to $\widehat\Gamma$ is a compact extension split over $\Gamma$. By compact transgression it is a pushout of (4.12) by a unique character of $C$, once the stem property is imposed. The resulting isomorphism over $\widehat\Gamma$ agrees with the rational splitting on $\Gamma$. It therefore agrees on every conjugate $q\widehat\Gamma q^{-1}$: both maps are continuous there and agree on the dense subgroup $q\Gamma q^{-1}$. These conjugate compact opens cover $\widetilde G^S$, so the local isomorphisms glue to a global extension isomorphism. This proves the following precise replacement for naive induction.

The character of $C$ does not depend on the chosen splitting over $H(F)$. Work on an $A_n$ lift. Two splittings differ on $\Gamma$ by a homomorphism $\Gamma\to A_n$. The abelian clause (4.11) says that this finite character is congruence-continuous, so it extends to $K$ and its pullback to $\widehat\Gamma$ kills $C$. Thus both splittings give the same transgression character. This is another use of the proved abelian congruence theorem; density would give only uniqueness of a continuous extension, not its existence.

**Proposition 6.1 (relative-completion equivalence).** Pushout along (6.7) induces an equivalence between:

1. circle pushouts of the central relative-completion extension by continuous characters of $C$;
2. Moore extensions of $G^S$ by $\mathbf T$ split over discrete $H(F)$.

Restriction to $K$ identifies this equivalence with compact transgression. It respects Baer sum, torsion, smaller open compact levels, and rational conjugation.

**Proof.** The preceding construction gives essential surjectivity. A map between two pushouts is determined on the open preimage of $K$ and on the rational splitting. Agreement on their dense intersection $\Gamma$, followed by conjugation, makes these maps agree on the covering family of compact opens. Thus it is unique and continuous. Fiber products and central pushouts commute with restriction, proving the stated compatibilities. $\square$

### 6.3 The perfect congruence--metaplectic pairing

For $\chi\in C^\vee=\operatorname{Hom}_{\mathrm{cont}}(C,\mathbf T)$, push out (4.12) along $\chi$:

$$
E_\chi=(\mathbf T\times\widehat\Gamma)/
\{(-\chi(c),c):c\in C\}.
\tag{6.8}
$$

This is a compact central extension of $K^*$ by $\mathbf T$. The map $\gamma\mapsto[0,\gamma]$ splits it over discrete $\Gamma$. Equivalently, push out (6.7) itself by $\chi$. Proposition 6.1 gives an adelic extension split over $H(F)$. Denote its class by $\Phi(\chi)$.

**Theorem 6.2 (perfect congruence--metaplectic duality).** Under (R2), the map

$$
\Phi:C^\vee\xrightarrow{\sim}M^S(H)
\tag{6.9}
$$

is an isomorphism. Equivalently, evaluation gives a perfect pairing of topological torsion groups

$$
\langle\ ,\ \rangle:
C\times M^S(H)\longrightarrow\mathbf T.
\tag{6.10}
$$

Here perfect means that $M^S(H)$ is the Pontryagin dual of the profinite group $C$, not merely that the pairing is nondegenerate on a selected finite subgroup.

**Proof strategy.** Work first on one torsion layer. The coefficient exact sequence converts a circle extension into a finite relative compact extension; stem transgression converts that extension into a character of $C$; the relative completion converts it back into the original adelic extension. Compactness then proves that every circle class lies on some torsion layer.

**Proof.** First consider an element $\alpha\in M^S(H)$ of order dividing $n$. Restrict it to $K^*$ and use its given abstract splitting over $\Gamma$. Theorem 5.3 lifts its class to a finite $A_n$-extension of $K^*$ split over $\Gamma$, after changing the lift by the Bockstein of a continuous character of $K^*$ if necessary. Formula (6.3) identifies that finite relative class with a unique $\chi_n\in\operatorname{Hom}_{\mathrm{cont}}(C,A_n)$. Pushing out $\chi_n$ to $\mathbf T$ recovers $\alpha$ by Proposition 6.1. Thus $\Phi$ is surjective on torsion.

For injectivity, suppose $\Phi(\chi)=0$. The compact pushout (6.8) then has a continuous splitting over $K^*$. Such a splitting is a continuous character $f:\widehat\Gamma\to\mathbf T$ whose restriction to $C$ is $\chi$. But every continuous image of the profinite group $\widehat\Gamma$ in $\mathbf T$ is finite, and $f$ kills $\overline{[\widehat\Gamma,\widehat\Gamma]}$. The stem inclusion (4.13) gives $f|_C=0$, so $\chi=0$.

It remains to see that every class in $M^S(H)$ is torsion; otherwise the preceding argument would prove only the torsion part. Restrict a class to the profinite group $K^*$. Lemma 5.2A gives a positive integer which kills that restriction. Proposition 6.1 is an equivalence of extension categories, so the same integer kills the adelic class. This proves surjectivity for all classes.

Finally, Pontryagin duality says that evaluation between a profinite abelian group and its continuous circle dual is perfect. The kernel $C$ is abelian because it is central in $\widehat\Gamma$. Transporting evaluation through $\Phi$ gives (6.10). $\square$

The torsion assertion uses the compact-group argument of Lemma 5.2A. It is not obtained by averaging a circle-valued cocycle, an operation which would have no additive meaning.

There is an intrinsic formula for the pairing. Let $\alpha\in M^S(H)$ have order dividing $n$. Choose a finite $A_n$ lift of its restriction to $K^*$ which splits on $\Gamma$, and choose such a splitting. Pull the extension back to $\widehat\Gamma$. For $c\in C$, lift $c$ to the pulled-back extension and compare it with the identity lift over $1\in K^*$. Their quotient is an element $\chi_\alpha(c)\in A_n$. Then

$$
\langle c,\alpha\rangle
=\frac{\chi_\alpha(c)}{n}\pmod{\mathbf Z}.
\tag{6.10a}
$$

Changing the finite lift adds the restriction of a character of $\widehat\Gamma$. The stem property makes that character zero on $C$, so (6.10a) is independent of the lift. Changing the rational splitting adds a character of $\Gamma$ whose finite extension is already accounted for by relative transgression; it gives the same value. If $m\alpha=0$ as well, coefficient reduction carries $\chi_\alpha$ to the $A_m$ character used at level $m$. Hence the formula is compatible across all torsion orders.

Nondegeneracy on the right is now concrete. A nonzero metaplectic class gives a nonzero relative compact class, hence a nonzero transgression character. Nondegeneracy on the left says that a nonidentity $c\in C$ survives some finite quotient of $C$; a character of that finite abelian quotient detects it and its pushout is a nonzero adelic extension. These are the two directions of perfectness, not a cardinality argument.

### 6.4 Independence of the reference level

Let $K_1^*,K_2^*$ be two reference integral levels. Their intersection $K_0$ is open in both. Lemma 3.1 identifies the three congruence kernels. Proposition 6.1 identifies the three relative extension categories with the same adelic category. The construction (6.8) commutes with restriction. Therefore the diagrams

$$
\begin{array}{ccc}
C(K_i^*)^\vee&\xrightarrow{\Phi_i}&M^S(H)\\
\big\downarrow&&\Vert\\
C(K_0)^\vee&\xrightarrow{\Phi_0}&M^S(H)
\end{array}
\tag{6.11}
$$

commute. The perfect pairing is consequently intrinsic to $(F,B,S)$.

## 7. Local scalar symbols

### 7.1 Norm-residue normalization

Let $k$ be a nonarchimedean local field and $n\ge1$. Put $A_n=\mathbf Z/n$ with trivial Galois action. Local duality supplies a perfect pairing

$$
H^2(k,A_n)\times\mu_n(k)\longrightarrow\mathbf D.
\tag{7.1}
$$

We retain this canonical form when $\mu_n$ is not contained in $k$. If $\zeta_n\in k$ is chosen, $A_n\simeq\mu_n$ and cup product of Kummer classes gives the Hilbert symbol

$$
(a,b)_{k,n}\in\mu_n.
\tag{7.2}
$$

Changing $\zeta_n$ changes both the identification and the character evaluating (7.2); the class in $H^2(k,A_n)$ is unchanged. Book 5 fixes the reciprocity normalization, and Book 6 fixes the global sum of local invariants. We use those conventions throughout.

A scalar class $\xi\in H^2(k,A_n)$ determines a continuous Steinberg symbol

$$
s_\xi:k^\times\times k^\times\longrightarrow A_n^\vee\subset\mathbf T
\tag{7.3}
$$

by evaluating the norm-residue cup product against $\xi$. It is bimultiplicative and satisfies

$$
s_\xi(a,1-a)=0
\qquad(a\ne0,1).
\tag{7.4}
$$

### 7.2 Topological Steinberg symbols

Let $A$ be finite. A **topological Steinberg symbol** is a continuous map

$$
s:k^\times\times k^\times\to A
$$

which is multiplicative in both variables and satisfies $s(a,1-a)=0$. Continuity means continuity for the product topology on $k^\times\times k^\times$ and the discrete topology on $A$.

The Steinberg relation has strong consequences. From $s(a,-a)=0$, obtained by applying the relation to $(1+a)^{-1}$ and simplifying, one obtains

$$
s(a,-1)=s(a,a)^{-1}.
\tag{7.5}
$$

Applying the relation to $a/(a-1)$ gives skew symmetry

$$
s(a,b)=s(b,a)^{-1}.
\tag{7.6}
$$

When $A$ is written additively, the inverse signs become minus signs. These identities remain valid at residue characteristic two; what changes there is the information lost by passing from the symbol to a commutator square.

### 7.3 The all-primary symbol lemma

**Theorem 7.1 (local symbol classification).** The assignment $\xi\mapsto s_\xi$ is an isomorphism

$$
H^2(k,A_n)
\xrightarrow{\sim}
\{\text{continuous $A_n^\vee$-valued Steinberg symbols on $k$}\}.
\tag{7.7}
$$

It is functorial for finite extensions through restriction and corestriction and does not require $\mu_n\subset k$.

**Proof strategy.** Split $k^\times$ into a uniformizer, residue units, and principal units. The Steinberg relation determines the mixed terms and forces the principal-unit part to be the local norm-residue pairing. Perfect local duality proves uniqueness.

**Proof.** Choose a uniformizer $\pi$ and write

$$
k^\times=\pi^{\mathbf Z}\times\mathcal O_k^\times,
\qquad
1\to U^1\to\mathcal O_k^\times\to\kappa^\times\to1.
\tag{7.8}
$$

Continuity makes $s$ trivial on $U^r$ in each variable for some $r$. Thus it factors through a finite quotient of each variable. On pairs of units with distinct residues, $1-a$ is again a unit, and repeated use of $s(a,1-a)=0$ reduces the value to symbols with one entry in $U^1$. For $u\in U^j$, choose $x$ with $u=1-x$ and $v(x)=j$; then the Steinberg relation exchanges $s(u,b)$ with a symbol involving $x$, lowering the unit depth in one variable and increasing it in the other. Induction on the filtration, stopping at $U^r$, determines the principal-unit pairing from the values $s(\pi,u)$.

The map $u\mapsto s(\pi,u)$ is a continuous character of $\mathcal O_k^\times$. Local reciprocity identifies it with a character of inertia of exponent dividing $n$. Its value on $\pi$ supplies the unramified coordinate. Together these give a unique character of the local fundamental class, hence a unique $\xi\in H^2(k,A_n)$ under (7.1). The norm-residue symbol $s_\xi$ has the same uniformizer and unit values. The filtration induction makes $s=s_\xi$ everywhere.

Conversely, cup products are bilinear and the Kummer classes of $a$ and $1-a$ have zero cup product: the cyclic algebra $(a,1-a)$ splits because $1-a$ is the norm of $1-\sqrt[n]{a}$ after the usual telescoping product, with Galois descent supplying the statement when the roots are not in $k$. Thus $s_\xi$ is a continuous Steinberg symbol.

Restriction and corestriction follow from the projection formula for cup products and the norm compatibility of local reciprocity. $\square$

The filtration argument includes wild and dyadic unit layers. It uses continuity to stop at finite depth; it does not divide by the residue characteristic or assume a tame symbol formula.

In the tame case the classification is visible in one line. Suppose the residue field has order $q$, $n$ is prime to the residue characteristic, and $\mu_n\subset k$. Write $a=\pi^ru$ and $b=\pi^sv$ with $u,v\in\mathcal O_k^\times$. Then

$$
(a,b)_{k,n}
=\left(
(-1)^{rs}\frac{\bar u^s}{\bar v^r}
\right)^{(q-1)/n}.
\tag{7.9}
$$

Thus the symbol is determined by valuation and residue-unit data, and it is trivial on two units. This explains why a nontrivial unramified local multiplier can nevertheless have a preferred hyperspecial splitting. When the residue characteristic divides $n$, formula (7.9) is insufficient: principal units carry additional information. The depth induction in Theorem 7.1 retains exactly those wild layers and is also why only finitely many layers occur for a continuous finite-valued symbol.

For example, over a dyadic field an order-two symbol may be nontrivial on $U^1\times U^1$ even though its tame reduction is one. The norm-residue description sees that class; a residue-field formula or the squared commutator of Section 8.3 does not.

## 8. Split local multipliers

### 8.1 Root lifts and the Steinberg relation

Let $G_k=\operatorname{SL}_2(k)$ and let

$$
1\to\mathbf T\to E\to G_k\to1
\tag{8.1}
$$

be a Moore extension of finite order. The additive root groups $(k,+)$ have no nontrivial finite-order circle extension compatible with the contracting torus action. To prove this, restrict to a compact open additive subgroup $L\subset k$. A finite multiple of the class is represented by a finite extension of $L$; conjugation by $h(a)$ with $|a|<1$ carries it into arbitrarily small subgroups. The finite cocycle is locally constant, so its restriction becomes zero. Expanding $k$ as the union of the contracted copies of $L$ makes the whole root restriction split. The splitting is unique after requiring the lift of $x(t)$, respectively $y(t)$, to be a homomorphism and to take $0$ to $1$.

Here is the contraction calculation in cochains. Let $c(r,s)$ be an $A_n$-valued continuous cocycle on $(k,+)$ obtained from Theorem 5.3. Choose $m$ so that $c$ is zero on $\mathfrak p^m\times\mathfrak p^m$ after a continuous coboundary. Conjugation invariance of the ambient extension gives a cochain $b_a$ with

$$
c(a^2r,a^2s)-c(r,s)=db_a(r,s).
\tag{8.1a}
$$

For $j$ large, $a^{2j}r,a^{2j}s\in\mathfrak p^m$. Summing the telescoping coboundaries from $0$ to $j-1$ writes $c(r,s)$ as a coboundary on every compact ball. Normalize the primitives compatibly on nested balls by subtracting additive characters. Their union is a Borel primitive on $k$, and the resulting splitting is a Borel homomorphism, hence continuous by Lemma 5.1. If two normalized root splittings existed, their quotient would be a continuous additive character fixed by $r\mapsto a^2r$ for every $a$. Choosing $a$ with $a^2-1$ invertible forces that character to vanish. This proves both existence and uniqueness.

Choose these lifts $\widetilde x(t)$ and $\widetilde y(t)$. Define

$$
\widetilde w(a)=
\widetilde x(a)\widetilde y(-a^{-1})\widetilde x(a),
\qquad
\widetilde h(a)=\widetilde w(a)\widetilde w(-1).
\tag{8.2}
$$

The defect

$$
\sigma_E(a,b)=
\widetilde h(a)\widetilde h(b)\widetilde h(ab)^{-1}
\tag{8.3}
$$

lies in $\mathbf T$. The rank-one Bruhat relations imply that it is bimultiplicative. Applying the lifted factorization (4.6) in the two possible orders gives

$$
\sigma_E(a,1-a)=1.
\tag{8.4}
$$

Thus $\sigma_E$ is a topological Steinberg symbol. A change in the normalized root splittings multiplies (8.3) by a coboundary and leaves the symbol class unchanged.

The two calculations can be made directly. Uniqueness of the upper-root lift forces

$$
\widetilde h(a)\widetilde x(t)\widetilde h(a)^{-1}
=\widetilde x(a^2t)
\tag{8.4a}
$$

with no central error. Compare the two sides after replacing $a$ successively by $a$, $b$, and $ab$; cancellation gives multiplicativity of $\sigma_E$ in its first variable. The lower-root identity gives the second variable. For $a\ne0,1$, factor the matrix which successively carries the three lines $[1:0]$, $[1:a]$, and $[1:1]$ into standard position in the two possible Bruhat orders. Cancelling the unique root lifts leaves exactly $\sigma_E(a,1-a)=1$. Thus the Steinberg relation is forced by the cell overlap rather than imposed as an extra hypothesis.

Conversely, a topological Steinberg symbol $\sigma$ defines an extension. Take generators $\widetilde x(t)$, $\widetilde y(t)$, and a central copy of its value group, impose the additive root relations, the conjugation relations, and (8.3). The only overlap among the two Bruhat cells is governed by (8.4), so the presentation is consistent. Give the extension the topology for which the lifted big cell

$$
k\times k^\times\times k\to E,
\quad(r,a,s)\mapsto\widetilde y(r)\widetilde h(a)\widetilde x(s)
\tag{8.5}
$$

is a local homeomorphism onto its image. The relations make multiplication continuous. This constructs the inverse to $E\mapsto\sigma_E$.

To check that no relation has been missed, use the two normal forms

$$
B=\{h(a)x(t)\},
\qquad
BwB=\{y(r)w(1)h(a)x(t)\}.
\tag{8.5a}
$$

Multiplication of normal forms requires only additive root multiplication, (8.4a), and the cell-crossing identity (4.6). Ambiguity occurs precisely at the overlap of the cells, where (8.4) resolves it. Associativity on triples reduces to bimultiplicativity and the Steinberg relation. Hence the presented group has central kernel exactly the value group of $\sigma$ and gives every extension with that symbol.

### 8.2 Classification at a split finite place

For a locally compact second-countable group $L$, write

$$
\overline H^2_n(L)=
H^2_{\mathrm m}(L,\mathbf T)[n]
\tag{8.5b}
$$

and call it the reduced $n$-multiplier. When it is computed from finite $A_n$-extensions, the coefficient exact sequence says to quotient those lifts by the Bocksteins of continuous circle characters, exactly as in (5.6). If $L$ has no nontrivial continuous circle character, that quotient is invisible. The circle group (8.5b), rather than a chosen finite lift, is the invariant seen by relative compact transgression.

**Theorem 8.1 (split local multiplier).** For every nonarchimedean local field $k$ there is a natural isomorphism

$$
\lambda_{k,n}^{\mathrm{sp}}:
\overline H^2_n(\operatorname{SL}_2(k))
\xrightarrow{\sim}H^2(k,A_n).
\tag{8.6}
$$

It is characterized by sending an extension to the scalar class corresponding under Theorem 7.1 to its torus defect (8.3). It is valid at residue characteristics two and three and for every $n$.

**Proof.** The preceding root-lift construction gives a bijection between reduced finite-order extension classes and continuous finite-order Steinberg symbols. Theorem 7.1 identifies the latter with $H^2(k,A_n)$. Baer sum multiplies the defects, so the bijection is a group isomorphism. Functoriality follows because the root presentation and the norm-residue symbol both commute with field embeddings. At the small residue fields, the full group can have a finite character coming from a compact quotient; the reduced convention removes exactly its Bockstein, as Theorem 5.3 requires. No root-generation exception remains in the multiplier quotient. $\square$

In particular, the ordered torus defect detects a reduced split extension. If it is trivial, the normal forms (8.5a) assemble the normalized root lifts into a global continuous splitting. The same statement with “ordered defect” replaced by “torus commutator” is false at even order.

### 8.3 Commutators and the square

Assume temporarily that $\mu_n\subset k$ and evaluate the scalar class through a character $\chi:\mu_n\to\mathbf T$. For diagonal torus elements, (8.3) and skew symmetry give

$$
[\widetilde h(a),\widetilde h(b)]
=\sigma_E(a,b)\sigma_E(b,a)^{-1}
=\chi\bigl((a,b)_{k,n}^{2}\bigr).
\tag{8.7}
$$

The square is forced: a commutator antisymmetrizes a bimultiplicative cocycle. Omitting it changes the odd-primary normalization by the automorphism $z\mapsto z^2$ and destroys all information of order two.

For odd $n$, squaring is an automorphism of $\mu_n$, so (8.7) determines the full symbol. For even $n$, it does not. The extension must be classified by the torus defect (8.3), not by the commutator alone.

### 8.4 Even-primary information

The real metaplectic double cover is the simplest warning: its diagonal commutator can be trivial on a large subgroup while the cover remains nonsplit. Locally, if $\sigma$ has order two, then $\sigma(a,b)^2=1$, so the right side of (8.7) is always one although $\sigma$ may be nontrivial.

Our all-primary classification retains three pieces simultaneously:

1. the ordered torus multiplication defect $\sigma_E(a,b)$;
2. the root normalization defining $\widetilde h(a)$;
3. the Bockstein quotient from Theorem 5.3.

These determine the two-primary class without selecting a primitive root of unity. This is essential because the totally real conclusion is an exponent-at-most-two theorem, not a theorem obtained by discarding the even part.

## 9. Division local multipliers

### 9.1 Cyclic coordinates and maximal tori

Let $D$ be the quaternion division algebra over a nonarchimedean local field $k$. Choose an unramified quadratic extension $L/k$ inside $D$ and an element $\Pi\in D$ such that

$$
D=L\oplus L\Pi,
\qquad
\Pi^2=\pi,
\qquad
\Pi z=\bar z\Pi.
\tag{9.1}
$$

Then

$$
\operatorname{Nrd}(x+y\Pi)=N_{L/k}(x)-\pi N_{L/k}(y).
\tag{9.2}
$$

The norm-one torus

$$
T_L=L^1=\{z\in L^\times:N_{L/k}(z)=1\}
\tag{9.3}
$$

lies in $D^1=\operatorname{SL}_1(D)$. Every noncentral element of $D$ generates a quadratic field, so the group is covered by its maximal norm-one tori. Two such tori are conjugate exactly when their quadratic fields are isomorphic as embedded extensions; conjugation compatibility is therefore part of any extension classification.

The element $\Pi$ normalizes $T_L$ and acts by $z\mapsto\bar z=z^{-1}$. Although $\Pi$ itself need not have norm one, multiplying by an element of $L^\times$ of norm $\pi^{-1}$ produces a norm-one normalizer after an unramified scalar enlargement; all formulas below descend because the resulting defect is invariant under $L/k$ conjugation.

### 9.2 Congruence filtration

Let $\mathcal O_D$ be the maximal order, $\mathfrak P=\Pi\mathcal O_D$ its radical, and

$$
U_D^r=(1+\mathfrak P^r)\cap D^1.
\tag{9.4}
$$

Book 82 gives

$$
D^1/U_D^1\simeq\ker(N:\kappa_{q^2}^\times\to\kappa_q^\times),
\tag{9.5}
$$

a cyclic group of order $q+1$. For $r\ge1$, multiplication and reduced norm give

$$
U_D^r/U_D^{r+1}
\simeq
\{\bar x\in\mathfrak P^r/\mathfrak P^{r+1}:
\operatorname{Trd}(x)=0\},
\tag{9.6}
$$

an additive residue-space quotient. Commutators satisfy

$$
[U_D^r,U_D^s]\subset U_D^{r+s},
\tag{9.7}
$$

because $(1+x)(1+y)(1+x)^{-1}(1+y)^{-1}\equiv1+xy-yx$ modulo $\mathfrak P^{r+s+1}$.

Conjugation by a residue torus element $t\in T_L$ acts on the trace-zero line in (9.6) by $t/\bar t=t^2$. Except on the fixed line forced at a dyadic boundary, these weights are nontrivial. At that boundary the next commutator layer and the norm equation supply the missing relation. This filtration is the division analogue of the two opposite root groups.

We isolate the filtration computation used in the classification.

**Lemma 9.2 (division filtration lifting).** Let $A$ be finite and let $E_A$ be a continuous central $A$-extension of $D^1$. Fix a splitting on $U_D^{r+1}$. The obstruction to extending it to $U_D^r$, modulo changing the splitting by a character, is determined by the restriction of the torus defect to $T_L\cap U_D^r$. If that defect is trivial for every maximal torus, the splitting extends. Compatible extensions through all $r$ are unique modulo a continuous character of $D^1$.

**Proof.** Write $V_r=U_D^r/U_D^{r+1}$. A choice of lifts of $V_r$ has two defects: a central alternating commutator form

$$
\omega_r:V_r\wedge V_r\to A
\tag{9.7a}
$$

and an additive $2$-cocycle on $V_r$. The latter is a Bockstein of a character after passage to circle coefficients and is removed in the reduced multiplier. Relation (9.7) identifies $\omega_r(\bar x,\bar y)$ with the central value assigned to $xy-yx$ in $U_D^{2r}/U_D^{2r+1}$.

Use (9.1) to describe $V_r$. If $r$ is even, its nonzero coordinate is represented by $x\Pi^r$ with $x+\bar x=0$; if $r$ is odd, it is represented by $x\Pi^r$ modulo the one trace relation coming from (9.9). Conjugation by $t\in T_L$ multiplies $x$ by $t^{1-(-1)^r}$ up to the Frobenius action on the residue field. Thus every nontrivial weight occurs together with its inverse. An invariant alternating form pairs only inverse weights, and that pairing is exactly the commutator of two elements which lie in the quadratic algebra generated by their product. It is therefore read by the defect on the corresponding maximal torus.

At residue characteristic two a weight can equal its inverse. Choose $x,y$ representing two successive filtration layers. Expanding (9.9) shows

$$
\operatorname{Trd}(x)+\operatorname{Nrd}(x)=0,
\qquad
[1+x,1+y]\equiv1+xy-yx
\tag{9.7b}
$$

at the first nonzero layer. The quadratic algebra generated by $x+y$ contains the fixed-weight line, and its torus defect supplies the remaining value of $\omega_r$. Hence trivial torus defects make $\omega_r=0$ in every case.

With both defects removed, the chosen splitting on $U_D^{r+1}$ extends across the finite abelian quotient $V_r$. Two extensions differ by a character of $V_r$. Choose those characters successively so that the splittings agree under conjugation by $T_L$; compactness gives an inverse-limit splitting of $U_D^1$. The residue quotient (9.5) is cyclic, so its remaining extension is again a Bockstein. This proves existence. The same induction applied to the quotient of two splittings proves uniqueness modulo a character. $\square$

### 9.3 The division classification theorem

Restrict a finite-order Moore extension $E$ of $D^1$ to every maximal torus $T_E=E^1$. Choose compatible splittings on sufficiently deep $U_D^r$; existence follows because a finite cocycle is locally constant, and compatibility is obtained recursively from (9.7). The multiplication defect on $T_E$ is a continuous bimultiplicative pairing. Conjugation by the normalizer forces it to be skew under the nontrivial automorphism of $E/k$. Corestricting its norm-residue class therefore gives a scalar class in $H^2(k,A_n)$.

**Theorem 9.1 (division local multiplier).** There is a natural isomorphism

$$
\lambda_{k,n}^{\mathrm{div}}:
\overline H^2_n(D^1)
\xrightarrow{\sim}H^2(k,A_n).
\tag{9.8}
$$

For every quadratic maximal field $E\subset D$, restriction of an extension with scalar class $\xi$ has torus defect equal to the restriction of the norm-residue symbol $s_\xi$ to $E^1$, with corestriction normalization. The construction is independent of the chosen maximal field and agrees with (8.6) after a field extension splitting $D$.

**Proof strategy.** First kill a class whose scalar invariant is zero by descending compatible splittings through the radical filtration. Then construct a class from a scalar symbol in cyclic coordinates. The overlap of two maximal tori is controlled by (9.7), which proves both independence and surjectivity.

**Proof.** Let $\alpha$ be a reduced $n$-torsion extension class. Choose $r$ so large that its finite $A_n$ representative splits on $U_D^r$. Suppose inductively it splits on $U_D^{j+1}$. The obstruction to extending the splitting to $U_D^j$ is an alternating form on the additive quotient (9.6), together with a linear defect for conjugation by the residue torus. Relation (9.7) identifies the alternating form with the restriction of the torus norm-residue pairing: for lifts $1+x,1+y$, its value on $xy-yx$ is the commutator of their lifts. The residue-torus weights show that the linear defect is a coboundary unless it is invariant under $t\mapsto t^2$. In the invariant dyadic line, the reduced-norm equation

$$
\operatorname{Nrd}(1+x)=1+\operatorname{Trd}(x)+\operatorname{Nrd}(x)
\tag{9.9}
$$

moves the obstruction to the next layer, where (9.7) treats it. Thus the sole obstruction at each stage is the scalar norm-residue class. If that class is zero, downward induction gives a splitting on $U_D^1$.

This is precisely Lemma 9.2 applied at $j=r-1,r-2,\ldots,1$. The downward induction is finite before reaching $U_D^1$; the inverse limit in the lemma is needed only to choose the initial splitting uniformly as the finite representative is refined.

The quotient (9.5) is cyclic. Any remaining extension of it is a Bockstein of a character and vanishes in the reduced multiplier. Hence a scalar-zero class is zero, proving injectivity.

Conversely, let $\xi\in H^2(k,A_n)$. On $T_L$ use the restriction of $s_\xi$; on each $U_D^j/U_D^{j+1}$ define the commutator pairing by the trace form

$$
(x,y)\longmapsto s_\xi(1+\operatorname{Trd}(xy),\pi),
\tag{9.10}
$$

interpreted at the first layer where the argument is nontrivial. Equations (9.7) and (9.9) show that adjacent definitions agree. They therefore define a central extension of $T_LU_D^1$. The two cyclic-coordinate cells

$$
T_LU_D^1,
\qquad
(T_LU_D^1)(1+y\Pi)(T_LU_D^1)
\tag{9.11}
$$

cover $D^1$: solve (9.2) for the $L$-coordinate and use Hensel lifting on the unit part. On their overlap, the two multiplication laws differ by the Steinberg relation for $s_\xi$. They glue to a Moore extension of $D^1$.

To see the cover directly, let $g=x+y\Pi\in D^1$. If $x$ is a unit, multiply on the left and right by elements of $T_L$ to make its residue one; equation (9.2) then places the result in $U_D^1$. If $x$ is not a unit, (9.2) forces $y$ to have the minimal valuation permitted by $\pi N(y)$; multiplying by a fixed norm-one representative in the second cell makes the new $L$-coordinate a unit, reducing to the first case. Hensel lifting corrects each residue normalization because the norm-one equation defines a smooth group scheme on these unit cells; in coordinates, one chooses a partial derivative not annihilated by the reduced-trace functional. The intersection formula obtained by performing the two reductions in reverse order is (4.6) after scalar extension to $L$, and its descended central discrepancy is $s_\xi(a,1-a)=1$.

If $E\subset D$ is another maximal field, choose a regular element $z\in E^1$. A neighborhood of $z$ meets the second cell in (9.11), and the glued formula restricts to $s_\xi|_{E^1}$. Regular elements are dense in $E^1$, so continuity gives the assertion on the whole torus. This also proves independence of $L$. After a splitting field extension, (9.11) becomes the two Bruhat cells used in Chapter 8, so the two classifications agree. $\square$

### 9.4 Why restriction--corestriction is insufficient

It is tempting to split $D$ over a quadratic extension $L$, apply Theorem 8.1, and descend by restriction--corestriction. That proves at most

$$
\operatorname{cor}_{L/k}\operatorname{res}_{L/k}(\alpha)=2\alpha.
\tag{9.12}
$$

It loses precisely the two-primary information which survives over a totally real field. It also does not show that a split extension invariant under $\operatorname{Gal}(L/k)$ admits descent data satisfying the cocycle condition. The direct radical-filtration proof of Theorem 9.1 supplies both missing facts. Equation (9.12) is a compatibility check, not the proof.

## 10. Products, cross terms, and restricted products

### 10.1 The product decomposition

Let $L_1$ and $L_2$ be locally compact second-countable groups, and let $E$ be a central extension of $L_1\times L_2$ by $\mathbf T$. Restriction gives extensions $E_i$ of $L_i$. Choose lifts $\widetilde g_1$ and $\widetilde g_2$ of $(g_1,1)$ and $(1,g_2)$. Since these elements commute in the quotient, their commutator lies in the central circle. Put

$$
\beta_E(g_1,g_2)=[\widetilde g_1,\widetilde g_2].
\tag{10.1}
$$

The value is independent of the chosen lifts. The commutator identities with a central commutator give

$$
\beta_E(g_1g_1',g_2)
=\beta_E(g_1,g_2)\beta_E(g_1',g_2),
$$

and similarly in the second variable. It is measurable, hence continuous by applying Lemma 5.1 to either variable and then the standard separate-to-joint continuity argument for homomorphisms. It factors through the topological abelianizations

$$
L_i^{\mathrm{ab,top}}
=L_i/\overline{[L_i,L_i]}.
\tag{10.2}
$$

Conversely, a continuous bicharacter $\beta:L_1^{\mathrm{ab,top}}\times L_2^{\mathrm{ab,top}}\to\mathbf T$ defines the cocycle

$$
c_\beta((g_1,g_2),(h_1,h_2))=\beta(h_1,g_2).
\tag{10.3}
$$

Its factor restrictions are split and its cross commutator is $\beta$.

**Proposition 10.1 (two-factor decomposition).** There is a natural split exact sequence

$$
0\to
\operatorname{Bich}_{\mathrm{cont}}
(L_1^{\mathrm{ab,top}},L_2^{\mathrm{ab,top}};\mathbf T)
\to H^2_{\mathrm m}(L_1\times L_2,\mathbf T)
\to H^2_{\mathrm m}(L_1,\mathbf T)\oplus H^2_{\mathrm m}(L_2,\mathbf T)
\to0.
\tag{10.4}
$$

The first arrow is (10.3), and the splitting takes the Baer sum of the two inflated factor extensions.

**Proof.** After subtracting the inflated factor restrictions from $E$, both factor restrictions split. Choose those splittings. Every element of the resulting extension is uniquely a central scalar times a lift from the first factor times a lift from the second. Multiplication is then determined by commuting the second lift past the first, and the sole defect is (10.1). This identifies the remaining extension with (10.3). $\square$

Iterating gives one local multiplier for each factor and one bicharacter for each unordered pair. Thus separate local restrictions never, by themselves, classify an extension of a product.

### 10.2 Cross-bicharacters

For norm-one quaternionic groups the full split local factors are topologically perfect, while their compact open subgroups can have small finite character quotients and a division factor can have a visible compact abelianization. Formula (9.5) already exhibits a cyclic residue quotient before commutators from deeper layers are imposed. It is therefore unsafe to declare all cross terms zero from local perfectness.

The exact local generation statement is simple. In a split factor,

$$
[h(a),x(t)]=x((a^2-1)t).
\tag{10.4a}
$$

Choose $a\in k^\times$ with $a^2\ne1$. As $t$ varies, the right side gives the entire upper root group; the lower root group follows similarly, and the two root groups generate $\operatorname{SL}_2(k)$. Thus its topological abelianization is trivial. At the few finite residue quotients encountered when one restricts to a compact subgroup, any surviving character is already included in the Bockstein convention.

In a division factor, every $g\ne\pm1$ lies in the norm-one torus of the quadratic field $k[g]\subset D$. The central elements also lie in every maximal torus. Hence the images of maximal tori generate $D^1$ and therefore its topological abelianization. This observation, rather than a claim that $D^1$ is perfect, is what is used below.

Here is a concrete construction. Let $\alpha:L_1\to A_n$ and $\gamma:L_2\to A_n$ be nonzero continuous characters and let $\langle\ ,\ \rangle:A_n\times A_n\to\mathbf T$ be a nontrivial pairing. Then

$$
c((g_1,g_2),(h_1,h_2))
=\langle\alpha(h_1),\gamma(g_2)\rangle
\tag{10.5}
$$

defines an extension whose restrictions to $L_1$ and $L_2$ are both split. The extension is nevertheless nontrivial because its cross commutator is the induced bicharacter. Any restricted-product theorem which lists only factor multipliers must explain why (10.5) is excluded.

### 10.3 Diagonal splitting kills cross terms

The relevant exclusion is global, not local. We work in the category of adelic extensions split over diagonal $H(F)$.

**Lemma 10.2 (commuting torus approximation).** Let $w_1\ne w_2$ be finite places. For $i=1,2$, let $g_i\in H(F_{w_i})$ have prescribed image in a finite quotient of $H(F_{w_i})^{\mathrm{ab,top}}$. There is a quadratic field $E/F$ embedded in $B$ and elements $t_1,t_2\in E^1$ such that:

1. the image of $t_i$ at $w_i$ equals the prescribed image of $g_i$;
2. the image of $t_i$ is trivial in the finite abelian quotient prescribed at the other place;
3. both elements meet arbitrary fixed open integral conditions away from $w_1,w_2$.

**Proof.** At a split place, every finite abelian quotient is generated by images of regular diagonal tori and the finitely many small residue classes. At a division place, (9.5)--(9.7) show that the topological abelianization is generated by the residue norm-one torus; deeper additive layers are commutators except for a possible dyadic line, which is also represented by a ramified quadratic torus through (9.9). Thus choose local quadratic étale algebras $E_i/F_{w_i}$ and norm-one elements representing the desired classes.

At a split place the preceding perfectness calculation actually makes the prescribed class trivial, so any regular split or nonsplit torus may be used there. At a division place the fact that every element belongs to a quadratic torus represents the class without first computing the entire abelianization. This also covers the dyadic layers.

The embedding criterion of Book 77 says that a quadratic field embeds in $B$ precisely when it remains a field at every ramified place. Choose a global quadratic polynomial approximating the defining polynomials of $E_i$ at $w_i$, irreducible at every ramified place, and split or inert as required at the finitely many auxiliary places. Weak approximation supplies its coefficients, and avoiding its discriminant zero locus makes it a field $E$ with an embedding in $B$.

The norm-one torus $E^1$ is a smooth rational conic once it has the point $1$. Parametrizing it by

$$
z(r)=\frac{1+r\theta}{1+r\bar\theta}
\tag{10.6}
$$

reduces the two element choices to weak approximation for $r\in F$, with finitely many denominators required to be units. Book 4's weak approximation and the denominator-clearing argument used in Lemma 4.3 give $t_1,t_2$ with the stated local images and integral conditions. $\square$

**Theorem 10.3 (no cross terms in the diagonal-split category).** Let $E$ be a finite-order Moore extension of a finite product

$$
\prod_{w\in T}H(F_w)
$$

which is the restriction of an extension of $G^S$ split over diagonal $H(F)$. Then every cross-bicharacter in Proposition 10.1 is trivial.

**Proof.** Fix $w_1\ne w_2$ and let $\beta$ be the cross-bicharacter. Since the class has finite order, $\beta$ has finite image and factors through finite quotients of the two topological abelianizations. Choose arbitrary classes $\bar g_i$ in those quotients. Lemma 10.2 supplies commuting global elements $t_1,t_2\in E^1\subset H(F)$ whose relevant local components represent $\bar g_1$ and $\bar g_2$, while all unwanted finite quotient components are trivial.

The adelic extension has a homomorphic splitting $s:H(F)\to E$. Since $t_1t_2=t_2t_1$ in the global torus,

$$
[s(t_1),s(t_2)]=s([t_1,t_2])=1.
\tag{10.7}
$$

Compute the same commutator using the factor decomposition. All local factor commutators occur at a single place and cancel after replacing one of the two elements there by its prescribed trivial class; all other cross terms are trivial by construction. The remaining value is $\beta(\bar g_1,\bar g_2)$. Hence it equals one. The two classes were arbitrary, so $\beta=1$. $\square$

The proof uses commuting rational approximants, not merely density of $H(F)$. Arbitrary rational approximants need not commute, and the commutator of their chosen splitting lifts would then be the lift of a nontrivial rational commutator rather than a cross term.

### 10.4 Passage to a restricted product

Let $\alpha$ be a finite-order Moore extension of $G^S$. Continuity at the identity gives a finite set $T$ and open subgroups $U_w\subset K_w^0$ for $w\in T$ such that a representative cocycle is trivial on

$$
\prod_{w\in T}U_w\times\prod_{w\notin S\cup T}K_w^0.
\tag{10.8}
$$

After a coboundary, its restriction to $K_w^0$ is the distinguished unramified splitting for every $w\notin S\cup T$. For a finite set $T'\supset T$, Proposition 10.1 decomposes the restriction to the product of the $T'$ local factors. Theorem 10.3 kills every cross term if $\alpha$ splits on $H(F)$. Enlarging $T'$ is compatible with the distinguished splittings. We obtain:

**Theorem 10.4 (restricted-product decomposition).** In the finite-order diagonal-split extension category, an adelic extension is determined by its local reduced multiplier classes

$$
\alpha_w\in\overline H^2_n(H(F_w))
\qquad(w\notin S),
\tag{10.9}
$$

together with the standard hyperspecial splittings outside a finite set. There are no cross-bicharacter parameters. If every local multiplier class is zero and the hyperspecial splittings are compatible, then the adelic extension is zero.

**Proof.** Existence of the decomposition follows by applying Proposition 10.1 on increasing finite products and using (10.8). Theorem 10.3 removes pair terms at every finite stage. If all factor classes vanish, choose compatible factor splittings, normalized to be the distinguished ones away from $T$. Their restricted product is a continuous global splitting because every adele lies in $K_w^0$ for almost all $w$. $\square$

The phrase compatible hyperspecial splittings is essential. Changing infinitely many local splittings by characters may destroy continuity of their product even though each local change is continuous.

## 11. Adelic globalization and scalar reduction

### 11.1 Local invariants of an adelic extension

Let $\alpha\in M^S(H)[n]$. By Theorems 8.1 and 9.1, every local factor $w\notin S$ has a scalar class

$$
\xi_w(\alpha)\in H^2(F_w,A_n).
\tag{11.1}
$$

At almost every split place the extension and its hyperspecial splitting are unramified. The raw family $(\xi_w)$ need not have finite support before normalization: a coherent global Hilbert-symbol cover can have the same unramified rule at infinitely many places. What has finite support is its deviation from a global scalar rule.

There is also a relative datum. Choose a finite $A_n$ lift on a reference compact open and a splitting $s:H(F)\to E$ of the circle extension. On a global quadratic torus $T\subset H$, compare $s|_{T(F)}$ with the product of the normalized local torus splittings used in Chapters 8 and 9. Their quotient is an $A_n$-valued scalar $1$-cochain on $T(F)$. Its coboundary measures the failure of the raw local scalar family to have finite support. Changing the finite lift or the normalized rational comparison changes this cochain by a global scalar $2$-class. Thus the datum which will enter $Q_n(F)$ consists of the local multiplier classes together with this rational comparison, not of an unadorned infinite tuple.

We make this precise. A **coherent scalar family away from $S$** is a family $(\xi_w)_{w\notin S}$ arising from a restricted-product extension with distinguished hyperspecial splittings, equipped with its rational comparison cochain. Two such data are equivalent if their comparison cochains differ by a class in $H^2(F,A_n)$; on local scalar coordinates this adds its localization. A datum is normalized if its resulting local coordinate is zero outside a finite set.

**Lemma 11.1 (finite-support normalization).** Every coherent scalar family whose quaternionic extension splits over $H(F)$ is equivalent to a normalized family. Any two normalized representatives differ by the localization of a global class and hence determine one element of

$$
Q_n(F)=\operatorname{coker}\!\left[
H^2(F,A_n)\longrightarrow
\bigoplus_wH^2(F_w,A_n)
\right].
\tag{11.2}
$$

The missing coordinates at $w\in S$ can be chosen so that the resulting class in (11.2) is independent of every choice.

**Proof.** Choose a finite set $T$ supporting the nonstandard local splittings in (10.8). At $w\notin S\cup T$, the local class is determined by its value on one uniformizer--unit pair and is unramified in the sense of Theorem 7.1. Diagonal splitting gives the product-one relation for every pair $a,b\in F^\times$ inserted in a common global maximal torus. Lemma 10.2 and weak approximation let $a$ and $b$ prescribe an arbitrary uniformizer--unit pair at one new place while remaining units with trivial detected class at the preceding places. Consequently the unramified tail is a single global scalar rule: its values on Frobenius elements are the localizations of one finite Galois cohomology class. Subtract that global class. The remaining family vanishes outside $S\cup T$.

In terms of comparison cochains, “subtract” means change the normalized comparison between the rational splitting and the product of local splittings. It does not mean Baer-sum the adelic extension with a new extension. The underlying adelic class is unchanged.

At the places of $S$, the same product-one relation determines the sum of the missing local evaluations. Two choices differ by a family orthogonal to every diagonal Kummer class. The finite arithmetic-duality exact sequence of Book 6 says precisely that changing such a choice changes the full tuple by a global localization. Thus it gives the same cokernel element. If two finite-support normalizations were chosen, their difference has zero pairing with every diagonal Kummer class, and the same exactness identifies it with a global class. $\square$

Only the last orthogonality identification in this proof is imported from Book 6. The reduction of a group extension to a coherent scalar family used the local classification and Theorem 10.3.

The construction can be used as an explicit globalization protocol:

1. lift an $n$-torsion circle extension to finite coefficients on one reference compact open using (5.6);
2. normalize upper and lower root lifts at every split factor and radical-filtration lifts at every division factor;
3. record the resulting ordered local scalar symbols, retaining the even-primary defect;
4. compare their product with the chosen splitting on rational maximal tori;
5. use commuting torus approximation to remove cross terms and to identify a single global comparison cochain;
6. change that comparison by a global $H^2(F,A_n)$ class until the remaining tuple has finite support;
7. take its class in (11.2).

Every arrow in this protocol is reversible up to the displayed equivalence. That reversibility, not merely the existence of local invariants, is what makes injectivity possible.

### 11.2 The scalar class

Define

$$
\operatorname{sc}_n(\alpha)
=[(\xi_w(\alpha))_w]\in Q_n(F)
\tag{11.3}
$$

using Lemma 11.1. Baer sum adds local defects, and changing a finite-coefficient lift through Theorem 5.3 adds the Bockstein of local characters. Those Bocksteins assemble into a global scalar localization because the original extension splitting on $H(F)$ changes by a rational character. Hence (11.3) is a well-defined homomorphism

$$
\operatorname{sc}_n:M^S(H)[n]\longrightarrow Q_n(F).
\tag{11.4}
$$

When $\mu_n\subset F_w$, the split local normalization can be checked on diagonal tori by

$$
[\widetilde h(a),\widetilde h(b)]
=\chi_w((a,b)_{w,n}^{2}),
\tag{11.5}
$$

but the definition of $\operatorname{sc}_n$ uses the ordered symbol, not only this commutator. At a division place it uses Theorem 9.1 directly. When roots of unity are absent, it uses the Galois-equivariant norm-residue class in $H^2(F_w,A_n)$.

If $m\mid n$, coefficient reduction $A_n\to A_m$ commutes with the Bockstein sequence, the two local classifications, rational comparison, and localization. Therefore

$$
\operatorname{sc}_m(\alpha^{n/m})
=\operatorname{red}_{n,m}(\operatorname{sc}_n(\alpha)).
\tag{11.5a}
$$

These compatibilities are what allow the separate torsion-layer bounds to control the entire metaplectic kernel.

### 11.3 Injectivity

**Theorem 11.2 (injective scalar reduction).** For every $n\ge1$, the map

$$
\operatorname{sc}_n:M^S(H)[n]\hookrightarrow Q_n(F)
\tag{11.6}
$$

is injective.

**Proof strategy.** Normalize a zero scalar cokernel class to zero at every place without changing the adelic extension. The split and division detection theorems then split every factor, the no-cross theorem makes the factor splittings multiplicative, and the rational comparison turns their remaining character discrepancy into one continuous adelic character.

**Proof.** Suppose $\operatorname{sc}_n(\alpha)=0$ and choose a finite $A_n$ representative on a reference compact level as in Theorem 5.3. By definition of the cokernel, a global class $\eta\in H^2(F,A_n)$ has localizations equal to the normalized relative scalar coordinate of $\alpha$.

Change the rational comparison cochain by a representative of $\eta$. This is one of the equivalences in Lemma 11.1 and does not alter the adelic extension class. After the change, every relative local scalar coordinate is zero. At a split factor, the detection statement following Theorem 8.1 produces a normalized local splitting. At a division factor, injectivity in Theorem 9.1 and Lemma 9.2 produce one as well. At almost all places these are the distinguished hyperspecial splittings.

There could still be two obstructions to multiplying the local splittings: cross-bicharacters and incompatible character changes. Theorem 10.3 removes the first. For the second, compare the product splitting with the fixed rational splitting on each global maximal torus. The comparison is a character because all scalar $2$-defects have been normalized to zero. Maximal tori generate every local factor, while commuting torus approximation makes the characters agree on overlaps. They therefore form one restricted-product continuous character of $G^S$. Adjust the product splitting by its inverse. It now agrees with the rational splitting on $H(F)$ and is a continuous global splitting of the extension. Thus $\alpha=0$. $\square$

There are four separate injectivity inputs in this proof: local detection at split factors, local detection at division factors, disappearance of cross-bicharacters, and the global character quotient. Omitting any one leaves a possible nonzero extension with zero scalar tuple.

One can see the last point on splittings. Suppose all local multiplier classes vanish. A choice of local splittings gives, for $g=(g_w)$,

$$
s_{\mathrm{loc}}(g)=\prod_ws_w(g_w),
\tag{11.6a}
$$

where the product is finite because $s_w$ is distinguished on $K_w^0$ almost everywhere. Another choice has the form $\chi_ws_w$ with local characters $\chi_w$. The product $\prod_w\chi_w(g_w)$ is continuous only when the characters are trivial on a common hyperspecial product outside a finite set. The rational comparison forces precisely this restricted-product condition. The stem property then ensures that a character which is invisible on $K$ cannot reappear on the congruence kernel. Thus the character correction in the proof is a genuine continuous adelic character, not a formal infinite product.

### 11.4 The global scalar cokernel

Book 6 proves, with the real Tate modifications included, the canonical perfect-duality identification

$$
Q_n(F)
\xrightarrow{\sim}
\operatorname{Hom}(\mu_n(F),\mathbf D).
\tag{11.7}
$$

When $\mu_n\subset F$, this is the Hilbert-symbol product formula and exact annihilator theorem. For general $F$, it is the same finite arithmetic duality with $A_n$ and $\mu_n$ retained as distinct Galois modules. No primitive $n$th root is chosen.

Combining (11.6) and (11.7) gives

$$
M^S(H)[n]
\hookrightarrow
\operatorname{Hom}(\mu_n(F),\mathbf D).
\tag{11.8}
$$

This is an injection, not an assertion that every scalar cokernel class is realized by the chosen inner form and omitted set. Surjectivity is unnecessary for the congruence-kernel bound and can fail when additional local splitting conditions are imposed.

## 12. Totally real fields and routed odd-primary vanishing

### 12.1 The exponent bound

First let $F$ be arbitrary. Its group of roots of unity $\mu(F)$ is finite cyclic; write

$$
m_F=|\mu(F)|.
\tag{12.0a}
$$

If $\alpha\in M^S(H)$ has order $n$, injectivity of (11.8) places the cyclic subgroup it generates inside $\operatorname{Hom}(\mu_n(F),\mathbf D)$. The latter has exponent $|\mu_n(F)|=\gcd(n,m_F)$. Therefore $n$ divides $m_F$. Every element of $M^S(H)$ lies in $M^S(H)[m_F]$, and applying (11.8) once with $n=m_F$ gives

$$
\exp M^S(H)\mid m_F,
\qquad
|M^S(H)|\le m_F.
\tag{12.0b}
$$

Perfect duality and Lemma 12.1 below give the same statements for $C^S(H)$. Thus the rank-two congruence kernel is finite over every number field in the present quaternionic range; the totally real case makes its bound especially sharp.

Assume now that $F$ is totally real. Its roots of unity are

$$
\mu(F)=\{\pm1\}.
\tag{12.1}
$$

Indeed, a root of unity in a real embedding is a real root of unity, hence $1$ or $-1$; an algebraic number is determined by one embedding. Therefore

$$
\mu_n(F)=
\begin{cases}
\{1\},&n\text{ odd},\\
\{\pm1\},&n\text{ even}.
\end{cases}
\tag{12.2}
$$

Equations (11.8) and (12.2) imply

$$
M^S(H)[n]=0\quad(n\text{ odd}),
\qquad
|M^S(H)[n]|\le2\quad(n\text{ even}).
\tag{12.3}
$$

The group $M^S(H)$ is torsion by Theorem 6.2. Alternatively, the general bound (12.0b) applies with $m_F=2$. There is no odd-primary torsion, and hence

$$
|M^S(H)|\le2,
\qquad
2M^S(H)=0.
\tag{12.4}
$$

### 12.2 Recovering the congruence kernel from its dual

Perfect duality (6.9) now gives $|C^\vee|\le2$. We must still pass from characters to the profinite group itself.

**Lemma 12.1 (character separation).** If $P$ is a profinite abelian group, its continuous finite-order characters separate points. If $P^\vee$ is finite, the evaluation map

$$
P\longrightarrow(P^\vee)^\vee
\tag{12.5}
$$

is an isomorphism. In particular $|P|=|P^\vee|$.

**Proof.** For $x\ne1$, choose an open normal subgroup $U$ not containing $x$. The image of $x$ in the finite abelian group $P/U$ is nontrivial. Characters of a finite abelian group separate points, so one of them, composed with $P\to P/U$, detects $x$. This proves injectivity of (12.5). If $P^\vee$ is finite, the intersection of the kernels of its finitely many characters is open and, by separation, trivial. Thus $P$ is finite. Ordinary finite Pontryagin duality makes (12.5) bijective and preserves order. $\square$

Apply the lemma to the central group $C$. We obtain

$$
|C^S(H)|\le2,
\qquad
2C^S(H)=0.
\tag{12.6}
$$

This deduction uses both perfect pairing and injective scalar reduction. A roots-of-unity count without them would bound only $Q_n(F)$.

### 12.3 Every routed spectator level

Let $K$ be any compact open subgroup of $G^S$. Lemma 3.1 identifies $C(K)$ as a group with $C^S(H)$. The conjugation action of $\widehat{\Gamma(K)}$ on its normal kernel gives a continuous map

$$
\widehat{\Gamma(K)}\longrightarrow\operatorname{Aut}(C^S(H)).
\tag{12.7}
$$

A group of order one or two has trivial automorphism group. Thus (12.7) is trivial. Consequently $C(K)$ is central for every compact open $K$, including levels not placed below the original reference level. This conclusion is now valid because of (12.6), not because of open-level invariance alone.

If $A$ is a finite abelian group of odd order, then

$$
\operatorname{Hom}_{\mathrm{cont}}(C(K),A)=0.
\tag{12.8}
$$

More generally, the topological abelianization of $C(K)$ has no odd-primary quotient. Since $C(K)$ itself is central, it has no nontrivial finite odd-primary quotient at all.

Every actual route of Section 3.3 acts on the common kernel through an automorphism. That action is trivial by (12.6). Hence principal, tame, ray, auxiliary, permutation, and adjoint-companion spectator changes all carry the same central kernel with trivial routing action. This is stronger than vanishing after descent invariants or localization: it kills the entire odd-primary character group before either operation.

## 13. Examples and failure tests

### 13.1 The rational indefinite example

Take $F=\mathbf Q$ and let $B$ be a quaternion division algebra split at the real place and at a finite place $v$. Put $S=\{\infty,v\}$. Then

$$
\operatorname{rk}_S\operatorname{SL}_1(B)=1+1=2.
$$

For maximal level away from $v$, the arithmetic group is the norm-one group of an order with $v$ inverted. Theorem 4.6 makes its full congruence kernel central and stem. Since $\mu(\mathbf Q)=\{\pm1\}$, (12.6) gives a kernel of order at most two. The theorem does not choose between the trivial group and $C_2$; that choice depends on whether the metaplectic double class survives the imposed local splitting conditions.

At an odd coefficient prime $\ell$, every homomorphism from this kernel to a finite $\ell$-group is zero. This remains true after adding any finite collection of tame principal levels away from $v$, after passing to a ray-trivializing cover, and after returning through a prime-to-$\ell$ descent group.

### 13.2 A division spectator place

Let $w\notin S$ be a finite place at which $B_w$ is division. The local compact group $H(F_w)=\mathcal O_{B,w}^{1}$ has the residue quotient

$$
\ker(\kappa_{w^2}^\times\to\kappa_w^\times)
$$

of order $q_w+1$. It can therefore have nontrivial continuous characters, especially at primes dividing $q_w+1$. Such a character contributes a Bockstein to finite-coefficient $H^2$ and can also form a cross extension like (10.5) with a second division factor.

The comparison theorem handles the first phenomenon by quotienting Bocksteins in (5.6). The diagonal rational splitting handles the second by Theorem 10.3. Simply calling the local group compact or an inner form of $\operatorname{SL}_2$ would handle neither.

### 13.3 Density without continuity

The abstract group $\mathbf Z$ embeds densely in $\mathbf Z_p$. Choose a prime $q\ne p$ and map $1\in\mathbf Z$ to $1\in\mathbf Z/q$. This homomorphism cannot extend continuously to $\mathbf Z_p$, because every continuous finite quotient of the pro-$p$ group $\mathbf Z_p$ is a $p$-group. Thus a dense arithmetic subgroup can possess finite characters invisible to its congruence completion.

The quaternionic theorem does not deny this general phenomenon. It proves, by the rank-two ideal-commutator argument and metaplectic duality, that the invisible abelian characters in the present group have only the possible two-primary residue dictated by global roots of unity.

### 13.4 Kernel invariance without centrality

Let $C=C_3$ and let $Q=C_2$ act on it by inversion. The semidirect product $E=C_3\rtimes C_2$ maps onto $C_2$ with kernel $C_3$. Over the identity subgroup of the quotient, the same kernel is the entire preimage and is central. In $E$ it is not central. Passing to an open subgroup and then identifying kernels therefore cannot transport centrality back to a larger group.

At routed quaternionic levels, centrality first descends from an actual reference completion or travels through an actual conjugation isomorphism. At completely arbitrary levels it is obtained only after the order bound makes $\operatorname{Aut}(C)$ trivial.

### 13.5 Roots of unity without duality

Let $P$ be any nonabelian finite group with large order and trivial character group, for example a nonabelian finite simple group. The fact that $P^\vee=0$ says nothing about $|P|$. Even for abelian groups, a map from some unrelated cohomology group into a two-element group does not bound $P$ unless that cohomology group is proved to be the full Pontryagin dual of $P$.

Our order proof has the exact sequence

$$
C^\vee\overset{\sim}{\longrightarrow}M^S(H)
\hookrightarrow Q_n(F)
\overset{\sim}{\longrightarrow}\operatorname{Hom}(\mu_n(F),\mathbf D)
$$

on every torsion layer. The first arrow is perfect duality, the second is injective scalar reduction, and only the last is the roots-of-unity calculation. Removing either of the first two invalidates (12.6).

## 14. The geometric Ihara corollary

### 14.1 The exact routed family

We now state the arithmetic export in the notation needed for a geometric Ihara argument. Let $\mathscr R$ be a finite family of constant-coefficient degeneracy rows. A row $R$ consists of:

1. a totally real field $F_R$;
2. a quaternion division algebra $B_R/F_R$ split at exactly one real place and at a changing finite place $v_R$;
3. the actual tame, ray, auxiliary, permutation, and adjoint-companion spectator levels away from $v_R$;
4. a full routed component orbit indexed by $c$, with compact open norm-one levels $K_{R,c}^{v_R}$;
5. a prime-to-$\ell$ descent group $\Delta_R$ and a non-Eisenstein maximal ideal $\mathfrak m_R$.

Put

$$
\Gamma_{R,c}=H_R(F_R)\cap K_{R,c}^{v_R},
\qquad
C_{R,c}=\ker\!\left[
\widehat{\Gamma_{R,c}}\twoheadrightarrow K_{R,c}^{v_R}
\right].
\tag{14.1}
$$

The routed component notation matters: one does not replace the direct sum over components by cohomology of an unmentioned product, and one does not discard the actions before proving vanishing.

The levels in this definition are the levels that actually occur after geometric reductions. Component representatives conjugate the initial maximal compact to $g_cK^*g_c^{-1}$. A tame type is replaced by its finite flag-permutation resolution, producing several open subgroups inside that conjugate. A scalar tame character is trivialized on a global ray cover rather than on a nominal local line, and an auxiliary principal level removes stabilizers. Adjoint companions add the dual flag row. Each operation changes only finitely many local factors, so every resulting $K_{R,c}^{v_R}$ satisfies the routed containment (3.4).

The component and fine-cover descent group $\Delta_R$ acts through the rational and adelic routes just described. Before the totally real bound, its action on the common kernel would have to be retained. After (12.6), it is trivial because it factors through $\operatorname{Aut}(C^S(H))$. Thus the arithmetic theorem applies simultaneously to the constant vertex, edge, permutation, quotient, augmentation, and adjoint-companion rows without replacing any of their actual spectator levels by a convenient maximal one.

The earlier geometric theory supplies the meaning of these rows: finite étale descent supplies the covers, component routing supplies their rational corrections, the semistable rank-two model supplies the vertex and edge curves, and the integral type lattices supply the flag resolutions. None of those geometric results is used to prove centrality or metaplectic duality. They determine only the finite family to which the uniform arithmetic conclusion is applied.

### 14.2 Odd-primary abelian Ihara

Let $\ell$ be odd and let $A$ be a finite $\ell$-primary trivial module. Theorem 12.3 gives, for every row and component,

$$
\operatorname{Hom}_{\mathrm{cont}}(C_{R,c},A)=0.
\tag{14.2}
$$

In particular the transgression kernel vanishes before taking routed invariants:

$$
\ker\!\left[
\operatorname{Hom}_{\mathrm{cont}}(C_{R,c},A)^{K_{R,c}^{v_R}}
\xrightarrow{\operatorname{tg}_{R,c,A}}
H^2_{\mathrm{cont}}(K_{R,c}^{v_R},A)
\right]=0.
\tag{14.3}
$$

For the residue field $k_R$ this implies the exact localized sum

$$
\left(
\left(
\bigoplus_c
\ker\!\left[
\operatorname{Hom}_{\mathrm{cont}}(C_{R,c},k_R)^{K_{R,c}^{v_R}}
\xrightarrow{\operatorname{tg}_{R,c,k_R}}
H^2_{\mathrm{cont}}(K_{R,c}^{v_R},k_R)
\right]
\right)^{\Delta_R}
\right)_{\mathfrak m_R}=0.
\tag{14.4}
$$

This is exactly the routed localized odd-primary abelian congruence assertion. No non-Eisenstein calculation is needed to prove (14.4); non-Eisensteinness belongs to its subsequent geometric use, where it removes the congruence-continuous character summand.

### 14.3 The exported corollary

**Corollary 14.1 (uniform routed geometric Ihara input).** Fix an odd prime $\ell$ and a finite routed family $\mathscr R$. Assume at every row the following seven hypotheses of the saturated geometric Ihara setting:

1. the totally real compact quaternionic Shimura-curve datum just described;
2. a proper stable component union at neat level, or prime-to-$\ell$ descent from one;
3. hyperspecial level at the split changing place and standard Iwahori edge level;
4. the verified flat self-dual rank-two incidence local model;
5. $\ell\ge7$ and $v_R\nmid\ell$;
6. trivial central and component action on the selected Hecke-stable block, with the stated unnormalized operator convention;
7. a non-Eisenstein maximal ideal.

Then (14.2)--(14.4) hold at every actual tame, ray, auxiliary, permutation, and adjoint-companion spectator level. Equivalently, the routed abelian Ihara hypothesis holds at every row before component descent and Hecke localization.

**Proof.** For each distinct triple $(F_R,B_R,v_R)$, the split real place and $v_R$ give $S$-rank two. Theorem 15.1 below applies. Equations (12.6) and (14.2) kill the entire odd-primary character group of every full congruence kernel. Taking $K$-invariants, transgression kernels, direct sums, $\Delta_R$-invariants, and localization preserves zero, giving (14.4). $\square$

This is the exact arithmetic corollary consumed by saturated geometric Ihara: its tree sequence identifies (14.4) with the remaining localized noncongruence-character kernel. Once its independent geometric hypotheses hold, zero in (14.4) gives residual injectivity of the two degeneracy maps; finite-free curve cohomology then turns that injectivity into an integral saturated image and a finite-free new quotient. The component, monodromy, branch-correction, adjunction, and routing statements retain their own geometric hypotheses. None of those geometric assertions is used in proving Corollary 14.1.

This corollary proves more arithmetic vanishing than the geometry consumes, but it does not enlarge the geometric range. It does not verify a node-uniformization bijection, construct an automorphic packet, handle a primitive wild type, or remove a branch Smith correction. Those are different inputs.

## 15. The reusable rank-two theorem

### 15.1 Main theorem

**Theorem 15.1 (congruence kernels and metaplectic duality for quaternionic groups).** Let $F$ be a number field, let $B/F$ be a quaternion algebra, let $H=\operatorname{SL}_1(B)$, and let $S\supset V_\infty(F)$ be finite. Assume:

1. $H(F)$ is dense in $G^S=H(\mathbf A_F^S)$;
2. at least two places in $S$ split $B$, equivalently $\operatorname{rk}_S H\ge2$ in the quaternionic case.

For any compact open $K\subset G^S$, put $\Gamma(K)=H(F)\cap K$ and

$$
C(K)=\ker(\widehat{\Gamma(K)}\twoheadrightarrow K).
$$

Then:

1. For a reference integral level $K^*$, $C(K^*)$ is central in $\widehat{\Gamma(K^*)}$ and lies in the closure of its commutator subgroup. The proof is the rank-two ideal-commutator theorem, not a congruence-subgroup assumption.
2. Every open subgroup of a conjugate reference level has the same kernel, transported through the actual inclusion and conjugation maps, and that kernel is central in its completion.
3. With $\mathbf T=\mathbf R/\mathbf Z$ and discrete topology on $H(F)$ in the restriction target, pushout and adelic induction give a canonical isomorphism
   $$
   C(K^*)^\vee\xrightarrow{\sim}
   M^S(H)=\ker\!\left[
   H^2_{\mathrm m}(G^S,\mathbf T)\to H^2(H(F),\mathbf T)
   \right].
   $$
   It is a perfect Pontryagin pairing.
4. The comparison between continuous finite-coefficient extensions and Moore circle extensions is the exact sequence (5.6). In particular, finite second cohomology is not inserted into circle second cohomology; the Bocksteins of continuous characters are quotiented.
5. At every finite split place, the reduced $n$-torsion multiplier of $\operatorname{SL}_2(F_w)$ is canonically $H^2(F_w,A_n)$ through the full Steinberg symbol. If $\mu_n\subset F_w$, its torus commutator is the square of the $n$th Hilbert symbol. The full symbol, rather than that square, retains the even-primary class.
6. At every finite division place, the reduced $n$-torsion multiplier of $\operatorname{SL}_1(B_w)$ is canonically $H^2(F_w,A_n)$. This is proved directly from cyclic coordinates and the radical filtration, including the two-primary part.
7. In the restricted-product extension category split over diagonal $H(F)$, all cross-bicharacter terms vanish. Local multiplier classes, compatible hyperspecial splittings, and the rational splitting determine the extension.
8. The metaplectic kernel is torsion, and for every $n$ there is a natural compatible injection
   $$
   \operatorname{sc}_n:M^S(H)[n]
   \hookrightarrow
   Q_n(F)
   \simeq\operatorname{Hom}(\mu_n(F),\mathbf D),
   $$
   where the last isomorphism is the scalar arithmetic-duality theorem of Book 6.
   Consequently, if $m_F=|\mu(F)|$, both $M^S(H)$ and $C(K)$ are finite of order at most $m_F$ and exponent dividing $m_F$.
9. If $F$ is totally real, then
   $$
   |M^S(H)|=|C(K)|\le2
   $$
   for every compact open $K$. The common kernel is central at every such level, every routed action on it is trivial, and
   $$
   \operatorname{Hom}_{\mathrm{cont}}(C(K),A)=0
   $$
   for every finite odd-primary abelian group $A$.

### 15.2 Proof assembly

**Proof.** Strong approximation identifies the congruence completion with $K$ in (2.7). Lemma 3.1 identifies the full kernels at commensurable levels without making a centrality assertion. The two split places give the rational root approximation, contraction, and relative generation of Chapter 4. Theorem 4.5 proves both the ideal-commutator and abelian congruence assertions. Lemmas 4.1 and 4.2 then prove reference centrality and the stem property, giving clauses 1 and 2.

Chapters 5 and 6 separate the coefficient topologies. The exact coefficient sequence (5.6), compact transgression, the proved stem property, and the central relative $S$-arithmetic completion identify every continuous character of $C$ with one and only one adelic Moore extension split on discrete $H(F)$. This proves clauses 3 and 4 and also proves torsion of the metaplectic kernel.

The root presentation and the all-primary topological symbol theorem prove the split local classification. The cyclic-coordinate and radical-filtration calculation proves the division classification without losing the two-primary part. Proposition 10.1 lists the possible product cross terms, while commuting global torus approximation makes every one of them trivial in the diagonal-split category. This proves clauses 5--7.

The local classifications produce a coherent scalar family. Lemma 11.1 normalizes it modulo global scalar classes and places it in $Q_n(F)$. Theorem 11.2 proves injectivity by changing the global comparison and then using local detection, no cross terms, and the character quotient. Book 6 identifies the scalar cokernel with the dual of $\mu_n(F)$. Every torsion order then divides $|\mu(F)|$, and the single torsion layer at that exponent has order at most $|\mu(F)|$. Perfect duality transfers the bound to $C$, proving clause 8.

For totally real $F$, the only roots of unity are $\pm1$. Thus every odd torsion layer of $M^S(H)$ vanishes and every even torsion layer has order at most two. Torsion makes the whole group have order at most two. Perfect duality and continuous character separation give the same bound for $C$. Its automorphism group is trivial, so centrality and trivial routing hold at every commensurable compact open, not only below a reference level. Odd-primary character vanishing follows. This proves clause 9. $\square$

### 15.3 Conclusion

The congruence kernel is the exact record of finite arithmetic quotients invisible in the adelic level. In quaternionic $S$-rank two it is controlled neither by density alone nor by an assumed full congruence subgroup property. The control comes from a sequence of sharper statements: ideal commutators make the kernel central, the abelian congruence theorem makes it stem, coefficient comparison turns compact transgression into circle-valued extensions, and the adelic induction theorem makes that comparison perfect.

Local rank one still remembers both forms of the quaternion algebra. Split factors are governed by root lifts and Steinberg symbols. Division factors require their own radical-filtration calculation. Products introduce genuine cross-bicharacters, removed only because a rational splitting supplies enough commuting global tori. Once those steps are complete, the group-theoretic extension reduces injectively to the scalar local-global cokernel. Global arithmetic duality then permits roots of unity to speak.

Over a totally real field they say exactly what is needed: the full congruence kernel has order at most two. That statement is uniform under every open spectator change, and its odd-primary character group vanishes before descent, invariants, or localization. The result is therefore a reusable arithmetic input for any rank-two quaternionic construction whose geometric argument isolates the same full profinite-to-congruence kernel.
