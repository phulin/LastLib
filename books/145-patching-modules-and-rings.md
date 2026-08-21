# Patching Modules and Rings

## Contents

1. [Why patching is necessary](#1-why-patching-is-necessary)
   - [The finite-level bargain](#11-the-finite-level-bargain)
   - [The object sought at infinite level](#12-the-object-sought-at-infinite-level)
   - [Standing hypotheses and notation](#13-standing-hypotheses-and-notation)
   - [Three rings that must not be conflated](#14-three-rings-that-must-not-be-conflated)
2. [The auxiliary power-series algebra](#2-the-auxiliary-power-series-algebra)
   - [The completed group algebra](#21-the-completed-group-algebra)
   - [Level ideals and their convergence to zero](#22-level-ideals-and-their-convergence-to-zero)
   - [Artinian precision ideals](#23-artinian-precision-ideals)
   - [The fixed deformation presentation](#24-the-fixed-deformation-presentation)
   - [The dimension and variable ledger](#25-the-dimension-and-variable-ledger)
3. [Why the arithmetic levels do not form a tower](#3-why-the-arithmetic-levels-do-not-form-a-tower)
   - [Unrelated auxiliary sets](#31-unrelated-auxiliary-sets)
   - [Common sources are not transition maps](#32-common-sources-are-not-transition-maps)
   - [What a finite shadow must remember](#33-what-a-finite-shadow-must-remember)
   - [Finiteness of the marked shadow sets](#34-finiteness-of-the-marked-shadow-sets)
4. [Diagonal compactness and coherent shadows](#4-diagonal-compactness-and-coherent-shadows)
   - [The finite-tree argument](#41-the-finite-tree-argument)
   - [Compatibility, not merely repeated isomorphism types](#42-compatibility-not-merely-repeated-isomorphism-types)
   - [Hecke labels, pairings, and generators](#43-hecke-labels-pairings-and-generators)
   - [What the pseudo-transitions mean](#44-what-the-pseudo-transitions-mean)
5. [Inverse limits and the patched rings](#5-inverse-limits-and-the-patched-rings)
   - [The exactness lemma for finite inverse systems](#51-the-exactness-lemma-for-finite-inverse-systems)
   - [Patching the relation tuple](#52-patching-the-relation-tuple)
   - [Construction of the patched deformation ring](#53-construction-of-the-patched-deformation-ring)
   - [The patched action algebra](#54-the-patched-action-algebra)
   - [Completeness, locality, and finite generation](#55-completeness-locality-and-finite-generation)
6. [The patched module and freeness over $S_\infty$](#6-the-patched-module-and-freeness-over-s_infty)
   - [A limit lemma for finite free modules](#61-a-limit-lemma-for-finite-free-modules)
   - [Construction of $M_\infty$](#62-construction-of-m_infty)
   - [Why rank counting is not a proof](#63-why-rank-counting-is-not-a-proof)
   - [A clean free Taylor--Wiles system](#64-a-clean-free-taylor--wiles-system)
7. [Augmentation and exact recovery](#7-augmentation-and-exact-recovery)
   - [Recovery of the deformation ring](#71-recovery-of-the-deformation-ring)
   - [Recovery of the minimal-level module](#72-recovery-of-the-minimal-level-module)
   - [The acting algebra at augmentation](#73-the-acting-algebra-at-augmentation)
   - [Ordinary tensor products, completed tensor products, and limits](#74-ordinary-tensor-products-completed-tensor-products-and-limits)
   - [Tor and regular-sequence criteria](#75-tor-and-regular-sequence-criteria)
8. [Balanced modules and perfect complexes](#8-balanced-modules-and-perfect-complexes)
   - [What balancedness actually patches](#81-what-balancedness-actually-patches)
   - [The correct depth statements](#82-the-correct-depth-statements)
   - [Patching bounded perfect complexes](#83-patching-bounded-perfect-complexes)
   - [Amplitude, homology, and specialization](#84-amplitude-homology-and-specialization)
   - [Criteria that really upgrade to freeness](#85-criteria-that-really-upgrade-to-freeness)
   - [A balanced but nonfree finite-level module](#86-a-balanced-but-nonfree-finite-level-module)
9. [Dimension bookkeeping and the Taylor--Wiles cancellation](#9-dimension-bookkeeping-and-the-taylor--wiles-cancellation)
   - [Dimensions of the source rings](#91-dimensions-of-the-source-rings)
   - [Relations and lower bounds](#92-relations-and-lower-bounds)
   - [Where the dual-Selmer defect disappears](#93-where-the-dual-selmer-defect-disappears)
   - [Forcing equality](#94-forcing-equality)
   - [Complete-intersection consequences](#95-complete-intersection-consequences)
10. [Depth over the three acting rings](#10-depth-over-the-three-acting-rings)
    - [The regular sequence supplied by $S_\infty$](#101-the-regular-sequence-supplied-by-s_infty)
    - [Depth over the action algebra](#102-depth-over-the-action-algebra)
    - [Depth over the patched deformation ring](#103-depth-over-the-patched-deformation-ring)
    - [Maximal Cohen--Macaulay conclusions](#104-maximal-cohen--macaulay-conclusions)
    - [When freeness over the deformation ring follows](#105-when-freeness-over-the-deformation-ring-follows)
11. [Support, components, and annihilators](#11-support-components-and-annihilators)
    - [The exact support](#111-the-exact-support)
    - [A union of components versus every component](#112-a-union-of-components-versus-every-component)
    - [Faithful and nearly faithful actions](#113-faithful-and-nearly-faithful-actions)
    - [Nilpotent-sensitive faithfulness criteria](#114-nilpotent-sensitive-faithfulness-criteria)
    - [Two failures: a missed component and a killed thickening](#115-two-failures-a-missed-component-and-a-killed-thickening)
12. [Perfect pairings and adjoints after patching](#12-perfect-pairings-and-adjoints-after-patching)
    - [Pairing-compatible finite shadows](#121-pairing-compatible-finite-shadows)
    - [Passage of perfectness to the limit](#122-passage-of-perfectness-to-the-limit)
    - [Adjoint Hecke actions](#123-adjoint-hecke-actions)
    - [What self-duality does and does not say](#124-what-self-duality-does-and-does-not-say)
13. [Frames and harmless power-series variables](#13-frames-and-harmless-power-series-variables)
    - [The framed variable count](#131-the-framed-variable-count)
    - [Descent along a regular smooth sequence](#132-descent-along-a-regular-smooth-sequence)
    - [Padding variables are different](#133-padding-variables-are-different)
    - [The framed-to-unframed patched pair](#134-the-framed-to-unframed-patched-pair)
14. [Choices, genuine towers, and uniqueness](#14-choices-genuine-towers-and-uniqueness)
    - [Coordinate and basis changes](#141-coordinate-and-basis-changes)
    - [Dependence on the diagonal subsequence](#142-dependence-on-the-diagonal-subsequence)
    - [The genuine-transition variant](#143-the-genuine-transition-variant)
    - [The common exported axioms](#144-the-common-exported-axioms)
15. [Failure modes and a hostile audit](#15-failure-modes-and-a-hostile-audit)
    - [Failure of uniform size](#151-failure-of-uniform-size)
    - [Diamond nonfreeness and torsion](#152-diamond-nonfreeness-and-torsion)
    - [Bad limits and incompatible structures](#153-bad-limits-and-incompatible-structures)
    - [Insufficient depth and hidden components](#154-insufficient-depth-and-hidden-components)
    - [Ineffective relation bounds](#155-ineffective-relation-bounds)
    - [The final audit ledger](#156-the-final-audit-ledger)
16. [The patched-pair theorem package](#16-the-patched-pair-theorem-package)
    - [The free-module theorem](#161-the-free-module-theorem)
    - [The balanced and derived theorem](#162-the-balanced-and-derived-theorem)
    - [The exact interface for the next argument](#163-the-exact-interface-for-the-next-argument)
    - [Conclusion](#164-conclusion)
17. [Paired source patching and support transfer](#17-paired-source-patching-and-support-transfer)
    - [The unique-horizontal support lemma](#171-the-unique-horizontal-support-lemma)
    - [Coefficient-power nilpotents](#172-coefficient-power-nilpotents)
    - [The paired source-patching theorem](#173-the-paired-source-patching-theorem)
    - [Module augmentation and finite-level factorization](#174-module-augmentation-and-finite-level-factorization)
    - [Exact acting-image augmentation under saturation](#175-exact-acting-image-augmentation-under-saturation)
    - [Why patching the source changes the argument](#176-why-patching-the-source-changes-the-argument)

## 1. Why patching is necessary

### 1.1 The finite-level bargain

The preceding construction produces, for every integer $N\geq 1$, an auxiliary set $Q_N$ and a collection of rings and modules

$$
\Lambda_N=\mathcal O[\Delta_N]
\longrightarrow R_N\longrightarrow\mathbb T_N
\longrightarrow\operatorname{End}_{\mathcal O}(M_N).
\tag{1.1}
$$

Here $\mathcal O$ is a complete discrete valuation ring with uniformizer $\varpi$ and finite residue field $k$ of characteristic $\ell$. The exact-level diamond group is

$$
\Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
\tag{1.2}
$$

where

$$
q=\dim_k H^1_{\mathcal L^\perp}(K,W^*(1))
\tag{1.3}
$$

is the original dual-Selmer dimension. The auxiliary condition kills that dual Selmer group. In exchange, it introduces $q$ finite character directions, recorded by $\Delta_N$. Augmentation removes those directions and recovers the original objects:

$$
R_N/\mathfrak a_NR_N\simeq R,
\qquad
M_N/\mathfrak a_NM_N\simeq M,
\tag{1.4}
$$

and, under the Hecke saturation hypothesis included in a controlled system,

$$
\mathbb T_N/\mathfrak a_N\mathbb T_N\simeq\mathbb T.
\tag{1.5}
$$

The point of patching is to keep the benefit of the auxiliary symmetry while making its finite order tend to infinity. A module free over $\mathcal O[\Delta_N]$ has a large supply of exact scalar directions, but at a fixed $N$ those directions satisfy the finite-order equations

$$
(1+z_i)^{\ell^N}-1=0.
\tag{1.6}
$$

As $N$ grows, these equations vanish to arbitrarily high adic order. Patching extracts a limit in which the equations have disappeared and the diamond algebra has become a regular power-series ring. That regular ring supplies the long regular sequence from which depth and freeness are obtained.

This summary hides the chief difficulty. The sets $Q_N$ are unrelated. There is generally no map $R_{N+1}\to R_N$, no map $M_{N+1}\to M_N$, and no geometric level-forgetting operation between them. An inverse limit cannot be taken until compatible finite shadows have been manufactured without pretending that such arithmetic maps exist. The compactness construction that performs this manufacturing is the logical center of the subject.

### 1.2 The object sought at infinite level

The clean output consists of three related objects.

First, there is a patched deformation ring $R_\infty$ receiving maps from the fixed old-place local ring and from the completed diamond algebra. It is a quotient of one fixed presentation ring and specializes exactly to $R$ at augmentation.

Second, there is a patched module $M_\infty$. In the strongest version it is finite free of a fixed rank $r$ over the completed diamond algebra. It is finite over $R_\infty$, and augmentation recovers $M$.

Third, there is a faithfully acting algebra $A_\infty$, obtained as the image of the patched action on $M_\infty$. The action factors as

$$
R_\infty\twoheadrightarrow A_\infty
\lhook\joinrel\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty).
\tag{1.7}
$$

When a compatible Hecke algebra is retained, $A_\infty$ is the patched Hecke action algebra and may be denoted $\mathbb T_\infty$. Defining it as an image makes its action faithful. It does not make the map from $R_\infty$ injective.

These three objects answer different questions. The presentation of $R_\infty$ carries the deformation-theoretic relation bound. The regular ring $S_\infty$ carries freeness and depth. The quotient $A_\infty$ records the actual support of the module. Treating them as one ring would turn several later conclusions into assumptions.

The augmented target square is

$$
\begin{array}{ccc}
R_\infty&\twoheadrightarrow&A_\infty\\
\downarrow&&\downarrow\\
R&\longrightarrow&\mathbb T,
\end{array}
\tag{1.8}
$$

together with the structural maps $R_{\mathrm{loc}}\to R_\infty$ and $S_\infty\to R_\infty\to A_\infty$, and with $M_\infty/\mathfrak a_\infty M_\infty\simeq M$. The left vertical map and the module quotient are exact augmentation recoveries built into the coherent shadows and proved by an inverse-limit argument. The right vertical map always induces a surjection $A_\infty/\mathfrak a_\infty A_\infty\twoheadrightarrow\mathbb T$; it induces an isomorphism only under the saturation statement proved or assumed for the acting algebras.

### 1.3 Standing hypotheses and notation

Fix a controlled presentation-compatible Taylor--Wiles system of Book 144. Thus the following data are available for every $N$.

1. The group $\Delta_N$ has the form (1.2), after a chosen ordering and a chosen generator in every cyclic factor.
2. The ring $R_N$ is a complete Noetherian local $\mathcal O$-algebra, equipped with maps from $R_{\mathrm{loc}}$ and $\Lambda_N$.
3. The finite module $M_N$ carries compatible $R_N$, $\mathbb T_N$, and $\Lambda_N$ actions, with $R_N\twoheadrightarrow\mathbb T_N$ and faithful $\mathbb T_N$-action.
4. The augmentation comparisons (1.4) hold and are compatible with every named action. When (1.5) is used, it is separately included.
5. In the free version, $M_N$ is $\Lambda_N$-free of one fixed positive rank $r$.
6. The rings $R_N$ admit presentations from one fixed source with one uniform bound $b$ on the relative relations after the finite-level diamond equations are removed.
7. Old local components, determinant conventions, frame counts, Hecke labels, and pairing normalizations do not vary with $N$.

The free-module construction will be developed first. The balanced and perfect-complex forms will then be stated with their weaker conclusions and their genuinely additional hypotheses.

The imported foundations are precisely earlier results. Book 144 supplies the controlled presentation-compatible systems, the fixed diamond and deformation sources, the uniform padded relation bound, and the coherent finite-shadow data. Book 69 supplies the effective relative deformation presentations from which that bound originates. Book 70 supplies the regular-sequence, depth, Auslander--Buchsbaum, finite-map, complete-intersection, support, and Fitting-ideal results used after the patched objects have been constructed. The finite-tree compactness, Mittag--Leffler lifting, limiting-kernel calculation, augmentation comparison, and paired support-transfer statements needed here are proved in this book rather than assumed as a patching interface.

Every ring homomorphism is continuous and local. Every module called finite is finitely generated. Inverse limits carry their inverse-limit topologies. For a complete local ring $B$ with maximal ideal $\mathfrak m_B$, a quotient described as a finite shadow is always an Artinian quotient by an explicitly stated open ideal; no untruncated infinite ring is inserted into a finite diagram.

### 1.4 Three rings that must not be conflated

Book 144 used the symbol $R_\infty$ for a common power-series source. Here it is useful to reserve $R_\infty$ for the actual patched quotient and to rename that source

$$
P_\infty
=R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]].
\tag{1.9}
$$

The three rings are therefore:

$$
P_\infty\twoheadrightarrow R_\infty
\twoheadrightarrow A_\infty.
\tag{1.10}
$$

The first is a chosen presentation ring. The second retains the limiting deformation relations. The third is the image on the patched module. Their kernels have different meanings:

$$
\ker(P_\infty\to R_\infty)
=\text{patched deformation equations},
\tag{1.11}
$$

whereas

$$
\ker(R_\infty\to A_\infty)
=\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{1.12}
$$

Some accounts call the source $P_\infty$ the patched deformation ring. That convention is harmless only if every subsequent statement remembers that its augmentation gives a presentation of $R$, rather than automatically giving $R$ itself. The convention (1.10) makes exact recovery and annihilators visible at the cost of one extra symbol.

## 2. The auxiliary power-series algebra

Patching succeeds only because every finite diamond algebra is presented by one regular complete ring and because its finite-order equations vanish at increasing adic precision. This chapter fixes the two filtrations that will later be used for rings and modules, then records the ambient deformation presentation in a way that keeps diamond, smooth, global, and framing coordinates separate.

### 2.1 The completed group algebra

Let

$$
\Gamma=\mathbf Z_\ell^q
$$

with ordered topological generators $\gamma_1,\ldots,\gamma_q$. Its completed group algebra is

$$
S_\infty=\mathcal O[[\Gamma]]
\simeq\mathcal O[[z_1,\ldots,z_q]],
\qquad
\gamma_i\longmapsto1+z_i.
\tag{2.1}
$$

It is a complete regular local ring with maximal ideal

$$
\mathfrak n_\infty=(\varpi,z_1,\ldots,z_q)
\tag{2.2}
$$

and dimension

$$
d_S:=\dim S_\infty=q+1.
\tag{2.3}
$$

Its augmentation is

$$
\epsilon_\infty:S_\infty\longrightarrow\mathcal O,
\qquad z_i\longmapsto0,
\tag{2.4}
$$

with ideal

$$
\mathfrak a_\infty=(z_1,\ldots,z_q).
\tag{2.5}
$$

When $q=0$, the group $\Gamma$ is trivial, $S_\infty=\mathcal O$, and both $\mathfrak a_\infty$ and every $\mathfrak c_N$ are zero. All arguments below remain valid with empty regular sequences; patching then concerns only the bounded deformation presentations and their module actions.

After choosing generators for $\Delta_N$, the finite diamond algebra is the quotient

$$
S_N=S_\infty/\mathfrak c_N
\xrightarrow{\sim}\Lambda_N,
\tag{2.6}
$$

where

$$
\mathfrak c_N=\bigl(
(1+z_1)^{\ell^N}-1,\ldots,
(1+z_q)^{\ell^N}-1
\bigr).
\tag{2.7}
$$

The sequence in (2.7) is $S_\infty$-regular. Quotienting one variable at a time leaves a finite free module with basis $1,z_i,\ldots,z_i^{\ell^N-1}$ over the power-series ring in the remaining variables. Consequently

$$
\operatorname{rank}_{\mathcal O}S_N=\ell^{Nq},
\tag{2.8}
$$

and $S_N$ is a one-dimensional complete-intersection local ring, finite flat over $\mathcal O$.

### 2.2 Level ideals and their convergence to zero

The phrase “the level equations tend to zero” has a precise adic meaning.

**Lemma 2.1 (vanishing of the level ideals).** For every open ideal $U\subset S_\infty$, there is an $N(U)$ such that

$$
\mathfrak c_N\subseteq U
\qquad(N\geq N(U)).
\tag{2.9}
$$

**Proof.** It is enough to take $U=\mathfrak n_\infty^d$. For one generator,

$$
(1+z)^{\ell^N}-1
=\sum_{j=1}^{\ell^N}\binom{\ell^N}{j}z^j.
\tag{2.10}
$$

If $\mathcal O$ has equal characteristic $\ell$, then

$$
(1+z)^{\ell^N}-1=z^{\ell^N},
$$

which belongs to $\mathfrak n_\infty^d$ once $\ell^N\geq d$. Suppose instead that $\mathcal O$ has mixed characteristic. Terms in (2.10) with $j\geq d$ already lie in $\mathfrak n_\infty^d$. For each of the finitely many $1\leq j<d$, the $\varpi$-adic valuation of $\binom{\ell^N}{j}$ tends to infinity with $N$. Hence the corresponding term eventually lies in $\varpi^{d-j}z^j\subseteq\mathfrak n_\infty^d$. The same bound may be chosen for all $q$ generators. $\square$

The lemma does not say that the ideals $\mathfrak c_N$ are nested after transport to the arithmetic group rings. It says that each separately chosen level equation becomes invisible at every fixed finite precision. That is exactly what diagonal patching needs.

### 2.3 Artinian precision ideals

For the module construction it is convenient to use the ideals

$$
\mathfrak b_d=(\varpi^d,z_1^d,\ldots,z_q^d)
\subset S_\infty
\qquad(d\geq1).
\tag{2.11}
$$

They are nested and cofinal with the powers of $\mathfrak n_\infty$. Indeed,

$$
\mathfrak b_d\subseteq\mathfrak n_\infty^d,
\tag{2.12}
$$

while every monomial of total degree greater than $(q+1)(d-1)$ has at least one exponent at least $d$, so

$$
\mathfrak n_\infty^{(q+1)(d-1)+1}\subseteq\mathfrak b_d.
\tag{2.13}
$$

Put

$$
C_d=S_\infty/\mathfrak b_d.
\tag{2.14}
$$

The ring $C_d$ is finite Artinian local. Lemma 2.1 also gives

$$
\mathfrak c_N\subseteq\mathfrak b_d
\tag{2.15}
$$

for all sufficiently large $N$. At such a level,

$$
S_N/\mathfrak b_dS_N\simeq C_d.
\tag{2.16}
$$

The special form of $\mathfrak b_d$ makes augmentation transparent:

$$
C_d/\mathfrak a_\infty C_d\simeq\mathcal O/\varpi^d.
\tag{2.17}
$$

One could work with powers of $\mathfrak n_\infty$ instead. The two filtrations give the same completion. The ideals (2.11) are chosen because (2.17) and free module reduction are immediate.

### 2.4 The fixed deformation presentation

Let $(R_{\mathrm{loc}},\mathfrak m_{\mathrm{loc}})$ be the fixed completed product of old-place local deformation rings, with one fixed component and one fixed framing convention at every level. Let

$$
P_\infty
=R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]]
\tag{2.18}
$$

and write $\mathfrak p_\infty$ for its maximal ideal. There are structural maps

$$
R_{\mathrm{loc}}\longrightarrow P_\infty,
\qquad
S_\infty\longrightarrow P_\infty,
\tag{2.19}
$$

or equivalently one map

$$
R_{\mathrm{loc}}\widehat\otimes_{\mathcal O}S_\infty
\longrightarrow P_\infty.
\tag{2.20}
$$

For every $N$, the chosen presentation-compatible system gives a surjection

$$
\beta_N:P_\infty\twoheadrightarrow R_N
\tag{2.21}
$$

whose restriction to $S_\infty$ is the diamond map and whose restriction to $R_{\mathrm{loc}}$ is the fixed local restriction map. The kernel has a marked presentation

$$
\ker\beta_N
=\mathfrak c_NP_\infty+(f_{N,1},\ldots,f_{N,b}).
\tag{2.22}
$$

The uniform integer $b$ is the padded relative relation bound of Book 144. If fewer relations are required, zero entries may be appended only after every unused source variable has been killed by a genuine linear relation. Thus (2.22) is a statement about an actual chosen generating tuple, not a count inferred from a tangent dimension.

The variables $x_i$ contain three kinds of coordinates: auxiliary Frobenius-eigenvalue coordinates, auxiliary or global frame coordinates when retained, and global relative tangent coordinates over the chosen local base. Their total number $G$ must be read from one convention. Moving an auxiliary smooth coordinate from the base into the relative presentation changes both ledgers and does not change the total ring.

There is also a fixed augmented presentation

$$
\beta_0:P_0:=P_\infty/\mathfrak a_\infty P_\infty
=R_{\mathrm{loc}}[[x_1,\ldots,x_G]]
\twoheadrightarrow R.
\tag{2.23}
$$

Compatibility means that augmenting (2.21) and using $R_N/\mathfrak a_NR_N\simeq R$ gives (2.23). This compatibility at every finite precision is what will prove, rather than merely suggest, the exact identity $R_\infty/\mathfrak a_\infty R_\infty\simeq R$.

### 2.5 The dimension and variable ledger

Put

$$
d_{\mathrm{loc}}=\dim R_{\mathrm{loc}}.
$$

Then

$$
\dim P_\infty=d_{\mathrm{loc}}+q+G.
\tag{2.24}
$$

If $R_{\mathrm{loc}}$ is regular, so is $P_\infty$. If $R_{\mathrm{loc}}$ is Cohen--Macaulay, so is $P_\infty$. If $R_{\mathrm{loc}}$ is a complete intersection, adjoining these power-series variables preserves that property. None of those hypotheses follows merely from the notation $R_{\mathrm{loc}}$.

The rank-two auxiliary local contribution used in this Taylor--Wiles system is as follows.

| coordinate type                       | unframed auxiliary place | framed auxiliary place |
| ------------------------------------- | -----------------------: | ---------------------: |
| finite diamond direction              |                      $1$ |                    $1$ |
| smooth eigenvalue coordinate          |                      $1$ |                    $1$ |
| smooth eigenline-position coordinates |                      $0$ |                    $2$ |

Thus $q$ auxiliary places contribute $q$ variables to $S_\infty$, together with $q$ or $3q$ smooth coordinates outside the diamond algebra according to the local convention. A partial framing at a fixed old-place set $T$ contributes

$$
c_T=d^2|T|-h^0(K,\operatorname{ad}\bar\rho)
\tag{2.25}
$$

smooth directions in rank $d$. For an absolutely irreducible rank-two representation this is $4|T|-1$. The case of one global frame gives three variables; it is not three new variables for every place in addition to (2.25).

The dimension formula (2.24) counts all these smooth variables exactly once. The relation bound $b$ excludes the $q$ finite-level equations $\mathfrak c_N$, because those equations disappear in the patched limit. This separation is the numerical reason patching can improve depth.

## 3. Why the arithmetic levels do not form a tower

An inverse limit is meaningful only after its transition maps have been named. The arithmetic input normally supplies a family rather than a tower, so the first task is negative but essential: determine which maps do not exist. Once that boundary is clear, finite presentation shadows can provide exactly the comparison data that are needed and no more.

### 3.1 Unrelated auxiliary sets

For a fixed finite place $v$, the integer $v_\ell(q_v-1)$ is finite. Hence $v$ satisfies

$$
q_v\equiv1\pmod{\ell^N}
$$

only for finitely many $N$. If every $Q_N$ has the fixed cardinality $q>0$, inclusions $Q_N\subseteq Q_{N+1}$ would force equality and hence force the same places to satisfy congruences of unbounded depth. This is impossible.

In fact, the prime-selection theorem permits the $Q_N$ to be pairwise disjoint. This is often convenient, but it makes the absence of transition maps visible. A deformation allowed to ramify at $Q_{N+1}$ does not naturally become a deformation allowed to ramify at the disjoint set $Q_N$. A module built from level structure at $Q_{N+1}$ has no automatic map to a module built from level structure at $Q_N$.

The abstract group quotients do admit chosen maps

$$
(\mathbf Z/\ell^{N+1}\mathbf Z)^q
\twoheadrightarrow(\mathbf Z/\ell^N\mathbf Z)^q.
\tag{3.1}
$$

After choosing generators, these maps transport to the $\Delta_N$. They compare coordinate groups. They do not compare the residue fields, decomposition groups, deformation conditions, or geometric levels at the underlying primes.

### 3.2 Common sources are not transition maps

The presentations

$$
P_\infty\twoheadrightarrow R_N,
\qquad
S_\infty\twoheadrightarrow\Lambda_N
\tag{3.2}
$$

put all levels under common sources. Two quotients of one ring need not map to one another. A map $P/I\to P/J$ compatible with the quotient maps exists precisely when $I\subseteq J$. No containment between the kernels in (2.22) is supplied by arithmetic.

Likewise, choosing $S_{N+1}\twoheadrightarrow S_N$ says nothing about the non-diamond coordinates of $R_{N+1}$ and $R_N$. Extending the chosen group-algebra quotient to a map of deformation rings would assert that ramification at one set of places can be functorially transferred to another. That assertion is generally false.

Patching therefore uses the following pattern:

$$
\begin{array}{ccccc}
\text{arithmetic level }N_1&&\text{arithmetic level }N_2&&\cdots\\
\downarrow&&\downarrow&&\\
\text{finite model at precision }1&\longleftarrow&
\text{finite model at precision }2&\longleftarrow&\cdots.
\end{array}
\tag{3.3}
$$

The vertical arrows are chosen identifications of finite shadows. The horizontal arrows are genuine reductions between the chosen models. There are no horizontal arrows in the top row.

### 3.3 What a finite shadow must remember

A ring quotient alone is not enough. At precision $d$, the shadow must retain every structure intended to survive in the limit:

- the quotient of the marked presentation ring $P_\infty$ and the images of the relation generators;
- the quotient $C_d$ of $S_\infty$ and its named coordinates;
- the module, with a chosen generating tuple or basis in the free case;
- the maps from $R_{\mathrm{loc}}$ and $S_\infty$;
- the action of the deformation ring and the acting image algebra;
- the first $d$ members of any enumerated common Hecke family;
- the augmentation maps to finite quotients of $R$, $\mathbb T$, and $M$;
- a companion module, an involution, and a pairing matrix when duality is retained;
- the reductions of all this data to every lower precision.

There are two useful filtrations. The deformation ring and its relation tuple are truncated by a cofinal sequence of powers of $\mathfrak p_\infty$. The module is truncated by $\mathfrak b_d$, because that quotient preserves the finite-level free structure. These filtrations need not have matching indices.

To combine them, choose an increasing function $\nu(d)$ such that the action of $P_\infty$ on

$$
M_N/\mathfrak b_dM_N
\tag{3.4}
$$

factors through $P_\infty/\mathfrak p_\infty^{\nu(d)}$ for every sufficiently large $N$. Such a uniform $\nu(d)$ exists. The module in (3.4) is free of rank $r$ over the fixed finite ring $C_d$, so its $C_d$-linear endomorphism ring is finite. The local image of $P_\infty$ has nilpotent maximal ideal, with nilpotence exponent bounded in terms of this finite endomorphism ring. A sufficiently large power of $\mathfrak p_\infty$ therefore acts by zero. Enlarging $\nu(d)$ makes it increasing and cofinal.

At precision $d$ we may consequently retain both

$$
R_N/\mathfrak p_\infty^{\nu(d)}R_N
\tag{3.5}
$$

and (3.4), together with the action map from (3.5) to the endomorphisms of (3.4). The target of an augmentation map is also truncated: (3.5) maps to the quotient of $R$ by the image of $\mathfrak p_\infty^{\nu(d)}$, while (3.4) maps to $M/\varpi^dM$. This prevents an infinite object from being smuggled into the finite-pigeonhole argument.

### 3.4 Finiteness of the marked shadow sets

**Proposition 3.1 (finite presentation sets).** Fix $d$. Among all sufficiently large $N$ satisfying $\mathfrak c_N\subseteq\mathfrak b_d$, only finitely many marked precision-$d$ diagrams of the kind just described can occur.

**Proof.** The ring $P_\infty/\mathfrak p_\infty^{\nu(d)}$ is finite because $P_\infty$ is Noetherian local with finite residue field. Its quotients are classified by ideals in a finite set. A marked list of at most $b$ relation classes is a tuple in a finite ring.

The module (3.4) is, after choosing a basis, $C_d^r$. Both $C_d^r$ and its endomorphism ring are finite. Hence there are only finitely many possible action homomorphisms, subalgebras, named endomorphisms, generating tuples, and module maps. A bilinear pairing is a finite matrix, and perfectness is a condition on that matrix, so only finitely many pairing shadows occur. Every truncated augmentation target is finite as well. Finally, only the first $d$ entries of an infinite named Hecke family are retained. The product of these finitely many finite choices is finite. $\square$

The set is nonempty for every $d$: Lemma 2.1 ensures that infinitely many levels lie beyond the required precision, and every such level supplies a diagram. The proposition would fail without the uniform rank $r$, the uniform relation bound $b$, or a uniform bound on the number of module generators. Those bounds are compactness hypotheses, not cosmetic numerical conveniences.

## 4. Diagonal compactness and coherent shadows

At a fixed precision, all bounded presentation data live in a finite set. Compactness turns the repeated finite approximations into one compatible path through all precisions. The compatibility of reductions, rather than recurrence of isolated isomorphism types, is what creates a legitimate inverse system.

### 4.1 The finite-tree argument

Repeated occurrence of an isomorphism type at each precision is not yet enough. The types must reduce compatibly. The clean construction is a finitely branching tree.

At depth $d$, take the marked precision-$d$ diagrams that occur for infinitely many sufficiently large levels. Join a vertex at depth $d+1$ to its reduction at depth $d$. The set of vertices at each depth is finite by Proposition 3.1 and nonempty by repeated pigeonhole selection. Every vertex kept in the pruned tree is required to have descendants at arbitrarily large depths. Thus the tree is infinite and finitely branching.

**Lemma 4.1 (coherent diagonal path).** The pruned tree has an infinite path

$$
\mathscr D_1\longleftarrow\mathscr D_2
\longleftarrow\mathscr D_3\longleftarrow\cdots
\tag{4.1}
$$

whose arrows are the actual quotient maps of the marked finite models.

**Proof.** At depth one, at least one vertex has descendants of arbitrarily large depth; otherwise finitely many bounded depths would bound the whole tree. Choose such a vertex. Among its finitely many children, one again has descendants of arbitrarily large depth. Continue. The chosen children form the path (4.1). $\square$

This is the finite form of compactness. Equivalently, one may view the product of the finite discrete sets of marked choices as compact and intersect the nested nonempty cylinder conditions expressing compatibility. The tree proof shows explicitly where nonemptiness and finite branching enter.

One can simultaneously choose a cofinal subsequence

$$
N_1<N_2<\cdots
\tag{4.2}
$$

such that for every $j\geq d$, the precision-$d$ shadow of level $N_j$ is identified with $\mathscr D_d$. Begin with an infinite set of levels realizing $\mathscr D_1$, refine to an infinite subset realizing $\mathscr D_2$ with the selected reduction, and continue. Taking the $j$th element from the $j$th subset gives (4.2).

### 4.2 Compatibility, not merely repeated isomorphism types

Automorphisms create a subtle gap if one records only unmarked isomorphism classes. Suppose a precision-two object reduces to something isomorphic to the selected precision-one object in several ways. Choosing a new isomorphism independently at every stage can make the composites disagree, so no inverse system results.

There are two safe remedies. One may mark every finite object by its quotient map from the fixed source and, in the free case, by an ordered basis. Then reduction is literal. Or one may retain the reduction isomorphism as part of the finite data and refine the subsequence until that isomorphism stabilizes. The automorphism set of a finite diagram is finite, so the second refinement costs no compactness.

We use marked objects. Thus (4.1) includes commutative squares

$$
\begin{array}{ccc}
P_\infty/\mathfrak p_\infty^{\nu(d+1)}&\longrightarrow&\mathscr R_{d+1}\\
\downarrow&&\downarrow\\
P_\infty/\mathfrak p_\infty^{\nu(d)}&\longrightarrow&\mathscr R_d,
\end{array}
\tag{4.3}
$$

and

$$
C_d\otimes_{C_{d+1}}\mathscr M_{d+1}
\xrightarrow{\sim}\mathscr M_d.
\tag{4.4}
$$

Every action, augmentation map, and named operator commutes with these arrows. Compatibility in (4.3) and (4.4), not similarity of cardinalities, is what permits an inverse limit.

### 4.3 Hecke labels, pairings, and generators

An away-from-level Hecke family is usually countable rather than finite. Enumerate its common labels as

$$
t_1,t_2,t_3,\ldots.
\tag{4.5}
$$

At precision $d$, retain only $t_1,\ldots,t_d$. If a fixed label is absent because its place lies in $Q_N$, discard the finitely many offending levels or use the pairwise-disjoint choice, for which every fixed place is auxiliary at most once. The diagonal path then retains every label eventually.

Relation generators require the same treatment. The ordered tuple

$$
(f_{N,1},\ldots,f_{N,b})
\tag{4.6}
$$

is part of the marked ring shadow. Stabilization of its reductions produces compatible elements at all precisions, not merely a uniform assertion that some generating tuple exists.

For a group-ring-valued perfect pairing, reduce both modules and the value ring by $\mathfrak b_d$. Sesquilinearity makes the quotient pairing well defined, and projectivity makes it perfect after base change. Its matrix is included in the marked shadow. A coefficient-valued pairing does not automatically descend to these two quotient modules; a dual filtration or separately supplied pairing shadow is required. Compactness preserves pairing data that have been defined. It does not manufacture a descended pairing.

### 4.4 What the pseudo-transitions mean

The arrows in (4.1) are genuine surjections among the selected finite models. They are called pseudo-transitions only to emphasize their relation to the original arithmetic family. There is generally no diagram

$$
R_{N_{j+1}}\longrightarrow R_{N_j},
\qquad
M_{N_{j+1}}\longrightarrow M_{N_j}
\tag{4.7}
$$

behind them. Instead, both arithmetic levels have shadows identified with successive members of (4.1).

Everything later proved from (4.1) is therefore a theorem about a chosen accumulation object of the finite presentations. It is not a theorem that the arithmetic family was secretly an inverse system. This distinction will also control the uniqueness statement: the exported properties are stable, but the accumulation object need not be canonical.

## 5. Inverse limits and the patched rings

Coherent shadows still have to be converted into complete algebra. This passage has two delicate points: surjections need a Mittag--Leffler argument, and a uniform relation bound must be upgraded to a compatible limiting relation tuple. Handling both points produces a genuine quotient of the fixed presentation ring and a separate faithfully acting quotient.

### 5.1 The exactness lemma for finite inverse systems

Taking an inverse limit preserves kernels but does not preserve surjections in complete generality. The missing condition is visible through the kernels.

**Lemma 5.1 (Mittag--Leffler exactness).** Suppose

$$
0\longrightarrow K_d\longrightarrow B_d\longrightarrow C_d
\longrightarrow0
\tag{5.1}
$$

is an inverse system of short exact sequences of modules. If the inverse system $(K_d)$ satisfies the Mittag--Leffler condition, then

$$
0\longrightarrow\varprojlim_dK_d
\longrightarrow\varprojlim_dB_d
\longrightarrow\varprojlim_dC_d
\longrightarrow0
\tag{5.2}
$$

is exact. In particular, the conclusion holds if all $K_d$ are finite, or if their transition maps are surjective.

**Proof.** Left exactness of an inverse limit is immediate. Let $(c_d)$ be a compatible element of the last limit. Choose arbitrary lifts $b_d\in B_d$. The discrepancy between the image of $b_{d+1}$ and $b_d$ belongs to $K_d$. Correcting the $b_d$ to a compatible family is an inverse lifting problem in the affine spaces under the images of the $K_e$ in $K_d$. The Mittag--Leffler condition makes these images stabilize. Starting at any precision and lifting through the stabilized nonempty fibers gives compatible corrections. Equivalently, the derived obstruction $\varprojlim{}^1K_d$ vanishes under the Mittag--Leffler condition. Thus $(c_d)$ lifts. $\square$

For finite groups or finite modules, descending chains of images stabilize, so the condition is automatic even when the displayed transition maps have not been proved surjective. In our coherent shadows the transitions are quotient maps, and surjectivity is usually visible. We will nevertheless cite Lemma 5.1 whenever a quotient is carried through a limit. Merely writing $\varprojlim$ beside a finite-level exact sequence is not a proof.

There is a companion compactness fact used to lift coefficients. An inverse system of nonempty finite sets has a nonempty inverse limit whenever its transition images satisfy the same stabilization condition. This is the finite-tree argument of Chapter 4 applied to the fibers. It will ensure that relations generated at every finite precision remain generated by the limiting relation tuple.

### 5.2 Patching the relation tuple

Let $\mathscr R_d$ be the ring object in the coherent diagram $\mathscr D_d$. Its marking makes it a quotient of

$$
P_\infty/\mathfrak p_\infty^{\nu(d)}.
$$

For large $N$, the level ideal $\mathfrak c_NP_\infty$ lies in $\mathfrak p_\infty^{\nu(d)}$ and hence is zero in this shadow. Thus the kernel of the marked map is generated by the reductions of the $b$ elements in (4.6).

Because the relation tuple was included in the diagonal data, there are compatible classes

$$
f_{d,i}\in P_\infty/\mathfrak p_\infty^{\nu(d)}
\qquad(1\leq i\leq b).
\tag{5.3}
$$

Completeness gives unique elements

$$
f_i\in P_\infty
\tag{5.4}
$$

with these reductions. Put $I_\infty=(f_1,\ldots,f_b)$.

**Proposition 5.2 (the limiting kernel).** There is a natural isomorphism

$$
\varprojlim_d\mathscr R_d
\simeq P_\infty/I_\infty.
\tag{5.5}
$$

**Proof.** The compatible marked quotient maps give

$$
P_\infty\longrightarrow\varprojlim_d\mathscr R_d.
\tag{5.6}
$$

The map is surjective. Indeed, at every finite precision it is surjective, and the kernels form a system of finite sets; Lemma 5.1, or the finite lifting-tree argument, supplies a compatible choice of lifts.

Every $f_i$ lies in the kernel. Conversely, suppose $x$ lies in the kernel. At precision $d$, its reduction belongs to the ideal generated by $f_{d,1},\ldots,f_{d,b}$. Hence

$$
x\in I_\infty+\mathfrak p_\infty^{\nu(d)}
\qquad\text{for every }d.
\tag{5.7}
$$

The ideal $I_\infty$ is finitely generated in the complete Noetherian ring $P_\infty$, so it is closed. Since the powers indexed by $\nu(d)$ are cofinal, intersecting (5.7) gives $x\in I_\infty$. This identifies the kernel of (5.6) and proves (5.5). $\square$

The proof uses the marked relation tuple twice. A mere bound $\mu(\ker\beta_N)\leq b$ would not choose compatible generators. Compactness of the finite sets of generator tuples is what converts that bound into the elements (5.4).

### 5.3 Construction of the patched deformation ring

Define

$$
\boxed{
R_\infty=P_\infty/(f_1,\ldots,f_b).}
\tag{5.8}
$$

The displayed list remembers the uniform finite-level relation bound, so it can contain redundant
or zero entries. The intrinsic number of patched relations is

$$
c_\infty
=\mu_{P_\infty}(I_\infty)
=\dim_k I_\infty/\mathfrak p_\infty I_\infty
\leq b.
\tag{5.8a}
$$

Choose a minimal generating tuple $g_1,\ldots,g_{c_\infty}$ for $I_\infty$. Then the same ring has
the minimal presentation

$$
R_\infty=P_\infty/(g_1,\ldots,g_{c_\infty}).
\tag{5.8b}
$$

The distinction between $b$ and $c_\infty$ matters only after the limit has been constructed. The
number $b$ is the uniform compactness input and gives a level-independent lower bound on dimension;
$c_\infty$ is an invariant of the chosen patched quotient and is the number that enters a sharp
height-equals-relations or complete-intersection criterion.

The structural maps (2.19) descend to

$$
R_{\mathrm{loc}}\longrightarrow R_\infty,
\qquad
S_\infty\longrightarrow R_\infty.
\tag{5.9}
$$

At this point the second map is not yet known to be injective. Its injectivity will follow from the faithful $S_\infty$-action on the free patched module.

The ring $R_\infty$ is not an inverse limit of the original $R_N$. It is the inverse limit of the coherent marked ring shadows. For every fixed $d$ and every sufficiently late term of the selected subsequence, there is a compatible identification

$$
R_\infty/\mathfrak p_\infty^{\nu(d)}R_\infty
\simeq
R_{N_j}/\mathfrak p_\infty^{\nu(d)}R_{N_j}
\tag{5.10}
$$

inside the chosen finite diagram. The right side changes with $j$ before the identification is chosen; (5.10) is not induced by a map between two arithmetic levels.

The relations in (5.8) are the limiting relative equations. The finite diamond equations do not appear because Lemma 2.1 makes them zero at every fixed precision along the diagonal. This is the algebraic content of passing from finite diamond groups to $\mathbf Z_\ell^q$.

### 5.4 The patched action algebra

Let $\mathscr M_d$ be the module in $\mathscr D_d$, and let

$$
A_d
=\operatorname{im}\left(
\mathscr R_d\longrightarrow
\operatorname{End}_{C_d}(\mathscr M_d)
\right).
\tag{5.11}
$$

When the Hecke algebra is included, this is equally the image of its precision-$d$ action. The coherent diagrams give surjections

$$
A_{d+1}\twoheadrightarrow A_d.
\tag{5.12}
$$

Define

$$
A_\infty=\varprojlim_dA_d.
\tag{5.13}
$$

The compatible surjections $\mathscr R_d\twoheadrightarrow A_d$ pass to a surjection

$$
R_\infty\twoheadrightarrow A_\infty.
\tag{5.14}
$$

Surjectivity here uses Lemma 5.1; the finite kernels satisfy Mittag--Leffler. Once $M_\infty$ is constructed, (5.13) embeds into its $S_\infty$-linear endomorphism ring. It follows that

$$
A_\infty
=R_\infty/\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{5.15}
$$

If the finite-level Hecke action algebras and their named operators were retained, we write

$$
\mathbb T_\infty=A_\infty.
$$

This notation asserts only that $A_\infty$ is the limiting acting image. An exact identity $A_\infty/\mathfrak a_\infty A_\infty\simeq\mathbb T$ requires the augmentation saturation discussed in Chapter 7.

### 5.5 Completeness, locality, and finite generation

The presentation (5.8) makes $R_\infty$ a complete Noetherian local ring. The ideal $(f_1,\ldots,f_b)$ is closed, and its maximal-adic topology is the quotient topology from $P_\infty$.

The ring $A_\infty$ is local because it is an inverse limit of finite local quotient algebras with local surjective transitions. Once embedded in a finite free endomorphism module over $S_\infty$, it is finite as an $S_\infty$-module: a submodule of the finite module $\operatorname{End}_{S_\infty}(M_\infty)$ is finite because $S_\infty$ is Noetherian. It is consequently complete for its maximal ideal, since a finite local algebra over a complete local ring is complete and the induced and intrinsic adic topologies are equivalent.

The module $M_\infty$ will be finite over all three rings. It is finite over $S_\infty$ by construction. The same generating set works over $R_\infty$ and $A_\infty$, because the image of $S_\infty$ lies in both acting rings. Finiteness of $M_\infty$ over $R_\infty$ does not imply finiteness of $R_\infty$ over $S_\infty$; only the acting quotient $A_\infty$ is forced to be finite over $S_\infty$.

## 6. The patched module and freeness over $S_\infty$

The module is where the regular auxiliary ring becomes useful. Its finite shadows must preserve actual diamond bases, since coefficient ranks cannot recognize a group-ring action. A compatible-basis lemma then turns finite-level freeness into freeness over the completed group algebra and simultaneously controls the topology of the limit.

### 6.1 A limit lemma for finite free modules

The key freeness statement is structural rather than numerical.

**Lemma 6.1 (free modules from compatible free shadows).** Let

$$
C_1\longleftarrow C_2\longleftarrow\cdots
$$

be surjective maps of Artinian local rings, let $S=\varprojlim C_d$, and suppose $L_d$ is finite free of rank $r$ over $C_d$. Assume the transition maps are semilinear surjections and induce isomorphisms

$$
C_d\otimes_{C_{d+1}}L_{d+1}
\xrightarrow{\sim}L_d.
\tag{6.1}
$$

Then

$$
L:=\varprojlim_dL_d
$$

is finite free of rank $r$ over $S$.

**Proof.** Choose a basis of $L_1$. Suppose a compatible basis has been chosen through level $d$. Lift its elements to $L_{d+1}$. Their reductions form a basis of $L_d$, so their images generate $L_{d+1}$ by Nakayama. A surjection $C_{d+1}^r\to L_{d+1}$ between free modules of the same rank is an isomorphism: its determinant is a unit because its reduction is a unit. Thus the lifts form a basis. Induction produces compatible bases at every level.

They define a map $S^r\to L$. Reducing modulo the kernel of $S\to C_d$ gives an isomorphism for every $d$. Its kernel and cokernel therefore have zero image at every finite precision. Separation kills the kernel, and completeness together with surjectivity at each stage kills the cokernel. Hence the map is an isomorphism. $\square$

No comparison of cardinalities occurs in the proof. The decisive facts are local freeness, base-change compatibility, Nakayama, and separated inverse limits.

### 6.2 Construction of $M_\infty$

For $N$ sufficiently large relative to $d$, finite-level freeness gives

$$
M_N/\mathfrak b_dM_N
\simeq
(S_N/\mathfrak b_dS_N)^r
\simeq C_d^r.
\tag{6.2}
$$

The first isomorphism comes from an actual $S_N$-basis of $M_N$; the second uses $\mathfrak c_N\subseteq\mathfrak b_d$. These bases, or equivalently the free module together with its marked basis torsor, were included in the diagonal construction. Thus the selected finite models satisfy

$$
\mathscr M_d\simeq C_d^r
$$

and the compatibility (6.1).

Define

$$
M_\infty=\varprojlim_d\mathscr M_d.
\tag{6.3}
$$

Because the ideals $\mathfrak b_d$ are cofinal with powers of $\mathfrak n_\infty$, their inverse limit is $S_\infty$. Lemma 6.1 gives

$$
\boxed{M_\infty\simeq S_\infty^{\oplus r}.}
\tag{6.4}
$$

The coherent action maps pass to

$$
R_\infty\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty),
\tag{6.5}
$$

and their image is $A_\infty$. Since the scalar action on the nonzero free module (6.4) is faithful, the composites

$$
S_\infty\longrightarrow R_\infty\longrightarrow A_\infty
\longrightarrow\operatorname{End}_{S_\infty}(M_\infty)
\tag{6.6}
$$

identify the last action with ordinary scalar multiplication. It follows that both maps from $S_\infty$ in (6.6) are injective.

The construction also proves topological completeness:

$$
M_\infty\xrightarrow{\sim}
\varprojlim_dM_\infty/\mathfrak b_dM_\infty.
\tag{6.7}
$$

Since $M_\infty$ is finite over each Noetherian acting ring, its topology induced from any finite local action algebra agrees with its intrinsic adic topology. The topology from $R_\infty$ factors through $A_\infty$ and is cofinal with the $S_\infty$-adic topology on the module.

### 6.3 Why rank counting is not a proof

Suppose $q=N=1$, let $\Delta_N=C_{\ell^N}$, and put

$$
Y_N=\mathcal O^{\oplus\ell^N}
$$

with trivial diamond action. Then

$$
\operatorname{rank}_{\mathcal O}Y_N
=\operatorname{rank}_{\mathcal O}\mathcal O[\Delta_N].
\tag{6.8}
$$

After quotienting by $\varpi^d$, the two underlying finite sets have equal cardinality. Yet $Y_N$ is not free of rank one over the group algebra: its augmentation ideal acts by zero, and its coinvariants have $\mathcal O$-rank $\ell^N$ rather than one.

Even faithfulness and the correct coefficient rank would not alone prove projectivity over an arbitrary local group algebra. What proves (6.4) is a finite-level theorem that each $M_N$ is actually free, followed by the compatible-basis argument of Lemma 6.1. In geometric applications, the finite-level theorem comes from a genuine torsor or projectivity argument, not a count of points in a covering fiber.

### 6.4 A clean free Taylor--Wiles system

The simplest system isolates the patching mechanism from all deformation equations. Take

$$
R_N=\mathbb T_N=\Lambda_N=S_N,
\qquad
M_N=S_N^{\oplus r},
\tag{6.9}
$$

with scalar action, the usual augmentation, and base objects

$$
R=\mathbb T=\mathcal O,
\qquad
M=\mathcal O^{\oplus r}.
\tag{6.10}
$$

Let $P_\infty=S_\infty$. The finite-level kernel is exactly $\mathfrak c_N$, so there are no relative relations. At precision $d$ and for large $N$, the shadow is

$$
C_d\longrightarrow C_d
\longrightarrow\operatorname{End}_{C_d}(C_d^r).
$$

Every diagonal choice gives

$$
R_\infty=A_\infty=S_\infty,
\qquad
M_\infty=S_\infty^{\oplus r}.
\tag{6.11}
$$

Augmentation gives (6.10), and the sequence $z_1,\ldots,z_q$ is regular on both the ring and module. A standard sesquilinear dot product, using inversion on the second diamond action, patches to a perfect $S_\infty$-valued pairing. This example is the control case: every more complicated argument must identify exactly which additional deformation equations, action kernels, or component issues it introduces.

## 7. Augmentation and exact recovery

A patched object is valuable only if it returns to the original problem. Exact recovery is subtler than reducing symbols $z_i$ to zero: kernels must survive an inverse limit, algebra actions must remain saturated, and ordinary, completed, and derived base change must be distinguished. This chapter proves the ring and module recovery statements and identifies the extra hypothesis needed for the acting algebra.

### 7.1 Recovery of the deformation ring

The augmented presentation (2.23) was retained at every finite precision. Let $I_0=\ker(P_0\to R)$. Finite-level control says

$$
\frac{\ker\beta_N+\mathfrak a_\infty P_\infty}
{\mathfrak a_\infty P_\infty}
=I_0.
\tag{7.1}
$$

The equality is one of ideals in $P_0$, not merely an isomorphism between abstract quotients. Passing along the coherent marked shadows and then to the inverse limit gives

$$
\frac{I_\infty+\mathfrak a_\infty P_\infty}
{\mathfrak a_\infty P_\infty}
=I_0.
\tag{7.2}
$$

To justify the passage, reduce (7.1) modulo the image of $\mathfrak p_\infty^{\nu(d)}$. These are exact sequences of finite ideals. Their transition images stabilize, so Lemma 5.1 applies. Both $I_\infty$ and $\mathfrak a_\infty P_\infty$ are finitely generated and closed, so the limiting equality is algebraic rather than merely an equality of closures.

Quotienting (7.2) gives the exact recovery theorem

$$
\boxed{
R_\infty/\mathfrak a_\infty R_\infty
\xrightarrow{\sim}R.}
\tag{7.3}
$$

This statement uses augmentation-compatible diagonal data. If one diagonalizes only the abstract rings and forgets the fixed map to $R$, there is no reason for (7.2) to survive.

### 7.2 Recovery of the minimal-level module

At level $N$, module control gives an exact sequence

$$
0\longrightarrow\mathfrak a_NM_N
\longrightarrow M_N\longrightarrow M\longrightarrow0.
\tag{7.4}
$$

For $N$ sufficiently large relative to $d$, quotienting by $\mathfrak b_dM_N$ gives

$$
0\longrightarrow
\mathfrak a_\infty(M_N/\mathfrak b_dM_N)
\longrightarrow M_N/\mathfrak b_dM_N
\longrightarrow M/\varpi^dM
\longrightarrow0.
\tag{7.5}
$$

The kernel is exactly the displayed augmentation multiple because the image of $\mathfrak b_d$ under augmentation is $(\varpi^d)$. These finite exact sequences were included in the coherent shadows. Their kernels are finite, hence Mittag--Leffler. Lemma 5.1 gives

$$
0\longrightarrow
\varprojlim_d\mathfrak a_\infty\mathscr M_d
\longrightarrow M_\infty\longrightarrow M\longrightarrow0.
\tag{7.6}
$$

Under the free identification $M_\infty\simeq S_\infty^r$, the first term is exactly $\mathfrak a_\infty M_\infty$. More generally, for a finite complete module the image of the finitely generated ideal $\mathfrak a_\infty$ is closed, so the same conclusion follows once multiplication is compatible in the shadows. Therefore

$$
\boxed{
M_\infty/\mathfrak a_\infty M_\infty
\xrightarrow{\sim}M.}
\tag{7.7}
$$

The isomorphism intertwines the descended $R$-action with the original action because the action squares were part of every finite diagram.

### 7.3 The acting algebra at augmentation

The action of $A_\infty$ on (7.7) has image $\mathbb T$. Hence there is always a surjection

$$
A_\infty/\mathfrak a_\infty A_\infty
\twoheadrightarrow\mathbb T.
\tag{7.8}
$$

Its kernel consists of classes that survive in the algebraic quotient but act trivially after base change. It vanishes precisely when the inclusion

$$
A_\infty\hookrightarrow
\operatorname{End}_{S_\infty}(M_\infty)
\tag{7.9}
$$

is saturated along augmentation in the required sense:

$$
A_\infty\cap
\mathfrak a_\infty
\operatorname{End}_{S_\infty}(M_\infty)
=\mathfrak a_\infty A_\infty.
\tag{7.10}
$$

When the Hecke augmentation isomorphisms and their saturation data were retained in the finite shadows, (7.10) passes to the limit by the same finite exactness argument. Then

$$
\boxed{
A_\infty/\mathfrak a_\infty A_\infty
\xrightarrow{\sim}\mathbb T.}
\tag{7.11}
$$

Without (7.10), only (7.8) is justified. Freeness of $M_\infty$ over $S_\infty$ identifies the base change of the full endomorphism ring with $\operatorname{End}_{\mathcal O}(M)$, but it does not force an arbitrary subalgebra to be saturated inside that endomorphism ring.

Combining (7.3), (7.7), and (7.11), when applicable, gives the commutative augmented square

$$
\begin{array}{ccc}
R_\infty/\mathfrak a_\infty R_\infty&\longrightarrow&
A_\infty/\mathfrak a_\infty A_\infty\\
\downarrow\wr&&\downarrow\wr\\
R&\longrightarrow&\mathbb T,
\end{array}
\tag{7.12}
$$

with the compatible action on $M$. Nothing in (7.12) says that either horizontal map is an isomorphism.

### 7.4 Ordinary tensor products, completed tensor products, and limits

For a finite $S_\infty$-module $L$,

$$
\mathcal O\otimes_{S_\infty}L
=L/\mathfrak a_\infty L.
\tag{7.13}
$$

Because the quotient is finite over the complete DVR $\mathcal O$, it is already complete. Thus

$$
L\widehat\otimes_{S_\infty}\mathcal O
\simeq L/\mathfrak a_\infty L
\tag{7.14}
$$

under the finite Noetherian hypotheses. The completion symbol records the category, but it adds no elements to this finite quotient.

Neither expression in (7.13) or (7.14) is the inverse limit used to define $L$. Rather,

$$
L\simeq\varprojlim_dL/\mathfrak b_dL,
\tag{7.15}
$$

and the tensor quotient is taken only after the complete object has been constructed. The interchange

$$
\mathcal O\otimes_{S_\infty}\varprojlim_dL_d
\stackrel{?}{\simeq}
\varprojlim_d
(\mathcal O/\varpi^d)\otimes_{C_d}L_d
\tag{7.16}
$$

requires the finite-generation and Mittag--Leffler arguments already used in (7.5)--(7.7). Tensor products are right exact; inverse limits are left exact; neither operation commutes with the other by notation alone.

For rings, one similarly has

$$
R_\infty\widehat\otimes_{S_\infty}\mathcal O
\simeq R_\infty/\mathfrak a_\infty R_\infty
\simeq R.
\tag{7.17}
$$

This is an identity of ordinary quotient rings. It does not assert that $R_\infty$ is flat over $S_\infty$ or that derived base change is concentrated in degree zero.

### 7.5 Tor and regular-sequence criteria

Since $M_\infty$ is free over $S_\infty$,

$$
\operatorname{Tor}^{S_\infty}_i
(\mathcal O,M_\infty)=0
\qquad(i>0).
\tag{7.18}
$$

Equivalently, the sequence

$$
z_1,\ldots,z_q
\tag{7.19}
$$

is $M_\infty$-regular. The Koszul complex on (7.19) resolves $\mathcal O$ over $S_\infty$, and tensoring it with $M_\infty$ has no positive homology. Thus (7.7) is not merely an underived coincidence in the free version: it is exact derived specialization.

The corresponding assertions for $R_\infty$ need not hold. The equality (7.3) can coexist with

$$
\operatorname{Tor}^{S_\infty}_1(\mathcal O,R_\infty)\ne0.
\tag{7.20}
$$

To conclude that augmentation lowers ring dimension and depth by exactly $q$, one must prove that (7.19) is $R_\infty$-regular. Exact recovery of the quotient alone proves no injectivity of multiplication by the $z_i$.

More generally, suppose a specialization ideal $J$ is generated by augmentation variables together with $c$ extra patching or frame variables:

$$
J=(z_1,\ldots,z_q,w_1,\ldots,w_c).
\tag{7.21}
$$

If this ordered sequence is regular on a ring $B$ and a finite $B$-module $L$, then

$$
\operatorname{Tor}^B_i(B/J,L)=0
\qquad(i>0),
\tag{7.22}
$$

and

$$
\operatorname{depth}_{B/J}(L/JL)
=\operatorname{depth}_BL-(q+c).
\tag{7.23}
$$

Without module regularity, quotienting can expose torsion and destroy exactness. Without ring regularity, the expected dimension drop is unavailable. These are two separate checks.

## 8. Balanced modules and perfect complexes

Cohomological realizations often fall short of diamond freeness. Balancedness preserves enough first-syzygy information to patch a square presentation, while a perfect complex preserves the full cohomological amplitude. Neither substitute should be described with the conclusions of the free case until derived coinvariants and coefficient torsion have been controlled.

### 8.1 What balancedness actually patches

Let $(A,\mathfrak m_A,k)$ be local and let $X$ be finite. Recall that $X$ is balanced when

$$
\dim_kX/\mathfrak m_AX
\geq
\dim_k\operatorname{Tor}_1^A(X,k).
\tag{8.1}
$$

Equivalently, it admits a square presentation

$$
A^d\longrightarrow A^d\longrightarrow X\longrightarrow0.
\tag{8.2}
$$

There are two different padding operations, and both are needed at different moments. Begin with a minimal presentation

$$
A^{d_1}\longrightarrow A^{d_0}\longrightarrow X\longrightarrow0.
\tag{8.3}
$$

Balancedness says $d_1\leq d_0$. To make this presentation square, enlarge only its source from $A^{d_1}$ to $A^{d_0}$ and send the new basis vectors to zero. This adds zero columns to the relation matrix and leaves the cokernel unchanged. Once a square presentation of size $e$ has been obtained, it can be enlarged to any size $d\geq e$ by taking its direct sum with

$$
A^{d-e}\xrightarrow{1}A^{d-e}.
\tag{8.4}
$$

These identity blocks are contractible generator--relation pairs and again leave the cokernel unchanged. They do not create balancedness: adding them to a genuinely rectangular presentation preserves the difference between its source and target ranks. Conversely, adding zero rows on the target would add a free summand to the cokernel and would change the module. Keeping these three operations distinct prevents a surprisingly common presentation error.

Suppose now that the $M_N$ are balanced over $S_N$ and admit square presentations of size at most one integer $d$. Use (8.4) to make every chosen square size exactly $d$. Include the resulting actual matrices, including all zero columns and identity blocks, in the finite shadows. Diagonal compactness gives compatible matrices

$$
\Phi_e:C_e^d\longrightarrow C_e^d.
$$

Taking inverse limits gives a matrix

$$
\Phi_\infty:S_\infty^d\longrightarrow S_\infty^d
$$

and a right-exact sequence

$$
S_\infty^d\xrightarrow{\Phi_\infty}
S_\infty^d\longrightarrow M_\infty\longrightarrow0.
\tag{8.5}
$$

Right exactness follows from Lemma 5.1 applied to the finite cokernel systems. There is no zero at the left of (8.5): balancedness does not say that $\Phi_\infty$ is injective. Consequently it does not by itself give a length-one free resolution. Nor does it say that the displayed matrix is minimal. Identity blocks deliberately make it nonminimal; they are harmless because the cokernel, rather than the determinant of this stabilized matrix, is the object being patched.

The construction still gives a finite complete $S_\infty$-module, compatible actions, and ordinary augmentation recovery if the relevant finite control sequences were included. What it does not give is (6.4).

### 8.2 The correct depth statements

Balancedness alone supplies no maximal-depth theorem. A square presentation can define a hypersurface module of depth $d_S-1$, and when the left kernel of (8.5) is complicated it can give still less control. Therefore the universally valid conclusion from (8.5) is finite presentation, not freeness and not maximal Cohen--Macaulayness.

If $\Phi_\infty$ is injective and $M_\infty\ne0$, then

$$
\operatorname{pd}_{S_\infty}M_\infty=1.
$$

Since $S_\infty$ is regular of depth $d_S$, Auslander--Buchsbaum gives

$$
\operatorname{depth}_{S_\infty}M_\infty=d_S-1.
\tag{8.6}
$$

Here projective dimension is exactly one, rather than merely at most one. Indeed $S_\infty$ is a domain and an injective square matrix has a torsion cokernel; a nonzero finite free module cannot have rank zero. This is the exact conclusion, not freeness. If the map in (8.5) is not injective, (8.6) cannot be invoked.

Coefficient torsion-freeness is also insufficient in dimensions greater than one. Since $S_\infty$ is a domain, a finite torsion-free module has depth at least one, but it need not have depth $q+1$. An ordinary perfect pairing with another torsion-free module likewise gives a duality statement, not the missing regular sequence.

A perfect complex of amplitude $[a,h]$ gives a controlled finite free resolution at the complex level. It should be patched as a complex, with differentials, actions, and derived pairings included in the shadows. Its amplitude controls homological complexity, but a complex of positive amplitude does not become a free module merely because its Euler characteristic has the expected value.

### 8.3 Patching bounded perfect complexes

Balancedness remembers only generators and first relations. When classes occupy several adjacent degrees, truncating to one cohomology module throws away precisely the higher syzygies that govern specialization. The stable object is then a bounded perfect complex. Patching it requires no new compactness principle, but it requires more marked data.

Fix integers $a\leq h$. Suppose that at level $N$ there is a strict bounded complex

$$
C_N^\bullet:
0\longrightarrow C_N^a\longrightarrow\cdots
\longrightarrow C_N^h\longrightarrow0
\tag{8.7}
$$

of finite free $S_N$-modules, with

$$
C_N^i\simeq S_N^{r_i}
\qquad(a\leq i\leq h),
\tag{8.8}
$$

where the ranks $r_i$ are independent of $N$. Choose actual bases and actual differentials. If actions are meant to survive, choose strict chain actions; an action known only after passing to cohomology is not enough to define action matrices on (8.7). If pairings are meant to survive, retain the companion complex, the degree shift, the signs in the transpose differential, and a chain-level representative of the pairing.

For $N$ large relative to $d$, base change along $S_N\to C_d$ gives a bounded complex of the fixed finite modules $C_d^{r_i}$. Its finitely many differential matrices satisfy the finitely many equations

$$
d^{i+1}d^i=0.
\tag{8.9}
$$

Thus complexes with these marked ranks form a finite set at precision $d$. Add their reduction maps and all named chain data to the finite tree. A coherent path yields differentials

$$
d_\infty^i:S_\infty^{r_i}\longrightarrow S_\infty^{r_{i+1}}
$$

whose composites vanish because they vanish modulo every $\mathfrak b_d$. Hence

$$
C_\infty^\bullet
=\varprojlim_d\mathscr C_d^\bullet
\tag{8.10}
$$

is a bounded complex of finite free $S_\infty$-modules in the same degree interval. It is therefore perfect. This proof patches the chosen strict representative. If two representatives are to be identified, compatible chain maps and homotopies must also be placed in the shadows; equality of cohomology dimensions does not produce a limiting quasi-isomorphism.

**Theorem 8.1 (perfect-complex patching).** Under the fixed-amplitude, fixed-rank, marked-basis, and chain-compatibility hypotheses above, diagonal patching produces a perfect complex $C_\infty^\bullet$ over $S_\infty$. Suppose in addition that there is a bounded complex $C_0^\bullet$ of finite free $\mathcal O$-modules and that, at precision $d$, the marked shadow contains chain maps and chain homotopies exhibiting an equivalence

$$
(\mathcal O/\varpi^d)\otimes_{C_d}\mathscr C_d^\bullet
\simeq
(\mathcal O/\varpi^d)\otimes_{\mathcal O}C_0^\bullet,
$$

compatibly under reduction in $d$. Then

$$
\mathcal O\otimes_{S_\infty}^{\mathbf L}C_\infty^\bullet
\simeq C_0^\bullet.
\tag{8.11}
$$

**Proof strategy.** Termwise freeness makes derived tensoring ordinary tensoring on the chosen complex. Marking the comparison maps and homotopies makes them compatible. Their inverse limits are chain maps whose two composites differ from the identity by the limiting homotopies. This proves (8.11). If the finite input supplies only quasi-isomorphisms, one must first choose uniformly bounded finite free representatives and compatible comparison data; without that additional uniform choice, the stated finite-shadow theorem does not apply. $\square$

The theorem distinguishes derived control from degree-zero control. An isomorphism

$$
H^j(C_N^\bullet)/\mathfrak a_NH^j(C_N^\bullet)
\simeq H^j(C_0^\bullet)
$$

does not imply (8.11): differentials can acquire new kernels after specialization, and adjacent cohomology can contribute through Tor. Derived augmentation is the statement that controls all those contributions at once.

### 8.4 Amplitude, homology, and specialization

The amplitude of a perfect complex is useful because it bounds projective dimension whenever the complex resolves a single module. Suppose

$$
C_\infty^\bullet\simeq L[-j]
\tag{8.12}
$$

for one nonzero finite module $L$. Shifting degrees, the finite free complex gives

$$
\operatorname{pd}_{S_\infty}L\leq h-a.
\tag{8.13}
$$

Auslander--Buchsbaum then yields the quantitative depth bound

$$
\operatorname{depth}_{S_\infty}L
\geq d_S-(h-a).
\tag{8.14}
$$

This is often the honest output before a concentration theorem is proved. A two-term complex can yield depth at least $d_S-1$; it does not yield depth $d_S$ merely because its two free terms have equal rank.

Minimal complexes make specialization especially transparent. Every bounded perfect complex over the local ring $S_\infty$ is isomorphic to a direct sum of a minimal complex and contractible identity blocks. In a minimal complex all differential entries lie in $\mathfrak n_\infty$, so tensoring with $k$ kills every differential. Consequently the number of free summands in degree $i$ is

$$
\dim_k H^i(k\otimes_{S_\infty}^{\mathbf L}C_\infty^\bullet).
\tag{8.15}
$$

Derived closed-fiber cohomology therefore detects the entire minimal complex, not just its Euler characteristic.

This observation also handles shifts correctly. If

$$
\mathcal O\otimes_{S_\infty}^{\mathbf L}C_\infty^\bullet
\simeq L_0[-j]
\tag{8.16}
$$

with $L_0$ finite free of rank $r$ over $\mathcal O$, then tensoring further with $k$ and using (8.15) shows

$$
C_\infty^\bullet\simeq S_\infty^{\oplus r}[-j].
\tag{8.17}
$$

If $L_0$ has coefficient torsion, further tensoring with $k$ can have cohomology in two degrees, and (8.17) need not hold. If the derived specialization occupies several degrees, the minimal patched complex has corresponding terms and must remain a complex.

### 8.5 Criteria that really upgrade to freeness

There are two reliable upgrades.

**Proposition 8.2 (derived coinvariant criterion).** Let $L$ be a nonzero finite $S_\infty$-module. Suppose

$$
\operatorname{Tor}^{S_\infty}_i(\mathcal O,L)=0
\qquad(i>0)
\tag{8.18}
$$

and $L/\mathfrak a_\infty L$ is torsion-free over $\mathcal O$. Then $L$ is finite free over $S_\infty$.

**Proof.** The Koszul criterion applied to the regular sequence $z_1,\ldots,z_q$ identifies the groups in (8.18) with its positive homology. Their vanishing makes this sequence $L$-regular. The quotient is a nonzero finite torsion-free module over the DVR $\mathcal O$, so $\varpi$ is regular on it. Hence

$$
\varpi,z_1,\ldots,z_q
$$

is an $L$-regular sequence after a permitted reordering, and

$$
\operatorname{depth}_{S_\infty}L=q+1=\dim S_\infty.
$$

Every finite module over the regular local ring $S_\infty$ has finite projective dimension. Auslander--Buchsbaum gives projective dimension zero, and finite projective modules over a local ring are free. $\square$

Thus balancedness can be upgraded when a separate theorem proves derived coinvariant concentration and torsion-free minimal-level cohomology. Ordinary coinvariant control alone gives only degree-zero base change and does not imply (8.18).

**Proposition 8.3 (perfect-complex concentration criterion).** Let $C_\infty$ be a perfect complex over $S_\infty$. Suppose

$$
\mathcal O\otimes_{S_\infty}^{\mathbf L}C_\infty
\simeq L_0[0]
\tag{8.19}
$$

for a finite free $\mathcal O$-module $L_0$. Then

$$
C_\infty\simeq S_\infty^{\oplus r}[0],
\qquad r=\operatorname{rank}_{\mathcal O}L_0.
\tag{8.20}
$$

**Proof.** Tensor (8.19) further with $k$. Then

$$
k\otimes_{S_\infty}^{\mathbf L}C_\infty
\simeq k^r[0].
$$

Represent $C_\infty$ by a bounded minimal complex of finite free modules. Every differential has entries in the maximal ideal, so tensoring with $k$ makes every differential zero. The resulting graded vector space can be concentrated in degree zero only if the minimal complex has a single nonzero term there, of rank $r$. This proves (8.20). $\square$

The hypotheses in (8.19) include all higher derived coinvariants and coefficient torsion. If the derived specialization has several nonzero degrees, the correct output remains a perfect complex. Selecting one cohomology module and calling it free would discard the other degrees.

### 8.6 A balanced but nonfree finite-level module

Let $G=C_{\ell^N}$ with generator $g$, put

$$
A=\mathcal O[G],
\qquad t=g-1,
$$

and consider the augmentation ideal

$$
I=(t)\subset A.
$$

Let

$$
\mathcal N=1+g+\cdots+g^{\ell^N-1}.
$$

Multiplication by $t$ maps $A$ onto $I$, and its kernel is $A\mathcal N$. Hence

$$
A\xrightarrow{\mathcal N}A\xrightarrow{t}I\longrightarrow0
\tag{8.21}
$$

is a square presentation. The relation entry $\mathcal N$ lies in the maximal ideal of $A$, since its augmentation is $\ell^N$, while $t$ is a minimal generator of $I$. Thus the presentation is minimal, and $I$ is balanced with one generator and one first relation.

The module $I$ is not free over $A$: the nonzero norm element annihilates it. It is nevertheless torsion-free over $\mathcal O$, because it is an $\mathcal O$-submodule of the free module $A$. Its coinvariants expose the missing flatness. From

$$
(1+t)^{\ell^N}-1=0
$$

one obtains

$$
I/tI\simeq\mathcal O/\ell^N\mathcal O,
\tag{8.22}
$$

If $\mathcal O$ has mixed characteristic and $\ell=u\varpi^e$, then the right side is $\mathcal O/\varpi^{eN}\mathcal O$, so augmentation introduces coefficient torsion. In equal characteristic $\ell$, the element $\ell$ is zero in $\mathcal O$ and the right side is $\mathcal O$; this particular specialization is torsion-free, but the periodic resolution obtained from multiplication by $t$ and $\mathcal N$ still has nonzero higher derived coinvariants. Thus the example rules out the shortcuts in their correct scope: balanced does not mean free, coefficient torsion-freeness before augmentation does not control derived coinvariants, and a square presentation does not justify a maximal-depth conclusion.

## 9. Dimension bookkeeping and the Taylor--Wiles cancellation

The purpose of the auxiliary primes is numerical as well as structural. Their new variables must cancel the obstruction defect without being counted again as relations or frames. This chapter places every coordinate and equation in one ledger, derives the honest lower bound, and states the independent mechanisms that can turn it into equality.

### 9.1 Dimensions of the source rings

There are two regular directions in the construction: the coefficient-and-diamond directions in $S_\infty$, and the formal coordinates added to the fixed local deformation base in $P_\infty$. Their dimensions are

$$
\dim S_\infty=q+1
\tag{9.1}
$$

and

$$
\dim P_\infty=d_{\mathrm{loc}}+q+G.
\tag{9.2}
$$

Formula (9.2) is exact for every Noetherian $R_{\mathrm{loc}}$. Regularity of $P_\infty$ requires regularity of $R_{\mathrm{loc}}$. Cohen--Macaulayness and complete-intersection structure likewise require the corresponding hypothesis on the local base.

If the local base itself is assembled from flat complete local factors,

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in T,\mathcal O}R_v,
\tag{9.3}
$$

then its dimension must be computed with the shared coefficient direction removed at every product step. For two nonzero $\mathcal O$-flat factors,

$$
\dim(R_1\widehat\otimes_{\mathcal O}R_2)
=\dim R_1+\dim R_2-1.
\tag{9.4}
$$

Iterating (9.4) gives the local-base dimension. Without $\mathcal O$-flatness, this equality is not available; a presentation bound may still give an inequality, but the coefficient direction cannot be subtracted mechanically.

Auxiliary framing affects $G$ and $d_{\mathrm{loc}}$ according to where the formally smooth factors are placed. In the rank-two regular local calculation, an unframed Taylor--Wiles factor contributes one smooth eigenvalue coordinate beyond its diamond algebra, while a framed factor contributes three. If those coordinates are already inside $R_{\mathrm{loc}}$, they are not included again in $G$.

### 9.2 Relations and lower bounds

The marked presentation (5.8) has $b$ displayed equations, while the intrinsic minimal presentation (5.8b) has $c_\infty\leq b$ equations. Krull's height theorem therefore gives the sharper lower bound

$$
\dim R_\infty
\geq d_{\mathrm{loc}}+q+G-c_\infty
\geq d_{\mathrm{loc}}+q+G-b.
\tag{9.5}
$$

It is useful to measure the excess over the diamond dimension by

$$
\delta_{\mathrm{patch}}
=d_{\mathrm{loc}}+G-b-1.
\tag{9.6}
$$

Then (9.5) becomes

$$
\dim R_\infty\geq\dim S_\infty+\delta_{\mathrm{patch}}.
\tag{9.7}
$$

The standard balanced numerical situation is

$$
d_{\mathrm{loc}}+G-b=1,
\qquad\text{equivalently}\qquad
\delta_{\mathrm{patch}}=0.
\tag{9.8}
$$

In that case (9.7) gives the global lower bound $\dim R_\infty\geq q+1$. If $P_\infty$ is also equidimensional and catenary, the generalized principal ideal theorem gives the same lower bound for every irreducible component of $R_\infty$. Even then, the inequality need not be an equality: the marked $b$-tuple can contain redundant equations, and even a minimal $c_\infty$-tuple can have height smaller than $c_\infty$.

The integer $b$ must be an effective relation bound. A cohomology group that merely receives obstruction classes does not suffice. The obstruction theory must be complete, functorial, additive, and effective for removing universal relation directions. Those hypotheses are what turn the relative dual-Selmer dimension into a bound on minimal equations. Patching cannot improve an unproved relation estimate.

Concretely, the relative global presentation theorem of Book 69 gives

$$
b_{\mathrm{rel},N}\leq q_{\mathrm{rel},N}
$$

only under those complete effective obstruction hypotheses. Book 144 compares the relative Selmer conditions for the actual finite-level local base, proves uniform boundedness, and performs simultaneous variable-and-relation padding. Equation (9.5) is the first place in the limiting argument where that finite-level bound is used.

### 9.3 Where the dual-Selmer defect disappears

The numerical cancellation can be seen directly from the finite levels. Before auxiliary primes are added, the dual-Selmer space has dimension $q$. Selecting $q$ Taylor--Wiles primes kills it. Each selected prime simultaneously adds one finite diamond direction. Thus

$$
\dim S_\infty=1+q.
\tag{9.9}
$$

At finite level those directions satisfy the $q$ equations $\mathfrak c_N$. The full kernel of the finite presentation therefore has the form

$$
\mathfrak c_NP_\infty+(f_{N,1},\ldots,f_{N,b}).
\tag{9.10}
$$

The first $q$ equations are not global deformation obstructions; they say that the new characters have order dividing $\ell^N$. Lemma 2.1 makes them disappear in every fixed patched shadow. The remaining relation number $b$ is uniformly bounded because the enlarged absolute dual Selmer group is zero and the relevant relative dual group injects into a fixed sum of local quotients.

More precisely, in the full-local-base convention of Book 144, let

$$
q_{\mathrm{rel},N}
=\dim_kH^1_{(\mathcal L_{Q_N,U_N}^0)^\perp}(K,W^*(1))
\tag{9.11}
$$

be the relative obstruction dimension and let $g_{\mathrm{rel},N}$ be the exact relative tangent dimension, including the stated frame correction. Global duality fixes the difference

$$
g_{\mathrm{rel},N}-q_{\mathrm{rel},N}
=c_{\mathrm{rel}},
\tag{9.12}
$$

independently of the identities of the auxiliary primes. The individual terms can vary. Put

$$
b=\max_N q_{\mathrm{rel},N},
\qquad
g=c_{\mathrm{rel}}+b.
\tag{9.13}
$$

Padding a level with $g-g_{\mathrm{rel},N}$ source variables also adds that many linear relations. The total relative kernel is still generated by at most $b$ elements because

$$
q_{\mathrm{rel},N}+g-g_{\mathrm{rel},N}=b.
\tag{9.14}
$$

After auxiliary smooth coordinates are placed in their chosen part of the source, $G$ is obtained from $g$ without double counting. Substituting the resulting arithmetic identity into (9.6) gives the application-specific value of $\delta_{\mathrm{patch}}$.

The cancellation is now visible: the number $q$ occurs once in (9.2) and once in (9.1), so it cancels from (9.6). The dual-Selmer defect has been exchanged for the regular variables $z_1,\ldots,z_q$ rather than left behind as extra relations. If padding primes are added, each adds both one diamond variable and one primal direction, so the same cancellation persists only after the variable ledger is adjusted on both sides.

### 9.4 Forcing equality

Assume the balanced numerical identity (9.8). Then

$$
\dim R_\infty\geq q+1.
\tag{9.15}
$$

There are several legitimate ways to obtain the reverse inequality.

1. An independent deformation-theoretic dimension theorem may give $\dim R_\infty\leq q+1$.
2. If $R_\infty$ is separately proved finite over $S_\infty$, then the injective finite map $S_\infty\to R_\infty$ gives equality of dimensions.
3. Exact augmentation gives a useful conditional bound. Since $\mathfrak a_\infty R_\infty$ is generated by $q$ elements and its quotient is $R$,

   $$
   \dim R_\infty\leq\dim R+q.
   \tag{9.16}
   $$

   Thus $\dim R\leq1$ gives the desired ceiling. Such a bound on $R$ must be proved independently; it cannot be inferred from the finite Hecke quotient before the action kernel is controlled.
4. If the support of $M_\infty$ contains the generic point of every irreducible component of $R_\infty$, equivalently every minimal prime lies in the support, then every component is contained in that support. Equation (11.3) gives the ceiling component by component. Mere nonempty intersection with every component would not suffice.

Under any one of these mechanisms,

$$
\boxed{
\dim R_\infty=\dim S_\infty=q+1.}
\tag{9.17}
$$

The existence of the finite $S_\infty$-algebra $A_\infty$ gives only a quotient of $R_\infty$ of dimension $q+1$. It proves that $R_\infty$ has at least one closed subset of that dimension. It does not rule out other components of larger dimension. Consequently the action quotient by itself is not the reverse inequality in (9.17).

### 9.5 Complete-intersection consequences

Suppose $P_\infty$ is Cohen--Macaulay and equality holds in the intrinsic sharp form

$$
\dim R_\infty=\dim P_\infty-c_\infty.
\tag{9.18}
$$

The complete local Cohen--Macaulay source is catenary and equidimensional, so (9.18) says that $I_\infty$ has height $c_\infty$. Choose the minimal generating tuple in (5.8b). Since grade equals height in a Cohen--Macaulay local ring and $I_\infty$ is generated by exactly $c_\infty$ elements, the complete-intersection criterion shows that

$$
g_1,\ldots,g_{c_\infty}
\tag{9.19}
$$

is a $P_\infty$-regular sequence. In particular, $R_\infty$ is Cohen--Macaulay and equidimensional.

The familiar equality $\dim R_\infty=\dim P_\infty-b$ is a stronger numerical hypothesis only because $b$ was permitted to be a padded bound. Indeed it gives

$$
b=\operatorname{ht}I_\infty\leq c_\infty\leq b,
$$

so $c_\infty=b$. The marked tuple $f_1,\ldots,f_b$ is then minimal and is itself regular. Thus the usual sharp-$b$ conclusion is a special case of the intrinsic criterion, while a strict inequality $c_\infty<b$ no longer hides a genuine complete-intersection conclusion.

If $P_\infty$ is regular, (9.19) makes $R_\infty$ a complete intersection. If $P_\infty$ is already a complete intersection, quotienting by the regular sequence again gives a complete intersection. If $P_\infty$ is merely Cohen--Macaulay, the conclusion is Cohen--Macaulayness; it does not promote the source to a regular ring.

Relation number alone proves none of this. Equality of the number of equations with the expected codimension supplies the missing height statement. Nor does complete-intersection structure make every maximal Cohen--Macaulay module free: a singular hypersurface has many nonfree modules of maximal depth.

## 10. Depth over the three acting rings

Depth is computed for a module over a named ring. The free $S_\infty$-structure supplies an explicit regular sequence, but moving that depth to the action algebra and the deformation ring requires finite local maps. Keeping those maps visible isolates exactly when the resulting Cohen--Macaulay module is maximal and when Auslander--Buchsbaum can make it free.

### 10.1 The regular sequence supplied by $S_\infty$

The free identification (6.4) immediately gives

$$
\operatorname{depth}_{S_\infty}M_\infty
=\operatorname{depth}S_\infty=q+1.
\tag{10.1}
$$

Concretely,

$$
\varpi,z_1,\ldots,z_q
\tag{10.2}
$$

is an $M_\infty$-regular sequence. The order may be permuted because the module is finite and the elements lie in the maximal ideal. The quotient by all of them is $k^r$.

The shorter sequence $z_1,\ldots,z_q$ controls augmentation, while $\varpi$ records coefficient torsion-freeness at the end. This distinction matters in balanced settings: derived diamond coinvariants can be concentrated in degree zero while their remaining $\mathcal O$-module still has $\varpi$-torsion.

Because $S_\infty$ maps into $R_\infty$, the elements in (10.2) also lie in the maximal ideal of $R_\infty$ and act on the same module. Thus they give the lower bound

$$
\operatorname{depth}_{R_\infty}M_\infty\geq q+1.
\tag{10.3}
$$

This lower bound alone is the only automatic comparison for a general local map. The equality below uses the finite action quotient.

### 10.2 Depth over the action algebra

The map

$$
S_\infty\hookrightarrow A_\infty
\tag{10.4}
$$

is finite local and injective. For the same finite $A_\infty$-module $M_\infty$, depth across a finite local map is unchanged because

$$
\sqrt{\mathfrak n_\infty A_\infty}=\mathfrak m_{A_\infty}.
$$

The Koszul depth formula therefore gives

$$
\operatorname{depth}_{A_\infty}M_\infty
=\operatorname{depth}_{S_\infty}M_\infty
=q+1.
\tag{10.5}
$$

The same finite map identifies support dimensions:

$$
\dim_{A_\infty}M_\infty
=\dim_{S_\infty}M_\infty=q+1.
\tag{10.6}
$$

Indeed $M_\infty$ is faithful over $A_\infty$, so its $A_\infty$-support is all of $\operatorname{Spec}A_\infty$, and integrality gives

$$
\dim A_\infty=\dim S_\infty=q+1.
\tag{10.7}
$$

Consequently $M_\infty$ is maximal Cohen--Macaulay as an $A_\infty$-module. This does not imply that $A_\infty$ is regular or that $M_\infty$ is free over $A_\infty$.

### 10.3 Depth over the patched deformation ring

The surjection

$$
R_\infty\twoheadrightarrow A_\infty
\tag{10.8}
$$

is a finite local map. Applying the same finite-map depth comparison to the $A_\infty$-module $M_\infty$ gives

$$
\boxed{
\operatorname{depth}_{R_\infty}M_\infty=q+1.}
\tag{10.9}
$$

Likewise,

$$
\dim_{R_\infty}M_\infty
=\dim A_\infty=q+1.
\tag{10.10}
$$

Thus $M_\infty$ is Cohen--Macaulay as an $R_\infty$-module, whether or not it has full support. It is maximal Cohen--Macaulay over $R_\infty$ exactly when

$$
\dim R_\infty=q+1.
\tag{10.11}
$$

Equations (10.5) and (10.9) do not follow simply because depth over $S_\infty$ has been computed. They use, respectively, the finite local maps (10.4) and (10.8), along with finiteness of the module. If one retains an $R_\infty$-action whose image has not been proved finite over $S_\infty$, only the regular-sequence lower bound (10.3) is available.

### 10.4 Maximal Cohen--Macaulay conclusions

Assume the dimension equality (9.17). Then (10.9) gives

$$
\operatorname{depth}_{R_\infty}M_\infty
=\dim R_\infty,
\tag{10.12}
$$

so $M_\infty$ is maximal Cohen--Macaulay. Every system of parameters for its support is regular on it, its support is unmixed, and it has no embedded associated primes.

If (9.18) also holds with $P_\infty$ Cohen--Macaulay, then both the ring and module are Cohen--Macaulay of the same dimension. This is the standard depth package exported to the subsequent comparison argument.

If instead $\dim R_\infty>q+1$, then $M_\infty$ is still Cohen--Macaulay on its own support, but it is not maximal over the entire ring. Calling it maximal Cohen--Macaulay in this case would silently replace module dimension by ring dimension.

### 10.5 When freeness over the deformation ring follows

Suppose $\dim R_\infty=q+1$. If $R_\infty$ is regular local, every finite module has finite projective dimension. Auslander--Buchsbaum and (10.12) yield

$$
\operatorname{pd}_{R_\infty}M_\infty=0,
$$

so $M_\infty$ is free over $R_\infty$.

More generally, if $R_\infty$ is Cohen--Macaulay and

$$
\operatorname{pd}_{R_\infty}M_\infty<\infty,
\tag{10.13}
$$

then the same formula gives freeness. The projective-dimension hypothesis is substantive when $R_\infty$ is singular.

For example, over

$$
B=k[[x,y]]/(xy),
$$

the module $B/(x)$ has depth one, equal to $\dim B$, but it is not free and has an infinite periodic resolution. Even adding a free summand makes it faithful without making it free. Therefore neither maximal depth, complete-intersection structure, nor faithfulness can replace (10.13).

The freeness proved unconditionally in the strong Taylor--Wiles system is freeness over the regular auxiliary ring $S_\infty$. Freeness over the patched deformation ring is a different conclusion with different hypotheses.

## 11. Support, components, and annihilators

Maximal depth measures the quality of a module on the part of the spectrum that it sees. It does not determine how many components it sees or whether nilpotent functions act nontrivially. The action quotient makes the support exact, after which equidimensionality, component coverage, reducedness, and faithfulness can be separated cleanly.

### 11.1 The exact support

By construction,

$$
\operatorname{Ann}_{R_\infty}(M_\infty)
=\ker(R_\infty\to A_\infty).
\tag{11.1}
$$

Hence

$$
\operatorname{Supp}_{R_\infty}M_\infty
=V(\operatorname{Ann}_{R_\infty}M_\infty)
\simeq\operatorname{Spec}A_\infty
\tag{11.2}
$$

as a closed subset, with $A_\infty$ carrying the scheme-theoretic action quotient. Its dimension is

$$
\dim\operatorname{Supp}_{R_\infty}M_\infty=q+1.
\tag{11.3}
$$

The zeroth Fitting ideal defines the same underlying closed set:

$$
V(\operatorname{Fitt}^{R_\infty}_0(M_\infty))
=V(\operatorname{Ann}_{R_\infty}(M_\infty)).
\tag{11.4}
$$

It need not equal the annihilator. If $s$ generators suffice, then

$$
\operatorname{Ann}(M_\infty)^s
\subseteq\operatorname{Fitt}_0(M_\infty)
\subseteq\operatorname{Ann}(M_\infty).
\tag{11.5}
$$

Thus Fitting ideals and annihilators have the same radical but can retain different nilpotent thickness.

### 11.2 A union of components versus every component

Assume $R_\infty$ is equidimensional of dimension $q+1$ and catenary. Complete local rings obtained as quotients of the excellent power-series rings used here have the needed catenary behavior. Since $M_\infty$ is Cohen--Macaulay of dimension $q+1$, its support is unmixed. Every minimal prime of its support has dimension $q+1$.

Let $\mathfrak q$ be such a prime and choose a minimal prime $\mathfrak p$ of $R_\infty$ contained in it. Equidimensionality gives

$$
\dim R_\infty/\mathfrak p=q+1
=\dim R_\infty/\mathfrak q.
$$

Catenarity rules out a strict inclusion $\mathfrak p\subsetneq\mathfrak q$, which would consume positive height. Thus $\mathfrak p=\mathfrak q$. It follows that

$$
\operatorname{Supp}_{R_\infty}M_\infty
\text{ is a union of irreducible components of }
\operatorname{Spec}R_\infty.
\tag{11.6}
$$

Nothing yet says it is the union of all components. Component coverage is a separate input. It may come from irreducibility of $R_\infty$, a component-hopping theorem, a comparison of generic points, or a separate statement that every minimal prime lies in the support.

If $R_\infty$ has components of dimension greater than $q+1$, the support can lie in a positive-codimension closed subset of such a component. Then even the union-of-components conclusion (11.6) is unavailable. The numerical dimension equality is therefore part of the support argument, not merely decorative bookkeeping.

### 11.3 Faithful and nearly faithful actions

A finite module is faithful when its annihilator is zero. It is **nearly faithful** when its annihilator is nilpotent. Equivalently,

$$
M_\infty\text{ is nearly faithful over }R_\infty
\quad\Longleftrightarrow\quad
\operatorname{Supp}_{R_\infty}M_\infty
=\operatorname{Spec}R_\infty.
\tag{11.7}
$$

Under the equidimensional component conclusion, near faithfulness is therefore equivalent to seeing every minimal component. If $R_\infty$ has one minimal prime, any nonzero union of components is the whole spectrum, so near faithfulness follows. If the ring is reduced as well, a nilpotent annihilator is zero and near faithfulness becomes faithfulness.

Over a nonreduced ring, full topological support proves only

$$
\operatorname{Ann}_{R_\infty}(M_\infty)
\subseteq\sqrt{0}.
\tag{11.8}
$$

It does not show that nilpotents act nontrivially. Dimension equality is even weaker: a module supported on one maximal-dimensional component has the full ring dimension while missing every other component.

Perfect pairings do not repair this gap by themselves. They can identify the support of a module with that of a companion module and constrain adjoints, but two self-dual modules can still live on one component. Faithfulness or component coverage must be established through the action.

### 11.4 Nilpotent-sensitive faithfulness criteria

Component coverage is topological. Faithfulness is scheme-theoretic. To pass from the first to the second without assuming that the ring is reduced, one needs information at every associated prime or an exact saturation statement for the annihilator. This section gives three criteria that do not erase nilpotents.

**Proposition 11.1 (associated-prime criterion).** Let $B$ be Noetherian and let $L$ be a finite $B$-module. Then $L$ is faithful if and only if

$$
\operatorname{Ann}_{B_{\mathfrak p}}(L_{\mathfrak p})=0
\qquad
\text{for every }\mathfrak p\in\operatorname{Ass}_B(B).
\tag{11.9}
$$

It is enough, in particular, that $L_{\mathfrak p}$ be a nonzero free $B_{\mathfrak p}$-module at every associated prime.

**Proof strategy.** A nonzero ideal cannot disappear at every associated prime of the ring. Rather than replacing the ring by its reduction, detect a nonzero element of the annihilator inside a cyclic submodule of $B$.

**Proof.** Necessity follows by localization. Conversely, put $J=\operatorname{Ann}_B(L)$ and suppose $J\ne0$. Choose $0\ne x\in J$. The nonzero cyclic submodule $Bx\subseteq B$ has an associated prime $\mathfrak p$, and associated primes of a submodule of $B$ belong to $\operatorname{Ass}_B(B)$. The element $x/1$ is nonzero in $B_{\mathfrak p}$: otherwise some $s\notin\mathfrak p$ would kill $x$, contradicting that $\mathfrak p$ is the annihilator of a suitable nonzero element of $Bx$. Hence $J_{\mathfrak p}\ne0$, contrary to (11.9). Thus $J=0$. $\square$

If $B$ is Cohen--Macaulay, it has no embedded associated primes and

$$
\operatorname{Ass}_B(B)=\operatorname{Min}(B).
\tag{11.10}
$$

In that case scheme-theoretic generic faithfulness on every irreducible component implies faithfulness, even when $B$ is nonreduced. The adjective “scheme-theoretic” is essential: merely knowing $L_{\mathfrak p}\ne0$ at each minimal prime proves component coverage, not that its annihilator over the zero-dimensional local ring $B_{\mathfrak p}$ vanishes.

**Corollary 11.2 (finite-projective-dimension criterion).** Let $(B,\mathfrak m)$ be Cohen--Macaulay, and let $L$ be a nonzero maximal Cohen--Macaulay $B$-module of finite projective dimension. Then $L$ is finite free of positive rank and hence faithful.

**Proof.** Auslander--Buchsbaum gives

$$
\operatorname{pd}_BL
=\operatorname{depth}B-\operatorname{depth}_BL=0.
$$

Thus $L$ is finite projective, hence free because $B$ is local. Its positive rank follows from $L\ne0$, and a positive-rank free module has zero annihilator. $\square$

This criterion simultaneously gives freeness and faithfulness and makes no reducedness assumption. Its price is the finite-projective-dimension hypothesis, which cannot be inferred from maximal depth over a singular complete intersection.

**Proposition 11.3 (augmentation-saturation criterion).** Let $(B,\mathfrak m)$ be Noetherian local, let $\mathfrak a\subseteq\mathfrak m$, let $L$ be a finite $B$-module, and put $J=\operatorname{Ann}_B(L)$. Suppose $L/\mathfrak aL$ is faithful over $B/\mathfrak a$. Then

$$
J\subseteq\mathfrak a.
\tag{11.11}
$$

If, in addition, the annihilator is saturated along augmentation in the precise sense

$$
J\cap\mathfrak a=\mathfrak aJ,
\tag{11.12}
$$

then $L$ is faithful over $B$.

**Proof.** Base-level faithfulness first gives (11.11): the class of every $x\in J$ annihilates $L/\mathfrak aL$, so $x$ belongs to $\mathfrak a$. Consequently $J=J\cap\mathfrak a$. Under (11.12), this says $J=\mathfrak aJ$. The ideal $J$ is finite because $B$ is Noetherian, and $\mathfrak a\subseteq\mathfrak m$, so Nakayama gives $J=0$. $\square$

The proof exposes the role of (11.12). Saturation says that an annihilator lying in the specialization ideal was already an augmentation multiple of an annihilator. Iteration and completeness are not needed. Without (11.12), a nilpotent thickening can lie inside $\mathfrak a$ and vanish on the specialized module without being an augmentation multiple of the annihilator.

Applied with

$$
B=R_\infty,
\qquad
\mathfrak a=\mathfrak a_\infty R_\infty,
\qquad
L=M_\infty,
\tag{11.13}
$$

this gives a second route from a faithful minimal action to a faithful patched action. It is different from augmentation saturation for the acting algebra in (7.10). Equation (7.10) controls which endomorphisms survive in $A_\infty/\mathfrak a_\infty A_\infty$; equation (11.12) controls the kernel of $R_\infty\to A_\infty$. Neither condition implies the other formally.

Finally, faithfulness is automatic if a prior argument proves that $M_\infty$ is a nonzero free $R_\infty$-module. This is why the homological freeness criterion of Section 10.5 is stronger than a component calculation. It controls every infinitesimal layer at once.

### 11.5 Two failures: a missed component and a killed thickening

The first example shows why maximal depth does not give component coverage. Let $S=S_\infty$ and form

$$
B=S[[u]]/(u(u-\varpi)).
\tag{11.14}
$$

The polynomial is monic, so $B$ is finite free of rank two over $S$ and

$$
\dim B=\dim S=q+1.
$$

The two minimal primes are $(u)$ and $(u-\varpi)$. Since $S[[u]]$ is a regular local unique factorization domain and the two factors are distinct prime elements, $B$ is reduced.

Take

$$
L=B/(u)\simeq S.
\tag{11.15}
$$

Then $L$ is free of rank one over $S$ and

$$
\operatorname{depth}_BL=q+1=\dim B.
$$

Thus it has every source-freeness and maximal-depth property one might hope to obtain from patching. Nevertheless

$$
\operatorname{Ann}_B(L)=(u)\ne0,
$$

and its support is only the component $V(u)$. Because $B$ is reduced, the module is not even nearly faithful. A perfect $S$-valued pairing on $L\simeq S$ changes none of these facts.

This example is the diagnostic for component arguments. Freeness over $S_\infty$, equality of Krull dimensions, maximal Cohen--Macaulayness, reducedness of the ring, and self-duality can all hold while full support fails.

The second example has full support but kills a nilpotent direction. Put

$$
B'=S[\epsilon]/(\epsilon^2),
\qquad
L'=B'/(\epsilon)\simeq S.
\tag{11.16}
$$

The extension is finite free of rank two over $S$, so $\dim B'=\dim S$. The module $L'$ is $S$-free of rank one and has depth $\dim S$ over $B'$. The ring $B'$ has a single minimal prime $(\epsilon)$, so

$$
\operatorname{Supp}_{B'}L'=\operatorname{Spec}B'.
\tag{11.17}
$$

Nevertheless

$$
\operatorname{Ann}_{B'}(L')=(\epsilon)\ne0.
\tag{11.18}
$$

Thus the action is nearly faithful but not faithful. Localizing at the unique associated prime does not fix the problem: $B'$ is already a zero-dimensional thickening in the transverse direction, and $L'$ is not faithful there. A perfect $S$-valued pairing on $L'$ sees its scalar lattice perfectly while remaining blind to the killed element $\epsilon$. This is the diagnostic for every argument that passes from full support to faithfulness: unless reducedness, associated-prime faithfulness, annihilator saturation, or target-ring freeness has been proved, the nilpotent kernel remains.

## 12. Perfect pairings and adjoints after patching

Duality is useful only if it survives both truncation and the diagonal choice. Group-ring-valued pairings are particularly well adapted to this task because projective base change preserves their perfectness. The limiting pairing controls ranks and adjoints, but its consequences stop short of freeness and component coverage.

### 12.1 Pairing-compatible finite shadows

Suppose each finite level carries a companion module $M_N'$ and a perfect sesquilinear pairing

$$
H_N:M_N\times M_N'\longrightarrow\Lambda_N,
\tag{12.1}
$$

where the second scalar action is twisted by

$$
\iota_N([\delta])=[\delta^{-1}].
\tag{12.2}
$$

Assume both modules are finite projective, hence free in the local group-ring setting. For $N$ large relative to $d$, base change gives

$$
H_{N,d}:
(M_N/\mathfrak b_dM_N)
\times(M_N'/\mathfrak b_dM_N')
\longrightarrow C_d.
\tag{12.3}
$$

The involution preserves $\mathfrak b_d$, so the pairing is well defined. Projective base change carries the duality isomorphism

$$
M_N'\xrightarrow{\sim}
\operatorname{Hom}_{\Lambda_N}(M_N,\Lambda_N)
\tag{12.4}
$$

to the analogous isomorphism over $C_d$. Thus (12.3) is perfect.

The matrices of (12.3), the companion actions, the involution, and every named adjoint operator are finite data. Include them in $\mathscr D_d$ before taking the diagonal. An $\mathcal O$-valued pairing alone requires a different construction: it naturally pairs diamond coinvariants on one side with invariants on the other. Unless projectivity and the norm identify those invariants with coinvariants, reducing both entries by $\mathfrak b_d$ need not define a pairing. This descent issue must be resolved before compactness is invoked.

### 12.2 Passage of perfectness to the limit

Let

$$
M_\infty'=\varprojlim_d\mathscr M_d'.
$$

The companion version of Lemma 6.1 makes it free of the same rank over $S_\infty$. The compatible pairings define

$$
H_\infty:M_\infty\times M_\infty'
\longrightarrow S_\infty.
\tag{12.5}
$$

It is sesquilinear for the continuous involution

$$
\iota_\infty(1+z_i)=(1+z_i)^{-1}.
\tag{12.6}
$$

**Proposition 12.1 (perfectness survives patching).** The pairing (12.5) induces an isomorphism

$$
M_\infty'\xrightarrow{\sim}
\operatorname{Hom}_{S_\infty}(M_\infty,S_\infty),
\tag{12.7}
$$

with the scalar twist from (12.6).

**Proof.** Both sides are finite free. Reducing (12.7) modulo every $\mathfrak b_d$ gives the perfect duality isomorphism in the selected finite shadow. Hence the kernel and cokernel reduce to zero modulo the maximal ideal. Nakayama kills the cokernel, while equal free ranks or separatedness kills the kernel. Equivalently, the determinant of a pairing matrix is a unit modulo every $\mathfrak b_d$, hence a unit in $S_\infty$. $\square$

Augmentation of (12.5) is a perfect pairing

$$
M\times M'\longrightarrow\mathcal O
\tag{12.8}
$$

because both modules are $S_\infty$-free and base change of (12.7) is exact. With coefficient torsion or without projectivity, an ordinary perfect pairing into $\mathcal O$ can fail and should be replaced by the appropriate derived duality.

### 12.3 Adjoint Hecke actions

Suppose the finite-level adjoint operation satisfies

$$
H_N(tx,y)=H_N(x,t^*y).
\tag{12.9}
$$

The first $d$ named operators and their adjoints were retained at precision $d$. Passing to the limit gives an isomorphism between acting algebras

$$

- : A_\infty\xrightarrow{\sim}A_\infty'
  \tag{12.10}
  $$

and

$$
H_\infty(tx,y)=H_\infty(x,t^*y).
\tag{12.11}
$$

If the same acting algebra occurs on both sides, (12.10) is an involution only when the finite normalizations make $**$ the identity. Auxiliary operators can acquire an inverse or a central-unit factor under adjunction; the normalization must be carried through the shadows.

The perfect pairing implies equality of the two $S_\infty$-ranks and transports annihilators under the adjoint isomorphism. It can also show that a determinant or discriminant remains a unit through the limit. It does not make $A_\infty$ Gorenstein without an additional rank-one duality statement for the algebra itself.

### 12.4 What self-duality does and does not say

A dual pair becomes a self-dual module only if there are compatible identifications

$$
M_N'\xrightarrow{\sim}M_N
\tag{12.12}
$$

at finite level, preserved by the diagonal and consistent with coefficients, central characters, and orientations. Perfectness of a pairing between two modules does not supply (12.12).

Even after a genuine self-duality has been proved, the conclusions remain limited. It gives

$$
M_\infty\simeq
\operatorname{Hom}_{S_\infty}(M_\infty,S_\infty)
\tag{12.13}
$$

and the adjoint identities. It does not imply:

- freeness over the singular ring $R_\infty$ or $A_\infty$;
- faithfulness of the $R_\infty$-action;
- support on every irreducible component;
- vanishing of a nilpotent annihilator;
- exact augmentation of the acting algebra without saturation.

Those conclusions concern projective dimension, action kernels, components, and base-change exactness. Duality is compatible with each question but does not answer it alone.

## 13. Frames and harmless power-series variables

Framing coordinates are introduced to make deformation problems representable and local products manageable. They are harmless only in the precise sense of a formally smooth power-series extension with a scalar-extended module. This chapter proves the dimension and depth shifts and distinguishes true smooth variables from presentation padding.

### 13.1 The framed variable count

Frames remove conjugation ambiguity by replacing an unframed deformation problem with a formally smooth cover. Let the residual representation have rank $d$, and let $T$ be a nonempty set of framed places. Under the scalar-centralizer and representability hypotheses, the relative frame dimension is

$$
c_T=d^2|T|-h^0(K,\operatorname{ad}\bar\rho).
\tag{13.1}
$$

For an absolutely irreducible rank-two representation,

$$
c_T=4|T|-1.
\tag{13.2}
$$

There is then a noncanonical isomorphism

$$
R^{\square_T}\simeq R[[w_1,\ldots,w_{c_T}]],
\tag{13.3}
$$

and the same number of frame coordinates occurs at every auxiliary level. Because the frame convention is fixed before diagonalization, the patched relation gives

$$
R_\infty^{\square_T}\simeq
R_\infty[[w_1,\ldots,w_{c_T}]]
\tag{13.4}
$$

provided the finite-level frame torsors and their coordinates were included compatibly.

Auxiliary local frames have their own count. At a regular rank-two Taylor--Wiles place, the unframed local ring is formally smooth of relative dimension one over the diamond algebra, while the framed local ring is formally smooth of relative dimension three. The extra two variables position the lifted eigenlines. They are distinct from the global frame directions in (13.1), and neither kind is a diamond variable.

Consequently

$$
\dim R_\infty^{\square_T}
=\dim R_\infty+c_T,
\tag{13.5}
$$

and the corresponding ambient presentation dimension increases by the same number. Relation counts are unchanged under this honest power-series extension.

### 13.2 Descent along a regular smooth sequence

A power-series extension is harmless for a module only when the module is extended along it. Let $A$ be a complete Noetherian local ring, and for a nonzero finite $A$-module $L$ put

$$
B=A[[w_1,\ldots,w_c]],
\qquad
L_B=B\widehat\otimes_A L
\tag{13.6}
$$

Then

$$
w_1,\ldots,w_c
\tag{13.7}
$$

is regular on both $B$ and $L_B$, and

$$
B/(w_1,\ldots,w_c)\simeq A,
\qquad
L_B/(w_1,\ldots,w_c)L_B\simeq L.
\tag{13.8}
$$

Flat base change and the regular-sequence depth shift give

$$
\operatorname{depth}_BL_B
=\operatorname{depth}_AL+c,
\tag{13.9}
$$

while

$$
\dim_BL_B=\dim_AL+c.
\tag{13.10}
$$

Thus Cohen--Macaulayness, maximal Cohen--Macaulayness relative to equal ring dimensions, and finite projective dimension transport in the expected way. Freeness transports in both directions: a finite module $L$ is $A$-free exactly when $L_B$ is $B$-free.

If instead $L$ is merely regarded as a $B$-module through $B\twoheadrightarrow A$, every $w_i$ annihilates it. The sequence (13.7) is then maximally nonregular on $L$, and (13.9) is false. A ring-level frame isomorphism alone does not determine the correct framed module.

### 13.3 Padding variables are different

Uniform presentations sometimes add a variable $y$ at a level where it is not needed and add the linear relation $y=0$. This replacement has the form

$$
P/I\simeq P[[y]]/(I,y).
\tag{13.11}
$$

It does not add a smooth direction to the quotient ring. The variable and relation cancel at the presentation level. In the quotient, $y$ is zero, so it cannot be a regular element on any nonzero module.

Removing the pair in (13.11) is an isomorphism of presented rings, not descent along a regular element of the quotient. By contrast, removing a frame variable in (13.8) is quotienting a larger ring by a genuine regular element. Confusing these operations changes both dimension and depth counts.

Zero entries may be appended to a relation list after all padded variables have been killed by their linear relations. Appending a zero relation does not change an ideal, but it also does not create codimension. A height-equals-relations argument must use the minimal effective relations, including the linear padding relations before cancellation.

### 13.4 The framed-to-unframed patched pair

Assume the finite-level system supplies compatible scalar-extension identifications for modules and action algebras. Patching then gives a diagram

$$
\begin{array}{ccc}
R_\infty^{\square_T}&\twoheadrightarrow&A_\infty^{\square_T}\\
\downarrow&&\downarrow\\
R_\infty&\twoheadrightarrow&A_\infty
\end{array}
\tag{13.12}
$$

with

$$
R_\infty^{\square_T}\simeq R_\infty[[\mathbf w]],
\qquad
M_\infty^{\square_T}\simeq
R_\infty^{\square_T}\widehat\otimes_{R_\infty}M_\infty,
\tag{13.13}
$$

and analogous statements for the action algebra when its scalar extension is saturated. Quotienting by $(\mathbf w)$ recovers the unframed pair. The sequence is regular on the two rings and on the scalar-extended module, so dimensions and depths decrease by exactly $c_T$.

The isomorphisms in (13.3), (13.4), and (13.13) are noncanonical: they depend on frame coordinates. The quotient maps forgetting the frames are canonical relative to the represented deformation problems. Component choices are not removed by frames; all rings in (13.12) must still use the same old local branches.

## 14. Choices, genuine towers, and uniqueness

Patching makes many choices visible: auxiliary sets, generators, bases, relation lifts, finite representatives, and a diagonal subsequence. Some are coordinate choices and disappear up to noncanonical isomorphism; others can change the accumulation object. Comparing this construction with a genuine transitioned tower identifies exactly what is canonical and exactly which properties are common to both methods.

### 14.1 Coordinate and basis changes

Several choices change the displayed patched object without changing its mathematical role.

Changing a generator of the $i$th cyclic diamond factor by a unit $u\in\mathbf Z_\ell^\times$ changes coordinates through

$$
z_i\longmapsto(1+z_i)^u-1.
\tag{14.1}
$$

Swapping the selected ordered eigenline changes the diamond character by inversion and gives

$$
z_i\longmapsto(1+z_i)^{-1}-1,
\tag{14.2}
$$

together with the corresponding change of auxiliary eigenvalue coordinate. These are continuous automorphisms of $S_\infty$ and, when extended to the full presentation, give noncanonical isomorphisms of the resulting coherent finite diagrams.

Changing a free basis of $M_N$ conjugates every action matrix by an element of $\operatorname{GL}_r(S_N)$. A compatible change of bases at finite precision passes to an element of $\operatorname{GL}_r(S_\infty)$ and produces an isomorphic patched module with conjugate action. Changing a minimal relation tuple by an invertible matrix changes the generators $f_i$ but not their ideal. Changing lifts of cotangent coordinates acts by a continuous automorphism of the presentation ring when both presentations are minimal.

These statements require compatibility. Arbitrary independent coordinate changes at every precision need not have a limit. The diagonal construction either marks the choices or includes their transition isomorphisms so that the limiting automorphism exists.

### 14.2 Dependence on the diagonal subsequence

Within one fixed coherent path (4.1), changing finite representatives or compatible markings gives a noncanonically isomorphic inverse limit. More generally, if two coherent shadow systems are pro-isomorphic by compatible isomorphisms at cofinal precisions, their inverse limits are noncanonically isomorphic with all named structures.

There need not be a pro-isomorphism between two different diagonal paths. A sequence in a finite discrete space can have several accumulation values; the same phenomenon occurs simultaneously at every precision. Different subsequences can therefore produce nonisomorphic patched deformation rings or action algebras, even though they have the same dimensions, ranks, relation bounds, and augmentation quotient.

The valid independence statement is consequently modest:

- coordinate choices, bases, and redundant presentation pairs change a fixed coherent construction only up to noncanonical isomorphism;
- replacing a coherent system by a pro-isomorphic one does the same;
- arbitrary auxiliary sets and arbitrary diagonal subsequences are guaranteed to produce some patched object satisfying the exported axioms, not one canonical object;
- uniqueness across two such choices requires an additional comparison theorem.

In particular, the original ring $R$ and module $M$ recovered at augmentation are canonical relative to the starting deformation and automorphic problems, while the thickened object above them can depend on the accumulation choices.

### 14.3 The genuine-transition variant

Occasionally geometry supplies actual maps

$$
R_{N+1}\longrightarrow R_N,
\qquad
M_{N+1}\longrightarrow M_N,
\qquad
\mathbb T_{N+1}\longrightarrow\mathbb T_N,
\tag{14.3}
$$

compatible with genuine quotients of diamond groups. If the ring and module maps are transitive, the module reductions satisfy base change, and the relevant transition maps are surjective or Mittag--Leffler, one may take their inverse limits directly.

Even in this case three checks remain. First, the $M_N$ must be free of uniform rank over the appropriate diamond quotients; otherwise Lemma 6.1 does not apply. Second, exact augmentation must be passed through the limit using Lemma 5.1. Third, pairings must obey an actual pullback or trace identity, including every degree factor. The existence of (14.3) does not make inverse limits exact by itself.

Relative to the specified transitions, the resulting inverse limit is canonical. If one forgets those transitions and applies diagonal patching, the diagonal limit agrees with the genuine one when the coherent shadows are the reductions of that same inverse system. This is a pro-isomorphism statement. It does not say that every transitioned tower has the same limit as every unrelated Taylor--Wiles family.

### 14.4 The common exported axioms

Both constructions yield the same kind of algebraic interface:

| property                                | diagonal construction                    | genuine-transition construction         |
| --------------------------------------- | ---------------------------------------- | --------------------------------------- |
| source $S_\infty$                       | fixed completed group algebra            | inverse limit of nested group algebras  |
| patched ring                            | limit of stabilized presentation shadows | limit of actual ring maps               |
| patched module                          | limit of stabilized free shadows         | limit of actual module maps             |
| arithmetic maps between original levels | absent                                   | supplied as data                        |
| freeness mechanism                      | Lemma 6.1                                | Lemma 6.1                               |
| augmentation mechanism                  | finite exact shadows and Mittag--Leffler | finite exact levels and Mittag--Leffler |
| canonicity                              | relative to a coherent diagonal path     | relative to the stated transitions      |

After construction, the later commutative algebra uses only the maps

$$
S_\infty\longrightarrow R_\infty\longrightarrow A_\infty,
$$

the module $M_\infty$, its rank and depth, the presentation and dimension bounds, its support, and its augmentation. It does not use the origin of the transition arrows. This is why diagonal patching and genuine towers can export identical axioms while having very different arithmetic meanings.

## 15. Failure modes and a hostile audit

Most gaps in patching proofs arise from replacing a structural hypothesis by a numerical resemblance. The following failure modes are organized by the step they break: compactness, freeness, exactness, depth, support, or the relation count. The closing ledger is meant to be applied before any conclusion is carried out of the patched setting.

### 15.1 Failure of uniform size

The finite-shadow argument begins with one finite universe at each precision. Uniformity is what makes that universe finite.

If the normalized ranks

$$
r_N=\frac{\operatorname{rank}_{\mathcal O}M_N}{|\Delta_N|}
\tag{15.1}
$$

are unbounded, the precision-$d$ modules are not quotients of one fixed finite module $C_d^r$. Even if each individual module is free, no fixed-rank limit lemma applies. Selecting a subsequence on which $r_N$ is constant is legitimate only when the sequence takes some value infinitely often; boundedness alone permits that selection, while unboundedness need not.

In a balanced system the analogous quantities are the numbers of generators and first relations. An unbounded sequence of square sizes produces infinitely many possible finite modules even over one fixed $C_d$. Replacing every module by a larger module with artificial free summands changes its action, pairing, and augmentation quotient and is not a harmless repair.

On the ring side, unbounded numbers of relative variables or relations prevent all $R_N$ from being quotients of one fixed $P_\infty$ with marked bounded tuples. Killing the absolute enlarged dual Selmer group is not enough if the relative obstruction groups for the actual local base remain unbounded.

Uniformity also includes $q$. If the cardinality of $Q_N$ varies, there is no one group $\mathbf Z_\ell^q$ and no one regular ring $S_\infty$ with the displayed dimension. Padding to a fixed larger cardinality is valid only when the added primes and their extra primal directions are included in the numerical ledger.

### 15.2 Diamond nonfreeness and torsion

The equation

$$
\operatorname{rank}_{\mathcal O}M_N
=r|\Delta_N|
\tag{15.2}
$$

is necessary for diamond freeness and does not prove it. Stabilizers in a geometric covering, a trivial diamond action, or a nonprojective lattice can all have the expected coefficient rank. A proof of freeness must construct local bases, prove projectivity over the group algebra, or prove the vanishing

$$
\operatorname{Tor}_1^{\Lambda_N}(M_N,k)=0.
\tag{15.3}
$$

When (15.3) holds for a finite module over the local ring $\Lambda_N$, flatness and hence freeness follow. Vanishing over $\mathcal O$ is not a substitute.

Coefficient torsion contradicts diamond freeness because $\Lambda_N$ is $\mathcal O$-flat. It also prevents an ordinary perfect $\mathcal O$-valued self-duality: the dual into the torsion-free ring $\mathcal O$ cannot recover a nonzero torsion submodule. Reducing modulo torsion before patching changes the augmentation module and can change the Hecke algebra; it is not an innocent simplification.

Balancedness accommodates some nonfree modules but supplies only the square presentation (8.5). In mixed characteristic, the augmentation-ideal example of Section 8.6 shows that even an $\mathcal O$-torsion-free balanced module can acquire coefficient torsion in its coinvariants. In equal characteristic its ordinary coinvariants remain $\mathcal O$-free, but its higher derived coinvariants are still nonzero. The honest remedies in either case are to prove derived coinvariant concentration and torsion-freeness, or to retain a perfect complex.

### 15.3 Bad limits and incompatible structures

Several failures can occur even when all cardinalities are bounded.

**Invented transitions.** A chosen quotient $\Delta_{N+1}\to\Delta_N$ does not induce maps of deformation rings or modules attached to unrelated prime sets. Taking an inverse limit over nonexistent maps has no mathematical meaning.

**Unmarked isomorphism types.** Stabilizing the isomorphism class of each truncation without stabilizing its reduction map can produce incompatible representatives. Marked quotient maps or stabilized reduction isomorphisms are required.

**Nonexact inverse limits.** A compatible family in the quotient terms of (5.1) need not lift when the kernel system is not Mittag--Leffler. Finiteness or surjective kernel transitions must be checked before passing a surjection to the limit.

**Unclosed limiting ideals.** From membership modulo every open ideal one obtains membership in the closure of an ideal. Equality with the algebraic ideal uses Noetherianity and finite generation. Without them, $P_\infty/I$ can fail to be separated.

**Incompatible relation generators.** A uniform relation number does not itself produce $f_1,\ldots,f_b$. Their residue classes must be part of the diagonal data. Otherwise the limiting kernel may be known only as an unspecified closed ideal.

**Mismatched topologies.** The module shadows use $\mathfrak b_d$, while the ring shadows use powers of $\mathfrak p_\infty$. One must prove both filtrations are cofinal with their intended adic topologies and choose $\nu(d)$ so the ring action factors through a finite shadow.

**Infinite operator families.** A finite-pigeonhole argument cannot retain infinitely many endomorphisms at once. An enumeration and a second diagonal, or a proved finite generating family, is necessary.

**Pairings on the wrong quotients.** A coefficient-valued pairing need not descend after quotienting both entries. Sesquilinear group-ring-valued pairings do descend under projective base change. The shadow must be defined before its matrix is stabilized.

**Forgotten augmentation targets.** A map from a finite shadow to the full ring $R$ is not a finite diagram. The target must be truncated, and the exact kernels must be included if recovery is to survive the limit.

### 15.4 Insufficient depth and hidden components

Freeness over $S_\infty$ gives a regular sequence of length $q+1$. It gives only a lower bound for depth over an arbitrary larger acting ring. Equality in (10.9) used the finite action quotient and the finite-map depth theorem. Omitting that finiteness loses the equality.

Even after

$$
\operatorname{depth}_{R_\infty}M_\infty=q+1
$$

has been proved, maximal Cohen--Macaulayness requires $\dim R_\infty=q+1$. If the ring has larger dimension, the module is Cohen--Macaulay only on its support.

Maximal Cohen--Macaulayness over a singular ring is not freeness. Auslander--Buchsbaum requires finite projective dimension. Regularity of $S_\infty$ proves $S_\infty$-freeness; it does not make $R_\infty$ regular.

The support can be one component of a reducible equidimensional ring. Equality

$$
\dim\operatorname{Supp}M_\infty=\dim R_\infty
$$

does not give full support. Full support gives only a nilpotent annihilator, and faithfulness additionally requires reducedness or a direct annihilator argument. Nilpotents are invisible to the underlying topological support.

Finally, augmentation recovery does not make the augmentation variables regular on $R_\infty$. The quotient identity (7.3) is underived. Dimension and depth descent for the ring require the Tor or regular-sequence hypotheses of Section 7.5.

### 15.5 Ineffective relation bounds

The relation ledger can fail in four distinct ways.

First, the absolute enlarged dual Selmer group may vanish while the relative dual group for the chosen local base is nonzero. The latter, not the former, bounds relations over that base.

Second, an obstruction space may only give necessary obstruction classes. Without completeness and effectiveness, its dimension is not a bound on minimal relations.

Third, moving local coordinates between the base and the relative source changes both tangent and obstruction conditions. Counting a framed auxiliary coordinate in the base and again among global variables makes the lower bound falsely large.

Fourth, padding variables without adding linear relations changes the represented ring. Correct padding adds a variable-relation pair. Appending zero entries is permitted only after that pair has been accounted for.

Even an effective bound gives

$$
\dim R_\infty\geq\dim P_\infty-b,
$$

not equality. Complete-intersection conclusions require the further height equality. A relation list can have the expected length while cutting too little because its elements share a component or a common factor.

### 15.6 The final audit ledger

Before using a patched pair, every row of the following ledger should have a definite answer.

| item                 | required verification                                                              | error prevented                             |
| -------------------- | ---------------------------------------------------------------------------------- | ------------------------------------------- |
| coefficient ring     | complete DVR, finite residue field, fixed uniformizer                              | nonfinite shadow sets and ambiguous torsion |
| diamond groups       | exact-level order and chosen generators                                            | wrong ranks and coordinate maps             |
| level ideals         | $\mathfrak c_N$ tends to zero in the chosen topology                               | finite equations surviving incorrectly      |
| common source        | one fixed $P_\infty$ and one local-base convention                                 | double-counted variables                    |
| relations            | effective uniform bound and marked tuples                                          | fictitious limiting equations               |
| module size          | fixed free rank or bounded balanced presentation                                   | loss of compactness                         |
| arithmetic levels    | no transition claimed without a construction                                       | false ramification transfer                 |
| finite shadows       | all objects and targets genuinely finite                                           | invalid pigeonhole argument                 |
| reduction maps       | marked and compatible                                                              | nonexistence of an inverse system           |
| inverse limits       | surjectivity or Mittag--Leffler where exactness is used                            | lost quotient elements                      |
| topology             | cofinal ideals and closed finite submodules                                        | nonseparated limits                         |
| actions              | $S_\infty$, $R_\infty$, and Hecke actions commute                                  | ill-defined scalar limit                    |
| action algebra       | defined as a faithful image                                                        | confused annihilator                        |
| augmentation         | exact kernels retained at finite precision                                         | only a surjection instead of recovery       |
| Hecke base change    | saturation checked                                                                 | invisible algebra classes after quotient    |
| $S_\infty$-freeness  | compatible free bases or an equivalent projectivity proof                          | rank-counting fallacy                       |
| balanced upgrade     | derived Tor vanishing and torsion-free quotient, or complex concentration          | unjustified freeness                        |
| dimensions           | all frame and coefficient directions counted once                                  | false numerical equality                    |
| depth                | the acting ring named and finite-map hypotheses checked                            | transferring depth without cause            |
| projective dimension | finite when target-ring freeness is claimed                                        | false freeness over a singular ring         |
| support              | component coverage proved                                                          | dimension mistaken for full support         |
| annihilator          | reducedness, associated-prime faithfulness, saturation, or direct vanishing proved | near faithfulness mistaken for faithfulness |
| pairings             | correct quotient, involution, companion, and torsion hypotheses                    | false self-duality                          |
| frame descent        | module is a genuine scalar extension                                               | zero variables called regular               |
| uniqueness           | pro-isomorphism or genuine transitions supplied                                    | a chosen limit called canonical             |

Passing this ledger is not an embellishment of the construction. Each row is used in a displayed theorem above, and failure of any one row changes the conclusion that can be exported.

## 16. The patched-pair theorem package

The preceding chapters deliberately kept conditional conclusions separate. The final package now assembles them without erasing those conditions. Its first theorem gives the free-module construction, its second identifies the exact balanced and derived substitutes, and its final interface records what remains available for the subsequent comparison of deformation and action rings.

### 16.1 The free-module theorem

We now collect the construction into one reusable statement. The hypotheses are deliberately explicit so that each conclusion can be traced to its source.

**Theorem 16.1 (standard patched pair).** Let $(\mathcal O,\varpi,k)$ be a complete DVR with finite residue field of characteristic $\ell$. Let

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad
\mathfrak a_\infty=(z_1,\ldots,z_q),
\tag{16.1}
$$

and let

$$
P_\infty
=R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]].
\tag{16.2}
$$

Suppose a controlled presentation-compatible Taylor--Wiles system satisfies the following hypotheses.

1. For every $N$,

   $$
   \Delta_N\simeq(\mathbf Z/\ell^N\mathbf Z)^q,
   \qquad
   \Lambda_N\simeq S_\infty/\mathfrak c_N,
   $$

   with the chosen coordinates and level ideals (2.7).
2. There are compatible surjections $P_\infty\twoheadrightarrow R_N$ whose kernels are

   $$
   \mathfrak c_NP_\infty+(f_{N,1},\ldots,f_{N,b}),
   $$

   where $b$ is uniform and the relation bound comes from a complete effective relative obstruction theory or an equally explicit algebraic presentation theorem.
3. Each $M_N$ is finite free of one fixed positive rank $r$ over $\Lambda_N$.
4. The actions factor through faithful finite action algebras:

   $$
   R_N\twoheadrightarrow\mathbb T_N
   \lhook\joinrel\longrightarrow\operatorname{End}_{\Lambda_N}(M_N),
   $$

   and the diamond action agrees with the composite from $S_\infty$.
5. Augmentation gives compatible isomorphisms

   $$
   R_N/\mathfrak a_NR_N\simeq R,
   \qquad
   M_N/\mathfrak a_NM_N\simeq M.
   $$

   If exact Hecke recovery is asserted, also assume the finite-level Hecke isomorphisms and their saturation data.
6. The fixed old local components, determinant, frames, named operators, module bases, relation tuples, augmentation maps, and any pairings admit the finite marked shadows of Chapters 3 and 4. Equivalently, pass to the coherent diagonal subsequence constructed there.

In an arithmetic realization, items 1 and 2 come from the Taylor--Wiles prime theorem, the regular local calculation, global duality, and effective relative obstruction theory. Items 3--6 are the automorphic or geometric input: a torsor or projectivity theorem for diamond freeness, a uniform multiplicity theorem, a Hecke-valued family satisfying every local condition and generating the stated quotient of $R_N$, exact level-lowering control, saturation at augmentation, and integral duality when pairings are used. None of these module-side statements follows from prime selection alone.

Then there are complete local rings and a finite module

$$
R_{\mathrm{loc}}\longrightarrow R_\infty
\twoheadrightarrow A_\infty
\lhook\joinrel\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty),
\qquad
S_\infty\hookrightarrow R_\infty,
\tag{16.3}
$$

with the following properties.

**(a) Presentation.** There are elements $f_1,\ldots,f_b\in P_\infty$ such that

$$
R_\infty=P_\infty/(f_1,\ldots,f_b).
\tag{16.4}
$$

If $I_\infty=\ker(P_\infty\to R_\infty)$, its intrinsic relation number is

$$
c_\infty
=\mu_{P_\infty}(I_\infty)
=\dim_k I_\infty/\mathfrak p_\infty I_\infty
\leq b,
\qquad
R_\infty=P_\infty/(g_1,\ldots,g_{c_\infty})
\tag{16.4a}
$$

for a minimal generating tuple. Thus $b$ remains the uniform arithmetic bound needed for compactness, while $c_\infty$ records the actual codimension input after patching.

The maps from $R_{\mathrm{loc}}$ and $S_\infty$ are the structural maps induced from $P_\infty$.

**(b) Auxiliary freeness.** One has

$$
M_\infty\simeq S_\infty^{\oplus r}.
\tag{16.5}
$$

In particular $M_\infty$ is finite, complete, coefficient-torsion-free, and faithful over $S_\infty$.

**(c) Acting algebra.** The ring $A_\infty$ is the image of $R_\infty$ on $M_\infty$. It is a finite local $S_\infty$-algebra, the map $S_\infty\to A_\infty$ is injective, and

$$
A_\infty
=R_\infty/\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{16.6}
$$

Consequently

$$
\dim A_\infty=q+1.
\tag{16.7}
$$

**(d) Exact augmentation.** There are action-compatible isomorphisms

$$
R_\infty/\mathfrak a_\infty R_\infty\simeq R,
\qquad
M_\infty/\mathfrak a_\infty M_\infty\simeq M.
\tag{16.8}
$$

Moreover

$$
\operatorname{Tor}^{S_\infty}_i(\mathcal O,M_\infty)=0
\qquad(i>0).
\tag{16.9}
$$

There is always a surjection $A_\infty/\mathfrak a_\infty A_\infty\twoheadrightarrow\mathbb T$ onto the minimal acting image. It is an isomorphism under augmentation saturation.

**(e) Dimensions.** Writing $d_{\mathrm{loc}}=\dim R_{\mathrm{loc}}$, one has

$$
\dim S_\infty=q+1,
\qquad
\dim P_\infty=d_{\mathrm{loc}}+q+G,
\tag{16.10}
$$

and

$$
\dim R_\infty
\geq d_{\mathrm{loc}}+q+G-c_\infty
\geq d_{\mathrm{loc}}+q+G-b.
\tag{16.11}
$$

The support of $M_\infty$ has exact dimension $q+1$.

**(f) Depth.** The exact depth statements are

$$
\operatorname{depth}_{S_\infty}M_\infty
=\operatorname{depth}_{A_\infty}M_\infty
=\operatorname{depth}_{R_\infty}M_\infty
=q+1,
\tag{16.12}
$$

and

$$
\dim_{R_\infty}M_\infty=q+1.
\tag{16.13}
$$

Thus $M_\infty$ is Cohen--Macaulay on its support. It is maximal Cohen--Macaulay over $R_\infty$ when $\dim R_\infty=q+1$.

**(g) Support.** One has

$$
\operatorname{Supp}_{R_\infty}M_\infty
=V(\ker(R_\infty\to A_\infty)).
\tag{16.14}
$$

If $R_\infty$ is catenary and equidimensional of dimension $q+1$, this support is a union of irreducible components. It is all of $\operatorname{Spec}R_\infty$ exactly when the action is nearly faithful. Full support plus reducedness gives faithfulness; without reducedness only a nilpotent annihilator follows.

Faithfulness without reducedness follows under any of the following stronger hypotheses: $M_\infty$ is nonzero free over $R_\infty$; the localized action is faithful at every associated prime of $R_\infty$; or the minimal action is faithful and the annihilator satisfies the augmentation saturation (11.12). These tests retain the nilpotent structure of the ring.

**(h) Pairings.** If compatible projective group-ring-valued perfect pairings were included, they patch to a perfect $S_\infty$-valued pairing with the diamond involution. It descends perfectly to the minimal-level modules and carries the named Hecke adjoints. It identifies a module with itself only when compatible finite-level self-identifications were also supplied.

**Proof.** Lemma 2.1 makes the level equations vanish in every fixed shadow. Proposition 3.1 and Lemma 4.1 produce coherent marked diagrams. Proposition 5.2 patches the relation tuple and proves (16.4). Lemma 6.1 proves (16.5), and faithfulness of scalar multiplication gives the injections from $S_\infty$. The action images give (16.6), their embedding in a finite free endomorphism module makes them finite over $S_\infty$, and integrality gives (16.7).

The finite augmentation sequences satisfy Mittag--Leffler, so Lemma 5.1 proves (16.8). Freeness gives (16.9). Krull's height theorem gives (16.11). Finite-map depth and dimension comparison along

$$
S_\infty\hookrightarrow A_\infty
\longleftarrow R_\infty
$$

gives (16.12) and (16.13). The support identity is the annihilator formula for a finite module; its component refinements are those of Chapter 11. Proposition 12.1 proves the final pairing assertion. $\square$

The standard numerical strengthening is immediate but conditional in exactly the right places.

**Corollary 16.2 (sharp dimension and depth package).** In Theorem 16.1, assume

$$
d_{\mathrm{loc}}+G-b=1
\tag{16.15}
$$

and assume one of the dimension-ceiling mechanisms of Section 9.4. Then

$$
\dim R_\infty=\dim S_\infty=q+1,
\tag{16.16}
$$

and $M_\infty$ is maximal Cohen--Macaulay over $R_\infty$. If $P_\infty$ is Cohen--Macaulay, the two equalities force $c_\infty=b$: indeed $\dim P_\infty-b=q+1=\dim R_\infty$, and Section 9.5 applies. Hence a minimal patched relation tuple is regular and $R_\infty$ is Cohen--Macaulay. If $P_\infty$ is regular, $R_\infty$ is a complete intersection. If $R_\infty$ is regular, or if $M_\infty$ separately has finite projective dimension over the Cohen--Macaulay ring $R_\infty$, then $M_\infty$ is $R_\infty$-free of positive rank and therefore faithful, with no reducedness hypothesis.

**Proof.** Equation (16.15) turns the lower bound (16.11) into $\dim R_\infty\geq q+1$, while the assumed ceiling gives the reverse inequality. Thus (16.16) holds, and (16.12)--(16.13) make $M_\infty$ maximal Cohen--Macaulay. Also

$$
\dim P_\infty=d_{\mathrm{loc}}+q+G=q+1+b,
$$

so a Cohen--Macaulay source satisfies the sharp-$b$ equality of Section 9.5. That section gives $c_\infty=b$, regularity of a minimal relation tuple, and the stated Cohen--Macaulay or complete-intersection conclusion. Finally, Section 10.5 and Corollary 11.2 give $R_\infty$-freeness under the two respective projective-dimension hypotheses. The rank is positive because $M_\infty\simeq S_\infty^r$ with $r>0$, and a nonzero free module is faithful. $\square$

Before this final freeness clause is invoked, the dimension and depth clauses alone supply no component coverage. If every minimal component is separately known to occur in the support, the action is nearly faithful. It is faithful when $R_\infty$ is reduced, when the action is faithful at every associated prime, or when the annihilator saturation criterion of Section 11.4 applies.

### 16.2 The balanced and derived theorem

**Theorem 16.3 (balanced patching).** Retain all hypotheses of Theorem 16.1 except finite-level diamond freeness. Suppose instead that every $M_N$ is balanced over $\Lambda_N$ with a square presentation of size at most one fixed $d$, and that compatible presentation matrices and augmentation maps are included in the coherent shadows. Then there is a finite complete $S_\infty$-module $M_\infty$ with compatible $R_\infty$-action, exact ordinary augmentation recovery, and a square presentation

$$
S_\infty^d\longrightarrow S_\infty^d
\longrightarrow M_\infty\longrightarrow0.
\tag{16.17}
$$

No general $S_\infty$-freeness or maximal-depth conclusion follows from these hypotheses.

If the left map in (16.17) is injective and $M_\infty\ne0$, then

$$
\operatorname{depth}_{S_\infty}M_\infty=q.
\tag{16.18}
$$

If instead a separate theorem proves

$$
\operatorname{Tor}^{S_\infty}_i(\mathcal O,M_\infty)=0
\quad(i>0)
$$

and proves that the augmented module is nonzero and $\mathcal O$-torsion-free, then Proposition 8.2 upgrades $M_\infty$ to a finite free $S_\infty$-module of positive rank. At that point the conclusions of Theorem 16.1 that use auxiliary freeness apply, subject to the same separate hypotheses on the action image, saturation, dimensions, support, and pairings.

**Proof.** Stabilizing the uniformly bounded square presentations by identity blocks and patching their marked matrices gives (16.17), as proved in Section 8.1. The same finite-shadow construction patches the ring action, and the Mittag--Leffler argument of Chapter 7 gives exact ordinary augmentation because those maps were retained. These steps provide no left exactness for (16.17), which is why freeness and maximal depth are absent without further input.

If the left map is injective, (16.17) is a length-one free resolution. Its nonzero cokernel has projective dimension exactly one: an injective square matrix over the domain $S_\infty$ has rank-zero cokernel, so that cokernel cannot be a nonzero free module. Auslander--Buchsbaum therefore gives depth $q$. Under the alternative derived hypotheses, Proposition 8.2 supplies the asserted freeness, after which each additional conclusion is obtained from the same separately named hypothesis used in Theorem 16.1. $\square$

If the natural finite-level objects are perfect complexes, retain them as such. A bounded perfect patched complex whose derived augmentation is a finite free $\mathcal O$-module in one degree is itself a finite free $S_\infty$-module in that degree by Proposition 8.3. If derived augmentation has more than one nonzero degree, the exported object remains a perfect complex with its actual amplitude; no single cohomology module inherits freeness without another concentration theorem.

**Theorem 16.4 (perfect-complex patching).** Retain the ring and presentation hypotheses of Theorem 16.1. Replace its module, action, and augmentation hypotheses by strict complexes $C_N^\bullet$ of finite free $\Lambda_N$-modules, all supported in one interval $[a,h]$ and having one fixed rank $r_i$ in each degree. Assume chosen bases, differential matrices, strict chain actions of $R_N$ compatible with the diamond action, and derived augmentation comparisons with one fixed bounded complex $C^\bullet$ of finite free $\mathcal O$-modules are included in the marked shadows. If a duality is desired, assume companion complexes and chain-level perfect pairings, including their shifts, signs, and adjoints, are also included.

Then diagonal patching produces a perfect complex $C_\infty^\bullet$ of finite free $S_\infty$-modules, supported in $[a,h]$, with the patched action and with exact derived augmentation

$$
\mathcal O\otimes_{S_\infty}^{\mathbf L}C_\infty^\bullet
\simeq C^\bullet.
\tag{16.19}
$$

Compatible perfect chain pairings pass to the limit and specialize to the stated pairing on $C^\bullet$. If $C^\bullet\simeq\mathcal O^{\oplus r}[-j]$, then

$$
C_\infty^\bullet\simeq S_\infty^{\oplus r}[-j].
\tag{16.20}
$$

If instead $C_\infty^\bullet\simeq L[-j]$ for one nonzero finite module $L$, then

$$
\operatorname{pd}_{S_\infty}L\leq h-a,
\qquad
\operatorname{depth}_{S_\infty}L\geq q+1-(h-a).
\tag{16.21}
$$

**Proof.** Theorem 8.1 patches the strict complexes and proves derived augmentation. Compatible pairing matrices patch degree by degree, and perfectness is detected after reduction to the residue field. Proposition 8.3 gives (16.20). A single surviving homology module is resolved by a shift of the patched complex, giving the projective-dimension bound; Auslander--Buchsbaum gives the depth bound. $\square$

### 16.3 The exact interface for the next argument

The construction exports the following facts and no hidden strengthening of them:

$$
\begin{array}{c}
S_\infty\hookrightarrow R_\infty\twoheadrightarrow A_\infty
\hookrightarrow\operatorname{End}_{S_\infty}(M_\infty),\\
M_\infty\simeq S_\infty^r,\\
R_\infty/\mathfrak a_\infty R_\infty\simeq R,
\qquad
M_\infty/\mathfrak a_\infty M_\infty\simeq M,\\
\dim A_\infty=\dim\operatorname{Supp}_{R_\infty}M_\infty=q+1,\\
\operatorname{depth}_{R_\infty}M_\infty=q+1,\\
\dim R_\infty\geq d_{\mathrm{loc}}+q+G-c_\infty
\geq d_{\mathrm{loc}}+q+G-b.
\end{array}
\tag{16.22}
$$

Under the sharp numerical and dimension hypotheses, $R_\infty$ has dimension $q+1$ and the module is maximal Cohen--Macaulay. Under component coverage it is nearly faithful. Faithfulness then follows from reducedness, from the associated-prime criterion, from annihilator saturation, or from positive-rank $R_\infty$-freeness. Each strengthening remains conditional on its stated hypothesis.

The next commutative-algebra step may use (16.22), a complete-intersection conclusion when proved, the exact annihilator or near-faithfulness statement actually available, and, when augmentation saturation has been established, the augmented square (7.12). It may not replace a nearly faithful action by a faithful one, a union of components by the entire spectrum, a maximal Cohen--Macaulay module by a free module over a singular ring, or an underived quotient by a Tor-independent specialization.

In particular, patching has not identified $R$ with $\mathbb T$. It has constructed the large regular auxiliary environment in which the remaining comparison becomes a precise question about annihilators, components, and descent.

### 16.4 Conclusion

Patching turns a family with no arithmetic transition maps into one coherent complete object by working at finite precision. The finite residue field, uniform presentations, uniform module size, and marked structural maps make the space of each finite shadow finite. A diagonal path then supplies genuine reductions among selected models without inventing maps between unrelated auxiliary prime sets. Surjectivity and the asserted ring and module augmentation identities survive because the relevant finite kernel systems are Mittag--Leffler.

At the module level, finite-level diamond freeness is transported by compatible bases, not guessed from ranks. The limiting equations imposing finite character order disappear, leaving

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]]
$$

and a free module over it. Its regular sequence gives depth $q+1$. The faithfully acting image is finite over $S_\infty$, which carries that depth to the patched deformation action and fixes the support dimension. The relation presentation supplies the complementary lower bound on the ring dimension; the Taylor--Wiles variable count makes the $q$ auxiliary directions cancel the original dual-Selmer defect.

The resulting strength is exact and deliberately bounded. Dimension equality yields maximal depth, not component coverage. Full support yields a nilpotent annihilator, not faithfulness over a nonreduced ring. Maximal Cohen--Macaulayness yields freeness only with regularity or finite projective dimension. Augmentation recovers the original objects, but Tor vanishing for the ring requires a regular-sequence theorem. Pairings persist when their finite shadows are genuinely compatible, but a dual pair is not a self-dual module without an identification.

The patched pair is therefore powerful because every source of information has a separate job: $S_\infty$ supplies regularity, $P_\infty$ supplies equations, $R_\infty$ retains deformation structure, $A_\infty$ records the actual action, and $M_\infty$ connects them through depth and support. Once these roles are kept distinct, the limiting construction ends with a dependable algebraic interface rather than a collection of numerical coincidences.

## 17. Paired source patching and support transfer

The preceding theorem package patches a quotient deformation ring and then asks which components its module sees. For a paired desired/avoidance argument, that order can lose the decisive geometry. The avoidance local source may be irreducible even when an arbitrary global quotient is not, while the desired source may come with a precise specialization map from its horizontal components to its special-fiber components. The right ambient rings are therefore the expanded local presentation sources themselves.

Throughout this chapter, $\mathcal O$ is a complete discrete valuation ring with uniformizer $\varpi$, and all complete local $\mathcal O$-algebras are Noetherian with finite residue field. Rings arising below are quotients of power-series rings over $\mathcal O$, so the catenary and finiteness properties used in component arguments are available.

### 17.1 The unique-horizontal support lemma

Let $B$ be an $\mathcal O$-flat, reduced, equidimensional Cohen--Macaulay complete local ring of dimension $D$. Flatness makes $\varpi$ a nonzerodivisor, and hence $B/\varpi$ is Cohen--Macaulay and equidimensional of dimension $D-1$. Suppose specialization gives a bijection

$$
\operatorname{Min}(B)
\xrightarrow{\sim}
\operatorname{Min}(B/\varpi).
\tag{17.1}
$$

Concretely, (17.1) says that each special-fiber component lies on one and only one horizontal component, and that every horizontal component reaches the special fiber in a minimal component. This is stronger than flatness. A flat domain can have a reducible special fiber.

**Lemma 17.1 (unique-horizontal support).** Let $L$ be a nonzero finite maximal Cohen--Macaulay $B$-module. If

$$
\operatorname{Supp}_{B/\varpi}(L/\varpi L)
=\operatorname{Spec}(B/\varpi),
\tag{17.2}
$$

then

$$
\operatorname{Supp}_B L=\operatorname{Spec}B.
\tag{17.3}
$$

Since $B$ is reduced, $L$ is faithful.

**Proof.** Maximal Cohen--Macaulayness and equidimensionality imply that every minimal prime of $\operatorname{Supp}_B L$ has dimension $D$. By the catenary argument of Section 11.2, such a prime is a minimal prime of $B$. Thus the support of $L$ is a union of horizontal irreducible components.

Let $\mathfrak q\in\operatorname{Min}(B/\varpi)$. Hypothesis (17.2) places $\mathfrak q$ in the support of $L/\varpi L$, and hence in the support of $L$. Choose a minimal prime $\mathfrak p'$ of $\operatorname{Supp}_B L$ contained in $\mathfrak q$. The preceding paragraph gives $\mathfrak p'\in\operatorname{Min}(B)$. A minimal prime of $B/\varpi$ lying over $\mathfrak p'$ is contained in $\mathfrak q$; minimality forces it to equal $\mathfrak q$. By the injectivity in (17.1), $\mathfrak p'$ is the unique horizontal minimal prime specializing to $\mathfrak q$.

Every $\mathfrak p\in\operatorname{Min}(B)$ specializes, by the surjectivity in (17.1), to some $\mathfrak q$. Applying the preceding argument to that $\mathfrak q$ shows that its unique horizontal antecedent $\mathfrak p$ lies in the support. Hence all minimal primes of $B$ lie in $\operatorname{Supp}_B L$, which proves (17.3). The annihilator of a full-support module is contained in the nilradical. Reducedness makes that nilradical zero. $\square$

The maximal Cohen--Macaulay hypothesis rules out support confined to a positive-codimension subset of a horizontal component. The uniqueness in (17.1) then rules out assigning a special component seen by the module to the wrong horizontal component. Both ingredients are necessary for this proof.

### 17.2 Coefficient-power nilpotents

The desired integral presentation is often first available as a raw source $B^{\mathrm{raw}}$. Let

$$
\mathcal N=\sqrt{0}_{B^{\mathrm{raw}}},
\qquad
B=B^{\mathrm{raw}}/\mathcal N.
\tag{17.4}
$$

Suppose that the raw generic fiber is reduced, or equivalently for (17.4) that

$$
\mathcal N[1/\varpi]=0.
\tag{17.5}
$$

The following elementary observation is what permits the raw source to act on an integral patched module without retaining spurious infinitesimal directions.

**Lemma 17.2 (coefficient-power nilradical).** Under (17.5), there is an integer $a\geq0$ such that

$$
\varpi^a\mathcal N=0.
\tag{17.6}
$$

If $L$ is $\mathcal O$-torsion-free, then $\mathcal N L=0$. Thus every $B^{\mathrm{raw}}$-action on $L$ factors through $B$.

**Proof.** The ideal $\mathcal N$ is finite over the Noetherian ring $B^{\mathrm{raw}}$. Choose generators $n_1,\ldots,n_s$. Equation (17.5) says that for each $i$ some power of $\varpi$ kills $n_i$. Taking the maximum of these exponents gives (17.6).

For $n\in\mathcal N$ and $x\in L$, equation (17.6) gives $\varpi^a(nx)=0$. Since $L$ is $\mathcal O$-torsion-free, $nx=0$. Hence $\mathcal N$ annihilates $L$, and the action factors through (17.4). $\square$

The hypothesis (17.5) cannot simply be omitted. The killed thickening in the second example of Section 11.5 survives after inverting $\varpi$ and is therefore not coefficient-power torsion. Horizontal reducedness must include the assertion that the raw and reduced sources have the same generic fiber, not just the formal operation of quotienting by a nilradical.

### 17.3 The paired source-patching theorem

Let

$$
S=\mathcal O[[z_1,\ldots,z_h,w_1,\ldots,w_c]]
\tag{17.7}
$$

be an expanded regular frame-and-diamond ring, where in the rank-two full partial-frame convention $c=4|T|-1$. Put $D=\dim S$. Consider an avoidance source $P^{\mathrm{av}}$, a raw desired source $P^{\mathrm{des,raw}}$, and its horizontal reduction

$$
P^{\mathrm{des}}
=P^{\mathrm{des,raw}}/\mathcal N.
\tag{17.8}
$$

The phrase “same residual source and module up to nilpotents” will mean the following precise datum. There is a complete local $k$-algebra $C$ and surjections

$$
P^{\mathrm{av}}/\varpi
\twoheadrightarrow C,
\qquad
P^{\mathrm{des}}/\varpi
\twoheadrightarrow C
\tag{17.9}
$$

with nilpotent kernels. After base change along (17.9), the residual patched modules are identified as $C$-modules, compatibly with every named residual action:

$$
(M^{\mathrm{av}}/\varpi)\otimes_{P^{\mathrm{av}}/\varpi}C
\xrightarrow{\sim}
(M^{\mathrm{des}}/\varpi)\otimes_{P^{\mathrm{des}}/\varpi}C.
\tag{17.10}
$$

Nilpotent kernels in (17.9) induce homeomorphisms on spectra. Passing to $C$ therefore forgets no component, while (17.10) remembers the residual module action rather than only a numerical rank.

**Theorem 17.3 (paired source patching and support transfer).** Assume:

1. $P^{\mathrm{av}}$ is an $\mathcal O$-flat Cohen--Macaulay domain of dimension $D$;
2. $P^{\mathrm{des}}$ is $\mathcal O$-flat, reduced, equidimensional, and Cohen--Macaulay of dimension $D$, and specialization gives a bijection

   $$
   \operatorname{Min}(P^{\mathrm{des}})
   \xrightarrow{\sim}
   \operatorname{Min}(P^{\mathrm{des}}/\varpi);
   \tag{17.11}
   $$

3. the raw desired generic fiber is reduced, so $\mathcal N[1/\varpi]=0$;
4. the common residual source and module datum (17.9)--(17.10) is given;
5. $M^{\mathrm{av}}$ and $M^{\mathrm{des}}$ are finite free of positive rank over $S$;
6. the commuting scalar and source actions give local maps

   $$
   \begin{aligned}
   &S\hookrightarrow A^{\mathrm{av}}
   \subseteq\operatorname{End}_S(M^{\mathrm{av}}),
   &&P^{\mathrm{av}}\twoheadrightarrow A^{\mathrm{av}},\\
   &S\hookrightarrow A^{\mathrm{des}}
   \subseteq\operatorname{End}_S(M^{\mathrm{des}}),
   &&P^{\mathrm{des,raw}}\twoheadrightarrow A^{\mathrm{des}},
   \end{aligned}
   \tag{17.12}
   $$

   where each $A^\bullet$ is the actual source action image. On the special fiber, the desired action factors through $P^{\mathrm{des}}/\varpi$ as part of the residual datum (17.10); integral factorization through $P^{\mathrm{des}}$ is a conclusion.

Then the avoidance source acts faithfully:

$$
A^{\mathrm{av}}=P^{\mathrm{av}},
\qquad
\operatorname{Supp}_{P^{\mathrm{av}}}M^{\mathrm{av}}
=\operatorname{Spec}P^{\mathrm{av}}.
\tag{17.13}
$$

The common residual module has full support over $C$, and the desired residual module has full support over $P^{\mathrm{des}}/\varpi$. Every horizontal desired component consequently occurs in the support, and

$$
A^{\mathrm{des}}=P^{\mathrm{des}},
\qquad
\operatorname{Supp}_{P^{\mathrm{des}}}M^{\mathrm{des}}
=\operatorname{Spec}P^{\mathrm{des}}.
\tag{17.14}
$$

Moreover there is an exponent $a$ for which $\varpi^a\mathcal N=0$, and

$$
\operatorname{Ann}_{P^{\mathrm{des,raw}}}(M^{\mathrm{des}})
=\mathcal N.
\tag{17.15}
$$

If the source actions factor through intermediate quotient deformation rings

$$
\begin{aligned}
P^{\mathrm{av}}&\twoheadrightarrow R^{\mathrm{av}}
\twoheadrightarrow A^{\mathrm{av}},\\
P^{\mathrm{des,raw}}&\twoheadrightarrow R^{\mathrm{des,raw}}
\twoheadrightarrow A^{\mathrm{des}},
\end{aligned}
\tag{17.16}
$$

then $R^{\mathrm{av}}=P^{\mathrm{av}}$, while $(R^{\mathrm{des,raw}})^{\mathrm{red}}=P^{\mathrm{des}}$.

More precisely, if

$$
I=\ker\bigl(P^{\mathrm{des,raw}}
\twoheadrightarrow R^{\mathrm{des,raw}}\bigr),
$$

then

$$
I\subseteq\mathcal N,
\qquad
\operatorname{Ann}_{R^{\mathrm{des,raw}}}(M^{\mathrm{des}})
=\mathcal N/I
=\sqrt{0}_{R^{\mathrm{des,raw}}}.
\tag{17.16a}
$$

**Proof.** We first use the avoidance domain before taking any global relation quotient. Since $M^{\mathrm{av}}$ is finite free over the regular local ring $S$,

$$
\operatorname{depth}_S M^{\mathrm{av}}=D.
\tag{17.17}
$$

The action image $A^{\mathrm{av}}$ is finite over $S$, because it is an $S$-submodule of the finite free module $\operatorname{End}_S(M^{\mathrm{av}})$. The finite local maps in (17.12) compare the depth of the same module, giving

$$
\operatorname{depth}_{P^{\mathrm{av}}}M^{\mathrm{av}}
=\operatorname{depth}_{A^{\mathrm{av}}}M^{\mathrm{av}}
=\operatorname{depth}_S M^{\mathrm{av}}
=D.
\tag{17.18}
$$

If the annihilator in the domain $P^{\mathrm{av}}$ were nonzero, its quotient would have dimension at most $D-1$. But depth never exceeds the dimension of the support, so (17.18) would give

$$
D
\leq\dim\operatorname{Supp}_{P^{\mathrm{av}}}M^{\mathrm{av}}
\leq D-1,
$$

a contradiction. The source action is faithful. Since $P^{\mathrm{av}}\twoheadrightarrow A^{\mathrm{av}}$ is its action map, it is an isomorphism, proving (17.13).

Full avoidance support descends to the special fiber. Indeed, for any prime $\mathfrak q$ containing $\varpi$, the localization $M^{\mathrm{av}}_{\mathfrak q}$ is nonzero. Nakayama's lemma makes

$$
M^{\mathrm{av}}_{\mathfrak q}/\varpi M^{\mathrm{av}}_{\mathfrak q}
$$

nonzero. Hence

$$
\operatorname{Supp}_{P^{\mathrm{av}}/\varpi}
(M^{\mathrm{av}}/\varpi)
=\operatorname{Spec}(P^{\mathrm{av}}/\varpi).
\tag{17.19}
$$

Quotienting a nonzero finite localized module by a nilpotent ideal cannot kill it, again by Nakayama. The first map in (17.9) therefore carries (17.19) to full support over $C$. The isomorphism (17.10) transfers that full support to the desired base change. Since the second map in (17.9) is a homeomorphism on spectra, nonvanishing of every localized base change implies

$$
\operatorname{Supp}_{P^{\mathrm{des}}/\varpi}
(M^{\mathrm{des}}/\varpi)
=\operatorname{Spec}(P^{\mathrm{des}}/\varpi).
\tag{17.20}
$$

We next justify the desired action appearing here. Lemma 17.2 applies to $P^{\mathrm{des,raw}}$ by hypothesis 3. It gives $\varpi^a\mathcal N=0$. The desired module is $S$-free, hence $\mathcal O$-torsion-free, so $\mathcal N$ acts trivially. Thus the raw action factors through $P^{\mathrm{des}}$.

The same finite-map depth comparison used in (17.18) gives

$$
\operatorname{depth}_{P^{\mathrm{des}}}M^{\mathrm{des}}
=D
=\dim P^{\mathrm{des}}.
\tag{17.21}
$$

Thus $M^{\mathrm{des}}$ is maximal Cohen--Macaulay over the desired horizontal source. Apply Lemma 17.1 to (17.20) and the component bijection (17.11). It follows that every desired horizontal component lies in the support. Reducedness of $P^{\mathrm{des}}$ then makes the action faithful, proving (17.14). The raw annihilator contains $\mathcal N$ because that ideal acts trivially, and its image in the faithful quotient $P^{\mathrm{des}}$ is zero only when it already lies in $\mathcal N$. This proves (17.15).

Finally, in the avoidance factorization (17.16), injectivity of the composite $P^{\mathrm{av}}\to A^{\mathrm{av}}$ forces both quotient maps to be isomorphisms. On the desired side, the composite action of $P^{\mathrm{des,raw}}$ has kernel $\mathcal N$ by (17.15). It factors through $R^{\mathrm{des,raw}}$, so $I\subseteq\mathcal N$. Therefore

$$
R^{\mathrm{des,raw}}
=P^{\mathrm{des,raw}}/I
$$

has nilradical $\mathcal N/I$: if a class is nilpotent, a power of any lift lies in $I\subseteq\mathcal N$, and hence the lift lies in $\mathcal N$. The kernel of the induced action of $R^{\mathrm{des,raw}}$ is also $\mathcal N/I$, because its inverse image in the raw source is $\mathcal N$. This proves (17.16a), and quotienting by that ideal gives $(R^{\mathrm{des,raw}})^{\mathrm{red}}=P^{\mathrm{des}}$. $\square$

The proof assigns one job to each hypothesis. The domain condition turns depth into avoidance faithfulness. The common residual diagram transfers topological support. The component-bijective specialization lifts that support to every desired horizontal component. Reducedness upgrades full desired support to faithfulness. Finally, coefficient-power torsion, not a generic assertion about nilpotents, makes the raw nilradical act trivially on the integral module.

### 17.4 Module augmentation and finite-level factorization

Support transfer has a useful finite-level consequence which does not require exact augmentation of the acting image. Assume the desired factorization in (17.16), and put

$$
B=R^{\mathrm{des,raw}},
\qquad
L=M^{\mathrm{des}}.
$$

Thus $B$ is the intermediate patched deformation ring actually recovered at finite level, not the presentation source. Let $\mathfrak a\subseteq B$ be the ideal induced by the marked diamond and frame specialization. Equation (17.16a) gives

$$
\operatorname{Supp}_B L=\operatorname{Spec}B
\tag{17.22}
$$

as a topological equality, because $\operatorname{Ann}_B(L)=\sqrt{0}_B=\mathcal N/I$.

**Corollary 17.4 (module-level augmentation and pointwise factorization).** In addition to Theorem 17.3 and the desired intermediate factorization (17.16), suppose finite-level recovery gives a ring isomorphism and a compatible module isomorphism

$$
B/\mathfrak aB\xrightarrow{\sim}R,
\qquad
L/\mathfrak aL\xrightarrow{\sim}M.
\tag{17.23}
$$

Let

$$
R\longrightarrow\mathbb T
\subseteq\operatorname{End}_{\mathcal O}(M)
\tag{17.24}
$$

be the finite-level deformation action, with $\mathbb T$ defined as its acting image. Then the kernel $J$ of (17.24) is nilpotent. Every homomorphism from $R$ to a characteristic-zero field factors uniquely through $\mathbb T$.

If $\mathbb T$ is finite over $\mathcal O$, then $R$ is finite over $\mathcal O$ as well.

**Proof.** Let $\mathfrak p$ be any prime of $B$ containing $\mathfrak a$. By (17.22), $L_{\mathfrak p}\ne0$. Since $\mathfrak aB_{\mathfrak p}$ lies in the maximal ideal of the local ring $B_{\mathfrak p}$, Nakayama gives

$$
L_{\mathfrak p}/\mathfrak aL_{\mathfrak p}\ne0.
$$

Consequently

$$
\operatorname{Supp}_{B/\mathfrak aB}(L/\mathfrak aL)
=\operatorname{Spec}(B/\mathfrak aB).
\tag{17.25}
$$

The recovery isomorphisms (17.23) turn (17.25) into $\operatorname{Supp}_R M=\operatorname{Spec}R$. Hence

$$
J=\operatorname{Ann}_R(M)\subseteq\sqrt{0}_R.
\tag{17.26}
$$

The Noetherian ideal $J$ is finitely generated by nilpotent elements, so some power of $J$ is zero.

A homomorphism from $R$ to a field kills every nilpotent element and hence kills $J$. It therefore factors uniquely through $R/J=\mathbb T$. This is the characteristic-zero factorization assertion.

If $J^n=0$ and $\mathbb T=R/J$ is finite over $\mathcal O$, each quotient $J^i/J^{i+1}$ is a finite module over $R/J$ and hence over $\mathcal O$. The finite filtration

$$
0\subseteq J^{n-1}\subseteq\cdots\subseteq J\subseteq R
$$

then proves that $R$ is finite over $\mathcal O$. $\square$

This nilpotent kernel is the precise finite-level conclusion needed for a characteristic-zero application. It says that every desired deformation point occurs in the finite action and that finiteness passes from the action to the deformation ring. An isomorphism $R\simeq\mathbb T$ would be stronger, but neither pointwise factorization nor finiteness requires it.

Notice what the proof used from augmentation: recovery of the intermediate represented ring $B=R^{\mathrm{des,raw}}$ and the module coinvariants in (17.23). It neither augments the presentation source as though it were the deformation ring nor identifies the quotient of the patched acting image. Thus Corollary 17.4 remains valid when acting-image augmentation has an unsaturated nilpotent kernel.

### 17.5 Exact acting-image augmentation under saturation

There is a clean criterion for retaining the stronger conclusion when it is actually available. Let $A\subseteq\operatorname{End}_S(L)$ be the patched acting image. The marked structural maps identify the image in $A$ of the specialization ideal $\mathfrak a\subseteq S$ with the image of the ideal denoted $\mathfrak a\subseteq B$ in (17.23). The module recovery in (17.23) always gives a surjection

$$
A/\mathfrak aA\twoheadrightarrow\mathbb T.
\tag{17.27}
$$

**Corollary 17.5 (exact acting-image augmentation under saturation).** In the setting of Corollary 17.4, suppose in addition that

$$
A\cap
\mathfrak a\operatorname{End}_S(L)
=\mathfrak aA.
\tag{17.28}
$$

Then (17.27) is an isomorphism:

$$
A/\mathfrak aA\xrightarrow{\sim}\mathbb T.
\tag{17.29}
$$

**Proof.** An element of $A$ maps to zero on $L/\mathfrak aL$ exactly when its image in $\operatorname{End}_S(L)$ lies in $\mathfrak a\operatorname{End}_S(L)$. By (17.28), such an element lies in $\mathfrak aA$. This proves injectivity of (17.27); surjectivity holds because $\mathbb T$ is the action image on the recovered module. $\square$

Condition (17.28) is an additional integral saturation theorem. It is not a consequence of source faithfulness, $S$-freeness, common residual reduction, perfect pairings, or exact module coinvariants. The exact result (17.29) is therefore a corollary of the paired source theorem plus saturation, not part of the basic paired source-patching conclusion.

### 17.6 Why patching the source changes the argument

The first counterexample of Section 11.5 already shows what goes wrong after quotienting too early. Its module is free over the regular auxiliary ring and maximal Cohen--Macaulay over an equal-dimensional reduced quotient, yet it sees only one of two components. No repetition of the depth calculation can recover the missed component. This is precisely the quotient-first danger: a global relation quotient may acquire several components before there is any irreducible ring on which a nonzero annihilator would force a dimension drop.

Theorem 17.3 avoids that example rather than contradicting it. On the avoidance side, the action is tested on the source domain. Equal-dimensional maximal depth makes a nonzero annihilator impossible there. On the desired side, support is not guessed from maximal depth; it is transferred through the common residual module and then lifted using the unique-horizontal bijection. Thus each desired component is accounted for by a named special-fiber component.

The second example of Section 11.5 explains the remaining nilpotent caution. Full topological support can coexist with a killed thickening. In the paired source theorem, the desired horizontal source is reduced, so full support gives faithfulness there. The raw thickening is handled separately: its nilradical is killed by a power of $\varpi$ and hence acts trivially on the $\mathcal O$-torsion-free patched module. The example's nilpotent survives in the generic fiber, so it fails exactly this coefficient-power hypothesis.

Source patching therefore does not assert that maximal Cohen--Macaulay modules always meet every component. It supplies two extra geometric mechanisms absent from the counterexamples: irreducibility on the avoidance source and component-bijective specialization on the desired source. Those mechanisms, combined with the synchronized residual module, are what turn depth into full support.
