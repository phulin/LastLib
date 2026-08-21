# The Abstract $R=T$ Argument

## Contents

1. [The final comparison problem](#1-the-final-comparison-problem)
   - [What patching has and has not proved](#11-what-patching-has-and-has-not-proved)
   - [The canonical map and the chosen patched world](#12-the-canonical-map-and-the-chosen-patched-world)
   - [A noncircular proof architecture](#13-a-noncircular-proof-architecture)
   - [Four possible endpoints](#14-four-possible-endpoints)
2. [The abstract input ledger](#2-the-abstract-input-ledger)
   - [Coefficients and residue data](#21-coefficients-and-residue-data)
   - [The finite-level comparison](#22-the-finite-level-comparison)
   - [The patched presentation](#23-the-patched-presentation)
   - [The auxiliary regular ring and the patched module](#24-the-auxiliary-regular-ring-and-the-patched-module)
   - [The acting quotient](#25-the-acting-quotient)
   - [Dimension and relation data](#26-dimension-and-relation-data)
   - [Augmentation and exact control](#27-augmentation-and-exact-control)
   - [Pairings, determinants, and local conditions](#28-pairings-determinants-and-local-conditions)
   - [The ledger in one diagram](#29-the-ledger-in-one-diagram)
3. [The first consequences of the patched pair](#3-the-first-consequences-of-the-patched-pair)
   - [The auxiliary action is faithful](#31-the-auxiliary-action-is-faithful)
   - [Finiteness of the acting algebra](#32-finiteness-of-the-acting-algebra)
   - [Depth over three rings](#33-depth-over-three-rings)
   - [The exact support dimension](#34-the-exact-support-dimension)
   - [Generic ranks and generic multiplicity](#35-generic-ranks-and-generic-multiplicity)
   - [What these conclusions do not imply](#36-what-these-conclusions-do-not-imply)
4. [Sharp dimension and Cohen--Macaulay structure](#4-sharp-dimension-and-cohen--macaulay-structure)
   - [The relation lower bound](#41-the-relation-lower-bound)
   - [Why the action quotient is not a dimension ceiling](#42-why-the-action-quotient-is-not-a-dimension-ceiling)
   - [Three valid dimension ceilings](#43-three-valid-dimension-ceilings)
   - [From equality to a regular sequence](#44-from-equality-to-a-regular-sequence)
   - [Complete-intersection rings and complete-intersection maps](#45-complete-intersection-rings-and-complete-intersection-maps)
   - [Auslander--Buchsbaum and miracle flatness](#46-auslander--buchsbaum-and-miracle-flatness)
   - [Where intersection theory enters](#47-where-intersection-theory-enters)
5. [Support, components, and annihilators](#5-support-components-and-annihilators)
   - [Height zero is only a beginning](#51-height-zero-is-only-a-beginning)
   - [Support as a union of components](#52-support-as-a-union-of-components)
   - [The component-coverage hypothesis](#53-the-component-coverage-hypothesis)
   - [Faithful, nearly faithful, and faithful modulo nilpotents](#54-faithful-nearly-faithful-and-faithful-modulo-nilpotents)
   - [Reducedness and direct annihilator arguments](#55-reducedness-and-direct-annihilator-arguments)
   - [Componentwise quotients](#56-componentwise-quotients)
6. [Comparing the patched deformation and action algebras](#6-comparing-the-patched-deformation-and-action-algebras)
   - [Surjectivity comes first](#61-surjectivity-comes-first)
   - [The faithful acting quotient](#62-the-faithful-acting-quotient)
   - [Criteria for injectivity](#63-criteria-for-injectivity)
   - [Generic-rank criteria](#64-generic-rank-criteria)
   - [Fitting criteria](#65-fitting-criteria)
   - [Rank one over the auxiliary ring](#66-rank-one-over-the-auxiliary-ring)
7. [Descent through augmentation](#7-descent-through-augmentation)
   - [Underived recovery](#71-underived-recovery)
   - [Regular augmentation sequences](#72-regular-augmentation-sequences)
   - [Tor vanishing and exact specialization](#73-tor-vanishing-and-exact-specialization)
   - [Descent of equality](#74-descent-of-equality)
   - [Descent of reduced equality](#75-descent-of-reduced-equality)
   - [Descent of complete intersections](#76-descent-of-complete-intersections)
   - [Descent of module freeness](#77-descent-of-module-freeness)
8. [Self-duality, Gorenstein rings, and multiplicity one](#8-self-duality-gorenstein-rings-and-multiplicity-one)
   - [What a perfect pairing gives](#81-what-a-perfect-pairing-gives)
   - [What it does not give](#82-what-it-does-not-give)
   - [Multiplicity one as cyclicity](#83-multiplicity-one-as-cyclicity)
   - [From rank-one freeness to Gorenstein duality](#84-from-rank-one-freeness-to-gorenstein-duality)
   - [When module freeness follows](#85-when-module-freeness-follows)
   - [Ring equality without module freeness](#86-ring-equality-without-module-freeness)
9. [Cotangent spaces, congruence ideals, and the numerical route](#9-cotangent-spaces-congruence-ideals-and-the-numerical-route)
   - [The augmented finite-level invariants](#91-the-augmented-finite-level-invariants)
   - [The direction of the numerical inequality](#92-the-direction-of-the-numerical-inequality)
   - [The module congruence lattice](#93-the-module-congruence-lattice)
   - [A common-determinant comparison](#94-a-common-determinant-comparison)
   - [The module-derived numerical equality](#95-the-module-derived-numerical-equality)
   - [The Wiles--Lenstra conclusion](#96-the-wiles--lenstra-conclusion)
   - [The numerical and support routes compared](#97-the-numerical-and-support-routes-compared)
10. [Framed and unframed comparisons](#10-framed-and-unframed-comparisons)
    - [The formally smooth frame extension](#101-the-formally-smooth-frame-extension)
    - [Removing frame variables](#102-removing-frame-variables)
    - [Faithfulness and components under power series](#103-faithfulness-and-components-under-power-series)
    - [Padding variables are not frames](#104-padding-variables-are-not-frames)
11. [Determinants and local-condition compatibility](#11-determinants-and-local-condition-compatibility)
    - [Fixed determinant throughout the comparison](#111-fixed-determinant-throughout-the-comparison)
    - [Old local components](#112-old-local-components)
    - [Auxiliary local branches](#113-auxiliary-local-branches)
    - [Why the quotient still represents the intended problem](#114-why-the-quotient-still-represents-the-intended-problem)
12. [Minimal and nonminimal abstract instances](#12-minimal-and-nonminimal-abstract-instances)
    - [The minimal pattern](#121-the-minimal-pattern)
    - [The nonminimal pattern](#122-the-nonminimal-pattern)
    - [Changing the local base](#123-changing-the-local-base)
    - [Component hopping as a named theorem](#124-component-hopping-as-a-named-theorem)
13. [Canonicity and independence of choices](#13-canonicity-and-independence-of-choices)
    - [What can depend on choices](#131-what-can-depend-on-choices)
    - [What is canonical](#132-what-is-canonical)
    - [Why one successful patch proves a choice-independent result](#133-why-one-successful-patch-proves-a-choice-independent-result)
    - [Reduced and componentwise independence](#134-reduced-and-componentwise-independence)
14. [Failure modes and diagnostic counterexamples](#14-failure-modes-and-diagnostic-counterexamples)
    - [A module on one component](#141-a-module-on-one-component)
    - [A nilpotent thickening invisible to support](#142-a-nilpotent-thickening-invisible-to-support)
    - [Dimension equality without faithfulness](#143-dimension-equality-without-faithfulness)
    - [A zerodivisor augmentation variable](#144-a-zerodivisor-augmentation-variable)
    - [An equal-dimensional proper quotient](#145-an-equal-dimensional-proper-quotient)
    - [A maximal Cohen--Macaulay nonfree module](#146-a-maximal-cohen--macaulay-nonfree-module)
    - [A torsion-free target that does not kill nilpotents](#147-a-torsion-free-target-that-does-not-kill-nilpotents)
    - [A false numerical comparison](#148-a-false-numerical-comparison)
15. [A clean theorem instance](#15-a-clean-theorem-instance)
    - [The one-branch complete-intersection model](#151-the-one-branch-complete-intersection-model)
    - [Verification of every hypothesis](#152-verification-of-every-hypothesis)
    - [Descent and the finite-level conclusion](#153-descent-and-the-finite-level-conclusion)
16. [The master theorem and its variants](#16-the-master-theorem-and-its-variants)
    - [The sharp patched comparison theorem](#161-the-sharp-patched-comparison-theorem)
    - [Full $R=T$](#162-full-rt)
    - [Equality of reduced quotients](#163-equality-of-reduced-quotients)
    - [Componentwise $R=T$](#164-componentwise-rt)
    - [Complete-intersection and freeness conclusions](#165-complete-intersection-and-freeness-conclusions)
    - [The numerical-criterion variant](#166-the-numerical-criterion-variant)
    - [A minimal hypothesis checklist](#167-a-minimal-hypothesis-checklist)
17. [The final audit](#17-the-final-audit)
    - [Dimensions and depth](#171-dimensions-and-depth)
    - [Support and nilpotents](#172-support-and-nilpotents)
    - [Regular sequences and Tor](#173-regular-sequences-and-tor)
    - [Numerical invariants](#174-numerical-invariants)
    - [Finite-level recovery](#175-finite-level-recovery)
18. [Conclusion](#18-conclusion)

## 1. The final comparison problem

### 1.1 What patching has and has not proved

The Taylor--Wiles construction begins with a canonical surjection from a global deformation ring to an algebra generated by arithmetic correspondences. At finite level it enlarges the deformation problem at carefully chosen auxiliary places. At infinite level it replaces the finite diamond groups by a regular power-series algebra and produces a module of maximal possible auxiliary depth. The purpose of the present book is to make the last implication:

$$
\text{large patched module}
\quad\Longrightarrow\quad
\text{no kernel in the canonical map }R\longrightarrow\mathbb T.
\tag{1.1}
$$

The implication is not automatic. Patching supplies a module $M_\infty$ that is free over an auxiliary regular ring $S_\infty$. It also supplies a quotient $A_\infty$ of the patched deformation ring $R_\infty$ that acts faithfully on $M_\infty$. What it does not supply merely by construction is

$$
R_\infty=A_\infty.
\tag{1.2}
$$

The kernel in (1.2) is exactly the annihilator of $M_\infty$ as an $R_\infty$-module. It can arise in two fundamentally different ways. The module may miss an entire irreducible component, or it may have full topological support while a nilpotent ideal acts by zero. Dimension detects neither defect by itself.

This is why the final argument is a theorem about support and annihilators, not a slogan about matching dimensions. The regular auxiliary ring supplies depth. The relation presentation supplies a lower bound for dimension. A separate ceiling makes that lower bound sharp. Sharpness turns the relation ideal into a regular sequence. Only then can component information be used without confusing a maximal-dimensional closed subset with the whole spectrum.

The resulting logic is robust enough to cover several outcomes. With coverage of every component one obtains near faithfulness. With reducedness, or with a direct annihilator argument, one obtains faithfulness. Without full coverage one obtains a theorem only on the components actually seen by the module. Without reducedness one obtains equality only after killing nilpotents.

The algebraic foundations used below have already been established in the preceding sequence of volumes. Complete local presentations, depth, regular sequences, and Fitting ideals provide the ordinary commutative-algebra background. Book 71 proves the Wiles--Lenstra numerical isomorphism criterion in the precise source-unrestricted form recalled in Chapter 9. Book 145 constructs the strong patched pair in its Theorem 16.1, proves the corresponding dimension and depth package in Corollary 16.2, and treats balanced and perfect-complex variants in Theorems 16.3 and 16.4. The present book does not repeat those constructions. Its task is to assemble them into the final comparison while proving every new implication from dimension to support, from support to annihilators, and from infinite-level equality to the canonical finite-level map.

### 1.2 The canonical map and the chosen patched world

The finite-level map

$$
\varphi:R\longrightarrow\mathbb T
\tag{1.3}
$$

is canonical relative to the starting deformation problem and the chosen acting algebra. It comes from the family of representations valued in $\mathbb T$. Its construction does not depend on a Taylor--Wiles set, an ordering of diamond generators, a basis of a patched module, or a diagonal subsequence.

The objects above it generally do depend on choices. One patching construction produces a diagram

$$
\begin{array}{ccccc}
S_\infty&\longrightarrow&R_\infty&\longrightarrow&A_\infty\\
&&\downarrow&&\downarrow\\
&&R&\xrightarrow{\varphi}&\mathbb T,
\end{array}
\tag{1.4}
$$

and another construction can produce a different triple. The vertical maps in (1.4) are augmentation quotients. The top row is a chosen thickening of the bottom row, not a second definition of it.

This distinction is advantageous. To prove that the canonical map (1.3) is an isomorphism, it is enough to produce one patched world in which the top comparison is an isomorphism and both vertical identifications are exact. Once $\varphi$ is known to be bijective, its inverse is uniquely determined. No canonicity of the thickening is required.

### 1.3 A noncircular proof architecture

The argument will follow the chain

$$
\begin{array}{c}
M_\infty\text{ finite free over }S_\infty\\
\Downarrow\\
\operatorname{depth}_{R_\infty}M_\infty
=\dim S_\infty,
\quad
\dim\operatorname{Supp}_{R_\infty}M_\infty
=\dim S_\infty\\
\Downarrow\quad\text{with the relation bound and a ceiling}\\
\dim R_\infty=\dim S_\infty,
\quad
R_\infty\text{ Cohen--Macaulay}\\
\Downarrow\quad\text{with component coverage}\\
\operatorname{Ann}_{R_\infty}(M_\infty)
\text{ is nilpotent}\\
\Downarrow\quad\text{with reducedness or direct annihilator control}\\
R_\infty\xrightarrow{\sim}A_\infty\\
\Downarrow\quad\text{by exact augmentation}\\
R\xrightarrow{\sim}\mathbb T.
\end{array}
\tag{1.5}
$$

Every downward arrow in (1.5) needs a named hypothesis. In particular, the first arrow does not assert that a maximal Cohen--Macaulay module over a singular ring is free. The second does not infer an upper dimension bound from the existence of a quotient of the desired dimension. The third does not replace component coverage by equidimensionality. The fourth does not confuse full support with a zero annihilator in a nonreduced ring. The last does not replace exact Hecke augmentation by a mere surjection.

There is a second route, through the numerical criterion for augmented finite flat algebras. A self-dual multiplicity-one module can calculate a congruence ideal. A cotangent calculation can produce the opposing Fitting ideal. When one determinant controls both, the Wiles--Lenstra criterion proves $R=\mathbb T$ and complete-intersection structure. This route will also be kept noncircular: the common determinant will be derived from explicit pairing and presentation data, not postulated as the desired equality of lengths.

### 1.4 Four possible endpoints

The phrase "$R=T$" can hide four different statements. We shall keep them separate.

1. **Full equality.** The canonical surjection $R\twoheadrightarrow\mathbb T$ has zero kernel.
2. **Reduced equality.** The induced map

   $$
   R^{\mathrm{red}}\xrightarrow{\sim}\mathbb T^{\mathrm{red}}
   $$

   is an isomorphism; the original kernel may be nilpotent.
3. **Componentwise equality.** After quotienting $R$ by the components not seen by the module, the resulting map is an isomorphism, or is an isomorphism after reduction.
4. **Structural equality.** In addition to ring equality, the common ring is finite flat, Cohen--Macaulay, or a complete intersection, and the distinguished module is free under separately stated hypotheses.

The fourth endpoint is strictly stronger than the first. Conversely, a complete-intersection conclusion about each ring does not prove that a surjection between them is injective. Structure and comparison must be proved by their own mechanisms.

## 2. The abstract input ledger

### 2.1 Coefficients and residue data

Fix a complete discrete valuation ring

$$
(\mathcal O,(\varpi),k)
\tag{2.1}
$$

with fraction field $E$ and finite residue field $k$ of characteristic $\ell$. Every local algebra in the argument is complete Noetherian, carries a continuous local $\mathcal O$-algebra structure, and has the specified residue field $k$. Every module is finite unless another finiteness condition is displayed.

Fix an integer $q\geq0$ and put

$$
S_\infty=\mathcal O[[z_1,\ldots,z_q]],
\qquad
\mathfrak a_\infty=(z_1,\ldots,z_q),
\qquad
d=q+1.
\tag{2.2}
$$

The ring $S_\infty$ is regular local of dimension $d$, and

$$
S_\infty/\mathfrak a_\infty\simeq\mathcal O.
\tag{2.3}
$$

The variables $z_i$ are the limiting diamond variables. They are not global deformation variables, frame variables, or padding variables. Their number is the cardinality of the auxiliary sets after any declared padding.

When an augmentation to $\mathcal O$ at a distinguished characteristic-zero point is needed, it will be denoted $\lambda$. This point is additional to the structural specialization (2.3). The first forgets all deformation parameters at one integral point; the second forgets only the diamond variables.

### 2.2 The finite-level comparison

Before passing to the original level, record the finite Taylor--Wiles system from which the patched pair arises. After a cofinal reindexing and any declared padding, suppose that

$$
\Delta_n\cong(\mathbf Z/\ell^{N_n}\mathbf Z)^q,
\qquad N_n\longrightarrow\infty.
$$

Its group algebra and augmentation ideal are

$$
\Lambda_n=\mathcal O[\Delta_n],
\qquad
\mathfrak a_n=\ker(\Lambda_n\to\mathcal O),
$$

Choosing generators identifies

$$
\Lambda_n\cong S_\infty/\mathfrak c_n,
\qquad
\mathfrak c_n=\bigl((1+z_i)^{\ell^{N_n}}-1:1\le i\le q\bigr).
$$

The ideals $\mathfrak c_n$ disappear in every fixed adic shadow as $n\to\infty$. There is a chain of maps

$$
\Lambda_n\longrightarrow R_n
\longrightarrow\mathbb T_n
\longrightarrow\operatorname{End}_{\Lambda_n}(M_n).
$$

Here $R_n$ represents the global deformation problem enlarged at the $n$th auxiliary set, with the same determinant and old local conditions as $R$; $\mathbb T_n$ is the named finite-level action algebra; and $M_n$ is the selected finite-level module. The four arrows carry separate content:

- local reciprocity supplies the $\Lambda_n$-action;
- the universal global family supplies $R_n\to\mathbb T_n$;
- a generator theorem makes $R_n\to\mathbb T_n$ surjective when that is asserted;
- defining $\mathbb T_n$ as the image makes its action on $M_n$ faithful.

The strong module input at finite level is

$$
M_n\cong\Lambda_n^{\oplus r}
$$

with one rank $r$ independent of $n$. It is stronger than equality of cardinalities or ranks after augmentation. The recovery maps are likewise three distinct statements:

$$
R_n/\mathfrak a_nR_n\cong R,
\qquad
M_n/\mathfrak a_nM_n\cong M,
\qquad
\mathbb T_n/\mathfrak a_n\mathbb T_n\cong\mathbb T.
$$

The last identity can require saturation of the operator algebra and is not implied by the middle one. If only a surjection from the leftmost quotient onto the finite object is known, that weaker fact must be carried all the way to descent.

At the presentation level, $R_n$ is obtained from the fixed old-place local base together with auxiliary local branches, framing coordinates, and global coordinates, subject to at most $b$ effective relations after the $q$ dual Selmer directions have been killed. In the marked finite shadows of the fixed presentation source introduced below, this means

$$
R_n\cong
P_\infty/
\bigl(\mathfrak c_nP_\infty+(f_{n,1},\ldots,f_{n,b})\bigr),
$$

after permissible variable--relation padding. The level ideal $\mathfrak c_nP_\infty$ is separate from the $b$ effective global relations and vanishes from the patched presentation at fixed precision. The integers $q$, $b$, and the number of smooth coordinates are uniform in $n$. This uniformity—not an actual transition map $R_{n+1}\to R_n$—is what permits patching. Compatible finite quotients are produced only after choosing generators, bases, and bounded presentations.

Choosing generators $\delta_{n,1},\ldots,\delta_{n,q}$ of $\Delta_n$ gives quotient maps from $S_\infty$ by

$$
z_i\longmapsto[\delta_{n,i}]-1.
$$

These coordinate maps are choices. Their inverse-limit role explains $S_\infty$ and its augmentation, but the finite coinvariant identifications above are intrinsic to the chosen auxiliary deformation problem.

The objects to be compared at the original level are

$$
R\xrightarrow{\varphi}\mathbb T
\hookrightarrow\operatorname{End}_{\mathcal O}(M).
\tag{2.4}
$$

The exact finite-level hypotheses are as follows.

- $R$ is the universal ring for one fixed global deformation problem. The determinant, local conditions, and framed or unframed convention are part of its definition.
- $M$ is the selected integral module.
- $\mathbb T$ is the image of the chosen commuting operator algebra on $M$. Consequently its action is faithful.
- A family valued in $\mathbb T$ satisfies the defining determinant and every defining local condition, giving the map $\varphi$.
- The chosen operator generators lie in the image of $R$, so $\varphi$ is surjective.

The last two bullets are different assertions. Existence of a family gives a map; a generating theorem gives surjectivity. Faithfulness of the $\mathbb T$-action gives

$$
\ker\varphi=\operatorname{Ann}_R(M),
\tag{2.5}
$$

but only after the $R$-action on $M$ has been verified to factor through (2.4).

For the numerical route, $R$ and $\mathbb T$ also carry compatible augmentations

$$
\lambda_R:R\longrightarrow\mathcal O,
\qquad
\lambda_{\mathbb T}:\mathbb T\longrightarrow\mathcal O,
\qquad
\lambda_{\mathbb T}\circ\varphi=\lambda_R.
\tag{2.6}
$$

These augmentations select the same integral eigensystem. Compatibility cannot be replaced by the existence of two unrelated $\mathcal O$-points.

### 2.3 The patched presentation

Let $R_{\mathrm{loc}}$ be the completed tensor product of the fixed old-place local deformation rings, formed with the flatness and residue-field hypotheses needed for the asserted dimension formula. If

$$
R_{\mathrm{loc}}
=R_1\widehat\otimes_{\mathcal O}\cdots
\widehat\otimes_{\mathcal O}R_t
$$

with nonzero $\mathcal O$-flat factors having the common residue field, then

$$
\dim R_{\mathrm{loc}}
=\sum_{i=1}^t\dim R_i-(t-1).
$$

The subtraction removes the repeated coefficient direction. Without the flatness hypotheses this formula is not automatic, and $\dim R_{\mathrm{loc}}$ must instead be supplied by an independent calculation. Fix the specified component or union of components at each old place. Let $G\geq0$ be the total number of smooth auxiliary, framing, and relative global coordinates after every coordinate has been counted exactly once. Put

$$
P_\infty
=R_{\mathrm{loc}}[[z_1,\ldots,z_q,x_1,\ldots,x_G]].
\tag{2.7}
$$

The patched deformation ring is a quotient

$$
R_\infty=P_\infty/J_\infty,
\qquad
J_\infty=(f_1,\ldots,f_c),
\qquad
c\leq b,
\tag{2.8}
$$

where $b$ is the uniform effective relation bound. We distinguish the actual minimal number $c=\mu_{P_\infty}(J_\infty)$ from a padded displayed length. When it is convenient to display exactly $b$ entries, some may be redundant, but a height argument must use $c$, not the length of a list padded by zeros.

The word **effective** in the relation bound has content. A cohomology space that merely receives obstruction classes does not bound $c$. The obstruction theory must be complete, functorial under small extensions, additive in square-zero kernels, and effective for universal relation directions. Equivalently, an independent algebraic presentation theorem may give (2.8) directly.

There are structural maps

$$
R_{\mathrm{loc}}\longrightarrow R_\infty,
\qquad
S_\infty\longrightarrow R_\infty.
\tag{2.9}
$$

The second map will be injective because of the patched module, not because the variables in (2.7) happen to have names.

### 2.4 The auxiliary regular ring and the patched module

The strong patched-module input is a nonzero module $M_\infty$ satisfying

$$
M_\infty\simeq S_\infty^{\oplus r}
\qquad(r\geq1).
\tag{2.10}
$$

It carries an $R_\infty$-action compatible with the map from $S_\infty$. The scalar action of $S_\infty$ in (2.10) is faithful, so the composite

$$
S_\infty\longrightarrow R_\infty
\longrightarrow\operatorname{End}_{S_\infty}(M_\infty)
\tag{2.11}
$$

is injective. Hence $S_\infty\to R_\infty$ itself is injective.

The strong input (2.10) normally comes from finite-level freeness over the exact diamond group algebras and a compatible-basis limiting argument. Equal coefficient ranks do not suffice. In a balanced or perfect-complex variant, one must first prove derived coinvariant concentration and torsion-freeness before replacing that variant by (2.10). The master theorem below begins only after the strong input has been obtained.

### 2.5 The acting quotient

Define the patched acting algebra by its image:

$$
A_\infty
=\operatorname{im}\left(
R_\infty\longrightarrow
\operatorname{End}_{S_\infty}(M_\infty)
\right).
\tag{2.12}
$$

Then there is a factorization

$$
R_\infty\twoheadrightarrow A_\infty
\hookrightarrow\operatorname{End}_{S_\infty}(M_\infty),
\tag{2.13}
$$

and the second arrow is injective by definition. If the named operators have been retained through patching, $A_\infty$ may be denoted $\mathbb T_\infty$. This notation never means that the first arrow in (2.13) is injective.

Put

$$
I_\infty
=\ker(R_\infty\to A_\infty)
=\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{2.14}
$$

The entire comparison problem at infinite level is the problem of determining $I_\infty$.

### 2.6 Dimension and relation data

The dimension of the presentation source is

$$
\dim P_\infty
=\dim R_{\mathrm{loc}}+q+G.
\tag{2.15}
$$

Krull's height theorem gives

$$
\dim R_\infty
\geq\dim P_\infty-c
\geq\dim P_\infty-b.
\tag{2.16}
$$

The **sharp Taylor--Wiles numerical identity** is

$$
\dim P_\infty-b=d=q+1.
\tag{2.17}
$$

Equation (2.17) is a ledger identity. It records the cancellation between the original reciprocity defect and the $q$ new regular directions. It does not say that the kernel in (2.8) has height $b$, and it does not by itself prove

$$
\dim R_\infty=d.
\tag{2.18}
$$

For complete-intersection conclusions we shall assume that $P_\infty$ is Cohen--Macaulay and satisfies the dimension formula along primes minimal over $J_\infty$. This holds in the standard case where $R_{\mathrm{loc}}$ is a complete intersection over $\mathcal O$: then $P_\infty$ is a complete, catenary, equidimensional Cohen--Macaulay local ring. If $R_{\mathrm{loc}}$ is regular, $P_\infty$ is regular.

### 2.7 Augmentation and exact control

The patched objects recover the finite-level objects through the ideal $\mathfrak a_\infty$. The required identities are

$$
R_\infty/\mathfrak a_\infty R_\infty
\xrightarrow{\sim}R,
\tag{2.19}
$$

$$
M_\infty/\mathfrak a_\infty M_\infty
\xrightarrow{\sim}M,
\tag{2.20}
$$

and, when full acting-algebra control is used,

$$
A_\infty/\mathfrak a_\infty A_\infty
\xrightarrow{\sim}\mathbb T.
\tag{2.21}
$$

The first two are exact recovery statements from the patched construction. The third requires saturation of the acting subalgebra inside the endomorphism algebra. Without that saturation there is only a canonical surjection from the left side of (2.21) onto $\mathbb T$.

The diagram

$$
\begin{array}{ccc}
R_\infty/\mathfrak a_\infty R_\infty&\longrightarrow&
A_\infty/\mathfrak a_\infty A_\infty\\
\downarrow\wr&&\downarrow\wr\\
R&\xrightarrow{\varphi}&\mathbb T
\end{array}
\tag{2.22}
$$

must commute. Exact recovery of the three objects without compatibility of the horizontal maps is not enough.

Freeness over $S_\infty$ gives

$$
\operatorname{Tor}^{S_\infty}_i
(\mathcal O,M_\infty)=0
\qquad(i>0),
\tag{2.23}
$$

so (2.20) is also exact derived specialization. No corresponding Tor vanishing for $R_\infty$ is included in (2.19).

### 2.8 Pairings, determinants, and local conditions

When duality is used, the input includes a companion module $M_\infty'$ and a perfect pairing

$$
H_\infty:M_\infty\times M_\infty'
\longrightarrow S_\infty
\tag{2.24}
$$

that is sesquilinear for diamond inversion. Named operators have named adjoints. A self-duality requires an additional compatible identification $M_\infty'\simeq M_\infty$; it is not contained in the word perfect. Even after that identification, the pairing remains sesquilinear unless an untwisting identifies the diamond involution with the ordinary scalar action. Its augmentation is an ordinary $\mathcal O$-bilinear pairing because diamond inversion acts trivially after $z_1=\cdots=z_q=0$.

For congruence ideals one also needs a rank-one distinguished generic eigenspace and an integral saturation statement. These are multiplicity-one inputs. A perfect pairing alone does not identify the module congruence ideal with the ring congruence ideal.

The determinant and local-condition ledger is fixed throughout:

- the residual representation is the same at every level;
- the determinant is the same prescribed character;
- every old local factor lies on the specified component or specified union of components;
- every auxiliary regular eigenline uses the same reciprocity convention as its diamond operator;
- augmentation makes auxiliary tame characters trivial and recovers the original unramified condition;
- the family giving $R_\infty\to A_\infty$ satisfies these conditions before universality is invoked.

These are not decorative arithmetic labels. They ensure that the map at the bottom of (2.22) is the canonical map for the intended deformation problem.

### 2.9 The ledger in one diagram

The entire strong input can be displayed as

$$
\begin{array}{ccccccccc}
R_{\mathrm{loc}}&\longrightarrow&P_\infty&\twoheadrightarrow&R_\infty
&\twoheadrightarrow&A_\infty&\hookrightarrow&
\operatorname{End}_{S_\infty}(M_\infty)\\
&&\mathord\uparrow&&\mathord\uparrow&&\mathord\uparrow&&\mathord\uparrow\\
&&S_\infty&=&S_\infty&=&S_\infty&=&S_\infty,
\end{array}
\tag{2.25}
$$

where

$$
R_\infty=P_\infty/(f_1,\ldots,f_c),
\qquad
M_\infty\simeq S_\infty^r,
\qquad
A_\infty=R_\infty/I_\infty.
\tag{2.26}
$$

At augmentation it becomes

$$
\begin{array}{ccccc}
R&\xrightarrow{\varphi}&\mathbb T&\hookrightarrow&
\operatorname{End}_{\mathcal O}(M)
\end{array}
\tag{2.27}
$$

provided (2.21) holds. Every later conclusion will cite the part of this ledger it uses.

## 3. The first consequences of the patched pair

### 3.1 The auxiliary action is faithful

The scalar action of $S_\infty$ on $M_\infty\simeq S_\infty^r$ is faithful. Therefore the composite (2.11) is injective. In particular,

$$
S_\infty\hookrightarrow R_\infty
\quad\text{and}\quad
S_\infty\hookrightarrow A_\infty.
\tag{3.1}
$$

This is the first legitimate faithfulness conclusion. It concerns the auxiliary ring. It does not concern the entire patched deformation ring.

The distinction is visible in the equality

$$
I_\infty\cap S_\infty=0.
\tag{3.2}
$$

Equation (3.2) says that the action kernel contains no nonzero pure diamond scalar. It can still contain deformation equations, an ideal defining an unobserved component, or nilpotent thickness transverse to $S_\infty$.

### 3.2 Finiteness of the acting algebra

The free module has finite endomorphism algebra

$$
\operatorname{End}_{S_\infty}(M_\infty)
\simeq M_r(S_\infty)
\tag{3.3}
$$

as an $S_\infty$-module. The subalgebra $A_\infty$ is therefore finite over $S_\infty$, because $S_\infty$ is Noetherian. The injective finite local map in (3.1) gives

$$
\dim A_\infty=\dim S_\infty=d.
\tag{3.4}
$$

Nothing here proves that $R_\infty$ is finite over $S_\infty$. A quotient of $R_\infty$ is finite; the source can have additional components or additional positive-dimensional directions killed by the action. This is the first place at which one must resist using $A_\infty$ as though it were already $R_\infty$.

### 3.3 Depth over three rings

Freeness gives

$$
\operatorname{depth}_{S_\infty}M_\infty=d.
\tag{3.5}
$$

The finite local map $S_\infty\to A_\infty$ has

$$
\sqrt{\mathfrak m_{S_\infty}A_\infty}
=\mathfrak m_{A_\infty}.
\tag{3.6}
$$

For a finite module, depth in an ideal depends only on its radical. Hence

$$
\operatorname{depth}_{A_\infty}M_\infty=d.
\tag{3.7}
$$

The surjection $R_\infty\twoheadrightarrow A_\infty$ is also finite and local. The same finite-map depth comparison, now applied to the same module, gives

$$
\boxed{
\operatorname{depth}_{R_\infty}M_\infty=d.}
\tag{3.8}
$$

This proof uses the finite action quotient twice. A general inclusion $S_\infty\to R_\infty$ would give only the visible regular sequence and the lower bound $\operatorname{depth}_{R_\infty}M_\infty\geq d$. Equality in (3.8) requires that the $R_\infty$-action factor through the finite local $S_\infty$-algebra $A_\infty$.

### 3.4 The exact support dimension

The action of $A_\infty$ is faithful, so

$$
\operatorname{Supp}_{A_\infty}M_\infty
=\operatorname{Spec}A_\infty.
\tag{3.9}
$$

Through the quotient $R_\infty\to A_\infty$,

$$
\operatorname{Supp}_{R_\infty}M_\infty
=V(I_\infty)
\simeq\operatorname{Spec}A_\infty
\tag{3.10}
$$

as a closed set. Consequently

$$
\boxed{
\dim_{R_\infty}M_\infty
=\dim\operatorname{Supp}_{R_\infty}M_\infty
=d.}
\tag{3.11}
$$

Combining (3.8) and (3.11), $M_\infty$ is a Cohen--Macaulay $R_\infty$-module on its support. It is maximal Cohen--Macaulay over $R_\infty$ if and only if

$$
\dim R_\infty=d.
\tag{3.12}
$$

The qualifier in the last sentence is essential. Module dimension, not ambient ring dimension, enters the definition of a Cohen--Macaulay module. Maximality is an additional equality with the ambient ring.

### 3.5 Generic ranks and generic multiplicity

Let $\mathfrak p$ be a minimal prime of $R_\infty$. The component $V(\mathfrak p)$ is **seen** by $M_\infty$ when

$$
(M_\infty)_{\mathfrak p}\ne0.
\tag{3.13}
$$

Equivalently,

$$
I_\infty\subseteq\mathfrak p.
\tag{3.14}
$$

If $R_\infty/\mathfrak p$ is a domain, put

$$
K(\mathfrak p)=\operatorname{Frac}(R_\infty/\mathfrak p).
\tag{3.15}
$$

On a seen component the **generic multiplicity** is

$$
m(\mathfrak p)
=\dim_{K(\mathfrak p)}
\left(M_\infty\otimes_{R_\infty}K(\mathfrak p)\right).
\tag{3.16}
$$

It is positive exactly when the component is seen. Its value can be useful for multiplicity-one and rank calculations, but positivity is the only fact relevant to component coverage.

If the ring is reduced, localization at a minimal prime is a field and any nonzero module over that field is faithful. Thus the action kernel localizes to zero at every seen minimal prime. This is a generic statement. It kills the global kernel only when every minimal prime is seen and the natural map into the product of the generic localizations is injective, as it is for a reduced Noetherian ring.

### 3.6 What these conclusions do not imply

The conclusions of this chapter are strong but sharply limited:

$$
\begin{array}{c|c}
\text{proved}&\text{not yet proved}\\ \hline
S_\infty\hookrightarrow A_\infty
&R_\infty\hookrightarrow A_\infty\\
A_\infty\text{ finite over }S_\infty
&R_\infty\text{ finite over }S_\infty\\
\dim A_\infty=d
&\dim R_\infty=d\\
\operatorname{depth}_{R_\infty}M_\infty=d
&M_\infty\text{ is }R_\infty\text{-free}\\
\dim\operatorname{Supp}M_\infty=d
&\operatorname{Supp}M_\infty=\operatorname{Spec}R_\infty\\
A_\infty\text{ acts faithfully}
&R_\infty\text{ acts faithfully}.
\end{array}
\tag{3.17}
$$

Every entry in the right column needs a new argument. The remaining chapters supply those arguments under hypotheses that can be checked independently.

## 4. Sharp dimension and Cohen--Macaulay structure

### 4.1 The relation lower bound

Write

$$
R_\infty=P_\infty/J_\infty,
\qquad
J_\infty=(f_1,\ldots,f_c),
\qquad c\le b.
\tag{4.1}
$$

The integer $b$ is the relation budget furnished by the global presentation, while $c$ is the number of generators actually retained after redundant equations have been removed. The dimension entry in the ledger is

$$
\dim P_\infty=d+b.
\tag{4.2}
$$

Krull's height theorem gives

$$
\operatorname{ht}_{P_\infty}(J_\infty)\le c\le b.
\tag{4.3}
$$

Suppose that $P_\infty$ is catenary and equidimensional and that, for every prime $\mathfrak q$ minimal over $J_\infty$, the dimension formula

$$
\dim P_\infty/\mathfrak q
=\dim P_\infty-\operatorname{ht}_{P_\infty}(\mathfrak q)
\tag{4.4}
$$

holds. This is automatic for the complete local rings normally used as presentation rings when they are equidimensional quotients of regular local rings. Equations (4.2)--(4.4) imply, component by component,

$$
\dim P_\infty/\mathfrak q\ge d.
\tag{4.5}
$$

Consequently every irreducible component of $R_\infty$ has dimension at least $d$, and in particular

$$
\dim R_\infty\ge d.
\tag{4.6}
$$

This is only a lower bound. The relation count says that the quotient cannot be too small. It does not say that the quotient has no unexpectedly large component. The inequality is also componentwise, a feature that will later interact with component coverage.

One must not reverse (4.6) by appealing to the module. We know that $M_\infty$ has support of dimension $d$, but a ring may have components outside that support. The ambient ring can therefore have dimension larger than the dimension of its patched module.

### 4.2 Why the action quotient is not a dimension ceiling

The faithful action quotient satisfies

$$
A_\infty=R_\infty/I_\infty,
\qquad
\dim A_\infty=d.
\tag{4.7}
$$

Since a quotient cannot have larger dimension than its source, (4.7) merely reproduces

$$
d\le\dim R_\infty.
\tag{4.8}
$$

It provides no inequality in the other direction. Nor does the finiteness of $A_\infty$ over $S_\infty$ imply finiteness of $R_\infty$ over $S_\infty$: a quotient may be finite while the source has an entire extra component. The elementary surjection

$$
k[[x,y]]/(xy)\longrightarrow k[[y]],
\qquad x\longmapsto0,
\tag{4.9}
$$

already exhibits this defect. The target is finite over $k[[y]]$, while the source is not finite over the displayed copy of $k[[y]]$ because the component $y=0$ remains.

Similarly, the equality

$$
\operatorname{depth}_{R_\infty}M_\infty=d
\tag{4.10}
$$

does not imply $\dim R_\infty\le d$. The general inequality is

$$
\operatorname{depth}_{R_\infty}M_\infty
\le\dim_{R_\infty}M_\infty
\le\dim R_\infty.
\tag{4.11}
$$

Here the first two terms both equal $d$; the last can still be larger. Any proof that jumps from (4.10) to $\dim R_\infty=d$ has silently assumed that the module has full support.

### 4.3 Three valid dimension ceilings

There are three standard ways to establish the missing upper bound. They are logically independent inputs.

**A deformation-theoretic ceiling.** A direct calculation of tangent and obstruction dimensions, or a known dimension theorem for the prescribed local deformation conditions, may give

$$
\dim R_\infty\le d.
\tag{4.12}
$$

Together with (4.6), this gives equality. Such a calculation must concern the same fixed determinant and the same local components as the patched ring.

**Finiteness over the auxiliary ring.** If it is independently known that $R_\infty$ is finite over $S_\infty$, then

$$
\dim R_\infty=\dim S_\infty=d.
\tag{4.13}
$$

Finiteness cannot be borrowed from $A_\infty$ unless the kernel $I_\infty$ is already known to be nilpotent. Indeed, if $I_\infty^N=0$, the filtration

$$
R_\infty\supset I_\infty\supset\cdots\supset I_\infty^N=0
\tag{4.14}
$$

has successive quotients finite over $A_\infty$, hence finite over $S_\infty$; it then proves that $R_\infty$ is finite. Without nilpotence this argument is unavailable.

**Coverage of every minimal component.** Assume that

$$
(M_\infty)_{\mathfrak p}\ne0
\quad\text{for every }\mathfrak p\in\operatorname{Min}R_\infty.
\tag{4.15}
$$

For such a minimal prime, $I_\infty\subseteq\mathfrak p$, so

$$
V(\mathfrak p)\subseteq V(I_\infty)
=\operatorname{Supp}_{R_\infty}M_\infty.
\tag{4.16}
$$

The right side has dimension $d$. Thus

$$
\dim R_\infty/\mathfrak p\le d.
\tag{4.17}
$$

The componentwise lower bound (4.5) supplies the reverse inequality. Hence every component has dimension exactly $d$, and

$$
\boxed{\dim R_\infty=d.}
\tag{4.18}
$$

This third proof is the basic component argument. Notice its two distinct ingredients: the relation presentation gives the lower bound on each component, and coverage places each component inside a closed set of dimension $d$. Equidimensionality of $P_\infty$ does not replace coverage. Nor does a statement that one automorphic component has the expected dimension say anything about the unseen components.

Once any one of (4.12), (4.13), or (4.15) proves (4.18), equation (3.8) says

$$
\operatorname{depth}_{R_\infty}M_\infty
=\dim R_\infty=d.
\tag{4.19}
$$

Thus $M_\infty$ is maximal Cohen--Macaulay over $R_\infty$. This is a depth conclusion, not a freeness conclusion.

### 4.4 From equality to a regular sequence

Assume now that $P_\infty$ is Cohen--Macaulay, that (4.4) holds, and that $\dim R_\infty=d$. By (4.5), every component of $R_\infty$ has dimension at least $d$; since the dimension of the whole ring is $d$, every component has dimension exactly $d$. Thus $R_\infty$ is equidimensional. Let $\mathfrak q$ be minimal over $J_\infty$. Equations (4.2) and (4.4) give

$$
\operatorname{ht}_{P_\infty}(\mathfrak q)
=d+b-\dim P_\infty/\mathfrak q.
\tag{4.20}
$$

The preceding observation makes the right side equal to $b$ for every such $\mathfrak q$. Hence

$$
\operatorname{ht}_{P_\infty}(J_\infty)=b.
\tag{4.21}
$$

But $J_\infty$ is generated by $c\le b$ elements, while height is at most the minimal number of generators. Therefore

$$
c=b
\quad\text{and}\quad
\mu_{P_\infty}(J_\infty)=b.
\tag{4.22}
$$

In a Cohen--Macaulay local ring, an ideal of height $b$ generated by $b$ elements is generated by a regular sequence. After replacing the displayed generators by a minimal generating set, we obtain

$$
f_1,\ldots,f_b
\quad\text{a }P_\infty\text{-regular sequence}.
\tag{4.23}
$$

It follows that $R_\infty$ is Cohen--Macaulay and

$$
\operatorname{depth}R_\infty
=\dim R_\infty=d.
\tag{4.24}
$$

The order of proof matters. One first proves the dimension equality without assuming that the relations are regular. Only then does height equal number of generators, allowing (4.23). Declaring the presentation to be a complete intersection at the outset would assume the desired sharpness.

There is also a componentwise version. If a union of components $X_\Sigma$ is cut out by an ideal $P_\Sigma$ and the induced presentation of its coordinate ring has height exactly $b$ and $b$ generators in a Cohen--Macaulay ambient ring, that component quotient is Cohen--Macaulay. This conclusion requires an actual presentation of the component quotient; it is not obtained merely by deleting other minimal primes from a complete-intersection ring.

### 4.5 Complete-intersection rings and complete-intersection maps

The phrase “complete intersection” has two uses that must be kept separate.

First, a local ring $B$ is an **absolute complete-intersection ring** if

$$
B\cong Q/(g_1,\ldots,g_e)
\tag{4.25}
$$

for a regular local ring $Q$ and a $Q$-regular sequence $g_1,\ldots,g_e$. Second, a local map $C\to B$ is a **complete-intersection map** if, after a formally smooth local factorization

$$
C\longrightarrow Q\longrightarrow B,
\tag{4.26}
$$

the kernel of $Q\to B$ is generated by a regular sequence. The base $C$ need not be regular.

In the patched setting the natural source often has the form

$$
P_\infty=R_{\mathrm{loc}}[[x_1,\ldots,x_g,z_1,\ldots,z_q]].
\tag{4.27}
$$

If (4.23) holds, then the map

$$
R_{\mathrm{loc}}\longrightarrow R_\infty
\tag{4.28}
$$

is a complete-intersection map of relative codimension $b$. The ring $R_\infty$ itself is an absolute complete intersection only if $P_\infty$ is regular, or more generally if a regular presentation of $P_\infty$ can be concatenated with (4.23). In particular:

$$
\begin{array}{c}
P_\infty\text{ regular}\\
\Downarrow\\
R_\infty\text{ absolute complete intersection};
\end{array}
\tag{4.29}
$$

and

$$
\begin{array}{c}
R_{\mathrm{loc}}\text{ complete intersection and }(4.23)\\
\Downarrow\\
R_\infty\text{ absolute complete intersection}.
\end{array}
\tag{4.30}
$$

If $R_{\mathrm{loc}}$ is merely Cohen--Macaulay, (4.23) proves that $R_\infty$ is Cohen--Macaulay and that (4.28) is a complete-intersection map; it does not prove (4.30).

Codimension bookkeeping is equally important. The relative codimension is $b$, the height of $J_\infty$ in $P_\infty$. If $P_\infty=Q/(h_1,\ldots,h_a)$ with $Q$ regular and the $h_i$ regular, then

$$
R_\infty
\cong Q/(h_1,\ldots,h_a,f_1,\ldots,f_b)
\tag{4.31}
$$

has absolute codimension $a+b$. The second sequence remains regular after the first quotient, so the concatenated sequence is regular. No codimension may be discarded merely because some variables were introduced for convenience.

### 4.6 Auslander--Buchsbaum and miracle flatness

The freeness over $S_\infty$ assumed for $M_\infty$ is part of the patched input. Under near faithfulness it can also force freeness of the ring $R_\infty$ over $S_\infty$, but the proof uses several hypotheses.

Assume:

1. $I_\infty=\operatorname{Ann}_{R_\infty}(M_\infty)$ is nilpotent;
2. $A_\infty=R_\infty/I_\infty$ is finite over $S_\infty$;
3. $R_\infty$ is Cohen--Macaulay of dimension $d$;
4. $S_\infty$ is regular local of dimension $d$ and the map $S_\infty\to R_\infty$ is local.

The nilpotent filtration (4.14) first proves that $R_\infty$ is finite over $S_\infty$. For a finite local map, depth of a finite module computed over the source equals depth computed over the target. Applied to the module $R_\infty$, this gives

$$
\operatorname{depth}_{S_\infty}R_\infty
=\operatorname{depth}_{R_\infty}R_\infty=d.
\tag{4.32}
$$

Because $S_\infty$ is regular local, it has finite global dimension $d$. Thus $R_\infty$, as a finite $S_\infty$-module, has finite projective dimension. The Auslander--Buchsbaum formula applies:

$$
\operatorname{pd}_{S_\infty}R_\infty
+\operatorname{depth}_{S_\infty}R_\infty
=\operatorname{depth}S_\infty=d.
\tag{4.33}
$$

Equations (4.32) and (4.33) give projective dimension zero. A finite projective module over a local ring is free, so

$$
\boxed{R_\infty\text{ is finite free over }S_\infty.}
\tag{4.34}
$$

This is the finite local form of miracle flatness. Its hypotheses include finiteness, Cohen--Macaulayness of the module being tested, and dimension equality. It is invalid to cite it before proving that $R_\infty$ is finite over $S_\infty$.

The same argument applies directly to $A_\infty$ once $A_\infty$ is known to be Cohen--Macaulay of dimension $d$. In fact $M_\infty$ need not be rank one for that purpose. On the other hand, it does not make $M_\infty$ free over $R_\infty$. Auslander--Buchsbaum over $R_\infty$ would require finite projective dimension of $M_\infty$ over $R_\infty$, a property not implied by maximal Cohen--Macaulayness when $R_\infty$ is singular.

### 4.7 Where intersection theory enters

The core argument above uses only Krull's height theorem, the dimension formula (4.4), and the Cohen--Macaulay height criterion. It does not silently appeal to an intersection multiplicity theorem. This economy is useful because stronger intersection statements require stronger hypotheses.

There is, however, an intersection-theoretic interpretation. The $b$ equations defining $R_\infty$ inside $P_\infty$ have expected codimension $b$. Sharp dimension says that their common zero locus has precisely this codimension on every relevant component. In a Cohen--Macaulay ambient ring, proper codimension is exactly what prevents hidden excess intersection and turns the equations into a regular sequence.

If one replaces the relation presentation by a finite free complex, the corresponding dimension tool is the new intersection theorem: for a Noetherian local ring $B$, a bounded complex

$$
0\longrightarrow F_s\longrightarrow\cdots\longrightarrow F_0\longrightarrow0
\tag{4.35}
$$

of finite free $B$-modules whose homology has finite length and whose zeroth homology is nonzero must have $s\ge\dim B$. An argument using (4.35) must actually construct such a complex and verify finite-length homology. Nothing in mere $S_\infty$-freeness supplies those conditions. In the present setting the explicit relation presentation is stronger and more transparent, so all later complete-intersection conclusions will rest on (4.21)--(4.23).

## 5. Support, components, and annihilators

### 5.1 Height zero is only a beginning

Let

$$
I_\infty=\operatorname{Ann}_{R_\infty}(M_\infty).
\tag{5.1}
$$

Since $R_\infty/I_\infty=A_\infty$ has dimension $d$, if $R_\infty$ is equidimensional of dimension $d$, the ideal $I_\infty$ has height zero in the sense that some prime minimal over it is a minimal prime of $R_\infty$. This does not imply $I_\infty=0$. Height-zero ideals can remove components, thicken components, or do both.

More explicitly, under the catenary dimension formula,

$$
\operatorname{ht}_{R_\infty}(I_\infty)
:=\inf_{\mathfrak q\supseteq I_\infty}
\operatorname{ht}_{R_\infty}(\mathfrak q)=0.
$$

This infimum records the existence of at least one height-zero prime over the annihilator. It does not assert that every minimal prime contains the annihilator, and it says nothing about the scheme structure along the primes that do contain it.

The exact topological identity is

$$
\operatorname{Supp}_{R_\infty}M_\infty
=V(I_\infty).
\tag{5.2}
$$

Thus support determines only the radical

$$
\sqrt{I_\infty}.
\tag{5.3}
$$

It cannot distinguish $I_\infty$ from a nilpotent thickening of the same ideal. Faithfulness, by contrast, is the scheme-theoretic equality $I_\infty=0$. Most errors in the last step of patching come from substituting a statement about (5.3) for a statement about (5.1).

### 5.2 Support as a union of components

Assume the conclusions of Section 4.4: $R_\infty$ is Noetherian, Cohen--Macaulay, and equidimensional of dimension $d$, while $M_\infty$ is maximal Cohen--Macaulay. A Cohen--Macaulay module in this catenary local setting is unmixed: every prime minimal in its support has quotient dimension $d$. Thus every irreducible component of $V(I_\infty)$ is contained in an irreducible component of $\operatorname{Spec}R_\infty$ of the same dimension. A proper closed irreducible subset of an ambient component has smaller dimension by the dimension formula in the ledger. It follows that

$$
V(I_\infty)
=\bigcup_{\mathfrak p\in\Sigma}V(\mathfrak p)
\tag{5.4}
$$

for a nonempty subset

$$
\Sigma\subseteq\operatorname{Min}R_\infty.
\tag{5.5}
$$

Equivalently,

$$
\sqrt{I_\infty}
=P_\Sigma:=\bigcap_{\mathfrak p\in\Sigma}\mathfrak p.
\tag{5.6}
$$

This is the precise meaning of saying that the patched module lives on a union of components. The conclusion uses both dimension equality and the absence of embedded dimension anomalies encoded in the catenary/equidimensional hypotheses. Before dimension equality, the support could instead be a proper codimension-zero-looking subset of a larger component.

At a minimal prime $\mathfrak p$, the following are equivalent:

$$
\mathfrak p\in\Sigma
\Longleftrightarrow
I_\infty\subseteq\mathfrak p
\Longleftrightarrow
(M_\infty)_{\mathfrak p}\ne0.
\tag{5.7}
$$

The last equivalence follows because localization kills a finite module precisely outside its support. It is often checked by identifying a nonzero generic arithmetic point or by a component-hopping theorem. It is never a consequence of equidimensionality alone.

### 5.3 The component-coverage hypothesis

We isolate the hypothesis that cannot be hidden inside dimension language.

> **Component coverage.** For every minimal prime $\mathfrak p$ of $R_\infty$, the generic fiber $(M_\infty)_{\mathfrak p}$ is nonzero.

By (5.7), component coverage is equivalent to $\Sigma=\operatorname{Min}R_\infty$. It then gives

$$
\operatorname{Supp}_{R_\infty}M_\infty
=\operatorname{Spec}R_\infty.
\tag{5.8}
$$

There are several legitimate ways an application may verify coverage:

- each irreducible component contains a Zariski-dense set of characteristic-zero points with nonzero eigenspace, or contains such a point in a component-separating open after (5.4) has been proved;
- $R_\infty$ is independently known to be irreducible, so the nonempty support in (5.4) contains its only component;
- an independently proved component-hopping result transports nonvanishing from known automorphic components to every allowed component;
- the global deformation problem has been defined from the outset by quotienting to the union of components already known to occur.

The last choice produces a componentwise theorem, not a theorem for an omitted larger ring. The third is a substantive arithmetic theorem. Calling it “standard” does not remove it from the hypothesis list.

Coverage is also the bridge between dimension and finiteness. Once it holds, (5.8) implies that $I_\infty$ is nilpotent; the nilpotent filtration then makes $R_\infty$ finite over $S_\infty$. This is the valid order. Using finiteness to prove dimension and dimension to prove coverage would be circular unless one of the steps came from an independent source.

### 5.4 Faithful, nearly faithful, and faithful modulo nilpotents

For a finite $R_\infty$-module $M_\infty$, we use the following terminology.

It is **faithful** if

$$
I_\infty=0.
\tag{5.9}
$$

It is **nearly faithful** if $I_\infty$ is nilpotent. Because $R_\infty$ is Noetherian, this is equivalent to each of

$$
I_\infty\subseteq\sqrt{(0)},
\qquad
\sqrt{I_\infty}=\sqrt{(0)},
\qquad
V(I_\infty)=\operatorname{Spec}R_\infty.
\tag{5.10}
$$

Indeed, an ideal contained in the nilradical is a finitely generated nil ideal and is therefore nilpotent. Thus

$$
\boxed{
M_\infty\text{ nearly faithful}
\Longleftrightarrow
M_\infty\text{ has full support}.}
\tag{5.11}
$$

Some accounts use “nearly faithful” for the equality of radicals in (5.10). Under the Noetherian hypothesis this is the same definition, but the nilpotence exponent is not canonical and need not be one.

The phrase **faithful modulo nilpotents** is best attached to the map of rings rather than literally to the module. A nearly faithful action gives an isomorphism

$$
R_\infty^{\mathrm{red}}
\xrightarrow{\sim}
A_\infty^{\mathrm{red}}.
\tag{5.12}
$$

It need not make $M_\infty$ a module over $R_\infty^{\mathrm{red}}$, because the whole nilradical need not annihilate $M_\infty$. Statement (5.12) means that the action loses no reduced geometric information. It does not mean that its original kernel is zero.

The implications are therefore

$$
\text{faithful}
\Longrightarrow
\text{nearly faithful}
\Longrightarrow
\text{faithful modulo nilpotents},
\tag{5.13}
$$

where the first implication is strict for nonreduced rings, and the second is an equality of descriptions only at the level of reduced quotients.

### 5.5 Reducedness and direct annihilator arguments

If $R_\infty$ is reduced and $M_\infty$ has full support, then

$$
I_\infty\subseteq\sqrt{(0)}=0,
\tag{5.14}
$$

so the module is faithful. Equivalently, the natural injection

$$
R_\infty
\hookrightarrow
\prod_{\mathfrak p\in\operatorname{Min}R_\infty}
\operatorname{Frac}(R_\infty/\mathfrak p)
\tag{5.15}
$$

shows that an element acting as zero on a nonzero generic module on every component must itself be zero.

Reducedness is sufficient, not necessary. A direct annihilator argument may prove $I_\infty=0$ even if $R_\infty$ has nilpotents. Typical direct inputs are:

- $M_\infty$ contains $R_\infty$ as a direct summand;
- $M_\infty$ is free of positive rank over $R_\infty$;
- $M_\infty$ is cyclic with annihilator known independently to vanish;
- a perfect trace pairing identifies $R_\infty$ with a submodule of an endomorphism module on which the action is visibly faithful.

Each is stronger than support. A perfect self-pairing on $M_\infty$ by itself is not on this list: it can descend perfectly to a quotient while a nilpotent kernel remains invisible.

There is a precise local test that packages such arguments. Let $B$ be Noetherian and $N$ a finite $B$-module. Then

$$
N\text{ is faithful over }B
\Longleftrightarrow
\operatorname{Ann}_{B_{\mathfrak p}}(N_{\mathfrak p})=0
\text{ for every }\mathfrak p\in\operatorname{Ass}_B(B).
\tag{5.16}
$$

Only the reverse implication needs proof. Put $J=\operatorname{Ann}_B(N)$ and suppose $J\ne0$. The nonzero finite submodule $J\subseteq B$ has an associated prime $\mathfrak p$, and $\operatorname{Ass}_B(J)\subseteq\operatorname{Ass}_B(B)$. Choosing an element of $J$ whose annihilator is $\mathfrak p$ shows that $J_{\mathfrak p}\ne0$. Since $J_{\mathfrak p}$ annihilates $N_{\mathfrak p}$, the localized action is not faithful, contrary to the right side of (5.16).

When $B$ is Cohen--Macaulay local, it has no embedded associated primes, so $\operatorname{Ass}_B(B)=\operatorname{Min}B$. In that case it is enough to prove scheme-theoretic faithfulness at every generic local ring. This remains strictly stronger than component coverage: over a nonreduced zero-dimensional local ring, a nonzero module may still have a nonzero nilpotent annihilator. Criterion (5.16) is therefore a genuine nilpotent-killing argument, whereas the condition $N_{\mathfrak p}\ne0$ is only a component-detection argument.

Reducedness only at finite level does not by itself prove $I_\infty=0$. It may kill the image of $I_\infty$ after augmentation while leaving a kernel supported in the augmentation direction. Conversely, reducedness of $R_\infty$ proves patched faithfulness and therefore finite equality without requiring reducedness of $R$ as a separate input.

### 5.6 Componentwise quotients

Let $\Sigma$ be the set of components seen by $M_\infty$ and define the reduced component ideal

$$
P_\Sigma=\bigcap_{\mathfrak p\in\Sigma}\mathfrak p.
\tag{5.17}
$$

Equation (5.6) gives

$$
(R_\infty/P_\Sigma)^{\mathrm{red}}
\xrightarrow{\sim}
A_\infty^{\mathrm{red}}.
\tag{5.18}
$$

Since $R_\infty/P_\Sigma$ is already reduced by construction, this can be written

$$
R_\infty/P_\Sigma
\xrightarrow{\sim}
A_\infty^{\mathrm{red}}.
\tag{5.19}
$$

Scheme-theoretic component equality is stronger. It requires

$$
I_\infty=P_\Sigma,
\tag{5.20}
$$

not merely equality of radicals. Under (5.20),

$$
R_\infty/P_\Sigma\xrightarrow{\sim}A_\infty.
\tag{5.21}
$$

Thus a componentwise $R=T$ theorem has two possible meanings: equality after reducing the selected union, which follows from topological support, or equality with its chosen scheme structure, which needs control of the annihilator itself.

At finite level the selected quotient is

$$
R_\Sigma
:=R_\infty/(P_\Sigma+\mathfrak a_\infty).
\tag{5.22}
$$

This definition records how the patched components specialize. It need not coincide with an independently chosen union of components of $R$ unless specialization of minimal primes has been checked. A component theorem must state which of these two meanings is intended.

## 6. Comparing the patched deformation and action algebras

### 6.1 Surjectivity comes first

The patched comparison begins with a map

$$
\rho_\infty:R_\infty\longrightarrow\operatorname{End}_{S_\infty}(M_\infty).
\tag{6.1}
$$

Define $A_\infty$ to be its image. Then the induced map

$$
R_\infty\twoheadrightarrow A_\infty
\tag{6.2}
$$

is surjective by definition, and

$$
\ker(6.2)=I_\infty.
\tag{6.3}
$$

If instead an independently presented patched Hecke algebra $\mathbb T_\infty$ is used, one must prove that the deformation action generates it before asserting a surjection

$$
R_\infty\twoheadrightarrow\mathbb T_\infty.
\tag{6.4}
$$

Once that generator theorem is available and $\mathbb T_\infty$ acts faithfully, it identifies $\mathbb T_\infty$ with $A_\infty$. Until then there are three distinct objects: the image $A_\infty$, the named algebra $\mathbb T_\infty$, and the full endomorphism ring.

The surjection (6.2) is the beginning of the comparison, not its conclusion. Equal dimensions on the two sides do not make it injective. The kernel may be a minimal prime, a nilpotent ideal, or an ideal whose quotient has the same dimension for another reason.

### 6.2 The faithful acting quotient

The advantage of $A_\infty$ is tautological but important:

$$
A_\infty\hookrightarrow\operatorname{End}_{S_\infty}(M_\infty).
\tag{6.5}
$$

Thus $M_\infty$ is a faithful $A_\infty$-module. This statement says nothing about faithfulness over $R_\infty$ until the kernel in (6.3) has been studied.

Since $M_\infty\cong S_\infty^r$, the endomorphism ring is a matrix algebra:

$$
\operatorname{End}_{S_\infty}(M_\infty)
\cong M_r(S_\infty).
\tag{6.6}
$$

Consequently $A_\infty$ is a finite torsion-free $S_\infty$-module. The torsion-free assertion follows from its injection into a free module. In particular, after tensoring with the fraction field $K_\infty$ of $S_\infty$,

$$
A_{\infty,K}:=A_\infty\otimes_{S_\infty}K_\infty
\hookrightarrow M_r(K_\infty).
\tag{6.7}
$$

The generic rank

$$
\operatorname{rank}_{S_\infty}A_\infty
=\dim_{K_\infty}A_{\infty,K}
\tag{6.8}
$$

is therefore finite and at most $r^2$. Generic rank controls the size of the faithful quotient, but not the nilpotent or component kernel in $R_\infty$.

### 6.3 Criteria for injectivity

For the surjection (6.2), the following are valid injectivity criteria.

1. **Direct faithfulness:** $\operatorname{Ann}_{R_\infty}M_\infty=0$.
2. **Reduced full support:** $R_\infty$ is reduced and $(M_\infty)_{\mathfrak p}\ne0$ for every $\mathfrak p\in\operatorname{Min}R_\infty$.
3. **Generic injectivity plus torsion control:** $R_\infty$ is torsion-free over a domain $S_\infty$, and (6.2) becomes injective after tensoring with its fraction field.
4. **A length or Fitting criterion:** both rings are finite free over a common Artinian or DVR base and the kernel has length zero, established from an exact numerical identity.
5. **A common presentation criterion:** the source and target are quotients of the same local ring by ideals whose inclusion and equality are proved, for example by Nakayama after equality of conormal modules.

Criterion 3 deserves proof. Let $K_\infty=\operatorname{Frac}S_\infty$. If $x\in I_\infty$, generic injectivity gives

$$
x\otimes1=0
\quad\text{in }R_\infty\otimes_{S_\infty}K_\infty.
\tag{6.9}
$$

Hence some nonzero $s\in S_\infty$ satisfies $sx=0$. Torsion-freeness of $R_\infty$ over $S_\infty$ forces $x=0$. Notice that torsion-freeness of the target $A_\infty$ is irrelevant to this last step; it is the source that must have no vertical torsion.

None of these criteria may be replaced by “surjective and equidimensional.” The latter controls only prime chains, not the scheme-theoretic kernel.

### 6.4 Generic-rank criteria

Suppose $R_\infty$ and $A_\infty$ are finite torsion-free modules over the domain $S_\infty$. A surjection between them gives

$$
\operatorname{rank}_{S_\infty}R_\infty
\ge
\operatorname{rank}_{S_\infty}A_\infty.
\tag{6.10}
$$

If the ranks are equal, the kernel has $S_\infty$-rank zero. This shows only that the kernel is $S_\infty$-torsion. If the source is itself $S_\infty$-torsion-free, every submodule is torsion-free, so a rank-zero submodule must vanish. Thus:

> A surjection of finite torsion-free modules over a domain is an isomorphism when their generic ranks agree.

This criterion is often applied after miracle flatness has made both rings finite free over $S_\infty$. The generic rank equality must still be proved, perhaps by characteristic-zero multiplicity one or by counting points with multiplicities. Equality of Krull dimensions is not equality of generic ranks.

If $S_\infty$ has several minimal primes, one must compare rank at each minimal prime. A single total-rank number can conceal loss on one component and gain on another. The appropriate assertion is that (6.2) becomes an isomorphism after localization at every minimal prime of $S_\infty$, followed by torsion-freeness of its kernel.

### 6.5 Fitting criteria

For a finite presentation

$$
S_\infty^m\xrightarrow{B}S_\infty^n
\longrightarrow N\longrightarrow0,
\tag{6.11}
$$

the zeroth Fitting ideal $\operatorname{Fitt}_{S_\infty}^0(N)$ is generated by the $n\times n$ minors of $B$. It is independent of the presentation and satisfies

$$
\operatorname{Fitt}_{S_\infty}^0(N)
\subseteq\operatorname{Ann}_{S_\infty}(N),
\qquad
\sqrt{\operatorname{Fitt}_{S_\infty}^0(N)}
=\sqrt{\operatorname{Ann}_{S_\infty}(N)}.
\tag{6.12}
$$

Apply this to the kernel or cokernel of a comparison map only after it is known to be finite over the chosen base. If $K=\ker(R_\infty\to A_\infty)$ is finite over $S_\infty$ and

$$
\operatorname{Fitt}_{S_\infty}^0(K)=S_\infty,
\tag{6.13}
$$

then $K=0$. By contrast, knowing only that the Fitting ideal has radical equal to the nilradical gives a support statement, not zero.

Fitting ideals also behave well under base change:

$$
\operatorname{Fitt}_{B}^0(N\otimes_A B)
=\operatorname{Fitt}_{A}^0(N)B
\tag{6.14}
$$

for a finitely presented $A$-module $N$ and an $A$-algebra $B$. This identity is useful in augmentation descent, but it cannot recover a kernel killed by specialization. To infer $K=0$ from $K/\mathfrak a_\infty K=0$, one needs $K$ finite over the local ring $S_\infty$ and then applies Nakayama. Establishing that finiteness is part of the proof.

### 6.6 Rank one over the auxiliary ring

When $r=1$, one has

$$
M_\infty\cong S_\infty,
\qquad
\operatorname{End}_{S_\infty}(M_\infty)=S_\infty.
\tag{6.15}
$$

Since $S_\infty$ already acts on $M_\infty$ and its action lies in $A_\infty$, equations (6.5) and (6.15) force

$$
A_\infty=S_\infty.
\tag{6.16}
$$

Thus the faithful action quotient is particularly simple. Nevertheless $R_\infty$ need not equal $S_\infty$: it may have extra components or a nilpotent ideal annihilating $M_\infty$. Rank one simplifies the target; it does not erase the source kernel.

If $R_\infty$ is reduced with full support, (6.16) and faithfulness do give $R_\infty\cong S_\infty$. If instead only near faithfulness is known, they give

$$
R_\infty^{\mathrm{red}}\cong S_\infty.
\tag{6.17}
$$

These are useful one-branch conclusions, but they still illustrate the universal distinction between faithful and nearly faithful actions.

## 7. Descent through augmentation

### 7.1 Underived recovery

Let

$$
\mathfrak a_\infty=(z_1,\ldots,z_q)\subset S_\infty.
\tag{7.1}
$$

The strong control hypotheses identify

$$
R_\infty/\mathfrak a_\infty R_\infty\cong R,
\qquad
M_\infty/\mathfrak a_\infty M_\infty\cong M,
\qquad
A_\infty/\mathfrak a_\infty A_\infty\cong\mathbb T.
\tag{7.2}
$$

The third equality is a separate saturation statement. Without it patching supplies only a natural surjection

$$
A_\infty/\mathfrak a_\infty A_\infty
\twoheadrightarrow\mathbb T.
\tag{7.3}
$$

The quotient in (7.2) is underived tensor product with

$$
S_\infty/\mathfrak a_\infty\cong\mathcal O.
\tag{7.4}
$$

For the module $M_\infty$, exactness is immediate from $S_\infty$-freeness. For the rings, exact recovery is input or must be proved from the construction. One may not infer it solely from the corresponding module identity.

The finite map induced from (6.2) is exactly the canonical comparison

$$
\varphi:R\twoheadrightarrow\mathbb T.
\tag{7.5}
$$

This compatibility is essential: an abstract isomorphism between the two finite rings would not by itself identify the canonical map.

### 7.2 Regular augmentation sequences

Because $M_\infty$ is free over $S_\infty$, the sequence

$$
z_1,\ldots,z_q
\tag{7.6}
$$

is $M_\infty$-regular. Explicitly, for each $i$ multiplication by $z_i$ is injective on

$$
M_\infty/(z_1,\ldots,z_{i-1})M_\infty.
\tag{7.7}
$$

This does not automatically make (7.6) regular on $R_\infty$. It becomes $R_\infty$-regular under any hypothesis proving that $R_\infty$ is finite free, or merely flat, over $S_\infty$. In particular, the near-faithful Cohen--Macaulay argument of Section 4.6 supplies exactly this conclusion:

$$
R_\infty\text{ finite free over }S_\infty
\Longrightarrow
z_1,\ldots,z_q\text{ is }R_\infty\text{-regular}.
\tag{7.8}
$$

The same applies to $A_\infty$ if it is $S_\infty$-flat. Torsion-freeness over the multidimensional ring $S_\infty$ is not enough for flatness and therefore not enough for regularity of the whole sequence.

If (7.6) is regular on a Cohen--Macaulay ring $B$ of dimension $d=q+1$, then

$$
\dim B/\mathfrak a_\infty B=1,
\qquad
\operatorname{depth}B/\mathfrak a_\infty B=1.
\tag{7.9}
$$

Thus the finite-level ring is Cohen--Macaulay of dimension one. If it is finite over the DVR $\mathcal O$, depth one is equivalent to $\mathcal O$-torsion-freeness and hence to finite flatness.

### 7.3 Tor vanishing and exact specialization

The Koszul complex $K_\bullet(z_1,\ldots,z_q;S_\infty)$ resolves $\mathcal O$ over $S_\infty$. Therefore an $S_\infty$-module $N$ satisfies

$$
\operatorname{Tor}^{S_\infty}_i(N,\mathcal O)=0
\quad(i>0)
\tag{7.10}
$$

whenever $N$ is $S_\infty$-flat. Equivalently, for finite $N$, the Koszul homology of (7.6) on $N$ vanishes in positive degrees.

For $M_\infty$ this gives

$$
M_\infty\otimes_{S_\infty}^{\mathbf L}\mathcal O
\simeq M
\tag{7.11}
$$

concentrated in degree zero. For $R_\infty$ and $A_\infty$, the analogous assertion requires their own flatness. Module-side Tor vanishing cannot be transferred to the acting ring without an argument.

Suppose

$$
0\longrightarrow K_\infty\longrightarrow R_\infty
\longrightarrow A_\infty\longrightarrow0
\tag{7.12}
$$

is exact. Tensoring with $\mathcal O$ gives

$$
\operatorname{Tor}^{S_\infty}_1(A_\infty,\mathcal O)
\longrightarrow K_\infty/\mathfrak a_\infty K_\infty
\longrightarrow R
\longrightarrow A_\infty/\mathfrak a_\infty A_\infty
\longrightarrow0.
\tag{7.13}
$$

Thus the specialized kernel is $K_\infty/\mathfrak a_\infty K_\infty$ only when the preceding Tor group vanishes. If $A_\infty$ is flat over $S_\infty$, it does. Formula (7.13) pinpoints why augmentation by zerodivisors can produce an erroneous comparison.

### 7.4 Descent of equality

If the patched map is an isomorphism,

$$
R_\infty\xrightarrow{\sim}A_\infty,
\tag{7.14}
$$

then quotienting both sides by the same ideal gives an isomorphism

$$
R_\infty/\mathfrak a_\infty R_\infty
\xrightarrow{\sim}
A_\infty/\mathfrak a_\infty A_\infty.
\tag{7.15}
$$

No flatness is needed for this elementary descent of an existing isomorphism. With all three control identifications in (7.2), (7.15) is the canonical isomorphism

$$
\boxed{R\xrightarrow{\sim}\mathbb T.}
\tag{7.16}
$$

If only (7.3) is known, (7.14) yields a surjection $R\twoheadrightarrow\mathbb T$, which is exactly where the argument began. Hence Hecke saturation is indispensable for descent by this route.

There is a useful converse under finiteness and Tor hypotheses. Suppose $K_\infty$ in (7.12) is finite over the local ring $S_\infty$, $A_\infty$ is $S_\infty$-flat, and the specialized map is an isomorphism. Then (7.13) gives

$$
K_\infty/\mathfrak a_\infty K_\infty=0.
\tag{7.17}
$$

Since $\mathfrak a_\infty$ lies in the maximal ideal of $S_\infty$, Nakayama's lemma gives $K_\infty=0$. This upward argument is valid only because the kernel is finite and the Tor term vanishes.

### 7.5 Descent of reduced equality

Assume merely that $K_\infty$ is nilpotent. Its image in the finite quotient $R$ is then nilpotent, so the kernel of

$$
R\longrightarrow A_\infty/\mathfrak a_\infty A_\infty
\tag{7.18}
$$

is a nilpotent ideal. Under exact action control, the target is $\mathbb T$, and therefore

$$
\boxed{R^{\mathrm{red}}\xrightarrow{\sim}\mathbb T^{\mathrm{red}}.}
\tag{7.19}
$$

To see surjectivity on reduced quotients, reduce the original surjection. To see injectivity, note that an element of $R$ mapping into the nilradical of $\mathbb T$ has some power in the image of $K_\infty$; a further power is zero. Thus it lies in the nilradical of $R$.

Several upgrades are possible:

- if $R$ is reduced, the finite kernel is zero, so $R\cong\mathbb T$;
- if $\mathbb T$ is reduced but $R$ is not known reduced, (7.19) identifies $\mathbb T$ with $R^{\mathrm{red}}$, not with $R$;
- if a direct finite-level argument proves that $R$ is $\mathcal O$-torsion-free, that still need not kill horizontal nilpotents;
- if $R$ is generically reduced and is a finite flat complete intersection over $\mathcal O$, then $R$ is reduced: a one-dimensional Cohen--Macaulay ring has no embedded associated primes, and a nilpotent would survive at some minimal prime, contrary to generic reducedness.

The last bullet is a genuine reducedness criterion. Torsion-freeness alone is not.

### 7.6 Descent of complete intersections

Suppose $R_\infty$ is an absolute complete intersection and $z_1,\ldots,z_q$ is $R_\infty$-regular. Then a regular presentation for $R_\infty$ can be extended by lifts of the $z_i$, and

$$
R=R_\infty/(z_1,\ldots,z_q)
\tag{7.20}
$$

is again a complete intersection. Its codimension in the same regular ambient ring increases by $q$, while its dimension decreases by $q$.

More explicitly, if

$$
R_\infty=Q/(g_1,\ldots,g_e)
\tag{7.21}
$$

with $Q$ regular and the $g_i$ regular, and if $\widetilde z_i\in Q$ lift $z_i$, then

$$
g_1,\ldots,g_e,
\widetilde z_1,\ldots,\widetilde z_q
\tag{7.22}
$$

is a $Q$-regular sequence. Hence

$$
R\cong Q/(g_1,\ldots,g_e,\widetilde z_1,\ldots,\widetilde z_q)
\tag{7.23}
$$

is a complete intersection of codimension $e+q$.

If some $z_i$ is a zerodivisor, this conclusion fails. A quotient of a complete-intersection ring by an arbitrary element need not be a complete intersection. Therefore near faithfulness, Cohen--Macaulayness, and miracle flatness are not decorative preliminaries: they can be what proves the regularity needed for (7.22).

For a complete-intersection map $R_{\mathrm{loc}}\to R_\infty$, quotienting by a sequence regular relative to the source gives a complete-intersection map to $R$. It does not turn a nonregular base into a regular one. Relative and absolute conclusions remain distinct after descent.

### 7.7 Descent of module freeness

If $M_\infty$ is free of rank $m$ over $R_\infty$, then

$$
M
\cong M_\infty/\mathfrak a_\infty M_\infty
\cong (R_\infty/\mathfrak a_\infty R_\infty)^m
\cong R^m.
\tag{7.24}
$$

No separate Tor calculation is needed once freeness is known. Similarly, if $R\cong\mathbb T$, then $M$ is free of rank $m$ over $\mathbb T$.

Projectivity descends in the same way. Conversely, freeness of $M$ over $R$ does not generally lift to freeness of $M_\infty$ over $R_\infty$. A lifting theorem requires flatness and control of the special fiber, and even then one must know that the relevant idempotents or presentations lift.

The conclusion most often available without multiplicity one is weaker:

$$
M_\infty\text{ is maximal Cohen--Macaulay over }R_\infty
\Longrightarrow
M\text{ is maximal Cohen--Macaulay over }R,
\tag{7.25}
$$

provided the augmentation sequence is regular on both the ring and module. If $R$ is finite flat over $\mathcal O$, this says that $M$ is $\mathcal O$-torsion-free. It still does not say that $M$ is $R$-free.

## 8. Self-duality, Gorenstein rings, and multiplicity one

### 8.1 What a perfect pairing gives

Suppose $M_\infty$ carries a perfect $S_\infty$-bilinear pairing

$$
\langle\ ,\ \rangle_\infty:
M_\infty\times M_\infty\longrightarrow S_\infty
\tag{8.1}
$$

and that the action of $A_\infty$ is self-adjoint:

$$
\langle am,n\rangle_\infty
=\langle m,an\rangle_\infty
\quad
(a\in A_\infty).
\tag{8.2}
$$

This is the untwisted pairing hypothesis. A pairing that is only sesquilinear for diamond inversion must retain that involution in its adjoint and duality statements; it does not become (8.1) over $S_\infty$ merely from a self-identification of the two modules. At augmentation the distinction disappears.

Perfectness means that the adjoint map

$$
M_\infty\xrightarrow{\sim}
\operatorname{Hom}_{S_\infty}(M_\infty,S_\infty)
\tag{8.3}
$$

is an isomorphism. It implies that $M_\infty$ is $S_\infty$-reflexive and, after augmentation, gives a perfect $\mathcal O$-pairing on $M$ whenever specialization is exact.

After extending scalars to $K_\infty=\operatorname{Frac}S_\infty$, distinct character eigenspaces of the commutative algebra $A_{\infty,K}$ are orthogonal. If $e$ is the idempotent of a distinguished generic branch, then

$$
eM_{\infty,K}\perp(1-e)M_{\infty,K}.
\tag{8.4}
$$

The pairing therefore computes the index between the integral branch lattice and its orthogonal projection. This index is the module congruence invariant developed in Chapter 9.

Self-adjointness also embeds $A_\infty$ into its $S_\infty$-dual under additional rank conditions. For instance, choose $m,n\in M_\infty$ and consider

$$
A_\infty\longrightarrow S_\infty,
\qquad
a\longmapsto\langle am,n\rangle_\infty.
\tag{8.5}
$$

Varying $m$ and $n$ produces a map

$$
A_\infty
\longrightarrow
\operatorname{Hom}_{S_\infty}(A_\infty,S_\infty)^{\oplus r^2}.
\tag{8.6}
$$

Faithfulness makes (8.6) injective after a suitable collective choice, but it does not generally identify one copy of the dual with $A_\infty$.

### 8.2 What it does not give

A perfect pairing on $M_\infty$ does not imply any of the following without further hypotheses:

$$
I_\infty=0,
\qquad
M_\infty\text{ is free over }R_\infty,
\qquad
A_\infty\text{ is Gorenstein},
\qquad
\eta(M)=\eta_{A}.
\tag{8.7}
$$

The first failure is immediate: if $R_\infty\twoheadrightarrow A_\infty$ and $A_\infty$ acts on a self-dual module, the pairing sees only the quotient action. Every element of the kernel acts as zero on both sides of (8.1).

The second failure reflects singularity. Duality can make a maximal Cohen--Macaulay module self-dual while leaving it nonfree. The third requires the dualizing module of the algebra itself to be cyclic, not merely a self-dual unrelated representation. The fourth requires the integral lattice on the distinguished generic branch to occur with precisely the saturation dictated by the ring.

Accordingly, pairings enter the proof in two controlled places: they produce determinant or congruence comparisons, and, when the module is already known to be rank one over the acting algebra, they can prove Gorenstein duality. They are not a substitute for support or annihilator arguments.

### 8.3 Multiplicity one as cyclicity

There are two related forms of multiplicity one.

**Generic multiplicity one** says that on the distinguished generic branch

$$
\dim_K M_K[\lambda]=1.
\tag{8.8}
$$

It makes the branch congruence lattice cyclic, so its Fitting ideal and annihilator agree. It does not imply that the whole integral module is cyclic over the algebra.

**Integral multiplicity one** often takes the stronger form that $M$ is generated by one element as a $\mathbb T$-module. If $m$ is a generator, the map

$$
\mathbb T\longrightarrow M,
\qquad t\longmapsto tm
\tag{8.9}
$$

is surjective. Its kernel is the annihilator of $m$. When $M$ is faithful, that kernel is zero, so

$$
M\cong\mathbb T.
\tag{8.10}
$$

The same statement holds at infinite level. A cyclic faithful $A_\infty$-module is free of rank one over $A_\infty$. If in addition $R_\infty=A_\infty$, it is free of rank one over $R_\infty$.

For numerical comparisons, generic rank one must be supplemented by **branch saturation**. If $e_\lambda$ is the generic idempotent, define

$$
M_\lambda=M\cap e_\lambda M_K,
\qquad
P_\lambda=e_\lambda M.
\tag{8.11}
$$

The ring congruence ideal $\eta_{\mathbb T}$ always satisfies

$$
\eta_{\mathbb T}P_\lambda\subseteq M_\lambda.
\tag{8.12}
$$

The exact multiplicity-one lattice condition is

$$
M_\lambda=\eta_{\mathbb T}P_\lambda.
\tag{8.13}
$$

Generic dimension one alone does not force (8.13); the lattice may be nonsaturated by an additional power of the uniformizer.

### 8.4 From rank-one freeness to Gorenstein duality

Let $A$ be a finite flat local $\mathcal O$-algebra. It is Gorenstein over $\mathcal O$ precisely when

$$
A^\vee:=\operatorname{Hom}_{\mathcal O}(A,\mathcal O)
\tag{8.14}
$$

is free of rank one as an $A$-module. Suppose now that $M$ is free of rank one over $A$ and carries a perfect $\mathcal O$-pairing for which $A$ is self-adjoint. Choose an $A$-basis $m_0$ of $M$. The pairing defines

$$
A\longrightarrow A^\vee,
\qquad
a\longmapsto
\bigl(b\longmapsto\langle abm_0,m_0\rangle\bigr).
\tag{8.15}
$$

Self-adjointness makes this map $A$-linear. Perfectness on $M=A m_0$ makes it an isomorphism. Hence $A$ is Gorenstein.

The proof shows exactly where rank-one freeness enters. If $M\cong A^m$ with $m>1$, a perfect pairing identifies a matrix-valued dual object and need not make $A^\vee$ cyclic. If $M$ is merely rank one generically, it may represent a nonprincipal reflexive ideal. If the action is not faithful, the argument proves a Gorenstein statement only for the acting quotient.

At patched level the same reasoning works over $S_\infty$: if $A_\infty$ is finite flat over $S_\infty$, $M_\infty$ is free of rank one over $A_\infty$, and (8.1) is perfect and self-adjoint, then

$$
\operatorname{Hom}_{S_\infty}(A_\infty,S_\infty)
\cong A_\infty.
\tag{8.16}
$$

Regular augmentation then descends the Gorenstein property to the finite ring.

### 8.5 When module freeness follows

Let $B$ be a local Cohen--Macaulay ring and $N$ a maximal Cohen--Macaulay $B$-module. The following are valid sufficient conditions for $N$ to be free.

1. $B$ is regular. Then every finite module has finite projective dimension, and Auslander--Buchsbaum gives projective dimension zero.
2. $N$ is independently known to have finite projective dimension. Again Auslander--Buchsbaum gives zero.
3. $N$ is cyclic and faithful. Then $B\to N$ is an isomorphism.
4. $N$ is projective. Since $B$ is local, it is free.
5. $N$ is represented by an invertible rank-one ideal. An invertible module over a local ring is free of rank one.

A complete-intersection hypothesis on $B$ is absent from this list because it is insufficient. Complete intersections are often singular and possess many nonfree maximal Cohen--Macaulay modules. Nor does a Gorenstein hypothesis suffice: Gorenstein rings are self-dual, but their maximal Cohen--Macaulay category can be highly nontrivial.

In applications the most efficient route to module freeness is frequently integral multiplicity one: first prove $R=\mathbb T$, then prove that the faithful $\mathbb T$-module $M$ is cyclic. The ring comparison and the module-freeness theorem are separate achievements.

### 8.6 Ring equality without module freeness

The support proof of $R_\infty=A_\infty$ needs only faithfulness. A faithful module can have high rank, can fail to be cyclic, and can be a nonfree maximal Cohen--Macaulay module. Thus

$$
R=\mathbb T
\tag{8.17}
$$

can hold even when $M$ is not free over this common ring.

This logical separation is useful. A theorem whose purpose is ring equality should list self-duality or multiplicity one only if it actually uses them to establish faithfulness, reducedness, saturation, or a numerical identity. If support and reducedness already prove faithfulness, no pairing hypothesis belongs in the minimal ring-equality statement. Conversely, a theorem claiming that arithmetic cohomology is free must add one of the criteria in Section 8.5.

## 9. Cotangent spaces, congruence ideals, and the numerical route

### 9.1 The augmented finite-level invariants

Let $B$ be a complete local $\mathcal O$-algebra with an augmentation

$$
\lambda_B:B\twoheadrightarrow\mathcal O,
\qquad
I_B=\ker\lambda_B.
\tag{9.1}
$$

The relative cotangent module at the distinguished point is

$$
\Phi_B=I_B/I_B^2.
\tag{9.2}
$$

It measures first-order deformations of that point relative to $\mathcal O$. The invariant used in the numerical criterion is its full $\mathcal O$-length, not merely the dimension of $\Phi_B/\varpi\Phi_B$ over the residue field.

When $B$ is finite flat over $\mathcal O$ and the distinguished generic point is isolated, define

$$
\eta_B
=\lambda_B\bigl(\operatorname{Ann}_B(I_B)\bigr)
\subseteq\mathcal O,
\qquad
\Psi_B=\mathcal O/\eta_B.
\tag{9.3}
$$

The ideal $\eta_B$ is the congruence ideal and $\Psi_B$ the congruence module. If $\eta_B=(\varpi^n)$, then

$$
\operatorname{length}_{\mathcal O}\Psi_B=n.
\tag{9.4}
$$

A smaller congruence ideal corresponds to a larger congruence module. This reversal explains the direction of all ideal inclusions below.

For a finite-length $\mathcal O$-module $N$,

$$
\operatorname{Fitt}_{\mathcal O}^0(N)
=(\varpi^{\operatorname{length}_{\mathcal O}N}).
\tag{9.5}
$$

Consequently numerical length statements can be written as principal-ideal comparisons without choosing generators.

### 9.2 The direction of the numerical inequality

For a finite flat complete local augmented $\mathcal O$-algebra $B$ with $\Phi_B$ of finite length, the intrinsic inequality is

$$
\operatorname{length}_{\mathcal O}\Phi_B
\ge
\operatorname{length}_{\mathcal O}\Psi_B.
\tag{9.6}
$$

Equality holds precisely when $B$ is a complete intersection. In terms of ideals,

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_B)
\subseteq\eta_B,
\tag{9.7}
$$

because larger length means a smaller power-of-$\varpi$ ideal.

Now let

$$
f:R\twoheadrightarrow\mathbb T
\tag{9.8}
$$

be compatible with augmentations. The desired numerical input is the opposite-looking estimate

$$
\operatorname{length}\Phi_R
\le
\operatorname{length}\Psi_{\mathbb T},
\tag{9.9}
$$

or equivalently

$$
\eta_{\mathbb T}
\subseteq
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R).
\tag{9.10}
$$

Since $\Phi_{\mathbb T}$ is a quotient of $\Phi_R$, the chain is

$$
\operatorname{length}\Phi_R
\ge
\operatorname{length}\Phi_{\mathbb T}
\ge
\operatorname{length}\Psi_{\mathbb T}.
\tag{9.11}
$$

Combining (9.9) and (9.11) forces equality everywhere. The difficulty is proving (9.9). It is a theorem extracted from the patched module and its pairing, not a harmless numerical assumption.

### 9.3 The module congruence lattice

Assume that $\mathbb T$ is finite flat over $\mathcal O$, that the generic point selected by the augmentation is an isolated factor of $\mathbb T_K$, that $M$ is finite free over $\mathcal O$, and that $M$ carries a faithful self-adjoint $\mathbb T$-action and a perfect pairing. Let $K$ be the fraction field of $\mathcal O$, and let $e_\lambda$ be the idempotent of that distinguished factor of $\mathbb T_K$.

Define

$$
M_\lambda=M\cap e_\lambda M_K,
\qquad
M^c=M\cap(1-e_\lambda)M_K,
\tag{9.12}
$$

and

$$
\Psi(M)=M/(M_\lambda+M^c).
\tag{9.13}
$$

Projection to $e_\lambda M_K$ gives

$$
\Psi(M)\cong P_\lambda/M_\lambda,
\qquad
P_\lambda=e_\lambda M.
\tag{9.14}
$$

The pairing identifies $P_\lambda$ with the dual lattice $M_\lambda^\vee$, so

$$
\Psi(M)\cong M_\lambda^\vee/M_\lambda.
\tag{9.15}
$$

Set

$$
\eta(M)=\operatorname{Fitt}_{\mathcal O}^0\bigl(\Psi(M)\bigr).
\tag{9.16}
$$

The ring congruence ideal always clears the branch idempotent, yielding

$$
\eta_{\mathbb T}P_\lambda\subseteq M_\lambda.
\tag{9.17}
$$

If $M_\lambda$ has rank one, then $P_\lambda/M_\lambda$ is cyclic and (9.17) gives

$$
\eta_{\mathbb T}\subseteq\eta(M).
\tag{9.18}
$$

Equality requires branch saturation (8.13). Neither faithful action nor a perfect pairing alone supplies it.

### 9.4 A common-determinant comparison

We now state the precise bridge from patching to (9.9). It is designed to be checked from the finite free resolutions and pairings produced in an application.

First isolate the elementary determinant statement. Let $U,V,L,L'$ be finite free $\mathcal O$-modules, with $\operatorname{rank}U=\operatorname{rank}V$ and $\operatorname{rank}L=\operatorname{rank}L'$. Let

$$
D:U\longrightarrow V,
\qquad
j:L\longrightarrow L'
$$

have finite cokernels. Suppose there are determinant-line isomorphisms

$$
\alpha:\det U\xrightarrow{\sim}\det L,
\qquad
\beta:\det V\xrightarrow{\sim}\det L'
$$

and a unit $u\in\mathcal O^\times$ such that

$$
\beta\circ\det(D)
=u\,\det(j)\circ\alpha.
$$

Choosing bases turns both top exterior maps into one-by-one matrices. The displayed compatibility says that their entries differ by a unit. Since a square presentation has zeroth Fitting ideal generated by its determinant,

$$
\operatorname{Fitt}_{\mathcal O}^0(\operatorname{coker}D)=

\operatorname{Fitt}_{\mathcal O}^0(\operatorname{coker}j).
$$

This determinant lemma compares maps and lattices, not lengths. Its hypotheses can be verified before either cokernel is measured.

> **Common-determinant hypothesis.** After exact augmentation, there are finite free $\mathcal O$-modules $U$ and $V$ of the same rank and a map $D:U\to V$ with finite cokernel such that:
>
> 1. $\operatorname{coker}D\cong\Phi_R$;
> 2. the patched pairing supplies determinant-line isomorphisms satisfying the compatibility in the determinant lemma for $D$ and the lattice inclusion $M_\lambda\hookrightarrow M_\lambda^\vee$.

Choose bases of $U$ and $V$. Because $D$ is square,

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)
=(\det D).
\tag{9.19}
$$

Choose dual bases for the two branch lattices. The determinant of

$$
M_\lambda\hookrightarrow M_\lambda^\vee
\tag{9.20}
$$

generates the Fitting ideal of its cokernel. By (9.15), that cokernel is $\Psi(M)$, so

$$
\eta(M)
=\operatorname{Fitt}_{\mathcal O}^0(\Psi(M))
=(\det D).
\tag{9.21}
$$

Therefore the common determinant proves

$$
\boxed{
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)=\eta(M).}
\tag{9.22}
$$

This is not a restatement of the desired numerical equality. The first side is computed by the linearized global relation complex; the second by the self-dual integral lattice. The patched construction connects them because its relation complex and its dual module complex are paired, and exact specialization prevents extra homology from changing either determinant.

Concretely, the required verification begins with a finite free relation complex whose degree-zero specialization presents the global conormal module. The perfect pairing identifies its dual complex with the complex controlling the orthogonal branch lattice. Compatibility of the local and global pairings makes the two top exterior maps commute up to a unit. Finally, regular augmentation, or explicit vanishing of the relevant positive Tor groups, ensures that specialization has introduced no extra homology. These are chain-level assertions; none mentions the kernel of $R\to\mathbb T$.

If the augmented relation complex is not square, the maximal minors rather than a single determinant generate $\operatorname{Fitt}^0(\Phi_R)$. Then the required input is an equality of determinant ideals, proved by comparing the appropriate top exterior maps. Choosing one convenient minor without proving that it generates the Fitting ideal is insufficient.

### 9.5 The module-derived numerical equality

Assume the common-determinant hypothesis and the branch-saturation equality

$$
M_\lambda=\eta_{\mathbb T}P_\lambda.
\tag{9.23}
$$

In generic rank one, (9.23) gives

$$
\eta(M)=\eta_{\mathbb T}.
\tag{9.24}
$$

Combining (9.22) and (9.24) yields

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)
=\eta_{\mathbb T},
\tag{9.25}
$$

and hence

$$
\operatorname{length}\Phi_R
=\operatorname{length}\Psi_{\mathbb T}.
\tag{9.26}
$$

Thus the numerical equality has been derived from four verifiable pieces:

1. exact specialization of the patched relation complex;
2. a perfect self-adjoint pairing;
3. equality of the two determinant lines;
4. rank-one branch saturation.

If the determinant comparison provides only

$$
\eta_{\mathbb T}
\subseteq\operatorname{Fitt}_{\mathcal O}^0(\Phi_R),
\tag{9.27}
$$

that is already enough for the Wiles--Lenstra criterion. Equality then follows as a conclusion. If instead one knows only the general inclusion (9.18), its direction does not imply (9.27): both ideals sit on the same side of $\eta(M)$. The common determinant is the missing connection to the cotangent module.

For generic multiplicity $s>1$, the determinant of $s$ identical congruence lattices is $\eta_{\mathbb T}^s$. Dividing its length by $s$ is justified only if an actual direct-sum or tensor-product decomposition proves that repetition. An arbitrary rank-$s$ lattice can have elementary divisors of different sizes, so a scalar “multiplicity correction” cannot be inserted by convention.

### 9.6 The Wiles--Lenstra conclusion

We record the exact numerical criterion in the form used here.

> **Numerical isomorphism theorem.** Let $R$ and $\mathbb T$ be complete Noetherian local $\mathcal O$-algebras with compatible augmentations. Suppose:
>
> 1. $R\twoheadrightarrow\mathbb T$ is surjective;
> 2. $\mathbb T$ is finite flat over $\mathcal O$;
> 3. $\Phi_R$ has finite $\mathcal O$-length;
> 4. $\operatorname{length}\Phi_R\le\operatorname{length}\Psi_{\mathbb T}$.
>
> Then $R\to\mathbb T$ is an isomorphism, both rings are finite flat complete intersections over $\mathcal O$, and
>
> $$
>
> \operatorname{length}\Phi_R
> =\operatorname{length}\Phi_{\mathbb T}
> =\operatorname{length}\Psi_{\mathbb T}.
> \tag{9.28}
> $$

No prior finite-flat or complete-intersection hypothesis on $R$ occurs here. The numerical inequality forces those properties. Conversely, one must not invoke the theorem if $\mathbb T$ has unremoved $\mathcal O$-torsion, if the augmentations choose different points, or if $\Phi_R$ is not finite length.

Under the hypotheses of Section 9.5, condition 4 follows from (9.26). The result is therefore a second route to

$$
R\xrightarrow{\sim}\mathbb T,
\tag{9.29}
$$

one which simultaneously proves finite flatness and the complete-intersection property at finite level.

### 9.7 The numerical and support routes compared

The support route works at infinite level:

$$
\text{component coverage}
+\text{nilpotent-killing input}
\Longrightarrow
R_\infty=A_\infty
\Longrightarrow R=\mathbb T.
\tag{9.30}
$$

The numerical route works at the distinguished finite-level branch:

$$
\text{common determinant}
+\text{branch saturation}
\Longrightarrow
\operatorname{length}\Phi_R
\le\operatorname{length}\Psi_{\mathbb T}
\Longrightarrow R=\mathbb T.
\tag{9.31}
$$

Neither route subsumes the other. Component coverage can prove equality without multiplicity one or a pairing. The numerical route can kill a kernel even when a global reducedness theorem for $R_\infty$ is unavailable. Conversely, near faithfulness alone yields only reduced equality, while the exact numerical criterion can see and eliminate nilpotent thickenings at the chosen finite point.

When both routes are available, they audit one another. The support route predicts the absence of missing components; the numerical route verifies that the distinguished branch has no excess cotangent defect. Agreement of their complete-intersection conclusions is a strong consistency check, but neither conclusion should be inserted as a premise of the other.

## 10. Framed and unframed comparisons

### 10.1 The formally smooth frame extension

Framed deformation problems retain choices of bases at specified places. Under the usual representability hypotheses, forgetting those choices is formally smooth. Abstractly, suppose there is an actual identification

$$
R_\infty^{\square}
\cong R_\infty[[u_1,\ldots,u_f]]
\tag{10.1}
$$

compatible with the corresponding action and module:

$$
M_\infty^{\square}
\cong M_\infty\widehat\otimes_{R_\infty}R_\infty^{\square},
\qquad
A_\infty^{\square}
\cong A_\infty[[u_1,\ldots,u_f]].
\tag{10.2}
$$

The number $f$ is the relative framing dimension. It depends on the chosen framing convention and on scalar automorphisms of the residual object. It must be computed, not guessed from the number of framed places.

The variables $u_i$ are formally smooth variables: they add dimension but no relations. Therefore

$$
\dim R_\infty^{\square}=\dim R_\infty+f,
\qquad
\operatorname{depth}M_\infty^{\square}
=\operatorname{depth}M_\infty+f.
\tag{10.3}
$$

Any relation budget stated in the framed setting must add the same $f$ to the presentation dimension and leave the relation codimension unchanged.

### 10.2 Removing frame variables

The sequence $u_1,\ldots,u_f$ is regular on a power-series ring and on the extended module in (10.2). Quotienting gives

$$
R_\infty^{\square}/(u_1,\ldots,u_f)
\cong R_\infty,
\quad
A_\infty^{\square}/(u_1,\ldots,u_f)
\cong A_\infty,
\tag{10.4}
$$

and similarly for $M_\infty$. Hence an isomorphism

$$
R_\infty^{\square}\xrightarrow{\sim}A_\infty^{\square}
\tag{10.5}
$$

descends immediately to the unframed comparison.

Conversely, an unframed isomorphism extends to a framed isomorphism by applying the same power-series functor. Complete-intersection and Cohen--Macaulay properties are preserved in both directions under adjoining variables and quotienting by those regular variables.

If one has only a formally smooth map rather than a chosen power-series identification, the same assertions hold after choosing parameters, but the parameters and the resulting isomorphism are noncanonical. The ring-theoretic property and the unframed comparison remain canonical.

### 10.3 Faithfulness and components under power series

For a finite $R_\infty$-module $M_\infty$,

$$
\operatorname{Ann}_{R_\infty[[u]]}
\bigl(M_\infty\widehat\otimes_{R_\infty}R_\infty[[u]]\bigr)
=I_\infty R_\infty[[u]].
\tag{10.6}
$$

This follows from faithful flatness of the power-series extension. Thus faithful and nearly faithful actions ascend and descend through frames.

Minimal primes correspond by

$$
\mathfrak p
\longleftrightarrow
\mathfrak pR_\infty[[u]],
\tag{10.7}
$$

and

$$
V(\mathfrak pR_\infty[[u]])
\cong
\operatorname{Spec}\bigl((R_\infty/\mathfrak p)[[u_1,\ldots,u_f]]\bigr)
\tag{10.8}
$$

at the level of prime topology over the base. Component coverage is therefore unchanged. Reducedness also ascends and descends under a power-series extension.

### 10.4 Padding variables are not frames

Presentation padding introduces variables to balance generators and relations or to place finite-level presentations in a fixed ambient ring. Auxiliary variables encode the inverse limit of diamond operators. Frame variables encode choices of basis. Although all may appear as power-series symbols, their control maps differ.

In particular:

- frame variables may be removed by a formally smooth quotient as in (10.4);
- auxiliary variables are removed by the augmentation ideal $\mathfrak a_\infty$ and require the control theorems of Chapter 7;
- padding variables may be paired with redundant relations and can be removed only after verifying the relevant regular sequence or presentation equivalence.

Treating every added variable as a frame can corrupt both dimension and codimension. The ledger must record each family separately and state which quotient recovers the intended finite problem.

## 11. Determinants and local-condition compatibility

### 11.1 Fixed determinant throughout the comparison

Let the residual global object have determinant $\overline\psi$, and fix a lift

$$
\psi:G\longrightarrow\mathcal O^\times.
\tag{11.1}
$$

The global ring $R$, every auxiliary ring $R_N$, the local base $R_{\mathrm{loc}}$, the presentation ring $P_\infty$, and the patched quotient $R_\infty$ must all belong to the fixed-$\psi$ deformation problem. The arithmetic representation valued in $\mathbb T$ must have the same determinant. Only then does the canonical map

$$
R\longrightarrow\mathbb T
\tag{11.2}
$$

exist in the stated category.

Allowing determinant variation adds deformation directions, usually represented by character variables. One cannot patch in that larger category and then silently quote a dimension formula computed with fixed determinant. To pass from variable to fixed determinant, one must quotient by the determinant equations and verify that they form the expected regular sequence, or redo the dimension ledger in the larger category.

The fixed determinant also constrains auxiliary local choices. The two eigencharacters introduced at a Taylor--Wiles place must have product equal to the prescribed local determinant. Thus the diamond variable records a ratio or one character subject to a product relation, not two independent characters.

### 11.2 Old local components

At each original ramified place $v$, choose a local deformation quotient

$$
R_v^{\mathrm{cond}}
\tag{11.3}
$$

encoding the desired inertial type, weight, monodromy condition, ordinarity condition, or selected irreducible components. The local base is a completed tensor product of these quotients, together with any framed factors:

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v\in S}R_v^{\mathrm{cond}}.
\tag{11.4}
$$

All dimension and Cohen--Macaulay hypotheses concern this chosen $R_{\mathrm{loc}}$, not the unrestricted local deformation rings. If a local quotient is a union of components, component coverage at global level must be compatible with that union.

The finite-level arithmetic representation verifies the local conditions through local--global compatibility. Algebraically, this gives factorizations

$$
R_v^{\square}\longrightarrow R_v^{\mathrm{cond}}
\longrightarrow\mathbb T_N.
\tag{11.5}
$$

The arithmetic levels need not admit transition maps. To make these factorizations survive patching, their reductions must instead be included among the marked finite shadows used in the coherent diagonal construction. Compatibility of those shadows and closedness of the defining ideals then force the limiting action to factor through the same local quotients. This is an input to the patching datum, not a formal consequence of having maps at every unrelated auxiliary level.

### 11.3 Auxiliary local branches

At an auxiliary place, the local deformation problem is enlarged in a controlled way. One selects an ordered or otherwise distinguished branch on which the tame character varies through a finite group $\Delta_N$. The group ring acts on $M_N$, and augmentation of that group ring returns the original local condition.

The abstract compatibility required is a Cartesian recovery statement at the level of represented conditions:

$$
R_N/\mathfrak a_N R_N\cong R,
\tag{11.6}
$$

not merely a bijection on closed points. Nilpotent tangent directions must also specialize correctly. At the patched level this becomes the first equality in (7.2).

If the auxiliary local ring has several branches, the finite module may be supported on only the chosen eigenvalue branch. That is legitimate provided $R_N$ and ultimately $R_\infty$ are defined using the same branch. If the ring retains additional branches, a separate component-coverage or component-hopping theorem is needed.

### 11.4 Why the quotient still represents the intended problem

The map from the universal global ring to the action algebra factors through the prescribed quotient because the representation carried by the module satisfies:

$$
\begin{array}{ll}
\text{(i)}&\det=\psi,\\
\text{(ii)}&\text{the condition }R_v^{\mathrm{cond}}\text{ at every old place},\\
\text{(iii)}&\text{the selected auxiliary branch at every new place},\\
\text{(iv)}&\text{the fixed ramification condition outside the allowed set}.
\end{array}
\tag{11.7}
$$

These properties are stable under passage to finite quotients and inverse limits. Therefore $R_\infty\to A_\infty$ is a comparison for the same deformation problem that appears at finite level.

Faithfulness cannot repair a mismatch here. If the action algebra represents a smaller local condition than the source, its kernel correctly records that discrepancy. Proving the kernel zero would then assert a false equivalence of deformation problems. The local-condition ledger is consequently prior to every support argument.

## 12. Minimal and nonminimal abstract instances

### 12.1 The minimal pattern

In a minimal problem, the allowed ramification and local types are exactly those forced by the residual object and the chosen determinant. The local base $R_{\mathrm{loc}}^{\min}$ is often irreducible or has a distinguished component known to contain every relevant point. The abstract input takes the form

$$
P_\infty^{\min}
=R_{\mathrm{loc}}^{\min}[[z_1,\ldots,z_q,x_1,\ldots,x_g]],
\qquad
R_\infty^{\min}=P_\infty^{\min}/(f_1,\ldots,f_b).
\tag{12.1}
$$

If the local base is regular and the relation ideal has actual height equal to its number of minimal generators, $R_\infty^{\min}$ is a complete intersection. If it is also reduced, the patched module covers every component, and exact action control holds, the support route yields

$$
R^{\min}\cong\mathbb T^{\min}.
\tag{12.2}
$$

Nothing in the abstract proof requires the word “minimal.” What matters is that the local-condition, dimension, coverage, reducedness, and control hypotheses are often easiest to verify in this case.

### 12.2 The nonminimal pattern

A nonminimal problem permits additional ramification or a larger local type at selected places. Its local base changes to

$$
R_{\mathrm{loc}}^{\mathrm{nonmin}}
=R_{\mathrm{loc}}^{\min}\widehat\otimes
\widehat\bigotimes_{v\in S_{\mathrm{new}}}R_v^{\mathrm{new}}.
\tag{12.3}
$$

The arithmetic module also changes. Old/new decompositions, degeneracy maps, or local projectors may be needed to isolate the part on which the intended deformation quotient acts. At the abstract level these facts enter as:

$$
M_\infty^{\mathrm{nonmin}}
\text{ is finite free over }S_\infty,
\tag{12.4}
$$

exact augmentation control, and a component statement for $R_\infty^{\mathrm{nonmin}}$.

The same commutative-algebra proof then applies. The difference is not a new $R=T$ argument but a different verification of its ledger. In particular, nonminimality does not authorize dropping component coverage merely because a minimal theorem is already known.

### 12.3 Changing the local base

Suppose a change of local condition induces

$$
R_{\mathrm{loc}}^{(1)}\longrightarrow R_{\mathrm{loc}}^{(2)}.
\tag{12.5}
$$

Dimension changes must be tracked through the presentation source. If the new local condition adds $a$ dimensions and $c$ independent equations, then the expected dimension changes by $a-c$. The auxiliary number $q$ and relation budget $b$ may also change because the global dual Selmer group changes.

A complete-intersection map in (12.5) can be composed with the patched complete-intersection map, adding codimensions. An arbitrary quotient cannot. If the kernel in (12.5) is generated by zerodivisors, Cohen--Macaulayness and complete-intersection structure may be lost before patching begins.

Likewise, reducedness of $R_{\mathrm{loc}}^{(1)}$ need not pass to $R_{\mathrm{loc}}^{(2)}$, and irreducible components can split or merge. Every nonminimal application must therefore restate, rather than inherit by name, the local dimension and component hypotheses.

### 12.4 Component hopping as a named theorem

Assume the patched module is known to meet a subset $\Sigma_{\mathrm{aut}}$ of the minimal primes of $R_\infty$. A **component-hopping theorem** is an independent assertion that

$$
\Sigma_{\mathrm{aut}}=\operatorname{Min}R_\infty
\tag{12.6}
$$

or, more generally, that it equals the set of components allowed by a stated local equivalence relation. Its proof may use congruences between local types, connectedness of generic fibers, or propagation of nonvanishing. None of those mechanisms belongs to the abstract comparison.

Once (12.6) is supplied, Section 4.3 proves the sharp dimension and Section 5.4 proves near faithfulness. If (12.6) is unavailable, the honest conclusion is the componentwise equality of Section 5.6. It is misleading to call the ring equidimensional and then act as though all its components were automatically arithmetic.

Thus minimal and nonminimal theorems have the same final form:

$$
\text{verified ledger}
+\text{verified component statement}
\Longrightarrow
\text{the appropriate comparison theorem}.
\tag{12.7}
$$

Their difference lies entirely in how those inputs are established.

## 13. Canonicity and independence of choices

### 13.1 What can depend on choices

The patched construction can depend on:

- the sequence of Taylor--Wiles sets;
- choices of generators of the finite diamond groups;
- presentations of the finite-level deformation rings;
- frame and padding variables;
- bases of finite free modules;
- identifications of group rings with truncated power-series rings;
- the diagonal subsequence used to pass to a limit.

Accordingly, the rings $P_\infty$, $R_\infty$, and $A_\infty$ and the module $M_\infty$ need not carry canonical identifications between two successful constructions. Even their displayed variables and relation generators have no intrinsic meaning.

The properties used in the comparison are invariant under coordinate changes and pro-isomorphisms: dimension, depth, being Cohen--Macaulay, being a complete intersection, support on all components, reducedness, faithfulness, and exact augmentation. A genuinely different diagonal need not be identified with the first one and must reverify these hypotheses. A proof may use coordinates to verify them, but its finite-level conclusion cannot depend on those coordinates.

### 13.2 What is canonical

At finite level the global deformation problem defines $R$, the chosen arithmetic action defines $\mathbb T$, and the universal arithmetic representation defines a specific map

$$
\varphi:R\twoheadrightarrow\mathbb T.
\tag{13.1}
$$

This map is canonical relative to the fixed determinant, local conditions, and localization at the chosen maximal ideal. The word “canonical” does not mean that $R$ or $\mathbb T$ are independent of those initial choices; it means that once the problem is fixed, no patching choices enter (13.1).

Exact control requires a commutative diagram

$$
\begin{array}{ccc}
R_\infty&\twoheadrightarrow&A_\infty\\
\downarrow&&\downarrow\\
R&\xrightarrow{\varphi}&\mathbb T,
\end{array}
\tag{13.2}
$$

whose vertical arrows are augmentation quotients. Thus the map obtained by descending the patched action is not merely isomorphic to $\varphi$; it is $\varphi$.

### 13.3 Why one successful patch proves a choice-independent result

Suppose one patched system proves

$$
R_\infty\xrightarrow{\sim}A_\infty.
\tag{13.3}
$$

Taking augmentation quotients in (13.2) gives that the canonical map $\varphi$ is bijective. A bijective ring map has a unique inverse as a set map and as a ring homomorphism. Hence

$$
\varphi^{-1}:\mathbb T\longrightarrow R
\tag{13.4}
$$

is determined without reference to the chosen patched system.

Now construct a second patched system. It may not be isomorphic to the first, but it descends to the same map $\varphi$. Since (13.1) is already known to be an isomorphism, the finite conclusion obtained from the second system, if its hypotheses are verified, must be the same conclusion. There is no need to compare the two infinite rings.

This proves choice independence in the strongest useful sense:

$$
\text{existence of one valid witness above }\varphi
\Longrightarrow
\varphi\text{ is canonically an isomorphism}.
\tag{13.5}
$$

The statement is existential at infinite level and intrinsic at finite level.

### 13.4 Reduced and componentwise independence

If a patch proves only

$$
R^{\mathrm{red}}\xrightarrow{\sim}\mathbb T^{\mathrm{red}},
\tag{13.6}
$$

the induced map is again the reduction of the canonical $\varphi$, so it is choice-independent. What may depend on the patch is a description of which infinite components were seen.

For a componentwise theorem, independence requires an intrinsic finite-level specification of the selected quotient: for example, a local type, a union of generic components characterized by deformation conditions, or the radical of the kernel of the canonical action. If one defines the quotient only as

$$
R_\infty/(P_\Sigma+\mathfrak a_\infty),
\tag{13.7}
$$

then it is tied to that patch until shown to equal the intrinsic finite quotient. Once such an equality is proved, the componentwise comparison is canonical for the same reason as (13.5).

The lesson is not that patched choices are harmless in every intermediate claim. It is that they are harmless for the final comparison precisely because exact control identifies the descended arrow with a map defined before patching.

## 14. Failure modes and diagnostic counterexamples

Each example below violates one tempting inference while preserving as many neighboring hypotheses as possible. The examples are complete local rings, so no pathology comes from lack of completion.

### 14.1 A module on one component

Let $k$ be a field and set

$$
B=k[[x,y]]/(xy),
\qquad
N=B/(x)\cong k[[y]].
\tag{14.1}
$$

The ring $B$ is a one-dimensional reduced hypersurface with two minimal primes $(x)$ and $(y)$. The module $N$ has

$$
\operatorname{Ann}_B(N)=(x),
\qquad
\operatorname{Supp}_B(N)=V(x).
\tag{14.2}
$$

Multiplication by $y$ is injective on $N$, so

$$
\operatorname{depth}_B N=1=\dim B.
\tag{14.3}
$$

Thus $N$ is maximal Cohen--Macaulay, and its support has the full ambient dimension, but it misses the component $V(y)$. It is not faithful. This disproves both “maximal Cohen--Macaulay implies full support” and “a support of full dimension is the whole spectrum.”

### 14.2 A nilpotent thickening invisible to support

Let

$$
B=k[[t,\epsilon]]/(\epsilon^2),
\qquad
N=B/(\epsilon)\cong k[[t]].
\tag{14.4}
$$

There is only one minimal prime, $(\epsilon)$, and

$$
\operatorname{Supp}_B(N)=\operatorname{Spec}B.
\tag{14.5}
$$

Nevertheless

$$
\operatorname{Ann}_B(N)=(\epsilon)\ne0,
\qquad
(\epsilon)^2=0.
\tag{14.6}
$$

The module is nearly faithful but not faithful. It is also maximal Cohen--Macaulay because $t$ is regular on both $B$ and $N$. This is the basic reason that full support proves only equality of reduced quotients.

### 14.3 Dimension equality without faithfulness

Return to (14.1) and consider the surjection

$$
B\twoheadrightarrow B/(x)\cong k[[y]].
\tag{14.7}
$$

Both rings have dimension one, and the target acts faithfully on itself. Yet the map has kernel $(x)$. Even the source is reduced, equidimensional, and a complete intersection. The missing hypothesis is coverage of the second component.

Alternatively, (14.4) gives equal-dimensional source and target with full topological support; there the missing hypothesis is reducedness. Together the two examples show that component loss and nilpotent loss are independent defects.

### 14.4 A zerodivisor augmentation variable

Let

$$
B=k[[x,y]]/(xy).
\tag{14.8}
$$

This is a one-dimensional complete intersection. The element $x^2$ is nonzero but is a zerodivisor because

$$
y x^2=x(xy)=0.
\tag{14.9}
$$

The quotient is

$$
B/(x^2)
\cong k[[x,y]]/(xy,x^2).
\tag{14.10}
$$

The ideal $(xy,x^2)$ has height one but needs two generators. In the regular local ring $k[[x,y]]$, a codimension-one complete-intersection ideal would be principal. Hence (14.10) is not a complete intersection. Its dimension also remains one instead of falling by one.

This example disproves descent of complete-intersection structure through an arbitrary augmentation quotient. Regularity of the augmentation sequence is essential.

### 14.5 An equal-dimensional proper quotient

The map

$$
k[[x,y]]/(xy)\twoheadrightarrow k[[x]],
\qquad y\longmapsto0,
\tag{14.11}
$$

is a surjection between reduced complete local rings of equal dimension one and is not an isomorphism. Its kernel is the minimal prime $(y)$.

This example isolates a purely ring-theoretic error: surjectivity plus equality of Krull dimensions does not imply injectivity. Neither Noetherianity, completeness, reducedness, equidimensionality, nor the complete-intersection property repairs the inference. One needs generic injectivity on every component, rank equality with torsion control, a numerical criterion, or another genuine kernel argument.

### 14.6 A maximal Cohen--Macaulay nonfree module

Again take $B=k[[x,y]]/(xy)$ and $N=B/(x)$. Equation (14.3) shows that $N$ is maximal Cohen--Macaulay. It is not free over $B$: a nonzero free module has zero annihilator, whereas

$$
\operatorname{Ann}_B(N)=(x).
\tag{14.12}
$$

Even a faithful maximal Cohen--Macaulay module need not be free. For example,

$$
N'=B/(x)\oplus B/(y)
\tag{14.13}
$$

has annihilator

$$
(x)\cap(y)=(xy)=0\quad\text{in }B,
\tag{14.14}
$$

so it is faithful and maximal Cohen--Macaulay. Its generic rank is one on each component, so if it were free it would have to be free of rank one. But

$$
\dim_k N'/\mathfrak m_BN'=2,
$$

whereas a free rank-one module over the local ring $B$ needs one generator. Thus faithfulness, maximal depth, and a hypersurface source still do not imply module freeness.

### 14.7 A torsion-free target that does not kill nilpotents

Let $\mathcal O$ be a complete DVR and put

$$
B=\mathcal O[\epsilon]/(\epsilon^2),
\qquad
C=\mathcal O,
\tag{14.15}
$$

with the surjection $B\to C$ sending $\epsilon$ to zero. Both $B$ and $C$ are finite free over $\mathcal O$, and both have dimension one. The target is reduced and torsion-free, but the kernel $(\epsilon)$ is nonzero and nilpotent.

Thus torsion-freeness or reducedness of the target cannot upgrade near faithfulness of the source action. One needs reducedness of the source, generic reducedness plus an appropriate Cohen--Macaulay criterion, or direct control of the kernel.

### 14.8 A false numerical comparison

Let $\mathcal O$ have uniformizer $\varpi$ and define

$$
R=\mathcal O[X]/(X(X-\varpi)),
\qquad
T=R/(\varpi X)
\cong\mathcal O[X]/(\varpi X,X^2),
\tag{14.16}
$$

with augmentation $X\mapsto0$. The map is surjective and

$$
\Phi_R\cong k,
\qquad
\Phi_T\cong k.
\tag{14.17}
$$

For $T$, the augmentation ideal is $(X)$ and both $\varpi$ and $X$ annihilate it. Therefore

$$
\eta_T=(\varpi),
\qquad
\Psi_T\cong k.
\tag{14.18}
$$

The apparent numerical equality

$$
\operatorname{length}\Phi_R
=\operatorname{length}\Psi_T=1
\tag{14.19}
$$

holds, but the kernel $(\varpi X)=(X^2)$ is nonzero. There is no contradiction with the numerical theorem because $T$ is not $\mathcal O$-flat: $X$ is nonzero $\varpi$-torsion. The target-flatness hypothesis prevents precisely this invisible vertical direction.

The example also shows why a tangent-length equality is not self-authenticating. Before applying a numerical criterion one must verify surjectivity, compatible augmentations, finite flatness of the target, finite cotangent length, and the origin and direction of the numerical inequality.

## 15. A clean theorem instance

### 15.1 The one-branch complete-intersection model

This model displays every commutative-algebra step without suppressing components or nilpotents. Let $\mathcal O$ be a complete DVR with uniformizer $\varpi$, fix an integer $b\ge1$, and put

$$
S_\infty=\mathcal O[[z_1,\ldots,z_b]],
\qquad
d=b+1,
\tag{15.1}
$$

$$
P_\infty=S_\infty[[x_1,\ldots,x_b]],
\tag{15.2}
$$

and

$$
R_\infty
=P_\infty/
\bigl(x_i(x_i-(\varpi+z_i)):1\le i\le b\bigr).
\tag{15.3}
$$

Take

$$
M_\infty=R_\infty,
\qquad
A_\infty=R_\infty
\tag{15.4}
$$

with the regular representation. Let $\mathfrak a_\infty=(z_1,\ldots,z_b)$.

Every element of $R_\infty$ has a unique expression

$$
\sum_{E\subseteq\{1,\ldots,b\}}a_E x_E,
\qquad
x_E=\prod_{i\in E}x_i,
\qquad
a_E\in S_\infty.
\tag{15.5}
$$

Indeed, each monic quadratic relation reduces the exponent of $x_i$ to at most one, and successive division proves uniqueness. Hence

$$
R_\infty\cong S_\infty^{\oplus 2^b}
\tag{15.6}
$$

as an $S_\infty$-module.

### 15.2 Verification of every hypothesis

The ring $P_\infty$ is regular local and

$$
\dim P_\infty=(b+1)+b=d+b.
\tag{15.7}
$$

The $b$ displayed monic equations form a regular sequence. One way to see this is inductive: after quotienting by the first $i-1$ equations, the ring is free over the remaining power-series ring in $x_i,\ldots,x_b$; the next monic polynomial is a nonzerodivisor. Thus

$$
\dim R_\infty=d
\tag{15.8}
$$

and $R_\infty$ is a complete intersection.

Equation (15.6) proves all auxiliary assertions at once: $M_\infty$ is finite free of positive rank over $S_\infty$, $R_\infty$ is finite flat over $S_\infty$, and $z_1,\ldots,z_b$ is regular on both ring and module. The regular action is faithful, so

$$
\operatorname{Ann}_{R_\infty}M_\infty=0.
\tag{15.9}
$$

Every component is therefore covered.

The ring is reduced as well. Let $K_\infty$ be the fraction field of $S_\infty$. Each $\varpi+z_i$ is nonzero, and

$$
K_\infty[x_i]/(x_i(x_i-(\varpi+z_i)))
\cong K_\infty\times K_\infty.
\tag{15.10}
$$

Tensoring the factors gives

$$
R_\infty\otimes_{S_\infty}K_\infty
\cong K_\infty^{2^b},
\tag{15.11}
$$

which is reduced. Since $R_\infty$ is $S_\infty$-torsion-free, it injects into (15.11), so it is reduced.

There is also a perfect self-adjoint pairing. Let $\ell:R_\infty\to S_\infty$ extract the coefficient of $x_1\cdots x_b$ in (15.5), and set

$$
\langle a,c\rangle_\infty=\ell(ac).
\tag{15.12}
$$

For one variable its matrix in the basis $1,x_i$ is

$$
\begin{pmatrix}
0&1\\
1&\varpi+z_i
\end{pmatrix},
\tag{15.13}
$$

whose determinant is $-1$. The multivariable matrix is the tensor product of these matrices and therefore has unit determinant. This proves perfectness. Commutativity proves self-adjointness.

### 15.3 Descent and the finite-level conclusion

Augmentation gives

$$
R=R_\infty/\mathfrak a_\infty R_\infty
\cong
\mathcal O[[x_1,\ldots,x_b]]/
\bigl(x_i(x_i-\varpi):1\le i\le b\bigr).
\tag{15.14}
$$

Set $\mathbb T=R$ and $M=R$ with their descended actions. Then all three control statements are exact and the canonical map is the identity:

$$
R\xrightarrow{\sim}\mathbb T.
\tag{15.15}
$$

The finite ring is free of rank $2^b$ over $\mathcal O$ and is a complete intersection. At the augmentation $x_i\mapsto0$, its cotangent module is

$$
\Phi_R\cong(k)^b,
\qquad
\operatorname{length}_{\mathcal O}\Phi_R=b.
\tag{15.16}
$$

The element

$$
h=\prod_{i=1}^b(x_i-\varpi)
\tag{15.17}
$$

annihilates the augmentation ideal and has augmentation $(-\varpi)^b$. Conversely, generic branch separation shows that no smaller power clears the idempotent of the all-zero branch.

Indeed, in the generic fiber that idempotent is

$$
e_0=\prod_{i=1}^b\left(1-\frac{x_i}{\varpi}\right).
$$

If $c e_0$ lies in the integral lattice (15.5), its coefficient of $x_1\cdots x_b$ is $(-1)^bc/\varpi^b$ and must lie in $\mathcal O$. Thus $c\in(\varpi^b)$. This proves the asserted minimality and hence

$$
\eta_R=(\varpi^b),
\qquad
\operatorname{length}_{\mathcal O}\Psi_R=b.
\tag{15.18}
$$

Thus the intrinsic numerical equality agrees with the complete-intersection calculation. Notice that the special fiber has nilpotents $x_i^2=0$ even though the total ring is reduced. Reducedness of a finite flat total space does not require a reduced special fiber.

This model verifies the entire clean chain:

$$
\begin{array}{c}
P_\infty\text{ regular, verified sharp height, and }S_\infty\text{-freeness}\\
+\text{the faithful regular representation}\\
\Downarrow\\
\text{complete intersection, full support, faithful action}\\
\Downarrow\\
\text{regular augmentation and exact control}\\
\Downarrow\\
R=\mathbb T,\quad M\text{ free of rank one over }R,
\end{array}
\tag{15.19}
$$

while also exhibiting nontrivial congruences between $2^b$ generic branches.

## 16. The master theorem and its variants

### 16.1 The sharp patched comparison theorem

We now consolidate the argument. The hypotheses are deliberately arranged so that each can be verified independently of the desired equality.

> **Theorem 16.1 (sharp patched comparison).** Let $\mathcal O$ be a complete DVR and let
>
> $$
>
> S_\infty=\mathcal O[[z_1,\ldots,z_q]],
> \qquad
> \mathfrak a_\infty=(z_1,\ldots,z_q),
> \qquad
> d=q+1.
> \tag{16.1}
> $$
>
> Suppose the following data and hypotheses are given.
>
> **Presentation.** There is a quotient of complete Noetherian local rings
>
> $$
>
> R_\infty=P_\infty/J_\infty,
> \tag{16.2}
> $$
>
> compatible with the displayed $S_\infty$-algebra structure, where $P_\infty$ is Cohen--Macaulay, catenary, and equidimensional of dimension $d+b$, the dimension formula holds at primes minimal over $J_\infty$, and $J_\infty$ is generated by at most $b$ elements.
>
> **Patched module and action.** A nonzero finite $R_\infty$-module $M_\infty$ is finite free over $S_\infty$. Its $R_\infty$-action is compatible with the structural $S_\infty$-action. Put
>
> $$
>
> I_\infty=\operatorname{Ann}_{R_\infty}M_\infty,
> \qquad
> A_\infty=R_\infty/I_\infty.
> \tag{16.3}
> $$
>
> **Coverage.** For every $\mathfrak p\in\operatorname{Min}R_\infty$,
>
> $$
>
> (M_\infty)_{\mathfrak p}\ne0.
> \tag{16.4}
> $$
>
> **Exact finite control.** There are complete local $\mathcal O$-algebras $R$ and $\mathbb T$ and a finite module $M$ with compatible identifications
>
> $$
>
> R_\infty/\mathfrak a_\infty R_\infty\cong R,
> \quad
> A_\infty/\mathfrak a_\infty A_\infty\cong\mathbb T,
> \quad
> M_\infty/\mathfrak a_\infty M_\infty\cong M,
> \tag{16.5}
> $$
>
> the algebra $\mathbb T$ is the faithful image of its action on $M$, and the descended map is the canonical surjection $R\twoheadrightarrow\mathbb T$ for the fixed-determinant deformation problem with the stated local conditions.
>
> Then:
>
> 1. $R_\infty$ is equidimensional of dimension $d$;
> 2. $J_\infty$ has height $b$, is minimally generated by $b$ elements, and is generated by a $P_\infty$-regular sequence;
> 3. $R_\infty$ is Cohen--Macaulay and $M_\infty$ is maximal Cohen--Macaulay over it;
> 4. $I_\infty$ is nilpotent, so
>
> $$
>
> R_\infty^{\mathrm{red}}\cong A_\infty^{\mathrm{red}};
> \tag{16.6}
> $$
>
> 5. $R_\infty$ is finite free over $S_\infty$, $z_1,\ldots,z_q$ is $R_\infty$-regular, and both $R$ and $\mathbb T$ are finite free over $\mathcal O$;
> 6. the finite comparison has nilpotent kernel and
>
> $$
>
> R^{\mathrm{red}}\xrightarrow{\sim}\mathbb T^{\mathrm{red}}.
> \tag{16.7}
> $$

**Proof.** Let $\mathfrak p$ be a minimal prime of $R_\infty$, viewed as a prime of $P_\infty$ minimal over $J_\infty$. The relation bound and dimension formula give

$$
\dim R_\infty/\mathfrak p\ge d.
\tag{16.8}
$$

Coverage gives $I_\infty\subseteq\mathfrak p$, hence

$$
V(\mathfrak p)
\subseteq V(I_\infty)
=\operatorname{Supp}_{R_\infty}M_\infty.
\tag{16.9}
$$

The support is $\operatorname{Spec}A_\infty$. Since

$$
A_\infty\hookrightarrow
\operatorname{End}_{S_\infty}(M_\infty)
\tag{16.10}
$$

is finite over $S_\infty$ and contains $S_\infty$ faithfully, it has dimension $d$. Thus the right side of (16.9) has dimension $d$, giving the reverse inequality to (16.8). Every component therefore has dimension $d$. This proves assertion 1.

The height of $J_\infty$ is now $(d+b)-d=b$. Since it is generated by at most $b$ elements, height theorem forces exactly $b$ minimal generators. The Cohen--Macaulay height criterion makes them a regular sequence. This proves assertion 2, and its quotient is Cohen--Macaulay of dimension $d$. Depth invariance under the finite action map gives

$$
\operatorname{depth}_{R_\infty}M_\infty
=\operatorname{depth}_{S_\infty}M_\infty=d,
\tag{16.11}
$$

which proves assertion 3.

Coverage says $I_\infty$ is contained in every minimal prime, hence in the nilradical. Since the ring is Noetherian, $I_\infty$ is nilpotent. This proves assertion 4.

The nilpotent filtration of $R_\infty$ has successive quotients finite over $A_\infty$, and $A_\infty$ is finite over $S_\infty$ by (16.10). Hence $R_\infty$ is finite over $S_\infty$. It is Cohen--Macaulay of the same dimension as the regular local ring $S_\infty$, so

$$
\operatorname{depth}_{S_\infty}R_\infty=d.
\tag{16.12}
$$

Auslander--Buchsbaum gives projective dimension zero over $S_\infty$. Thus $R_\infty$ is finite free and the parameter sequence is regular. Its augmentation quotient is finite free over $S_\infty/\mathfrak a_\infty=\mathcal O$. Likewise $M\cong\mathcal O^r$, and the faithful action embeds the finite algebra $\mathbb T$ into $\operatorname{End}_{\mathcal O}(M)$; hence $\mathbb T$ is $\mathcal O$-torsion-free and therefore finite free. This proves assertion 5.

Finally, the kernel of the descended map in (16.5) is the image of the nilpotent ideal $I_\infty$, hence nilpotent. Reducing the canonical surjection proves (16.7). This proves assertion 6. $\square$

The theorem proves near faithfulness, not patched faithfulness. This limitation is intentional and exact.

### 16.2 Full $R=T$

Theorem 16.1 upgrades to full equality under any one of the following additional hypotheses:

$$
\begin{array}{ll}
\text{(F1)}&R_\infty\text{ is reduced};\\
\text{(F2)}&I_\infty=0\text{ by a direct annihilator argument};\\
\text{(F3)}&R_\infty\otimes_{S_\infty}K_\infty\text{ is reduced};\\
\text{(F4)}&R\text{ is reduced};\\
\text{(F5)}&\operatorname{Ann}_{(R_\infty)_{\mathfrak p}}
((M_\infty)_{\mathfrak p})=0
\text{ for every }\mathfrak p\in\operatorname{Min}R_\infty.
\end{array}
\tag{16.13}
$$

Under (F1), the nilpotent ideal $I_\infty$ is zero. Under (F2), this is the hypothesis itself. Under (F3), assertion 5 of Theorem 16.1 makes $R_\infty$ $S_\infty$-torsion-free, so it injects into its generic fiber; a nilpotent element maps to zero there and must vanish. Under (F5), Theorem 16.1 makes $R_\infty$ Cohen--Macaulay, so its associated primes are its minimal primes; the associated-prime criterion (5.16) makes the action faithful. In these four cases

$$
R_\infty\xrightarrow{\sim}A_\infty,
\tag{16.14}
$$

and exact control gives

$$
\boxed{R\xrightarrow{\sim}\mathbb T.}
\tag{16.15}
$$

Under (F4), Theorem 16.1 already says that the finite kernel is nilpotent. A reduced source contains no nonzero nilpotent ideal, so (16.15) follows without patched reducedness.

Another useful version replaces coverage plus reducedness by direct faithful action:

> **Faithful-action variant.** Assume the presentation and patched-module hypotheses of Theorem 16.1, but not coverage, together with exact finite control and $I_\infty=0$. Then $R_\infty=A_\infty$ is finite over $S_\infty$, so $\dim R_\infty=d$; consequently $R=\mathbb T$, and the sharp relation and Cohen--Macaulay conclusions follow.

Here direct faithfulness supplies both the dimension ceiling, through finiteness of $R_\infty=A_\infty$ over $S_\infty$, and the kernel argument. This variant makes clear that component coverage is a method for obtaining near faithfulness, not part of the definition of an $R=T$ theorem.

### 16.3 Equality of reduced quotients

The reduced variant is exactly assertion 6 of Theorem 16.1:

> **Reduced comparison.** Under the presentation, module, coverage, and exact-control hypotheses, with no reducedness assumption on either patched ring, the canonical map induces
>
> $$
>
> R^{\mathrm{red}}\xrightarrow{\sim}\mathbb T^{\mathrm{red}}.
> \tag{16.16}
> $$

This is the optimal conclusion from full support alone. It can be sharpened to

$$
R^{\mathrm{red}}\cong\mathbb T
\tag{16.17}
$$

if $\mathbb T$ is reduced, but (16.17) still does not identify $R$ with $\mathbb T$ unless $R$ is reduced or its nilradical is otherwise killed.

An often useful sufficient condition for reducedness of $R$ is:

$$
R\text{ finite flat and Cohen--Macaulay over }\mathcal O,
\quad
R[1/\varpi]\text{ reduced}.
\tag{16.18}
$$

Indeed, flatness injects $R$ into $R[1/\varpi]$. A nilpotent of $R$ becomes zero in the reduced generic fiber and therefore is already zero. The Cohen--Macaulay phrase is not needed for this injection once flatness is known, but is often how flatness is proved by regular descent.

### 16.4 Componentwise $R=T$

Suppose the presentation and module hypotheses of Theorem 16.1 hold, but full coverage is unavailable. Assume instead that $R_\infty$ is equidimensional of dimension $d$ by an independent ceiling and that

$$
\operatorname{Supp}_{R_\infty}M_\infty
=\bigcup_{\mathfrak p\in\Sigma}V(\mathfrak p)
\tag{16.19}
$$

for a specified subset $\Sigma\subseteq\operatorname{Min}R_\infty$. Put

$$
P_\Sigma=\bigcap_{\mathfrak p\in\Sigma}\mathfrak p.
\tag{16.20}
$$

Then

$$
\sqrt{I_\infty}=P_\Sigma,
\qquad
(R_\infty/P_\Sigma)
\cong A_\infty^{\mathrm{red}}.
\tag{16.21}
$$

After augmentation, define

$$
R_\Sigma=R_\infty/(P_\Sigma+\mathfrak a_\infty).
\tag{16.22}
$$

Because

$$
\sqrt{I_\infty+\mathfrak a_\infty R_\infty}
=\sqrt{P_\Sigma+\mathfrak a_\infty R_\infty},
\tag{16.23}
$$

exact action control gives a canonical reduced equality

$$
\boxed{R_\Sigma^{\mathrm{red}}
\xrightarrow{\sim}\mathbb T^{\mathrm{red}}.}
\tag{16.24}
$$

If the stronger scheme-theoretic equality

$$
I_\infty=P_\Sigma
\tag{16.25}
$$

holds, then $A_\infty=R_\infty/P_\Sigma$ and exact augmentation gives

$$
R_\Sigma\xrightarrow{\sim}\mathbb T.
\tag{16.26}
$$

For (16.24) or (16.26) to be an intrinsic componentwise theorem, $R_\Sigma$ must be identified with the finite quotient defined by the intended local conditions. Otherwise it is a correct comparison for a patch-defined quotient but not yet a named finite deformation problem.

### 16.5 Complete-intersection and freeness conclusions

Continue under Theorem 16.1. The regular relation sequence proves that

$$
P_\infty\longrightarrow R_\infty
\tag{16.27}
$$

is a complete-intersection quotient of codimension $b$. If

$$
P_\infty=R_{\mathrm{loc}}[[w_1,\ldots,w_g]],
\tag{16.28}
$$

then $R_{\mathrm{loc}}\to R_\infty$ is a complete-intersection map of relative codimension $b$. If $P_\infty$ is regular, then $R_\infty$ is an absolute complete intersection.

Assertion 5 makes the augmentation sequence regular on $R_\infty$. Hence, when $R_\infty$ is an absolute complete intersection,

$$
R=R_\infty/\mathfrak a_\infty R_\infty
\tag{16.29}
$$

is an absolute complete intersection. It is finite free over $\mathcal O$ because $R_\infty$ is finite free over $S_\infty$. If full $R=T$ also holds, the same conclusions apply to $\mathbb T$.

For the module, Theorem 16.1 gives only

$$
M_\infty\text{ maximal Cohen--Macaulay over }R_\infty.
\tag{16.30}
$$

It becomes $R_\infty$-free if, in addition, it has finite projective dimension over $R_\infty$, if $R_\infty$ is regular, or if it is cyclic and faithful. In that event its freeness descends to $M$ over $R$. No freeness claim follows solely from the complete-intersection property.

If $M_\infty$ is free of rank one over the faithful acting algebra and has a perfect self-adjoint $S_\infty$-pairing, then an acting-algebra basis identifies that algebra with the $S_\infty$-free module $M_\infty$. Thus the flatness required in Section 8.4 is automatic, and the acting algebra is Gorenstein over $S_\infty$. Under full ring equality this makes $R_\infty$ Gorenstein, and regular descent makes $R=\mathbb T$ Gorenstein over $\mathcal O$.

### 16.6 The numerical-criterion variant

There is a finite-level master variant that does not require patched reducedness or full component coverage.

> **Theorem 16.2 (module-derived numerical comparison).** Let $R\twoheadrightarrow\mathbb T$ be the canonical surjection of complete local augmented $\mathcal O$-algebras. Assume:
>
> 1. $\mathbb T$ is finite flat over $\mathcal O$;
> 2. $\Phi_R$ has finite $\mathcal O$-length;
> 3. a finite free $\mathcal O$-module $M$ has a faithful $\mathbb T$-action and a perfect self-adjoint pairing;
> 4. the distinguished generic eigenspace has rank one and satisfies branch saturation;
> 5. exact specialization of the patched relation complex gives a square map $D:U\to V$ presenting $\Phi_R$, and the patched self-duality gives determinant-line isomorphisms that identify $\det(D)$, up to a unit, with the determinant of $M_\lambda\hookrightarrow M_\lambda^\vee$ as in Section 9.4.
>
> Then
>
> $$
>
> R\xrightarrow{\sim}\mathbb T,
> \tag{16.31}
> $$
>
> both rings are finite flat complete intersections over $\mathcal O$, and
>
> $$
>
> \operatorname{Fitt}_{\mathcal O}^0(\Phi_R)
> =\eta(M)=\eta_{\mathbb T}.
> \tag{16.32}
> $$

**Proof.** The determinant lemma of Section 9.4 applied to hypothesis 5 gives

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_R)=\eta(M).
\tag{16.33}
$$

Branch saturation and rank one give $\eta(M)=\eta_{\mathbb T}$. Equation (16.33) therefore gives equality of the cotangent and congruence lengths. All hypotheses of the numerical isomorphism theorem in Section 9.6 hold, so (16.31) and the structural conclusions follow. $\square$

The common determinant in hypothesis 5 is a conclusion of the patched complexes, not the statement that $R=\mathbb T$ in disguise. It compares a presentation of $\Phi_R$ with a lattice discriminant on $M$. Branch saturation is likewise a module-size statement. Both can be checked before kernel elimination.

### 16.7 A minimal hypothesis checklist

No single hypothesis list is minimal for every conclusion. The following ledger records the irreducible jobs performed by the assumptions.

$$
\begin{array}{c|l}
\text{desired conclusion}&\text{input that performs the missing job}\\ \hline
\dim R_\infty\ge d
&\dim P_\infty=d+b\text{ and at most }b\text{ relations}\\
\dim R_\infty\le d
&\text{independent ceiling, finiteness, or all-component coverage}\\
J_\infty\text{ regular}
&P_\infty\text{ Cohen--Macaulay and sharp height }b\\
M_\infty\text{ maximal Cohen--Macaulay}
&S_\infty\text{-freeness and }\dim R_\infty=d\\
I_\infty\text{ nilpotent}
&\text{full component coverage}\\
I_\infty=0
&\text{source reducedness, generic associated-prime faithfulness, or a direct annihilator proof}\\
R_\infty\text{ finite free over }S_\infty
&\text{near faithfulness, ring Cohen--Macaulayness, dimension equality}\\
R=\mathbb T
&\text{patched faithfulness plus exact action control}\\
R^{\mathrm{red}}=\mathbb T^{\mathrm{red}}
&\text{near faithfulness plus exact action control}\\
R\text{ complete intersection}
&R_\infty\text{ absolute complete intersection, regular augmentation, exact ring control}\\
M\text{ free over }R
&M_\infty\text{ free over }R_\infty\text{ and exact module control}\\
\text{numerical }R=\mathbb T
&\text{compatible surjection, target flatness, finite cotangent, common determinant, saturation}.
\end{array}
\tag{16.34}
$$

The coefficient DVR, fixed determinant, local-condition compatibility, and compatible canonical finite-level surjection underlie every row. Framed variables may be added and removed only through formally smooth control. Nonminimal problems must reverify the local dimension and component rows.

## 17. The final audit

### 17.1 Dimensions and depth

The dimension argument contains two inequalities with different sources:

$$
\underbrace{\dim R_\infty/\mathfrak p\ge d}_{\text{height theorem and relation budget}},
\qquad
\underbrace{\dim R_\infty/\mathfrak p\le d}_{\text{coverage and support dimension}}.
\tag{17.1}
$$

The first is componentwise because the dimension formula was assumed at every prime minimal over $J_\infty$. The second is componentwise because coverage puts all of $V(\mathfrak p)$ inside the module support. Neither follows from the other, and the action quotient supplies only the lower direction for the ambient dimension.

Depth is transported through finite local maps only for the same finite module. Thus

$$
\operatorname{depth}_{S_\infty}M_\infty
=\operatorname{depth}_{A_\infty}M_\infty
=\operatorname{depth}_{R_\infty}M_\infty=d.
\tag{17.2}
$$

Maximal Cohen--Macaulayness is asserted only after $\dim R_\infty=d$. Ring Cohen--Macaulayness comes separately from the regular relation sequence. Auslander--Buchsbaum is used only over the regular local ring $S_\infty$, after finiteness has been proved. No step infers module freeness over a singular ring from maximal depth.

### 17.2 Support and nilpotents

The annihilator chain has been checked in the following exact order:

$$
\text{coverage}
\Longrightarrow
I_\infty\subseteq\bigcap_{\mathfrak p\in\operatorname{Min}R_\infty}\mathfrak p
=\sqrt{(0)}
\Longrightarrow
I_\infty\text{ nilpotent}.
\tag{17.3}
$$

The final implication uses Noetherianity. It yields near faithfulness and equality of reduced quotients. The extra step

$$
I_\infty\text{ nilpotent}\Longrightarrow I_\infty=0
\tag{17.4}
$$

is made only under reducedness of the source or a direct zero-annihilator proof. Target reducedness and target torsion-freeness were explicitly rejected as substitutes. Componentwise statements distinguish $\sqrt{I_\infty}=P_\Sigma$ from $I_\infty=P_\Sigma$.

### 17.3 Regular sequences and Tor

The relation sequence is declared regular only after

$$
\operatorname{ht}J_\infty=b=\mu(J_\infty)
\tag{17.5}
$$

has been proved in the Cohen--Macaulay ambient ring. Absolute complete-intersection language is used only when the ambient presentation is regular or already an absolute complete intersection.

The augmentation variables are known to be regular on $M_\infty$ from $S_\infty$-freeness. They are known to be regular on $R_\infty$ only after miracle flatness proves $S_\infty$-freeness of the ring. Therefore

$$
\operatorname{Tor}^{S_\infty}_i(R_\infty,\mathcal O)=0
\quad(i>0)
\tag{17.6}
$$

when complete-intersection descent is invoked. For the acting quotient, no Tor vanishing is presumed unless its flatness is independently established. Equality itself descends by ordinary quotienting and does not require Tor; identifying kernels after tensoring does.

### 17.4 Numerical invariants

Every numerical use is relative to $\mathcal O$ and to the same compatible augmentation. The direction has been checked:

$$
\operatorname{length}\Phi_{\mathbb T}
\ge\operatorname{length}\Psi_{\mathbb T},
\qquad
\text{required: }
\operatorname{length}\Phi_R
\le\operatorname{length}\Psi_{\mathbb T}.
\tag{17.7}
$$

The required inequality arises from the common determinant and branch saturation. Pairing alone yields a dual-lattice description but not equality with the ring congruence ideal. Fitting ideals, rather than annihilators, retain total length in higher rank. The numerical theorem is invoked only with a surjective map, finite flat target, finite source cotangent module, and compatible points.

No complete-intersection property of $R$ is assumed in the refined numerical route. It is a conclusion. In the support route, by contrast, complete-intersection structure is proved from sharp patched codimension before descent. The two routes do not borrow conclusions from one another.

### 17.5 Finite-level recovery

The three recovery statements have been kept distinct:

$$
R_\infty/\mathfrak a_\infty R_\infty=R,
\qquad
M_\infty/\mathfrak a_\infty M_\infty=M,
\qquad
A_\infty/\mathfrak a_\infty A_\infty=\mathbb T.
\tag{17.8}
$$

The last is the action-saturation hypothesis. Without it, patched equality descends only to the larger specialized action quotient. The commutative control diagram identifies the descended arrow with the canonical map for the fixed determinant and chosen local conditions.

Nilpotent patched kernels have nilpotent finite images, giving reduced equality. Zero patched kernels give full equality. Regular augmentation descends Cohen--Macaulay, complete-intersection, Gorenstein, and module-freeness statements only under the hypotheses stated for each. Formally smooth frame variables are removed separately from auxiliary and padding variables.

## 18. Conclusion

The abstract Taylor--Wiles argument is a controlled passage from depth to support, from support to an annihilator statement, and from that statement to a canonical finite comparison. Its decisive chain is

$$
\begin{array}{c}
M_\infty\text{ finite free over }S_\infty
+\text{a sharp Cohen--Macaulay relation presentation}\\
+\text{a valid dimension ceiling}\\
\Downarrow\\
\dim R_\infty=d,
\quad R_\infty\text{ Cohen--Macaulay},
\quad M_\infty\text{ maximal Cohen--Macaulay}\\
\Downarrow\\
\text{component coverage}
\Longrightarrow
\operatorname{Ann}_{R_\infty}M_\infty\text{ nilpotent}\\
+\text{exact action control}\\
\Downarrow\\
R^{\mathrm{red}}\cong\mathbb T^{\mathrm{red}},
\end{array}
\tag{18.1}
$$

with reducedness or direct faithfulness adding the final upgrade

$$
\boxed{R\cong\mathbb T.}
\tag{18.2}
$$

The numerical route reaches the same endpoint through a different exact bridge: a common determinant turns the patched self-dual module into a cotangent Fitting ideal, multiplicity-one saturation identifies that determinant with the ring congruence ideal, and the numerical criterion eliminates the kernel while proving finite flat complete-intersection structure.

Every qualification carries mathematical content. Equal dimensions do not kill a kernel. Maximal Cohen--Macaulay modules over singular rings need not be free. Full support does not see nilpotent thickenings. Complete-intersection structure descends only through regular sequences. Pairings compute lattice indices but do not manufacture multiplicity one. Component hopping is a hypothesis or theorem of its own. Exact action control is separate from deformation and module control.

Once these boundaries are respected, the final comparison is both strong and portable. The infinite objects may depend on choices, the verification of coverage may vary between minimal and nonminimal settings, and either the support or numerical route may be preferable. Yet the conclusion concerns one fixed, canonical arrow attached to the original deformation problem:

$$
R\longrightarrow\mathbb T.
\tag{18.3}
$$

One successful verification of the ledger together with one of the stated kernel-killing inputs proves that this arrow is an isomorphism, independently of every choice used to build the witness above it.
