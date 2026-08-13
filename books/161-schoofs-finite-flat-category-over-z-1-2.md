# Schoof's Finite-Flat Category over $\mathbf Z[1/2]$

## Contents

1. [The global integral problem](#1-the-global-integral-problem)
   - [Why a category is needed](#11-why-a-category-is-needed)
   - [The base and the two exceptional primes](#12-the-base-and-the-two-exceptional-primes)
   - [The odd-tame condition](#13-the-odd-tame-condition)
   - [The Schoof category](#14-the-schoof-category)
   - [The main theorem package](#15-the-main-theorem-package)
2. [From local models to a global Hopf order](#2-from-local-models-to-a-global-hopf-order)
   - [The gluing question](#21-the-gluing-question)
   - [Hopf orders at the odd primes](#22-hopf-orders-at-the-odd-primes)
   - [Intersection of lattices](#23-intersection-of-lattices)
   - [Gluing theorem](#24-gluing-theorem)
   - [Uniqueness and exceptional cases](#25-uniqueness-and-exceptional-cases)
3. [Exact structure, closure, and duality](#3-exact-structure-closure-and-duality)
   - [Why ordinary kernels are unsafe](#31-why-ordinary-kernels-are-unsafe)
   - [Saturated closure over the Dedekind base](#32-saturated-closure-over-the-dedekind-base)
   - [Quotients and admissible exact sequences](#33-quotients-and-admissible-exact-sequences)
   - [Stability of the inertia condition](#34-stability-of-the-inertia-condition)
   - [Cartier duality](#35-cartier-duality)
   - [Primary decomposition and composition series](#36-primary-decomposition-and-composition-series)
4. [The arithmetic ceiling for exponent three](#4-the-arithmetic-ceiling-for-exponent-three)
   - [Fields cut out by objects](#41-fields-cut-out-by-objects)
   - [The exact contribution at two](#42-the-exact-contribution-at-two)
   - [The finite-flat contribution at three](#43-the-finite-flat-contribution-at-three)
   - [The root-discriminant inequality](#44-the-root-discriminant-inequality)
   - [The unconditional degree cutoff](#45-the-unconditional-degree-cutoff)
5. [The small abelian calculations](#5-the-small-abelian-calculations)
   - [Why abelian quotients decide simple modules](#51-why-abelian-quotients-decide-simple-modules)
   - [Abelian subfields over the rationals](#52-abelian-subfields-over-the-rationals)
   - [Arithmetic of $\mathbf Q(\zeta_3)$](#53-arithmetic-of-mathbf-qzeta_3)
   - [The ray groups at the prime above three](#54-the-ray-groups-at-the-prime-above-three)
   - [The exact prime-to-three field exclusion](#55-the-exact-prime-to-three-field-exclusion)
6. [Classification of simple objects](#6-classification-of-simple-objects)
   - [A simple object has exponent three](#61-a-simple-object-has-exponent-three)
   - [Solvability of the image](#62-solvability-of-the-image)
   - [The commutator subgroup](#63-the-commutator-subgroup)
   - [Normal three-groups in characteristic three](#64-normal-three-groups-in-characteristic-three)
   - [Identification of the two integral models](#65-identification-of-the-two-integral-models)
7. [Extension groups between the simple objects](#7-extension-groups-between-the-simple-objects)
   - [What must be computed](#71-what-must-be-computed)
   - [Constant by constant](#72-constant-by-constant)
   - [Multiplicative by multiplicative](#73-multiplicative-by-multiplicative)
   - [Kummer extensions of constant by multiplicative](#74-kummer-extensions-of-constant-by-multiplicative)
   - [Vanishing in the reverse direction](#75-vanishing-in-the-reverse-direction)
   - [The complete extension table](#76-the-complete-extension-table)
8. [Ray and Kummer calculations through all levels](#8-ray-and-kummer-calculations-through-all-levels)
   - [Units of $\mathbf Z[1/2]$](#81-units-of-mathbf-z12)
   - [Local cube classes at three](#82-local-cube-classes-at-three)
   - [Cyclotomic units and the cubic ray direction](#83-cyclotomic-units-and-the-cubic-ray-direction)
   - [Higher Kummer levels](#84-higher-kummer-levels)
   - [The one-motive model](#85-the-one-motive-model)
9. [Filtration rearrangement](#9-filtration-rearrangement)
   - [Why a composition series is not enough](#91-why-a-composition-series-is-not-enough)
   - [Swapping one inversion](#92-swapping-one-inversion)
   - [The sorting theorem](#93-the-sorting-theorem)
   - [Pure constant and pure multiplicative blocks](#94-pure-constant-and-pure-multiplicative-blocks)
   - [Existence and uniqueness of the two-step filtration](#95-existence-and-uniqueness-of-the-two-step-filtration)
10. [Finite coefficient levels](#10-finite-coefficient-levels)
   - [Coefficient actions and stable cuts](#101-coefficient-actions-and-stable-cuts)
   - [The canonical image submodule](#102-the-canonical-image-submodule)
   - [The cross relation](#103-the-cross-relation)
   - [The trace identity](#104-the-trace-identity)
   - [The residual orientation and its Kummer class](#105-the-residual-orientation-and-its-kummer-class)
11. [All-level devissage](#11-all-level-devissage)
   - [Compatible finite-flat levels](#111-compatible-finite-flat-levels)
   - [Passage to a stable lattice](#112-passage-to-a-stable-lattice)
   - [The integral cyclotomic line](#113-the-integral-cyclotomic-line)
   - [The three-adic conclusion](#114-the-three-adic-conclusion)
   - [$3$-divisible groups in the category](#115-3-divisible-groups-in-the-category)
12. [Examples and boundary cases](#12-examples-and-boundary-cases)
   - [The split object](#121-the-split-object)
   - [The Kummer object attached to two](#122-the-kummer-object-attached-to-two)
   - [Why the residual field need not split](#123-why-the-residual-field-need-not-split)
   - [What fails without the local hypotheses](#124-what-fails-without-the-local-hypotheses)
   - [Conclusion](#125-conclusion)

## 1. The global integral problem

### 1.1 Why a category is needed

A three-adic representation is visible through a tower of finite quotients, but a list of those quotients is not yet an arithmetic structure. At the prime $3$ one must know that each quotient comes from finite-flat geometry. At the prime $2$ one must retain the special tame unipotence forced by semistable monodromy. Away from $2$ and $3$ one needs genuine unramifiedness. Finally, all of these conditions must survive the operations used in a composition series: subgroup, quotient, extension, and duality.

The natural organizing object is therefore an exact category of finite locally free commutative group schemes over

$$
R=\mathbf Z[1/2].
$$

Removing the prime $2$ from the base does not discard its arithmetic. It moves that arithmetic to the generic fiber, where inertia at $2$ is recorded as a condition on the Galois action. The prime $3$ remains on the base, so flatness there is built into the object itself. Every other odd prime also remains on the base; because the order of our groups is a power of $3$, the groups are automatically finite etale there.

This division of labor is the central idea of the book. Integral geometry at $3$, tame Galois theory at $2$, and finite etale descent elsewhere can be glued into one global Hopf order. Once that is done, schematic closure gives a composition theory and arithmetic controls the simple factors.

### 1.2 The base and the two exceptional primes

Fix an algebraic closure $\overline{\mathbf Q}$ and write

$$
G_{\mathbf Q}=\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q).
$$

For a finite locally free commutative $R$-group $G$, its generic fiber is finite etale because the generic field has characteristic zero. We write

$$
V(G)=G_{\mathbf Q}(\overline{\mathbf Q}).
$$

This is a finite abelian group with continuous $G_{\mathbf Q}$-action. If $G$ has order a power of $3$, then $V(G)$ is a finite $3$-group.

At an odd prime $q\ne3$, the integer $3$ is a unit in $\mathbf Z_q$. A finite locally free group of $3$-power order over $\mathbf Z_q$ is therefore finite etale. Its generic Galois module is unramified at $q$, and conversely an unramified finite module has a unique finite etale model over $\mathbf Z_q$. At $q=3$, neither assertion remains true: connected finite-flat models such as $\mu_3$ occur, and the generic representation can be ramified.

At $2$ there is no integral fiber because $2$ is inverted. We choose an inertia group $I_2\subset G_{\mathbf Q}$ and its wild subgroup $P_2$. Different choices are conjugate, so the conditions below are independent of the choice.

The prerequisite results used later enter with exactly these hypotheses. Books 2--3 supply finite extensions of $\mathbf Q_2$ and $\mathbf Q_3$, lower and upper ramification groups, Herbrand's quotient theorem, and the integrality of abelian upper breaks for finite Galois extensions of local fields with perfect residue field. Book 17 supplies finite etale descent over the henselian DVRs $\mathbf Z_q$. Books 28, 34, and 42 supply saturated closure, represented quotients, coefficient actions, and the generic-module dictionary, while Book 34 supplies Cartier duality. Book 51 proves the order-three classification over the unramified mixed-characteristic DVR $\mathbf Z_3$. Book 29 proves the fppf Kummer sequence, including residue characteristic three, and Book 55 proves the finite-level criterion for a $3$-divisible system. Book 56, Theorems 6.1, 7.1, and 14.2 supply the local finite-flat upper-break, different, and global root-discriminant bounds used in Chapter 4. Book 160, Theorem 15.2 supplies the combined unconditional degree cutoffs after importing the certified analytic calculation from Book 7. The reciprocity conventions and ray exact sequences of Books 5--6 explain the surrounding class-field picture, but the exact small abelian exclusions needed here are proved directly in Chapter 5. No later classification result is used as an input.

### 1.3 The odd-tame condition

The phrase “odd tame inertia” has two independent parts. Tameness says that $P_2$ acts trivially. Oddness says that the finite image of $I_2$ has odd order. Since finite tame inertia is cyclic, its odd image is cyclic, but its order need not be a power of $3$ and need not be at most three.

For a finite $3$-primary module $M$, say that it has **odd-tame inertia at $2$** when $P_2$ acts trivially and the finite image of $I_2$ has odd order. This is the categorical condition used throughout the book. It is stable under subquotients, extensions, products, and duals.

There is an important refined case. If an exponent-three module also satisfies

$$
(\sigma-1)^2=0\qquad(\sigma\in I_2),
$$

then $\sigma^3=1$, so the inertia image is trivial or cyclic of order three. Semistable rank-two representations have precisely this square-zero residual behavior. Chapter 4 gives a degree bound for the full odd-tame category and a sharper degree-$20$ bound in this cubic-inertia case. Keeping the two assertions separate prevents a hidden strengthening of the category.

### 1.4 The Schoof category

The **Schoof category** $\mathcal S$ consists of finite locally free commutative group schemes $G/R$ satisfying:

- the order of $G$ is a power of $3$;
- $V(G)$ has odd-tame inertia at $2$.

Morphisms are homomorphisms of $R$-group schemes. An admissible exact sequence is an fppf-exact sequence

$$
0\longrightarrow G'\longrightarrow G\longrightarrow G''\longrightarrow0
$$

whose three terms lie in $\mathcal S$. We write

$$
C=\underline{\mathbf Z/3\mathbf Z},
\qquad
M=\mu_3.
$$

These will turn out to be the two simple objects.

An equivalent local-generic description is often more useful. An object is determined by a finite $3$-primary $G_{\mathbf Q}$-module $V$ which is unramified outside $\{2,3\}$, a finite-flat model of $V|_{G_{\mathbf Q_3}}$ over $\mathbf Z_3$, and the odd-tame condition at $2$. Chapter 2 proves that these data glue. The local model at $3$ is part of the data required for existence, but after gluing the resulting global group is independent of auxiliary choices at the other odd primes.

### 1.5 The main theorem package

The development culminates in four assertions.

**Theorem 1.1 (Schoof package).** The category $\mathcal S$ has the following properties.

1. It is stable under saturated schematic subobjects, represented quotients, admissible extensions, finite products, and Cartier duality.
2. Its simple objects are exactly $C$ and $M$.
3. Every object $G$ has an exact sequence
   $$
   0\longrightarrow G^{\mathrm m}\longrightarrow G
   \longrightarrow G^{\mathrm c}\longrightarrow0,
   $$
   where $G^{\mathrm m}$ is of multiplicative type and $G^{\mathrm c}$ is constant.
4. Let $A$ be a finite local quotient of the ring of integers in a finite extension of $\mathbf Q_3$, let $W$ be free of rank two over $A$, and suppose its Galois action, including the $A$-action, is modeled by an object of $\mathcal S$ and has determinant $\chi_3$. Then
   $$
   \operatorname{tr}\rho(g)=1+\chi_3(g)
   \qquad(g\in G_{\mathbf Q}).
   $$
   For a free rank-two $\mathbf Z_3$-lattice whose every finite level lies in $\mathcal S$, there is a stable exact sequence
   $$
   0\longrightarrow\mathbf Z_3(1)\longrightarrow T
   \longrightarrow\mathbf Z_3\longrightarrow0.
   $$

The extension in the last line need not split. Its distinguished nonsplit direction is the Kummer class of $2$. Thus the theorem proves reducibility and the semisimplification $1\oplus\chi_3$, not a false residual splitting statement.

## 2. From local models to a global Hopf order

### 2.1 The gluing question

Suppose a finite $3$-primary Galois module $V$ is unramified outside $\{2,3\}$ and has a finite-flat model at $3$. To place $V$ in $\mathcal S$, one must construct one group scheme over all of $R$. Merely saying that local models agree generically does not glue schemes: their coordinate rings are different integral lattices inside one rational Hopf algebra.

The correct construction is an intersection of Hopf orders. The base $R$ is Dedekind, so a finite torsion-free module is projective, and a lattice is recovered from its localizations at height-one primes. Those two facts are exactly what make the construction work.

### 2.2 Hopf orders at the odd primes

Let $V$ be a finite $3$-primary $G_{\mathbf Q}$-module, and let $G_{\mathbf Q}$ also denote the associated finite etale group scheme when no confusion is possible. Write

$$
B=\mathcal O(G_{\mathbf Q})
$$

for its finite-dimensional commutative Hopf algebra over $\mathbf Q$.

For every odd prime $q\ne3$, unramifiedness gives a unique finite etale group $G_q/\mathbf Z_q$ with generic fiber $G_{\mathbf Q_q}$. Its coordinate ring $B_q\subset B\otimes\mathbf Q_q$ is a finite free Hopf order. At $q=3$, choose the supplied finite-flat model and call its coordinate order $B_3$. This order need not be etale.

Only finitely many of these local orders differ from one global order. Here is the required spreading argument. Choose a $\mathbf Q$-basis of $B$ containing $1$ and write the multiplication, coproduct, counit, and antipode in that basis. After inverting one odd integer $N$, all their structure constants are integral. The free $R[1/N]$-module on that basis is then directly a Hopf algebra $B^{(N)}$ with generic fiber $B$. After increasing $N$ once more, its trace discriminant is a unit, so $B^{(N)}$ is finite etale. For every odd $q\nmid N$, both $B^{(N)}\otimes\mathbf Z_q$ and $B_q$ are finite etale models of the same generic group; henselian uniqueness identifies them. At the finitely many primes dividing $N$, and at $3$ if necessary, retain the prescribed $B_q$. Thus the family of local orders satisfies the restrictedness hypothesis of Lemma 2.1; the intersection below is not an uncontrolled infinite intersection.

### 2.3 Intersection of lattices

We need the underlying algebra lemma in a form that also controls tensor products.

**Lemma 2.1 (Dedekind lattice intersection).** Let $R$ be a Dedekind domain with fraction field $K$, let $W$ be finite-dimensional over $K$, and for every nonzero prime $\mathfrak p$ let $L_{\mathfrak p}\subset W_{\mathfrak p}$ be a full $R_{\mathfrak p}$-lattice. Assume $L_{\mathfrak p}=(L_0)_{\mathfrak p}$ for all but finitely many $\mathfrak p$. Then

$$
L=\{x\in W:x\in L_{\mathfrak p}\text{ for every }\mathfrak p\}
$$

is a finite projective $R$-module, $L\otimes_RK=W$, and $L_{\mathfrak p}$ is its localization at every $\mathfrak p$. Moreover

$$
L\otimes_RL
=
\{z\in W\otimes_KW:z\in
L_{\mathfrak p}\otimes_{R_{\mathfrak p}}L_{\mathfrak p}
\text{ for every }\mathfrak p\}.
$$

**Proof.** Clear denominators relative to $L_0$. There is a nonzero ideal $\mathfrak a$ supported on the finite exceptional set such that

$$
\mathfrak aL_0\subseteq L\subseteq\mathfrak a^{-1}L_0.
$$

Hence $L$ is finite and torsion-free. A finite torsion-free module over a Dedekind domain is projective. Localizing the defining intersection at $\mathfrak p$ removes every condition away from $\mathfrak p$: denominators supported at other primes are units. This gives $L_{\mathfrak p}$.

Both $L\otimes L$ and the displayed intersection on $W\otimes W$ are finite projective lattices with the same localization at every nonzero prime. The quotient of one by their intersection has zero localization everywhere and is therefore zero. Thus they agree. $\square$

The tensor assertion is the decisive part. Without it, knowing locally that a coproduct lands in $L_{\mathfrak p}\otimes L_{\mathfrak p}$ would not yet show globally that it lands in $L\otimes L$.

### 2.4 Gluing theorem

**Theorem 2.2 (Hopf-order gluing).** Let $V$ be a finite $3$-primary $G_{\mathbf Q}$-module unramified outside $\{2,3\}$. Suppose its restriction at $3$ has a finite locally free commutative model over $\mathbf Z_3$. Then there is a finite locally free commutative group $G/R$ with generic module $V$. Its localization at $3$ is the chosen model, and its localization at every odd $q\ne3$ is the unique finite etale model.

**Proof strategy.** Intersect all local coordinate orders inside the rational coordinate algebra. Then check each Hopf operation locally and use Lemma 2.1 to return to the global lattice.

**Proof.** For the local orders $B_q$ of §2.2, put

$$
A=B\cap\prod_{q\text{ odd}}B_q
=\{b\in B:b\in B_q\text{ in }B\otimes\mathbf Q_q
\text{ for every odd }q\}.
$$

Lemma 2.1 makes $A$ finite projective over $R$ and identifies $A\otimes\mathbf Z_q$ with $B_q$. Since each $B_q$ is a subalgebra containing $1$, the same is true of $A$.

Let $\Delta_B$, $\varepsilon_B$, and $S_B$ be the rational coproduct, counit, and antipode. For $a\in A$, every localization satisfies

$$
\Delta_B(a)\in B_q\otimes B_q.
$$

The tensor clause of Lemma 2.1 gives $\Delta_B(a)\in A\otimes A$. Similarly $\varepsilon_B(a)$ belongs to every $\mathbf Z_q$ and hence to $R$, while $S_B(a)$ belongs to every $B_q$ and hence to $A$. All Hopf identities already hold over $\mathbf Q$; both sides are maps between torsion-free modules, so they hold on $A$. Therefore $A$ is a finite projective Hopf algebra, and $G=\operatorname{Spec}A$ has the required properties. $\square$

This proof also shows that a coefficient action glues. An endomorphism of the rational Hopf algebra which preserves every local order preserves their intersection. Thus actions by $\mathbf Z/3^n\mathbf Z$ or by a finite local coefficient ring can be installed globally once they are present generically and preserve the chosen model at $3$.

### 2.5 Uniqueness and exceptional cases

The theorem gives uniqueness relative to the local orders: an $R$-lattice is the intersection of its height-one localizations. It does not say that a generic module has only one finite-flat model over an arbitrary ramified $3$-adic base. After a ramified extension containing the relevant roots of unity, constant and multiplicative-type models can have isomorphic generic fibers while retaining different special fibers. Over the unramified base $\mathbf Z_3$, order-three models are more rigid; the precise dichotomy used later is proved in §6.5.

Three hypotheses are essential. If the base had dimension greater than one, torsion-free would not imply locally free. If the module were ramified at an odd $q\ne3$, there would be no finite etale order at that prime. If one specified only a model after a ramified extension of $\mathbf Q_3$, descent of the generic module would not descend the Hopf lattice. The gluing theorem uses an actual model over $\mathbf Z_3$.

## 3. Exact structure, closure, and duality

### 3.1 Why ordinary kernels are unsafe

Finite locally free group schemes do not form an abelian category under every morphism. A scheme-theoretic kernel can acquire a vertical nonflat component, and the raw image can fail to be flat. The safe operations begin with a generic subgroup inside a fixed finite-flat ambient group, close it schematically, and then take the represented quotient.

This restriction is well suited to composition series. A stable subgroup of the generic Galois module is unambiguous. Its closure inside the chosen global model supplies the integral subobject; no independent choice of model is made for the subgroup.

### 3.2 Saturated closure over the Dedekind base

Let $G=\operatorname{Spec}A$ be finite locally free over $R$, and let $H_{\mathbf Q}\subset G_{\mathbf Q}$ be a closed subgroup with Hopf ideal $I_{\mathbf Q}\subset A\otimes\mathbf Q$. Define

$$
I=A\cap I_{\mathbf Q},
\qquad
\overline H=\operatorname{Spec}(A/I).
$$

**Proposition 3.1 (global saturated closure).** The group $\overline H$ is finite locally free over $R$, has generic fiber $H_{\mathbf Q}$, and is the unique finite-flat closed subgroup of $G$ with that generic fiber.

**Proof.** The quotient $A/I$ injects into $(A\otimes\mathbf Q)/I_{\mathbf Q}$, so it is torsion-free. It is finite over $R$ and hence projective. Localizing at each odd prime reduces the Hopf-ideal assertion to saturated closure over a DVR: the coproduct of $I$ maps to zero in the torsion-free tensor square of $A/I$, and the counit and antipode behave similarly. Thus $I$ is a Hopf ideal.

If $J$ is the Hopf ideal of another finite-flat closed subgroup with the same generic fiber, then $A/J$ is torsion-free, so $J$ is saturated and

$$
J=A\cap(J\otimes\mathbf Q)=A\cap I_{\mathbf Q}=I.
$$

This proves uniqueness. $\square$

### 3.3 Quotients and admissible exact sequences

A finite-flat closed subgroup $H\subset G$ has a represented fppf quotient $G/H$, again finite locally free, and

$$
0\longrightarrow H\longrightarrow G\longrightarrow G/H\longrightarrow0
$$

is exact. Formation of the quotient commutes with base change. Consequently a generic exact sequence inside a fixed middle object extends integrally by closing the generic subobject and taking this quotient.

Conversely, if $G'$ and $G''$ are given independently, an arbitrary generic extension of $G''_{\mathbf Q}$ by $G'_{\mathbf Q}$ need not have a finite-flat middle model. Extension-closure of $\mathcal S$ means the following precise statement: whenever an fppf extension has finite-flat end terms in $\mathcal S$, its finite-flat middle term also satisfies the generic inertia condition. It does not manufacture a middle term from a bare Galois cohomology class.

### 3.4 Stability of the inertia condition

Subgroups and quotients of a module with trivial wild inertia again have trivial wild inertia. Their tame inertia images are quotients of subgroups of a cyclic odd-order group and therefore still have odd order.

For an exact sequence

$$
0\to V'\to V\to V''\to0,
$$

suppose the inertia images on the ends have odd order. The kernel of the map from the inertia image on $V$ to the product of the two end images consists of filtration-lowering automorphisms. Because $V$ is $3$-primary, that kernel is a $3$-group: with respect to the two-step filtration its elements are $1+N$, where $N$ maps the quotient into the submodule, and successive coefficient layers are additive $3$-groups. Hence the middle inertia image is also odd. Wild inertia has pro-$2$ image, so it maps trivially. Thus odd-tame inertia is stable under extensions, not merely under those extensions whose middle term was assumed in advance to satisfy the condition.

Finite products behave similarly. Tame inertia is procyclic, and the image on a product is the cyclic image of one tame generator. Its order is the least common multiple of finitely many odd orders and is therefore odd.

### 3.5 Cartier duality

Cartier duality sends a finite locally free commutative group $G$ to $G^D$, commutes with base change, reverses admissible exact sequences, and exchanges

$$
C^D=M,
\qquad M^D=C.
$$

On generic points,

$$
V(G^D)\simeq\operatorname{Hom}(V(G),\mu_{3^n})
$$

when $G$ is killed by $3^n$. Thus the Galois action is the ordinary dual twisted by the cyclotomic character. At $2$ that character is unramified. Duality replaces an inertia matrix by its inverse transpose, which has the same finite order. Odd tame inertia and wild triviality therefore persist, and $G^D\in\mathcal S$.

Duality is compatible with closure: the annihilator of a saturated closure is the saturated closure of the generic annihilator. This ensures that the subquotients appearing in a dual composition series remain the correct integral models rather than merely groups with isomorphic generic fibers.

### 3.6 Primary decomposition and composition series

Every object of $\mathcal S$ has order $3^N$ for some $N$. If $G\ne0$, the generic module has a nonzero subgroup killed by $3$. Close such a subgroup in $G$ and choose one of minimal positive order. Repeating with the quotient gives a finite chain

$$
0=G_0\subset G_1\subset\cdots\subset G_r=G
$$

whose successive quotients are simple in the exact sense. Ranks strictly increase, so the process terminates. The generic fiber functor is faithful, and every step was made by saturated closure and represented quotient, so no hidden nonflat term enters.

The classification of those simple intervals is now an arithmetic problem. Geometry has reduced it to irreducible exponent-three Galois modules with an exact local ramification ledger.

## 4. The arithmetic ceiling for exponent three

### 4.1 Fields cut out by objects

Let $G\in\mathcal S$ be killed by $3$, and put $V=V(G)$. The kernel of

$$
G_{\mathbf Q}\longrightarrow\operatorname{Aut}_{\mathbf F_3}(V)
$$

cuts out a finite Galois field $L=\mathbf Q(V)$. Its Galois group is the faithful image. Because $G$ extends over every odd prime, $L/\mathbf Q$ is unramified outside $\{2,3\}$.

At $3$, the generic module has an actual finite-flat model over $\mathbf Z_3$. At $2$, odd-tame inertia gives a cyclic inertia group of some odd order $e_2$. These two facts give a uniform root-discriminant ceiling. When $e_2\le3$, they give the sharper ceiling used to exclude the one exceptional group in the simple-factor argument.

### 4.2 The exact contribution at two

The extension at $2$ is tame because wild inertia is trivial. If inertia has order $e_2$, its different exponent is

$$
d_2=e_2-1,
\qquad
\frac{d_2}{e_2}=1-\frac1{e_2}<1.
$$

Thus the uniform factor at $2$ is strictly less than $2$. If inertia is trivial the factor is absent. If inertia has order $3$, the sharper exact value is

$$
d_2=e_2-1=2,
\qquad
\frac{d_2}{e_2}=\frac23.
$$

An unramified residue extension changes neither number. In the cubic-inertia case the factor contributed to the absolute root discriminant is exactly

$$
2^{2/3}.
$$

This factor is paid once. The number of primes above $2$ and the dimension of $V$ do not multiply it; after division by the global degree the common local ratio $d_2/e_2$ is exactly the exponent of $2$.

### 4.3 The finite-flat contribution at three

Book 56, Theorem 6.1, specialized to a module killed by $3$ over the unramified local field $\mathbf Q_3$, says

$$
G_{\mathbf Q_3}^u\text{ acts trivially for }u>\frac12.
$$

Book 56, Theorem 7.1 then gives

$$
\frac{d_3}{e_3}<1+\frac12=\frac32.
$$

The strict sign comes from the term $-1/e_3$ in the exact bound, not from excluding a break at $u=1/2$. This distinction matters: $\mu_3$ attains the critical congruence radius even though the normalized different still satisfies the strict inequality.

### 4.4 The root-discriminant inequality

Combining the two local entries gives

**Proposition 4.1 (two-prime ceilings).** For every exponent-three object $G\in\mathcal S$ and $L=\mathbf Q(V(G))$,

$$
\boxed{
\operatorname{rd}(L)<2\cdot3^{3/2}.
}
$$

If inertia at $2$ has order at most $3$, then

$$
\boxed{
\operatorname{rd}(L)<3^{3/2}2^{2/3}.
}
$$

If inertia is trivial, the factor at $2$ is omitted entirely.

**Proof.** The global discriminant formula for a Galois extension ramified only at $2$ and $3$ is

$$
\operatorname{rd}(L)=
2^{d_2/e_2}3^{d_3/e_3}.
$$

Insert the general tame value $1-1/e_2<1$ and the strict finite-flat value at $3$. If $e_2\le3$, then $1-1/e_2\le2/3$, which gives the refined inequality. $\square$

The general ceiling applies unchanged to a finite direct sum of exponent-three objects. The product of their models is finite flat at $3$, while procyclic tame inertia at $2$ still has odd image. The refined ceiling applies when the image of the common tame generator on the direct sum has order at most three.

### 4.5 The unconditional degree cutoff

The combined cutoff in Book 160, Theorem 15.2 uses Book 7's certified test function

$$
F_6(x)=\frac{(1-|x|/6)_+}{\cosh(x/2)}
$$

and the certified inequality $B_6<1.10356$. For every number field of degree $n$ it gives

$$
\log\operatorname{rd}(L)>
\gamma+\log(8\pi)-\frac{12}{n}-1.10356.
$$

At $n=34$ the right side is greater than $2.3448859$, whereas

$$
\log(2\cdot3^{3/2})<2.3410657.
$$

The lower bound increases with $n$. Therefore the general part of Proposition 4.1 implies

$$
\boxed{[L:\mathbf Q]\le33.}
$$

In the cubic-inertia case, Book 160, Theorem 15.2 gives

$$
\operatorname{rd}(L)<3^{3/2}2^{2/3}
\quad\Longrightarrow\quad
[L:\mathbf Q]\le20.
\tag{4.1}
$$

Both conclusions are unconditional. The first applies to every faithful exponent-three action in $\mathcal S$, regardless of its dimension. The second will exclude the only exceptional order-$12$ commutator left by the broad bound.

## 5. The small abelian calculations

### 5.1 Why abelian quotients decide simple modules

A solvable nontrivial group always has a nontrivial abelian quotient. For a simple module in characteristic $3$, normal $3$-subgroups act trivially. The classification will therefore proceed by trapping the abelian quotients of its Galois image and then showing that the remaining commutator subgroup is a normal $3$-group.

This is the point at which a vague appeal to a maximal abelian extension would conceal too much. We calculate the exact fields and ray groups needed below.

### 5.2 Abelian subfields over the rationals

**Lemma 5.1 (rational abelian-field lemma).** Let $F/\mathbf Q$ be an abelian subextension of a field cut out by an exponent-three object of $\mathcal S$. Then

$$
F=\mathbf Q
\qquad\text{or}\qquad
F=K:=\mathbf Q(\zeta_3).
$$

**Proof strategy.** Remove ramification at $2$ by the structure of tame abelian extensions of $\mathbf Q_2$, remove positive wild depth at $3$ by Hasse--Arf integrality in upper numbering, and then use inertia and Minkowski's bound to limit the global degree.

**Proof.** In an abelian tame extension of a local field with residue field $\mathbf F_q$, the ramification index divides $q-1$. Indeed, if $\pi_L$ is a uniformizer, the tame character

$$
I\longrightarrow k_L^\times,
\qquad
\sigma\longmapsto\overline{\sigma(\pi_L)/\pi_L}
$$

is injective. Commutation with residue Frobenius sends a tame generator to its $q$th power and, in an abelian group, fixes it; hence its order divides $q-1$. For $\mathbf Q_2$, $q-1=1$. Thus every abelian quotient is unramified at $2$.

At $3$, the finite-flat bound puts every positive upper break below or at $1/2$. The Hasse--Arf theorem says that the upper breaks of an abelian extension are integers. Hence there is no positive break. The extension is at most tame at $3$, and the same tame-character argument makes the inertia order divide $3-1=2$.

Let $I$ be the inertia subgroup at $3$. It has order at most two. The fixed field $F^I$ is unramified at every finite prime. If it were nontrivial, its relative discriminant over $\mathbf Q$ would be the unit ideal, so its absolute root discriminant would be $1$, contradicting Minkowski's bound. Thus $F^I=\mathbf Q$ and $[F:\mathbf Q]=|I|\le2$.

If the degree is two, its discriminant is a fundamental quadratic discriminant supported only at $3$. A squarefree presentation $\mathbf Q(\sqrt d)$ has discriminant $d$ when $d\equiv1\pmod4$ and $4d$ otherwise. Avoiding the prime $2$ leaves only $d=-3$, so $F=\mathbf Q(\sqrt{-3})=\mathbf Q(\zeta_3)$. $\square$

The upper-numbering step is indispensable. Herbrand's quotient theorem passes the finite-flat cutoff to the abelian quotient, and Hasse--Arf then makes its breaks integral. A nonabelian finite-flat field can have a fractional upper break at $3$; only after passing to an abelian quotient does integrality force it away.

### 5.3 Arithmetic of $\mathbf Q(\zeta_3)$

Put $\zeta=\zeta_3$ and

$$
\mathcal O_K=\mathbf Z[\zeta],
\qquad
\lambda=1-\zeta.
$$

Then

$$
(3)=-\zeta^2\lambda^2,
\qquad N(\lambda)=3,
\qquad D_K=-3.
$$

The class number is one. Minkowski's bound says that every ideal class contains an integral ideal of norm at most

$$
\frac{4}{\pi}\frac{2!}{2^2}\sqrt3
=\frac{2\sqrt3}{\pi}<2.
$$

The only integral ideal of norm less than two is the unit ideal. Hence every ideal is principal.

The unit group is

$$
\mathcal O_K^\times=\mu_6.
$$

Indeed, for $u\in\mathcal O_K^\times$, both complex embeddings have absolute value whose product is $1$. Applying the same fact to all powers and using discreteness, or using the norm form

$$
N(a+b\zeta)=a^2-ab+b^2,
$$

shows that a unit has norm one and the six solutions of norm one modulo the hexagonal symmetry are $\pm1,\pm\zeta,\pm\zeta^2$.

### 5.4 The ray groups at the prime above three

Let $\mathrm{Cl}_{\lambda^n}(K)$ be the finite ray class group of ideals prime to $\lambda$ modulo principal ideals generated by elements congruent to $1$ modulo $\lambda^n$. Since the ordinary class group is trivial, the ray exact sequence reduces to

$$
\mathcal O_K^\times
\longrightarrow
(\mathcal O_K/\lambda^n)^\times
\longrightarrow
\mathrm{Cl}_{\lambda^n}(K)
\longrightarrow1.
$$

**Lemma 5.2 (ray calculation).** Every group $\mathrm{Cl}_{\lambda^n}(K)$ is a $3$-group.

**Proof.** Reduction to the residue field gives

$$
1\longrightarrow
(1+\lambda\mathcal O_K)/(1+\lambda^n\mathcal O_K)
\longrightarrow
(\mathcal O_K/\lambda^n)^\times
\longrightarrow\mathbf F_3^\times
\longrightarrow1.
$$

The first group has a filtration whose successive quotients are additive copies of $\mathbf F_3$, so it is a $3$-group. The prime-to-$3$ quotient is $\mathbf F_3^\times$, of order two. The global cyclotomic unit $-1$ maps to its nontrivial element. After quotienting by global units, no prime-to-$3$ part remains. $\square$

This elementary calculation is the only ray-class structure needed in the simple-factor proof. It also explains why a hidden quadratic layer over $K$ cannot occur at the prime above $3$.

### 5.5 The exact prime-to-three field exclusion

The ray calculation predicts that no prime-to-$3$ abelian layer supported only at $\lambda$ survives. The exact case needed below can be proved directly, so the classification does not depend on a general conductor-existence theorem.

**Proposition 5.3 (small prime-to-three exclusion).** Let $E/K$ be a nontrivial elementary abelian $r$-extension for a prime $r\ne3$. Assume it is unramified away from $\lambda$ and at most tamely ramified at $\lambda$. Then no such $E$ exists.

**Proof.** It is enough to take a degree-$r$ subextension. In a tame abelian extension of $K_\lambda$, whose residue field is $\mathbf F_3$, the ramification index divides $3-1=2$. If $r$ is odd, the degree-$r$ extension is therefore unramified also at $\lambda$. It is unramified at every finite prime, so

$$
\operatorname{rd}(E)=\operatorname{rd}(K)=\sqrt3.
$$

Minkowski's bound already exceeds $\sqrt3$ in every absolute degree at least four, and here $[E:\mathbf Q]=2r\ge10$. This is impossible.

It remains to take $r=2$. If $E/K$ is unramified at $\lambda$, the same argument applies. If it is ramified, the ramification is tame quadratic, so its relative discriminant is $\lambda$. The absolute discriminant formula gives

$$
|D_E|=|D_K|^2N(\lambda)=3^3=27,
\qquad
\operatorname{rd}(E)=27^{1/4}.
$$

The field $E$ is totally imaginary of degree four. Minkowski's inequality gives

$$
\operatorname{rd}(E)\ge
\left(
\left(\frac\pi4\right)^2\frac{4^4}{4!}
\right)^{1/2}
>2.56,
$$

whereas $27^{1/4}<2.28$. This contradiction finishes the proof. $\square$

Lemma 5.2 remains useful information rather than an unsupported bridge: it calculates the full prime-to-$3$ part of every $\lambda$-ray group. Proposition 5.3 independently proves the exact field nonexistence used in this book.

## 6. Classification of simple objects

### 6.1 A simple object has exponent three

Let $S$ be a nonzero simple object of $\mathcal S$. Multiplication by $3$ on $S$ has a nonzero generic kernel because $V(S)$ is a nonzero finite $3$-group. Close that kernel in $S$. Simplicity makes the closure all of $S$, so $[3]$ is zero on the generic fiber. Two maps between finite flat schemes which agree generically agree everywhere; hence

$$
[3]_S=0.
$$

Therefore $V(S)$ is a finite-dimensional $\mathbf F_3$-vector space. A nonzero stable subspace would close to a proper nonzero subobject, so $V(S)$ is irreducible. Let

$$
G=\operatorname{im}(G_{\mathbf Q}\to\operatorname{GL}(V(S))).
$$

The action is faithful by definition of its cutout field.

### 6.2 Solvability of the image

Chapter 4 gives $|G|\le33$. Every group of order at most thirty-three is solvable.

Here is a proof suited to the exact range. Groups of prime-power order are solvable because their centers are nontrivial and induction applies to the central quotient. For a mixed order at most $33$, the Sylow congruences show that the Sylow subgroup for the largest prime is normal except possibly at orders $12$, $24$, and $30$: the only possible orders are

$$
6,10,12,14,15,18,20,21,22,24,26,28,30,33,
$$

and the assertion is immediate from $n_p\equiv1\pmod p$ and $n_p\mid |G|/p$ outside those three exceptions. At order $12$ or $24$, the Sylow $3$-subgroup is either normal or there are four such subgroups. In the latter case conjugation on them gives a homomorphism to $S_4$. Its image is solvable, and its kernel, being of smaller order, is solvable by induction. At order $30$, if neither a Sylow $5$-subgroup nor a Sylow $3$-subgroup were normal, there would be six Sylow $5$-subgroups and ten Sylow $3$-subgroups. Their nonidentity elements are disjoint, giving $6\cdot4+10\cdot2=44$ nonidentity elements in a group of order $30$, a contradiction. A normal Sylow subgroup has solvable prime-power kernel and smaller solvable quotient. This completes the induction.

If $G$ were nontrivial and perfect, its derived series would never reach the identity, contradicting solvability. Thus a nontrivial $G$ has nontrivial abelianization.

### 6.3 The commutator subgroup

Lemma 5.1 shows that the field fixed by $[G,G]$ is $K=\mathbf Q(\zeta_3)$. Consequently

$$
G^{\mathrm{ab}}\simeq C_2,
\qquad
H:=[G,G],
\qquad
|H|\le16,
$$

unless $G$ is already trivial.

We claim that $H$ is a $3$-group. Suppose a prime $r\ne3$ divides $H^{\mathrm{ab}}$. Choose a quotient $H\twoheadrightarrow C_r$. Its kernel need not be normal in $G$, so intersect it with its conjugate under a lift of the nontrivial element of $G/H$. The resulting subgroup is normal in $G$ and gives a nontrivial elementary abelian $r$-extension $E/K$ which is Galois over $\mathbf Q$.

The polynomial $X^2+X+1$ of $\zeta$ remains irreducible modulo $2$, so $2$ is inert in $K$ and the residue field at its unique prime is $\mathbf F_4$. In a tame abelian local extension the ramification index divides $4-1=3$. Hence the $r$-extension is unramified there because $r\ne3$. At $\lambda$, a prime-to-$3$ quotient is at most tamely ramified. Proposition 5.3 excludes the resulting elementary abelian $r$-extension. This contradiction proves that $H^{\mathrm{ab}}$ is a $3$-group.

If $H\ne1$, solvability makes $H^{\mathrm{ab}}$ nontrivial. Since $|H|\le16$, only the orders $3$, $6$, $9$, $12$, and $15$ need attention. A group of order $6$ is cyclic or isomorphic to $S_3$, so its abelianization is not a nontrivial $3$-group. Every group of order $15$ is cyclic: the Sylow $5$-subgroup is normal, and the conjugation map from a Sylow $3$-subgroup to its automorphism group of order four is trivial. Thus order $15$ is also impossible.

At order $12$, if a Sylow $3$-subgroup were normal, the quotient of order four would be an abelian prime-to-$3$ quotient, impossible. Hence there are four Sylow $3$-subgroups. Counting their eight nonidentity elements leaves a normal set consisting of the identity and three elements of order two; it is the Klein four group, and $H$ is isomorphic to $A_4$. In that case $|G|=24$. But every odd-order subgroup of a group of order $24$ has order at most three, so the refined bound (4.1) would give $|G|\le20$, a contradiction. Therefore the order-$12$ case cannot occur. We conclude that $|H|$ is $3$ or $9$, and $H$ is a $3$-group.

### 6.4 Normal three-groups in characteristic three

**Lemma 6.1.** Let $P$ be a nontrivial finite $3$-group acting on a nonzero finite-dimensional $\mathbf F_3$-space $W$. Then $W^P\ne0$.

**Proof.** The center of $P$ contains an element $z$ of order $3$. In characteristic $3$,

$$
(z-1)^3=z^3-1=0,
$$

so $z-1$ is nilpotent and has nonzero kernel. The kernel $W^{\langle z\rangle}$ is stable under $P$ because $z$ is central. Apply induction to the action of $P/\langle z\rangle$ on its nonzero fixed space. $\square$

If $P\triangleleft G$, then $W^P$ is $G$-stable. On a simple $G$-module it is therefore all of $W$, so $P$ acts trivially. Apply this to the normal $3$-subgroup $H$. Faithfulness of the action forces $H=1$. Hence

$$
G=1\quad\text{or}\quad G=C_2.
$$

The irreducible module is one-dimensional, with character $1$ or the unique nontrivial mod-$3$ character. By Lemma 5.1 the latter is the cyclotomic character $\overline\chi_3$.

### 6.5 Identification of the two integral models

It remains to recover the integral group from its generic character. Over the unramified DVR $\mathbf Z_3$, the order-three Oort--Tate parameters $a,b$ satisfy

$$
ab=3u,
\qquad u\in\mathbf Z_3^\times.
$$

Their nonnegative valuations add to one. Thus the only possibilities are

$$
(v_3(a),v_3(b))=(0,1)
\quad\text{or}\quad(1,0).
$$

The first is etale and the second is of multiplicative type. The valuation alone does not discard possible unramified unit twists, so one more argument is required. In the etale case, henselian finite-etale descent says that the integral model is uniquely determined by its unramified generic character. The globally trivial character therefore has the constant model $C$. In the multiplicative case, Cartier duality turns the group into an etale order-three group whose generic character is

$$
\overline\chi_3\,\overline\chi_3^{-1}=1.
$$

Its dual is therefore constant, so the original group is $M$. The finite etale models at every other odd prime are already unique, and Hopf-order gluing identifies the global object. This argument uses both the Oort--Tate endpoint dichotomy and the generic character; the valuation pair by itself would not identify a twisted endpoint.

We have proved the central classification.

**Theorem 6.2 (simple objects).** Every simple object of $\mathcal S$ is isomorphic to exactly one of

$$
\underline{\mathbf Z/3\mathbf Z}
\qquad\text{and}\qquad
\mu_3.
$$

They are nonisomorphic because their special fibers at $3$ are respectively etale and connected. Cartier duality exchanges them.

## 7. Extension groups between the simple objects

### 7.1 What must be computed

Knowing the simple objects does not determine a nonsimple object. Four Yoneda groups control the first possible gluings:

$$
\operatorname{Ext}^1_{\mathcal S}(C,C),\quad
\operatorname{Ext}^1_{\mathcal S}(M,M),\quad
\operatorname{Ext}^1_{\mathcal S}(C,M),\quad
\operatorname{Ext}^1_{\mathcal S}(M,C).
$$

Our convention is that $\operatorname{Ext}^1(B,A)$ classifies sequences

$$
0\longrightarrow A\longrightarrow E\longrightarrow B\longrightarrow0.
$$

The order of the arguments is important. The Kummer extension has multiplicative subgroup and constant quotient, so it lies in $\operatorname{Ext}^1(C,M)$. The reverse group will vanish. This asymmetry is exactly what permits filtration rearrangement.

The Ext groups are groups under Baer sum. In the calculations below, the zero class is the split product. Isomorphisms of extensions are required to induce the identity on both named end terms.

### 7.2 Constant by constant

Consider

$$
0\longrightarrow C\longrightarrow E\longrightarrow C\longrightarrow0.
\tag{7.1}
$$

Over $\mathbf Z_3$, both end terms are finite etale. Since $E\to C$ is a torsor under the finite etale group $C$, the middle term is finite etale as well. Thus its generic Galois module is unramified at $3$. It is unramified at every odd $q\ne3$ because it extends over $R$.

The action on the two constant factors is trivial. If the middle group is killed by $3$, then in a basis adapted to (7.1), every Galois element acts by

$$
\begin{pmatrix}1&c(g)\\0&1\end{pmatrix},
$$

where $c:G_{\mathbf Q}\to\mathbf F_3$ is a continuous homomorphism if the middle group is killed by $3$. Its field would be a cyclic cubic extension unramified at every odd prime and at most tamely ramified at $2$. But an abelian tame extension of $\mathbf Q_2$ has ramification index dividing $2-1=1$, so it is also unramified at $2$. A nontrivial number field unramified at every finite prime cannot exist: its root discriminant would be $1$, contradicting Minkowski's discriminant bound. Hence $c=0$.

An extension need not be killed by $3$. Its abstract geometric-point group is either $C_3\times C_3$ or $C_9$. In both cases an automorphism inducing the identity on the named subgroup and quotient belongs to a group of order three. Thus any nontrivial Galois action again cuts out a cyclic cubic extension with precisely the ramification just excluded. The action is therefore trivial, and the middle group is the constant group attached to an extension of finite abelian groups

$$
0\to\mathbf Z/3\mathbf Z\to A\to\mathbf Z/3\mathbf Z\to0.
$$

There are two middle groups, the split group and $\mathbf Z/9\mathbf Z$. The latter represents a generator under Baer sum. Therefore

$$
\boxed{
\operatorname{Ext}^1_{\mathcal S}(C,C)\simeq\mathbf Z/3\mathbf Z,
}
\tag{7.2}
$$

generated by

$$
0\to C\xrightarrow{\,3\,}
\underline{\mathbf Z/9\mathbf Z}
\longrightarrow C\to0.
$$

### 7.3 Multiplicative by multiplicative

Cartier duality reverses an extension and exchanges $C$ with $M$. Dualizing a constant-by-constant extension again gives a multiplicative-by-multiplicative extension. Hence (7.2) yields

$$
\boxed{
\operatorname{Ext}^1_{\mathcal S}(M,M)\simeq\mathbf Z/3\mathbf Z,
}
\tag{7.3}
$$

generated by

$$
0\to\mu_3\longrightarrow\mu_9
\xrightarrow{(\cdot)^3}\mu_3\to0.
$$

The duality argument includes the integral structure at $3$; it is not merely a calculation with abstract generic modules.

### 7.4 Kummer extensions of constant by multiplicative

Now consider

$$
0\longrightarrow M\longrightarrow E\longrightarrow C\longrightarrow0.
\tag{7.4}
$$

Multiplication by $3$ on $E$ kills the subgroup and the quotient, so it factors as a morphism $C\to M$. Such a morphism is zero: on generic fibers it would be a map from the trivial character to the nontrivial cyclotomic character. Hence $E$ is killed by $3$. This is why one Kummer torsor, rather than an additional coefficient-extension class, captures the whole group.

Pull (7.4) back along the section $1\in C(R)$. Its inverse image is an $M$-torsor. Conversely, an $M$-torsor $P$ together with the canonical trivialization of its third contracted power constructs a cyclic extension of $C$ by $M$. This gives

$$
\operatorname{Ext}^1_{\mathcal S}(C,M)\simeq
H^1_{\mathrm{fppf}}(R,\mu_3).
\tag{7.5}
$$

There is no missing choice in this correspondence. In general, changing the trivialization of the contracted third power can contribute an element of $M(R)/3M(R)$. Here $\mu_3(R)=\{1\}$, because $R\subset\mathbf Q$ contains no nontrivial cube root of unity. Thus the torsor class determines the extension uniquely.

We make both directions explicit. Since $R$ is a principal ideal domain, $\operatorname{Pic}(R)=0$. The fppf Kummer sequence gives

$$
H^1(R,\mu_3)=R^\times/R^{\times3}.
$$

For $a\in R^\times$, define $E_a$ on a test $R$-algebra $T$ by pairs $(i,x)$, locally with

$$
i\in\{0,1,2\},
\qquad x^3=a^i.
$$

If $i+j=3k+r$ with $0\le r<3$, put

$$
(i,x)(j,y)=(r,xy/a^k).
$$

Then

$$
(xy/a^k)^3=a^{i+j-3k}=a^r,
$$

and the carry identity

$$
\left\lfloor\frac{i+j}{3}\right\rfloor
+\left\lfloor\frac{(i+j)\bmod3+k}{3}\right\rfloor
=
\left\lfloor\frac{j+k}{3}\right\rfloor
+\left\lfloor\frac{i+(j+k)\bmod3}{3}\right\rfloor
$$

proves associativity. The kernel over $i=0$ is $\mu_3$, and projection to $i$ gives a faithfully flat quotient to $C$. Each of the three components has coordinate algebra $R[X]/(X^3-a^i)$; because $a$ is a unit and the polynomial is monic, the total scheme is finite free of rank nine. Thus $E_a$ is a finite-flat extension.

Replacing $a$ by $ab^3$ and $x$ by $xb^i$ gives an isomorphic extension. Conversely, an isomorphism of extensions identifies the torsor over $1$ and hence its Kummer class. Baer sum multiplies $a$. This proves (7.5) without leaving an obstruction unexamined.

The units are

$$
R^\times=\{\pm2^m:m\in\mathbf Z\}.
$$

The sign contributes nothing because $-1=(-1)^3$. Consequently

$$
\boxed{
\operatorname{Ext}^1_{\mathcal S}(C,M)\simeq\mathbf Z/3\mathbf Z,
}
\tag{7.6}
$$

generated by $E_2$. Its generic splitting field is

$$
\mathbf Q(\zeta_3,\sqrt[3]{2}).
$$

At $2$ it has tame cubic inertia. At $3$, the class of $2$ is a unit class and (7.4) is finite flat. Thus the generator genuinely lies in $\mathcal S$.

### 7.5 Vanishing in the reverse direction

Consider the reverse extension

$$
0\longrightarrow C\longrightarrow E\longrightarrow M\longrightarrow0.
\tag{7.7}
$$

Here too $[3]_E$ factors through a morphism $M\to C$, which is zero on generic characters. Thus the middle group is killed by $3$, and its generic extension class is an ordinary $\mathbf F_3$-linear cohomology class.

The decisive fact is that (7.7) splits after base change to $\mathbf Z_3$.

**Lemma 7.1 (local reverse splitting).** Every finite-flat extension (7.7) over $\mathbf Z_3$ is split.

**Proof.** Use the connected--etale sequence of $E$ over the henselian DVR $\mathbf Z_3$. The constant subgroup $C$ is etale and the quotient $M$ has connected special fiber. The connected part $E^0$ cannot have rank one, because then the connected quotient $M$ would receive only the identity. It cannot have rank nine, because then the nontrivial etale subgroup $C$ would lie in a connected finite group. Hence $E^0$ has rank three.

More explicitly, the image of $E^0$ in $M$ is a connected subgroup. If it were trivial, the faithfully flat map $E\to M$ would factor on the special fiber through the finite etale component quotient of $E$; every homomorphism from a finite etale group to the connected group $\mu_3$ is trivial, contradicting surjectivity. Thus $E^0\to M$ is nontrivial and hence surjective, because $M$ has prime order. Its kernel is the connected group $E^0\cap C$, which is also a subgroup of the etale group $C$ and is therefore trivial. Rank multiplicativity now gives $|E^0|=|M|=3$.

The resulting faithfully flat morphism $E^0\to M$ has degree one and is an isomorphism. Its inverse supplies a section $M\to E$. $\square$

On generic fibers, extensions of $\mathbf F_3(1)$ by $\mathbf F_3$ are measured by

$$
H^1(\mathbf Q,\mathbf F_3(-1))
=H^1(\mathbf Q,\mathbf F_3(1)),
$$

because $\overline\chi_3^{-1}=\overline\chi_3$. Ramification outside $\{2,3\}$ restricts the Kummer class to

$$
\langle[2],[3]\rangle
\subset\mathbf Q^\times/\mathbf Q^{\times3}.
\tag{7.8}
$$

The two classes remain independent in $\mathbf Q_3^\times/\mathbf Q_3^{\times3}$. The valuation separates $[3]$ from the unit classes. For $[2]$, use the same cube class $[-2]$, since $-1$ is a cube. We have $-2=1-3$. Every cube of a unit congruent to $1$ modulo $3$ is congruent to $1$ modulo $9$, whereas $-2\equiv7\pmod9$. Thus $[2]$ is nonzero. The square class $[4]$ is also nonzero, since cubes of units modulo $9$ are $\pm1$ and $4$ is neither. This proves independence.

Lemma 7.1 says that the localization of the global class in (7.8) is zero. Independence makes both coefficients zero. Therefore the generic extension splits, and faithfulness of the generic-fiber functor makes the integral extension split.

We have proved

$$
\boxed{
\operatorname{Ext}^1_{\mathcal S}(M,C)=0.
}
\tag{7.9}
$$

### 7.6 The complete extension table

The four calculations are summarized by

$$
\begin{array}{c|cc}
\operatorname{Ext}^1(B,A)&B=C&B=M\\
\hline
A=C&\mathbf F_3\,[\underline{\mathbf Z/9}]&0\\
A=M&\mathbf F_3\,[E_2]&\mathbf F_3\,[\mu_9].
\end{array}
\tag{7.10}
$$

The entries label generators, not direct-product decompositions of every middle object. In particular, $E_2$ is a nonsplit mixed extension. The single zero in the upper-right corner is the engine of the sorting argument, while the lower-left Kummer class is the reason the final representation need not be semisimple.

## 8. Ray and Kummer calculations through all levels

### 8.1 Units of $\mathbf Z[1/2]$

The level-three Ext table is only the first layer of the all-level theory. The units of $R$ have the particularly simple form

$$
R^\times=\mu_2\times2^{\mathbf Z}.
$$

For every $n\ge1$, Kummer theory and $\operatorname{Pic}(R)=0$ give

$$
H^1(R,\mu_{3^n})\simeq
R^\times/R^{\times3^n}\simeq\mathbf Z/3^n\mathbf Z,
\tag{8.1}
$$

with generator $[2]$. The group $\mu_2$ disappears because raising to the odd power $3^n$ is an automorphism of it.

This calculation has two consequences. There is exactly one compatible $3$-adic direction for extensions of the constant divisible group by the multiplicative divisible group, and every finite-level class is represented by a power $2^a$ with $a$ well defined modulo $3^n$.

### 8.2 Local cube classes at three

The local multiplicative group decomposes as

$$
\mathbf Q_3^\times
\simeq3^{\mathbf Z}\times\mu_2\times(1+3\mathbf Z_3).
$$

Modulo cubes, the first and third factors each contribute one $\mathbf F_3$-dimension, while $\mu_2$ contributes none. Thus

$$
\mathbf Q_3^\times/\mathbf Q_3^{\times3}
\simeq\mathbf F_3[3]\oplus\mathbf F_3[2].
\tag{8.2}
$$

The valuation proves that $[3]$ is nonzero. The congruence calculation of §7.5 proves that the unit $[2]=[-2]$ is nonzero. These two tests also show directly that the global localization map on the span of $[2],[3]$ is injective.

For finite-flat extensions of $C$ by $M$ over $\mathbf Z_3$, the Kummer parameter must be a unit. The valuation class $[3]$ produces a torsor whose integral closure has the wrong flat connected--etale behavior. Therefore the local finite-flat line is exactly the unit line $\mathbf F_3[2]$. This is why the residual global extension can retain $[2]$ but not $[3]$.

### 8.3 Cyclotomic units and the cubic ray direction

Over $K=\mathbf Q(\zeta_3)$, the prime $2$ is inert because $X^2+X+1$ is irreducible over $\mathbf F_2$. Its residue field is $\mathbf F_4$, whose multiplicative group has order three. Hence the unique tame cubic inertia direction at the prime over $2$ is already visible in the reduction of units.

At $\lambda=1-\zeta$, the global cyclotomic units $\mu_6$ map onto the prime-to-three residue units, as proved in Lemma 5.2. The remaining ray filtration

$$
(1+\lambda^j)/(1+\lambda^{j+1})
$$

is additive of order three. Herbrand theory explains how these integral unit layers correspond to upper ramification layers: local reciprocity carries $1+\lambda^j$ to the $j$th upper ramification subgroup in the abelian quotient. In the present finite-flat problem the upper cutoff at $1/2$ kills every positive integral abelian break at $3$, so none of these positive ray layers can occur in an abelian quotient of an exponent-three field.

At the prime over $2$, the class of the rational unit $2$ is a uniformizer rather than a local unit. Kummer theory over $K$, which contains $\mu_3$, gives the cubic extension $K(\sqrt[3]{2})/K$. It is totally tamely ramified at that prime and unramified away from it and $\lambda$; at $\lambda$ the fact that $2$ is a $3$-adic unit gives the finite-flat extension. This is the unique mixed Ext direction found in (7.6).

### 8.4 Higher Kummer levels

For $n\ge1$, consider an extension

$$
0\to\mu_{3^n}\to E\to
\underline{\mathbf Z/3^n\mathbf Z}\to0
\tag{8.3}
$$

which is killed by $3^n$. Pulling back over $1\in\underline{\mathbf Z/3^n\mathbf Z}(R)$ gives a $\mu_{3^n}$-torsor. Conversely, repeated contracted products of such a torsor give the fibers over all residue classes, and the group law is the carry law of §7.4 with $3$ replaced by $3^n$. The contracted $3^n$th power needs a trivialization. Two trivializations differ by $\mu_{3^n}(R)$, which is trivial because $R\subset\mathbf Q$ contains no nontrivial $3$-power root of unity. Thus pullback over $1$ gives a bijection

$$
\operatorname{Ext}^1_{[3^n]=0}
\left(\underline{\mathbf Z/3^n\mathbf Z},\mu_{3^n}\right)
\simeq H^1(R,\mu_{3^n})
\simeq R^\times/R^{\times3^n}.
\tag{8.3a}
$$

The killed-by-$3^n$ qualification is automatic for the levels of a $3$-divisible extension. Indeed, multiplication by $3^n$ on the middle term factors through a morphism from the constant quotient to the multiplicative subgroup. Such a morphism is zero: on generic fibers the image of $1$ would be a rational $3$-power root of unity, and $\mathbf Q$ has no nontrivial one of any order. Hence every finite level in the all-level application is represented by a Kummer class

$$
q\in R^\times/R^{\times3^n}.
$$

Compatibility under multiplication by $3$ sends the class modulo $3^{n+1}$ to its reduction modulo $3^n$. By (8.1), a compatible system is an element

$$
a\in\varprojlim_n\mathbf Z/3^n\mathbf Z=\mathbf Z_3,
$$

and its level-$n$ parameter is $2^{a_n}$, where $a_n$ is the image of $a$ modulo $3^n$.

No additional class appears at infinite level. The sign is uniquely divisible by odd powers, the Picard group is zero, and the inverse system in (8.1) has surjective transition maps, so there is no inverse-limit obstruction. Equation (8.3a) proves both surjectivity and injectivity of the parameter: it is not merely a construction of some examples.

### 8.5 The one-motive model

The compatible extension can be written without choosing roots. For $q\in R^\times$, consider the homomorphism

$$
\mathbf Z\longrightarrow\mathbf G_m,
\qquad1\longmapsto q.
$$

Its $3^n$-torsion group $E_q[3^n]$ consists fppf-locally of pairs

$$
(i,x),\qquad
i\in\mathbf Z/3^n\mathbf Z,\qquad
x^{3^n}=q^i,
$$

with the same carry law used in §7.4. It fits into

$$
0\to\mu_{3^n}\to E_q[3^n]
\to\underline{\mathbf Z/3^n\mathbf Z}\to0.
\tag{8.4}
$$

Multiplication by $3$ maps level $n+1$ faithfully flatly onto level $n$, with kernel the level-one group. Hence the system defines a $3$-divisible group of height two. For $q=2$, every finite level lies in $\mathcal S$: it is finite flat at $3$, unramified at odd primes other than $3$, and has tame $3$-power inertia at $2$. Its residual inertia also has the familiar square-zero form, although the definition of $\mathcal S$ requires only odd tameness.

This family shows that the eventual filtration theorem is sharp. It cannot be strengthened to a product decomposition.

## 9. Filtration rearrangement

### 9.1 Why a composition series is not enough

A composition series labels every interval by $C$ or $M$, but the labels can occur in any order. To deduce a stable cyclotomic subobject, all multiplicative intervals must be moved below all constant intervals. This is not a formal Jordan--Holder argument: exchanging adjacent factors changes an extension, and the exchange is possible only because one mixed Ext group vanishes.

Call an adjacent pair an **inversion** if a constant factor lies below a multiplicative factor. Thus an inversion is represented by a subquotient fitting into

$$
0\to C\to X\to M\to0.
$$

### 9.2 Swapping one inversion

By (7.9), the displayed extension splits. Hence

$$
X\simeq C\times M.
$$

Inside $X$, replace the lower subgroup $C$ by the other direct factor $M$. Pull this replacement back to the relevant term of the original filtration. Saturated closure ensures that the new generic subgroup is an integral finite-flat subgroup, and represented quotients give a new admissible composition series. The two adjacent factors have been exchanged, while every other interval is unchanged.

The splitting is global. A local splitting at $3$ alone would not justify the exchange over $R$; §7.5 used the global Kummer calculation to prove that the entire extension class vanishes.

### 9.3 The sorting theorem

Define the inversion number of a labeled composition series to be the number of pairs $(i,j)$ with $i<j$, the $i$th factor constant, and the $j$th factor multiplicative. Swapping an adjacent inversion decreases this nonnegative integer by one and creates no new inversion. Repetition terminates.

**Theorem 9.1 (filtration rearrangement).** Every $G\in\mathcal S$ has a composition series in which all $M$-factors occur below all $C$-factors.

**Proof.** Start with the series of §3.6. If it has an inversion, choose two oppositely labeled factors with minimal distance. All factors between them have the same label as one endpoint, so successive adjacent swaps reduce their distance; at the final step §9.2 swaps the adjacent inversion. Equivalently, apply the inversion-number procedure directly. Since the length is finite, the process ends in a sorted series. Every replacement uses an admissible saturated subobject and quotient, so the final series remains in $\mathcal S$. $\square$

### 9.4 Pure constant and pure multiplicative blocks

Let $H$ be an object all of whose simple factors are $C$. We prove by induction on its length that $H$ is a constant group scheme. Choose a constant simple quotient with kernel $H'$. By induction $H'$ is constant. Filter $H'$ by cyclic constant groups and repeatedly use the constant-by-constant calculation: no Galois cocycle survives, and the only nonsplit classes enlarge the abstract finite abelian $3$-group, as $\mathbf Z/9$ enlarged $\mathbf Z/3$. Thus $H$ is the constant group attached to some finite abelian $3$-group.

More explicitly, its generic Galois action is a finite $3$-group acting unipotently. If nontrivial, its abelianization has a $C_3$ quotient, producing a cyclic cubic extension unramified at every odd prime and at most tamely ramified at $2$. The argument of §7.2 rules this out. Hence the action is trivial. The finite etale model over every localization is then constant, and Hopf-order uniqueness makes $H$ constant over $R$.

Cartier duality gives the parallel assertion: an object all of whose factors are $M$ is of multiplicative type, the dual of a constant finite abelian $3$-group. If the constant dual is

$$
\prod_i\mathbf Z/3^{a_i}\mathbf Z,
$$

then the multiplicative group is

$$
\prod_i\mu_{3^{a_i}}.
$$

### 9.5 Existence and uniqueness of the two-step filtration

In a sorted composition series, let $G^{\mathrm m}$ be the term immediately after the last multiplicative factor; take it to be zero if no such factor occurs. The preceding section makes it multiplicative, and the quotient $G^{\mathrm c}=G/G^{\mathrm m}$ constant. Thus

$$
0\longrightarrow G^{\mathrm m}\longrightarrow G
\longrightarrow G^{\mathrm c}\longrightarrow0.
\tag{9.1}
$$

This subgroup is independent of the chosen sorted series. Indeed, any morphism from a multiplicative-type object to a constant object is zero. After base change to $\mathbf Z_3$, it factors through the maximal etale quotient of its source. The source has connected special fiber, so that quotient is trivial; hence the localized morphism is zero. Its generic fiber is consequently zero, and faithfulness of the global generic-fiber functor makes the original morphism zero. Therefore every multiplicative subgroup of $G$ maps trivially to $G^{\mathrm c}$ and lies in $G^{\mathrm m}$. Hence $G^{\mathrm m}$ is the unique maximal multiplicative subgroup. Dually, $G^{\mathrm c}$ is the unique maximal constant quotient.

**Theorem 9.2 (multiplicative--constant filtration).** Every object of $\mathcal S$ has the canonical exact sequence (9.1). Formation of this sequence is functorial for morphisms in $\mathcal S$ and compatible with Cartier duality, which exchanges the filtration with its quotient-dual filtration.

The sequence need not split. Its first nonsplit layer is $E_2$, and its compatible higher layers are the Kummer systems of Chapter 8.

## 10. Finite coefficient levels

### 10.1 Coefficient actions and stable cuts

Let $A$ be a finite local quotient of the integers in a finite extension of $\mathbf Q_3$, and let $W$ be free of rank two over $A$. Suppose

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_A(W)
$$

has an underlying finite group scheme in $\mathcal S$, and suppose the $A$-action extends to its model. We assume

$$
\det\rho=\chi_3,
\tag{10.1}
$$

where the cyclotomic character is reduced to $A^\times$.

The subgroup $G^{\mathrm m}$ from Theorem 9.2 need not initially be an $A$-direct summand. A scalar endomorphism carries multiplicative subgroups to multiplicative subgroups, so maximality makes $G^{\mathrm m}$ stable under $A$. Its generic points therefore give an $A$-submodule. There is nevertheless a more intrinsic submodule which directly yields the trace identity.

### 10.2 The canonical image submodule

Define

$$
N=\sum_{g\in G_{\mathbf Q}}(\rho(g)-1)W.
\tag{10.2}
$$

Although the displayed sum ranges over a profinite group, it is an ordinary finite $A$-submodule: $W$ is noetherian, so the increasing family of submodules generated by finite subsets stabilizes. No topological completion is hidden in (10.2).

This is an $A$-submodule, and it is Galois-stable because

$$
\rho(h)(\rho(g)-1)
=(\rho(hgh^{-1})-1)\rho(h).
$$

The constant quotient in (9.1) has trivial Galois action, so every $(\rho(g)-1)W$ lies in the generic points of $G^{\mathrm m}$. Therefore $N\subseteq V(G^{\mathrm m})$. By definition, the action on $W/N$ is trivial.

On a multiplicative-type $3$-primary group, Galois acts on geometric points by the cyclotomic character: this is clear on each $\mu_{3^a}$ and hence on their products. Thus

$$
\rho(h)x=\chi_3(h)x
\qquad(x\in N).
\tag{10.3}
$$

### 10.3 The cross relation

Combining (10.2) and (10.3) gives, for all $g,h\in G_{\mathbf Q}$,

$$
\boxed{
(\rho(h)-\chi_3(h))(\rho(g)-1)=0.
}
\tag{10.4}
$$

This is stronger than a statement about semisimplification. It controls the off-diagonal extension because the image of every augmentation operator lies in the cyclotomic block.

The determinant condition now identifies the scalar in (10.4) intrinsically. Without (10.1), the same argument gives cyclotomic action on $N$, but it would not turn into a formula involving $\det\rho$.

### 10.4 The trace identity

Fix $g$ and put

$$
f=\rho(g),
\qquad d=\det f=\chi_3(g).
$$

Taking $h=g$ in (10.4) gives

$$
(f-d)(f-1)=0,
$$

or

$$
f^2-(1+d)f+d=0.
\tag{10.5}
$$

Cayley--Hamilton on the free rank-two $A$-module $W$ gives

$$
f^2-(\operatorname{tr}f)f+d=0.
\tag{10.6}
$$

Subtracting (10.5) from (10.6) yields

$$
(\operatorname{tr}f-1-d)f=0.
$$

The matrix $f$ is invertible, so the scalar is zero in $A$. We have proved

**Theorem 10.1 (finite-level Schoof identity).** Under the hypotheses of §10.1,

$$
\boxed{
\operatorname{tr}\rho(g)=1+\det\rho(g)
=1+\chi_3(g)
}
$$

for every $g\in G_{\mathbf Q}$.

No freeness of $N$ or $W/N$ was used. That is important at an isolated finite coefficient level, where a canonical submodule can have torsion quotient.

### 10.5 The residual orientation and its Kummer class

Suppose now $A=\mathbf F_3$ and $W$ has dimension two. The subspace $N$ is neither zero nor all of $W$. If $N=0$, the action is trivial and its determinant is $1$, contradicting the nontrivial cyclotomic determinant. If $N=W$, (10.3) makes every $\rho(g)$ the scalar $\overline\chi_3(g)$; its determinant would be $\overline\chi_3(g)^2=1$. Complex conjugation has cyclotomic value $-1$, again a contradiction.

Thus $N$ is a line, and

$$
0\longrightarrow\mathbf F_3(1)
\longrightarrow W\longrightarrow\mathbf F_3\longrightarrow0.
\tag{10.7}
$$

Its global extension class lies in the span $\mathbf F_3[2]\oplus\mathbf F_3[3]$. Finite flatness at $3$ restricts it to the unit line, so

$$
[W]=a[2]
\qquad\text{for a unique }a\in\mathbf F_3.
\tag{10.8}
$$

The two cases $a=0$ and $a\ne0$ are both possible. When $a\ne0$, the residual field contains $\mathbf Q(\zeta_3,\sqrt[3]{2})$. The theorem orients the extension but does not falsely declare it split.

## 11. All-level devissage

### 11.1 Compatible finite-flat levels

Let $T$ be a free rank-two $\mathbf Z_3$-module with continuous $G_{\mathbf Q}$-action. Put

$$
T_n=T/3^nT.
$$

Assume for every $n\ge1$:

- $T_n$ is the generic module of an object $G_n\in\mathcal S$;
- the transition $T_{n+1}\twoheadrightarrow T_n$ is the generic fiber of the compatible coefficient reduction;
- $\det T=\chi_3$.

The full field $\mathbf Q(T_n)$ has a root-discriminant bound growing with $n$; we do not apply either residual ceiling to it. Instead, composition factors and first-order exchanges are killed by $3$, so Chapters 4--9 apply separately at each devissage step. This is the fixed-exponent mechanism that avoids the cyclotomic-tower counterexample.

### 11.2 Passage to a stable lattice

At level $n$, define

$$
N_n=\sum_g(\rho_n(g)-1)T_n.
$$

Reduction carries $N_{n+1}$ onto $N_n$: each generator reduces to the corresponding generator, and every generator downstairs lifts. Hence the inverse limit

$$
N=\varprojlim_nN_n
$$

embeds in $T$. To identify it without hiding a completion, first form the ordinary algebraic submodule

$$
N^{\mathrm{alg}}=\sum_g(\rho(g)-1)T.
$$

Because $T$ is a noetherian $\mathbf Z_3$-module, finitely many augmentation images generate $N^{\mathrm{alg}}$. It is therefore finitely generated and $3$-adically closed. Its image in $T_n$ is exactly $N_n$: one inclusion is immediate, while every generator of $N_n$ is the reduction of the corresponding generator upstairs. Completeness and separatedness now give

$$
N^{\mathrm{alg}}
\simeq\varprojlim_n N^{\mathrm{alg}}/(N^{\mathrm{alg}}\cap3^nT)
=\varprojlim_nN_n.
$$

We henceforth write this common submodule as

$$
N=\sum_g(\rho(g)-1)T.
$$

Passing (10.4) through the inverse limit gives

$$
(\rho(h)-\chi_3(h))(\rho(g)-1)=0
\qquad(g,h\in G_{\mathbf Q})
\tag{11.1}
$$

on $T$. Thus $G_{\mathbf Q}$ acts trivially on $T/N$ and cyclotomically on $N$.

### 11.3 The integral cyclotomic line

The residual calculation shows that $N_1$ is a one-dimensional subspace of $T/3T$. Therefore $N$ is nonzero and is not contained in $3T$. As a submodule of the free module $T$, it is torsion-free. Its rank cannot be two: tensoring (11.1) with $\mathbf Q_3$ would then make the whole representation scalar cyclotomic, contradicting the determinant at complex conjugation. Its rank is therefore one.

Because $N$ contains an element not divisible by $3$ in $T$, it is primitive. Extend such an element to a basis of $T$; this proves that $T/N$ is torsion-free of rank one. Equation (11.1) identifies the two actions. Consequently

$$
N\simeq\mathbf Z_3(1),
\qquad
T/N\simeq\mathbf Z_3.
$$

The identifications are noncanonical as module identifications, but their characters are canonical.

### 11.4 The three-adic conclusion

**Theorem 11.1 (Schoof's three-adic conclusion).** Let $T$ satisfy the hypotheses of §11.1. Then there is a $G_{\mathbf Q}$-stable exact sequence

$$
\boxed{
0\longrightarrow\mathbf Z_3(1)
\longrightarrow T\longrightarrow\mathbf Z_3
\longrightarrow0.
}
\tag{11.2}
$$

For every $g\in G_{\mathbf Q}$,

$$
\operatorname{tr}(g|T)=1+\chi_3(g),
\qquad
\det(g|T)=\chi_3(g).
\tag{11.3}
$$

After tensoring with $\mathbf Q_3$,

$$
(T\otimes\mathbf Q_3)^{\mathrm{ss}}\simeq
\mathbf Q_3\oplus\mathbf Q_3(1).
\tag{11.4}
$$

**Proof.** Sections 11.2--11.3 prove (11.2). The action on the submodule and quotient gives (11.3). Exactness after tensoring gives a two-step representation with those one-dimensional constituents, so its semisimplification is (11.4). $\square$

One can also recover (11.4) from traces: the finite-level identity passes to $\mathbf Z_3$, and the characteristic-zero semisimple representation with trace $1+\chi_3$ and determinant $\chi_3$ has the same character as $\mathbf Q_3\oplus\mathbf Q_3(1)$. The explicit line in (11.2) is stronger.

### 11.5 $3$-divisible groups in the category

Suppose a compatible system $(G_n)$ satisfies

$$
0\to G_n\to G_{n+m}\xrightarrow{3^n}G_m\to0
$$

and suppose that $V(G_n)$ is free of rank two over $\mathbf Z/3^n\mathbf Z$, with compatible coefficient action and determinant $\chi_3$. In particular, $|G_n|=3^{2n}$. The system defines a $3$-divisible group $G$ of height two over $R$. Applying the canonical filtration at every level and using functoriality makes the multiplicative subgroups compatible.

We spell out the height assertion, since unrelated levelwise filtrations would not suffice. Multiplication by $3^n$ sends $G_{n+m}^{\mathrm m}$ into $G_m^{\mathrm m}$ by functoriality. The induced map is faithfully flat. To see this, its generic cokernel is simultaneously a quotient of a multiplicative-type group and a subgroup of the constant group $G_m/G_m^{\mathrm m}$; it must vanish because every morphism from a multiplicative-type object to a constant object vanishes. Its kernel is the maximal multiplicative subgroup of $G_n$, hence $G_n^{\mathrm m}$. Thus

$$
0\longrightarrow G_n^{\mathrm m}\longrightarrow
G_{n+m}^{\mathrm m}\xrightarrow{3^n}G_m^{\mathrm m}
\longrightarrow0
$$

is exact, and the constant quotients satisfy the parallel exact sequence.

At level one, the determinant argument of §10.5 gives exactly one $M$-factor and one $C$-factor. Exact divisibility and rank multiplicativity now give inductively

$$
|G_n^{\mathrm m}|=3^n,
\qquad
|G_n/G_n^{\mathrm m}|=3^n.
$$

The two compatible systems therefore have height one. Passing to the fppf colimit gives

$$
0\longrightarrow\mu_{3^\infty}
\longrightarrow G\longrightarrow\mathbf Q_3/\mathbf Z_3
\longrightarrow0.
\tag{11.5}
$$

After choosing compatible identifications of the height-one ends with $\mu_{3^\infty}$ and $\mathbf Q_3/\mathbf Z_3$, the framed extension classes form the inverse limit (8.1), hence are parameterized by $a\in\mathbf Z_3$. Changing generators of an end changes this coordinate by the corresponding $3$-adic unit, so the coordinate is not intrinsic to an unframed middle group. The value $a=0$ gives the split divisible group. With the standard generators, $a=1$ gives the one-motive extension attached to $2$, and general $a$ is its $3$-adic Baer multiple. Thus the all-level devissage classifies not only the rational constituents but also the single integral extension direction allowed by the category.

## 12. Examples and boundary cases

### 12.1 The split object

The product

$$
\mu_{3^n}\times\underline{\mathbf Z/3^n\mathbf Z}
$$

lies in $\mathcal S$. It is finite flat at $3$, unramified at $2$, and its generic determinant is $\chi_3$ when regarded as a rank-two module over $\mathbf Z/3^n\mathbf Z$. The canonical multiplicative--constant sequence is the evident product sequence, and

$$
\operatorname{tr}(g)=1+\chi_3(g)
$$

holds by inspection.

### 12.2 The Kummer object attached to two

For $q=2$, the one-motive groups $E_2[3^n]$ of §8.5 give nonsplit sequences

$$
0\to\mu_{3^n}\to E_2[3^n]
\to\underline{\mathbf Z/3^n\mathbf Z}\to0.
$$

At $2$, choose a compatible $3^n$th root of $2$. Tame inertia multiplies it by a $3^n$th root of unity, so in a basis adapted to the exact sequence the matrix is

$$
\begin{pmatrix}
\chi_3(\sigma)&c_2(\sigma)\\
0&1
\end{pmatrix}.
$$

On the residual level, $(\sigma-1)^2=0$ and the nontrivial inertia image has order three. At $3$, the parameter $2$ is a unit, so the Kummer torsors extend finite flatly. The example satisfies every hypothesis and remains nonsplit at all levels compatible with the nonzero parameter in $\mathbf Z_3$.

### 12.3 Why the residual field need not split

At level one the nonsplit Kummer object cuts out

$$
L=\mathbf Q(\zeta_3,\sqrt[3]{2}).
$$

Its Galois group is $S_3$. The normal cubic subgroup acts trivially on every simple $\mathbf F_3[S_3]$-module, so the simple factors are still $1$ and $\overline\chi_3$. This example reconciles the simple-object theorem with the existence of a nonabelian residual field.

Its root discriminant lies below the refined two-prime ceiling and its degree is six, well within the degree-$20$ cutoff. The analytic argument was never meant to eliminate this field. Its role is to exclude large images so that the solvable and ray calculations can classify factors; the Ext calculation then records the surviving small field rather than discarding it.

### 12.4 What fails without the local hypotheses

Each assumption has a distinct job.

If finite flatness at $3$ is removed, the Kummer class $[3]$ survives in (10.8), positive upper breaks need not stop at $1/2$, and the root-discriminant ceiling fails. If the wild inertia at $2$ is allowed, its different contribution is not tame. If odd tameness is retained but cubic inertia is not known, the broad degree-$33$ bound remains valid, while the refined degree-$20$ comparison is available only when the inertia order is at most three.

If ramification at another odd prime $q$ is allowed, a new factor $q^{d_q/e_q}$ enters the discriminant and new Kummer generators enter $R^\times/R^{\times3}$. For example, replacing $R$ by $\mathbf Z[1/2q]$ adds the class $[q]$ and generally enlarges $\operatorname{Ext}^1(C,M)$. The vanishing of the reverse Ext group must then be recalculated; it is not formal.

Potential finite flatness at $3$ is also insufficient. The Hopf-order gluing theorem needs a model over $\mathbf Z_3$, and the finite-flat ramification constant is normalized over that actual base. A model obtained only after ramified scalar extension can have different descent and ramification behavior.

Finally, the full fields $\mathbf Q(T/3^nT)$ do not have one uniform root-discriminant ceiling. The safe bound grows with $n$, as the cyclotomic tower already demonstrates. The proof succeeded because every simple factor and every adjacent exchange returned to an exponent-three object over the fixed base.

### 12.5 Conclusion

The category over $\mathbf Z[1/2]$ now carries all three parts of Schoof's argument in one structure. Intersections of local Hopf orders turn a generic representation with an actual model at $3$ into a global finite-flat group. Saturated closure, represented quotients, and Cartier duality make the resulting collection an exact environment in which composition series are legitimate. Bounded tame inertia at $2$ and finite-flat ramification at $3$ give the strict ceiling

$$
2\cdot3^{3/2},
$$

and the explicit discriminant lower bound forces every exponent-three cutout field to have degree at most thirty-three. Cubic inertia sharpens the ceiling to $3^{3/2}2^{2/3}$ and the degree to twenty; that refinement removes the sole $A_4$ commutator case left by the broad estimate.

That finite arena makes the simple-factor classification possible. Herbrand quotient compatibility and Hasse--Arf integrality remove positive abelian depth at $3$; the tame-character calculation removes abelian ramification at $2$ over the rationals; the explicit ray calculation over $\mathbf Q(\zeta_3)$ has no prime-to-three quotient. Solvability and the fixed-point lemma for normal $3$-groups then leave exactly the constant group $C$ and the multiplicative group $M$.

The extension table supplies the finer answer that semisimplification alone misses. Same-type factors build constant groups and their multiplicative duals. The reverse mixed extension vanishes, so every filtration can be sorted. The forward mixed extension is one-dimensional and generated by the Kummer class of $2$, so the sorted filtration need not split. Through all levels that class becomes a single $\mathbf Z_3$-parameter.

Consequently every compatible rank-two object with cyclotomic determinant contains an integral cyclotomic line and has constant quotient:

$$
0\longrightarrow\mathbf Z_3(1)
\longrightarrow T\longrightarrow\mathbf Z_3
\longrightarrow0.
$$

This is Schoof's three-adic conclusion in its precise form. It retains the exceptional nonsplit Kummer object, handles the endpoints at both primes, and identifies exactly why every possible simple or extension layer remains inside the earlier arithmetic bounds.
