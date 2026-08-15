# Faithfully Flat Descent in Algebraic Geometry

## Contents

1. [Why descent is possible](#1-why-descent-is-possible)
   - [Local descriptions and global objects](#11-local-descriptions-and-global-objects)
   - [Faithful flatness](#12-faithful-flatness)
   - [The geometric meaning](#13-the-geometric-meaning)
   - [A first warning about hypotheses](#14-a-first-warning-about-hypotheses)
2. [The fpqc and fppf covering theories](#2-the-fpqc-and-fppf-covering-theories)
   - [Covering families](#21-covering-families)
   - [Single covers and affine reduction](#22-single-covers-and-affine-reduction)
   - [Infinite families and size](#23-infinite-families-and-size)
   - [Stability and refinement](#24-stability-and-refinement)
3. [The algebraic engine](#3-the-algebraic-engine)
   - [Tensor products detect exactness](#31-tensor-products-detect-exactness)
   - [The Amitsur equalizer](#32-the-amitsur-equalizer)
   - [Purity and descent tests](#33-purity-and-descent-tests)
   - [Examples and failures](#34-examples-and-failures)
4. [Cech nerves and descent data](#4-cech-nerves-and-descent-data)
   - [The nerve of a cover](#41-the-nerve-of-a-cover)
   - [Objects, isomorphisms, and cocycles](#42-objects-isomorphisms-and-cocycles)
   - [Morphisms and full faithfulness](#43-morphisms-and-full-faithfulness)
   - [Families and indices](#44-families-and-indices)
5. [Effective descent for modules](#5-effective-descent-for-modules)
   - [The invariant module](#51-the-invariant-module)
   - [Proof of effectivity](#52-proof-of-effectivity)
   - [Morphisms and exact sequences](#53-morphisms-and-exact-sequences)
   - [Base change and transitivity](#54-base-change-and-transitivity)
6. [Finiteness, flatness, and projectivity](#6-finiteness-flatness-and-projectivity)
   - [Finite generation and finite presentation](#61-finite-generation-and-finite-presentation)
   - [Flat modules](#62-flat-modules)
   - [Finite projective modules](#63-finite-projective-modules)
   - [Rank and related invariants](#64-rank-and-related-invariants)
7. [Algebras and affine schemes](#7-algebras-and-affine-schemes)
   - [Descent of algebra structures](#71-descent-of-algebra-structures)
   - [Quotients and equations](#72-quotients-and-equations)
   - [Affine descent](#73-affine-descent)
   - [Finite and finite locally free affine schemes](#74-finite-and-finite-locally-free-affine-schemes)
8. [Quasi-coherent sheaves](#8-quasi-coherent-sheaves)
   - [Pullback data on a cover](#81-pullback-data-on-a-cover)
   - [Affine-local construction](#82-affine-local-construction)
   - [Effectivity and full faithfulness](#83-effectivity-and-full-faithfulness)
   - [Coherence and exactness](#84-coherence-and-exactness)
9. [Line bundles and vector bundles](#9-line-bundles-and-vector-bundles)
   - [Descent of local freeness](#91-descent-of-local-freeness)
   - [Transition matrices and cocycles](#92-transition-matrices-and-cocycles)
   - [Determinants, sections, and forms](#93-determinants-sections-and-forms)
   - [Why local triviality is not descent data](#94-why-local-triviality-is-not-descent-data)
10. [Morphisms and properties local on the base](#10-morphisms-and-properties-local-on-the-base)
    - [Descent of maps](#101-descent-of-maps)
    - [The diagonal method](#102-the-diagonal-method)
    - [A table of descending properties](#103-a-table-of-descending-properties)
    - [Proofs of the principal cases](#104-proofs-of-the-principal-cases)
    - [Descent along a cover of the source](#105-descent-along-a-cover-of-the-source)
11. [Effective descent and the scheme boundary](#11-effective-descent-and-the-scheme-boundary)
    - [The fpqc equalizer and the algebraic-space boundary](#111-the-fpqc-equalizer-and-the-algebraic-space-boundary)
    - [Why the scheme assertion fails](#112-why-the-scheme-assertion-fails)
    - [The invariant-affine criterion](#113-the-invariant-affine-criterion)
    - [The first scheme cases](#114-the-first-scheme-cases)
12. [Finite-flat group objects and actions](#12-finite-flat-group-objects-and-actions)
    - [Group laws descend](#121-group-laws-descend)
    - [Hopf-algebra form](#122-hopf-algebra-form)
    - [Subgroups, homomorphisms, and exactness](#123-subgroups-homomorphisms-and-exactness)
    - [Actions and quotients in the finite case](#124-actions-and-quotients-in-the-finite-case)
13. [Torsors](#13-torsors)
    - [The torsor identity](#131-the-torsor-identity)
    - [Local triviality and effectivity](#132-local-triviality-and-effectivity)
    - [Contracted products and twisting](#133-contracted-products-and-twisting)
    - [Examples and boundary cases](#134-examples-and-boundary-cases)
14. [Quasi-affine descent](#14-quasi-affine-descent)
    - [Intrinsic affine envelopes](#141-intrinsic-affine-envelopes)
    - [Descending quasi-affine schemes](#142-descending-quasi-affine-schemes)
    - [Finite presentation and openness](#143-finite-presentation-and-openness)
    - [The precise reusable criterion](#144-the-precise-reusable-criterion)
15. [Quasi-projective and projective descent](#15-quasi-projective-and-projective-descent)
    - [Polarized descent](#151-polarized-descent)
    - [Very ampleness and closed immersions](#152-very-ampleness-and-closed-immersions)
    - [Producing compatible positive data](#153-producing-compatible-positive-data)
    - [Limits of the statement](#154-limits-of-the-statement)
    - [The expanded scheme-effectivity package](#155-the-expanded-scheme-effectivity-package)
16. [The descent package for moduli geometry](#16-the-descent-package-for-moduli-geometry)
    - [Generalized elliptic curves](#161-generalized-elliptic-curves)
    - [PEL objects](#162-pel-objects)
    - [Representability after descent](#163-representability-after-descent)
    - [A practical descent protocol](#164-a-practical-descent-protocol)
17. [Synthesis](#17-synthesis)
    - [The three levels of descent](#171-the-three-levels-of-descent)
    - [Reusable theorem package](#172-reusable-theorem-package)
    - [Conclusion](#173-conclusion)

## 1. Why descent is possible

### 1.1 Local descriptions and global objects

Geometry is often constructed after a change of base. A bundle is trivialized, a family acquires
a convenient projective embedding, or a group action becomes a familiar constant action. The real
problem begins when one tries to return to the original base. Two copies of the local object live
over the double overlap; an identification between them is necessary, and on the triple overlap
the three possible identifications must agree. Descent asks when these compatibility conditions
are not merely necessary but sufficient, and in which geometric category the descended object
lives.

The prototype is ordinary gluing over open subsets. Faithfully flat descent is subtler because the members of the cover need not be open immersions. A field extension $\operatorname{Spec}L\to\operatorname{Spec}K$ is a cover, although its source has no smaller pieces corresponding to open subsets of the one-point target. What substitutes for literal intersection is the fiber product

$$
\operatorname{Spec}L\times_{\operatorname{Spec}K}\operatorname{Spec}L
=\operatorname{Spec}(L\otimes_KL).
$$

The tensor product remembers the two ways a scalar can be viewed after base change. Equality between those two views is the algebraic form of being defined over $K$.

This book develops that observation from modules to geometric objects and then to the scheme-effectivity criteria needed in moduli problems. The guiding sequence is

$$
\text{faithful exactness}
\Longrightarrow \text{effective module descent}
\Longrightarrow \text{affine descent}
\Longrightarrow
\begin{cases}
\text{an fpqc equalizer sheaf with effective pullback},\\
\text{an algebraic space for a surjective étale cover},\\
\text{a scheme under a proved criterion}.
\end{cases}
$$

The last distinction is essential. Schemes do not form an effective fpqc descent category in
complete generality. Chapter 11 constructs the fpqc equalizer sheaf and proves algebraic-space
effectivity for a surjective étale cover. For a general fpqc cover, producing a representable diagonal and
an étale atlas is an additional theorem, not a consequence of the sheaf condition. This book does
not assert that theorem without hypotheses. It instead proves scheme effectivity in the affine,
finite, quasi-affine, and compatibly polarized situations used below. Properness or local
projectivity alone is not such a hypothesis.

At every stage there are two distinct assertions. Full faithfulness says that maps downstairs can be recognized upstairs. Effectivity says that every compatible object upstairs actually comes from downstairs. Confusing them is a common source of incomplete descent arguments.

### 1.2 Faithful flatness

Let $A\to B$ be a homomorphism of commutative rings. The $A$-algebra $B$ is **flat** if tensoring an exact sequence of $A$-modules with $B$ preserves exactness. It is **faithfully flat** if it is flat and

$$
B\otimes_A M=0\quad\Longrightarrow\quad M=0
$$

for every $A$-module $M$. Equivalently, tensoring with $B$ both preserves and reflects exact sequences. Indeed, flatness gives preservation. To reflect exactness of $M'\to M\to M''$, first observe upstairs that the composite vanishes and descend that equality by faithfulness; then tensor the quotient of the kernel by the image. This quotient becomes zero upstairs and hence was zero downstairs.

Other useful equivalent conditions are:

- $B$ is flat and $IB\ne B$ for every proper ideal $I\subset A$;
- $B$ is flat and $\operatorname{Spec}B\to\operatorname{Spec}A$ is surjective;
- for every $M$, the map $M\to B\otimes_AM$, $m\mapsto1\otimes m$, is injective.

For the first equivalence, $(A/I)\otimes_AB\simeq B/IB$. Thus faithfulness forces $IB\ne B$. Conversely, if a nonzero module $M$ is chosen and $m\ne0$, the cyclic submodule $Am\simeq A/I$ has proper annihilator $I$. Flatness injects $B\otimes_AAm$ into $B\otimes_AM$, while $B/IB$ is nonzero. For the spectral formulation, suppose first that $B$ is faithful and let $\mathfrak p\subset A$. The fiber

$$
B\otimes_A\kappa(\mathfrak p)
$$

is nonzero, so a prime of this fiber gives a prime of $B$ contracting to $\mathfrak p$. Conversely, if every prime of $A$ is reached and $I\subsetneq A$, choose $\mathfrak p\supset I$ and a prime $\mathfrak q$ of $B$ above it. Then $IB\subseteq\mathfrak q$, so $IB\ne B$. This proves the equivalence without silently replacing containment of contractions by equality.

These equivalences explain the name. Flatness guarantees that no algebraic relation is introduced by base change; faithfulness guarantees that no nonzero relation or object disappears.

### 1.3 The geometric meaning

A morphism $p:T\to S$ is flat when its maps on local rings are flat. It is faithfully flat when it is flat and surjective. If it is also quasi-compact, it is called an **fpqc morphism**. The abbreviation records “faithfully flat and quasi-compact.” A morphism is **fppf** when it is flat and locally of finite presentation. A surjective fppf morphism is an fpqc cover in the family sense defined below, although it need not itself be quasi-compact if infinitely many redundant components occur.

The geometric characterization matters. Flatness alone does not cover the base: the localization $A\to A_f$ is flat, but it misses $V(f)$. Surjectivity alone does not preserve equations: $A\to A/I$ may kill nonzero modules. Faithful flatness is exactly their conjunction.

Examples include field extensions, nonempty finite locally free covers, and the map from a union of open subsets covering $S$. The map

$$
A\longrightarrow A_f\times A_g
$$

is faithfully flat when $(f,g)=A$. It turns the familiar gluing cover $D(f)\cup D(g)$ into a single algebraic map. A completion $A\to\widehat A$ may be faithfully flat under noetherian hypotheses and an ideal contained in the Jacobson radical, but completion is not faithfully flat without such hypotheses; it must never be used as a cover merely because it is flat in a favorite example.

### 1.4 A first warning about hypotheses

The adjective “faithfully” does the detecting, while “flat” does the preserving. Both enter every effectivity proof. If $A\to A/I$ is used in place of a flat cover, an object annihilated by $I$ cannot remember how to lift across $I$. If $A\to A_f$ is used without covering the complement, two distinct $A$-maps can become equal after localization.

Quasi-compactness has a different role. It supplies finite control. Finite generation, finite presentation, and the existence of finitely many affine charts are conclusions about finitely many pieces of information; their descent requires that a cover of a quasi-compact region admit a finite reduction. This is why the topology is fpqc rather than merely the topology generated by arbitrary faithfully flat-looking families.

## 2. The fpqc and fppf covering theories

### 2.1 Covering families

A set-indexed family $\{p_i:T_i\to S\}_{i\in I}$ is an **fpqc covering family** if every $p_i$ is flat and, for every quasi-compact open $U\subseteq S$, there are finitely many indices $i_1,\ldots,i_n$ and quasi-compact opens $V_j\subseteq T_{i_j}$ such that

$$
U=\bigcup_{j=1}^n p_{i_j}(V_j).
$$

It is enough to require this for affine $U$. This formulation is sometimes called jointly surjective and quasi-compact as a family. It deliberately allows infinitely many members, while insisting that their contribution over any affine part of the base can be reduced to finitely much data.

An **fppf covering family** is a jointly surjective family of flat morphisms locally of finite presentation. Over an affine open of $S$, images of such morphisms are open. Quasi-compact opens in the sources cover the relevant inverse images, and quasi-compactness of the base then selects finitely many. Hence every fppf covering family is fpqc in the family sense.

Every Zariski open cover is fpqc: open immersions are flat, and a quasi-compact open admits a finite subcover. Every étale covering is fppf. Thus the chain of permissible localizations grows from Zariski to étale to fppf to fpqc. The stronger the topology, the stronger the assertion that an object is local.

### 2.2 Single covers and affine reduction

An fpqc morphism $p:T\to S$ gives an fpqc singleton covering family. The converse needs a qualification. The family condition for the singleton says that over every quasi-compact open of $S$ some quasi-compact open part of $T$ already maps onto it; it does not say that the whole inverse image is quasi-compact. An infinite disjoint union of redundant copies of $S$ illustrates the distinction. If $p$ is quasi-compact as well, the two notions agree. In all cases, over an affine base the singleton family contains a quasi-compact open subspace that is still surjective and can be refined by finitely many affines.

Suppose $S=\operatorname{Spec}A$ and $\{T_i\to S\}$ is an fpqc family. Choose the finitely many quasi-compact opens promised by the definition, refine each by finitely many affine opens $\operatorname{Spec}B_j$, and set

$$
B=\prod_{j=1}^n B_j.
$$

Each $B_j$ is flat over $A$, so their finite product, which is also their finite direct sum as an $A$-module, is flat. The spectra of the $B_j$ cover $\operatorname{Spec}A$, so $A\to B$ is faithfully flat. Descent for the original family can therefore be proved locally on $S$ by a single ring map, provided the pairwise and triple overlaps are retained. This is the basic reduction used throughout the book.

### 2.3 Infinite families and size

It is tempting to replace any family by

$$
\coprod_{i\in I}T_i\longrightarrow S.
$$

For an infinite family this map generally fails to be quasi-compact: the inverse image of an affine open may be an infinite disjoint union of nonempty opens. The family is nevertheless a valid fpqc cover if it has finite reductions over affine opens. Thus “the coproduct is an fpqc morphism” is not the definition and is false in useful examples.

For instance, let $S$ be an infinite disjoint union of affine schemes and take its individual components as the family. Every quasi-compact open meets only finitely many components, so the family is fpqc. Its coproduct happens to be $S$ itself in this example, but after adding infinitely many redundant copies of one component the coproduct map ceases to be quasi-compact. The covering theory should not change when harmless redundant members are added.

Covering families are indexed by sets, not by a collection too large to form fiber products and products of Hom sets. Once a universe of schemes has been fixed, one either restricts to families in that universe or enlarges it once and for all. No mathematical conclusion depends on the choice. What matters in proofs is that each affine region uses only a finite subfamily. Products $\prod_iB_i$ over infinitely many flat $A$-algebras are avoided: infinite products of flat modules need not be flat over a general ring.

### 2.4 Stability and refinement

Fpqc and fppf covers are stable under base change. Flatness and local finite presentation are stable under base change. Joint surjectivity is preserved because a point $s'$ over $s$ can be lifted after choosing a point above $s$ and then taking a prime of the tensor product over the common residue field. The finite-reduction condition pulls back over affine opens and is checked after refining by quasi-compact opens.

They are also stable under composition. Given a cover of $S$ and covers of each member, first choose finitely many members relevant over a quasi-compact $U\subseteq S$, then finitely many members of the second-stage covers over the chosen quasi-compact pieces. This two-step finite selection is precisely where the family formulation proves its worth.

A refinement does not change descent in a category for which the two relevant effectivity steps
are known. Data on the coarse cover pull back to the refinement. Conversely, compatible data on a
refinement first descend to each coarse member and then descend to $S$; uniqueness at both stages
makes the resulting comparison canonical. For modules and affine schemes this is unrestricted.
For other schemes, each stage must separately satisfy one of Chapter 11's criteria.
We shall use transitivity only after identifying those two steps.

## 3. The algebraic engine

### 3.1 Tensor products detect exactness

Let $A\to B$ be faithfully flat. For a sequence

$$
M'\xrightarrow{u}M\xrightarrow{v}M'',
$$

exactness is equivalent to exactness after tensoring with $B$. Preservation is flatness. For reflection, the upstairs equality $(1\otimes v)(1\otimes u)=0$ says that $B\otimes_A(vu)=0$. The image of $vu$ becomes zero, hence the image itself is zero by faithfulness. We may therefore form

$$
H=\ker(v)/\operatorname{im}(u).
$$

Flatness identifies $B\otimes_AH$ with the corresponding upstairs homology, which is zero. Faithfulness gives $H=0$.

Consequently injectivity, surjectivity, and bijectivity of module maps can be tested after faithfully flat base change. The same applies to equality of maps: tensor their difference. This simple observation proves most full-faithfulness statements later.

There is also a useful ideal consequence:

$$
IB\cap A=I.
$$

Indeed, $A/I\to B/IB\simeq B\otimes_AA/I$ is injective. Thus equations and closed conditions do not acquire false solutions upon extension and contraction along a faithfully flat map.

### 3.2 The Amitsur equalizer

Write

$$
B^{[n]}=\underbrace{B\otimes_A\cdots\otimes_AB}_{n+1\text{ factors}}.
$$

The two maps $d^0,d^1:B\to B^{[1]}$ are $b\mapsto1\otimes b$ and $b\mapsto b\otimes1$. The first fundamental exact sequence is

$$
0\longrightarrow A\longrightarrow B
\mathrel{\substack{\xrightarrow{d^0}\\[-.4em]\xrightarrow[d^1]{}}}
B\otimes_AB.
$$

In words, $A$ is the equalizer of the two maps from $B$ to $B\otimes_AB$.

The proof illustrates the standard descent technique: make a faithfully flat base change until a splitting appears. The alternating differential in degree $n$ is

$$
\partial^n=\sum_{i=0}^{n+1}(-1)^id^i,
$$

where $d^i$ inserts $1$ in the $i$th position. Tensor the augmented complex with $B$ over $A$. The new leftmost $B$-factor supplies an extra degeneracy: multiply it into the next factor. The identities between insertions and this multiplication give $h\partial+\partial h=1$ in positive degrees and the augmented identity in degree zero. Thus the base-changed complex is contractible beyond its augmentation. Faithful flatness reflects exactness, proving the assertion downstairs.

More generally, for every $A$-module $M$ the augmented Amitsur complex begins exactly:

$$
0\longrightarrow M\longrightarrow B\otimes_AM
\longrightarrow B^{[1]}\otimes_AM,
$$

where the last arrow is the difference of insertion in the first and second $B$ positions. Higher alternating insertion maps produce a complex. Its exactness in positive degrees can be proved by the same base-change-and-contract argument. We need principally degrees zero and one, but the higher picture explains why the cocycle condition occurs on triple overlaps.

### 3.3 Purity and descent tests

The injection $M\to B\otimes_AM$ for every $M$ says that $A\to B$ is pure as a map of $A$-modules. Purity is weaker than faithful flatness, yet it explains why finitely presented relations can be descended. If elements $m_1,\ldots,m_r$ generate $B\otimes_AM$, each local expression involves finitely many coefficients and elements of $M$. The cokernel of the submodule they generate becomes zero after base change, so it was already zero.

Similarly, a finite system of linear equations over $A$ has a solution whenever a compatible solution exists after faithfully flat extension and satisfies the equalizer condition. One must retain compatibility: the equation $x^2+1=0$ has a solution after $\mathbf R\to\mathbf C$, but no real solution. The two complex conjugate choices do not define invariant data.

Several properties can now be tested upstairs:

$$
M=0,\quad u=0,\quad u\text{ injective},\quad
u\text{ surjective},\quad \text{and exactness}.
$$

Finite generation and finite presentation also descend, but their proofs require finite bookkeeping and will be given in Chapter 6. Projectivity requires both finite presentation and flatness; neither piece should be suppressed.

### 3.4 Examples and failures

For a field extension $K\subset L$, every $K$-module is flat and $L\otimes_KM=0$ only when $M=0$. Thus all field extensions are faithfully flat. The equalizer

$$
K\longrightarrow L\rightrightarrows L\otimes_KL
$$

does not in general say “fixed by a Galois group.” That description is available only for suitable Galois extensions. The tensor-product formulation works equally for inseparable extensions and nonnormal extensions.

For $A\to A_f$, the Amitsur equalizer need not recover $A$: it recovers the part visible on $D(f)$. If $f$ is nilpotent, the localization may even be zero. For $A\to A/I$, tensoring kills $I$ and cannot reflect injectivity. These examples show why neither flatness without faithfulness nor faithfulness of the underlying set map without flatness suffices.

## 4. Cech nerves and descent data

### 4.1 The nerve of a cover

Let $p:T\to S$ be a cover. Its Cech nerve (usually written “Čech nerve”) is the sequence

$$
T,\qquad T^{[1]}=T\times_ST,\qquad
T^{[2]}=T\times_ST\times_ST,\qquad\ldots
$$

with projections obtained by omitting factors and diagonals obtained by repeating them. We write $p_1,p_2:T^{[1]}\to T$, and $p_{12},p_{23},p_{13}:T^{[2]}\to T^{[1]}$. The nerve is the algebraic substitute for all multiple intersections of an open cover.

The triple product is indispensable. Pairwise identifications can contradict one another around a triangle. The triple-overlap condition rules out precisely that defect, just as transition functions $g_{ij}$ for a vector bundle obey $g_{ik}=g_{jk}g_{ij}$.

### 4.2 Objects, isomorphisms, and cocycles

Suppose a kind of geometric object can be pulled back. A **descent datum** on an object $E$ over $T$ is an isomorphism

$$
\theta:p_1^*E\xrightarrow{\sim}p_2^*E
$$

over $T^{[1]}$ satisfying

$$
p_{23}^*\theta\circ p_{12}^*\theta=p_{13}^*\theta
$$

over $T^{[2]}$. The convention says that the first map transports from factor $1$ to factor $2$, and the second from factor $2$ to factor $3$.

The cocycle implies the omitted normalization conditions. Pulling back along the diagonal $T\to T^{[1]}$ shows that $\theta$ restricts to the identity: the cocycle there says $e^2=e$, and an idempotent automorphism is the identity. Pulling along the transposition of factors then gives $\theta_{21}=\theta^{-1}$.

Every object $F$ over $S$ has a canonical datum on $p^*F$: both pullbacks to $T^{[1]}$ are canonically the pullback of $F$, and associativity of pullback gives the cocycle. Descent asks whether this construction is fully faithful and essentially surjective.

### 4.3 Morphisms and full faithfulness

A morphism between $(E,\theta)$ and $(E',\theta')$ is a map $u:E\to E'$ for which

$$
p_2^*u\circ\theta=\theta'\circ p_1^*u.
$$

This is not extra decoration. If $u$ is pulled back from $S$, the equation is forced. Full faithfulness asserts the converse: every compatible $u$ descends uniquely.

For modules this follows from an equalizer of Hom sets. For schemes it can be checked after covering the source by affines and reducing maps into an affine target to ring maps; general targets then follow because equal maps have equal restrictions and compatible local maps glue. The uniqueness part is usually easier than existence but remains logically separate.

### 4.4 Families and indices

For a family $\{T_i\to S\}$, a datum consists of objects $E_i$ over $T_i$ and isomorphisms

$$
\theta_{ij}:E_i|_{T_i\times_ST_j}
\xrightarrow{\sim}
E_j|_{T_i\times_ST_j}
$$

for every ordered pair, with

$$
\theta_{jk}\theta_{ij}=\theta_{ik}
$$

on $T_i\times_ST_j\times_ST_k$. The diagonal and inverse conditions again follow. This formulation, rather than an infinite coproduct, is the correct one for an infinite cover.

On each affine $U\subset S$, select a finite affine refinement as in Section 2.2 and descend there
in the category under consideration. Different selections have a common refinement. Full
faithfulness supplies unique comparison isomorphisms, and the cocycle for those comparisons is
automatic by uniqueness. The locally descended objects therefore glue. This argument will be
invoked only when the single-cover theorem has first been proved in that category; it does not
turn a noneffective scheme datum into an effective one.

## 5. Effective descent for modules

### 5.1 The invariant module

Let $A\to B$ be faithfully flat, and let $N$ be a $B$-module. The two scalar extensions of $N$ to $B\otimes_AB$ may be written

$$
N_1=N\otimes_{B,d^1}(B\otimes_AB),
\qquad
N_2=N\otimes_{B,d^0}(B\otimes_AB).
$$

A descent datum is a $(B\otimes_AB)$-linear isomorphism $\theta:N_1\to N_2$ satisfying the cocycle over $B^{[2]}$. We seek an $A$-module $M$ whose scalar extension is $N$.

The answer is forced. Define

$$
M=\{n\in N:\theta(n\otimes1)=1\otimes n\}.
$$

More invariantly, $M$ is the equalizer of the two $A$-linear maps from $N$ to $N_2$, one induced by $\theta$ and the other by the canonical inclusion. It is an $A$-submodule because the two occurrences of $a\in A$ agree in $B\otimes_AB$. There is a canonical $B$-linear map

$$
\varepsilon:B\otimes_AM\longrightarrow N,
\qquad b\otimes m\longmapsto bm.
$$

Effectivity is the assertion that $\varepsilon$ is an isomorphism and that its canonical descent datum is $\theta$.

### 5.2 Proof of effectivity

**Faithfully flat module descent theorem.** The functor

$$
M\longmapsto(B\otimes_AM,\text{canonical datum})
$$

is an equivalence from $A$-modules to $B$-modules with descent datum.

The proof strategy is to test $\varepsilon$ after tensoring once more with $B$. Faithful flatness
will then reflect that it is an isomorphism. We isolate the elementary split calculation which
makes this test work.

**Split-cover lemma.** Let $C\to D$ have a $C$-algebra retraction $s:D\to C$. If a $D$-module
$Q$ has descent datum, put $Q_0=C\otimes_{D,s}Q$. Pulling the datum back along the two maps

$$
D\longrightarrow D\otimes_CD
$$

and then along $1\otimes s$ gives a $D$-linear isomorphism

$$
D\otimes_CQ_0\xrightarrow{\sim}Q.
$$

On $D\otimes_CD\otimes_CD$, the assertion that this isomorphism respects the datum is exactly the
cocycle. Pulling the cocycle along the diagonal defined by $s$ proves one inverse identity; its
normalization on the diagonal proves the other. Thus every datum for a split cover is effective,
and its invariant module is canonically $Q_0$.

Apply this lemma after the faithfully flat base change $A\to B$. The pulled-back cover is

$$
B\longrightarrow B\otimes_AB,
$$

and multiplication $\mu(b_1\otimes b_2)=b_1b_2$ is a retraction of either structural map. Because
$B$ is flat over $A$, tensoring preserves the equalizer defining $M$. Consequently
$B\otimes_AM$ is the invariant module of the pulled-back datum. The split-cover lemma identifies
the base change of

$$
\varepsilon:B\otimes_AM\longrightarrow N
$$

with an isomorphism. Hence the kernel and cokernel of $\varepsilon$ vanish after tensoring with
$B$; faithful flatness makes both vanish before tensoring.

Finally, the definition of $M$ says exactly that $\varepsilon$ intertwines the canonical datum with $\theta$. This proves essential surjectivity. Notice how each hypothesis enters: flatness lets kernels and cokernels commute with the test, faithfulness brings the conclusion back, and the cocycle constructs the inverse after the split base change.

Equivalently, the same calculation is organized by the exact Amitsur equalizer

$$
0\to M\to N\rightrightarrows N_2.
$$

After tensoring with $B$, the complex is split by insertion and multiplication. The equalizer is therefore restored by base change. This proof is often shorter in applications involving several compatible maps.

### 5.3 Morphisms and exact sequences

Let $M,M'$ be $A$-modules. A $B$-linear map

$$
u:B\otimes_AM\longrightarrow B\otimes_AM'
$$

descends if and only if its two pullbacks to $B\otimes_AB$ agree under the canonical data. To prove this, view the graph of $u$ elementwise or apply the module theorem to the equalizer: compatibility ensures that $u(1\otimes m)$ is invariant and hence equals $1\otimes u_0(m)$ for a unique $u_0(m)\in M'$. Linearity follows upstairs and descends by injectivity of $M'\to B\otimes_AM'$. Thus

$$
\operatorname{Hom}_A(M,M')
\longrightarrow
\operatorname{Hom}_B(B\otimes_AM,B\otimes_AM')
$$

identifies the left side with compatible maps. This proves full faithfulness.

Kernels, cokernels, images, finite direct sums, tensor products, symmetric powers, exterior powers, and duals when defined all inherit descent data functorially. Because exactness is reflected, taking the descended kernel or cokernel gives the kernel or cokernel downstairs. In particular, a compatible short exact sequence upstairs descends to a unique short exact sequence downstairs.

One must distinguish “the middle module has a datum” from “the sequence has a datum.” A submodule $N'\subset N$ descends only when the overlap isomorphism carries its first pullback onto its second. An arbitrary subspace of $L\otimes_KM$ need not be defined over $K$.

### 5.4 Base change and transitivity

If $A\to A'$ is any map, pulling a descent datum for $A\to B$ to $A'\to B\otimes_AA'$ gives the scalar extension of the descended module. This follows either from the explicit equalizer when $A'$ is flat, or in general from uniqueness: both candidates become canonically isomorphic after the faithfully flat base change $B\otimes_AA'$.

For a tower $A\to B\to C$ of faithfully flat maps, descent from $C$ to $A$ can be performed in two stages. First restrict the datum to the Čech nerve over $B$ and descend to $B$. The remaining compatibility descends, by full faithfulness, to a datum relative to $A\to B$, which is then effective. Conversely the pullback of the two-stage result is the original object. This transitivity is the algebraic model for refining a geometric cover.

## 6. Finiteness, flatness, and projectivity

### 6.1 Finite generation and finite presentation

Let $M$ be an $A$-module and suppose $B\otimes_AM$ is finitely generated over $B$. Choose generators. Each is a finite sum of tensors $b\otimes m$, so finitely many elements $m_1,\ldots,m_r$ of $M$ occur. If $M_0$ is their span, then

$$
B\otimes_A(M/M_0)=0.
$$

Faithfulness gives $M=M_0$. Thus finite generation descends without any noetherian hypothesis.

Suppose next that $B\otimes_AM$ is finitely presented. It is finitely generated, so choose a surjection $A^r\to M$ with kernel $K$. After tensoring, flatness identifies $B\otimes_AK$ with the kernel of $B^r\to B\otimes_AM$. That kernel is finitely generated because the target is finitely presented. By the preceding paragraph $K$ is finitely generated. Hence $M$ is finitely presented.

The same argument proves descent of finite type and finite presentation for algebras. For finite type, descend finitely many algebra generators from their finite tensor expressions. For finite presentation, present the algebra as a quotient of a finite polynomial algebra; faithful flatness and the module argument descend finite generation of the ideal of relations. The conclusion is false for a merely pointwise family without affine-local finite reduction, because no uniform finite list of generators need exist.

### 6.2 Flat modules

Flatness descends along faithfully flat base change. Suppose $B\otimes_AM$ is flat over $B$. For an injection $N'\to N$, tensoring with $M$ gives a map whose further tensor product with $B$ is

$$
(B\otimes_AN')\otimes_B(B\otimes_AM)
\longrightarrow
(B\otimes_AN)\otimes_B(B\otimes_AM).
$$

The first base change remains injective because $B$ is flat, and the displayed map is injective because the base-changed $M$ is flat. Faithfulness of $B$ reflects injectivity. Therefore $M$ is flat.

This proof also shows the correct relative statement. Given $A\to R$ and a faithfully flat $A\to B$, if $R_B=R\otimes_AB$ and an $R$-module $M$ become flat over $R_B$ after base change, then $M$ is flat over $R$, because $R\to R_B$ is faithfully flat. Flatness of a morphism is consequently fpqc local on the base.

### 6.3 Finite projective modules

A module is finite projective if and only if it is finitely presented and flat. One direction follows because a direct summand of a finite free module is finitely presented and flat. For the other, localize at a prime and choose elements whose residues form a basis of $M/\mathfrak mM$. They give a surjection from a finite free module onto $M$. If $K$ is its kernel, flatness of $M$ makes

$$
0\longrightarrow K\otimes k(\mathfrak m)
\longrightarrow k(\mathfrak m)^r
\longrightarrow M\otimes k(\mathfrak m)\longrightarrow0
$$

exact. The last map is an isomorphism, so $K/\mathfrak mK=0$. The finite-presentation hypothesis
makes $K$ finitely generated, and Nakayama gives $K=0$. Thus $M$ is free at every prime. Clearing
the finitely many coefficients in a chosen presentation makes it free on a neighborhood, so it
is finite locally free. A finite affine cover then supplies a finite dual basis, or equivalently
an idempotent matrix exhibiting $M$ as a direct summand of a finite free module.

Since both finite presentation and flatness descend, finite projectivity descends. Thus if $B\otimes_AM$ is finite projective over $B$, then $M$ is finite projective over $A$. More generally, the effective descent equivalence restricts to an equivalence between finite projective modules and finite projective modules with datum.

Projective without “finite” is more delicate. Arbitrary projectivity is not controlled by a finite presentation, and descent along a general faithfully flat map requires additional hypotheses. The applications in this book use finite projective modules, vector bundles of finite rank, or finitely presented flat modules; no unrestricted projectivity assertion is needed.

### 6.4 Rank and related invariants

For a finite projective $M$, the function

$$
\mathfrak p\longmapsto\dim_{\kappa(\mathfrak p)}M\otimes_A\kappa(\mathfrak p)
$$

is locally constant. Under a faithfully flat map, every prime of $A$ has a prime of $B$ above it, and fiber rank is unchanged after residue-field extension. Hence being of constant rank $r$, or having rank in a specified subset of the nonnegative integers, descends.

The determinant $\det M=\bigwedge^rM$ commutes with base change. A map between finite projective modules of the same rank is an isomorphism exactly when its determinant is invertible, a condition detectable after faithful base change. Fitting ideals also commute with base change, and $IB\cap A=I$; therefore loci defined by ranks of finitely presented modules descend. These observations will control vector bundles, finite locally free schemes, and degeneracy conditions in moduli problems.

## 7. Algebras and affine schemes

### 7.1 Descent of algebra structures

An $A$-algebra structure on a module $R$ consists of maps

$$
\mu:R\otimes_AR\to R,
\qquad \eta:A\to R,
$$

satisfying associativity, commutativity, and unit identities. If a $B$-algebra $C$ has a module descent datum and the overlap isomorphism is an algebra isomorphism, then $\mu$ and $\eta$ are compatible morphisms of descent data. Module full faithfulness descends them uniquely. Their identities hold downstairs because they hold after tensoring with $B$, and equality of maps is reflected. Thus $C\simeq B\otimes_AR$ as algebras for a unique $A$-algebra $R$.

This argument is an instance of a broad principle: any structure specified by maps between finite tensor constructions and equations between composites descends with the underlying module. Associative algebras, commutative algebras, coalgebra maps on finite projective objects, bilinear pairings, involutions, and module actions all fit this pattern. Existence descends the structure maps; full faithfulness descends the identities.

### 7.2 Quotients and equations

Let $C$ descend to $R$, and let $J\subset C$ be an ideal stable under the descent datum. As a submodule it descends to $I\subset R$. Stability under multiplication is an equality/inclusion of descended maps, so $I$ is an ideal. Exactness gives

$$
B\otimes_A(R/I)\simeq C/J.
$$

If $J$ is finitely generated, then $I$ is finitely generated. Hence finite systems of equations descend when their ideal is compatible.

Nilpotence and reducedness deserve care. If $R_B$ is reduced and $B$ is faithfully flat, then $r^n=0$ implies $(1\otimes r)^n=0$, hence $1\otimes r=0$ and $r=0$. Thus reducedness descends. The converse, ascent of reducedness, fails for inseparable field extensions. Likewise geometric reducedness is deliberately stronger than reducedness and is tested after all field extensions, not one arbitrary cover.

### 7.3 Affine descent

Passing to spectra reverses arrows. The algebra theorem says:

**Affine descent theorem.** Let $T\to S$ be fpqc. Affine $T$-schemes with descent datum relative to $T/S$ are precisely pullbacks of affine $S$-schemes, and compatible morphisms descend uniquely.

When $S=\operatorname{Spec}A$ and $T=\operatorname{Spec}B$, an affine $T$-scheme is $\operatorname{Spec}C$. Its scheme datum is opposite to an algebra datum on $C$, so the result is immediate. For a general fpqc cover over this affine $S$, choose a finite affine refinement $T'=\operatorname{Spec}B\to S$. Since affineness is preserved by base change, $X_T\times_TT'$ is affine. Its algebra datum relative to $T'/S$ descends to an $A$-algebra $R$. On $T'\times_ST$ the two affine $T'\times_ST$-schemes $\operatorname{Spec}R$ and $X_T$ are canonically identified. Affine full faithfulness on an affine cover of $T$ descends these identifications and their inverse, so $\operatorname{Spec}R\times_ST\simeq X_T$. This also proves independence of the chosen refinement. The same construction over affine opens of a general $S$ glues, by uniqueness, to an affine $S$-scheme.

Affineness itself descends under fpqc base change: if $X_T\to T$ is affine, then the canonical descent datum on $X_T$ lies in the affine subcategory, so its effective affine descent is an affine $S$-scheme. Full faithfulness identifies it with $X$. This concise proof depends on having already established effectivity, not merely on affineness being visible on fibers.

### 7.4 Finite and finite locally free affine schemes

An affine morphism $X=\operatorname{Spec}_S\mathcal A\to S$ is finite when $\mathcal A$ is a finite module, finite presentation when it is a finitely presented algebra, and finite locally free of rank $r$ when $\mathcal A$ is finite locally free of rank $r$ as a module. Chapters 5 and 6 therefore give effective descent for each class.

In particular, if $X_T\to T$ is finite and the datum is effective as an affine scheme, then $X\to S$ is finite. If it is finite and flat, it is finite locally free. The key local algebra is that a finitely generated flat module over a local ring is free. One proves this by the equational criterion for flatness: a basis modulo the maximal ideal lifts to generators, and every finite relation factors through relations whose coefficients vanish modulo the maximal ideal; the resulting determinant argument eliminates the kernel. Localizing the finite generating data gives freeness on a neighborhood. The rank then descends. Stating “finite locally free” remains useful because it records this conclusion and its locally constant rank at once.

Closed immersions descend as well. Affine-locally they correspond to surjective ring maps, and surjectivity is reflected by faithful flatness. Thus a compatible closed subscheme upstairs has a unique closed subscheme downstairs. This fact will repeatedly convert equations imposed after a cover into equations on the original family.

## 8. Quasi-coherent sheaves

### 8.1 Pullback data on a cover

Let $p:T\to S$ be fpqc. A quasi-coherent sheaf $\mathcal F_T$ with descent datum is equipped with

$$
\theta:p_1^*\mathcal F_T\xrightarrow{\sim}p_2^*\mathcal F_T
$$

and the usual cocycle. The desired sheaf downstairs cannot be obtained by simply taking equalizers on arbitrary opens, because inverse images of opens and pullback of modules interact through tensor products. The correct construction is affine-local.

Over an affine $U=\operatorname{Spec}A\subseteq S$, choose a finite affine refinement $\operatorname{Spec}B_j$ of the cover and combine it into the faithfully flat algebra $B=\prod B_j$. Restrictions of $\mathcal F_T$ correspond to modules on these affine pieces, while compatibility on pairwise overlaps produces a module descent datum. Chapter 5 gives an $A$-module $M_U$.

### 8.2 Affine-local construction

If $V=D(f)\subseteq U$, the restriction of the descended module is $(M_U)_f$. This follows from compatibility of module descent with base change. It agrees with the module obtained by descending directly over $V$. Hence the sheaves $\widetilde{M_U}$ agree canonically on intersections of affine opens.

These canonical identifications satisfy a cocycle: after pulling back to the cover, both composites are the same evident identification, and full faithfulness forces equality downstairs. Ordinary Zariski gluing therefore produces a quasi-coherent sheaf $\mathcal F$ on $S$. Its pullback is $\mathcal F_T$, because this is true over every chosen affine refinement. The same argument works for a morphism $X\to S$ and a cover of the base: apply it to the fpqc cover $X_T\to X$, obtained by base change.

### 8.3 Effectivity and full faithfulness

We have proved the central sheaf theorem:

**Quasi-coherent descent theorem.** For an fpqc morphism $T\to S$, pullback gives an equivalence between quasi-coherent sheaves on $S$ and quasi-coherent sheaves on $T$ with descent datum. The same holds for an fpqc covering family, interpreted with pairwise and triple overlaps.

For full faithfulness, a compatible map upstairs descends on every affine open by module full faithfulness. Those local maps agree on intersections, again by uniqueness, and glue. For effectivity, the preceding construction gives the sheaf and a canonical comparison after pullback. The comparison is an isomorphism affine-locally and hence globally.

The theorem fails for arbitrary sheaves of sets if “quasi-coherent” is silently retained only on the pieces but compatibility with tensor-product restriction is omitted. Quasi-coherence is exactly what turns geometric restriction over affine maps into scalar extension, where faithful flatness applies.

### 8.4 Coherence and exactness

Finite type, finite presentation, flatness, and finite local freeness of quasi-coherent sheaves are fpqc local on the base. Each property is checked on affine opens and is one of the module properties of Chapter 6. Rank descends pointwise. Exactness of a sequence of quasi-coherent sheaves is also fpqc local, since stalkwise or affine-module exactness is reflected by faithful flatness.

“Coherent” requires a convention. On a locally noetherian scheme it means locally finitely presented and is therefore descended. On a general scheme, some definitions require finite-type kernels for maps from finite free sheaves; under that definition coherence descends along quasi-compact faithfully flat maps by applying finite generation to those kernels. Without quasi-compactness or a coherent base, casual claims about coherence can fail. Later applications use locally noetherian bases or explicitly finitely presented sheaves.

## 9. Line bundles and vector bundles

### 9.1 Descent of local freeness

A vector bundle of rank $r$ is a finite locally free sheaf of rank $r$; a line bundle is the case $r=1$. Quasi-coherent descent plus Chapter 6 immediately gives:

**Vector-bundle descent.** On a fixed scheme $X$, vector bundles, line bundles, and their
morphisms satisfy effective descent along every fpqc cover $X'\to X$. This theorem descends a
bundle on an already available base object; it does not assert that a simultaneous descent datum
on an arbitrary scheme $X_T$ is effective as a scheme or even prove that its fpqc equalizer is an
algebraic space for an arbitrary fpqc cover. Representability of that equalizer requires a
separate, explicitly proved criterion.

To see local freeness directly, descend the sheaf as finitely presented and flat. At a point $x\in X$, choose a point $x'$ above it. Upstairs the sheaf is free near $x'$. The rank at $x$ equals the rank after extending $\kappa(x)$ to $\kappa(x')$. A finite presentation matrix has an invertible rank minor near $x$, and flatness eliminates the complementary relations. Thus the descended sheaf is free on a neighborhood of $x$.

### 9.2 Transition matrices and cocycles

If a rank-$r$ bundle becomes trivial on $T$, choosing a basis identifies its descent datum with a matrix

$$
g\in\operatorname{GL}_r(\Gamma(T\times_ST,\mathcal O))
$$

in the affine case. The cocycle is

$$
g_{23}g_{12}=g_{13}
$$

over $T^{[2]}$. Changing the chosen basis by $h\in\operatorname{GL}_r(\Gamma(T,\mathcal O))$ replaces $g$ by

$$
g'_{12}=h_2g_{12}h_1^{-1}.
$$

Thus isomorphic descended bundles correspond to cocycles differing by such a change. For $r=1$, matrices are units and the formula becomes multiplicative. This is the concrete origin of the classification of line bundles by degree-one multiplicative cocycles.

The datum need not arise from a global trivialization. On $\mathbf P^1$, the standard line bundle of degree one is trivial on the two standard affine opens but the transition function is the coordinate on their overlap. The nontrivial cocycle is precisely what remembers the bundle.

### 9.3 Determinants, sections, and forms

Tensor products, duals, symmetric powers, exterior powers, and internal Hom of finite locally free sheaves commute with pullback and descent. Therefore a bilinear form

$$
b:\mathcal E\otimes\mathcal E\to\mathcal L
$$

descends when it is compatible with the data on $\mathcal E$ and $\mathcal L$. Symmetry, alternatingness, and perfectness descend: the first two are equalities of maps, while the last says that $\mathcal E\to\mathcal E^\vee\otimes\mathcal L$ is an isomorphism.

A section $s\in\Gamma(X_T,\mathcal E_T)$ descends exactly when its two pullbacks correspond under the datum. Its zero scheme, when defined by the dual map $\mathcal E_T^\vee\to\mathcal O_{X_T}$, then descends as a closed subscheme. If $\mathcal E$ is a line bundle and $s$ is regular, regularity can be checked after flat base change because injectivity of multiplication by $s$ is reflected. Effective Cartier divisors therefore descend with their compatible defining line bundle and section.

### 9.4 Why local triviality is not descent data

Knowing only that a bundle exists after a cover is not enough to choose a bundle downstairs. One must specify how its two pullbacks are identified. For example, over a field extension $L/K$, an $L$-vector space of dimension $r$ certainly has $K$-forms, but no particular form is selected until descent data are given. Additional tensors may have an obstruction to admitting any compatible datum.

Likewise, an ample line bundle on $X_T$ need not itself descend unless it carries a cocycle. Its
isomorphism class might be moved by the overlap correspondence, or choices of pairwise
isomorphisms might fail the triple condition by units. Any valid polarized construction must
include the line bundle in the datum and cannot invoke a norm before constructing the quotient on
which that norm would live.

## 10. Morphisms and properties local on the base

### 10.1 Descent of maps

Let $X$ and $Y$ be $S$-schemes. The sequence

$$
\operatorname{Hom}_S(X,Y)
\longrightarrow \operatorname{Hom}_T(X_T,Y_T)
\rightrightarrows
\operatorname{Hom}_{T^{[1]}}(X_{T^{[1]}},Y_{T^{[1]}})
$$

is an equalizer for an fpqc cover $T\to S$. This is descent of morphisms. A map on $X_T$ descends exactly when its two pullbacks agree.

First assume $X$ and $Y$ affine over an affine $S$. The assertion is the full-faithfulness part of algebra descent with arrows reversed. If only $Y$ is affine over $S$, a map $X\to Y$ is an $\mathcal O_S$-algebra map from the coordinate algebra of $Y$ to the direct image of $\mathcal O_X$; it can be checked on affine opens of $X$, where module equalizers apply.

We also need the elementary descent of opens. A surjective fpqc morphism $q:Z'\to Z$ is a
quotient map on underlying spaces: a subset $U\subseteq Z$ is open exactly when $q^{-1}U$ is open.
Indeed, after restricting to affines, flatness gives going-down and hence lifts every
generalization, while quasi-compactness makes the image of the complement of a quasi-compact open
stable under specialization; affine-local finite reduction then gives the assertion for an
arbitrary open. Consequently a saturated open $U'\subseteq Z'$—one whose two inverse images to
$Z'\times_ZZ'$ agree—is the inverse image of the unique open $q(U')\subseteq Z$.

For general $Y$, cover it by affine opens. Their inverse images under the upstairs map are
saturated, so the preceding paragraph descends them to opens of $X$. The maps into the affine
members of the cover descend there and glue. Uniqueness follows because equal maps after a
surjective base change agree on underlying points and on functions over affine neighborhoods.

As a consequence, sections descend. A section of $X_T\to T$ is a map $T\to X$ after base change, and the overlap equality is exactly its descent condition. Automorphisms form a sheaf: compatible automorphisms descend, and the inverse descends with them.

### 10.2 The diagonal method

Many properties of a morphism $f:X\to S$ are encoded by its diagonal

$$
\Delta_f:X\longrightarrow X\times_SX.
$$

The morphism is separated when $\Delta_f$ is a closed immersion, unramified when it is locally of
finite type and the diagonal is an open immersion, and a monomorphism when the diagonal is an
isomorphism. Smoothness and étaleness, unlike unramifiedness in this generality, include local
finite presentation. Since diagonals commute with base change, descent of closed immersions, open
immersions, and isomorphisms yields descent of these properties.

Open immersions require a short argument. If $U_T\to X_T$ is an open immersion with compatible datum and its source descends to $U\to X$, then it is a monomorphism locally of finite presentation and flat. These three properties descend; such a morphism is an open immersion. Alternatively, its image is a subset whose inverse image is open. Flat morphisms locally of finite presentation are open, so the descended image is open, and the map identifies $U$ with it after a cover, hence already downstairs.

The diagonal method also reduces quasi-separatedness to quasi-compactness of a diagonal. It is safer than trying to reason directly with intersections of arbitrary affine opens after base change.

### 10.3 A table of descending properties

For a morphism $f:X\to S$, the following properties are fpqc local on the base, with the qualifications displayed.

| Property of $f$                           | Required qualification                               | Main reason                                      |
| ----------------------------------------- | ---------------------------------------------------- | ------------------------------------------------ |
| affine                                    | none                                                 | effective descent of affine schemes              |
| quasi-compact                             | cover is fpqc as a family                            | finite affine reduction                          |
| quasi-separated                           | none beyond fpqc                                     | diagonal and quasi-compactness                   |
| separated                                 | none beyond fpqc                                     | diagonal is a closed immersion                   |
| locally of finite type                    | none beyond fpqc                                     | finite algebra generators descend locally        |
| finite type                               | quasi-compactness included                           | local finite type plus quasi-compactness         |
| locally of finite presentation            | none beyond fpqc                                     | finite generators and relations descend          |
| finite presentation                       | quasi-compactness included                           | local finite presentation plus quasi-compactness |
| flat                                      | none beyond fpqc                                     | faithful exactness                               |
| finite locally free of rank $r$           | none beyond fpqc                                     | affine descent and module descent                |
| finite                                    | none beyond fpqc                                     | affine plus finite module                        |
| monomorphism                              | none beyond fpqc                                     | diagonal is an isomorphism                       |
| open, closed, or locally closed immersion | none beyond fpqc                                     | affine equations and open-image descent          |
| proper                                    | finite type and separated are part of the definition | universal closedness descends                    |
| smooth and étale                          | locally of finite presentation                       | infinitesimal or differential criterion          |
| unramified                                | locally of finite type                               | diagonal is an open immersion                    |

Quasi-affine and quasi-projective morphisms are postponed because their proofs use global functions or ample bundles. Projective morphisms are treated there as well. Noetherianity is not needed for the entries above unless it is built into a chosen alternative definition.

### 10.4 Proofs of the principal cases

For quasi-compactness, cover $S$ by affine opens $U$. Choose finitely many quasi-compact pieces of the fpqc family covering $U$. If $X_T\to T$ is quasi-compact, the inverse images of those finitely many pieces have finite affine covers. Their images cover $X_U$ because the base change is surjective. Descending the finitely many relevant opens, or applying the topological fact that a surjective quasi-compact map detects quasi-compactness, gives a finite cover of $X_U$. The family finiteness condition is essential here.

Local finite type and local finite presentation reduce to affine charts after using descent of quasi-compact open neighborhoods. On rings, they are exactly finite generation and finite presentation of algebras, proved in Section 6.1. Finite type and finite presentation add quasi-compactness.

For properness, finite type and separatedness have already descended. It remains to descend universal closedness. After any $S'\to S$, the induced $T\times_SS'\to S'$ is fpqc. A closed subset $Z\subset X_{S'}$ has closed inverse image in $X_{T\times_SS'}$, whose image in $T\times_SS'$ is closed because the upstairs morphism is proper. This closed subset is saturated for the cover. A subset of $S'$ is closed if its inverse image under an fpqc morphism is closed: reduce to affine faithfully flat maps, where specialization lifts by going-down for flat maps and surjectivity supplies a point over the initial prime. Thus the image of $Z$ is closed.

For smoothness and étaleness, first descend local finite presentation and flatness. Smoothness may be characterized, for a finitely presented flat morphism, by geometrically regular fibers. A point of $S$ lifts after the cover, and geometric regularity of the fiber can be checked after a faithfully flat field extension. Étaleness is smoothness of relative dimension zero, or equivalently flatness plus unramifiedness. For unramifiedness by itself, local finite type descends and the diagonal is an open immersion exactly when its base change is. This proves the table without assuming the base is noetherian or a field.

Some properties are local on the source, others on the target, and some on both. The phrase “fpqc local on the base” means exactly

$$
f\text{ has }P
\quad\Longleftrightarrow\quad
f_T\text{ has }P
$$

for every fpqc cover $T\to S$, with ascent supplied by base-change stability and descent by the arguments above. Nothing proved so far applies to a cover of the source, because such a cover is not a base change of the morphism being studied. The next section isolates and proves the one source-local statement that later books consume.

### 10.5 Descent along a cover of the source

Quotient constructions raise the opposite question to the one settled above. There one knows a
property of $X\to S$ and wants it for $Y\to S$, where $g:X\to Y$ is a faithfully flat cover of the
**source**. The archetype is a quotient $H/G$ of a smooth group scheme by a finite locally free
subgroup scheme: the quotient receives a finite locally free surjection from the smooth $H$, and
smoothness of the quotient is what an atlas argument needs. No entry of the table in Section 10.3
applies, since $g$ is not the base change of $Y\to S$ along anything, and no descent datum for
$Y$ is given.

Three statements are involved, and it is worth separating them before proving anything.

| Property of $f:Y\to S$         | Hypothesis on $g:X\to Y$                                                     | Main reason                                                                 |
| ------------------------------ | ---------------------------------------------------------------------------- | --------------------------------------------------------------------------- |
| flat                           | faithfully flat                                                              | faithfully flat local rings reflect injectivity                             |
| locally of finite presentation | finite locally free surjective, $S$ locally noetherian                       | Artin--Tate for the invariant subalgebra                                    |
| reduced geometric fibers       | faithfully flat                                                              | $\mathcal O_{Y_{\bar s}}$ injects into $g_{\bar s*}\mathcal O_{X_{\bar s}}$ |
| smooth                         | the three rows above, plus geometric fibers homogeneous under a group action | generic smoothness together with homogeneity                                |

Throughout, $f:Y\to S$, $g:X\to Y$, and $h=f\circ g:X\to S$.

**Flatness along the source.** If $g$ is faithfully flat and $h$ is flat, then $f$ is flat.

**Proof.** Flatness is a condition on local rings. Let $y\in Y$, let $s=f(y)$, and use
surjectivity of $g$ to choose $x\in X$ with $g(x)=y$. The induced local homomorphism
$\mathcal O_{Y,y}\to\mathcal O_{X,x}$ is flat, and it is faithfully flat: every proper ideal of
$\mathcal O_{Y,y}$ lies in the maximal ideal, whose extension lies in the maximal ideal of
$\mathcal O_{X,x}$ and is therefore proper, which is the criterion of Section 1.2. Let
$M'\to M$ be an injection of $\mathcal O_{S,s}$-modules. Since $h$ is flat, the map

$$
M'\otimes_{\mathcal O_{S,s}}\mathcal O_{X,x}
\longrightarrow
M\otimes_{\mathcal O_{S,s}}\mathcal O_{X,x}
$$

is injective. It is obtained from
$M'\otimes_{\mathcal O_{S,s}}\mathcal O_{Y,y}\to M\otimes_{\mathcal O_{S,s}}\mathcal O_{Y,y}$
by applying $-\otimes_{\mathcal O_{Y,y}}\mathcal O_{X,x}$, and a faithfully flat extension
reflects injectivity by Section 3.1. Hence $\mathcal O_{Y,y}$ is flat over
$\mathcal O_{S,s}$. $\square$

Nothing here needs finite presentation, and the argument is the exact mirror of Section 6.2:
there faithful flatness of a base change reflected flatness of a module, here faithful flatness
of a cover of the source reflects flatness of the target.

**Finite presentation along the source.** Suppose $g$ is finite locally free and surjective, $S$
is locally noetherian, and $h$ is locally of finite type. Then $f$ is locally of finite
presentation.

**Proof.** The assertion is local, so choose an affine open $\operatorname{Spec}R\subseteq S$ and
an affine open $V=\operatorname{Spec}A\subseteq Y$ lying over it. Since $g$ is finite it is
affine, so $g^{-1}(V)=\operatorname{Spec}B$ with $B$ a finite locally free faithfully flat
$A$-algebra; in particular $A\to B$ is injective. The scheme $\operatorname{Spec}B$ is a
quasi-compact open of $X$, so $B$ is a finite-type $R$-algebra.

Now run the Artin--Tate argument. Choose $b_1,\ldots,b_n$ generating $B$ as an $R$-algebra and
$y_1,\ldots,y_m$ generating $B$ as an $A$-module, with $y_1=1$. Write

$$
b_i=\sum_j a_{ij}y_j,
\qquad
y_iy_j=\sum_k a_{ijk}y_k,
\qquad a_{ij},a_{ijk}\in A,
$$

and let $A_0\subseteq A$ be the $R$-subalgebra generated by the finitely many $a_{ij}$ and
$a_{ijk}$. Then $A_0$ is a finite-type algebra over the noetherian ring $R$, hence noetherian.
Every monomial in the $b_i$ is an $A_0$-linear combination of the $y_k$, by induction on its
degree using the two displayed families of coefficients; therefore $B$ is generated as an
$A_0$-module by $y_1,\ldots,y_m$. A finite module over a noetherian ring is a noetherian module,
so its $A_0$-submodule $A$ is a finite $A_0$-module. Consequently $A$ is a finite-type
$R$-algebra, and finite type over a noetherian ring is finite presentation. $\square$

The noetherian hypothesis is used only here. Without it the same conclusion is true but requires
a limit argument that this book does not develop; every consumer below works over a locally
noetherian base.

**Reducedness of the geometric fibers.** If $g$ is faithfully flat and $X$ has reduced geometric
fibers over $S$, then so does $Y$.

**Proof.** Fix a geometric point $\bar s\to S$. The base change
$g_{\bar s}:X_{\bar s}\to Y_{\bar s}$ is again flat and surjective, hence faithfully flat. On an
affine open $\operatorname{Spec}A\subseteq Y_{\bar s}$ with faithfully flat $A\to B$ over an
affine open of $X_{\bar s}$ dominating it, the map $A\to B$ is injective. A subring of a reduced
ring is reduced, and reducedness is affine-local. $\square$

Note that only injectivity of $\mathcal O_{Y_{\bar s}}\to g_{\bar s*}\mathcal O_{X_{\bar s}}$ is
used, and that this injectivity is exactly what faithful flatness supplies; a merely surjective
$g$ would not give it, as the reduction map of a nonreduced scheme shows.

**Source-descent lemma for smoothness.** Let $g:X\to Y$ be a faithfully flat morphism of
$S$-schemes which is locally of finite presentation, and assume:

1. $h=f\circ g:X\to S$ is smooth;
2. either $f:Y\to S$ is locally of finite presentation, or $g$ is finite locally free and $S$ is
   locally noetherian;
3. there is an $S$-group scheme $P$ acting on $Y$ over $S$ such that for every geometric
   point $\bar s\to S$, with algebraically closed residue field $k$, the group $P(k)$ acts
   transitively on the closed points of $Y_{\bar s}$.

Then $f:Y\to S$ is smooth.

**Proof.** Flatness of $f$ is the first lemma. Local finite presentation of $f$ is either
assumed or supplied by the second lemma, since a smooth $h$ is locally of finite type. By the
fiber criterion recalled in Section 10.4 it now suffices to prove that every fiber $Y_s$ is
smooth over $\kappa(s)$, and by the entry for smoothness in the table of Section 10.3, applied to
the faithfully flat field extension $\kappa(s)\to k$, it suffices to prove that the geometric
fiber $Y_{\bar s}$ is smooth over $k$.

Fix such an $\bar s$. Then $Y_{\bar s}$ is locally of finite type over $k$, the base change
$g_{\bar s}$ is faithfully flat, and $X_{\bar s}$ is smooth over $k$, hence regular and in
particular reduced. By the third lemma $Y_{\bar s}$ is reduced.

Let $U\subseteq Y_{\bar s}$ be the smooth locus over $k$; it is open, smoothness being an open
condition on a morphism locally of finite presentation. We claim it is dense. Let
$\eta$ be the generic point of an irreducible component of dimension $d$, and let $K=\kappa(\eta)$
be the corresponding function field, a finitely generated extension of $k$. Because $k$ is
algebraically closed, hence perfect, $K$ is separably generated over $k$, so

$$
\dim_K\Omega^1_{K/k}=\operatorname{trdeg}_kK=d.
$$

Since $Y_{\bar s}$ is reduced, $\mathcal O_{Y_{\bar s},\eta}=K$, so the stalk of
$\Omega^1_{Y_{\bar s}/k}$ at $\eta$ is $\Omega^1_{K/k}$ and its fiber there has dimension $d$.
The sheaf $\Omega^1_{Y_{\bar s}/k}$ is quasi-coherent of finite type, so by Nakayama its fiber
dimension is at most $d$ on a nonempty open neighbourhood $W$ of $\eta$, which we shrink to be
disjoint from the other irreducible components. Let $w\in W$ be a closed point. Its residue field is $k$, so
the conormal sequence of the closed immersion $\{w\}\hookrightarrow Y_{\bar s}$ identifies
$\Omega^1_{Y_{\bar s}/k}\otimes\kappa(w)$ with the cotangent space
$\mathfrak m_w/\mathfrak m_w^2$. Hence that cotangent space has dimension at most $d$, while
$\dim\mathcal O_{Y_{\bar s},w}=d$ because $w$ is a closed point of a $d$-dimensional component
and lies on no other. The local ring is therefore regular, and a finite-type scheme over an
algebraically closed field is smooth exactly at the closed points where its local ring is
regular. Thus $w\in U$. Closed points are dense in $W$, so $U$ meets every irreducible component
and is dense.

Now use homogeneity. Each $p\in P(k)$ acts on $Y_{\bar s}$ as a $k$-automorphism, so it carries
$U$ onto $U$. Choose a closed point $u\in U$. By hypothesis every closed point of $Y_{\bar s}$ is
$p\cdot u$ for some $p\in P(k)$, hence lies in $U$. The complement of $U$ is a closed subset of a
scheme locally of finite type over a field containing no closed point, hence is empty. Therefore
$Y_{\bar s}=U$ is smooth over $k$, which completes the proof. $\square$

**Smooth-quotient corollary.** Let $S$ be locally noetherian, let $H\to S$ be a smooth $S$-group
scheme, and let $G\subseteq H$ be a closed subgroup scheme that is finite locally free over $S$.
Suppose the quotient sheaf $Y=H/G$ is represented by a scheme with $q:H\to Y$ finite locally free
and surjective, that is, a $G$-torsor. Then $Y\to S$ is smooth.

**Proof.** Existence of the quotient is a hypothesis here, not a conclusion. All that is used is
the stated conclusion about $q$. Apply the source-descent lemma with $X=H$ and $g=q$: hypothesis (1)
holds because $H$ is smooth over $S$, and hypothesis (2) holds because $q$ is finite locally free
and $S$ is locally noetherian. For hypothesis (3), let $P=H$ act on $Y$ by left translation, which is legitimate
because $q$ is equivariant for left translation on both sides. Fix a geometric point with
algebraically closed residue field $k$. A closed point $y$ of $Y_{\bar s}$ has nonempty finite
preimage under the finite surjective $q_{\bar s}$, and a closed point of that preimage is a
closed point of $H_{\bar s}$, hence an element of $H(k)$ by the Nullstellensatz. If
$y_i=q(h_i)$ for $i=1,2$, then $h_2h_1^{-1}\in H(k)$ carries $y_1$ to $y_2$. The action is
therefore transitive on closed points of every geometric fiber. $\square$

In particular, for a finite locally free closed subgroup $G\subseteq\operatorname{GL}_{r,S}$ over
a locally noetherian base, the homogeneous space $\operatorname{GL}_r/G$ is smooth over $S$. This
is the form in which later books use the statement when they build a smooth atlas of a quotient
stack by a non-smooth finite flat group.

Three hypotheses are genuinely needed. Flatness of $g$ cannot be dropped: the normalization
$\mathbf A^1\to\{y^2=x^3\}$ is finite, surjective, and birational with smooth source, while its
target is not smooth, and it is not flat. Surjectivity cannot be dropped, since $Y$ is
unconstrained away from the image of $g$. The homogeneity hypothesis is used only in the last
paragraph of the proof, to spread smoothness from a dense open of a geometric fiber to the whole
fiber. The lemma remains true without it, but the fiber step then requires descending regularity
of local rings along a faithfully flat map, which rests on the homological characterization of
regular local rings; that characterization is not developed in this collection, and every
consumer here is a homogeneous space, so nothing is lost by keeping the hypothesis explicit.

## 11. Effective descent and the scheme boundary

### 11.1 The fpqc equalizer and the algebraic-space boundary

We now construct the correct unrestricted target, and we keep the topology in the theorem
visible. An **algebraic space** over $S$ is an fppf sheaf $X$ on $S$-schemes whose diagonal is
representable by schemes and which admits a surjective étale morphism $U\to X$ from a scheme.
The two representability requirements cannot be replaced by the assertion that $X$ is merely a
quotient sheaf.

We first record a nonaffine scheme-effectivity input used in the quotient constructions.

**Separated locally-quasi-finite effectivity lemma.** Let $T\to S$ be an fppf cover. A descent
datum on a $T$-scheme $V\to T$ which is separated and locally quasi-finite over $T$ is effective
as a scheme over $S$.

**Proof.** By affine-local finite refinement and transitivity, take $S$ and $T$ affine and the
cover a single faithfully flat map of finite presentation. Given an affine open $W_0\subset V$,
transport $W_0\times_ST$ across the descent isomorphism and project it to the other copy of $V$.
The projection is open because a flat morphism of finite presentation is universally open, and
its image $W$ is quasi-compact because $W_0\times_ST\to W$ is quasi-compact and surjective.
The cocycle gives

$$
\theta(W\times_ST)=T\times_SW,
$$

so $W$ is invariant and contains $W_0$. Now $W\to T$ is quasi-compact, separated, and locally
quasi-finite, hence quasi-finite and separated. Zariski's Main Theorem factors it as a
quasi-compact open immersion into a finite $T$-scheme, so it is quasi-affine. On an affine part of
$T$, this open is a finite union of principal opens in an affine scheme; their defining functions
restrict to $W$. Writing $g:W\to T$, they show directly that the canonical map
$W\to\operatorname{Spec}_T(g_*\mathcal O_W)$ is a quasi-compact open immersion. Flat base
change identifies the two pullbacks of $g_*\mathcal O_W$, so this
quasi-coherent algebra descends; affine descent gives the relative spectrum, and the canonical
open just constructed is invariant and therefore descends by the quotient-topology argument of
Section 10.1.
Such $W$ cover $V$; intersections are invariant opens and full faithfulness descends their
gluing maps and triple cocycle. The descended pieces therefore glue to the required scheme.
$\square$

Next let $R\rightrightarrows U$ be an étale equivalence relation in schemes and let $F=U/R$ be
the fppf sheafification of the orbit presheaf. We prove, rather than assume, that $F$ is an
algebraic space.

Take first $U$ affine. The map $j=(s,t):R\to U\times_SU$ is a monomorphism. Hence it is separated.
Moreover $U\times_SU$ is separated as a scheme: it maps monomorphically to the affine scheme
$U\times U$. Thus $R$ and the two maps $s,t:R\to U$ are separated. Because $s$ and $t$ are
étale, $j$ is locally of finite type with finite fibers, and therefore is separated and locally
quasi-finite. Let a scheme $A$ map to $F$. By the definition of fppf
sheafification there is an fppf cover $A_i\to A$ and lifts $a_i:A_i\to U$. Then

$$
A_i\times_FU\simeq A_i\times_{a_i,U,t}R.                 \tag{11.1}
$$

The right side is a scheme separated and locally quasi-finite over $A_i$. On double overlaps the
two schemes in (11.1) have their canonical descent isomorphism, so the preceding lemma glues them
to a scheme representing $A\times_FU$. Thus $U\to F$ is representable. Its base change to each
$A_i$ is the étale surjection $A_i\times_{a_i,U,t}R\to A_i$; étaleness and surjectivity are local
on the base, so $U\to F$ is étale and surjective.

It remains to check the diagonal, rather than infer it from a picture. For a scheme
$A\to F\times F$, put $A' = A\times_{F\times F}(U\times_SU)$. The map $A'\to A$ is an étale
surjection by what was just proved, and

$$
A'\times_A(A\times_{F\times F}F)
\simeq A'\times_{U\times_SU}R.                           \tag{11.2}
$$

The right side is a separated locally-quasi-finite scheme over $A'$. Its canonical descent datum
along $A'\to A$ is effective by the lemma, so (11.2) descends to a scheme representing the
pullback of the diagonal. Hence the diagonal of $F$ is representable and $U\to F$ is an étale
scheme atlas.

For general $U$, replace it by the disjoint union of an affine open cover. Restricting $R$ gives
another étale equivalence relation with the same quotient sheaf. On each affine component the
preceding construction gives an algebraic space $F_i$. Its map to $F$ is a representable open
immersion. To check this, pull back by an fppf-local lift $A'\to U$ of any $A\to F$; the inverse
image is the pullback to $A'$ of the saturation

$$
t\bigl(s^{-1}(U_i)\bigr)\subseteq U,
$$

which is open because $s^{-1}(U_i)$ is open and the étale map $t$ is open. Open subschemes and
their inclusions descend along the fppf cover $A'\to A$, proving representability. The $F_i$
cover $F$. Choose a scheme atlas of each $F_i$; their disjoint union is an étale surjective
scheme atlas of $F$. Finally, after pulling a proposed diagonal fiber product back to the open
cover by the $F_i\times F_j$, it is the intersection $F_i\times_FF_j$, an open subspace of
$F_i$. After any further map from a scheme this is an open subscheme; those open schemes glue by
open descent. Thus the diagonal is representable. We have
proved the quotient theorem:

**Quotient theorem for étale equivalence relations.** The fppf sheaf quotient $U/R$ is an
algebraic space, $U\to U/R$ is representable, étale, and surjective, and
$R\simeq U\times_{U/R}U$.

Now let $p:T\to S$ be a surjective étale morphism and let $X_T$ be a $T$-scheme with descent
isomorphism $\theta:p_1^*X_T\to p_2^*X_T$. Regard $U=X_T$ as an $S$-scheme and set

$$
R=p_1^*X_T,
$$

with source the projection to $X_T$ and target its composite with $\theta$. The unit, inverse,
and composition come respectively from the diagonal, transposition, and triple cocycle. Both
arrows are base changes of $p$, hence étale, and $(s,t)$ is a monomorphism because the datum
identifies at most one arrow over a fixed pair. Thus $R\rightrightarrows U$ is an étale
equivalence relation. Its quotient $X=U/R$ is an algebraic space by the theorem, and base change
to $T$ is $X_T$: after that base change the cover is split by the diagonal $T\to T\times_ST$, and
the quotient of a split descent datum is its degree-zero object.

Equivalently, on an $S$-scheme $A$ the same quotient is the equalizer sheaf

$$
X(A)=\left\{x\in X_T(A_T):
\theta(p_1^*x)=p_2^*x\text{ in }X_T(A_{T\times_ST})\right\}.       \tag{11.3}
$$

Because representable functors are fpqc sheaves and equalizers of sheaves are sheaves, (11.3) is
an fpqc sheaf. It is also the fppf quotient just constructed: both sheaves coequalize the same
relation, and after the étale cover $T\to S$ both become the split quotient $X_T$. For the
pullback assertion, apply the same formula over $T$ and use the diagonal section of the pulled-back cover; an invariant
section is uniquely determined by, and reconstructed from, its restriction along that section.
The equalizer formula for maps proves full faithfulness. We have therefore proved:

**Unrestricted étale scheme-to-space descent theorem.** Every scheme with descent datum along a
surjective étale cover has a unique algebraic-space descent, represented by (11.3). Compatible
morphisms descend uniquely. Here “unrestricted” concerns the geometry of the scheme upstairs;
it does not change “étale” into “fpqc.”

For an arbitrary fpqc $p:T\to S$, define $X$ by the same equalizer formula (11.3). It is an fpqc
sheaf. Moreover $X\times_ST\simeq X_T$ already at the sheaf level: the pulled-back cover
$T\times_ST\to T$ has the diagonal section, and restriction to that section and extension by the
given cocycle are mutually inverse on the equalizer. The same split-cover argument gives full
faithfulness for compatible maps. To promote this sheaf to an algebraic space one would still
have to construct a representable diagonal and a surjective étale scheme atlas. The next theorem
does one necessary job—descending a quasi-compact separated étale object once it already carries
descent data—but does not construct such objects equivariantly.

We need one topological fact about fpqc morphisms. For a quasi-compact and quasi-separated scheme
$Y$, write $Y^{\mathrm{cons}}$ for its **constructible topology**: a constructible subset is open
and closed, and these subsets form a basis. This topology is compact and Hausdorff. A
quasi-compact morphism is closed for constructible topologies, while a morphism locally of finite
presentation is open for them. These assertions reduce to affines: Boolean combinations of
principal opens pull back to Boolean combinations of principal opens, and compactness says that a
cover by such combinations has a finite subcover.

There is a second topology, recording specialization. Write $y_0\leadsto y_1$ when $y_1$ is a
specialization of $y_0$. If $A\to B$ is faithfully flat and
$\mathfrak p_0\subseteq\mathfrak p_1$ in $A$, choose
$\mathfrak q_1$ over $\mathfrak p_1$ and apply going-down to obtain
$\mathfrak q_0\subseteq\mathfrak q_1$ over $\mathfrak p_0$. The same argument after every base
change proves:

**Specialization-lifting lemma.** An fpqc morphism is universally surjective both for the
constructible topology and for ordered specialization pairs. Consequently, if a saturated subset
has pro-constructible inverse image upstairs, then it is pro-constructible downstairs; if in
addition it is stable under specialization, it is closed in the Zariski topology. The analogous
statement with generization gives open subsets.

For the constructible assertion, reduce to a faithfully flat map of affines. Its map on spectra is
a quotient map because it is a continuous closed surjection in the compact Hausdorff
constructible topologies. Saturation is exactly equality of the two inverse images on the double
overlap. A pro-constructible saturated subset therefore descends. In a spectral space, the
Zariski closure of a pro-constructible subset consists precisely of its specializations: if a
point is not such a specialization, a quasi-compact open separates it from the subset, by
compactness in the constructible topology. Thus specialization stability makes the subset
Zariski closed. This also proves the assertions after arbitrary base change.

We can now prove the exact étale effectivity result needed below.

**Constructible-étale fpqc effectivity theorem.** Let $q:T\to S$ be fpqc. Pullback is an
equivalence between quasi-compact separated étale $S$-schemes and quasi-compact separated étale
$T$-schemes with descent datum.

**Proof.** Full faithfulness is first. The graph of a map between separated étale schemes is both
open (it is a section of an étale map) and closed (the target is separated). A compatible graph
upstairs is saturated, so the specialization-lifting lemma descends its open-and-closed
underlying subset. Flat descent of its ideal and of the complementary localization makes it an
open-and-closed subscheme of the product downstairs. Its first projection becomes an isomorphism after the fpqc
cover and hence is an isomorphism; the descended graph is the unique required map.

For effectivity, all ingredients are quasi-compact, so reduce to $S$ and $T$ affine. Zariski's
Main Theorem factors $E_T\to T$ as a quasi-compact open immersion

$$
E_T\hookrightarrow \overline E_T
$$

with $\overline E_T\to T$ finite. In particular $E_T$ is quasi-affine. We spell out the descent
rather than appeal to étale-local gluing. For $g:E_T\to T$, the intrinsic algebra
$g_*\mathcal O_{E_T}$ is quasi-coherent: use a finite affine cover and the finite equalizer of
functions on its pairwise intersections. Flat base change identifies its two pullbacks, so affine
descent gives an affine $S$-scheme

$$
\overline E=\operatorname{Spec}_S(g_*\mathcal O_{E_T})^{\mathrm{desc}}.
$$

The canonical map $E_T\to\operatorname{Spec}_T(g_*\mathcal O_{E_T})$ is a quasi-compact open
immersion. Its image is saturated because the construction is intrinsic. The
specialization-lifting lemma descends that image to an open of $\overline E$: on affine charts it
is the unique subset whose inverse image is the given saturated open, and flat descent of the
corresponding localized algebras supplies its scheme structure. Call the resulting open scheme
$E$. Then $E\times_ST\simeq E_T$ compatibly with the datum. Quasi-compactness, separatedness, and
étaleness are reflected by the fpqc cover. This explicit affine-envelope and open-gluing
construction proves effectivity as a **scheme** and never chooses a section of $T\to S$.
$\square$

The constructible-étale theorem does **not** by itself construct an étale atlas for the equalizer
$X$ of an arbitrary scheme datum. To use it one would first need enough quasi-compact separated
étale maps $V_T\to X_T$ carrying genuine descent data. Starting with finite affine charts does not
produce those data automatically.

Here is the precise obstruction in a frequently attempted construction. Put

$$
R_X=p_1^*X_T=X_T\times_{T,p_1}(T\times_ST),
$$

with source the projection and target the descent isomorphism followed by projection to $X_T$.
For a proposed finite étale chart-choice $C\to X_T$, equivariance is an isomorphism
$s^*C\simeq t^*C$ over the **whole** arrow scheme $R_X$, and the cocycle is an equality over the
scheme $R_X\times_{s,X_T,t}R_X$ of composable arrows. A fiberwise isomorphism functor may be
finite étale over $R_X$, but the functor of its global sections along $s:R_X\to X_T$ is a
Weil-restriction/equalizer functor. A quasi-compact flat map need be neither finite nor proper, so
no representability theorem used here
makes that section functor a scheme. Constructible compactness can select finitely many open
subsets of an orbit; it cannot turn a section over all of $R_X$ into finitely many algebraic
equations. Thus the alleged finite-choice scheme, and hence the alleged atlas and representable
diagonal, have not been constructed.

Accordingly, the proved unrestricted statement for an arbitrary fpqc cover is exactly this:

**Fpqc equalizer theorem.** Formula (11.3) defines an fpqc sheaf $X$ with
$X\times_ST\simeq X_T$, compatibly with the given datum, and compatible morphisms descend
uniquely. If the cover is surjective étale, $X$ is the algebraic space constructed above. For a
general fpqc cover this chapter makes no unconditional algebraicity assertion.

This boundary is not repaired by quoting that algebraic spaces are fpqc sheaves: that result is
the full-faithfulness statement for maps into an algebraic space already known to exist. An
algebraicity theorem for a broader class of covers would have to construct a representable
diagonal and an étale atlas; no such construction is asserted here.

The conclusion that the quotient is a scheme still requires a separate criterion. Descent data
relative even to an étale cover can be ineffective in schemes although the local scheme is
projective. Thus neither properness nor local projectivity alone repairs scheme effectivity.

### 11.2 Why the scheme assertion fails

Write $p_1,p_2:T\times_ST\to T$. If $V\subseteq X_T$ is open, call it **invariant** when

$$
\theta(p_1^{-1}V)=p_2^{-1}V.
$$

An invariant affine open descends by Chapter 7. It is tempting to claim that every point of
$X_T$ has such a neighborhood. That claim is false. In a noneffective scheme descent datum, the
orbits of the overlap groupoid cannot be enclosed in enough invariant affine opens; if they
could, the construction of Section 11.3 would produce a scheme quotient and contradict
noneffectivity.

Quasi-compactness of the groupoid arrows does not cure the problem. It can make an orbit or a
finite list of conditions manageable, but it does not imply that an entire orbit lies in one
affine open. Nor can arbitrary affine neighborhoods be intersected and transported until they
become invariant: the transported collection need not have an affine common neighborhood. This
is precisely the invalid step in the unrestricted stable-affine-neighborhood argument.

The cocycle remains necessary. Without it, the two arrows do not define an equivalence relation
at all. But the cocycle is not sufficient for a quotient sheaf to be a scheme. Along a surjective
étale cover the elementary quotient proof supplies the algebraic space. For a general fpqc cover,
including an fppf cover not known to be étale, the equalizer exists as a sheaf, but Section 11.1
deliberately does not assert that it is algebraic. Invariant affine opens bypass both issues by
constructing a scheme directly.

### 11.3 The invariant-affine criterion

Although invariant affine neighborhoods do not exist automatically, their existence is an exact
and useful sufficient criterion.

**Invariant-affine scheme criterion.** Let $X_T$ be a $T$-scheme with fpqc descent datum. If
$X_T$ has a cover by invariant affine opens $V_\alpha$, then the equalizer sheaf (11.3) is
represented by an $S$-scheme. The same holds for an fpqc covering family, with invariance
interpreted on every pairwise overlap.

Indeed, affine descent produces an affine $S$-scheme $U_\alpha$ from each $V_\alpha$. The open
$V_\alpha\cap V_\beta\subseteq V_\alpha$ is invariant. Since
$V_\alpha\to U_\alpha$ is fpqc and surjective, the quotient-topology argument of Section 10.1
identifies its underlying subset with the pullback of a unique open
$U_{\alpha\beta}\subseteq U_\alpha$. Affine-local descent of the structure sheaf identifies
$V_\alpha\cap V_\beta$ with
$U_{\alpha\beta}\times_ST$, so this is descent as an open subscheme, not only
as a subset. The same construction from $V_\beta$ gives an isomorphic open of $U_\beta$.
Full faithfulness descends the overlap isomorphism, and the triple cocycle descends to the usual
Zariski gluing cocycle. Gluing the $U_\alpha$ gives the desired scheme.

This proof also gives uniqueness among scheme descents. More generally, uniqueness never causes
the obstruction: morphisms of schemes satisfy fpqc descent by Section 10.1, so any scheme
representing the equalizer sheaf is unique up to unique isomorphism. The obstruction is
existence of a scheme cover downstairs.

There are useful variants. It suffices to exhibit a cover by invariant open subschemes whose
descents are already known to be schemes. Likewise, a compatible immersion into an $S$-scheme
reduces effectivity to descent of the corresponding invariant open or closed subscheme.

### 11.4 The first scheme cases

The following cases have been proved at this point and are safe to use in the next two chapters.

- **Affine data.** Chapter 7 constructs the descended affine scheme from the descended
  quasi-coherent algebra. Closed subschemes and compatible affine equations descend with it.
- **Finite and finite locally free data.** Such morphisms are affine, so Chapter 7 applies; the
  relevant module properties then descend by Chapter 6. The same applies to finite locally free
  group schemes and their affine torsors.

A bare assertion that the local object is proper, projective, or a group scheme is not on this
list. Projectivity is useful only when the polarization or embedding participates in the cocycle.
Similarly, contracted products and twists exist without qualification as fpqc sheaves. At this
stage they are schemes when their local model is affine, finite, or finite locally free. Later
chapters prove additional direct scheme criteria without first assuming algebraicity of the
equalizer.

## 12. Finite-flat group objects and actions

### 12.1 Group laws descend

An $S$-group scheme is an $S$-scheme $G$ with multiplication, identity, and inverse maps

$$
m:G\times_SG\to G,
\qquad e:S\to G,
\qquad i:G\to G,
$$

satisfying the group diagrams. Suppose $G_T$ carries descent data and these three maps are
compatible. The equalizer theorem of Section 11.1 descends the underlying fpqc sheaf and the maps
$m,e,i$. Associativity, the unit identities, and the inverse identities are equalities of maps and
can be checked after the cover. Commutativity is likewise the equality $m=m\circ\tau$. For a
surjective étale cover the underlying sheaf is an algebraic space by Section 11.1. For an
arbitrary fpqc cover, including a general fppf cover, one must instead apply a direct scheme
criterion or supply a separate algebraicity theorem.

To conclude that $G$ is a group **scheme**, apply a scheme criterion from Section 11.4. In
particular, affine group schemes descend as affine group schemes. Finite and finite locally free
group schemes are affine, so they form effective fpqc descent categories; their finiteness,
flatness, and rank descend by Chapters 6 and 7. A general nonaffine group scheme with descent data
need not have a scheme descent merely because its group laws descend.

### 12.2 Hopf-algebra form

When $G=\operatorname{Spec}H$ is affine, the group maps correspond to

$$
\Delta:H\to H\otimes_AH,
\qquad \epsilon:H\to A,
\qquad S:H\to H.
$$

Coassociativity, counit, and antipode identities are equations of algebra maps. Algebra descent first recovers $H$ and then recovers these maps. If $H_B$ is finite projective over $B$, then $H$ is finite projective over $A$. This gives a particularly transparent proof for finite locally free group schemes.

Dualization is legitimate for finite projective $H$. The dual $H^\vee$ commutes with base change, and the transpose of the Hopf maps again descends. Consequently constructions based on finite duality commute with fpqc descent. The finite-projective hypothesis is decisive: dualizing an arbitrary module does not commute reliably with base change and need not recover a representable object.

### 12.3 Subgroups, homomorphisms, and exactness

A homomorphism $G_T\to H_T$ compatible with descent data descends uniquely between their
fpqc-sheaf descents because the underlying map is an fpqc-sheaf morphism and compatibility
with multiplication and identity is detected upstairs. If the equalizers are algebraic spaces,
this is a homomorphism of algebraic spaces. If $G$ has already been shown to be a scheme, a compatible closed subgroup
$K_T\hookrightarrow G_T$ descends through its quasi-coherent ideal as a closed subscheme of $G$;
the group structure restricts and descends. In particular, finite locally free subgroup data are
affine and descend to a finite locally free group scheme.

For a sequence of finite locally free commutative group schemes

$$
0\longrightarrow G'\longrightarrow G\longrightarrow G''\longrightarrow0,
$$

the meaning of exactness is sheaf-theoretic for the fppf topology: the first map identifies $G'$ with the kernel and the second is an fppf epimorphism with that kernel. Kernels are fiber products and commute with base change. Being a closed immersion and being faithfully flat locally of finite presentation descend. Thus exactness can be checked fpqc-locally, provided the asserted quotient map has the stated finiteness and flatness.

### 12.4 Actions and quotients in the finite case

An action $a:G\times_SX\to X$ is another morphism satisfying identity and associativity diagrams,
so compatible actions descend. A fixed-point construction descends whenever its representing
equalizer has been formed; no general representability claim is needed here.

Let a finite locally free group scheme $G$ act on an affine $X=\operatorname{Spec}R$. The affine quotient is

$$
\operatorname{Spec}(R^G),
\qquad
R^G=\{r:a^*(r)=1\otimes r\}.
$$

This is an equalizer and commutes with flat base change because flat tensor product preserves
equalizers; finite local freeness of $G$ ensures that the coaction is represented by the finite
projective Hopf algebra. If the action is free in the torsor sense,
$X\to\operatorname{Spec}(R^G)$ is finite locally free and the expected orbit relation is
effective.

For nonaffine $X$, representability of either a quotient or a fixed-point functor may require
invariant affine neighborhoods or a separate theorem. Descent preserves such an object once it
has been constructed; it must not be cited as constructing every group quotient.

## 13. Torsors

### 13.1 The torsor identity

Let $G$ be an $S$-group scheme acting on the right on an $S$-scheme or algebraic space $P$. The
action is **simply transitive over the base** when

$$
P\times_SG\longrightarrow P\times_SP,
\qquad(p,g)\longmapsto(p,pg)
$$

is an isomorphism. An **algebraic-space $G$-torsor for the fpqc topology** is such a $P$ with
$P\to S$ an fpqc cover. It is a **scheme torsor** when $P$ is a scheme. For an fppf torsor one
asks $P\to S$ to be fppf. This vocabulary keeps representability separate from the torsor
identity.

The isomorphism says that any two points in the same fiber differ by a unique group element. The covering condition says that points exist locally. Both clauses are necessary: the empty scheme satisfies the displayed isomorphism vacuously but is not a torsor.

If $G\to S$ is finite locally free of positive rank and a torsor is given by fpqc local
trivializations with cocycle, the local model $G$ is affine. Chapter 7 therefore constructs the
torsor directly as an affine scheme, and Chapter 6 makes it finite locally free of the same rank.
Thus the finite locally free torsors constructed from descent data in this book have no
algebraic-space ambiguity; no general flat-quotient theorem is needed for them.

### 13.2 Local triviality and effectivity

Conversely, suppose $P_T\simeq G_T$ over a cover $T\to S$, with transition maps that are
$G$-equivariant and satisfy the cocycle. Section 11.1 gives an fpqc equalizer sheaf $P$ for every
fpqc cover; it is an algebraic space when the cover is surjective étale. The action maps and
torsor identity descend by full faithfulness, and the covering property is checked after
$T\to S$. If $G$ is affine, Chapter 7 applies directly to the affine local model $G_T$ and makes
$P$ an affine scheme. If $G$ is finite locally free, the descended affine morphism has the same
property and rank by Chapter 6.

Choose trivializations $P_{T_i}\simeq G_{T_i}$. We retain the convention of Section 4.4 that
$\theta_{ij}$ transports from the $i$th trivialization to the $j$th. A $G$-equivariant
automorphism of the right regular $G$-space is left translation by a unique element
$g_{ij}\in G(T_i\times_ST_j)$. Since composition of left translations reverses the written
transport order, the cocycle is

$$
g_{ik}=g_{jk}g_{ij}.
$$

If the new $i$th trivialization is left translation by $h_i$ followed by the old one, then

$$
g'_{ij}=h_jg_{ij}h_i^{-1}.
$$

These two displayed orders follow from the declared right-action and $i$-to-$j$ conventions; using
the opposite convention reverses both formulas. This is the noncommutative cocycle description
of torsors. It is a pointed classification: the trivial torsor corresponds to the identity
cocycle.

### 13.3 Contracted products and twisting

If $P$ is a right $G$-torsor and $G$ acts on the left on $X$, the contracted product is locally the quotient of $P\times_SX$ by the right action

$$
(p,x)\cdot g=(pg,g^{-1}x).
$$

Trivialize $P$ locally. On each trivializing member the desired object is $X$, and on overlaps the
torsor cocycle acts on $X$. The action law supplies the triple cocycle, so Section 11.1 produces
an fpqc sheaf

$$
P\times^GX.
$$

After pullback to $P$, it is isomorphic to $X_P$.

When the trivializing cover is surjective étale this sheaf is an algebraic space. For an arbitrary
fpqc trivialization, the affine criterion constructs it directly as a scheme, without first
assuming algebraicity.

**Contracted-product representability theorem.** The contracted product $P\times^GX$ is a
scheme in each of the following cases:

1. $X\to S$ is affine;
2. $X\to S$ is finite or finite locally free.

**Proof.** The transition automorphisms preserve the affine structure, so Chapter 7 descends the
coordinate algebra. Finiteness, flatness, and rank then descend by Chapter 6. The construction
pulls back to $X_P$ and satisfies the required sheaf
quotient universal property by fpqc full faithfulness, so it represents the contracted-product
sheaf. $\square$

Once scheme effectivity has been established, every property in Chapter 10 that is fpqc local
on the base passes to the twist. Smoothness or properness alone does not prove that the twist is
a scheme; without one of the displayed criteria they describe the local model and the descended
fpqc sheaf. A general fppf trivialization by itself does not strengthen that conclusion in this
book.

For a representation of $G$ on a finite locally free sheaf $V$, the same construction yields an associated vector bundle $P\times^GV$. Tensor operations and invariant pairings descend. This mechanism produces the bundles and tensors attached to level structures and PEL data.

### 13.4 Examples and boundary cases

For $G=\mathbf G_m$, torsors and line bundles encode one another. From a line bundle $\mathcal L$, remove the zero section from its total space, or equivalently take the sheaf of trivializations of $\mathcal L$; scalar multiplication gives a $\mathbf G_m$-torsor. From a torsor $P$, contract with the standard one-dimensional representation. These constructions are inverse by local triviality and descent.

For $G=\operatorname{GL}_r$, the frame bundle of a rank-$r$ vector bundle is a torsor, and the associated bundle for the standard representation recovers the vector bundle. For $\mu_n$, the equation $z^n=a$ gives a torsor where $a$ is a unit; when $n$ is not invertible on the base it is generally fppf rather than étale. This is one reason finite-flat descent, not only étale descent, is indispensable in integral moduli problems.

A transitive action on geometric points is not enough to be a torsor. Infinitesimal stabilizers
may remain invisible on geometric points. The isomorphism $P\times G\simeq P\times P$ detects
them. Likewise a quotient on topological spaces does not supply the structure sheaf or its
effectivity. General torsor and contracted-product descent always gives an fpqc sheaf. A
surjective étale trivialization gives an algebraic space, and scheme representability is the
additional conclusion supplied by a direct criterion.

## 14. Quasi-affine descent

### 14.1 Intrinsic affine envelopes

An $S$-scheme $X$ is quasi-affine over $S$ when it admits an open immersion into an affine $S$-scheme. An arbitrary chosen embedding is awkward for descent: its ambient affine scheme may have no overlap datum. The remedy is an intrinsic ambient scheme.

Assume $f:X\to S$ is quasi-compact and quasi-separated. Then $f_*\mathcal O_X$ is a quasi-coherent $\mathcal O_S$-algebra. To see this, work over $U=\operatorname{Spec}A$, choose a finite affine cover $V_i$ of $X_U$, and use quasi-separatedness to cover every $V_i\cap V_j$ by finitely many affines. Global functions are the equalizer of the product of the coordinate rings of the $V_i$ and the product over these intersection charts. Localization of $A$ is flat and commutes with this finite equalizer. Therefore the resulting module sheaf is quasi-coherent.

Define the affine envelope

$$
\mathbf A(X/S)=\operatorname{Spec}_S(f_*\mathcal O_X).
$$

Evaluation of functions gives a canonical map

$$
j_X:X\longrightarrow\mathbf A(X/S).
$$

If $X$ is quasi-affine and quasi-compact over $S$, this map is a quasi-compact open immersion. Indeed, locally write $X$ as a quasi-compact open of $\operatorname{Spec}R$. It is a finite union of principal opens $D(f_i)$. The functions $f_i$ live on $X$, and $j_X^{-1}D(f_i)=D(f_i)$; these principal opens cover and on each the map on coordinate rings is the identity after localization. Conversely, if $j_X$ is an open immersion, $X$ is quasi-affine by definition.

### 14.2 Descending quasi-affine schemes

Let $T\to S$ be fpqc, and let $X_T\to T$ be a quasi-compact quasi-separated quasi-affine scheme
with descent datum. We construct its descent as a scheme, without assuming general scheme
effectivity.

Put

$$
\mathcal A_T=(f_T)_*\mathcal O_{X_T}.
$$

The finite affine equalizer of Section 14.1 shows both that $\mathcal A_T$ is quasi-coherent and
that its formation commutes with the flat pullbacks in the Čech nerve. The datum on $X_T$
therefore induces a genuine algebra descent datum on $\mathcal A_T$. Quasi-coherent algebra
descent gives an algebra $\mathcal A$ on $S$ and hence an affine $S$-scheme

$$
Y=\operatorname{Spec}_S\mathcal A
$$

whose pullback is the intrinsic affine envelope of $X_T$.

The canonical map

$$
j_T:X_T\longrightarrow Y_T
$$

is a quasi-compact open immersion. Its image is invariant: functoriality of the affine envelope
makes the two pullbacks of $j_T$ correspond under the descent datum. Since $Y_T\to Y$ is an fpqc
quotient map on underlying spaces, this invariant open is the inverse image of a unique open
$X\subseteq Y$. Descent of the open immersion, checked affine-locally by localization of
$\mathcal A$, identifies $X_T$ with $X\times_ST$ and recovers the original cocycle. Thus $X$ is
a quasi-affine $S$-scheme.

We have proved both effectivity and the property statement:

**Quasi-affine descent theorem.** Quasi-compact quasi-separated quasi-affine schemes and their
morphisms satisfy effective fpqc descent. Equivalently, quasi-affineness is fpqc local on the base
among quasi-compact quasi-separated morphisms once the underlying scheme exists.

The hypotheses are not ornamental. Without quasi-compactness, the canonical map into the spectrum
of global functions need not exhibit a quasi-affine scheme as a quasi-compact open, and the finite
equalizer proof of flat base change breaks down. One can formulate a locally quasi-affine variant
by working on quasi-compact opens, but later moduli applications are finitely presented and hence
fall within the stated theorem.

### 14.3 Finite presentation and openness

Suppose $X_T$ is not merely quasi-affine but of finite presentation over $T$. Finite presentation descends, so $X$ is of finite presentation over $S$. The open immersion $j_X$ is then quasi-compact and locally of finite presentation. Over an affine open of the envelope, its image is a quasi-compact open and hence a finite union of principal opens. Thus the descended quasi-affine presentation uses finitely much algebraic data.

This finiteness is useful in parameter problems. Conditions imposed by nonvanishing of finitely many determinants define quasi-affine loci. They may be checked after an fpqc trivialization of the relevant bundles, but the determinant sections and their common nonvanishing locus descend. The affine-envelope theorem ensures that the result remains a scheme of finite presentation rather than an uncontrolled union.

### 14.4 The precise reusable criterion

The criterion used later can be stated without mentioning a chosen embedding. Let $f:X\to S$ be
quasi-compact and quasi-separated. Then the following are equivalent:

1. $f$ is quasi-affine;
2. $j_X:X\to\operatorname{Spec}_S(f_*\mathcal O_X)$ is a quasi-compact open immersion;
3. after restricting to any affine open $U\subseteq S$, finitely many relative functions
   $g_i\in\Gamma(X_U,\mathcal O_{X_U})$ have affine principal opens $(X_U)_{g_i}$ which cover
   $X_U$.

The implication $1\Rightarrow2$ was proved by principal opens; $2\Rightarrow1$ is immediate. For
$2\Rightarrow3$, pull back finitely many standard principal opens of the affine envelope.
Conversely, on $(X_U)_{g_i}$ the canonical map identifies the coordinate ring with the
localization of $\Gamma(X_U,\mathcal O)$ at $g_i$. These identifications agree on
$D(g_ig_j)$, so $j_X$ is an open immersion. This criterion is stable under flat base change and
is therefore suited to descent.

## 15. Quasi-projective and projective descent

### 15.1 Polarized descent

Projective geometry requires positivity, and positivity is carried by a line bundle. Let
$T\to S$ be fpqc, let $X_T\to T$ be a quasi-compact finitely presented scheme with descent datum,
and let $\mathcal L_T$ be an invertible sheaf whose overlap isomorphism is compatible with that
datum and satisfies its own cocycle.

We construct the scheme directly, so no unrestricted algebraic-space theorem is hidden here. Put

$$
\mathcal A_T=\bigoplus_{n\geq0}(f_T)_*\mathcal L_T^{\otimes n}.
$$

Finite presentation makes $f_T$ quasi-compact and quasi-separated. The finite affine Čech
equalizer therefore proves flat base change for every graded piece, and multiplication is
preserved. The scheme and line-bundle cocycles induce a graded quasi-coherent algebra descent
datum on $\mathcal A_T$. Descend it to $\mathcal A$ on $S$ and form
$Y=\operatorname{Proj}_S(\mathcal A)$.

If $\mathcal L_T$ is relatively ample, the canonical map

$$
X_T\longrightarrow\operatorname{Proj}_T(\mathcal A_T)=Y_T
$$

is an open immersion. Indeed, affine-locally on $T$, positive-degree sections $s_i$ may be chosen
so that the affine opens $(X_T)_{s_i}$ cover; on each one the canonical map identifies it with
the standard affine open determined by the corresponding homogeneous element. Quasi-compactness
selects finitely many $s_i$ locally on the base. Functoriality makes the image invariant under the
cocycle. Since $Y_T\to Y$ is fpqc, the quotient-topology lemma descends that image to an open
subscheme $X\subseteq Y$, and affine descent on the standard opens identifies
$X_T\simeq X\times_ST$ with the original cocycle. Now vector-bundle descent on the already
constructed $X$ descends $\mathcal L_T$ to $\mathcal L$; ampleness is reflected by the same
standard-open criterion. Thus the polarization is the datum that proves scheme effectivity.

Relative ampleness is preserved and reflected by faithfully flat quasi-compact base change under
these hypotheses. It is tested affine-locally on $S$ by positive tensor powers and sections whose
nonvanishing loci are affine and cover $X$; pullback preserves such a cover. Thus

$$
\mathcal L\text{ is }f\text{-ample}
\quad\Longleftrightarrow\quad
\mathcal L_T\text{ is }f_T\text{-ample}.
$$

It follows that a **polarized quasi-projective object** $(X,\mathcal L)$ satisfies effective fpqc
descent when $f$ is of finite presentation and $\mathcal L$ is relatively ample. If $S$ is
quasi-compact, one sufficiently high power gives one finite-rank projective-bundle embedding over
all of $S$; without that hypothesis the conclusion and embedding are local on $S$. The word
polarized means that the overlap datum includes the line bundle and its cocycle, not merely that
some ample line bundle exists after the cover.

### 15.2 Very ampleness and closed immersions

Suppose $\mathcal L_T$ is relatively very ample and the datum includes a finite locally free
sheaf $\mathcal E_T$ on $T$, its descent datum, and a compatible surjection

$$
f_T^*\mathcal E_T\twoheadrightarrow\mathcal L_T
$$

whose associated morphism is an immersion

$$
X_T\hookrightarrow\mathbf P_T(\mathcal E_T).
$$

Descend $\mathcal E_T$, the quotient map, and the induced morphism to projective space. If the
upstairs immersion is closed, closed immersion is fpqc local, so the descended map is closed.
Thus very ampleness with its compatible finite system of sections descends; for a proper
$X_T/T$, the immersion is automatically closed.

For an ample line bundle, a sufficiently high power becomes very ample when $f$ is quasi-projective of finite presentation and the relevant finite generation theorem applies. Book 8 supplies this relative embedding result. Once one power and a finite set of sections have been chosen compatibly, the preceding paragraph descends the embedding. On a quasi-compact base the finite data give one global projective-bundle embedding. On an arbitrary base they do so locally on the base, which is the form used in local moduli constructions. Properness of the descended morphism follows independently from Chapter 10.

The distinction between a closed and an open immersion is stable under descent. Thus if $X_T$ is exhibited as a locally closed subscheme of a projective bundle by compatible data, the locally closed immersion and its image descend, giving a quasi-projective $X$.

### 15.3 Producing compatible positive data

The norm construction requires a representable target first. Suppose a criterion above has
constructed the scheme descent $X$ (or the surjective étale case has constructed an algebraic-space descent)
and let $q:X_T\to X$ be the pullback map. If this particular $q$ is finite locally free, then

$$
N_q(\mathcal M)=\det(q_*\mathcal M)\otimes
\det(q_*\mathcal O_{X_T})^{-1}
$$

is an invertible sheaf on the algebraic space $X$. Positivity of this norm, and the assertion that
an algebraic space carrying it is a scheme, are separate theorems with their own hypotheses. They
are not consequences of the determinant formula. Consequently this book does not use a finite
locally free base cover by itself to remove the need for compatible positive data when a
**scheme** is required. For a general fpqc cover the norm cannot be used to prove algebraicity of
the equalizer, because writing the determinant already presupposes the representable target and
the finite locally free morphism $q$.

In moduli problems the object may instead carry compatible positive data. A marked effective
Cartier divisor $D_T$ gives $\mathcal O(D_T)$ with descent datum. If a fixed power is ample,
polarized descent applies. On a reducible curve the divisor must meet every geometric component;
the identity divisor alone does not do so on a polygon with more than one component. For an
abelian scheme, an ample rigidified line bundle may be used only when its overlap isomorphisms and
triple cocycle are part of the data. Rigidification removes scalar automorphisms of an already
chosen overlap isomorphism, but does not by itself create an isomorphism between two unrelated
line bundles. Thus no general assertion about arbitrary polarization classes is being smuggled
into the argument.

### 15.4 Limits of the statement

One must not argue: “$X_T$ has some ample line bundle, therefore that line bundle descends.” Its two pullbacks may not even be isomorphic, and chosen isomorphisms may fail the cocycle. The safe statements proved here are:

- quasi-projectivity descends with a compatible relatively ample line bundle, globally when the
  finite embedding data are uniform and otherwise locally on the base;
- it descends in a moduli problem when a canonical divisor, rigidified polarization, or explicitly chosen tensor power supplies compatible positive data.

These are exactly the forms used below. No unrestricted claim that an arbitrary locally existing polarization descends is needed. Similarly, proper plus quasi-projective implies projective because a quasi-projective immersion into projective space is locally closed and proper, hence closed. Properness alone does not produce a projective embedding over an arbitrary base.

### 15.5 The expanded scheme-effectivity package

Chapters 14 and 15 now add two direct criteria to the affine and finite cases of Section 11.4.
They do not first promote the equalizer sheaf to an algebraic space: each constructs a scheme and
then identifies its represented fpqc sheaf with the equalizer by full faithfulness.

- A quasi-compact, quasi-separated, quasi-affine scheme with descent datum descends through its
  intrinsic affine envelope and invariant canonical open immersion.
- A finitely presented scheme with a compatible relatively ample line bundle descends through its
  graded section algebra and invariant canonical open immersion in relative Proj. Compatible
  locally closed projective-bundle embeddings give the parallel embedded criterion.

These criteria apply in particular to the contracted product of Section 13.3. Let $P$ be a right
$G$-torsor, let $G$ act on the left on $X$, and give $P\times^G X$ the fpqc equalizer sheaf
constructed there. In addition to the affine and finite cases already proved in Chapter 13, this
sheaf is represented by a scheme in any of the following cases:

1. $X\to S$ is quasi-compact, quasi-separated, and quasi-affine;
2. $X$ carries a $G$-linearized relatively ample line bundle in the quasi-compact,
   finite-presentation range of Section 15.1;
3. $X$ has a $G$-equivariant locally closed immersion into a projective bundle associated to a
   finite locally free representation of $G$.

Indeed, in the first case the transition automorphisms act on the intrinsic affine envelope and
its canonical open immersion, so Chapter 14 constructs the descent. In the second, the
$G$-linearization supplies exactly the overlap isomorphism and triple cocycle for the ample line
bundle, so Section 15.1 applies. In the third, the representation descends the ambient projective
bundle, equivariance makes the locally closed image invariant, and Section 15.2 descends that
image. Each construction pulls back to $X_P$ and therefore represents the contracted-product
sheaf by fpqc full faithfulness.

Thus, outside the surjective étale case already treated in Section 11.1, an fppf-trivial contracted
product or twist is called an algebraic space here only when one of these direct criteria, or the
earlier affine or finite criterion, has actually produced a scheme. With no such criterion, the
conclusion remains the fpqc sheaf of Section 13.3. Smoothness, properness, or projectivity of the
local model alone does not change that target category.

## 16. The descent package for moduli geometry

### 16.1 Generalized elliptic curves

A generalized elliptic curve over $S$ consists, in the range relevant here, of a proper flat finitely presented family $E\to S$ whose geometric fibers are smooth genus-one curves or prescribed Néron polygons, a section $e:S\to E$ in the smooth locus, and a commutative group action of the smooth locus extending the usual translation action with the required behavior on components. Each clause is fpqc local once expressed scheme-theoretically.

Given such an object over $T$ with descent datum, a compatible positive divisor as below (or
another criterion from Section 11.4) constructs the scheme $E$ directly for an arbitrary fpqc
cover. Independently of that criterion, Section 11.1 supplies the underlying fpqc equalizer
sheaf, and supplies an algebraic space when the cover is surjective étale. Once $E$ is a scheme,
properness, flatness, finite presentation,
smoothness of the indicated locus, and the finite locally free component conditions descend by
Chapter 10. The group and action identities descend as equalities of morphisms.

The geometric fiber condition is unchanged by the residue-field extensions occurring here. After
passing two field extensions to a common algebraic closure, their geometric fibers become the
same scheme. Thus geometric irreducible components and their incidence graph agree. A node is
the étale-local plane singularity $uv=0$; that description is preserved and reflected by a
faithfully flat field extension. Finally, cover the proper separated fiber by finitely many
affines. Their finite intersections are affine, so the finite Čech complex computes coherent
cohomology. Tensoring that complex with a field extension is exact and gives the Čech complex of
the base-changed cover. The dimensions of the resulting finite-dimensional cohomology spaces are
unchanged, so

$$
\chi(\mathcal O)=\sum_i(-1)^i\dim H^i(\mathcal O),
$$

is unchanged. Thus the arithmetic genus agrees. This verifies, rather than assumes, descent of
the smooth genus-one and prescribed polygon alternatives.

For scheme effectivity and projectivity, the input to descent is a compatible finite effective
Cartier divisor $D_T$ and an integer $n>0$ for which $\mathcal O(nD_T)$ has already been verified
relatively ample over $T$.
This verification is part of the particular moduli presentation, not a consequence of descent.
On a smooth genus-one fiber the identity divisor is the usual candidate. On an $m$-gon with
$m>1$, however, the identity section lies on only one component, so its multiples cannot serve;
one instead uses a divisor in the smooth locus meeting every geometric irreducible component,
for example an orbit under specified level data when that orbit meets all components.
Compatibility of $D_T$ and its line bundle is part of the descent datum. Polarized descent
constructs the scheme by its descended section algebra; the relative embedding theorem then
supplies the projective embedding. Without this positive datum, arbitrary fpqc descent still
produces the equalizer sheaf, but the argument proves neither its algebraicity nor that it is a
scheme even though the local fibers are proper. This avoids both an unrelated ample bundle upstairs and the
false use of the identity divisor on a polygon.

Level structures are morphisms from finite locally free group schemes into the smooth group locus or its torsion. Their homomorphism identities descend. Conditions such as being a closed immersion, being finite locally free of a given rank, or giving a full set of sections are fpqc local. Exactness of subgroup sequences is interpreted in the fppf sense as in Section 12.3. Thus level structures at primes not invertible on the base are handled without pretending they are étale.

### 16.2 PEL objects

A PEL object comprises an abelian scheme $A\to S$, an action $\iota:\mathcal O\to\operatorname{End}_S(A)$ by a fixed finite algebra with involution, a polarization $\lambda:A\to A^\vee$, and a level structure, subject to determinant and compatibility conditions. Descent treats these pieces in a rigid order.

For every fpqc cover, Section 11.1 first descends the proper smooth group object as an fpqc
equalizer sheaf. The compatible positive data below construct the abelian **scheme** required by
the moduli problem directly; properness, smoothness, and geometric connectedness alone are not
effectivity inputs. For a surjective étale cover the intermediate equalizer is an algebraic space.
Endomorphisms $\iota(a)$ then descend by full faithfulness. Since $\mathcal O$ is finitely generated
as an abelian group in the applications, finitely many multiplication and involution identities
suffice, and all are equalities of maps.

For the polarization, a rigidified relatively ample line bundle with its genuine cocycle is the
safe scheme-effectivity input. The section-algebra construction of Section 15.1 makes $A$ a
scheme; properness, smoothness, and geometric connectedness then show that it is an abelian
scheme. If the moduli problem instead records only a homomorphism
$\lambda:A_T\to A_T^\vee$, that homomorphism alone does not prove scheme effectivity in this
book. One must additionally supply the compatible inducing ample bundle, compatible very
ample embedding data, or another proved criterion. In particular, this argument does not infer
a descendable inducing line bundle merely from the homomorphism.

The relation

$$
\lambda\circ\iota(a)=\iota(a^*)^\vee\circ\lambda
$$

descends because both sides are morphisms. Being an isogeny is detected by finiteness and
surjectivity of $\lambda$ and, in the finite-flat presentation used here, by flatness as well; the
degree or rank of its kernel descends. Positivity, and here scheme representability itself, is
encoded by the compatible ample rigidified bundle, not by an order relation on geometric points.

The determinant condition compares the characteristic polynomial of the $\mathcal O$-action on the Lie bundle with a prescribed polynomial. The Lie bundle is finite locally free and commutes with base change for a smooth group scheme. Characteristic-polynomial coefficients are polynomial expressions in the action matrix and hence descend. Equality with the prescribed coefficients can be checked after faithful base change. Alternating pairings, isotropic subgroup conditions, and similitude factors are likewise equations or perfectness conditions on finite locally free sheaves.

### 16.3 Representability after descent

Descent does not by itself prove that a moduli functor is represented. It supplies the sheaf
condition. The fpqc theorem of Section 11.1 glues a scheme descent datum to an equalizer sheaf,
and proves that sheaf algebraic for a surjective étale cover. For a general fpqc cover, to obtain
a representing scheme one must retain affine, quasi-affine, or compatible projective embedding
data. Under the noetherian, projective, finite-presentation, and fixed-polynomial
hypotheses of the parameter theorems in Book 8, a typical argument proceeds as follows. After an
fppf cover, trivialize the relevant vector bundles and choose a projective embedding supplied by
an ample canonical line bundle. The choices place the objects in the corresponding Hilbert scheme
or locally closed parameter space. Equations expressing group laws, endomorphism actions,
polarizations, and determinant conditions cut out closed loci; nondegeneracy and smoothness cut
out open loci.

On overlaps, changing the trivialization produces canonical isomorphisms between the parameter
spaces and universal objects. The triple identity follows from composition of changes of basis.
The compatible locally closed embeddings and ample universal bundles put these data in the safe
scheme-effectivity cases of Chapters 11 and 15, so their descents are schemes rather than merely
algebraic spaces. Full faithfulness guarantees that the glued object represents the original
functor rather than only its objects after a cover.

Automorphisms remain. If an object has nontrivial automorphisms, descent naturally produces a groupoid-valued moduli problem rather than a set-valued one. The present book proves the object and morphism descent needed for that groupoid. The systematic language of stacks, inertia, rigidification, and coarse spaces belongs to Book 35a.

### 16.4 A practical descent protocol

For later constructions the following order prevents circular arguments.

1. Specify a set-indexed fpqc or fppf cover and verify the affine-local finite-reduction condition.
2. List every object upstairs and every isomorphism on pairwise overlaps.
3. Check the triple cocycle, including compatibility with all structure maps.
4. Descend quasi-coherent modules and finite locally free tensors first.
5. Descend algebras, affine pieces, and closed or open loci cut out by those tensors.
6. Form the fpqc equalizer sheaf of Section 11.1; use its quotient theorem when the cover is
   surjective étale.
7. For a general fpqc cover, prove representability by identifying invariant affine charts,
   quasi-affineness, compatible
   ample or very ample data.
8. Only after obtaining a scheme, descend finiteness, flatness, smoothness, properness, and related
   properties separately.
9. Verify the claimed universal property by full faithfulness, not only by local existence.

For an infinite family, perform steps 4–8 over each affine part of the base using a finite affine refinement, then glue by uniqueness. This protocol keeps size, quasi-compactness, effectivity, and property descent visibly distinct.

## 17. Synthesis

### 17.1 The three levels of descent

Faithfully flat descent has three interacting levels. At the algebraic level, tensoring with a
faithfully flat algebra preserves and reflects exactness. The Amitsur equalizer then reconstructs
modules, their morphisms, and algebraic structures. At the unrestricted fpqc-sheaf level,
Section 11.1 forms the equalizer of an arbitrary scheme datum and proves effective pullback and
full faithfulness. At the algebraic-space level it constructs a representable diagonal and étale
atlas for a surjective étale cover. At the fpqc scheme-theoretic level, affine charts, intrinsic
quasi-affine envelopes, or compatible positive line bundles construct a representing scheme
directly. There is no automatic equivariant-atlas or stable-affine-neighborhood step between
these levels. Constructible-étale effectivity descends an atlas that already has descent data; it
does not manufacture the missing equivariant atlas.

The logic can be summarized by the diagram

$$
\begin{array}{ccccc}
M&\longrightarrow&B\otimes_AM&\rightrightarrows&B^{[1]}\otimes_AM\\
\downarrow&&\downarrow&&\downarrow\\
X&\longleftarrow&X_T&\substack{\longleftarrow\\[-.35em]\longleftarrow}&X_{T^{[1]}}.
\end{array}
$$

The upper row is an equalizer; reversing affine arrows turns it into affine geometric gluing.
Triple tensor products enforce transitivity. Faithfulness gives uniqueness, flatness preserves
relations, and quasi-compactness makes finite data descend. For a nonaffine $X_T$, this diagram
still controls functions and morphisms, but it does not by itself prove that the quotient is a
scheme.

### 17.2 Reusable theorem package

The results established in this book may be used in the following precise form.

- Set-indexed fpqc families admit affine-local finite affine refinements; infinite coproducts and infinite products are unnecessary.
- Modules, algebras, quasi-coherent sheaves, affine schemes, and their morphisms have effective
  fpqc descent, with pairwise isomorphisms satisfying the triple cocycle.
- Arbitrary scheme descent data along any fpqc cover define an fpqc equalizer sheaf with effective
  pullback and full faithfulness. Along a surjective étale cover this sheaf is an algebraic space.
  No unrestricted arbitrary-fpqc algebraicity theorem is asserted here.
- Finite generation, finite presentation, flatness, finite projectivity, finite local freeness, and rank descend faithfully flatly.
- Affine, finite, finite locally free, quasi-compact, quasi-separated, separated, finite-type, finite-presentation, flat, proper, smooth, étale, and unramified morphisms are fpqc local on the base with the qualifications stated in Chapter 10.
- Line bundles, vector bundles, tensors, pairings, sections, and effective Cartier divisors descend
  on a descended scheme, and finite locally free group schemes and their affine torsors satisfy
  effective scheme descent.
- General group objects, torsors, contracted products, and twists descend as fpqc sheaves along
  arbitrary fpqc covers and as algebraic spaces along surjective étale covers.
  They are schemes under the affine, finite, quasi-affine, or compatible-polarization criteria
  proved here, not merely from properness or projectivity.
- Quasi-compact quasi-separated quasi-affine schemes satisfy effective scheme descent through the
  intrinsic affine envelope.
- Quasi-projective and projective objects descend as schemes with compatible ample data in the
  local-on-the-base form, and globally when one finite embedding system is available; compatible
  positive divisors and rigidified ample line bundles cover the stated generalized elliptic and
  PEL cases. Properness or local projectivity without such data is not an effectivity criterion.

Every object-category assertion above includes both effectivity and full faithfulness in its stated
target category. Properties are not confused with objects: after constructing the descended
object and, when required, proving it is a scheme, the relevant local-on-the-base theorem must
still be applied.

### 17.3 Conclusion

Descent replaces the vague instruction “glue the local pieces” by a rigid and verifiable mechanism. Double overlaps say how to compare, triple overlaps say that comparison is transitive, faithful flatness says that local equality is genuine equality, and flatness says that the algebraic relations survive transport. Quasi-compactness ensures that finite geometry remains finite.

For every fpqc cover this mechanism recovers a global equalizer sheaf with the prescribed
pullback. For a surjective étale cover Section 11.1 constructs its algebraic-space atlas and
representable diagonal. For a general fpqc cover, algebraicity is not a formal consequence of the
cocycle. Recovering a scheme is still stronger. In the generalized elliptic and PEL applications,
the compatible positive divisor or rigidified ample bundle supplies that step. Those families can
therefore be built where their coordinates and bundles are simplest and returned to the original
base as schemes without loss of structure. In an application lacking such a criterion, the
honest arbitrary-fpqc conclusion proved here is the equalizer sheaf carrying all descended maps
and equations; it may be called an algebraic space only when a separate algebraicity theorem
applies.
