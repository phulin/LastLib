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
11. [Effective descent for schemes](#11-effective-descent-for-schemes)
    - [The theorem and its hypotheses](#111-the-theorem-and-its-hypotheses)
    - [Descending affine opens](#112-descending-affine-opens)
    - [Gluing the quotient](#113-gluing-the-quotient)
    - [Separatedness and quasi-compactness issues](#114-separatedness-and-quasi-compactness-issues)
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
    - [Removing a chosen polarization](#153-removing-a-chosen-polarization)
    - [Limits of the statement](#154-limits-of-the-statement)
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

Geometry is often constructed after a change of base. A bundle is trivialized, a family acquires a convenient projective embedding, or a group action becomes a familiar constant action. The real problem begins when one tries to return to the original base. Two copies of the local object live over the double overlap; an identification between them is necessary, and on the triple overlap the three possible identifications must agree. Descent is the theorem that these compatibility conditions are not merely necessary but, under suitable coverings, sufficient.

The prototype is ordinary gluing over open subsets. Faithfully flat descent is subtler because the members of the cover need not be open immersions. A field extension $\operatorname{Spec}L\to\operatorname{Spec}K$ is a cover, although its source has no smaller pieces corresponding to open subsets of the one-point target. What substitutes for literal intersection is the fiber product

$$
\operatorname{Spec}L\times_{\operatorname{Spec}K}\operatorname{Spec}L
=\operatorname{Spec}(L\otimes_KL).
$$

The tensor product remembers the two ways a scalar can be viewed after base change. Equality between those two views is the algebraic form of being defined over $K$.

This book develops that observation from modules to schemes and then to the geometric objects needed in moduli problems. The guiding sequence is

$$
\text{faithful exactness}
\Longrightarrow \text{effective module descent}
\Longrightarrow \text{affine descent}
\Longrightarrow \text{scheme descent}.
$$

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

For the first equivalence, $(A/I)\otimes_AB\simeq B/IB$. Thus faithfulness forces $IB\ne B$. Conversely, if a nonzero module $M$ is chosen and $m\ne0$, the cyclic submodule $Am\simeq A/I$ has proper annihilator $I$. Flatness injects $B\otimes_AAm$ into $B\otimes_AM$, while $B/IB$ is nonzero. For the spectral formulation, a proper ideal of $B$ lies in a prime, and contraction shows that every prime of $A$ is reached. The converse follows because a proper $I$ contained in a prime $\mathfrak p$ cannot extend to the unit ideal if a prime of $B$ lies over $\mathfrak p$.

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

A refinement does not change descent. Data on the coarse cover pull back to the refinement. Conversely, compatible data on a refinement first descend to each coarse member and then descend to $S$; uniqueness at both stages makes the resulting comparison canonical. We shall use this transitivity silently only after identifying the two effectiveness steps involved.

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

The proof illustrates the standard descent technique: make a faithfully flat base change until a splitting appears. Tensor the sequence with $B$. In the resulting augmented complex, insert $1$ as the first tensor factor. This gives a contracting homotopy: multiplication removes the inserted factor at one end, and the alternating terms cancel in pairs. The base-changed complex is exact. Faithful flatness reflects exactness, proving the assertion downstairs.

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
T,qquad T^{[1]}=T\times_ST,qquad
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

On each affine $U\subset S$, select a finite affine refinement as in Section 2.2 and descend there. Different selections have a common refinement. Full faithfulness supplies unique comparison isomorphisms, and the cocycle for those comparisons is automatic by uniqueness. The locally descended objects therefore glue. This argument will be invoked whenever the single-cover theorem has first been proved.

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

The proof strategy is to test $\varepsilon$ after tensoring once more with $B$. Faithful flatness will then reflect that it is an isomorphism. After base change, the cover $B\to B\otimes_AB$ has a section given by multiplication $B\otimes_AB\to B$. Descent along a split cover is elementary: transport an element along the datum and then pull it back through the section.

Here are the decisive details. Regard $B\otimes_AN$ as obtained from $N$ by the first copy of $B$. The datum supplies a map which, in symbolic Sweedler notation, writes

$$
\theta(n\otimes1)=\sum n_{(0)}\otimes n_{(1)}.
$$

Apply the datum once more over $B^{[2]}$. The cocycle says that transporting first from position $1$ to $2$ and then from $2$ to $3$ equals direct transport from $1$ to $3$. Pulling back along multiplication of the first two positions shows that the transported element satisfies the equalizer condition defining $M$. This construction gives an inverse to

$$
B\otimes_A\varepsilon:
B\otimes_AB\otimes_AM\longrightarrow B\otimes_AN.
$$

The two inverse identities reduce respectively to the normalization of $\theta$ on the diagonal and to the cocycle. Therefore $B\otimes_A\varepsilon$ is an isomorphism. Its kernel and cokernel become zero after tensoring with $B$, so $\varepsilon$ is an isomorphism.

Finally, the definition of $M$ says exactly that $\varepsilon$ intertwines the canonical datum with $\theta$. This proves essential surjectivity. Notice how each hypothesis enters: flatness lets kernels and cokernels commute with the test, faithfulness brings the conclusion back, and the cocycle constructs the inverse after the split base change.

An alternative proof organizes the same calculation through the exact Amitsur complex

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

A module is finite projective if and only if it is finitely presented and flat. One direction follows because a direct summand of a finite free module is finitely presented and flat. For the other, choose a finite presentation

$$
A^m\to A^n\to M\to0.
$$

Flatness makes the kernel locally a direct summand; equivalently, localization at each prime gives a finite free module. Around each prime a suitable minor becomes invertible and supplies a splitting. These neighborhoods cover the spectrum, and the local splittings show that $M$ is finite locally free, hence projective.

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

When $S=\operatorname{Spec}A$ and $T=\operatorname{Spec}B$, an affine $T$-scheme is $\operatorname{Spec}C$. Its scheme datum is opposite to an algebra datum on $C$, so the result is immediate. If $T$ is not affine, cover $S$ by affines, refine the inverse image by finitely many affines, apply ring descent, and glue the resulting affine schemes. Independence of refinement follows from full faithfulness.

Affineness itself descends under fpqc base change: if $X_T\to T$ is affine, then the canonical descent datum on $X_T$ lies in the affine subcategory, so its effective affine descent is an affine $S$-scheme. Full faithfulness identifies it with $X$. This concise proof depends on having already established effectivity, not merely on affineness being visible on fibers.

### 7.4 Finite and finite locally free affine schemes

An affine morphism $X=\operatorname{Spec}_S\mathcal A\to S$ is finite when $\mathcal A$ is a finite module, finite presentation when it is a finitely presented algebra, and finite locally free of rank $r$ when $\mathcal A$ is finite locally free of rank $r$ as a module. Chapters 5 and 6 therefore give effective descent for each class.

In particular, if $X_T\to T$ is finite and the datum is effective as an affine scheme, then $X\to S$ is finite. If it is finite and flat, it is finite locally free. The key local algebra is that a finitely generated flat module over a local ring is free: choose a minimal generating set from a basis modulo the maximal ideal; the equational criterion for flatness forces every relation among those generators to have all coefficients zero. Localizing and clearing the finitely many coefficients in the chosen generators gives freeness on a neighborhood. The rank then descends. Stating “finite locally free” remains useful because it records this conclusion and its locally constant rank at once.

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

**Vector-bundle descent.** Vector bundles, line bundles, and their morphisms satisfy effective fpqc descent.

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

Likewise, an ample line bundle on $X_T$ need not itself descend unless it carries a cocycle. Its isomorphism class might be moved by the overlap correspondence, or choices of pairwise isomorphisms might fail the triple condition by units. Chapter 15 will separate polarized descent, where the line bundle is part of the datum, from arguments that manufacture a descendable power or norm under stronger hypotheses.

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

First assume $X$ and $Y$ affine over an affine $S$. The assertion is the full-faithfulness part of algebra descent with arrows reversed. If only $Y$ is affine over $S$, a map $X\to Y$ is an $\mathcal O_S$-algebra map from the coordinate algebra of $Y$ to the direct image of $\mathcal O_X$; it can be checked on affine opens of $X$, where module equalizers apply. For general $Y$, cover it by affine opens. The inverse images upstairs descend as open subsets once one observes that the condition of a point landing in an open is compatible and fpqc local. The local maps descend and glue. Uniqueness follows because equal maps after a surjective base change agree on underlying points and on functions over affine neighborhoods.

As a consequence, sections descend. A section of $X_T\to T$ is a map $T\to X$ after base change, and the overlap equality is exactly its descent condition. Automorphisms form a sheaf: compatible automorphisms descend, and the inverse descends with them.

### 10.2 The diagonal method

Many properties of a morphism $f:X\to S$ are encoded by its diagonal

$$
\Delta_f:X\longrightarrow X\times_SX.
$$

The morphism is separated when $\Delta_f$ is a closed immersion, unramified when the diagonal is an open immersion together with a finite-presentation condition, and a monomorphism when the diagonal is an isomorphism. Since diagonals commute with base change, descent of closed immersions, open immersions, and isomorphisms yields descent of these properties.

Open immersions require a short argument. If $U_T\to X_T$ is an open immersion with compatible datum and its source descends to $U\to X$, then it is a monomorphism locally of finite presentation and flat. These three properties descend; such a morphism is an open immersion. Alternatively, its image is a subset whose inverse image is open. Flat morphisms locally of finite presentation are open, so the descended image is open, and the map identifies $U$ with it after a cover, hence already downstairs.

The diagonal method also reduces quasi-separatedness to quasi-compactness of a diagonal. It is safer than trying to reason directly with intersections of arbitrary affine opens after base change.

### 10.3 A table of descending properties

For a morphism $f:X\to S$, the following properties are fpqc local on the base, with the qualifications displayed.

| Property of $f$ | Required qualification | Main reason |
|---|---|---|
| affine | none | effective descent of affine schemes |
| quasi-compact | cover is fpqc as a family | finite affine reduction |
| quasi-separated | none beyond fpqc | diagonal and quasi-compactness |
| separated | none beyond fpqc | diagonal is a closed immersion |
| locally of finite type | none beyond fpqc | finite algebra generators descend locally |
| finite type | quasi-compactness included | local finite type plus quasi-compactness |
| locally of finite presentation | none beyond fpqc | finite generators and relations descend |
| finite presentation | quasi-compactness included | local finite presentation plus quasi-compactness |
| flat | none beyond fpqc | faithful exactness |
| finite locally free of rank $r$ | none beyond fpqc | affine descent and module descent |
| finite | none beyond fpqc | affine plus finite module |
| monomorphism | none beyond fpqc | diagonal is an isomorphism |
| open, closed, or locally closed immersion | none beyond fpqc | affine equations and open-image descent |
| proper | finite type and separated are part of the definition | universal closedness descends |
| smooth, étale, unramified | locally of finite presentation | infinitesimal or differential criterion |

Quasi-affine and quasi-projective morphisms are postponed because their proofs use global functions or ample bundles. Projective morphisms are treated there as well. Noetherianity is not needed for the entries above unless it is built into a chosen alternative definition.

### 10.4 Proofs of the principal cases

For quasi-compactness, cover $S$ by affine opens $U$. Choose finitely many quasi-compact pieces of the fpqc family covering $U$. If $X_T\to T$ is quasi-compact, the inverse images of those finitely many pieces have finite affine covers. Their images cover $X_U$ because the base change is surjective. Descending the finitely many relevant opens, or applying the topological fact that a surjective quasi-compact map detects quasi-compactness, gives a finite cover of $X_U$. The family finiteness condition is essential here.

Local finite type and local finite presentation reduce to affine charts after using descent of quasi-compact open neighborhoods. On rings, they are exactly finite generation and finite presentation of algebras, proved in Section 6.1. Finite type and finite presentation add quasi-compactness.

For properness, finite type and separatedness have already descended. It remains to descend universal closedness. After any $S'\to S$, the induced $T\times_SS'\to S'$ is fpqc. A closed subset $Z\subset X_{S'}$ has closed inverse image in $X_{T\times_SS'}$, whose image in $T\times_SS'$ is closed because the upstairs morphism is proper. This closed subset is saturated for the cover. A subset of $S'$ is closed if its inverse image under an fpqc morphism is closed: reduce to affine faithfully flat maps, where specialization lifts by going-down for flat maps and surjectivity supplies a point over the initial prime. Thus the image of $Z$ is closed.

For smoothness and étaleness, first descend local finite presentation and flatness. Smoothness may be characterized, for a finitely presented flat morphism, by geometrically regular fibers. A point of $S$ lifts after the cover, and geometric regularity of the fiber can be checked after a faithfully flat field extension. Étaleness is smoothness of relative dimension zero, or equivalently flatness plus unramifiedness. Unramifiedness descends through the diagonal criterion. This proves the table without assuming the base is noetherian or a field.

Some properties are only local on the source, others only on the target, and some on both. The phrase “fpqc local on the base” means exactly

$$
f\text{ has }P
\quad\Longleftrightarrow\quad
f_T\text{ has }P
$$

for every fpqc cover $T\to S$, with ascent supplied by base-change stability and descent by the arguments above.

## 11. Effective descent for schemes

### 11.1 The theorem and its hypotheses

**Scheme descent theorem.** Let $p:T\to S$ be an fpqc morphism. Every $T$-scheme $X_T$ equipped with a descent datum relative to $T/S$ descends to an $S$-scheme $X$, uniquely up to unique isomorphism. Morphisms descend uniquely. The same statement holds for set-indexed fpqc covering families satisfying the affine-local finite-reduction condition of Section 2.1.

No separatedness, quasi-compactness, finite type, or noetherian hypothesis is imposed on $X_T$. Quasi-compactness belongs to the cover, not to the object. The proof cannot simply assert that affine opens of $X_T$ descend: a random affine open need not be preserved by the equivalence relation. The key step is to construct enough affine opens that are compatible.

### 11.2 Descending affine opens

The assertion is local on $S$. Over an affine open of $S$, choose finitely many affine opens in $T$ whose images cover it and replace them by their disjoint union. Restricting the datum gives an affine faithfully flat cover. If a scheme is constructed from that refinement, its pullback to the original $T$ is identified with $X_T$ after the fpqc cover formed by the pairwise fiber products; full faithfulness then supplies the identification on $T$. We may therefore assume for the central argument that both $S$ and $T$ are affine.

Fix $x\in X_T$. Choose an affine neighborhood $W$ of $x$. Over $T^{[1]}$, the datum compares the two pullbacks of $W$, but they need not coincide. Their intersection is open. Because the projections $T^{[1]}\to T$ are affine and quasi-compact, the relevant inverse images admit finite covers by quasi-compact pieces. Shrinking on these finitely many pieces makes the two transports lie in a common quasi-compact open.

Repeat over the triple overlap and intersect the finitely many resulting opens. The cocycle ensures stability under further transport. We obtain a quasi-compact open $V\subset X_T$ whose two inverse images correspond under the datum. Refining $V$ by finitely many principal affine opens and replacing their defining functions by finite products of all transported functions produces a datum-stable affine open around the chosen equivalence class. The algebra behind the last step is the principal-open identity $D(f)\cap D(g)=D(fg)$; affineness of the cover makes every transport describable by tensor-product localization, and quasi-compactness ensures that only finitely many functions occur.

Thus every point has a datum-stable affine neighborhood after an fpqc refinement of the base. This statement, often called the affine-neighborhood lemma for descent, is the geometric heart of the proof. Its finite choices explain exactly why an arbitrary surjective flat map without quasi-compact control is insufficient for this direct argument.

### 11.3 Gluing the quotient

Cover $X_T$ by datum-stable affine opens $V_\alpha$. By affine descent each $V_\alpha$ descends to an affine $S$-scheme $U_\alpha$. The intersections $V_\alpha\cap V_\beta$ are open subschemes carrying compatible data. Cover each intersection by stable affine opens and descend them. Descent of open immersions identifies the resulting schemes with open subschemes of both $U_\alpha$ and $U_\beta$.

The overlap isomorphisms satisfy the ordinary gluing cocycle because their pullbacks do and morphisms descend fully faithfully. Zariski gluing produces an $S$-scheme $X$. Its pullback to $T$ is assembled from the $V_\alpha$ with their original overlaps, hence is canonically $X_T$. The comparison respects the original datum by construction.

If two descents $X$ and $X'$ exist, the upstairs isomorphism between their pullbacks is compatible. Descent of morphisms gives $X\to X'$ and its inverse; the two composites are identities after pullback and hence downstairs. This is uniqueness up to unique isomorphism, the strongest useful form of uniqueness.

For an fpqc family, descend over each affine $U\subset S$ using a finite affine refinement. On overlaps of affine opens the two results have canonically isomorphic pullbacks and hence are uniquely isomorphic. These isomorphisms satisfy a cocycle and glue. At no point is an infinite product of rings or a quasi-compact infinite coproduct required.

### 11.4 Separatedness and quasi-compactness issues

Scheme descent is effective even when $X_T$ is not separated. What fails without separatedness are certain convenient shortcuts. For example, intersections of affine opens in a non-quasi-separated scheme need not be quasi-compact, so one cannot assume a finite affine overlap cover. The stable-affine construction works locally with quasi-compact pieces and allows an arbitrary set of them in the final gluing.

If one wants the descended $X\to S$ to be quasi-compact or quasi-separated, these properties must be verified upstairs and then descended by Chapter 10. They do not appear automatically from the existence theorem. Similarly, a descent datum on an algebraic space need not have a scheme as its quotient unless the scheme affine-neighborhood condition can be proved; for fpqc equivalence relations arising from a scheme already over a base, the theorem above supplies it, but arbitrary equivalence relations are a different quotient problem.

An instructive nonexample comes from dropping the cocycle. Glue three copies over pairwise overlaps by automorphisms whose product around the triple overlap is nontrivial. Pairwise quotients may look locally valid, yet transitivity fails and no sheaf, much less a scheme, can represent the proposed quotient. The triple condition is the mathematical content that turns identifications into an equivalence relation.

## 12. Finite-flat group objects and actions

### 12.1 Group laws descend

An $S$-group scheme is an $S$-scheme $G$ with multiplication, identity, and inverse maps

$$
m:G\times_SG\to G,
\qquad e:S\to G,
\qquad i:G\to G,
$$

satisfying the group diagrams. Suppose $G_T$ carries descent data and these three maps are compatible. Scheme effectivity descends $G_T$ to $G$, while descent of morphisms descends $m,e,i$. Associativity, the unit identities, and the inverse identities are equalities of maps. They can be checked after the surjective base change, so they hold on $G$. Thus group schemes satisfy effective fpqc descent.

Commutativity is likewise an equality $m=m\circ\tau$ and descends. If $G_T\to T$ is finite, flat, finitely presented, or finite locally free of rank $n$, the corresponding property of $G\to S$ descends. Hence finite-flat and finite locally free group objects form effective descent categories.

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

A homomorphism $G_T\to H_T$ compatible with descent data descends uniquely because the underlying map descends and compatibility with multiplication and identity is detected upstairs. A compatible closed subgroup $K_T\hookrightarrow G_T$ descends as a closed subscheme; the group structure restricts and descends. If it is finite locally free, so is $K$.

For a sequence of finite locally free commutative group schemes

$$
0\longrightarrow G'\longrightarrow G\longrightarrow G''\longrightarrow0,
$$

the meaning of exactness is sheaf-theoretic for the fppf topology: the first map identifies $G'$ with the kernel and the second is an fppf epimorphism with that kernel. Kernels are fiber products and commute with base change. Being a closed immersion and being faithfully flat locally of finite presentation descend. Thus exactness can be checked fpqc-locally, provided the asserted quotient map has the stated finiteness and flatness.

### 12.4 Actions and quotients in the finite case

An action $a:G\times_SX\to X$ is another morphism satisfying identity and associativity diagrams, so compatible actions descend. Fixed-point subschemes defined as equalizers descend whenever the relevant equalizer is representable; for a separated $X$, the fixed locus of a finite group action is closed because it is pulled back from a diagonal.

Let a finite locally free group scheme $G$ act on an affine $X=\operatorname{Spec}R$. The affine quotient is

$$
\operatorname{Spec}(R^G),
\qquad
R^G=\{r:a^*(r)=1\otimes r\}.
$$

This is an equalizer and commutes with flat base change when the finite projectivity needed to control the coaction is present. If the action is free in the torsor sense, $X\to\operatorname{Spec}(R^G)$ is finite locally free and the expected orbit relation is effective. For nonaffine $X$, existence of a scheme quotient needs invariant affine neighborhoods or a separate representability theorem; descent alone must not be cited as producing all group quotients.

## 13. Torsors

### 13.1 The torsor identity

Let $G$ be an $S$-group scheme acting on the right on an $S$-scheme $P$. The action is **simply transitive over the base** when

$$
G\times_SP\longrightarrow P\times_SP,
\qquad(g,p)\longmapsto(p,pg)
$$

is an isomorphism. A **$G$-torsor for the fpqc topology** is an $S$-scheme $P$ with this identity such that $P\to S$ is an fpqc cover. For an fppf torsor one asks $P\to S$ to be fppf.

The isomorphism says that any two points in the same fiber differ by a unique group element. The covering condition says that points exist locally. Both clauses are necessary: the empty scheme satisfies the displayed isomorphism vacuously but is not a torsor.

If $G\to S$ is finite locally free of positive rank and $P$ is a torsor, then after the cover $P\to S$ the scheme $P$ becomes isomorphic to $G$: choose the tautological point on $P_P$ and translate. Finite local freeness descends, so $P\to S$ is finite locally free of the same rank. Thus fpqc and fppf torsors coincide for finite locally free $G$.

### 13.2 Local triviality and effectivity

Conversely, suppose $P_T\simeq G_T$ over a cover $T\to S$, with transition maps that are $G$-equivariant and satisfy the cocycle. Scheme descent gives $P$, action descent gives the action, and the torsor identity descends because being an isomorphism is fpqc local. The cover $P\to S$ is fpqc or fppf when this property is verified after $T\to S$. Hence torsors are exactly locally trivial $G$-spaces equipped with coherent transition data.

Choose trivializations $P_{T_i}\simeq G_{T_i}$. A $G$-equivariant automorphism of the right regular $G$-space is left translation by a unique element $g_{ij}\in G(T_i\times_ST_j)$. The cocycle becomes

$$
g_{ik}=g_{ij}g_{jk}
$$

with the order depending on the left/right convention. Changing trivializations by $h_i\in G(T_i)$ changes $g_{ij}$ by

$$
g'_{ij}=h_i g_{ij}h_j^{-1}.
$$

This is the noncommutative cocycle description of torsors. It is a pointed classification: the trivial torsor corresponds to the identity cocycle.

### 13.3 Contracted products and twisting

If $P$ is a right $G$-torsor and $G$ acts on the left on $X$, the contracted product is locally the quotient of $P\times_SX$ by

$$
(p,x)g=(pg,g^{-1}x).
$$

It can be constructed without first proving a general quotient theorem. Trivialize $P$ fpqc-locally. On each trivializing member the desired object is $X$, and on overlaps the torsor cocycle acts on $X$. The action law supplies the triple cocycle, so scheme descent produces

$$
P\times^GX.
$$

After pullback to $P$, it is isomorphic to $X_P$. Therefore every property of $X\to S$ that is fpqc local on the base passes to the twist. If $X$ is affine, finite, smooth, proper, or finite locally free, so is its twist under the corresponding hypotheses.

For a representation of $G$ on a finite locally free sheaf $V$, the same construction yields an associated vector bundle $P\times^GV$. Tensor operations and invariant pairings descend. This mechanism produces the bundles and tensors attached to level structures and PEL data.

### 13.4 Examples and boundary cases

For $G=\mathbf G_m$, torsors and line bundles encode one another. From a line bundle $\mathcal L$, remove the zero section from its total space, or equivalently take the sheaf of trivializations of $\mathcal L$; scalar multiplication gives a $\mathbf G_m$-torsor. From a torsor $P$, contract with the standard one-dimensional representation. These constructions are inverse by local triviality and descent.

For $G=\operatorname{GL}_r$, the frame bundle of a rank-$r$ vector bundle is a torsor, and the associated bundle for the standard representation recovers the vector bundle. For $\mu_n$, the equation $z^n=a$ gives a torsor where $a$ is a unit; when $n$ is not invertible on the base it is generally fppf rather than étale. This is one reason finite-flat descent, not only étale descent, is indispensable in integral moduli problems.

A transitive action on geometric points is not enough to be a torsor. Infinitesimal stabilizers may remain invisible on geometric points. The scheme isomorphism $G\times P\simeq P\times P$ detects them. Likewise a quotient on topological spaces does not supply the structure sheaf or its effectivity; torsor descent is a scheme-theoretic statement.

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

Let $T\to S$ be fpqc and suppose $X\to S$ is quasi-compact and quasi-separated. Flat base change gives

$$
(f_*\mathcal O_X)|_T\simeq (f_T)_*\mathcal O_{X_T}.
$$

The proof uses the finite affine equalizer just described: tensoring with a flat algebra preserves that equalizer. Hence the affine envelope of $X_T$ is the pullback of the affine envelope of $X$ and $j_{X_T}$ is the base change of $j_X$.

If $X_T\to T$ is quasi-affine, then $j_{X_T}$ is an open immersion. Open immersions descend fpqc-locally, so $j_X$ is an open immersion and $X\to S$ is quasi-affine. We have therefore proved:

**Quasi-affine descent theorem.** Quasi-affineness is fpqc local on the base among quasi-compact, quasi-separated morphisms.

The hypotheses are not ornamental. Without quasi-compactness, the canonical map into the spectrum of global functions need not exhibit a quasi-affine scheme as a quasi-compact open, and the finite equalizer proof of flat base change breaks down. One can formulate a locally quasi-affine variant by working on quasi-compact opens, but later moduli applications are finitely presented and hence fall within the stated theorem.

### 14.3 Finite presentation and openness

Suppose $X_T$ is not merely quasi-affine but of finite presentation over $T$. Finite presentation descends, so $X$ is of finite presentation over $S$. The open immersion $j_X$ is then quasi-compact and locally of finite presentation. Over an affine open of the envelope, its image is a quasi-compact open and hence a finite union of principal opens. Thus the descended quasi-affine presentation uses finitely much algebraic data.

This finiteness is useful in parameter problems. Conditions imposed by nonvanishing of finitely many determinants define quasi-affine loci. They may be checked after an fpqc trivialization of the relevant bundles, but the determinant sections and their common nonvanishing locus descend. The affine-envelope theorem ensures that the result remains a scheme of finite presentation rather than an uncontrolled union.

### 14.4 The precise reusable criterion

The criterion used later can be stated without mentioning a chosen embedding. Let $f:X\to S$ be quasi-compact and quasi-separated. Then the following are equivalent:

1. $f$ is quasi-affine;
2. $j_X:X\to\operatorname{Spec}_S(f_*\mathcal O_X)$ is a quasi-compact open immersion;
3. every point of $X$ has a neighborhood of the form $X_s\cap D(g)$, for finitely many relative functions whose principal loci are affine over $S$ locally.

The implication $1\Rightarrow2$ was proved by principal opens; $2\Rightarrow1$ is immediate. For $2\Rightarrow3$, pull back standard principal opens of the affine envelope. Conversely, the local principal-open condition makes $j_X$ an isomorphism on an open cover, and monomorphism follows because global functions separate the same affine charts. The criterion is stable under flat base change and therefore ideal for descent.

## 15. Quasi-projective and projective descent

### 15.1 Polarized descent

Projective geometry requires positivity, and positivity is carried by a line bundle. Let $f:X\to S$ be quasi-compact and of finite presentation, let $T\to S$ be fpqc, and let $\mathcal L_T$ be an invertible sheaf on $X_T$ with descent datum compatible with that of $X_T$. Chapter 9 descends it to a line bundle $\mathcal L$ on $X$.

Book 8 established that relative ampleness is preserved and reflected by faithfully flat quasi-compact base change under these hypotheses. The mechanism is worth recalling. Ampleness may be tested affine-locally on $S$ by requiring finitely many positive tensor powers and sections whose nonvanishing loci are affine and cover $X$. Upstairs, quasi-compactness selects finitely many such sections. Their finite algebraic coefficients and the affine loci can be descended after passing to tensor combinations compatible with the cocycle. Conversely, pullback of an affine nonvanishing cover remains affine and covering. Thus

$$
\mathcal L\text{ is }f\text{-ample}
\quad\Longleftrightarrow\quad
\mathcal L_T\text{ is }f_T\text{-ample}.
$$

It follows that a **polarized quasi-projective object** $(X,\mathcal L)$ satisfies effective fpqc descent when $f$ is of finite presentation and $\mathcal L$ is relatively ample. The word polarized means that the overlap datum includes the line bundle and its cocycle, not merely that some ample line bundle exists after the cover.

### 15.2 Very ampleness and closed immersions

Suppose $\mathcal L_T$ is relatively very ample with a compatible finite locally free space of generating sections $\mathcal E_T\twoheadrightarrow(f_T)_*\mathcal L_T$ in the form needed for an embedding

$$
X_T\hookrightarrow\mathbf P_T(\mathcal E_T).
$$

Descend $\mathcal E_T$, the quotient map, and the induced morphism to projective space. Closed immersion is fpqc local, so the descended map is a closed immersion. Hence very ampleness with its finite system of sections descends.

For an ample line bundle, a sufficiently high power becomes very ample when $f$ is quasi-projective of finite presentation and the relevant finite generation theorem applies. Book 8 supplies this relative embedding result. Once one power and a finite set of sections have been chosen compatibly, the preceding paragraph descends the embedding. In particular, projectivity descends for a projective object equipped with compatible ample polarization data; properness of the descended morphism also follows independently from Chapter 10.

The distinction between a closed and an open immersion is stable under descent. Thus if $X_T$ is exhibited as a locally closed subscheme of a projective bundle by compatible data, the locally closed immersion and its image descend, giving a quasi-projective $X$.

### 15.3 Removing a chosen polarization

There are two situations needed later in which a line bundle can be manufactured rather than supplied.

First, let $T\to S$ be finite locally free of constant positive rank and suppose $X\to S$ is of finite presentation. The projection $q:X_T\to X$ is finite locally free. For a line bundle $\mathcal M$ on $X_T$, its norm is

$$
N_q(\mathcal M)
=\det(q_*\mathcal M)\otimes\det(q_*\mathcal O_{X_T})^{-1}.
$$

It is a line bundle and is multiplicative in $\mathcal M$. This is checked after a cover on which $q_*\mathcal O_{X_T}$ and $q_*\mathcal M$ are free, where the norm is the determinant of multiplication and transition determinants multiply. If $\mathcal M$ is relatively ample over $T$, then $N_q(\mathcal M)$ is relatively ample over $S$. Here is a proof that does not assume a ramified finite cover becomes a disjoint union. Take a sufficiently high power of $\mathcal M$ and finitely many sections whose nonvanishing loci are affine and cover $X_T$. The determinant norm sends each section to a section of the corresponding norm line bundle. Cayley--Hamilton applied to multiplication on the finite locally free algebra shows that the nonvanishing locus of a norm section is the largest locus over which the original section is invertible on every point of the finite fiber. Finite products of suitably chosen norm sections give a covering by affine loci: their inverse images are finite intersections of affine principal loci, and affineness descends along the finite faithfully flat map. The affine-open criterion from Book 8 proves ampleness. Thus quasi-projectivity and projectivity descend along finite locally free surjective base change without a preselected polarization.

Second, in moduli problems the object carries a canonical positive divisor or polarization. A marked effective Cartier divisor $D_T$ that is compatible with descent gives $\mathcal O(D_T)$ with descent datum. If a fixed power is ample—for example, a sufficiently positive multiple of the identity divisor on a family of genus-one curves—polarized descent applies. For an abelian scheme with a specified polarization represented fpqc-locally by an ample line bundle, rigidification and symmetry remove the scalar ambiguity; a fixed tensor power then has a genuine cocycle and descends. The precise power is chosen as part of the moduli construction, so no general assertion about arbitrary polarization classes is required.

### 15.4 Limits of the statement

One must not argue: “$X_T$ has some ample line bundle, therefore that line bundle descends.” Its two pullbacks may not even be isomorphic, and chosen isomorphisms may fail the cocycle. The safe statements proved here are:

- quasi-projectivity descends with a compatible relatively ample line bundle;
- it descends without a chosen line bundle along a finite locally free surjective cover, by the norm construction;
- it descends in a moduli problem when a canonical divisor, rigidified polarization, or explicitly chosen tensor power supplies compatible positive data.

These are exactly the forms used below. No unrestricted claim that an arbitrary locally existing polarization descends is needed. Similarly, proper plus quasi-projective implies projective because a quasi-projective immersion into projective space is locally closed and proper, hence closed. Properness alone does not produce a projective embedding over an arbitrary base.

## 16. The descent package for moduli geometry

### 16.1 Generalized elliptic curves

A generalized elliptic curve over $S$ consists, in the range relevant here, of a proper flat finitely presented family $E\to S$ whose geometric fibers are smooth genus-one curves or prescribed Néron polygons, a section $e:S\to E$ in the smooth locus, and a commutative group action of the smooth locus extending the usual translation action with the required behavior on components. Each clause is fpqc local once expressed scheme-theoretically.

Given such an object over $T$ with descent datum, descend the scheme $E$, the section $e$, the smooth open, the multiplication/action maps, and all incidence morphisms. Properness, flatness, finite presentation, smoothness of the indicated locus, and the finite locally free component conditions descend by Chapter 10. The group and action identities descend as equalities of morphisms. The fiber condition can be tested after residue-field extension: nodal singularities, the number and cyclic incidence of geometrically irreducible components, and arithmetic genus are preserved and reflected after faithfully flat field extension when the family is finitely presented and flat.

For projectivity, use the marked divisor. In a genus-one family, a fixed sufficiently large multiple $n[e]$ has relatively ample associated line bundle; on an $m$-gon one includes the orbit of the identity section, or an invariant divisor meeting every component, so positive degree occurs on every component. The divisor and its line bundle carry descent data because the section and action do. Book 8 then descends ampleness and the resulting projective embedding. This avoids selecting an unrelated ample bundle upstairs.

Level structures are morphisms from finite locally free group schemes into the smooth group locus or its torsion. Their homomorphism identities descend. Conditions such as being a closed immersion, being finite locally free of a given rank, or giving a full set of sections are fpqc local. Exactness of subgroup sequences is interpreted in the fppf sense as in Section 12.3. Thus level structures at primes not invertible on the base are handled without pretending they are etale.

### 16.2 PEL objects

A PEL object comprises an abelian scheme $A\to S$, an action $\iota:\mathcal O\to\operatorname{End}_S(A)$ by a fixed finite algebra with involution, a polarization $\lambda:A\to A^\vee$, and a level structure, subject to determinant and compatibility conditions. Descent treats these pieces in a rigid order.

First descend the proper smooth group scheme and its identity. Geometric connectedness of fibers descends after field extension, so the result is an abelian scheme. The polarization is encoded here by its rigidified relatively ample line bundle; its associated homomorphism and the bidual comparison then commute with base change by their universal construction. Endomorphisms $\iota(a)$ descend by full faithfulness. Since $\mathcal O$ is finitely generated as an abelian group in the applications, finitely many multiplication and involution identities suffice, and all are equalities of maps.

The relation

$$
\lambda\circ\iota(a)=\iota(a^*)^\vee\circ\lambda
$$

descends because both sides are morphisms. Being an isogeny is detected by finiteness, flatness, and surjectivity of $\lambda$; the degree or rank of its kernel descends. Positivity is encoded by the ample rigidified bundle used to define the polarization, not by an order relation on geometric points.

The determinant condition compares the characteristic polynomial of the $\mathcal O$-action on the Lie bundle with a prescribed polynomial. The Lie bundle is finite locally free and commutes with base change for a smooth group scheme. Characteristic-polynomial coefficients are polynomial expressions in the action matrix and hence descend. Equality with the prescribed coefficients can be checked after faithful base change. Alternating pairings, isotropic subgroup conditions, and similitude factors are likewise equations or perfectness conditions on finite locally free sheaves.

### 16.3 Representability after descent

Descent does not by itself prove that a moduli functor is represented. It supplies the sheaf condition and lets locally constructed representing schemes glue. A typical argument proceeds as follows. After an fppf cover, trivialize the relevant vector bundles and choose a projective embedding supplied by an ample canonical line bundle. The choices place the objects in a Hilbert scheme or a locally closed parameter space of the kind constructed in Book 8. Equations expressing group laws, endomorphism actions, polarizations, and determinant conditions cut out closed loci; nondegeneracy and smoothness cut out open loci.

On overlaps, changing the trivialization produces canonical isomorphisms between the parameter spaces and universal objects. The triple identity follows from composition of changes of basis. Effective descent glues the universal families and morphisms. Full faithfulness guarantees that the glued object represents the original functor rather than only its objects after a cover.

Automorphisms remain. If an object has nontrivial automorphisms, descent naturally produces a groupoid-valued moduli problem rather than a set-valued one. The present book proves the object and morphism descent needed for that groupoid. The systematic language of stacks, inertia, rigidification, and coarse spaces belongs to Book 14.

### 16.4 A practical descent protocol

For later constructions the following order prevents circular arguments.

1. Specify a set-indexed fpqc or fppf cover and verify the affine-local finite-reduction condition.
2. List every object upstairs and every isomorphism on pairwise overlaps.
3. Check the triple cocycle, including compatibility with all structure maps.
4. Descend quasi-coherent modules and finite locally free tensors first.
5. Descend algebras, affine pieces, and closed or open loci cut out by those tensors.
6. Apply scheme effectivity and then descend morphisms and their identities.
7. Descend finiteness, flatness, smoothness, properness, and related properties separately.
8. For quasi-projectivity, identify the compatible ample line bundle, a finite-flat norm, or the canonical positive divisor that supplies it.
9. Verify the claimed universal property by full faithfulness, not only by local existence.

For an infinite family, perform steps 4–8 over each affine part of the base using a finite affine refinement, then glue by uniqueness. This protocol keeps size, quasi-compactness, effectivity, and property descent visibly distinct.

## 17. Synthesis

### 17.1 The three levels of descent

Faithfully flat descent has three interacting levels. At the algebraic level, tensoring with a faithfully flat algebra preserves and reflects exactness. The Amitsur equalizer then reconstructs modules, their morphisms, and algebraic structures. At the geometric level, affine spectra translate algebra descent into affine descent, and stable affine neighborhoods permit general schemes to be glued. At the positive-geometric level, finite presentation and ample line bundles turn local embeddings into global quasi-projective or projective models.

The logic can be summarized by the diagram

$$
\begin{array}{ccccc}
M&\longrightarrow&B\otimes_AM&\rightrightarrows&B^{[1]}\otimes_AM\\
\downarrow&&\downarrow&&\downarrow\\
X&\longleftarrow&X_T&\substack{\longleftarrow\\[-.35em]\longleftarrow}&X_{T^{[1]}}.
\end{array}
$$

The upper row is an equalizer; reversing affine arrows turns it into geometric gluing. Triple tensor products enforce transitivity. Faithfulness gives uniqueness, flatness preserves relations, and quasi-compactness makes finite data descend.

### 17.2 Reusable theorem package

The results established in this book may be used in the following precise form.

- Set-indexed fpqc families admit affine-local finite affine refinements; infinite coproducts and infinite products are unnecessary.
- Modules, algebras, quasi-coherent sheaves, schemes, and their morphisms have effective fpqc descent, with pairwise isomorphisms satisfying the triple cocycle.
- Finite generation, finite presentation, flatness, finite projectivity, finite local freeness, and rank descend faithfully flatly.
- Affine, finite, finite locally free, quasi-compact, quasi-separated, separated, finite-type, finite-presentation, flat, proper, smooth, étale, and unramified morphisms are fpqc local on the base with the qualifications stated in Chapter 10.
- Line bundles, vector bundles, tensors, pairings, sections, effective Cartier divisors, finite-flat group schemes, actions, and torsors descend when their structure maps and cocycles are included.
- Quasi-affineness descends for quasi-compact quasi-separated morphisms through the intrinsic affine envelope.
- Quasi-projective and projective objects descend with compatible ample data; a finite locally free cover permits an unpolarized descent by norms; canonical positive divisors and rigidified polarizations cover the generalized elliptic and PEL cases.

Each assertion includes both effectivity and full faithfulness. Properties are not confused with objects: after constructing the descended object, the relevant local-on-the-base theorem must still be applied.

### 17.3 Conclusion

Descent replaces the vague instruction “glue the local pieces” by a rigid and verifiable mechanism. Double overlaps say how to compare, triple overlaps say that comparison is transitive, faithful flatness says that local equality is genuine equality, and flatness says that the algebraic relations survive transport. Quasi-compactness ensures that finite geometry remains finite.

This mechanism is broad enough to recover schemes and their sheaves, yet precise enough to remember a group law, a torsor, a determinant condition, or an ample polarization. Generalized elliptic curves and PEL families can therefore be built where their coordinates and bundles are simplest and then returned to the original base without loss of structure. The result is not merely a local object whose fibers look right. It is a unique global object, carrying exactly the maps, equations, finiteness, and positivity that the moduli problem requires.
