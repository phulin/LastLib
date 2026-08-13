# Continuous Cohomology of Profinite Groups

## Contents

1. [Compact symmetry and discrete arithmetic](#1-compact-symmetry-and-discrete-arithmetic)
   - [Why continuity changes group cohomology](#11-why-continuity-changes-group-cohomology)
   - [Profinite groups](#12-profinite-groups)
   - [Discrete continuous modules](#13-discrete-continuous-modules)
   - [Compact-to-discrete factorization](#14-compact-to-discrete-factorization)
   - [Invariants and the first warning about exactness](#15-invariants-and-the-first-warning-about-exactness)
   - [Orbits, stabilizers, and finite submodules](#16-orbits-stabilizers-and-finite-submodules)
2. [Continuous cochains](#2-continuous-cochains)
   - [Why inhomogeneous cochains are practical](#21-why-inhomogeneous-cochains-are-practical)
   - [The differential and its signs](#22-the-differential-and-its-signs)
   - [Normalized cochains](#23-normalized-cochains)
   - [Homogeneous cochains](#24-homogeneous-cochains)
   - [Continuous versus abstract classes](#25-continuous-versus-abstract-classes)
   - [Why the two complexes encode the same geometry](#26-why-the-two-complexes-encode-the-same-geometry)
3. [The first three degrees](#3-the-first-three-degrees)
   - [Degree zero: fixed points](#31-degree-zero-fixed-points)
   - [Degree one: crossed homomorphisms](#32-degree-one-crossed-homomorphisms)
   - [Torsors and descent](#33-torsors-and-descent)
   - [Degree two: factor sets](#34-degree-two-factor-sets)
   - [Which topological extensions are classified](#35-which-topological-extensions-are-classified)
   - [Central extensions and projective lifting](#36-central-extensions-and-projective-lifting)
   - [Three low-degree sanity checks](#37-three-low-degree-sanity-checks)
4. [Exact sequences and connecting classes](#4-exact-sequences-and-connecting-classes)
   - [Why a boundary map must exist](#41-why-a-boundary-map-must-exist)
   - [The explicit connecting homomorphism](#42-the-explicit-connecting-homomorphism)
   - [The long exact sequence](#43-the-long-exact-sequence)
   - [Naturality and diagrams of coefficients](#44-naturality-and-diagrams-of-coefficients)
   - [Why topological coefficients require new hypotheses](#45-why-topological-coefficients-require-new-hypotheses)
   - [Bockstein maps and a worked boundary](#46-bockstein-maps-and-a-worked-boundary)
5. [Functoriality, restriction, and transfer](#5-functoriality-restriction-and-transfer)
   - [Two kinds of variance](#51-two-kinds-of-variance)
   - [Restriction and conjugation](#52-restriction-and-conjugation)
   - [Coinduction as the source of corestriction](#53-coinduction-as-the-source-of-corestriction)
   - [Shapiro first, then corestriction](#54-shapiro-first-then-corestriction)
   - [Restriction–corestriction formulas](#55-restrictioncorestriction-formulas)
   - [A vanishing consequence](#56-a-vanishing-consequence)
   - [Permutation modules and a concrete Shapiro calculation](#57-permutation-modules-and-a-concrete-shapiro-calculation)
6. [Normal subgroups and inflation](#6-normal-subgroups-and-inflation)
   - [Separating quotient and kernel information](#61-separating-quotient-and-kernel-information)
   - [Inflation and restriction](#62-inflation-and-restriction)
   - [The five-term inflation–restriction sequence](#63-the-five-term-inflationrestriction-sequence)
   - [Transgression as an extension obstruction](#64-transgression-as-an-extension-obstruction)
   - [Complete proof in low degrees](#65-complete-proof-in-low-degrees)
   - [A useful special case](#66-a-useful-special-case)
   - [Two tests for transgression](#67-two-tests-for-transgression)
7. [Cup products and coefficient pairings](#7-cup-products-and-coefficient-pairings)
   - [Why cohomology should multiply](#71-why-cohomology-should-multiply)
   - [The cochain formula](#72-the-cochain-formula)
   - [Leibniz rule](#73-leibniz-rule)
   - [Associativity, units, and signs](#74-associativity-units-and-signs)
   - [Naturality and the projection formula](#75-naturality-and-the-projection-formula)
   - [Evaluation, duality, and low-degree meaning](#76-evaluation-duality-and-low-degree-meaning)
8. [Finite quotients and filtered limits](#8-finite-quotients-and-filtered-limits)
   - [Why compactness makes discrete cohomology finite-level](#81-why-compactness-makes-discrete-cohomology-finite-level)
   - [The finite-quotient theorem](#82-the-finite-quotient-theorem)
   - [Finite modules and filtered unions](#83-finite-modules-and-filtered-unions)
   - [Why this fails for profinite coefficients](#84-why-this-fails-for-profinite-coefficients)
   - [What a finite-level representative does and does not prove](#85-what-a-finite-level-representative-does-and-does-not-prove)
9. [Induction, coinduction, and Shapiro's lemma](#9-induction-coinduction-and-shapiros-lemma)
   - [Distributing a module over cosets](#91-distributing-a-module-over-cosets)
   - [Evaluation and an explicit inverse](#92-evaluation-and-an-explicit-inverse)
   - [Proof and continuity of Shapiro's lemma](#93-proof-and-continuity-of-shapiros-lemma)
   - [Infinite index and acyclic modules](#94-infinite-index-and-acyclic-modules)
10. [The derived-functor meaning of continuous cohomology](#10-the-derived-functor-meaning-of-continuous-cohomology)
    - [Why a second construction matters](#101-why-a-second-construction-matters)
    - [Coinduced objects and enough injectives](#102-coinduced-objects-and-enough-injectives)
    - [Acyclicity of coinduced modules](#103-acyclicity-of-coinduced-modules)
    - [The comparison theorem](#104-the-comparison-theorem)
    - [Consequences of the comparison](#105-consequences-of-the-comparison)
    - [What the theorem does not say](#106-what-the-theorem-does-not-say)
11. [Cyclic and procyclic calculations](#11-cyclic-and-procyclic-calculations)
    - [Why cyclic groups are the local model](#111-why-cyclic-groups-are-the-local-model)
    - [The periodic resolution](#112-the-periodic-resolution)
    - [Recovering the degree-one formula directly](#113-recovering-the-degree-one-formula-directly)
    - [Trivial action and concrete examples](#114-trivial-action-and-concrete-examples)
    - [A nontrivial action](#115-a-nontrivial-action)
    - [The procyclic group](#116-the-procyclic-group-widehatmathbf-z)
    - [The group $\mathbf Z_\ell$](#117-the-group-mathbf-z_ell)
    - [Finite quotient calculations as consistency checks](#118-finite-quotient-calculations-as-consistency-checks)
    - [Worked extension classes for $C_m$](#119-worked-extension-classes-for-c_m)
12. [Topological and $\ell$-adic coefficients](#12-topological-and-ell-adic-coefficients)
    - [A separate coefficient theory](#121-a-separate-coefficient-theory)
    - [Four coefficient regimes](#122-four-coefficient-regimes)
    - [Profinite modules and the Milnor sequence](#123-profinite-modules-and-the-milnor-sequence)
    - [$\ell$-adic lattices and vector spaces](#124-ell-adic-lattices-and-vector-spaces)
    - [Products and matrix actions](#125-products-and-matrix-actions)
    - [A procyclic comparison across topologies](#126-a-procyclic-comparison-across-topologies)
    - [The strict procyclic lattice complex](#126a-the-strict-procyclic-lattice-complex)
    - [Exact sequences in the topological setting](#127-exact-sequences-in-the-topological-setting)
    - [Algebraic groups and their possible quotient topologies](#128-algebraic-groups-and-their-possible-quotient-topologies)
13. [Cohomological dimension and the normal-subgroup spectral sequence](#13-cohomological-dimension-and-the-normal-subgroup-spectral-sequence)
    - [Measuring the height of obstructions](#131-measuring-the-height-of-obstructions)
    - [Examples and torsion](#132-examples-and-torsion)
    - [Dimension shifting](#133-dimension-shifting)
    - [The Hochschild--Serre spectral sequence](#134-the-hochschild--serre-spectral-sequence)
    - [Edges, differentials, and low degrees](#135-edges-differentials-and-low-degrees)
    - [Subgroups and extensions](#136-subgroups-and-extensions)
    - [Consequences and limitations](#137-consequences-and-limitations)
    - [Detecting bounds with finite coefficients](#138-detecting-bounds-with-finite-coefficients)
14. [Tangent spaces, obstructions, and a working toolkit](#14-tangent-spaces-obstructions-and-a-working-toolkit)
    - [Why deformation theory sees the adjoint action](#141-why-deformation-theory-sees-the-adjoint-action)
    - [Equivalence and the tangent space](#142-equivalence-and-the-tangent-space)
    - [The obstruction cocycle for a small extension](#143-the-obstruction-cocycle-for-a-small-extension)
    - [The torsor of lifts and its automorphisms](#144-the-torsor-of-lifts-and-its-automorphisms)
    - [Extension classes as the universal model](#145-extension-classes-as-the-universal-model)
    - [Characters and extensions of representations](#146-characters-and-extensions-of-representations)
    - [Fixed determinant and framed conditions](#147-fixed-determinant-and-framed-conditions)
    - [Imposing and comparing local or quotient conditions](#148-imposing-and-comparing-local-or-quotient-conditions)
    - [Vanishing criteria and what they buy](#149-vanishing-criteria-and-what-they-buy)
    - [A calculation protocol](#1410-a-calculation-protocol)
    - [Final perspective](#1411-final-perspective)

Continuous cohomology is where topology, symmetry, and obstruction theory meet. A profinite group
is assembled from finite quotients, but its natural representations need not factor through one
finite quotient. Discrete coefficients see only finite information one cochain at a time;
profinite and $\ell$-adic coefficients retain compatible information at every level. Much of the
subject consists of knowing which of these two principles is active in a given argument.

The first half of the book builds the explicit calculus. Chapters 1--3 pass from continuous
actions to homogeneous and inhomogeneous cochains and then interpret degrees zero, one, and two.
Chapters 4--7 develop the four operations that move classes: connecting maps change
coefficients, restriction and corestriction change groups, inflation and transgression separate a
normal subgroup from its quotient, and cup products combine classes. Chapters 8--10 explain why
the calculus is canonical: finite quotients compute discrete cochains, Shapiro identifies
cohomology after coinduction, and the cochain construction agrees with right derived invariants.

The second half tests and extends the theory. Cyclic and procyclic groups make every convention
computable. Topological coefficients force a careful distinction between direct limits, inverse
limits, and scalar extension. Cohomological dimension and the normal-subgroup spectral sequence
organize higher obstructions. The final chapter derives tangent and obstruction spaces for
continuous representations directly from matrix multiplication across square-zero extensions.

Throughout, an unadorned $H^n(G,A)$ has discrete continuous coefficients. For a nondiscrete
topological module $M$ we write $H^n_{\mathrm{cts}}(G,M)$ when the distinction matters. Every
statement involving a quotient, a limit, or a transfer records the topology and finiteness
hypothesis that makes it valid.

## 1. Compact symmetry and discrete arithmetic

### 1.1 Why continuity changes group cohomology

Group cohomology measures the failure of invariants to be exact. For a group $G$ acting on an abelian group $A$, the invariants

$$
A^G=\{a\in A:ga=a\text{ for every }g\in G\}
$$

form a left exact functor, but an invariant element in a quotient need not have an invariant lift. The successive cohomology groups record this failure. When $G$ is a Galois group, however, it is usually profinite rather than merely abstract, and its representations carry continuity conditions. Ignoring topology creates many spurious cochains. For example, an abstract homomorphism from a profinite group to a discrete group need not have open kernel; only those with open kernel are visible to continuous cohomology.

This chapter establishes the topological vocabulary that makes the distinction precise. The central setting is a profinite group acting continuously on a discrete abelian group. It is broad enough for finite Galois modules and discrete torsion modules, and rigid enough that compactness turns every individual calculation into a finite one. Later we enlarge the coefficient category to profinite and $\ell$-adic modules, but we will not silently transfer exactness assertions from one setting to the other.

### 1.2 Profinite groups

A **profinite group** is a compact Hausdorff totally disconnected topological group. Equivalently, it is an inverse limit of finite discrete groups. Open normal subgroups form a neighborhood basis of the identity, and

$$
G\simeq\varprojlim_{U\trianglelefteq_o G}G/U.
$$

Here $U\trianglelefteq_oG$ means that $U$ is open and normal. Every open subgroup has finite index, because its cosets form an open cover of the compact space $G$. Conversely, every **closed** finite-index subgroup is open. An abstract finite-index subgroup need not be open in a general profinite group: discontinuous finite quotients can occur. We state hypotheses in terms of openness because topology, not abstract index, controls continuous cochains.

A closed subgroup of a profinite group is profinite. A quotient by a closed normal subgroup is profinite. An arbitrary subgroup need be neither closed nor profinite in its subspace topology. Restriction of continuous cohomology will therefore be used primarily for closed subgroups, and corestriction only for open subgroups.

The basic examples are finite groups, $\mathbf Z_\ell=\varprojlim_n\mathbf Z/\ell^n\mathbf Z$, the procyclic group $\widehat{\mathbf Z}$, products of finite groups, and Galois groups of possibly infinite Galois extensions. In ramification theory, upper ramification groups in an infinite Galois group are defined through compatible finite quotients. That same finite-quotient philosophy will reappear here, but cohomology also remembers coefficient stabilizers.

### 1.3 Discrete continuous modules

Let $G$ be profinite. A **discrete $G$-module** is an abelian group $A$, given the discrete topology, together with an action $G\times A\to A$ that is continuous. Since $A$ is discrete, continuity is equivalent to requiring that every stabilizer

$$
G_a=\{g\in G:ga=a\}
$$

be open. It is not necessary that one open subgroup fix all of $A$. Such a common subgroup exists when $A$ is finite, because the intersection of finitely many open stabilizers is open. Thus every continuous action on a finite discrete module factors through a finite quotient of $G$.

For an arbitrary discrete module,

$$
A=\bigcup_{U\trianglelefteq_oG}A^U=\varinjlim_{U\trianglelefteq_oG}A^U.
$$

Indeed, the stabilizer of $a$ contains an open normal subgroup: take the core of an open subgroup contained in $G_a$. This identity is one source of the finite-quotient description of continuous cohomology.

The category of discrete $G$-modules is abelian. Kernels and cokernels carry the discrete topology and the induced action remains continuous. A short exact sequence will always mean

$$
0\longrightarrow A\xrightarrow{i}B\xrightarrow{p}C\longrightarrow0
$$

exact as abelian groups, with continuous $G$-equivariant maps. Notice that $p$ admits a set-theoretic section, and every map between discrete spaces is continuous. This elementary fact will make cochains degreewise exact; it has no automatic analogue for nondiscrete topological modules.

### 1.4 Compact-to-discrete factorization

The decisive compactness principle is simple.

**Lemma (finite image).** If $X$ is compact and $D$ is discrete, every continuous map $f:X\to D$ has finite image.

**Proof.** The fibers $f^{-1}(d)$ are open and cover $X$. Compactness gives a finite subcover, so only finitely many fibers are nonempty. $\square$

When $X$ is profinite, more is true: every continuous map $X\to D$ factors through a finite discrete quotient of the underlying profinite space. To see this, cover $X$ by finitely many clopen sets on which $f$ is constant, then refine that partition by fibers of a sufficiently fine finite quotient. For $X=G^n$, one may choose an open normal $U\trianglelefteq G$ such that $f$ is constant on every product of right $U$-cosets. Thus

$$
f:G^n\longrightarrow D
$$

factors as a set map through $(G/U)^n$.

There is an important qualification. A cochain factoring as a function through $(G/U)^n$ need not belong to the cochain complex for the quotient action unless $U$ also acts trivially on all values involved. Enlarging the condition to include the finitely many values ensures they lie in $A^U$. This simultaneous control of arguments and values is the mechanism behind the direct-limit theorem in Chapter 8.

### 1.5 Invariants and the first warning about exactness

The functor $A\mapsto A^G$ is left exact. Given a short exact sequence as above,

$$
0\longrightarrow A^G\longrightarrow B^G\longrightarrow C^G
$$

is exact. Surjectivity at the right generally fails. Let $G=C_m=\langle\sigma\rangle$ act on $B=\mathbf Z/m^2\mathbf Z$ by

$$
\sigma b=(1+m)b,
$$

and let $A=mB$, $C=B/A$. The action on $C$ is trivial, so $C^G=C$. But an element $b$ lifting $\bar b\in C$ is invariant precisely when $mb=0$ in $B$, which forces $\bar b=0$. Thus nonzero invariant classes have no invariant lift. The connecting homomorphism will turn this failure into a class in $H^1(G,A)$.

This example also indicates the governing principle of the book: cohomology is not extra decoration on invariants. It is the organized record of every obstruction to making choices equivariant.

### 1.6 Orbits, stabilizers, and finite submodules

The open-stabilizer condition has two useful consequences that will silently support later finite
reductions. For $a\in A$, the orbit $Ga$ is finite because it is in bijection with the finite set
$G/G_a$. If $A$ is torsion and $S\subset A$ is finite, the subgroup generated by the union of the
orbits of elements of $S$ is a finitely generated torsion group, hence finite, and it is
$G$-stable. Thus every discrete torsion $G$-module is a filtered union of finite $G$-submodules.

Neither conclusion survives after removing its decisive hypothesis. For a nontorsion discrete
module, the $G$-stable subgroup generated by one finite orbit can be infinite: with trivial
action, the orbit of $1\in\mathbf Z$ has one element but generates all of $\mathbf Z$. For a
topological module, an orbit may itself be infinite: multiplication by units gives a continuous
action of $\mathbf Z_\ell^\times$ on the compact module $\mathbf Z_\ell$, and the orbit of $1$ is
infinite. These examples explain why later filtered-union results assume torsion when they invoke
finite submodules, while cochain factorization itself needs only a discrete target.

There is also a useful distinction between an action that is continuous element by element and
one controlled by a common finite quotient. Every $a\in A$ has an open stabilizer, but their
intersection over all $a$ can fail to be open. For example,

$$
A=\mathbf Q_\ell/\mathbf Z_\ell
$$

may carry a continuous action detected at arbitrarily high $\ell$-power levels. Each finite
subgroup is controlled by an open kernel, but the entire action can have infinite image. This is
precisely why $A^U$ appears in the finite-quotient theorem rather than one fixed finite quotient
acting on all of $A$.

## 2. Continuous cochains

### 2.1 Why inhomogeneous cochains are practical

There are several equivalent models for group cohomology. Homogeneous cochains display symmetry cleanly, while inhomogeneous cochains make low-degree formulas and deformation calculations transparent. We use normalized inhomogeneous cochains for calculations, retaining the unnormalized complex when degeneracies simplify proofs.

For a discrete $G$-module $A$, define

$$
C^n(G,A)=\operatorname{Map}_{\mathrm{cts}}(G^n,A),\qquad n\geq0,
$$

where $G^0$ is a point, so $C^0(G,A)=A$. Addition is pointwise. These are **continuous cochains**. The corresponding abstract cochain group contains every set map $G^n\to A$ and can be vastly larger.

### 2.2 The differential and its signs

For $f\in C^n(G,A)$, set

$$
\begin{aligned}
(df)(g_1,\ldots,g_{n+1})={}&g_1f(g_2,\ldots,g_{n+1})\\
&+\sum_{i=1}^{n}(-1)^if(g_1,\ldots,g_ig_{i+1},\ldots,g_{n+1})\\
&+(-1)^{n+1}f(g_1,\ldots,g_n).
\end{aligned}
$$

Each term is continuous: multiplication in $G$, the action, and $f$ are continuous. In degrees zero, one, and two this says

$$
(da)(g)=ga-a,
$$

$$
(df)(g,h)=g f(h)-f(gh)+f(g),
$$

and

$$
(dc)(g,h,k)=g c(h,k)-c(gh,k)+c(g,hk)-c(g,h).
$$

The signs are chosen so that adjacent ways of multiplying or deleting entries cancel.

**Proposition.** The composite $d\circ d$ is zero.

**Proof.** Introduce coface maps on an $n$-cochain:

$$
\begin{aligned}
(\delta^0f)(g_1,\ldots,g_{n+1})&=g_1f(g_2,\ldots,g_{n+1}),\\
(\delta^if)(g_1,\ldots,g_{n+1})&=f(g_1,\ldots,g_ig_{i+1},\ldots,g_{n+1})\quad(1\leq i\leq n),\\
(\delta^{n+1}f)(g_1,\ldots,g_{n+1})&=f(g_1,\ldots,g_n).
\end{aligned}
$$

Associativity of the group law and the action gives $\delta^j\delta^i=\delta^i\delta^{j-1}$ for $i<j$. In the double alternating sum

$$
d^2f=\sum_{i,j}(-1)^{i+j}\delta^j\delta^if,
$$

each term indexed by $i<j$ cancels the same composite indexed in the opposite order, whose sign differs by one. Hence $d^2f=0$. $\square$

We write

$$
Z^n(G,A)=\ker(d:C^n\to C^{n+1}),\qquad
B^n(G,A)=\operatorname{im}(d:C^{n-1}\to C^n),
$$

and define

$$
H^n(G,A)=Z^n(G,A)/B^n(G,A).
$$

By convention $B^0=0$.

### 2.3 Normalized cochains

An inhomogeneous cochain is **normalized** if it vanishes whenever one of its arguments is the identity. Normalized cochains form a subcomplex. Every cohomology class has a normalized representative, and the inclusion of the normalized complex into the full complex induces an isomorphism on cohomology.

Here is the normalization argument. For $0\leq i<n$, let $s_i$ delete an identity inserted after
the first $i$ arguments; equivalently, on the simplicial bar construction the corresponding
degeneracy repeats one vertex. The face and degeneracy operations satisfy

$$
\delta_i s_j=
\begin{cases}
s_{j-1}\delta_i,&i<j,\\
1,&i=j\text{ or }i=j+1,\\
s_j\delta_{i-1},&i>j+1.
\end{cases}
$$

Filter the degenerate cochains by the position of the first identity argument. On the associated
successive quotient, $(-1)^j s_j$ is a contracting homotopy: the two identity terms above leave
one copy of the cochain, and all remaining faces stay in an earlier filtration piece. Descending
induction on $j$ contracts the whole degeneracy subcomplex. The quotient by it is exactly the
normalized complex. Therefore the inclusion of normalized cochains is a quasi-isomorphism.

Every operation used here inserts or deletes a fixed identity coordinate and composes with a
continuous cochain. It therefore preserves continuity. This last observation is small but
essential: the abstract normalization proof really does remain inside continuous cochains. We
will impose normalization whenever writing cocycles that classify extensions, but the
differential always means the formula of the preceding section.

For a normalized $1$-cochain, $f(1)=0$. For a normalized $2$-cochain, $c(1,g)=c(g,1)=0$. These conditions ensure that the identity in a crossed product has the expected form.

### 2.4 Homogeneous cochains

The homogeneous model is useful for transfer and conceptual symmetry. Let

$$
C^n_{\mathrm{hom}}(G,A)=\{F:G^{n+1}\to A\text{ continuous}:F(gg_0,\ldots,gg_n)=gF(g_0,\ldots,g_n)\}.
$$

Its differential is omission:

$$
(DF)(g_0,\ldots,g_{n+1})=\sum_{i=0}^{n+1}(-1)^iF(g_0,\ldots,\widehat g_i,\ldots,g_{n+1}).
$$

The two models are isomorphic. From homogeneous to inhomogeneous,

$$
f(g_1,\ldots,g_n)=F(1,g_1,g_1g_2,\ldots,g_1\cdots g_n),
$$

and conversely

$$
F(g_0,\ldots,g_n)=g_0f(g_0^{-1}g_1,g_1^{-1}g_2,\ldots,g_{n-1}^{-1}g_n).
$$

A direct substitution verifies that these maps are inverse chain maps. This also gives a second proof of $d^2=0$: in the homogeneous complex, deleting two entries in opposite orders produces identical terms with opposite signs.

### 2.5 Continuous versus abstract classes

When $G$ is finite, its topology is discrete and every cochain is continuous, so continuous and abstract cohomology agree. When $G$ is infinite profinite, they need not. With trivial action on a discrete group $A$,

$$
H^1(G,A)=\operatorname{Hom}_{\mathrm{cts}}(G,A),
$$

whereas abstract $H^1$ contains all group homomorphisms. A continuous homomorphism to a discrete group has open kernel and finite image. Thus a homomorphism that detects infinitely fine information cannot define a continuous class.

The point is not merely cardinality. Continuous classes are exactly those compatible with passage to sufficiently coarse finite arithmetic data. All constructions below—connecting maps, products, restriction, and transfer—are built within this continuous complex.

### 2.6 Why the two complexes encode the same geometry

The formulas of Section 2.4 can be remembered geometrically. A homogeneous tuple

$$
(g_0,\ldots,g_n)
$$

is a list of vertices. Left multiplication moves every vertex at once, so equivariance removes
the irrelevant choice of origin. After moving $g_0$ to $1$, the successive edge labels are

$$
g_0^{-1}g_1,\quad g_1^{-1}g_2,\quad\ldots,\quad g_{n-1}^{-1}g_n.
$$

These are exactly the inhomogeneous variables. Conversely, starting with edge labels
$(x_1,\ldots,x_n)$ and origin $g_0$, the vertices are

$$
g_0,\quad g_0x_1,\quad g_0x_1x_2,\quad\ldots,\quad g_0x_1\cdots x_n.
$$

Deleting an interior vertex multiplies the two adjacent edge labels. Deleting the first vertex
moves the origin and therefore applies the action to the value. Deleting the last vertex simply
forgets the final edge. These three possibilities are precisely the three kinds of terms in the
inhomogeneous differential.

This picture supplies more than a mnemonic. The homogeneous model makes conjugation homotopies,
transfer, and graded commutativity transparent because one can insert or move vertices. The
inhomogeneous model makes a $1$-cocycle a crossed homomorphism and a $2$-cocycle an associativity
defect. We will switch models only through the explicit chain isomorphism of Section 2.4, so no
cohomology class or sign changes when the notation changes.

## 3. The first three degrees

### 3.1 Degree zero: fixed points

The equation $da=0$ says $ga=a$ for all $g$, so

$$
H^0(G,A)=A^G.
$$

This identification is the anchor for all higher degrees: continuous cohomology extends the invariants functor. If $G$ acts trivially, every element survives in degree zero, but higher groups can still be nonzero because equivariant lifting remains a separate problem.

If the order of every finite quotient through which a calculation factors is invertible on the coefficients, averaging often makes invariants exact. For a finite group $F$, if multiplication by $|F|$ is invertible on $A$, then

$$
a\longmapsto \frac1{|F|}\sum_{g\in F}ga
$$

is a projection onto $A^F$, and $H^n(F,A)=0$ for $n>0$. For an infinite profinite group there is no literal finite sum over all elements. One must first know that the problem factors through a finite quotient, or use a suitable integration theory. This is a recurring reason not to import finite-group arguments without checking continuity and coefficients.

### 3.2 Degree one: crossed homomorphisms

A continuous map $f:G\to A$ is a $1$-cocycle precisely when

$$
f(gh)=f(g)+g f(h).
$$

Such a map is called a **crossed homomorphism** or **derivation**. A $1$-coboundary has the form

$$
f_a(g)=ga-a.
$$

Thus

$$
H^1(G,A)=\frac{\{\text{continuous crossed homomorphisms }G\to A\}}
{\{g\mapsto ga-a:a\in A\}}.
$$

For trivial action, crossed homomorphisms are ordinary continuous homomorphisms and all coboundaries vanish. With nontrivial action, $H^1$ measures affine actions with prescribed linear part. Indeed, a cocycle $f$ defines

$$
g*a=ga+f(g).
$$

The cocycle equation is exactly associativity of this affine action. Translating the origin by $a_0$ changes $f$ by the coboundary $g\mapsto ga_0-a_0$. Consequently $H^1(G,A)$ classifies such affine actions up to translation, and the class is zero exactly when the affine action has a fixed point.

### 3.3 Torsors and descent

The same idea has a coordinate-free form. An $A$-torsor is a nonempty set $X$ on which $A$ acts simply transitively. Suppose $X$ is discrete and $G$ acts continuously, compatibly with the $G$-action on $A$:

$$
g(a+x)=ga+gx.
$$

Choose $x_0\in X$ and define $f(g)$ by $gx_0=f(g)+x_0$. Then $f$ is a continuous $1$-cocycle. Replacing $x_0$ changes it by a coboundary. Hence $H^1(G,A)$ classifies continuous $A$-torsors with compatible $G$-action, up to equivariant isomorphism. The zero class corresponds to a $G$-fixed point.

This interpretation explains why $H^1$ is a natural home for descent problems: local or quotient data determine a torsor of choices, and the cohomology class measures whether a choice can be made invariant.

### 3.4 Degree two: factor sets

A normalized continuous $2$-cochain $c:G\times G\to A$ is a cocycle when

$$
g c(h,k)-c(gh,k)+c(g,hk)-c(g,h)=0.
$$

This equation is the associativity condition for the multiplication

$$
(a,g)(b,h)=(a+gb+c(g,h),gh)
$$

on $A\times G$. Normalization makes $(0,1)$ the identity, and

$$
0\longrightarrow A\longrightarrow A\times_cG\longrightarrow G\longrightarrow1
$$

becomes a group extension inducing the given conjugation action on $A$.

If $c'=c+db$ for a normalized continuous $1$-cochain $b:G\to A$, then

$$
(a,g)\longmapsto(a-b(g),g)
$$

is an isomorphism $A\times_cG\to A\times_{c'}G$ fixing $A$ and $G$. Thus a coboundary is precisely a change of section.

### 3.5 Which topological extensions are classified

Topology requires an exact statement. Give $A\times_cG$ the product topology. It is a topological group because the action and $c$ are continuous. Conversely, consider an extension of topological groups

$$
0\longrightarrow A\longrightarrow E\xrightarrow{\pi}G\longrightarrow1
$$

in which $A$ is a discrete abelian normal subgroup, conjugation induces the specified action, and $\pi$ admits a continuous set-theoretic section $s:G\to E$ with $s(1)=1$. Define

$$
c(g,h)=s(g)s(h)s(gh)^{-1}\in A.
$$

Then $c$ is continuous, normalized, and associative multiplication in $E$ gives the cocycle equation. Changing $s$ changes $c$ by a coboundary. Therefore $H^2(G,A)$ classifies equivalence classes of extensions that are continuously split as spaces.

For finite discrete kernels in many profinite situations the quotient map has continuous local sections, and compact zero-dimensional patching supplies a global section. The section hypothesis should nevertheless be kept visible; arbitrary topological extensions are not classified by writing down continuous global factor sets unless such a section exists.

The zero class means that one can choose $s$ to be a homomorphism, so the extension is the semidirect product $A\rtimes G$. Thus $H^2$ is an obstruction group: it measures the failure of a set-theoretic lift of multiplication to be compatible with multiplication itself.

### 3.6 Central extensions and projective lifting

If the $G$-action on $A$ is trivial, $A$ lies in the center of $A\times_cG$, and $H^2(G,A)$ classifies continuously split central extensions. This includes the familiar problem of lifting a projective representation. Given maps $\widetilde\rho(g)$ lifting a projective representation, products differ by scalars:

$$
\widetilde\rho(g)\widetilde\rho(h)=c(g,h)\widetilde\rho(gh).
$$

Associativity forces $c$ to be a $2$-cocycle. Rescaling the lifts changes $c$ by a coboundary. The projective representation lifts to an honest representation exactly when $[c]=0$.

This is the foundational obstruction pattern used repeatedly later: choose provisional lifts, measure their failure to respect structure, prove that failure is a cocycle, and observe that changing choices alters it by a coboundary.

### 3.7 Three low-degree sanity checks

If $G$ is trivial, the complex has $C^n=A$ in every degree, but its alternating differential
contracts all positive degrees. Thus

$$
H^0(1,A)=A,\qquad H^n(1,A)=0\quad(n>0).
$$

The vanishing agrees with every interpretation: all elements are fixed, every affine action of
the trivial group has a fixed point, and every extension of the trivial group splits.

If $G$ acts trivially on $A$, then

$$
H^1(G,A)=\operatorname{Hom}_{\mathrm{cts}}(G,A).
$$

Take $G=\prod_{r\geq1}C_2$ and $A=C_2$. Every continuous character depends on only finitely many
coordinates because its kernel is open. An abstract character need not have this property. The
example makes the word “continuous” visible without any higher machinery.

Finally, let $G=C_2$ act on $A=\mathbf Z$ by sign. A crossed homomorphism is determined by
$a=f(\sigma)$, and the relation $\sigma^2=1$ imposes

$$
a+\sigma a=0,
$$

which holds for every $a$. Coboundaries have the form $\sigma b-b=-2b$, so

$$
H^1(C_2,\mathbf Z_{\mathrm{sign}})\simeq\mathbf Z/2\mathbf Z.
$$

The nonzero class defines the affine involution $x\mapsto-x+1$ on $\mathbf Z$. It has no integral
fixed point, although it acquires one after enlarging the coefficient group to
$\tfrac12\mathbf Z$. The connecting and coefficient maps developed next formalize exactly this
kind of change in solvability.

## 4. Exact sequences and connecting classes

### 4.1 Why a boundary map must exist

Suppose

$$
0\longrightarrow A\xrightarrow{i}B\xrightarrow{p}C\longrightarrow0
$$

is a short exact sequence of discrete $G$-modules. A cocycle in $C$ may be lifted as a cochain in $B$, but its lift need not remain a cocycle. Its differential lands in $A$, and that defect is the connecting class. This construction turns failed equivariant lifting into a systematic sequence relating all degrees.

For every $n$, the sequence

$$
0\longrightarrow C^n(G,A)\longrightarrow C^n(G,B)\longrightarrow C^n(G,C)\longrightarrow0
$$

is exact. Only surjectivity needs comment. A continuous cochain $f:G^n\to C$ has finite image. Choose in $B$ one lift of each of those finitely many values; composing with this finite choice gives a continuous lift. No equivariance of the choice is required.

### 4.2 The explicit connecting homomorphism

Let $c\in Z^n(G,C)$. Choose a continuous cochain $b\in C^n(G,B)$ with $p(b)=c$. Since

$$
p(db)=d(p b)=dc=0,
$$

there is a unique $a\in C^{n+1}(G,A)$ with $i(a)=db$. Moreover $i(da)=d^2b=0$, so $a$ is a cocycle. Define

$$
\delta[c]=[a]\in H^{n+1}(G,A).
$$

If $b$ is replaced by $b+i(x)$, then $a$ changes by $dx$. If $c$ is changed by a coboundary, lifting the cochain that produces that coboundary shows that $[a]$ is unchanged. Hence $\delta$ is well defined.

In degree zero, for $c\in C^G$ choose $b\in B$ lifting it. Then

$$
\delta(c)(g)=g b-b\in A.
$$

This is a crossed homomorphism. It vanishes in cohomology precisely when some correction $b-i(a)$ is $G$-fixed, which is precisely when $c$ has an invariant lift.

In degree one, lift a cocycle $c:G\to C$ to a continuous map $b:G\to B$. Then

$$
\delta[c](g,h)=g b(h)-b(gh)+b(g).
$$

The resulting extension-type class is the obstruction to correcting $b$ into a $B$-valued cocycle.

### 4.3 The long exact sequence

The preceding maps form the long exact sequence

$$
\begin{aligned}
0&\to H^0(G,A)\to H^0(G,B)\to H^0(G,C)\xrightarrow{\delta}H^1(G,A)\\
&\to H^1(G,B)\to H^1(G,C)\xrightarrow{\delta}H^2(G,A)\to\cdots.
\end{aligned}
$$

**Proof of exactness.** Exactness at $H^n(G,B)$ is representative-level. A class coming from $A$ maps to zero in $C$. Conversely, if $b\in Z^n(G,B)$ maps to a coboundary $d c_0$ in $C$, lift $c_0$ to $b_0$ in $B$. Then $b-db_0$ is a cocycle taking values in $A$, so $[b]$ comes from $H^n(G,A)$.

At $H^n(G,C)$, a class coming from $B$ has a cocycle lift, so its connecting class is zero. Conversely, if $c\in Z^n(G,C)$ has $\delta[c]=0$, choose a lift $b$. Writing $db=i(dx)$ for some $x\in C^n(G,A)$, the corrected lift $b-i(x)$ is a cocycle and maps to $c$.

At $H^{n+1}(G,A)$, a connecting class maps to zero in $B$ because it is represented there by $db$. Conversely, if $a\in Z^{n+1}(G,A)$ becomes $db$ in $B$, then $p(b)$ is a cocycle in $C$ and its boundary is $[a]$. These three arguments repeat in every degree and prove the sequence exact. $\square$

The proof exposes the practical content of exactness: each kernel statement is a recipe for correcting a cochain by one degree lower.

### 4.4 Naturality and diagrams of coefficients

A commutative diagram of short exact sequences of discrete $G$-modules induces a morphism of long exact sequences. In particular, connecting homomorphisms commute with coefficient maps. To verify this, take a lift upstairs, apply the vertical map, and observe that it is a valid lift downstairs; applying $d$ in either order gives the same cochain.

Naturality prevents connecting classes from depending on arbitrary presentations. It also allows a complicated obstruction to be mapped into a simpler coefficient module where it can be calculated. Later cup products and restriction maps will commute with boundaries in similarly controlled ways.

### 4.5 Why topological coefficients require new hypotheses

If $A,B,C$ are nondiscrete topological modules, a continuous cochain $G^n\to C$ need not lift continuously to $B$. Therefore a short exact sequence of underlying topological groups need not yield a short exact sequence of cochain complexes. The long exact sequence remains valid when $B\to C$ has enough continuous lifting—for example, a continuous global section, or hypotheses ensuring continuous lifts from every profinite $G^n$—but not from algebraic exactness alone.

This is the first major boundary between discrete and topological coefficient theories. We will construct cohomology for topological modules in Chapter 12, but all unqualified long exact sequences before then belong to the discrete category.

### 4.6 Bockstein maps and a worked boundary

A particularly useful connecting map comes from multiplication by an integer. Suppose
multiplication by $m$ is surjective on a discrete $G$-module $B$, and put $A=B[m]$. Then

$$
0\longrightarrow A\longrightarrow B\xrightarrow{m}B\longrightarrow0,
$$

is short exact. The connecting map

$$
\beta:H^n(G,B)\longrightarrow H^{n+1}(G,A)
$$

is called a **Bockstein**. More commonly one uses
$0\to\mathbf Z/m\to\mathbf Z/m^2\to\mathbf Z/m\to0$, with the first map multiplication by
$m$ and the second reduction. If $c$ is represented by a cocycle modulo $m$, lift its values
modulo $m^2$, apply $d$, and divide the result by $m$. The result modulo $m$ is $\beta(c)$.

For example, let $G=C_m$ act trivially and let

$$
x\in H^1(C_m,\mathbf Z/m\mathbf Z)
$$

send the chosen generator to $1$. Lift $x(\sigma^i)=i$ using representatives
$0,\ldots,m-1$ in $\mathbf Z/m^2\mathbf Z$. Its differential records whether addition of $i$ and
$j$ crosses a multiple of $m$. After division by $m$, the resulting $2$-cocycle is the carry
cocycle of Section 11.9. It represents the extension

$$
0\to C_m\to C_{m^2}\to C_m\to0.
$$

Thus a boundary map can turn a character into the obstruction to lifting that character through
a larger cyclic group. This calculation also checks the sign convention: reversing the
differential convention would replace the extension class by its negative.

## 5. Functoriality, restriction, and transfer

### 5.1 Two kinds of variance

Cohomology is covariant in coefficients and contravariant in groups. If $u:A\to B$ is a continuous $G$-equivariant homomorphism, composition defines

$$
u_*:H^n(G,A)\longrightarrow H^n(G,B).
$$

If $\varphi:H\to G$ is a continuous homomorphism and $A$ is a discrete $G$-module, regard $A$ as an $H$-module through $\varphi$. Pullback of cochains gives

$$
\varphi^*:H^n(G,A)\longrightarrow H^n(H,A),
$$

$$
(\varphi^*f)(h_1,\ldots,h_n)=f(\varphi(h_1),\ldots,\varphi(h_n)).
$$

Both operations commute with $d$, as follows directly from equivariance and the differential formula. They preserve identity maps and composition. A map involving both groups and coefficients is obtained by combining them, provided the coefficient map is equivariant for the relevant pulled-back action.

### 5.2 Restriction and conjugation

For a closed subgroup $H\leq G$, the inclusion gives the **restriction** map

$$
\operatorname{res}^G_H:H^n(G,A)\longrightarrow H^n(H,A).
$$

Closedness ensures that $H$ is itself profinite. The cochain formula is simply restriction from $G^n$ to $H^n$.

Conjugation also acts on subgroup cohomology. For $g\in G$, define

$$
c_g:H\longrightarrow gHg^{-1},\qquad h\longmapsto ghg^{-1}.
$$

Together with the coefficient action $a\mapsto ga$, this induces

$$
g_*:H^n(H,A)\longrightarrow H^n(gHg^{-1},A).
$$

In degree one,

$$
(g_*f)(x)=g f(g^{-1}xg).
$$

Inner conjugation acts trivially on $H^n(G,A)$. At the cochain level it is chain homotopic to the identity; in degree one the difference is visibly a coboundary after applying the cocycle equation. This fact is what makes quotient groups act on the cohomology of normal subgroups.

### 5.3 Coinduction as the source of corestriction

Restriction exists for every closed subgroup, but transfer back to $G$ requires $H$ to be open. Before defining it, we introduce a module that packages cosets correctly. For a closed subgroup $H$ and a discrete $H$-module $A$, let

$$
\operatorname{Coind}_H^G A
=\{\phi:G\to A\text{ continuous}:\phi(hx)=h\phi(x)\}.
$$

Give it the $G$-action

$$
(g\phi)(x)=\phi(xg).
$$

We give this function group the discrete topology. The action is continuous: a continuous map from compact $G$ to discrete $A$ is uniformly locally constant, so some open subgroup fixes it under right translation. Thus every coinduced function has an open stabilizer.

When $H$ is open, $H\backslash G$ is finite and a coinduced function is determined by finitely many values. Choose representatives $R$ for the right cosets $H\backslash G$. Then

$$
\operatorname{Coind}_H^G A\simeq\prod_{r\in R}A
$$

as abelian groups, though the $G$-action permutes factors and twists them by $H$.

There is a $G$-equivariant trace map

$$
\epsilon:\operatorname{Coind}_H^G A\longrightarrow A,
\qquad
\epsilon(\phi)=\sum_{r\in H\backslash G}r^{-1}\phi(r),
$$

when $A$ is the restriction of a $G$-module. The expression is independent of representatives: replacing $r$ by $hr$ changes $r^{-1}\phi(r)$ to $r^{-1}h^{-1}h\phi(r)$. To check equivariance, write $rg=hr'$ and use $r^{-1}h=gr'^{-1}$; right multiplication permutes the cosets.

### 5.4 Shapiro first, then corestriction

Shapiro's lemma, proved with explicit maps in Chapter 9, provides an isomorphism

$$
H^n(G,\operatorname{Coind}_H^GA)\simeq H^n(H,A).
$$

For open $H$, define

$$
\operatorname{cor}^G_H:H^n(H,A)\longrightarrow H^n(G,A)
$$

as the inverse of Shapiro followed by $H^n(G,\epsilon)$. This direction is worth fixing: restriction goes from the large group to the subgroup, while corestriction goes from an open subgroup to the large group.

The construction has an explicit inhomogeneous formula. Choose $R$ representing $H\backslash G$. For $r\in R$ and $g_1,\ldots,g_n\in G$, define recursively $r_0=r$ and representatives $r_i\in R$ by

$$
Hr_{i-1}g_i=Hr_i,
$$

and put

$$
h_i=r_{i-1}g_ir_i^{-1}\in H.
$$

For $f\in C^n(H,A)$,

$$
(\operatorname{Cor}f)(g_1,\ldots,g_n)
=\sum_{r\in R}r^{-1}f(h_1,\ldots,h_n).
$$

This is a continuous cochain because the coset choices are locally constant. A calculation with the differential shows that $\operatorname{Cor}$ is a chain map; changing representatives changes it by a chain homotopy, so the induced map is canonical. The formula is best understood as “follow each coset through the word $g_1\cdots g_n$, record the correction terms in $H$, then average after transporting coefficients back.”

In degree zero,

$$
\operatorname{cor}^G_H(a)=\sum_{r\in H\backslash G}r^{-1}a
=\sum_{x\in G/H}xa,\qquad a\in A^H.
$$

This is the norm from $H$-invariants to $G$-invariants.

### 5.5 Restriction–corestriction formulas

The fundamental identity on cohomology of the large group is

$$
\operatorname{cor}^G_H\circ\operatorname{res}^G_H=[G:H]
\quad\text{on }H^n(G,A).
$$

At degree zero it follows because an invariant element is fixed by every coset representative.
For the general proof, use homogeneous cochains. Restrict a simplex to $H$, lift it along every
coset, and apply the trace. The result is a sum indexed by $H\backslash G$. The summand indexed by
$Hr$ is the original cochain after translating all vertices by $r$ and transporting the value by
$r^{-1}$. Translation of all vertices is an inner-action map on the homogeneous resolution. The
prism obtained by inserting $r$ successively among the vertices is a chain homotopy from that map
to the identity. Hence every summand induces the identity on cohomology, and there are $[G:H]$
summands.

The reverse composite is not generally multiplication by the index. If $H\trianglelefteq G$ is open and normal, then

$$
\operatorname{res}^G_H\circ\operatorname{cor}^G_H
=\sum_{g\in G/H}g_*
\quad\text{on }H^n(H,A).
$$

Only on classes fixed by the quotient action does this become $[G:H]$. Confusing the two composites is a common source of incorrect arguments.

For arbitrary open subgroups $H,K\leq G$, the full relation is the Mackey formula

$$
\operatorname{res}^G_K\operatorname{cor}^G_H
=\sum_{x\in K\backslash G/H}
\operatorname{cor}^{K}_{K\cap xHx^{-1}}
\,x_*\,
\operatorname{res}^{H}_{H\cap x^{-1}Kx}.
$$

Each term corresponds to one double coset. Here is the decisive combinatorics. Partition
$G/H$ into $K$-orbits. The orbit containing $xH$ is

$$
K/(K\cap xHx^{-1}).
$$

Following the transfer path inside this orbit first conjugates the original $H$-cochain by $x$,
then restricts it to $H\cap x^{-1}Kx$, and finally transfers from
$K\cap xHx^{-1}$ to $K$. Summing over the orbit gives the corresponding term of the formula;
summing over all orbits gives the full left side. Changes of representatives alter the cochain
maps by the same inner-conjugation homotopies used above. This proves the Mackey formula on
cohomology and explains why restriction and corestriction form a coherent calculus rather than
two unrelated operations.

### 5.6 A vanishing consequence

If $H$ is open and $H^n(H,A)=0$, restriction–corestriction shows that $[G:H]$ annihilates $H^n(G,A)$. More generally, the kernel of restriction is killed by $[G:H]$. This elementary observation is frequently decisive when $H$ is chosen to trivialize an action and the index is invertible on the coefficient group.

The hypothesis “open” cannot be weakened to “closed” in corestriction statements: the sum would range over infinitely many cosets, and a general discrete module carries no notion of convergence for it.

### 5.7 Permutation modules and a concrete Shapiro calculation

Let $H\leq G$ be open and take the trivial $H$-module $\mathbf Z$. Coinduction is the permutation
module of integer-valued functions on the finite set $H\backslash G$:

$$
\operatorname{Coind}_H^G\mathbf Z
\simeq\mathbf Z[H\backslash G].
$$

Shapiro gives

$$
H^n\bigl(G,\mathbf Z[H\backslash G]\bigr)
\simeq H^n(H,\mathbf Z).
$$

In degree zero, a $G$-invariant function on the transitive coset set is constant, so evaluation at
$H$ identifies it with an integer. This is the visible degree-zero shadow of the theorem. In
degree one both sides vanish when $H$ is finite, but for infinite $H$ the statement retains
genuine continuous information.

Now replace $\mathbf Z$ by a finite trivial module $A$. A class in
$H^1(H,A)=\operatorname{Hom}_{\mathrm{cts}}(H,A)$ corresponds under Shapiro to an affine cocycle
on $G$ with values distributed over the cosets. Corestriction sums its transported components.
If $H$ is normal, restricting the result back to $H$ produces the sum of the conjugate
characters

$$
h\longmapsto\sum_{g\in G/H}g f(g^{-1}hg).
$$

For trivial coefficients and abelian $G$, this is $[G:H]f$. For nontrivial conjugation or
coefficients it need not be. This simple calculation is the degree-one reason the reverse
restriction--corestriction composite is a conjugate sum rather than plain multiplication.

## 6. Normal subgroups and inflation

### 6.1 Separating quotient and kernel information

Let $N\trianglelefteq G$ be closed and normal, and write $Q=G/N$. A $G$-cocycle can carry information already visible on $Q$ and additional information detected on $N$. Inflation–restriction organizes these layers. It is the elementary precursor of a spectral sequence, but low degrees can be proved entirely with cocycles and extensions.

The group $Q$ acts on $A^N$. It also acts on $H^j(N,A)$: for a representative $g\in G$ of $q\in Q$,

$$
(qf)(n_1,\ldots,n_j)
=g f(g^{-1}n_1g,\ldots,g^{-1}n_jg)
$$

up to the standard cochain homotopy. A different representative differs by an inner element of $N$, which acts trivially on cohomology, so the action is well defined.

### 6.2 Inflation and restriction

For $f\in C^n(Q,A^N)$, define

$$
(\operatorname{inf}f)(g_1,\ldots,g_n)
=f(\bar g_1,\ldots,\bar g_n).
$$

Because values are $N$-fixed, the quotient action used in the differential is well defined. This gives

$$
\operatorname{inf}:H^n(Q,A^N)\longrightarrow H^n(G,A).
$$

Restriction gives $H^n(G,A)\to H^n(N,A)$. Its image is $Q$-invariant: conjugating a restricted global class by $g\in G$ gives the restriction of the inner conjugate of that global class, hence the same cohomology class.

### 6.3 The five-term inflation–restriction sequence

The low-degree sequence is

$$
\begin{aligned}
0\longrightarrow H^1(Q,A^N)&\xrightarrow{\operatorname{inf}}H^1(G,A)
\xrightarrow{\operatorname{res}}H^1(N,A)^Q\\
&\xrightarrow{\operatorname{trg}}H^2(Q,A^N)
\xrightarrow{\operatorname{inf}}H^2(G,A).
\end{aligned}
$$

The middle map is called transgression. Before proving exactness, we construct it in a way that makes its obstruction meaning precise.

### 6.4 Transgression as an extension obstruction

Take $\xi\in H^1(N,A)^Q$. A cocycle $f:N\to A$ equips the $A$-torsor underlying $A$ with the
affine $N$-action

$$
n*a=na+f(n).
$$

Quotient invariance of $[f]$ says that conjugation by every $g\in G$ carries this $N$-torsor to
an isomorphic one. Choosing such isomorphisms need not make them compatible under multiplication
in $Q$. Their failure of compatibility is an automorphism of the underlying $N$-torsor, hence
translation by an element of $A^N$. It is a $2$-cocycle on $Q$; changing the chosen isomorphisms
changes it by a coboundary. Its class is $\operatorname{trg}(\xi)$.

For readers wanting a cochain formula, suppose that the following continuous choices are
available. Choose a continuous section $s:Q\to G$, with $s(1)=1$, and set

$$
u(q,r)=s(q)s(r)s(qr)^{-1}\in N.
$$

Assume one can choose $a_q\in A$ continuously in $q$, with $a_1=0$, satisfying

$$
s(q)f(s(q)^{-1}ns(q))-f(n)=na_q-a_q.
$$

Define a continuous $1$-cochain $F:G\to A$ by the unique expression $g=ns(q)$:

$$
F(ns(q))=f(n)+na_q.
$$

Its differential is constant on quotient cosets and takes values in $A^N$. Evaluating it on the chosen section gives the explicit cocycle

$$
t(q,r)=s(q)a_r-f(u(q,r))-u(q,r)a_{qr}+a_q.
$$

Indeed this is $(dF)(s(q),s(r))$. The displayed invariance relation shows directly that conjugating either argument through $N$ does not change $dF$, and $d^2F=0$ then gives $dt=0$. We define $\operatorname{trg}[f]=[t]$. Replacing $a_q$ changes $t$ by a coboundary; changing $f$ within its class or changing $s$ gives the same result after the corresponding correction of $F$.

The existence of $a_q$ for each individual $q$ follows from invariance of the cohomology class;
its continuous dependence on $q$ is an additional point and is why it was stated as a hypothesis
for this formula. In complete generality, transgression is constructed from the filtered
continuous bar complex, as proved in Sections 13.4--13.5. The intrinsic compatibility obstruction
of the preceding paragraph is the same differential. Thus neither a global section nor a
continuous family $a_q$ is a hypothesis of the five-term sequence; they are only conveniences
for displaying a single cocycle formula.

Most applications use an easier characterization:

$$
\operatorname{trg}(\xi)=0
\quad\Longleftrightarrow\quad
\xi\text{ is the restriction of a class in }H^1(G,A).
$$

The proof below establishes this equivalence rather than assuming it.

### 6.5 Complete proof in low degrees

**Theorem.** The five-term sequence of Section 6.3 is exact.

**Proof.** First, inflation on $H^1$ is injective. If an inflated cocycle $f(\bar g)$ equals $ga-a$, then for $n\in N$ its value is zero, so $na=a$ and $a\in A^N$. Therefore $f(q)=qa-a$ already as a cocycle on $Q$.

A global cocycle $z:G\to A$ restricts trivially in $H^1(N,A)$ exactly when, after subtracting a coboundary, it vanishes on $N$. Suppose $z|_N(n)=na-a$. Replace $z$ by $z-(g\mapsto ga-a)$. Then $z(n)=0$, and the cocycle equation gives

$$
z(gn)=z(g),\qquad z(ng)=z(g),
$$

the second equality using $z(n)=0$ and applying the first to the conjugate $g^{-1}ng$. Also $n z(g)=z(g)$, obtained by comparing $z(ng)$ and $z(g(g^{-1}ng))$. Hence $z$ descends to a cocycle $Q\to A^N$. This proves exactness at $H^1(G,A)$.

The restriction of a global class has zero transgression: the global cocycle itself supplies compatible identifications, so the compatibility defect vanishes. Conversely, if the transgression of $\xi$ vanishes, alter the chosen identifications by an $A^N$-valued $1$-cochain so that their multiplication defect is zero. They then define a genuine compatible $G$-action on the torsor representing $\xi$. Choosing a point of that torsor produces a continuous crossed homomorphism $G\to A$ restricting to $\xi$. This proves exactness at $H^1(N,A)^Q$.

Finally, the inflated transgression is zero. Over $G$, the quotient compatibility choices can be indexed by actual elements rather than quotient classes; the original $N$-object then supplies a splitting of the obstruction. Conversely, suppose $c\in Z^2(Q,A^N)$ inflates to a coboundary $db$ on $G$. Restricting $b$ to $N$ gives a $1$-cocycle because the inflated $c$ vanishes on $N\times N$. The relation $db=\operatorname{inf}c$ implies that its class is $Q$-invariant. Tracing through the compatibility defect shows that its transgression is $[c]$: the cochain $b$ is exactly a system of quotient identifications whose failure to multiply is $c$. Thus $[c]$ lies in the image of transgression, proving exactness at $H^2(Q,A^N)$. $\square$

The proof also explains the limit of the statement: inflation need not be injective in degree two; its kernel is precisely the transgressive part of $H^1(N,A)^Q$.

### 6.6 A useful special case

If $H^1(N,A)=0$, inflation gives an isomorphism

$$
H^1(Q,A^N)\xrightarrow{\sim}H^1(G,A)
$$

and an injection $H^2(Q,A^N)\hookrightarrow H^2(G,A)$. If instead $N$ acts trivially on $A$, then

$$
H^1(N,A)=\operatorname{Hom}_{\mathrm{cts}}(N,A),
$$

with $Q$ acting by conjugation on $N$ and through its action on $A$. This form is particularly effective when $N$ is an inertia subgroup or a kernel chosen to trivialize finite coefficients, though arithmetic calculations themselves belong to later applications.

### 6.7 Two tests for transgression

If the group extension is a direct product $G=N\times Q$ and $N$ acts trivially on $A$, every
$Q$-invariant homomorphism $f:N\to A$ extends to $G$ by $f(n,q)=f(n)$. Exactness therefore forces
its transgression to vanish. The same conclusion is visible from the factor set: the section
$q\mapsto(1,q)$ is a homomorphism, so $u(q,r)=1$ and one may take all compatibility corrections
to be zero.

A nonsplit central extension gives the opposite behavior. Let

$$
1\longrightarrow N\longrightarrow G\longrightarrow Q\longrightarrow1
$$

be central, let $A$ have trivial action, and let $f:N\to A$ be a continuous homomorphism. Choose a
continuous section when available and let

$$
u(q,r)=s(q)s(r)s(qr)^{-1}\in N
$$

be its factor set. No conjugation corrections are needed. Up to the sign fixed by the chosen
differential, transgression is represented by

$$
(q,r)\longmapsto -f(u(q,r)).
$$

Thus transgression pushes the extension class of $G$ forward along $f$. It vanishes exactly when
the character $f$ extends from $N$ to $G$. For the cyclic sequence

$$
1\to C_m\to C_{m^2}\to C_m\to1
$$

and $f:C_m\to C_m$ the identity, the carry factor set maps to the nonzero class in
$H^2(C_m,C_m)$. Hence $f$ cannot extend to a homomorphism $C_{m^2}\to C_m$ whose restriction to
the kernel is the identity: such a homomorphism would send a generator to an element whose
restriction has incompatible order.

These tests capture the role of transgression. It is zero when kernel data and quotient
multiplication can be made simultaneously compatible, and it is the pushed-forward factor set
when the group extension itself supplies the incompatibility.

## 7. Cup products and coefficient pairings

### 7.1 Why cohomology should multiply

Obstructions often interact bilinearly: a character pairs with another character, an endomorphism pairs with a dual endomorphism, or two extension classes combine into a higher class. Cup products lift a $G$-equivariant pairing of coefficients to cohomology. Their signs are forced by the differential, not chosen for appearance.

Let $A,B,C$ be discrete $G$-modules and let $\mu:A\times B\to C$ be biadditive and $G$-equivariant:

$$
\mu(ga,gb)=g\mu(a,b).
$$

### 7.2 The cochain formula

For $f\in C^p(G,A)$ and $g\in C^q(G,B)$ define

$$
(f\smile g)(x_1,\ldots,x_{p+q})
=\mu\big(f(x_1,\ldots,x_p),(x_1\cdots x_p)g(x_{p+1},\ldots,x_{p+q})\big).
$$

The empty product is $1$ when $p=0$. The twist by $x_1\cdots x_p$ is essential: without it, the first face of the differential would not match equivariance of $\mu$. The resulting cochain is continuous. In degree $(1,1)$,

$$
(f\smile g)(x,y)=\mu(f(x),xg(y)).
$$

Thus even the simplest product remembers the action.

### 7.3 Leibniz rule

**Proposition.** For $f$ of degree $p$,

$$
d(f\smile g)=df\smile g+(-1)^pf\smile dg.
$$

**Proof.** Expand the left side. Faces that multiply two entries among the first $p$ arguments reproduce $df\smile g$. Faces wholly among the last $q$ arguments reproduce $f\smile dg$, with their indices shifted by $p$ and hence the factor $(-1)^p$. At the seam, the final face of $df$ and the initial action face of $dg$ appear with opposite signs. Equivariance of $\mu$ identifies their values, so they cancel. Every term is accounted for exactly once. $\square$

Consequently cocycles cup to cocycles, and changing either factor by a coboundary changes the product by a coboundary. We obtain

$$
H^p(G,A)\times H^q(G,B)\longrightarrow H^{p+q}(G,C).
$$

### 7.4 Associativity, units, and signs

If coefficient pairings are associative, substitution in the formula shows

$$
(f\smile g)\smile h=f\smile(g\smile h)
$$

already on cochains. The two action twists multiply to the same prefix. Thus for a discrete $G$-ring $R$, $H^*(G,R)$ is an associative graded ring with unit $1\in H^0(G,R)$.

The cochain product is not literally graded commutative. To compare the two orders, pass to
homogeneous cochains. The product comes from the front--back diagonal on a simplex: the first
cochain reads the first $p+1$ vertices and the second reads the last $q+1$. Swapping the two
factors uses the back--front diagonal. Insert one vertex at a time to slide the dividing point
through the simplex. The alternating sum of these prisms is a homotopy between the two diagonals;
moving a block of $p$ degrees past a block of $q$ degrees contributes $(-1)^{pq}$. All insertion
maps preserve continuity. Thus, on cohomology, if the reversed pairing satisfies
$\mu^\tau(b,a)=\mu(a,b)$, then

$$
\alpha\smile\beta=(-1)^{pq}\beta\smile\alpha,
$$

where the right side uses $\mu^\tau$. For commutative $R$, the cohomology ring is graded-commutative. If $2$ is invertible, odd-degree classes square to zero; in characteristic two the sign gives no such conclusion. The coefficient switch must be stated: classes with distinct coefficient modules cannot exchange places without a reversed pairing.

### 7.5 Naturality and the projection formula

Cup products commute with coefficient maps and group pullback. In particular,

$$
\operatorname{res}^G_H(\alpha\smile\beta)
=\operatorname{res}^G_H\alpha\smile\operatorname{res}^G_H\beta.
$$

For open $H\leq G$, corestriction satisfies

$$
\operatorname{cor}^G_H(\operatorname{res}^G_H\alpha\smile\beta)
=\alpha\smile\operatorname{cor}^G_H\beta.
$$

This follows by inserting the transfer sum and moving the global cochain outside it. A second projection formula places the restricted global class on the right, with the corresponding graded sign and reversed pairing.

If short exact coefficient sequences and pairings are compatible, choosing lifts and applying the Leibniz rule gives

$$
\delta(\alpha\smile\beta)
=\delta(\alpha)\smile\beta+(-1)^{\deg\alpha}\alpha\smile\delta(\beta),
$$

whenever the two terms are defined. This is the precise sense in which the defect of a product is the product of the defects.

### 7.6 Evaluation, duality, and low-degree meaning

Let $A$ be a finite discrete $G$-module and let
$A^\vee=\operatorname{Hom}(A,\mathbf Q/\mathbf Z)$ carry the contragredient action

$$
(g\lambda)(a)=\lambda(g^{-1}a).
$$

Evaluation is $G$-equivariant, so it gives pairings

$$
H^p(G,A)\times H^q(G,A^\vee)
\longrightarrow H^{p+q}(G,\mathbf Q/\mathbf Z).
$$

The construction alone does not say that these pairings are perfect; perfectness is an
additional theorem depending on the group and finiteness properties. What is formal is their
naturality and the projection formula. This distinction will matter whenever a later arithmetic
duality theorem uses the cup product as its underlying pairing.

In low degree the formula has a direct interpretation. If $a\in A^G$ and
$f:G\to A^\vee$ is a crossed homomorphism, then

$$
(a\smile f)(g)=f(g)(a).
$$

Thus an invariant vector evaluates a dual deformation class. If $x:G\to A$ and
$y:G\to B$ are $1$-cocycles, then

$$
(x\smile y)(g,h)=\mu(x(g),g y(h))
$$

is a factor set. It measures the failure of two compatible first-order choices to combine
without a second-order correction. This is the elementary source of many obstruction pairings.

The Bockstein of Section 4.6 is also a derivation. For a coefficient ring sequence compatible
with multiplication,

$$
\beta(\alpha\smile\gamma)
=\beta(\alpha)\smile\gamma
+(-1)^{\deg\alpha}\alpha\smile\beta(\gamma).
$$

The proof requires no new machinery: lift the two cocycles, expand the differential of their cup
product, and use the cochain Leibniz rule. This example illustrates why signs should be fixed at
the cochain level before interpreting products geometrically.

## 8. Finite quotients and filtered limits

### 8.1 Why compactness makes discrete cohomology finite-level

A continuous cochain on $G^n$ with discrete values sees only finitely much of $G$. Yet its values may be fixed by a different open subgroup from the one controlling its arguments. The correct finite-level complex therefore uses both a quotient $G/U$ and the invariant subgroup $A^U$.

For $U\trianglelefteq_oG$, the quotient $G/U$ acts on $A^U$. Inflation embeds

$$
C^n(G/U,A^U)\longrightarrow C^n(G,A).
$$

If $V\subseteq U$, inflation and inclusion of invariants give the transition maps for a filtered system.

### 8.2 The finite-quotient theorem

**Theorem.** For every discrete continuous $G$-module $A$ and every $n\geq0$,

$$
C^n(G,A)=\varinjlim_{U\trianglelefteq_oG}C^n(G/U,A^U)
$$

as cochain complexes, and

$$
H^n(G,A)\simeq\varinjlim_{U\trianglelefteq_oG}H^n(G/U,A^U).
$$

**Proof.** Let $f:G^n\to A$ be continuous. Its image is finite. Choose an open normal subgroup fixing every value. Uniform local constancy on compact $G^n$ also gives an open normal subgroup such that $f$ is constant on products of its cosets. Intersect the two subgroups. Then $f$ has values in $A^U$ and factors through $(G/U)^n$.

The transition maps commute with $d$. Filtered colimits are exact in abelian groups, so kernels and images commute with this colimit. Taking cohomology therefore proves the second identity. $\square$

The theorem is often quoted for discrete torsion modules because those are the coefficients most common in Galois cohomology. Torsion is not needed: discreteness and continuity of the action are the exact hypotheses. Writing $H^n(G/U,A)$ with fixed $A$ is usually meaningless because $U$ may act nontrivially.

### 8.3 Finite modules and filtered unions

If $A$ is finite, one open normal subgroup $U_0$ acts trivially on all of $A$, and

$$
H^n(G,A)=\varinjlim_{U\subseteq U_0}H^n(G/U,A).
$$

This does not say that one fixed finite quotient computes all degrees. A cocycle factors through some quotient, but a coboundary relation may require a finer quotient.

Similarly, if $A=\varinjlim_iA_i$ is a filtered union of discrete $G$-submodules, compactness and exactness of filtered colimits give

$$
H^n(G,A)=\varinjlim_iH^n(G,A_i).
$$

For a torsion module, one may use finite pieces only after verifying that they are $G$-stable. A finite set has finite $G$-orbits, but the subgroup generated by those orbits must also be checked to be finite in the coefficient category under consideration.

### 8.4 Why this fails for profinite coefficients

For a profinite coefficient module $T$, a continuous map $G^n\to T$ need not have finite image and generally does not factor through a finite quotient of $G$. The identity $\mathbf Z_\ell\to\mathbf Z_\ell$ is the simplest counterexample. Thus the theorem is not a generic compactness slogan.

Profinite and $\ell$-adic coefficients are approached through inverse limits of finite coefficient quotients, with possible derived-limit corrections, rather than through a direct limit over quotients of the group.

### 8.5 What a finite-level representative does and does not prove

Suppose $c\in Z^n(G,A)$ factors through a cocycle

$$
c_U\in Z^n(G/U,A^U).
$$

If $[c_U]=0$, then the inflated class is certainly zero. The converse can fail at that same
level: a continuous cochain $b$ with $db=c$ may require a smaller open normal subgroup
$V\subseteq U$ before it factors. Then the inflation of $[c_U]$ to
$H^n(G/V,A^V)$ is zero even though $[c_U]$ was nonzero. A class in the filtered colimit is zero
precisely when it dies after some sufficiently fine transition.

Finite cyclic groups display this phenomenon explicitly. A positive even class in a cyclic
quotient can inflate to zero after the cyclic quotient is enlarged by a kernel whose order kills
the class. The procyclic group consequently has no cohomology above degree one with discrete
torsion coefficients even though every one of its nontrivial finite cyclic quotients has
periodic higher cohomology.

There is a second caution. If $A$ is finite and $U_0$ acts trivially on it, the system may be
indexed by $U\subseteq U_0$, but it is still a system:

$$
H^n(G,A)\neq H^n(G/U_0,A)
$$

in general. Equality holds only if every class and every relation among classes is already
detected at that fixed level. This extra assertion requires a separate argument; continuity
alone gives only the filtered colimit.

## 9. Induction, coinduction, and Shapiro's lemma

### 9.1 Distributing a module over cosets

Restriction changes the acting group without changing the module. Coinduction turns an $H$-module into a $G$-module by distributing copies over cosets. Shapiro's lemma says that this distribution introduces no new cohomology.

For open $H\leq G$, the module $\operatorname{Coind}_H^GA$ from Section 5.3 is a finite product
of discrete copies of $A$, hence is discrete. Induction distributes a direct sum of copies of
$A$ over the cosets, whereas coinduction distributes a product. At finite index the coset set is
finite, so sums and products coincide and the two constructions are naturally isomorphic. At
infinite index they differ, and topology must be specified; coinduction by continuous equivariant
functions is the robust construction here.

### 9.2 Evaluation and an explicit inverse

Evaluation at the identity gives a chain map

$$
S:C^n(G,\operatorname{Coind}_H^GA)\longrightarrow C^n(H,A),
$$

$$
S(F)(h_1,\ldots,h_n)=F(h_1,\ldots,h_n)(1).
$$

The right-translation action on coinduced functions and their $H$-equivariance make $S$ commute with $d$.

Choose representatives $R$ for $H\backslash G$, with $1\in R$, and write

$$
x=\kappa(x)r(x),\qquad \kappa(x)\in H, r(x)\in R.
$$

For $f\in C^n(H,A)$, put $r_0=r(x)$ and recursively

$$
r_i=r(r_{i-1}g_i),\qquad h_i=r_{i-1}g_ir_i^{-1}\in H.
$$

Define

$$
(Tf)(g_1,\ldots,g_n)(x)=\kappa(x)f(h_1,\ldots,h_n).
$$

It is $H$-equivariant in $x$ and continuous because all coset functions are locally constant. If $g_i\in H$ and $x=1$, then $r_i=1$, so $STf=f$.

### 9.3 Proof and continuity of Shapiro's lemma

**Theorem (Shapiro).** For open $H\leq G$ and discrete $H$-module $A$, evaluation induces natural isomorphisms

$$
H^n(G,\operatorname{Coind}_H^GA)\xrightarrow{\sim}H^n(H,A).
$$

**Proof.** A face-by-face calculation gives $dT=Td$: multiplying an entry updates the coset path, while $h_i$ records exactly its correction in $H$. We have $ST=1$.

The composite $TS$ depends on the transversal. In the homogeneous model, insert $r(x)$ successively among the vertices. The alternating sum of these insertions defines a prism homotopy $K$ with

$$
dK+Kd=1-TS.
$$

Interior faces cancel in pairs and the two boundary faces are the original simplex and its coset retraction. Since $r(x)$ is locally constant, $K$ preserves continuity. Thus $S$ and $T$ induce inverse maps. $\square$

This proof recovers the corestriction formula of Chapter 5 by following $T$ with the coinduced trace.

### 9.4 Infinite index and acyclic modules

For closed $H$ of infinite index, there is generally no continuous transversal for
$H\backslash G$, so the finite-transversal proof cannot simply be repeated. Shapiro nevertheless remains
valid for the discrete coinduced module of continuous equivariant functions. Its proof requires
the cochain--derived comparison and is given in Section 10.5, after the needed comparison theorem
has been established. What already remains clear is the limitation: there is no finite trace sum
over $G/H$. Thus Shapiro survives at infinite index, but corestriction does not.

For $H=\{1\}$, the desired conclusion is

$$
H^n(G,\operatorname{Coind}_{1}^{G}A)=0\qquad(n>0).
$$

This special case does not need the deferred theorem. In homogeneous cochains, identify a
cochain with a continuous function of the simplex variables and one final $G$-variable. Moving
the final variable to the origin by equivariance and then inserting it as a new first vertex
defines an extra degeneracy. The alternating omission differential $D$ satisfies

$$
Ds+sD=1
$$

in positive degrees: every interior omission occurs twice with opposite signs, while the two end
terms leave the original cochain. Coordinate insertion, multiplication, and inversion are
continuous, so this is a contraction inside the continuous complex. Hence coinduced modules from
the trivial subgroup are acyclic for invariants. This supplies the engine for dimension shifting
and for the comparison theorem without using infinite-index Shapiro circularly.

## 10. The derived-functor meaning of continuous cohomology

### 10.1 Why a second construction matters

The cochain complex gives formulas, but formulas alone do not explain why continuous cohomology
is the canonical sequence of functors extending invariants. A different route begins with the
left exact functor

$$
\Gamma(G,-):A\longmapsto A^G
$$

on the abelian category of discrete continuous $G$-modules and forms its right derived functors
$R^n\Gamma(G,-)$. If these groups agree with cochain cohomology, every theorem proved by cocycles
can be used together with the formal calculus of derived functors, and conversely the abstract
construction acquires explicit representatives.

The coefficient category is important. This chapter concerns **discrete continuous**
$G$-modules. The analogous assertion for an unrestricted category of topological modules is not
automatic: that category may have the wrong exact structure, and continuous maps into a
quotient need not lift. The comparison theorem below is therefore both a positive result and a
boundary marker.

### 10.2 Coinduced objects and enough injectives

Let $I$ be a discrete abelian group. Set

$$
\mathcal C(I)=\operatorname{Map}_{\mathrm{cts}}(G,I),
\qquad
(g\phi)(x)=\phi(xg).
$$

The group $\mathcal C(I)$ is given the discrete topology. Every $\phi$ has finite image and is
uniformly locally constant, so an open subgroup of $G$ fixes it under right translation. Thus it
is a discrete continuous $G$-module. Evaluation at $1$ gives the adjunction

$$
\operatorname{Hom}_G(A,\mathcal C(I))
\simeq \operatorname{Hom}_{\mathbf Z}(A,I).
$$

Indeed, a $G$-map $u$ is sent to $a\mapsto u(a)(1)$. In the other direction, an additive map
$v:A\to I$ gives

$$
u_v(a)(x)=v(xa).
$$

For fixed $a$, the orbit map $x\mapsto xa$ is continuous into a discrete space and hence has
finite image, so $u_v(a)$ really is a continuous function. The two constructions are inverse.

If $I$ is injective as an abelian group, the adjunction shows that $\mathcal C(I)$ is injective
among discrete $G$-modules: extending a $G$-map into $\mathcal C(I)$ is the same as extending an
additive map into $I$. Given a discrete $G$-module $A$, choose an embedding of its underlying
abelian group into an injective group $I$. Then

$$
A\longrightarrow\mathcal C(I),
\qquad
a\longmapsto\bigl(x\mapsto \iota(xa)\bigr)
$$

is $G$-equivariant and injective, as evaluation at $1$ recovers $\iota(a)$. Consequently the
category has enough injectives and $R^n\Gamma(G,-)$ is defined in the usual way.

This construction also explains why continuity belongs in the definition: replacing continuous
functions by all functions would produce injectives for abstract group cohomology, a different
theory.

### 10.3 Acyclicity of coinduced modules

For any discrete abelian group $I$, not necessarily injective, the coinduced module
$\mathcal C(I)$ has no positive continuous cohomology:

$$
H^n(G,\mathcal C(I))=0\qquad(n>0).
$$

This is Shapiro's lemma for the trivial subgroup, but the contraction is worth seeing. Use
homogeneous cochains and identify a $G$-equivariant map

$$
F:G^{n+1}\longrightarrow\mathcal C(I)
$$

with the continuous function

$$
\widetilde F(g_0,\ldots,g_n,x)=F(g_0,\ldots,g_n)(x).
$$

Equivariance lets one move $x$ into the other variables. Inserting the identity in the resulting
bar variables defines a homotopy $s$ satisfying

$$
Ds+sD=1
$$

in positive degrees. In inhomogeneous language this is the familiar operation of evaluating one
variable and translating the rest. All maps remain continuous because they are obtained by
composition with multiplication, inversion, and coordinate insertion. Hence every positive
cocycle is a coboundary.

There is also an effacement interpretation. Every $A$ embeds in a coinduced module, and the
induced map on $H^n$ for $n>0$ lands in zero. Thus every positive-degree class can be killed by a
monomorphism of coefficients. This property is exactly what singles out a universal
cohomological delta functor.

### 10.4 The comparison theorem

**Theorem (cochain--derived comparison).** Let $G$ be profinite. In the category of discrete
continuous $G$-modules there are natural isomorphisms

$$
H^n(G,A)\simeq R^n\Gamma(G,A)\qquad(n\geq0).
$$

They identify the explicit connecting maps of Chapter 4 with the derived-functor connecting
maps and are compatible with coefficient morphisms.

**Proof.** The functors $H^n(G,-)$ form a cohomological delta functor: Chapter 4 supplies the
long exact sequence for every short exact sequence of discrete modules, and the construction of
the boundary is natural. Degree zero is invariants. Section 10.3 shows that this delta functor is
effaceable in every positive degree. An effaceable cohomological delta functor extending a left
exact functor is universal. The right derived functors form another universal delta functor with
the same degree-zero term. There is therefore a unique natural isomorphism between them which is
the identity in degree zero.

For a more concrete view, resolve $A$ by injectives of the form $\mathcal C(I)$ and compare that
resolution with the augmented continuous bar complex. A map in degree zero extends successively
because the injective terms have the required lifting property; any two extensions are chain
homotopic. Taking cohomology yields the same natural isomorphism. This second description also
shows directly that the two boundary maps agree: both lift a cocycle once and differentiate the
lift. $\square$

The proof strategy is economical. We did not compute an injective resolution. We proved that the
explicit theory has the two formal properties that characterize derived functors: long exact
sequences and effacement.

### 10.5 Consequences of the comparison

Several facts now acquire a common explanation.

First, a discrete module is **acyclic** when its positive continuous cohomology vanishes.
Coinduced modules are acyclic, and resolutions by them may replace injective resolutions for
computations. This is the conceptual content of dimension shifting.

Second, natural transformations constructed in degree zero and compatible with exact sequences
extend uniquely to all degrees once the relevant delta functors are universal. Explicit formulas
remain valuable: they determine signs, exhibit continuity, and describe low-degree classes. But
uniqueness often proves relations among the resulting maps without repeating a bar-complex
calculation.

We can now complete the infinite-index form of Shapiro promised in Section 9.4. For every closed
subgroup $H\leq G$, continuous coinduction is right adjoint to restriction, and evaluation at
$1$ identifies invariants:

$$
(\operatorname{Coind}_H^G A)^G\simeq A^H.
$$

Explicitly, a $G$-map $u:B\to\operatorname{Coind}_H^G A$ is sent to the $H$-map
$b\mapsto u(b)(1)$. Conversely, an $H$-map $v:B\to A$ gives

$$
u_v(b)(x)=v(xb).
$$

The orbit map of each $b$ is continuous with finite image, so $u_v(b)$ is continuous; the
$H$-equivariance and the right-translation action give respectively the coinduction relation and
$G$-equivariance. These two constructions are inverse. Taking $B=\mathbf Z$ with trivial action
gives the displayed identity on invariants.

Two exactness points deserve proof. Restriction is exact because it changes only the action.
Continuous coinduction is also exact on discrete modules. Given a surjection $B\to C$ and an
$H$-equivariant continuous function $f:G\to C$, first use local constancy of $f$ and open
stabilizers of chosen lifts of its finitely many values. For every $x\in G$, choose an open
subgroup $U_x$ such that $f$ is constant on $xU_x$ and the chosen lift of $f(x)$ is fixed by
$H\cap xU_x x^{-1}$. The sets $HxU_x$ are $H$-stable and clopen; compactness gives a finite
cover, whose Boolean refinement is a finite disjoint $H$-stable clopen partition subordinate to
these sets. On a piece contained in $HxU_x$, define the lift at $hxu$ to be $h$ times the chosen
lift at $x$. The stabilizer condition makes this independent of the presentation $hxu$, and the
finite clopen partition makes the resulting lift continuous. Thus
$\operatorname{Coind}_H^G B\to\operatorname{Coind}_H^G C$ is surjective.

Because restriction is exact, its right adjoint carries injective $H$-modules to injective
$G$-modules. Because coinduction is exact, applying it to an injective resolution
$A\to I^\bullet$ gives an injective resolution of $\operatorname{Coind}_H^G A$. Termwise
evaluation identifies the two invariant complexes:

$$
\bigl(\operatorname{Coind}_H^G I^\bullet\bigr)^G=(I^\bullet)^H.
$$

Taking cohomology and using the comparison theorem gives the full statement

$$
H^n(G,\operatorname{Coind}_H^G A)\simeq H^n(H,A)
$$

for every closed $H$, and the isomorphism is induced by evaluation. For open $H$ it therefore
agrees with the explicit map of Chapter 9 by uniqueness of the derived extension of the
degree-zero map.

Third, the comparison identifies Yoneda extension groups with continuous cohomology. In
particular, $H^1(G,A)$ may be read as equivalence classes of extensions of the trivial module
$\mathbf Z$ by $A$ in the discrete $G$-module category, while $H^2$ records two-fold extensions.
This is compatible with, but not identical in presentation to, the topological group extensions
of Chapter 3. One statement lives in an abelian category of modules; the other concerns group
laws and factor sets.

Finally, the comparison explains the finite-quotient formula of Chapter 8 at a structural level.
Discrete continuous modules are assembled from data fixed by open normal subgroups, and filtered
colimits are exact. Nevertheless, the cochain proof remains essential because it gives the exact
formula $A^U$ and shows why no one quotient need compute every class.

### 10.6 What the theorem does not say

If $M$ is profinite, locally compact, or an $\ell$-adic vector space, the group
$H^n_{\mathrm{cts}}(G,M)$ may still be defined as the cohomology of continuous cochains. The
comparison theorem does **not** identify it with derived invariants in some unspecified category
of topological modules. One must first choose an exact category and prove that it has suitable
acyclic objects. In this book we instead control such coefficients directly: profinite modules
through towers of finite quotients, and $\ell$-adic vector spaces through stable lattices and
boundedness on compact domains. This keeps every exactness claim attached to a verifiable lifting
hypothesis.

## 11. Cyclic and procyclic calculations

### 11.1 Why cyclic groups are the local model

Cyclic quotients are the first nontrivial test of every convention. Their cohomology is explicit, periodic, and sensitive to both invariants and norms. Procyclic groups then show how continuity can destroy that finite periodicity in the limit. These calculations provide a diagnostic toolkit: many restriction, inflation, and obstruction questions reduce to recognizing a norm or a difference operator.

Let $C_m=\langle\sigma\rangle$ be cyclic of order $m$, acting on an abelian group $A$. Define

$$
D=\sigma-1,\qquad N=1+\sigma+\cdots+\sigma^{m-1}.
$$

Then $DN=ND=0$. Thus the alternating complex

$$
A\xrightarrow{D}A\xrightarrow{N}A\xrightarrow{D}A\xrightarrow{N}\cdots
$$

is a cochain complex.

### 11.2 The periodic resolution

The standard free resolution of the trivial $\mathbf Z[C_m]$-module $\mathbf Z$ is

$$
\cdots\xrightarrow{N}\mathbf Z[C_m]\xrightarrow{\sigma-1}
\mathbf Z[C_m]\xrightarrow{N}\mathbf Z[C_m]
\xrightarrow{\sigma-1}\mathbf Z[C_m]\longrightarrow\mathbf Z\to0.
$$

Exactness can be checked directly. An element $\sum a_i\sigma^i$ lies in the augmentation kernel exactly when the coefficients have sum zero, and then it is $(\sigma-1)$ times an element obtained from partial sums. The kernel of multiplication by $\sigma-1$ consists of constant coefficient vectors, exactly the image of $N$. Finally $N(\sum a_i\sigma^i)=(\sum a_i)N$, so its kernel is the augmentation ideal.

Applying $\operatorname{Hom}_{C_m}(-,A)$ identifies every term with $A$ and reverses the arrows into the displayed alternating cochain complex. Hence

$$
H^0(C_m,A)=A^{C_m}=\ker D,
$$

$$
H^{2r+1}(C_m,A)=\frac{\ker N}{DA}\qquad(r\geq0),
$$

and

$$
H^{2r}(C_m,A)=\frac{A^{C_m}}{NA}\qquad(r\geq1).
$$

The exception in degree zero matters: $H^0$ is $A^{C_m}$, not $A^{C_m}/NA$.

### 11.3 Recovering the degree-one formula directly

A crossed homomorphism $f:C_m\to A$ is determined by $a=f(\sigma)$. Repeated use of the cocycle equation gives

$$
f(\sigma^j)=(1+\sigma+\cdots+\sigma^{j-1})a.
$$

The relation $\sigma^m=1$ requires $Na=0$. A coboundary has $f(\sigma)=(\sigma-1)b=Db$. This proves

$$
H^1(C_m,A)=\ker N/DA
$$

without a resolution and illustrates how group relations become cocycle equations.

For degree two, an extension of $C_m$ by $A$ can be described by a lift $t$ of $\sigma$. Conjugation by $t$ gives the prescribed action, while $t^m\in A^{C_m}$. Replacing $t$ by $at$ changes $t^m$ by $Na$. Therefore extension classes are $A^{C_m}/NA$, matching the cohomology formula.

### 11.4 Trivial action and concrete examples

If the action is trivial, $D=0$ and $N=m$. Thus

$$
H^{2r+1}(C_m,A)=A[m],\qquad
H^{2r}(C_m,A)=A/mA\quad(r\geq1).
$$

For $A=\mathbf Z$ this gives $H^{2r+1}=0$ and $H^{2r}=\mathbf Z/m\mathbf Z$. For $A=\mathbf Q/\mathbf Z$, multiplication by $m$ is surjective, so positive even cohomology vanishes, while odd cohomology is the cyclic group of elements killed by $m$.

If multiplication by $m$ is invertible on $A$, every positive-degree group vanishes. One can see this either in the formulas or by averaging. This includes $C_m$ acting on a vector space over a field whose characteristic does not divide $m$, even for nontrivial action.

In characteristic dividing $m$, invariants can fail dramatically to be exact. For $C_p$ acting trivially on $\mathbf F_p$, both $D$ and $N$ vanish, so

$$
H^n(C_p,\mathbf F_p)\simeq\mathbf F_p
$$

in every degree. Finite cyclic groups therefore have infinite cohomological dimension at primes dividing their order.

### 11.5 A nontrivial action

Let $C_2$ act on $A=\mathbf Z$ by $\sigma a=-a$. Then $N=1+\sigma=0$ and $D=-2$. Hence

$$
H^{2r+1}(C_2,\mathbf Z_{\mathrm{sign}})=\mathbf Z/2\mathbf Z,\qquad
H^{2r}(C_2,\mathbf Z_{\mathrm{sign}})=0\quad(r\geq1),
$$

because the only invariants in $\mathbf Z$ are zero. This example shows that odd and even behavior can exchange when the action changes; formulas depending only on the abstract coefficient group cannot be correct.

### 11.6 The procyclic group $\widehat{\mathbf Z}$

Let $\Gamma=\widehat{\mathbf Z}$ with a chosen topological generator $\sigma$. For a discrete torsion $\Gamma$-module $A$, continuous cohomology is concentrated in degrees zero and one:

$$
H^0(\Gamma,A)=\ker(\sigma-1),\qquad
H^1(\Gamma,A)=A/(\sigma-1)A,
$$

$$
H^n(\Gamma,A)=0\qquad(n\geq2).
$$

The torsion hypothesis in the $H^1$ formula is essential. With trivial action on a discrete torsion module, an element $a$ of order $m$ defines a continuous homomorphism $\widehat{\mathbf Z}\to A$ by sending $1$ to $a$; it factors through $\mathbf Z/m\mathbf Z$. Thus every element contributes. With $A=\mathbf Z$ discrete and trivial, however, every continuous homomorphism from compact $\widehat{\mathbf Z}$ has finite image and is zero, whereas $A/(\sigma-1)A=\mathbf Z$. The naive formula fails.

To prove the torsion statement, use the finite-quotient theorem. Each element and each cochain is
visible in some cyclic quotient. The transition maps can be read directly from the periodic
complex, which removes any ambiguity about higher degrees. Suppose the action on the coefficient
elements under consideration factors through $C_m$, and inflate along
$C_{mr}\twoheadrightarrow C_m$, sending the chosen generator upstairs to the chosen generator
downstairs. The two periodic complexes have the same operator $D=\sigma-1$, while

$$
N_{mr}=rN_m.
$$

A comparison map is multiplication by $r^j$ in degrees $2j$ and $2j+1$. Indeed, across a
$D$-arrow both adjacent multipliers are $r^j$, and across an $N$-arrow the extra factor $r$ is
exactly the identity $N_{mr}=rN_m$. In degree zero and one the comparison is the identity; in
every degree at least two it contains a positive power of $r$. This comparison induces the
inflation map because it is the identity in degree zero and is compatible with the augmentations.
Since every coefficient element is torsion, choosing $r$ divisible by the orders of the finitely
many representatives kills every class in degree at least two after one refinement. Thus the
filtered colimit vanishes in those degrees. Degree-one classes stabilize to the cokernel of
$\sigma-1$: the finite-order condition needed to close a cocycle is achieved in some quotient.
Hence the direct limit of finite cyclic cohomology has the asserted form.

The degree-one assertion can be checked without taking the direct limit on faith. Given $a\in A$,
the orbit of $a$ under $\sigma$ is finite, so $\sigma^r a=a$ for some $r$. The partial norm

$$
N_r a=a+\sigma a+\cdots+\sigma^{r-1}a
$$

is torsion; choose $t$ with $tN_ra=0$. Then $N_{rt}a=0$, and the cyclic calculation produces a
cocycle on $C_{rt}$ sending its generator to $a$. Inflation gives a continuous cocycle on
$\widehat{\mathbf Z}$. Two choices $a,a'$ define the same class exactly when
$a-a'=(\sigma-1)b$, by the degree-one coboundary formula. This proves the cokernel description.

For higher degree, the comparison just computed is the decisive point: inflation to
$C_{mr}$ multiplies a degree-$n$ representative by $r^{\lfloor n/2\rfloor}$. A refinement with
$r$ divisible by its order therefore kills it when $n\geq2$. What matters is not that any one
finite cyclic group has small cohomology—it does not—but that no positive-degree periodic class
above degree one survives all refinements.

This is a striking continuity effect. Every finite cyclic quotient has periodic higher cohomology, but those classes do not persist coherently through all refinements.

### 11.7 The group $\mathbf Z_\ell$

Let $\Gamma=\mathbf Z_\ell$ and choose a topological generator $\gamma$. For a discrete $\ell$-primary torsion module $A$,

$$
H^0(\Gamma,A)=\ker(\gamma-1),\qquad
H^1(\Gamma,A)=A/(\gamma-1)A,\qquad
H^n(\Gamma,A)=0\ (n\geq2).
$$

If $A$ is discrete torsion of order prime to $\ell$, then all positive cohomology vanishes. Indeed every finite stage is an $\ell$-group acting on a module on which its order is invertible, so averaging applies.

For trivial $A=\mathbf Q_\ell/\mathbf Z_\ell$, one obtains

$$
H^1(\mathbf Z_\ell,\mathbf Q_\ell/\mathbf Z_\ell)
\simeq\mathbf Q_\ell/\mathbf Z_\ell.
$$

For trivial finite $A=\mathbf Z/\ell^r\mathbf Z$, the same calculation gives $H^1\simeq A$. These classes are precisely the continuous homomorphisms, each factoring through a finite quotient of $\mathbf Z_\ell$.

### 11.8 Finite quotient calculations as consistency checks

The cyclic formulas interact cleanly with restriction and corestriction. If $C_d\leq C_m$ has index $e$, restriction sends a homomorphism to its value on $\sigma^e$, while corestriction is a norm over $e$ cosets. Their composite on $H^n(C_m,A)$ is multiplication by $e$, as the general theorem predicts.

Inflation from $C_m$ to a cyclic extension quotient can annihilate an even class, which is precisely why inflation in degree two is not always injective. The five-term sequence identifies the lost class as a transgression from a character of the kernel. Thus the abstract functorial statements of Chapters 5 and 6 can be tested, including their directions and indices, in this explicit periodic complex.

### 11.9 Worked extension classes for $C_m$

Take trivial coefficients $A=\mathbf Z/m\mathbf Z$. For each $a\in A$, define a group $E_a$ generated by a central copy of $A$ and an element $t$, subject to

$$
t^m=a.
$$

The quotient sending $t$ to $\sigma$ is an extension of $C_m$ by $A$. Replacing $t$ by $b+t$ in additive notation replaces $t^m$ by $a+mb=a$, so distinct $a$ give distinct extension classes. This realizes

$$
H^2(C_m,A)=A/mA=A.
$$

For $a=0$, the lift $t$ has order dividing $m$ and the extension splits. For $a=1$, $t$ has order $m^2$ when $A$ is cyclic with its chosen generator, giving the nonsplit extension

$$
0\to C_m\to C_{m^2}\to C_m\to0.
$$

The factor set can be seen without a presentation. Represent elements of $C_m$ by integers $0,\ldots,m-1$ and set

$$
c(i,j)=
\begin{cases}
0,&i+j<m,\\
a,&i+j\geq m.
\end{cases}
$$

It records the carry in addition modulo $m$. The cocycle equation says that the total number of carries in adding three integers is independent of parenthesization. This concrete model makes the associativity origin of $2$-cocycles literal.

Now let $A$ be any trivial module and let $x,y\in H^1(C_m,A)$ arise from homomorphisms. Their cup is represented by

$$
(g,h)\longmapsto\mu(x(g),y(h)).
$$

When the coefficient characteristic is odd, graded commutativity forces $x\smile x=0$. In characteristic two, the square may be the nonzero periodic class. This is a useful warning that a missing sign can change an actual extension class, not merely its notation.

## 12. Topological and $\ell$-adic coefficients

### 12.1 A separate coefficient theory

Discrete modules are appropriate for finite modules and groups such as $\mathbf Q_\ell/\mathbf Z_\ell$. Lattices such as $\mathbf Z_\ell^d$ and vector spaces such as $\mathbf Q_\ell^d$ are not discrete in their natural topology. Declaring them discrete would impose the wrong continuity condition: a continuous action on a finitely generated discrete module must have finite image, while an $\ell$-adic representation usually has infinite compact image.

A **topological $G$-module** is a Hausdorff topological abelian group $M$ with a jointly continuous action $G\times M\to M$. Define

$$
C^n_{\mathrm{cts}}(G,M)=\operatorname{Map}_{\mathrm{cts}}(G^n,M)
$$

with the same differential, and call its cohomology $H^n_{\mathrm{cts}}(G,M)$. The calculation $d^2=0$ remains valid. What changes is exactness: continuous surjections need not permit continuous cochain lifts, and images need not be closed. Results from the discrete theory survive only under stated lifting or inverse-limit hypotheses.

### 12.2 Four coefficient regimes

It is useful to keep four regimes distinct.

1. A **finite module** has the discrete topology, equivalently its compact topology. Its action factors through a finite quotient.

2. A **discrete torsion module** may be infinite. Every element and cochain is finite-level, but no common finite quotient need control the whole module.

3. A **profinite module** is an inverse limit of finite discrete modules with compatible continuous action. Its elements can contain infinitely much information.

4. An **$\ell$-adic module** is typically a finite free $\mathbf Z_\ell$-module $T$, a finite-dimensional $\mathbf Q_\ell$-space $V$, or $V/T$. Here $T$ is profinite, $V$ is locally compact, and $V/T$ is discrete torsion.

The same algebraic group can yield different cohomology with different topologies. Continuous homomorphisms $\mathbf Z_\ell\to\mathbf Z_\ell$ include all scalar multiplications when the target is profinite, but are zero when it is discrete. Topology is part of the coefficient object.

### 12.3 Profinite modules and the Milnor sequence

Suppose

$$
T\simeq\varprojlim_rT_r
$$

as a topological $G$-module, where $T_r$ is finite discrete and transitions are surjective. A map to $T$ is continuous exactly when all maps to $T_r$ are, so

$$
C^n_{\mathrm{cts}}(G,T)\simeq\varprojlim_r C^n(G,T_r).
$$

The isomorphism of cochain groups uses both compactness and surjectivity. A compatible family of
maps $f_r:G^n\to T_r$ gives a map to the inverse limit by its universal property, and continuity
can be tested on the finite coordinates. Conversely, projection gives the family. Moreover, if
$T_{r+1}\to T_r$ is surjective, then

$$
C^n(G,T_{r+1})\longrightarrow C^n(G,T_r)
$$

is surjective: the lower-level cochain has finite image, so choose one lift of each value. The
resulting lift is locally constant and therefore continuous. Notice how special this is to a
finite discrete target at each level.

Inverse limits are only left exact. For a countable tower there is a natural Milnor exact sequence

$$
0\longrightarrow\varprojlim{}^1_rH^{n-1}(G,T_r)
\longrightarrow H^n_{\mathrm{cts}}(G,T)
\longrightarrow\varprojlim_rH^n(G,T_r)
\longrightarrow0.
$$

To see its origin, let $u_r:T_{r+1}\to T_r$ be the transition. On a product of complexes define

$$
\Delta((c_r)_r)=(c_r-u_r(c_{r+1}))_r.
$$

Degreewise surjectivity of the cochain transitions lets one solve recursively for a preimage under
$\Delta$, and hence gives a short exact sequence of complexes

$$
0\longrightarrow\varprojlim_r C^\bullet(G,T_r)
\longrightarrow\prod_r C^\bullet(G,T_r)
\xrightarrow{\Delta}\prod_r C^\bullet(G,T_r)
\longrightarrow0.
$$

The associated long exact sequence breaks into the displayed short exact sequences. In this
countable setting, $\varprojlim^1$ is concretely the cokernel of the analogous map $\Delta$ on
$\prod_rH^{n-1}(G,T_r)$. This description also proves naturality.

The $\varprojlim^1$ term measures the failure to choose compatible cocycle representatives. It
vanishes when the system $H^{n-1}(G,T_r)$ is Mittag--Leffler: for every $r$, the images in the
$r$th group from all sufficiently high levels must stabilize. This holds, for example, when the
$H^{n-1}(G,T_r)$ are finite. Only then may one conclude

$$
H^n_{\mathrm{cts}}(G,T)\simeq\varprojlim_rH^n(G,T_r).
$$

The condition is substantive. For the abstract tower

$$
\mathbf Z\xleftarrow{\times\ell}\mathbf Z
\xleftarrow{\times\ell}\mathbf Z\xleftarrow{\times\ell}\cdots,
$$

the images in the first term form the strictly decreasing chain
$\ell^r\mathbf Z$, so the system is not Mittag--Leffler and its $\varprojlim^1$ is nonzero. This
tower is not itself the usual tower of finite quotients of a lattice; it is a warning that
inverse limits do not commute with cohomology for purely formal reasons. In applications one
must point to finiteness, surjectivity on cohomology, stabilization of images, or another actual
argument that kills the derived limit.

### 12.4 $\ell$-adic lattices and vector spaces

Let $T$ be finite free over $\mathbf Z_\ell$ with continuous action. Then

$$
T\simeq\varprojlim_rT/\ell^rT,
$$

so the Milnor sequence applies. Under suitable finiteness, its cohomology is the inverse limit of finite-level cohomology.

Now put $V=T\otimes_{\mathbf Z_\ell}\mathbf Q_\ell$ and give it its natural $\ell$-adic topology.
There is a clean scalar-extension theorem which needs no cohomological finiteness assumption.

**Proposition (inverting $\ell$).** For every $n\geq0$,

$$
H^n_{\mathrm{cts}}(G,V)
\simeq H^n_{\mathrm{cts}}(G,T)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

**Proof.** A continuous map from compact $G^n$ to $V$ has compact, hence bounded, image. It is
therefore contained in $\ell^{-r}T$ for some $r$. Consequently

$$
C^n_{\mathrm{cts}}(G,V)
=\varinjlim_r C^n_{\mathrm{cts}}(G,\ell^{-r}T)
=C^n_{\mathrm{cts}}(G,T)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

Filtered colimits of abelian groups are exact, so taking cohomology commutes with this colimit.
$\square$

The stable-lattice hypothesis is decisive. It lets all bounded images be compared inside one
coherent tower. Without a $G$-stable lattice, the displayed argument has no starting object.

The coefficient sequence

$$
0\longrightarrow T\longrightarrow V=T\otimes_{\mathbf Z_\ell}\mathbf Q_\ell
\longrightarrow V/T\longrightarrow0
$$

mixes topological regimes, but in this particular case it is cochainwise exact. The quotient
$V/T$ is discrete. A continuous map $G^n\to V/T$ has finite image; choose a lift in $V$ of each
value. The resulting locally constant map is continuous. Hence there is a long exact sequence

$$
\cdots\to H^n_{\mathrm{cts}}(G,T)\to H^n_{\mathrm{cts}}(G,V)\to H^n(G,V/T)
\xrightarrow{\delta}H^{n+1}_{\mathrm{cts}}(G,T)\to\cdots.
$$

This useful success should not be generalized from algebraic exactness alone.

For a short exact sequence of profinite modules, a continuous section of the quotient map makes
the cochain sequence exact and recovers Chapter 4. Alternatively, use compatible levelwise exact
sequences and then pass to limits, retaining any $\varprojlim^1$ terms. Levelwise lifting does not
by itself produce one compatible lift through the whole inverse system.

### 12.5 Products and matrix actions

A continuous equivariant pairing of topological modules defines cup products by the same formula, with the same Leibniz sign and associativity. For profinite modules the pairing may factor through a completed tensor product. Products can be checked at finite levels, but perfectness or nondegeneracy requires additional finiteness and never follows merely from the formula.

Choosing a basis of finite free $T$ identifies its action with

$$
\rho:G\longrightarrow\operatorname{GL}_d(\mathbf Z_\ell).
$$

Continuity is equivalent to continuity of every finite reduction. Each reduction has open kernel, though their intersection need not be open; this permits infinite $\ell$-adic image. The module $\operatorname{End}(T)$ carries conjugation action $gX=\rho(g)X\rho(g)^{-1}$, whose cohomology will appear in the final toolkit.

### 12.6 A procyclic comparison across topologies

Let $G=\mathbf Z_\ell$ act trivially. With finite coefficients $A_r=\mathbf Z/\ell^r\mathbf Z$,

$$
H^1(G,A_r)=\operatorname{Hom}_{\mathrm{cts}}(G,A_r)\simeq A_r,
$$

and $H^2(G,A_r)=0$. The transition maps on $H^1$ are surjective. Therefore the Milnor sequence gives

$$
H^1_{\mathrm{cts}}(G,\mathbf Z_\ell)
\simeq\varprojlim_rA_r\simeq\mathbf Z_\ell,
\qquad
H^2_{\mathrm{cts}}(G,\mathbf Z_\ell)=0.
$$

Directly, the first group consists of continuous endomorphisms of the additive group $\mathbf Z_\ell$, each given by multiplication by an $\ell$-adic integer. By contrast, if the same abstract coefficient group is declared discrete, every continuous homomorphism from compact $G$ has finite image and must be zero. Thus

$$
H^1(G,(\mathbf Z_\ell)_{\mathrm{discrete}})=0.
$$

For $V=\mathbf Q_\ell$ with its natural topology, continuous homomorphisms
$\mathbf Z_\ell\to\mathbf Q_\ell$ are again determined by the image of $1$, but that image can
be any element of $\mathbf Q_\ell$. Hence
$H^1_{\mathrm{cts}}(G,V)\simeq\mathbf Q_\ell$. These three answers—finite level, profinite
lattice, and vector space—fit together only because their topologies were kept explicit.

### 12.6A The strict procyclic lattice complex

The preceding calculations determine groups.  Nearby-cycle calculations also need a functorial
complex, including the action of an element which conjugates a procyclic generator.  The finite
cyclic periodic resolution is the wrong complex when the cyclic quotient has $\ell$-power
order: its higher terms disappear only after passage to the torsion-free procyclic group.

Let $\Lambda$ be the integers in a finite extension of $\mathbf Q_\ell$, let
$\Gamma\simeq\mathbf Z_\ell$ have topological generator $\gamma$, and let $M$ be a finite free
$\Lambda$-module with continuous $\Gamma$-action.  Write $T$ for the action of $\gamma$.

**Proposition 12.1 (strict procyclic complex).** In the continuous derived category of compact
$\Lambda$-modules there is a functorial model

$$
R\Gamma_{\rm cts}(\Gamma,M)
\simeq
K_\Gamma(M):=[M\xrightarrow{\ T-1\ }M],                 \tag{12.18}
$$

with the terms in degrees zero and one.  In particular,

$$
H^0=\ker(T-1),\qquad H^1=\operatorname{coker}(T-1),
\qquad H^i=0\quad(i\ge2).                                \tag{12.19}
$$

The terms of (12.18), rather than its cohomology, are finite free.  Thus (12.18) remains a
perfect complex when $T-1$ has nonprimitive image and $H^1$ has $\ell$-torsion.

**Proof.** The completed group algebra is

$$
\Lambda[[\Gamma]]\simeq\Lambda[[X]],\qquad \gamma\longmapsto1+X.
$$

The augmentation has the length-one topologically free resolution

$$
0\longrightarrow\Lambda[[\Gamma]]
\xrightarrow{\ \gamma-1\ }\Lambda[[\Gamma]]
\longrightarrow\Lambda\longrightarrow0.                 \tag{12.20}
$$

Indeed, under the displayed power-series identification the first map is multiplication by
$X$, which is injective, and its cokernel is evaluation at $X=0$.  A rank-one topologically
free compact $\Lambda[[\Gamma]]$-module is projective for continuous equivariant Hom: a module
map out of it is determined by the image of $1$, and that image lifts across a continuous
surjection.  The resulting module map is continuous by the universal property of the
completed group algebra.  Applying
$\operatorname{Hom}^{\rm cts}_{\Lambda[[\Gamma]]}(-,M)$ to (12.20) gives (12.18).  This also
shows functoriality and proves (12.19). $\square$

There is an equally important semidirect-product formula.  For $a\in\mathbf Z_\ell^\times$ put

$$
[a]_T=\frac{T^a-1}{T-1}
=\sum_{n\ge1}\binom an(T-1)^{n-1},                        \tag{12.21}
$$

where the right side is evaluated continuously in the completed group algebra.  Let $A$ be a
$\Lambda$-linear automorphism of $M$ satisfying

$$
ATA^{-1}=T^a.                                               \tag{12.22}
$$

The series in (12.21) converges because continuity of the $\mathbf Z_\ell$-action makes
$T-1$ topologically nilpotent: some power of $T-1$ lies in
$\ell\operatorname{End}_\Lambda(M)$.

Then the automorphism which acts by $A$ in degree zero and by

$$
A[a^{-1}]_T                                                \tag{12.23}
$$

in degree one is a chain automorphism of (12.18).  The check is the exact identity

$$
A[a^{-1}]_T(T-1)=A(T^{a^{-1}}-1)=(T-1)A.                  \tag{12.24}
$$

This is the continuous-cochain conjugation action, not an optional normalization.  If $T=1$,
the degree-one factor is $a^{-1}A$.  Thus an arithmetic Frobenius satisfying
$\phi\gamma\phi^{-1}=\gamma^q$ acts on the degree-one constant-coefficient term by $q^{-1}$,
as required for a $(-1)$ Tate twist; geometric Frobenius acts by $q$.

The same model fixes the relevant chain maps, but one must distinguish the pro-$\ell$ group
from a full tame covering degree. If a homomorphism sends a source generator to the $e$th
power of a target generator, restriction is the chain map

$$
K(T)\longrightarrow K(T^e),\qquad
(f^0,f^1)=(1,[e]_T),                                      \tag{12.25}
$$

and the adjoint norm chain map is

$$
K(T^e)\longrightarrow K(T),\qquad
(c^0,c^1)=([e]_T,1).                                      \tag{12.26}
$$

Both assertions follow from $(T^e-1)=[e]_T(T-1)$. When $e$ is a power of $\ell$ and the
source is identified with the index-$e$ subgroup $e\Gamma$, these are the usual restriction
and corestriction maps. For a general integer $e$, (12.26) is still the displayed adjoint norm,
but it is not corestriction for the pro-$\ell$ group alone: multiplication by the
prime-to-$\ell$ part of $e$ is an automorphism of $\mathbf Z_\ell$. The two maps are adjoint under the evaluation pairing
with the contragredient module after the canonical orientation identification of the dual
strict complex; this is not termwise matrix transposition.  For expansion index one every entry in (12.25)--(12.26) is
literally $1$.  Reversing the chosen generator replaces $T$ by $T^{-1}$; the resulting chain
isomorphism is the identity in degree zero and $-T^{-1}$ in degree one, which is the origin of
the orientation sign.

Finally, if a tame procyclic group has a closed prime-to-$\ell$ kernel $H$ and maximal
pro-$\ell$ quotient $\Gamma$, take $H$-invariants first.  Every finite quotient of $H$ has unit
order in $\Lambda$, so averaging is compatible through the inverse system and invariants are
exact.  Consequently the full tame complex is (12.18) with $M$ replaced by the finite-free
direct summand $M^H$.  This reduction does not average over an additional flag or stabilizer
group whose order may be divisible by $\ell$.

Under a finite map of full tame groups, however, the source invariant summand can be larger:
writing $eH$ for the image of $H$ under multiplication by $e$, it is $M^{eH}$ rather than necessarily
$M^H$. Restriction and transfer must then be inserted between these two summands before using
the procyclic complexes. For instance, away from residue characteristics two and three, a
rank-one order-two tame character over $\mathbf Z_3$ has $M^H=0$, while its degree-two
pullback is trivial and has $M^{2H}=M$. Thus
(12.25)--(12.26) give the full annular pull--trace formulas on one common module only when the
prime-to-$\ell$ invariant summand is unchanged; expansion index one is always in this range.

### 12.7 Exact sequences in the topological setting

The right hypothesis for a cochain long exact sequence can be stated without ambiguity. Call a
short exact sequence of Hausdorff topological $G$-modules

$$
0\longrightarrow M'\longrightarrow M\xrightarrow{q}M''\longrightarrow0
$$

**$G$-cochain-exact** if $M'$ has the subspace topology under its identification with
$\ker(q)$ and, for every $n\geq0$, every continuous map $G^n\to M''$ has a continuous lift to
$M$. Then

$$
0\longrightarrow C^n_{\mathrm{cts}}(G,M')\longrightarrow C^n_{\mathrm{cts}}(G,M)
\longrightarrow C^n_{\mathrm{cts}}(G,M'')\longrightarrow0
$$

is exact, and the proof of Chapter 4 gives a natural long exact sequence. It is enough that $q$
have a continuous global section as a map of spaces; the section need not be additive or
$G$-equivariant. It is also enough to verify the lifting property directly on the particular
compact spaces $G^n$.

Two common cases deserve to be separated.

* For discrete modules, cochain-exactness is automatic because every cochain has finite image and
  a lift may be chosen value by value.

* For $0\to T\to V\to V/T\to0$ as above, it is automatic because the quotient is discrete and
  maps from $G^n$ again have finite image.

By contrast, a continuous surjection of compact modules need not be assumed to possess a
continuous section. Algebraic exactness and compactness alone do not prove cochain-exactness.
When no lifting theorem is available, the safe method is to resolve the modules by compatible
finite quotients and retain the derived-limit terms.

The connecting map under cochain-exactness has exactly the familiar formula. Lift a cocycle
$c$ to a continuous cochain $b$; then $db$ takes values in $M'$ and represents $\delta[c]$. Thus
the obstruction interpretation survives unchanged once the topological lifting step has been
justified.

### 12.8 Algebraic groups and their possible quotient topologies

The notation $H^n_{\mathrm{cts}}(G,M)$ in this book denotes an abelian group. The cochain groups
carry natural topologies—uniform convergence when $M$ is a topological group—but the subgroup of
coboundaries need not be closed inside the cocycles. The quotient topology on cohomology can
therefore fail to be Hausdorff. No algebraic exact sequence above asserts closedness, strictness,
or topological exactness of the maps on cohomology.

This distinction matters in families. Suppose a sequence of coboundaries converges to a cocycle
which is not itself a coboundary. Algebraically the limiting class is nonzero, even though its
image lies in the closure of zero for the quotient topology. Finiteness hypotheses often prevent
this phenomenon—for example, a finite cohomology group has only the discrete Hausdorff topology—
but finiteness must be proved in the arithmetic setting where it is used.

There are thus three different operations that should never be denoted by the same unqualified
limit:

$$
\varinjlim_U H^n(G/U,A^U)
$$

for discrete coefficients,

$$
\varprojlim_r H^n(G,T_r)
$$

for a profinite tower when the $\varprojlim^1$ term vanishes, and

$$
H^n_{\mathrm{cts}}(G,T)\otimes\mathbf Q_\ell
$$

for passage from a stable lattice to its vector space. The first uses exact filtered colimits,
the second may carry a derived-limit correction, and the third uses boundedness of continuous
maps on compact domains.

## 13. Cohomological dimension and the normal-subgroup spectral sequence

### 13.1 Measuring the height of obstructions

For a prime $p$, the **$p$-cohomological dimension** $\operatorname{cd}_p(G)$ is the least $d$ such that

$$
H^n(G,A)=0
$$

for every discrete $p$-primary torsion $G$-module $A$ and every $n>d$. If none exists, it is infinite. The torsion cohomological dimension is the supremum over $p$. This definition keeps $\ell$-adic derived-limit issues separate.

### 13.2 Examples and torsion

The trivial group has dimension zero. More generally, $\operatorname{cd}_p(G)=0$ exactly when invariants are exact on discrete $p$-primary modules; equivalently, finite quotients of $G$ have order prime to $p$.

A nontrivial finite $p$-group has infinite $p$-cohomological dimension, as periodic cyclic cohomology with $\mathbf F_p$ coefficients already suggests. More generally, an element of order $p$ forces $\operatorname{cd}_p(G)=\infty$. Thus $p$-torsion-freeness is necessary for finite $p$-dimension.

Chapter 11 gives

$$
\operatorname{cd}_p(\widehat{\mathbf Z})=1,
\qquad \operatorname{cd}_\ell(\mathbf Z_\ell)=1,
\qquad \operatorname{cd}_p(\mathbf Z_\ell)=0\ (p\ne\ell).
$$

### 13.3 Dimension shifting

Embed a discrete $G$-module $A$ into

$$
I(A)=\operatorname{Map}_{\mathrm{cts}}(G,A)
$$

by sending $a$ to $g\mapsto ga$, and let $Q(A)=I(A)/A$. Since coinduced modules are acyclic, the long exact sequence gives

$$
H^{n+1}(G,A)\simeq H^n(G,Q(A))\qquad(n\geq1).
$$

This **dimension shifting** turns a high-degree obstruction into a lower-degree one with changed coefficients. It shows that sufficiently uniform vanishing in one degree propagates upward.

### 13.4 The Hochschild--Serre spectral sequence

The five-term sequence of Chapter 6 is the visible edge of a larger mechanism. Let

$$
1\longrightarrow N\longrightarrow G\longrightarrow Q\longrightarrow1
$$

be an exact sequence of profinite groups, with $N$ closed and normal, and let $A$ be a discrete
continuous $G$-module. Then there is a first-quadrant spectral sequence

$$
E_2^{i,j}=H^i\bigl(Q,H^j(N,A)\bigr)
\Longrightarrow H^{i+j}(G,A).
$$

The $Q$-module structure on $H^j(N,A)$ is the conjugation action from Section 6.1. It is a
discrete continuous action. To see continuity, represent a class by a continuous cocycle. That
cocycle and every cochain involved in comparing it with its conjugates are controlled by finite
data, so an open subgroup of $G$ fixes its class; the stabilizer in $Q$ is therefore open.

Here **convergence** has a precise elementary meaning. For each $n$, $H^n(G,A)$ has a finite
decreasing filtration

$$
H^n(G,A)=F^0\supseteq F^1\supseteq\cdots\supseteq F^{n+1}=0
$$

whose successive quotients are $E_\infty^{i,n-i}$. Because the spectral sequence lies in the
first quadrant, only finitely many terms contribute to a fixed total degree; no completeness or
conditional-convergence issue occurs.

The construction uses the composite of left exact functors

$$
A\longmapsto A^N\longmapsto (A^N)^Q=A^G.
$$

Here are the hypotheses behind the composite-functor argument. The inflation functor from
discrete $Q$-modules to discrete $G$-modules is exact and is left adjoint to $N$-invariants.
Consequently $N$-invariants carry injective $G$-modules to injective, hence acyclic,
$Q$-modules. Resolve $A$ by injective discrete $G$-modules, apply $N$-invariants, and then resolve
the resulting complex for $Q$-invariants. The first filtration computes $H^j(N,A)$ and then
$H^i(Q,-)$, giving

$$
E_2^{i,j}=H^i(Q,H^j(N,A)).
$$

The other filtration computes the derived functors of the composite, which are $H^{i+j}(G,A)$
by Chapter 10. This proves both the asserted page and its abutment using the ordinary spectral
sequence of a first-quadrant double complex. Equivalently, one may filter homogeneous cochains
by quotient directions; the horizontal differential computes $Q$-cohomology and the vertical
differential computes $N$-cohomology. The total differential uses $d_h+(-1)^i d_v$, so its two
parts anticommute and fix the sign of transgression.

### 13.5 Edges, differentials, and low degrees

The two edge maps are familiar. Along the bottom row,

$$
H^i(Q,A^N)=E_2^{i,0}\longrightarrow H^i(G,A)
$$

is inflation. Along the left column, the map from $H^j(G,A)$ to
$E_2^{0,j}=H^j(N,A)^Q$ is restriction. The first potentially nonzero differential leaving the
left column is

$$
d_2^{0,1}:H^1(N,A)^Q\longrightarrow H^2(Q,A^N),
$$

and it is exactly the transgression of Chapter 6, with the same sign convention once the
inhomogeneous differential is fixed.

Reading the filtration in total degrees one and two gives

$$
\begin{aligned}
0\to H^1(Q,A^N)&\xrightarrow{\inf}H^1(G,A)
\xrightarrow{\res}H^1(N,A)^Q\\
&\xrightarrow{d_2}H^2(Q,A^N)
\xrightarrow{\inf}H^2(G,A).
\end{aligned}
$$

Thus the earlier five-term theorem is not an isolated calculation. Let

$$
H^2(G,A)_1=
\ker\bigl(H^2(G,A)\xrightarrow{\operatorname{res}}H^2(N,A)\bigr).
$$

The next part of the edge sequence continues precisely as

$$
H^2(G,A)_1\longrightarrow H^1\bigl(Q,H^1(N,A)\bigr)
\longrightarrow H^3(Q,A^N),
$$

together with the preceding five terms, with the last inflation map viewed as landing in
$H^2(G,A)_1$. The kernel is essential: a general class in
$H^2(G,A)$ can restrict nontrivially to $H^2(N,A)^Q$ and does not lie on this edge. This is why
quoting a longer ``inflation--restriction exact sequence'' from memory is hazardous: beyond five
terms, the filtration matters.

If $H^j(N,A)=0$ for $j>r$ and $H^i(Q,M)=0$ for $i>s$ for every relevant discrete module $M$,
then $E_2^{i,j}$ is zero outside a rectangle. Hence

$$
H^n(G,A)=0\qquad(n>r+s).
$$

This is the proof behind the cohomological-dimension inequality in the next section. If $N$ has
cohomological dimension zero at a prime $p$, the spectral sequence collapses on the bottom row
for $p$-primary coefficients and inflation is an isomorphism in every degree. If $Q$ has
dimension zero, restriction identifies global cohomology with the $Q$-invariants of subgroup
cohomology. These collapse statements require vanishing for all coefficient modules appearing
on the page, not just for the original $A$.

Cup products respect the filtration. On the $E_2$ page they combine the cup products for $N$ and
$Q$, with the sign imposed when horizontal and vertical degrees cross. Consequently

$$
d_r(xy)=d_r(x)y+(-1)^{\deg x}x\,d_r(y)
$$

for total degree. In particular, transgression interacts with products by the same Leibniz
principle as the connecting maps of Chapter 7.

### 13.6 Subgroups and extensions

For open $H\leq G$,

$$
\operatorname{cd}_p(H)\leq\operatorname{cd}_p(G).
$$

The proof uses Shapiro rather than transfer. Given a discrete $p$-primary $H$-module $A$,
$\operatorname{Coind}_H^GA$ is again discrete and $p$-primary, and

$$
H^n(H,A)\simeq H^n(G,\operatorname{Coind}_H^GA).
$$

Vanishing for $G$ therefore implies vanishing for $H$. The same argument proves monotonicity for
every closed subgroup, including infinite-index ones.

If $H$ is open and $[G:H]$ is prime to $p$, the reverse inequality also holds. For a discrete
$p$-primary $G$-module $A$, restriction in a degree above $\operatorname{cd}_p(H)$ is zero.
But

$$
\operatorname{cor}\operatorname{res}=[G:H]
$$

and multiplication by the prime-to-$p$ integer $[G:H]$ is an automorphism of every $p$-primary
cochain group and hence of its cohomology. Restriction is therefore injective, forcing the global
group to vanish. Thus

$$
\operatorname{cd}_p(H)=\operatorname{cd}_p(G)
$$

for open subgroups of index prime to $p$. For infinite index there is no transfer sum and no such
reverse argument.

For $1\to N\to G\to Q\to1$, the spectral sequence of Section 13.4 yields, under finite-dimension hypotheses,

$$
\operatorname{cd}_p(G)\leq\operatorname{cd}_p(N)+\operatorname{cd}_p(Q).
$$

The idea is that obstructions are resolved first along $N$ and then along $Q$. Determining local Galois dimensions and Euler characteristics requires arithmetic input and lies beyond this foundational statement.

### 13.7 Consequences and limitations

If $\operatorname{cd}_p(G)\leq1$, then $H^2(G,A)=0$ for every discrete $p$-primary $A$, so every continuously split extension by such $A$ splits and every degree-two lifting obstruction vanishes. If $\operatorname{cd}_p(G)\leq2$, there are no torsion obstructions above degree two, though $H^2$ may remain substantial.

Cohomological dimension is a vanishing bound, not a size formula. It does not determine $H^1$, and it does not by itself eliminate $\varprojlim^1$ for profinite coefficients.

### 13.8 Detecting bounds with finite coefficients

Suppose $H^n(G,A)=0$ for all finite $p$-primary discrete modules $A$ and all $n>d$. A general discrete $p$-primary module is a filtered union of its finitely generated subgroups, but those subgroups need not be $G$-stable. For any finite set of elements, continuity gives finite orbits; the subgroup generated by finitely many finite orbits is a finite $G$-submodule because it is finitely generated and $p$-primary torsion. Thus the module is a filtered union of finite $G$-submodules. Chapter 8 then extends the vanishing to every discrete $p$-primary module. This justifies testing cohomological dimension on finite coefficients.

There is a complementary detection principle. If a class in $H^n(G,A)$ with discrete coefficients is nonzero, the class and any proposed null-homotopy are controlled at finite level. The class therefore appears in some finite quotient $G/U$ with coefficients $A^U$, although it may die after further inflation. Nonvanishing in the direct limit means precisely that it survives every sufficiently fine refinement. This is why a single finite quotient can exhibit a potential obstruction while the profinite group may still have smaller cohomological dimension, as happened for procyclic groups.

## 14. Tangent spaces, obstructions, and a working toolkit

### 14.1 Why deformation theory sees the adjoint action

The preceding constructions become especially concrete when a representation is varied
infinitesimally. Let $k$ be a finite field, let $G$ be profinite, and let

$$
\bar\rho:G\longrightarrow\operatorname{GL}(V)
$$

be a continuous representation on a finite-dimensional $k$-space $V$. The target is finite and
discrete, so continuity is equivalent to open kernel. Put

$$
\operatorname{ad}(\bar\rho)=\operatorname{End}_k(V),
\qquad
g\cdot X=\bar\rho(g)X\bar\rho(g)^{-1}.
$$

Consider the dual numbers $k[\varepsilon]/(\varepsilon^2)$. Any lift reducing to $\bar\rho$ can be written uniquely as

$$
\rho(g)=(1+\varepsilon c(g))\bar\rho(g)
$$

for a continuous map $c:G\to\operatorname{ad}(\bar\rho)$. Multiplying two such matrices gives

$$
\rho(g)\rho(h)
=(1+\varepsilon(c(g)+g\cdot c(h)))\bar\rho(gh).
$$

Thus $\rho$ is a homomorphism exactly when

$$
c(gh)=c(g)+g\cdot c(h),
$$

so infinitesimal lifts are $1$-cocycles.

### 14.2 Equivalence and the tangent space

Conjugate $\rho$ by $1+\varepsilon X$. Since $(1+\varepsilon X)^{-1}=1-\varepsilon X$, its cocycle changes by

$$
c(g)\longmapsto c(g)+X-g\cdot X.
$$

This differs from $c$ by the negative of the coboundary $dX(g)=gX-X$, which generates the same subgroup of cocycles. Therefore infinitesimal lifts modulo infinitesimal conjugacy form

$$
H^1(G,\operatorname{ad}(\bar\rho)).
$$

This identification is not an analogy: it follows from the degree-one formula term by term. Framed deformations, in which a basis is retained and conjugation is not imposed, correspond to $Z^1$ rather than $H^1$. The exact sequence

$$
0\longrightarrow H^0(G,\operatorname{ad}(\bar\rho))
\longrightarrow\operatorname{ad}(\bar\rho)
\xrightarrow{d}Z^1(G,\operatorname{ad}(\bar\rho))
\longrightarrow H^1(G,\operatorname{ad}(\bar\rho))\longrightarrow0
$$

separates infinitesimal automorphisms, changes of frame, framed tangent vectors, and unframed tangent vectors.

If the determinant is fixed, its linearized condition selects the coefficient submodule

$$
\operatorname{ad}^0(\bar\rho)=\{X:\operatorname{tr}X=0\}.
$$

Indeed

$$
\det(1+\varepsilon X)=1+\varepsilon\operatorname{tr}X.
$$

In characteristics dividing $\dim V$, scalar and trace-zero subspaces need not split, so one must
use this kernel rather than assume a direct-sum decomposition. There is a second subtlety:
unframed strict conjugacy still allows every $X\in\operatorname{ad}(\bar\rho)$, not only
trace-zero $X$. Thus trace-zero cocycles do not always give $H^1(G,\operatorname{ad}^0)$ after
quotienting. Section 14.7 gives the exact fixed-determinant formulation.

### 14.3 The obstruction cocycle for a small extension

Let $R'\twoheadrightarrow R$ be a surjection of finite commutative rings with square-zero kernel
$I$, so $I^2=0$, and give both rings the discrete topology. Suppose a continuous representation

$$
\rho:G\to\operatorname{GL}_d(R)
$$

is given. Choose continuous set-theoretic lifts $\widetilde\rho(g)\in\operatorname{GL}_d(R')$. Their multiplicative defect is

$$
c(g,h)=\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}.
$$

It reduces to the identity, so using $1+M_d(I)$ it may be regarded additively as a cochain with
values in $M_d(I)$. This group is a $G$-module under conjugation through $\rho$; the action is
well defined because two lifts of a matrix differ by $M_d(I)$ and $I^2=0$. Denote it by

$$
\operatorname{ad}(\rho;I).
$$

Because $I^2=0$, conjugation on this kernel factors through $\rho$. Associativity of triple products gives

$$
g c(h,k)-c(gh,k)+c(g,hk)-c(g,h)=0.
$$

The provisional lift $g\mapsto\widetilde\rho(g)$ can be chosen continuous: $\rho(G)$ is finite,
and one chooses one matrix lift for each of its values. Thus $c$ is a continuous $2$-cocycle. If
the lifts are replaced by

$$
\widetilde\rho'(g)=(1+b(g))\widetilde\rho(g),
$$

where $b(g)\in M_d(I)$, the defect changes by $db$. Consequently

$$
[c]\in H^2(G,\operatorname{ad}(\rho;I))
$$

is independent of choices.

The class vanishes exactly when $c=db$ for some $b$. Correcting the lifts by $1-b(g)$ then makes
them multiplicative, producing a lift to $R'$. If $R'$ and $R$ are local $k$-algebras and the
surjection is **small**, meaning that the maximal ideal of $R'$ annihilates $I$, then conjugation
factors through $\bar\rho$ and

$$
\operatorname{ad}(\rho;I)
\simeq\operatorname{ad}(\bar\rho)\otimes_k I.
$$

This is the coefficient module most often used in dimension counts.

For complete coefficient rings one must build compatible finite-level lifts and confront the
inverse-limit issues of Chapter 12. A lift at every finite level is not yet a compatible system
of lifts; the distinction is exactly the one measured by inverse-limit obstructions.

### 14.4 The torsor of lifts and its automorphisms

Suppose the obstruction vanishes and choose one lift $\rho'_0:G\to\operatorname{GL}_d(R')$.
Every other lift with the same reduction has a unique expression

$$
\rho'_b(g)=(1+b(g))\rho'_0(g),
\qquad b(g)\in M_d(I).
$$

Multiplicativity of $\rho'_b$ is equivalent to $db=0$. Conjugation by $1+X$, with
$X\in M_d(I)$, changes $b$ by a coboundary. Therefore strict-equivalence classes of lifts form a
principal homogeneous space under

$$
H^1(G,\operatorname{ad}(\rho;I)).
$$

There is no distinguished origin until $\rho'_0$ is chosen, so this set is naturally a torsor,
not naturally the group itself. The strict automorphisms of a chosen lift that reduce to the
identity are $1+X$ with $X$ fixed by $G$; infinitesimally they are

$$
H^0(G,\operatorname{ad}(\rho;I)).
$$

This proves the degree-zero, degree-one, and degree-two dictionary in one calculation. It also
clarifies a frequent overstatement: nonzero $H^2$ does not say that a particular deformation is
obstructed. It says only that the canonical obstruction has a potentially nonzero receptacle.
Vanishing of $H^2$ is sufficient for every such square-zero lifting problem to be unobstructed;
it is not necessary for a given lift to exist.

### 14.5 Extension classes as the universal model

The matrix calculation is a specialized form of the $H^2$ extension classification. A provisional lift defines a factor set; associativity makes it a cocycle; changing the section adds a coboundary. The same pattern applies whenever one lifts a multiplication law, a group action, or descent data across a square-zero kernel.

There is a useful hierarchy:

$$
\begin{array}{c|c|c}
\text{degree}&\text{geometric meaning}&\text{deformation meaning}\\ \hline
0&\text{fixed elements}&\text{infinitesimal automorphisms}\\
1&\text{torsors or affine actions}&\text{tangent directions}\\
2&\text{extensions or factor sets}&\text{lifting obstructions}
\end{array}
$$

The table is a guide, not a claim that every deformation problem is exhausted by these three groups. Extra structures impose subspaces or kernels, and nonlinear compatibility can create successive obstruction problems. Cohomology supplies the ambient linear receptacles.

### 14.6 Characters and extensions of representations

Two elementary applications expose different faces of $H^1$.

First take a continuous character $\bar\chi:G\to k^\times$. Since conjugation on a
one-dimensional endomorphism space is trivial, an infinitesimal lift has the form

$$
\chi(g)=(1+\varepsilon c(g))\bar\chi(g)
$$

with $c\in\operatorname{Hom}_{\mathrm{cts}}(G,k)$. There is no nontrivial infinitesimal
conjugacy in dimension one, and therefore the tangent space is

$$
H^1(G,k)=\operatorname{Hom}_{\mathrm{cts}}(G,k)
$$

for the trivial action. Every such homomorphism factors through a finite quotient. This example
shows exactly how the topology discards abstract characters with nonopen kernel.

Second let $V_1,V_2$ be finite discrete $k$-representations. An extension

$$
0\longrightarrow V_1\longrightarrow E\longrightarrow V_2\longrightarrow0
$$

splits as a sequence of $k$-spaces. Choose a linear splitting and write the action in blocks:

$$
\rho_E(g)=
\begin{pmatrix}
\rho_1(g)&c(g)\rho_2(g)\\
0&\rho_2(g)
\end{pmatrix}.
$$

Here $c(g)\in\operatorname{Hom}_k(V_2,V_1)$, with $G$ acting by

$$
g\cdot X=\rho_1(g)X\rho_2(g)^{-1}.
$$

Matrix multiplication says that $c$ is a $1$-cocycle. Changing the linear splitting adds a
coboundary. Thus equivalence classes of continuous extensions are naturally

$$
H^1\bigl(G,\operatorname{Hom}_k(V_2,V_1)\bigr).
$$

The extension splits $G$-equivariantly precisely when the class is zero. Unlike the factor-set
interpretation of $H^2$, this is an extension in an abelian representation category, so it
occupies degree one.

### 14.7 Fixed determinant and framed conditions

For the dual-number deformation of $\bar\rho$, the determinant identity

$$
\det(1+\varepsilon X)=1+\varepsilon\operatorname{tr}(X)
$$

shows that fixing the determinant cuts out cocycles with values in

$$
\operatorname{ad}^0(\bar\rho)=\ker\bigl(\operatorname{tr}:\operatorname{ad}(\bar\rho)\to k\bigr).
$$

Framed fixed-determinant cocycles therefore form $Z^1(G,\operatorname{ad}^0)$. For unframed
deformations, however, strict conjugation by $1+\varepsilon X$ is allowed for every
$X\in\operatorname{ad}$ and changes the cocycle by $-dX$. Since trace is invariant under
conjugation, $dX$ is trace zero even when $X$ is not. The unframed fixed-determinant tangent
space is consequently

$$
\frac{Z^1(G,\operatorname{ad}^0)}{d(\operatorname{ad})}
\simeq
\ker\left(H^1(G,\operatorname{ad})
\xrightarrow{\operatorname{tr}}H^1(G,k)\right).
$$

The second description follows from the long exact sequence of
$0\to\operatorname{ad}^0\to\operatorname{ad}\xrightarrow{\operatorname{tr}}k\to0$.
It is naturally $H^1(G,\operatorname{ad}^0)$ if the map
$H^0(G,\operatorname{ad})\to k$ is surjective. This holds, for example, when
$\operatorname{char}k$ does not divide $\dim V$, because a scalar matrix of trace $1$ then
exists. In characteristic dividing $\dim V$, the scalar and trace-zero subspaces need not split,
and the kernel formula above is the statement valid without an extra hypothesis.

Framing retains a basis and forbids quotienting by strict conjugacy. Its tangent space is
$Z^1(G,\operatorname{ad})$. The exact sequence

$$
0\to H^0(G,\operatorname{ad})\to\operatorname{ad}
\xrightarrow{d}Z^1(G,\operatorname{ad})
\to H^1(G,\operatorname{ad})\to0
$$

therefore measures the difference between framed and unframed tangent dimensions. Over a finite
field, all terms are finite-dimensional. Taking dimensions gives

$$
\dim Z^1=\dim H^1+\dim\operatorname{ad}-\dim H^0.
$$

The last correction is the dimension of infinitesimal automorphisms; omitting it gives the wrong
number whenever the residual representation has extra endomorphisms.

For a small extension and a prescribed determinant, choose provisional matrix lifts with the
correct determinant. Their defect has trace zero, so the obstruction lies in

$$
H^2(G,\operatorname{ad}^0(\bar\rho)\otimes_k I).
$$

This conclusion requires the determinant-compatible provisional lifts. Starting with arbitrary
lifts and merely projecting an obstruction from $\operatorname{ad}$ to a trace-zero summand is
invalid when no such summand exists.

### 14.8 Imposing and comparing local or quotient conditions

A condition on a deformation often becomes a condition on its tangent cocycle. If a property is detected after restriction to a closed subgroup $H$, the allowed tangent space may be

$$
\ker\big(H^1(G,M)\longrightarrow H^1(H,M)/L_H\big)
$$

for a chosen subspace $L_H\subseteq H^1(H,M)$. If a representation must be trivial on a normal subgroup $N$, inflation–restriction identifies tangent classes arising from $G/N$. If a condition is induced from an open subgroup, Shapiro translates its tangent calculation back to that subgroup.

Connecting maps measure failure to lift a coefficient filtration. Cup products combine tangent classes with characters or dual classes. Corestriction transports subgroup classes globally and the projection formula controls their pairings. These are not independent tricks; they are compatible operations on one cochain complex.

Obstruction spaces behave similarly. A local or quotient obstruction is the restriction or inflation of a global $H^2$ class. Vanishing after restriction to an open subgroup only shows that the original obstruction is killed by the index; it need not vanish if that index is not invertible on the coefficients. This is exactly where the restriction–corestriction formula prevents an unjustified descent.

### 14.9 Vanishing criteria and what they buy

Suppose $k$ is finite and $M$ is a finite discrete $k[G]$-module. If

$$
H^2(G,M)=0,
$$

then every obstruction class with coefficients in $M\otimes_k I$ vanishes for every finite
$k$-space $I$ carrying the trivial $G$-action, because cochains commute with finite direct sums and

$$
H^2(G,M\otimes_k I)\simeq H^2(G,M)\otimes_k I.
$$

Thus a representation whose small-extension obstruction module is $M$ lifts across every small
extension, provided the auxiliary structures—such as a fixed determinant—have also been lifted
and their obstruction really lands in $M$. Successively lifting through a chain of small
extensions produces lifts over any finite local coefficient ring in the chain. At an inverse
limit of rings, compatibility must still be arranged; Chapter 12 explains the remaining issue.

If in addition $H^1(G,M)=0$, a lift, when it exists, is unique up to strict equivalence across
each small extension. If $H^0(G,M)=0$, it has no nontrivial infinitesimal strict automorphisms.
These statements have different degrees and should not be conflated:

$$
\begin{array}{c|c}
H^0=0&\text{no infinitesimal automorphisms}\\
H^1=0&\text{infinitesimal rigidity or uniqueness}\\
H^2=0&\text{unobstructed square-zero lifting}.
\end{array}
$$

The converses are generally false. A deformation problem may be unobstructed because all of its
actual obstruction classes vanish inside a nonzero $H^2$. It may be rigid even though the ambient
$H^1$ is nonzero because imposed local, determinant, or filtration conditions cut the tangent
space down to zero. Cohomology gives ambient linear spaces; the deformation problem specifies
which parts occur.

Restriction and corestriction give a useful vanishing test. If an obstruction
$o\in H^2(G,M)$ becomes zero over an open subgroup $H$, then $[G:H]o=0$. If $M$ is
$p$-primary and the index is prime to $p$, multiplication by the index is invertible, so $o=0$.
If the index is divisible by $p$, no such conclusion follows. This is the precise descent
principle behind many arguments that remove an obstruction after a prime-to-$p$ extension.

### 14.10 A calculation protocol

For a concrete continuous cohomology problem, the following order keeps hypotheses visible.

1. Specify the topology on $G$ and the coefficients. Decide whether the coefficients are finite, discrete torsion, profinite, or $\ell$-adic.

2. Verify continuity of the action. For discrete coefficients, check open stabilizers; for a lattice, check all finite reductions.

3. Decide whether the problem is coefficient-theoretic or group-theoretic. Use a long exact sequence for the former, and restriction, inflation–restriction, or Shapiro for the latter.

4. Work with normalized inhomogeneous cochains in degrees one and two. Write

$$
f(gh)=f(g)+gf(h)
$$

or

$$
g c(h,k)-c(gh,k)+c(g,hk)-c(g,h)=0
$$

before invoking general machinery; this fixes conventions and signs.

5. If coefficients are discrete, pass to a finite quotient only in the form

$$
H^n(G,A)=\varinjlim_UH^n(G/U,A^U).
$$

Do not omit the invariants $A^U$.

6. If coefficients are inverse limits, write the Milnor sequence and justify the vanishing of $\varprojlim^1$ before identifying cohomology with an inverse limit.

7. For an open subgroup, check the direction of maps:

$$
\operatorname{res}:H^n(G,A)\to H^n(H,A),
\qquad
\operatorname{cor}:H^n(H,A)\to H^n(G,A).
$$

Use $\operatorname{cor}\operatorname{res}=[G:H]$ on global cohomology; use the conjugate sum for the reverse composite.

8. Interpret the result. A class in $H^1$ is a torsor or tangent direction; a class in $H^2$ is an extension or obstruction. State what its vanishing constructs, not merely that a group is zero.

### 14.11 Final perspective

Continuous cohomology reconciles two opposing features of profinite symmetry. A profinite group contains information at infinitely many finite levels, but a discrete continuous cochain can inspect only finitely much at once. The cochain complex records this tension exactly: direct limits assemble discrete information, inverse limits retain complete coefficient information, and the possible $\varprojlim^1$ term marks the boundary between the two.

The low degrees give the theory its practical force. Fixed points occupy degree zero. Crossed homomorphisms, torsors, and infinitesimal variations occupy degree one. Factor sets, extensions, and lifting obstructions occupy degree two. Long exact sequences explain how a failure of lifting moves up one degree; inflation–restriction separates quotient data from kernel data; Shapiro moves problems across open subgroups; transfer brings them back; cup products let classes interact with controlled signs.

These operations form a single coherent language for continuous symmetry. Once the topology of the coefficients is stated honestly and the finite-level passage is made with its exact hypotheses, tangent spaces and obstruction spaces cease to be metaphors: they are explicit cohomology groups whose cocycles can be written, transported, paired, and corrected. That is the durable foundation on which later arithmetic calculations rest.
