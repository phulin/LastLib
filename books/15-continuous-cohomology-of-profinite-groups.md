# Continuous Cohomology of Profinite Groups

## Contents

1. [Compact symmetry and discrete arithmetic](#1-compact-symmetry-and-discrete-arithmetic)
   - [Why continuity changes group cohomology](#11-why-continuity-changes-group-cohomology)
   - [Profinite groups](#12-profinite-groups)
   - [Discrete continuous modules](#13-discrete-continuous-modules)
   - [Compact-to-discrete factorization](#14-compact-to-discrete-factorization)
   - [Invariants and the first warning about exactness](#15-invariants-and-the-first-warning-about-exactness)
2. [Continuous cochains](#2-continuous-cochains)
   - [Why inhomogeneous cochains are practical](#21-why-inhomogeneous-cochains-are-practical)
   - [The differential and its signs](#22-the-differential-and-its-signs)
   - [Normalized cochains](#23-normalized-cochains)
   - [Homogeneous cochains](#24-homogeneous-cochains)
   - [Continuous versus abstract classes](#25-continuous-versus-abstract-classes)
3. [The first three degrees](#3-the-first-three-degrees)
   - [Degree zero: fixed points](#31-degree-zero-fixed-points)
   - [Degree one: crossed homomorphisms](#32-degree-one-crossed-homomorphisms)
   - [Torsors and descent](#33-torsors-and-descent)
   - [Degree two: factor sets](#34-degree-two-factor-sets)
   - [Which topological extensions are classified](#35-which-topological-extensions-are-classified)
   - [Central extensions and projective lifting](#36-central-extensions-and-projective-lifting)
4. [Exact sequences and connecting classes](#4-exact-sequences-and-connecting-classes)
   - [Why a boundary map must exist](#41-why-a-boundary-map-must-exist)
   - [The explicit connecting homomorphism](#42-the-explicit-connecting-homomorphism)
   - [The long exact sequence](#43-the-long-exact-sequence)
   - [Naturality and diagrams of coefficients](#44-naturality-and-diagrams-of-coefficients)
   - [Why topological coefficients require new hypotheses](#45-why-topological-coefficients-require-new-hypotheses)
5. [Functoriality, restriction, and transfer](#5-functoriality-restriction-and-transfer)
   - [Two kinds of variance](#51-two-kinds-of-variance)
   - [Restriction and conjugation](#52-restriction-and-conjugation)
   - [Coinduction as the source of corestriction](#53-coinduction-as-the-source-of-corestriction)
   - [Shapiro first, then corestriction](#54-shapiro-first-then-corestriction)
   - [Restriction–corestriction formulas](#55-restrictioncorestriction-formulas)
   - [A vanishing consequence](#56-a-vanishing-consequence)
6. [Normal subgroups and inflation](#6-normal-subgroups-and-inflation)
   - [Separating quotient and kernel information](#61-separating-quotient-and-kernel-information)
   - [Inflation and restriction](#62-inflation-and-restriction)
   - [The five-term inflation–restriction sequence](#63-the-five-term-inflationrestriction-sequence)
   - [Transgression as an extension obstruction](#64-transgression-as-an-extension-obstruction)
   - [Complete proof in low degrees](#65-complete-proof-in-low-degrees)
   - [A useful special case](#66-a-useful-special-case)
7. [Cup products and coefficient pairings](#7-cup-products-and-coefficient-pairings)
   - [Why cohomology should multiply](#71-why-cohomology-should-multiply)
   - [The cochain formula](#72-the-cochain-formula)
   - [Leibniz rule](#73-leibniz-rule)
   - [Associativity, units, and signs](#74-associativity-units-and-signs)
   - [Naturality and the projection formula](#75-naturality-and-the-projection-formula)
8. [Finite quotients and filtered limits](#8-finite-quotients-and-filtered-limits)
   - [Why compactness makes discrete cohomology finite-level](#81-why-compactness-makes-discrete-cohomology-finite-level)
   - [The finite-quotient theorem](#82-the-finite-quotient-theorem)
   - [Finite modules and filtered unions](#83-finite-modules-and-filtered-unions)
   - [Why this fails for profinite coefficients](#84-why-this-fails-for-profinite-coefficients)
9. [Induction, coinduction, and Shapiro's lemma](#9-induction-coinduction-and-shapiros-lemma)
   - [Distributing a module over cosets](#91-distributing-a-module-over-cosets)
   - [Evaluation and an explicit inverse](#92-evaluation-and-an-explicit-inverse)
   - [Proof and continuity of Shapiro's lemma](#93-proof-and-continuity-of-shapiros-lemma)
   - [Infinite index and acyclic modules](#94-infinite-index-and-acyclic-modules)
10. [Cyclic and procyclic calculations](#10-cyclic-and-procyclic-calculations)
    - [Why cyclic groups are the local model](#101-why-cyclic-groups-are-the-local-model)
    - [The periodic resolution](#102-the-periodic-resolution)
    - [Recovering the degree-one formula directly](#103-recovering-the-degree-one-formula-directly)
    - [Trivial action and concrete examples](#104-trivial-action-and-concrete-examples)
    - [A nontrivial action](#105-a-nontrivial-action)
    - [The procyclic group](#106-the-procyclic-group-widehatmathbf-z)
    - [The group $\mathbf Z_\ell$](#107-the-group-mathbf-z_ell)
    - [Finite quotient calculations as consistency checks](#108-finite-quotient-calculations-as-consistency-checks)
    - [Worked extension classes for $C_m$](#109-worked-extension-classes-for-c_m)
11. [Topological and $\ell$-adic coefficients](#11-topological-and-ell-adic-coefficients)
    - [A separate coefficient theory](#111-a-separate-coefficient-theory)
    - [Four coefficient regimes](#112-four-coefficient-regimes)
    - [Profinite modules and the Milnor sequence](#113-profinite-modules-and-the-milnor-sequence)
    - [$\ell$-adic lattices and vector spaces](#114-ell-adic-lattices-and-vector-spaces)
    - [Products and matrix actions](#115-products-and-matrix-actions)
    - [A procyclic comparison across topologies](#116-a-procyclic-comparison-across-topologies)
12. [Cohomological dimension](#12-cohomological-dimension)
    - [Measuring the height of obstructions](#121-measuring-the-height-of-obstructions)
    - [Examples and torsion](#122-examples-and-torsion)
    - [Dimension shifting](#123-dimension-shifting)
    - [Subgroups and extensions](#124-subgroups-and-extensions)
    - [Consequences and limitations](#125-consequences-and-limitations)
    - [Detecting bounds with finite coefficients](#126-detecting-bounds-with-finite-coefficients)
13. [Tangent spaces, obstructions, and a working toolkit](#13-tangent-spaces-obstructions-and-a-working-toolkit)
    - [Why deformation theory sees the adjoint action](#131-why-deformation-theory-sees-the-adjoint-action)
    - [Equivalence and the tangent space](#132-equivalence-and-the-tangent-space)
    - [The obstruction cocycle for a small extension](#133-the-obstruction-cocycle-for-a-small-extension)
    - [Extension classes as the universal model](#134-extension-classes-as-the-universal-model)
    - [Imposing and comparing conditions](#135-imposing-and-comparing-conditions)
    - [A calculation protocol](#136-a-calculation-protocol)
    - [Final perspective](#137-final-perspective)

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

The reason is that the cochains supported on tuples containing an identity form an acyclic degeneracy subcomplex. Explicitly, successively subtracting coboundaries obtained by inserting the identity eliminates degenerate values. This process is finite in each degree and preserves continuity. We will therefore impose normalization whenever writing cocycles that classify extensions, but the differential always means the formula of the preceding section.

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

This is the first major boundary between discrete and topological coefficient theories. We will construct cohomology for topological modules in Chapter 11, but all unqualified long exact sequences before then belong to the discrete category.

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

At degree zero it follows because an invariant element is fixed by every coset representative. In all degrees, the transfer construction decomposes into a sum of conjugation maps, and inner conjugations act trivially; hence each of the $[G:H]$ summands is the identity.

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

Each term corresponds to one double coset. The formula follows by partitioning the cosets used in transfer into $K$-orbits. It explains why restriction and corestriction form a coherent calculus rather than two unrelated operations.

### 5.6 A vanishing consequence

If $H$ is open and $H^n(H,A)=0$, restriction–corestriction shows that $[G:H]$ annihilates $H^n(G,A)$. More generally, the kernel of restriction is killed by $[G:H]$. This elementary observation is frequently decisive when $H$ is chosen to trivialize an action and the index is invertible on the coefficient group.

The hypothesis “open” cannot be weakened to “closed” in corestriction statements: the sum would range over infinitely many cosets, and a general discrete module carries no notion of convergence for it.

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

Take $\xi\in H^1(N,A)^Q$. A cocycle $f:N\to A$ defines the extension

$$
0\longrightarrow A\longrightarrow A\rtimes_f N\longrightarrow N\longrightarrow1
$$

in its torsor interpretation, or equivalently an $A$-torsor with $N$-action. Quotient invariance of $[f]$ says that conjugation by every $g\in G$ carries this object to an isomorphic one. Choosing such isomorphisms need not make them compatible under multiplication in $Q$. Their failure of compatibility is an automorphism of the underlying $N$-object, hence translation by an element of $A^N$. It is a $2$-cocycle on $Q$; changing the chosen isomorphisms changes it by a coboundary. Its class is $\operatorname{trg}(\xi)$.

For readers wanting a cochain formula, the construction can be normalized as follows. Choose a continuous section $s:Q\to G$ when one is available, with $s(1)=1$, and set

$$
u(q,r)=s(q)s(r)s(qr)^{-1}\in N.
$$

For each $q$, quotient invariance supplies $a_q\in A$, with $a_1=0$, satisfying

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

This explicit formula applies whenever the quotient map has a continuous section. In complete generality transgression is obtained from the same cochain filtration without choosing a global section; continuous local representatives produce the identical canonical class. The intrinsic definition is the compatibility obstruction of the preceding paragraph, so existence of a global section is not a hypothesis of the five-term sequence.

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

The cochain product is not literally graded commutative. A canonical cochain homotopy interchanges its blocks. On cohomology, if the reversed pairing satisfies $\mu^\tau(b,a)=\mu(a,b)$, then

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

## 9. Induction, coinduction, and Shapiro's lemma

### 9.1 Distributing a module over cosets

Restriction changes the acting group without changing the module. Coinduction turns an $H$-module into a $G$-module by distributing copies over cosets. Shapiro's lemma says that this distribution introduces no new cohomology.

For open $H\leq G$, the module $\operatorname{Coind}_H^GA$ from Section 5.3 is a finite product of discrete copies of $A$, hence is discrete. Induction may be written $\mathbf Z[G]\otimes_{\mathbf Z[H]}A$ with locally constant conventions. At finite index, finite sums and products coincide, so induction and coinduction are naturally isomorphic. At infinite index they differ, and topology must be specified; coinduction is the robust construction here.

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

For closed $H$ of infinite index, Shapiro remains valid for the discrete coinduced module of continuous equivariant functions. The proof uses finite clopen partitions in place of a finite transversal: every individual cochain factors through sufficiently coarse finite coset data, and the same evaluation and prism homotopies apply at that level. What fails at infinite index is the identification of induction with coinduction and the finite trace map used for corestriction. There is no sum over $G/H$, so Shapiro survives but transfer does not.

With $H=\{1\}$, Shapiro gives

$$
H^n(G,\operatorname{Coind}_{1}^{G}A)=0\qquad(n>0).
$$

Coinduced modules are therefore acyclic for invariants. Concretely, translation and evaluation contract their cocycles. This supplies the engine for dimension shifting without requiring abstract machinery.

## 10. Cyclic and procyclic calculations

### 10.1 Why cyclic groups are the local model

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

### 10.2 The periodic resolution

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

### 10.3 Recovering the degree-one formula directly

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

### 10.4 Trivial action and concrete examples

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

### 10.5 A nontrivial action

Let $C_2$ act on $A=\mathbf Z$ by $\sigma a=-a$. Then $N=1+\sigma=0$ and $D=-2$. Hence

$$
H^{2r+1}(C_2,\mathbf Z_{\mathrm{sign}})=\mathbf Z/2\mathbf Z,\qquad
H^{2r}(C_2,\mathbf Z_{\mathrm{sign}})=0\quad(r\geq1),
$$

because the only invariants in $\mathbf Z$ are zero. This example shows that odd and even behavior can exchange when the action changes; formulas depending only on the abstract coefficient group cannot be correct.

### 10.6 The procyclic group $\widehat{\mathbf Z}$

Let $\Gamma=\widehat{\mathbf Z}$ with a chosen topological generator $\sigma$. For a discrete torsion $\Gamma$-module $A$, continuous cohomology is concentrated in degrees zero and one:

$$
H^0(\Gamma,A)=\ker(\sigma-1),\qquad
H^1(\Gamma,A)=A/(\sigma-1)A,
$$

$$
H^n(\Gamma,A)=0\qquad(n\geq2).
$$

The torsion hypothesis in the $H^1$ formula is essential. With trivial action on a discrete torsion module, an element $a$ of order $m$ defines a continuous homomorphism $\widehat{\mathbf Z}\to A$ by sending $1$ to $a$; it factors through $\mathbf Z/m\mathbf Z$. Thus every element contributes. With $A=\mathbf Z$ discrete and trivial, however, every continuous homomorphism from compact $\widehat{\mathbf Z}$ has finite image and is zero, whereas $A/(\sigma-1)A=\mathbf Z$. The naive formula fails.

To prove the torsion statement, use the finite-quotient theorem. Each element and each cochain is visible in some cyclic quotient. Under inflation from $C_m$ to $C_{mr}$, the periodic even classes are multiplied through a norm along the larger kernel; after refining by a multiple of their torsion orders they die. Degree-one classes stabilize to the cokernel of $\sigma-1$: the finite-order condition needed to close a cocycle is achieved in some quotient. Hence the direct limit of finite cyclic cohomology has the asserted form.

This is a striking continuity effect. Every finite cyclic quotient has periodic higher cohomology, but those classes do not persist coherently through all refinements.

### 10.7 The group $\mathbf Z_\ell$

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

### 10.8 Finite quotient calculations as consistency checks

The cyclic formulas interact cleanly with restriction and corestriction. If $C_d\leq C_m$ has index $e$, restriction sends a homomorphism to its value on $\sigma^e$, while corestriction is a norm over $e$ cosets. Their composite on $H^n(C_m,A)$ is multiplication by $e$, as the general theorem predicts.

Inflation from $C_m$ to a cyclic extension quotient can annihilate an even class, which is precisely why inflation in degree two is not always injective. The five-term sequence identifies the lost class as a transgression from a character of the kernel. Thus the abstract functorial statements of Chapters 5 and 6 can be tested, including their directions and indices, in this explicit periodic complex.

### 10.9 Worked extension classes for $C_m$

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

## 11. Topological and $\ell$-adic coefficients

### 11.1 A separate coefficient theory

Discrete modules are appropriate for finite modules and groups such as $\mathbf Q_\ell/\mathbf Z_\ell$. Lattices such as $\mathbf Z_\ell^d$ and vector spaces such as $\mathbf Q_\ell^d$ are not discrete in their natural topology. Declaring them discrete would impose the wrong continuity condition: a continuous action on a finitely generated discrete module must have finite image, while an $\ell$-adic representation usually has infinite compact image.

A **topological $G$-module** is a Hausdorff topological abelian group $M$ with a jointly continuous action $G\times M\to M$. Define

$$
C^n_{\mathrm{cts}}(G,M)=\operatorname{Map}_{\mathrm{cts}}(G^n,M)
$$

with the same differential, and call its cohomology $H^n_{\mathrm{cts}}(G,M)$. The calculation $d^2=0$ remains valid. What changes is exactness: continuous surjections need not permit continuous cochain lifts, and images need not be closed. Results from the discrete theory survive only under stated lifting or inverse-limit hypotheses.

### 11.2 Four coefficient regimes

It is useful to keep four regimes distinct.

1. A **finite module** has the discrete topology, equivalently its compact topology. Its action factors through a finite quotient.

2. A **discrete torsion module** may be infinite. Every element and cochain is finite-level, but no common finite quotient need control the whole module.

3. A **profinite module** is an inverse limit of finite discrete modules with compatible continuous action. Its elements can contain infinitely much information.

4. An **$\ell$-adic module** is typically a finite free $\mathbf Z_\ell$-module $T$, a finite-dimensional $\mathbf Q_\ell$-space $V$, or $V/T$. Here $T$ is profinite, $V$ is locally compact, and $V/T$ is discrete torsion.

The same algebraic group can yield different cohomology with different topologies. Continuous homomorphisms $\mathbf Z_\ell\to\mathbf Z_\ell$ include all scalar multiplications when the target is profinite, but are zero when it is discrete. Topology is part of the coefficient object.

### 11.3 Profinite modules and the Milnor sequence

Suppose

$$
T\simeq\varprojlim_rT_r
$$

as a topological $G$-module, where $T_r$ is finite discrete and transitions are surjective. A map to $T$ is continuous exactly when all maps to $T_r$ are, so

$$
C^n_{\mathrm{cts}}(G,T)\simeq\varprojlim_r C^n(G,T_r).
$$

Inverse limits are only left exact. For a countable tower there is a natural Milnor exact sequence

$$
0\longrightarrow\varprojlim{}^1_rH^{n-1}(G,T_r)
\longrightarrow H^n_{\mathrm{cts}}(G,T)
\longrightarrow\varprojlim_rH^n(G,T_r)
\longrightarrow0.
$$

Represent the inverse limit as the kernel of $1-\mathrm{shift}$ on $\prod_rC^\bullet(G,T_r)$ and take the associated long exact sequence. Surjective coefficient transitions give the needed degreewise lifting because cochains into finite levels have finite image.

The $\varprojlim^1$ term measures compatible cohomology classes that cannot be represented by compatible cocycles. It vanishes when the system $H^{n-1}(G,T_r)$ is Mittag–Leffler; this holds, for example, when all those groups are finite, since descending images stabilize. Only then may one conclude

$$
H^n_{\mathrm{cts}}(G,T)\simeq\varprojlim_rH^n(G,T_r).
$$

### 11.4 $\ell$-adic lattices and vector spaces

Let $T$ be finite free over $\mathbf Z_\ell$ with continuous action. Then

$$
T\simeq\varprojlim_rT/\ell^rT,
$$

so the Milnor sequence applies. Under suitable finiteness, its cohomology is the inverse limit of finite-level cohomology.

The coefficient sequence

$$
0\longrightarrow T\longrightarrow V=T\otimes_{\mathbf Z_\ell}\mathbf Q_\ell
\longrightarrow V/T\longrightarrow0
$$

mixes topological regimes. A long exact sequence exists only in a theory where maps into the quotient have continuous lifts. Compact source spaces and local sections often supply them, but this must be proved. Likewise,

$$
H^n(G,T)\otimes\mathbf Q_\ell\simeq H^n(G,V)
$$

requires control of torsion and limits; it is not a formal identity.

For a short exact sequence of profinite modules, a continuous section of the quotient map makes the cochain sequence exact and recovers Chapter 4. Alternatively, use compatible levelwise exact sequences and then pass to limits, retaining any $\varprojlim^1$ terms. Levelwise lifting does not guarantee a compatible lift.

### 11.5 Products and matrix actions

A continuous equivariant pairing of topological modules defines cup products by the same formula, with the same Leibniz sign and associativity. For profinite modules the pairing may factor through a completed tensor product. Products can be checked at finite levels, but perfectness or nondegeneracy requires additional finiteness and never follows merely from the formula.

Choosing a basis of finite free $T$ identifies its action with

$$
\rho:G\longrightarrow\operatorname{GL}_d(\mathbf Z_\ell).
$$

Continuity is equivalent to continuity of every finite reduction. Each reduction has open kernel, though their intersection need not be open; this permits infinite $\ell$-adic image. The module $\operatorname{End}(T)$ carries conjugation action $gX=\rho(g)X\rho(g)^{-1}$, whose cohomology will appear in the final toolkit.

### 11.6 A procyclic comparison across topologies

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

For $V=\mathbf Q_\ell$ with its natural topology, continuous homomorphisms $\mathbf Z_\ell\to\mathbf Q_\ell$ are again determined by the image of $1$, but that image can be any element of $\mathbf Q_\ell$. Hence $H^1(G,V)\simeq\mathbf Q_\ell$. These three answers—finite level, profinite lattice, and vector space—fit together only because their topologies were kept explicit.

## 12. Cohomological dimension

### 12.1 Measuring the height of obstructions

For a prime $p$, the **$p$-cohomological dimension** $\operatorname{cd}_p(G)$ is the least $d$ such that

$$
H^n(G,A)=0
$$

for every discrete $p$-primary torsion $G$-module $A$ and every $n>d$. If none exists, it is infinite. The torsion cohomological dimension is the supremum over $p$. This definition keeps $\ell$-adic derived-limit issues separate.

### 12.2 Examples and torsion

The trivial group has dimension zero. More generally, $\operatorname{cd}_p(G)=0$ exactly when invariants are exact on discrete $p$-primary modules; equivalently, finite quotients of $G$ have order prime to $p$.

A nontrivial finite $p$-group has infinite $p$-cohomological dimension, as periodic cyclic cohomology with $\mathbf F_p$ coefficients already suggests. More generally, an element of order $p$ forces $\operatorname{cd}_p(G)=\infty$. Thus $p$-torsion-freeness is necessary for finite $p$-dimension.

Chapter 10 gives

$$
\operatorname{cd}_p(\widehat{\mathbf Z})=1,
\qquad \operatorname{cd}_\ell(\mathbf Z_\ell)=1,
\qquad \operatorname{cd}_p(\mathbf Z_\ell)=0\ (p\ne\ell).
$$

### 12.3 Dimension shifting

Embed a discrete $G$-module $A$ into

$$
I(A)=\operatorname{Map}_{\mathrm{cts}}(G,A)
$$

by sending $a$ to $g\mapsto ga$, and let $Q(A)=I(A)/A$. Since coinduced modules are acyclic, the long exact sequence gives

$$
H^{n+1}(G,A)\simeq H^n(G,Q(A))\qquad(n\geq1).
$$

This **dimension shifting** turns a high-degree obstruction into a lower-degree one with changed coefficients. It shows that sufficiently uniform vanishing in one degree propagates upward.

### 12.4 Subgroups and extensions

For open $H\leq G$,

$$
\operatorname{cd}_p(H)\leq\operatorname{cd}_p(G).
$$

If $[G:H]$ is prime to $p$, restriction is injective on $p$-primary cohomology by restriction–corestriction, and standard induction gives equality of dimensions. Closed infinite-index subgroups require coinduction rather than transfer; monotonicity remains valid under the usual profinite hypotheses, but there is no finite coset sum.

For $1\to N\to G\to Q\to1$, the higher form of inflation–restriction yields, under finite-dimension hypotheses,

$$
\operatorname{cd}_p(G)\leq\operatorname{cd}_p(N)+\operatorname{cd}_p(Q).
$$

The idea is that obstructions are resolved first along $N$ and then along $Q$. Determining local Galois dimensions and Euler characteristics requires arithmetic input and lies beyond this foundational statement.

### 12.5 Consequences and limitations

If $\operatorname{cd}_p(G)\leq1$, then $H^2(G,A)=0$ for every discrete $p$-primary $A$, so every continuously split extension by such $A$ splits and every degree-two lifting obstruction vanishes. If $\operatorname{cd}_p(G)\leq2$, there are no torsion obstructions above degree two, though $H^2$ may remain substantial.

Cohomological dimension is a vanishing bound, not a size formula. It does not determine $H^1$, and it does not by itself eliminate $\varprojlim^1$ for profinite coefficients.

### 12.6 Detecting bounds with finite coefficients

Suppose $H^n(G,A)=0$ for all finite $p$-primary discrete modules $A$ and all $n>d$. A general discrete $p$-primary module is a filtered union of its finitely generated subgroups, but those subgroups need not be $G$-stable. For any finite set of elements, continuity gives finite orbits; the subgroup generated by finitely many finite orbits is a finite $G$-submodule because it is finitely generated and $p$-primary torsion. Thus the module is a filtered union of finite $G$-submodules. Chapter 8 then extends the vanishing to every discrete $p$-primary module. This justifies testing cohomological dimension on finite coefficients.

There is a complementary detection principle. If a class in $H^n(G,A)$ with discrete coefficients is nonzero, the class and any proposed null-homotopy are controlled at finite level. The class therefore appears in some finite quotient $G/U$ with coefficients $A^U$, although it may die after further inflation. Nonvanishing in the direct limit means precisely that it survives every sufficiently fine refinement. This is why a single finite quotient can exhibit a potential obstruction while the profinite group may still have smaller cohomological dimension, as happened for procyclic groups.

## 13. Tangent spaces, obstructions, and a working toolkit

### 13.1 Why deformation theory sees the adjoint action

The preceding constructions become especially concrete when a representation is varied infinitesimally. Let $k$ be a field, let $G$ be profinite, and let

$$
\bar\rho:G\longrightarrow\operatorname{GL}(V)
$$

be a continuous representation on a finite-dimensional $k$-space with finite discrete topology. Put

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

### 13.2 Equivalence and the tangent space

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

If a determinant is fixed and the characteristic permits the expected trace decomposition, the relevant coefficient module is often

$$
\operatorname{ad}^0(\bar\rho)=\{X:\operatorname{tr}X=0\}.
$$

Indeed

$$
\det(1+\varepsilon X)=1+\varepsilon\operatorname{tr}X.
$$

In characteristics dividing $\dim V$, scalar and trace-zero subspaces need not split, so one must impose the actual linearized determinant condition rather than assume a direct-sum decomposition.

### 13.3 The obstruction cocycle for a small extension

Let $R'\twoheadrightarrow R$ be a surjection of coefficient rings with square-zero kernel $I$, so $I^2=0$. Suppose a representation

$$
\rho:G\to\operatorname{GL}_d(R)
$$

is given. Choose continuous set-theoretic lifts $\widetilde\rho(g)\in\operatorname{GL}_d(R')$. Their multiplicative defect is

$$
c(g,h)=\widetilde\rho(g)\widetilde\rho(h)
\widetilde\rho(gh)^{-1}.
$$

It reduces to the identity, so using $1+M_d(I)$ it may be regarded additively as a cochain with values in

$$
\operatorname{ad}(\rho)\otimes_R I.
$$

Because $I^2=0$, conjugation on this kernel factors through $\rho$. Associativity of triple products gives

$$
g c(h,k)-c(gh,k)+c(g,hk)-c(g,h)=0.
$$

Thus $c$ is a continuous $2$-cocycle. If the lifts are replaced by

$$
\widetilde\rho'(g)=(1+b(g))\widetilde\rho(g),
$$

where $b(g)\in M_d(I)$, the defect changes by $db$. Consequently

$$
[c]\in H^2(G,\operatorname{ad}(\rho)\otimes_RI)
$$

is independent of choices.

The class vanishes exactly when $c=db$ for some $b$. Correcting the lifts by $1-b(g)$ then makes them multiplicative, producing a lift to $R'$. Hence $H^2$ contains the obstruction, while, if it vanishes, the set of lifts is a torsor under $H^1$ with the same coefficients. Automorphisms of a lift are controlled by $H^0$.

Continuity is not automatic from an algebraic choice of matrices. For finite Artinian coefficient rings the target kernels are finite discrete, so compact-to-discrete factorization permits continuous choices after passage to a finite quotient. For complete coefficient rings one must build compatible finite-level lifts and confront the inverse-limit issues of Chapter 11.

### 13.4 Extension classes as the universal model

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

### 13.5 Imposing and comparing conditions

A condition on a deformation often becomes a condition on its tangent cocycle. If a property is detected after restriction to a closed subgroup $H$, the allowed tangent space may be

$$
\ker\big(H^1(G,M)\longrightarrow H^1(H,M)/L_H\big)
$$

for a chosen subspace $L_H\subseteq H^1(H,M)$. If a representation must be trivial on a normal subgroup $N$, inflation–restriction identifies tangent classes arising from $G/N$. If a condition is induced from an open subgroup, Shapiro translates its tangent calculation back to that subgroup.

Connecting maps measure failure to lift a coefficient filtration. Cup products combine tangent classes with characters or dual classes. Corestriction transports subgroup classes globally and the projection formula controls their pairings. These are not independent tricks; they are compatible operations on one cochain complex.

Obstruction spaces behave similarly. A local or quotient obstruction is the restriction or inflation of a global $H^2$ class. Vanishing after restriction to an open subgroup only shows that the original obstruction is killed by the index; it need not vanish if that index is not invertible on the coefficients. This is exactly where the restriction–corestriction formula prevents an unjustified descent.

### 13.6 A calculation protocol

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

### 13.7 Final perspective

Continuous cohomology reconciles two opposing features of profinite symmetry. A profinite group contains information at infinitely many finite levels, but a discrete continuous cochain can inspect only finitely much at once. The cochain complex records this tension exactly: direct limits assemble discrete information, inverse limits retain complete coefficient information, and the possible $\varprojlim^1$ term marks the boundary between the two.

The low degrees give the theory its practical force. Fixed points occupy degree zero. Crossed homomorphisms, torsors, and infinitesimal variations occupy degree one. Factor sets, extensions, and lifting obstructions occupy degree two. Long exact sequences explain how a failure of lifting moves up one degree; inflation–restriction separates quotient data from kernel data; Shapiro moves problems across open subgroups; transfer brings them back; cup products let classes interact with controlled signs.

These operations form a single coherent language for continuous symmetry. Once the topology of the coefficients is stated honestly and the finite-level passage is made with its exact hypotheses, tangent spaces and obstruction spaces cease to be metaphors: they are explicit cohomology groups whose cocycles can be written, transported, paired, and corrected. That is the durable foundation on which later arithmetic calculations rest.
