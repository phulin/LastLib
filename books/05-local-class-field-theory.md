# Local Class Field Theory

## Contents

1. [The local reciprocity problem](#1-the-local-reciprocity-problem)
   - [What kind of local field is meant](#11-what-kind-of-local-field-is-meant)
   - [The classification one hopes for](#12-the-classification-one-hopes-for)
   - [The reciprocity convention](#13-the-reciprocity-convention)
   - [Why the proof has several layers](#14-why-the-proof-has-several-layers)
2. [The topology of the multiplicative group and its norm subgroups](#2-the-topology-of-the-multiplicative-group-and-its-norm-subgroups)
   - [Separating magnitude from units](#21-separating-magnitude-from-units)
   - [Open subgroups of finite index](#22-open-subgroups-of-finite-index)
   - [Norms and valuation coordinates](#23-norms-and-valuation-coordinates)
   - [Norm groups are open and closed](#24-norm-groups-are-open-and-closed)
   - [The index question](#25-the-index-question)
3. [Cyclic extensions, norms, and Hilbert 90](#3-cyclic-extensions-norms-and-hilbert-90)
   - [Why cyclic extensions come first](#31-why-cyclic-extensions-come-first)
   - [Hilbert's Theorem 90 with proof](#32-hilberts-theorem-90-with-proof)
   - [Tate cohomology of a cyclic group](#33-tate-cohomology-of-a-cyclic-group)
   - [Cyclic algebras](#34-cyclic-algebras)
   - [The unramified cyclic computation](#35-the-unramified-cyclic-computation)
4. [The Brauer invariant of a local field](#4-the-brauer-invariant-of-a-local-field)
   - [Why central simple algebras enter reciprocity](#41-why-central-simple-algebras-enter-reciprocity)
   - [Valuations on division algebras](#42-valuations-on-division-algebras)
   - [Unramified splitting and the invariant](#43-unramified-splitting-and-the-invariant)
   - [Relative Brauer groups and the norm index](#44-relative-brauer-groups-and-the-norm-index)
   - [The fundamental class](#45-the-fundamental-class)
5. [From the fundamental class to finite reciprocity](#5-from-the-fundamental-class-to-finite-reciprocity)
   - [Why abelianization appears](#51-why-abelianization-appears)
   - [Tate homology in degree minus two](#52-tate-homology-in-degree-minus-two)
   - [The class-formation isomorphism](#53-the-class-formation-isomorphism)
   - [Definition of the finite Artin map](#54-definition-of-the-finite-artin-map)
   - [Norm limitation](#55-norm-limitation)
   - [The reciprocity theorem at finite level](#56-the-reciprocity-theorem-at-finite-level)
6. [Constructing enough abelian extensions](#6-constructing-enough-abelian-extensions)
   - [Why a separate existence construction is necessary](#61-why-a-separate-existence-construction-is-necessary)
   - [A formal module attached to a uniformizer](#62-a-formal-module-attached-to-a-uniformizer)
   - [Torsion points and Eisenstein polynomials](#63-torsion-points-and-eisenstein-polynomials)
   - [The Galois action on torsion](#64-the-galois-action-on-torsion)
   - [The norm group of the torsion extension](#65-the-norm-group-of-the-torsion-extension)
   - [Adding the unramified direction](#66-adding-the-unramified-direction)
   - [The existence theorem](#67-the-existence-theorem)
7. [The infinite reciprocity map](#7-the-infinite-reciprocity-map)
   - [Passage through finite quotients](#71-passage-through-finite-quotients)
   - [Continuity](#72-continuity)
   - [Density and failure of literal surjectivity](#73-density-and-failure-of-literal-surjectivity)
   - [Injectivity](#74-injectivity)
   - [Profinite completion](#75-profinite-completion)
   - [The reciprocity, existence, and norm theorems together](#76-the-reciprocity-existence-and-norm-theorems-together)
8. [Uniformizers, units, and ramification](#8-uniformizers-units-and-ramification)
   - [The unramified coordinate](#81-the-unramified-coordinate)
   - [Units are the abelian inertia group](#82-units-are-the-abelian-inertia-group)
   - [Why higher unit groups require upper numbering](#83-why-higher-unit-groups-require-upper-numbering)
   - [The unit and ramification theorem](#84-the-unit-and-ramification-theorem)
   - [Conductors](#85-conductors)
   - [Tame and wild pieces](#86-tame-and-wild-pieces)
9. [Functoriality in finite extensions](#9-functoriality-in-finite-extensions)
   - [Why directions are easy to reverse accidentally](#91-why-directions-are-easy-to-reverse-accidentally)
   - [Norm corresponds to Galois inclusion](#92-norm-corresponds-to-galois-inclusion)
   - [Multiplicative inclusion corresponds to transfer](#93-multiplicative-inclusion-corresponds-to-transfer)
   - [Towers and finite quotient diagrams](#94-towers-and-finite-quotient-diagrams)
   - [Base change and norm subgroups](#95-base-change-and-norm-subgroups)
10. [Explicit norm quotients and extension classes](#10-explicit-norm-quotients-and-extension-classes)
    - [Unramified extensions](#101-unramified-extensions)
    - [Totally tamely ramified cyclic extensions](#102-totally-tamely-ramified-cyclic-extensions)
    - [The three quadratic extensions for odd residue characteristic](#103-the-three-quadratic-extensions-for-odd-residue-characteristic)
    - [Formal-module layers](#104-formal-module-layers)
    - [Composita and intersections](#105-composita-and-intersections)
    - [Building an extension from congruence data](#106-building-an-extension-from-congruence-data)
11. [Continuous one-dimensional characters](#11-continuous-one-dimensional-characters)
    - [The exact topological statement](#111-the-exact-topological-statement)
    - [Finite-order characters and cyclic extensions](#112-finite-order-characters-and-cyclic-extensions)
    - [Unramified characters](#113-unramified-characters)
    - [Ramified characters and conductor](#114-ramified-characters-and-conductor)
    - [Characters in towers](#115-characters-in-towers)
12. [The local reciprocity dictionary](#12-the-local-reciprocity-dictionary)
    - [Fields and subgroups](#121-fields-and-subgroups)
    - [Multiplicative pieces and Galois pieces](#122-multiplicative-pieces-and-galois-pieces)
    - [Norm tests](#123-norm-tests)
    - [Functoriality at a glance](#124-functoriality-at-a-glance)
    - [Characters at a glance](#125-characters-at-a-glance)
    - [Conclusion](#126-conclusion)

## 1. The local reciprocity problem

### 1.1 What kind of local field is meant

The multiplicative group of a local field looks elementary: a valuation records an integer, reduction records a residue-field unit, and increasingly deep congruences record the remaining principal-unit data. The finite abelian extensions of the field look much less elementary. They include unramified extensions, tame radical extensions, wildly ramified extensions, and composites of all three. Local class field theory says that these two collections are nevertheless the same object viewed from opposite sides.

Throughout this book a **nonarchimedean local field** means a field $K$ complete for a nontrivial discrete valuation and having finite residue field. Thus $K$ is locally compact. We write

$$
v=v_K:K^\times\longrightarrow\mathbf Z,
\qquad \mathcal O=\mathcal O_K,
\qquad \mathfrak m=(\pi),
\qquad k=\mathcal O/\mathfrak m=\mathbf F_q.
$$

The valuation is normalized by $v(\pi)=1$. We use

$$
U^0=\mathcal O^\times,
\qquad U^n=1+\mathfrak m^n\quad(n\geq1).
$$

An algebraic closure $\overline K$ and a separable closure $K^s\subseteq\overline K$ are fixed. Since finite fields are perfect, every finite extension of $K$ has separable residue extension; every finite separable extension is an unramified extension followed by a totally ramified one. Purely inseparable finite extensions can occur when $K$ has equal characteristic, but class field theory concerns finite separable, and ultimately finite abelian, extensions.

The finiteness of $k$ is not decorative. It makes $\mathcal O$ compact, gives a canonical Frobenius on every finite residue extension, and forces finite-index subgroups of $K^\times$ to interact well with the topology. A complete discretely valued field with infinite residue field has much of the valuation theory developed earlier, but the reciprocity theorem in the form proved here is not a theorem about that broader class.

### 1.2 The classification one hopes for

For a finite extension $L/K$, the norm is a continuous homomorphism

$$
N_{L/K}:L^\times\longrightarrow K^\times.
$$

If $L/K$ is abelian, its norm image is an open subgroup of finite index. The first surprising assertion of local class field theory is the exact formula

$$
[K^\times:N_{L/K}(L^\times)]=[L:K].
$$

The second assertion reverses the construction: every open finite-index subgroup $H\subseteq K^\times$ is the norm group of a unique finite abelian extension $L/K$ inside $K^s$. Inclusion reverses direction:

$$
L_1\subseteq L_2
\quad\Longleftrightarrow\quad
N_{L_2/K}(L_2^\times)\subseteq N_{L_1/K}(L_1^\times).
$$

This resembles Galois theory, but the subgroup lives in the concrete abelian group $K^\times$, not in an already known Galois group. The bridge is a canonical isomorphism

$$
K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}
\operatorname{Gal}(L/K)
$$

for every finite abelian $L/K$. These finite maps are compatible as $L$ varies and assemble into the local reciprocity map

$$
\operatorname{rec}_K:K^\times\longrightarrow
G_K^{\mathrm{ab}}=\operatorname{Gal}(K^{\mathrm{ab}}/K).
$$

The target is profinite and therefore compact. The source is not: its valuation quotient is $\mathbf Z$. Consequently $\operatorname{rec}_K$ cannot be an isomorphism of topological groups onto the whole target. It is continuous and has dense image; after profinite completion it becomes an isomorphism. This distinction between density and surjectivity is one of the central topological points of the subject.

### 1.3 The reciprocity convention

Every finite unramified extension $L/K$ has a canonical **arithmetic Frobenius**

$$
\operatorname{Frob}_{L/K}:\bar x\longmapsto\bar x^q
$$

on its residue field, lifted uniquely to $L$. We normalize reciprocity by

$$
\operatorname{rec}_{L/K}(\pi)=\operatorname{Frob}_{L/K}
$$

for every uniformizer $\pi$ of $K$ and every finite unramified $L/K$. Equivalently, on the maximal unramified extension a uniformizer acts as arithmetic Frobenius. This will be called the **arithmetic normalization**.

Some authors use geometric Frobenius $\operatorname{Frob}^{-1}$. Their reciprocity map is the inverse of ours:

$$
\operatorname{rec}^{\mathrm{geom}}_K(x)
=\operatorname{rec}_K(x)^{-1}.
$$

Every formula involving norms, restriction, and transfer remains structurally the same after simultaneous inversion, but an isolated Frobenius formula changes direction. We will never use the unqualified word “Frobenius” where the direction matters.

### 1.4 Why the proof has several layers

The theorem joins topology, field extensions, and group cohomology, so no single calculation proves it. The argument will proceed through four mechanisms.

First, compactness shows that norm images are closed and helps identify their topology. Second, cyclic cohomology explains why a norm quotient is the natural degree-zero cohomology group and why Hilbert's Theorem 90 removes a neighboring obstruction. Third, the Brauer group of a local field supplies a canonical fundamental class of every finite Galois extension. Capping with that class turns the abstract abelianization of the Galois group into a norm quotient. Finally, explicit unramified and formal-module extensions show that enough abelian extensions exist to realize every open finite-index subgroup.

The order matters. Norm computations suggest reciprocity but cannot classify wild extensions by themselves. Cohomology produces the finite reciprocity maps but, without an existence construction, would not prove that all open subgroups arise. The explicit construction supplies that missing half rather than hiding it behind the name “existence theorem.”

## 2. The topology of the multiplicative group and its norm subgroups

### 2.1 Separating magnitude from units

The valuation exact sequence

$$
1\longrightarrow\mathcal O^\times
\longrightarrow K^\times
\xrightarrow{v}\mathbf Z
\longrightarrow0
$$

splits after choosing a uniformizer. Thus

$$
K^\times=\pi^{\mathbf Z}\times\mathcal O^\times.
$$

The splitting is not canonical: replacing $\pi$ by $u\pi$ changes it by a unit. The exact sequence is canonical, and that is enough for all invariant statements.

The unit group is compact. Reduction and the principal-unit filtration give

$$
\mathcal O^\times/U^1\cong k^\times,
\qquad
U^n/U^{n+1}\cong k^+\quad(n\geq1).
$$

Each $U^n$ is compact and open, the family $(U^n)$ is a neighborhood basis of $1$, and $\bigcap_nU^n=\{1\}$. Therefore

$$
\mathcal O^\times\cong\varprojlim_n(\mathcal O/\mathfrak m^n)^\times.
$$

This decomposition already predicts the three parts of reciprocity. The quotient $\mathbf Z$ controls the unramified direction. The finite group $k^\times$ controls tame residue-unit behavior. The pro-$p$ group $U^1$ controls wild ramification when $p=\operatorname{char}k$.

### 2.2 Open subgroups of finite index

The subgroups that can plausibly be norm groups must be topologically large. The following elementary criterion will later make the existence theorem concrete.

**Proposition 2.1.** For a subgroup $H\subseteq K^\times$, the following are equivalent.

1. $H$ is open and has finite index.
2. There exist integers $m,n\geq1$ such that
   $$
   \pi^{m\mathbf Z}U^n\subseteq H.
   $$
3. The quotient $K^\times/H$ is finite and discrete.

**Proof.** If $H$ is open, it contains some $U^n$. Its valuation image $v(H)$ is a subgroup of $\mathbf Z$, say $m\mathbf Z$ or $0$. Finite index rules out $0$, so choose $h\in H$ with $v(h)=m$. Write $h=\pi^m u$. Because the compact quotient $\mathcal O^\times/(H\cap\mathcal O^\times)$ is finite, some positive power of $u$ lies in $H\cap\mathcal O^\times$. Replacing $m$ by a multiple if necessary gives $\pi^m\in H$, hence condition 2. Conversely, $K^\times/(\pi^{m\mathbf Z}U^n)$ is finite, so condition 2 makes $H$ open and finite-index. The equivalence with 3 is the general fact that a subgroup is open precisely when its quotient is discrete; compactness of the unit part then supplies finiteness. $\square$

One cannot omit openness. The subgroup generated algebraically by a uniformizer and a dense proper subgroup of $\mathcal O^\times$ may have finite-looking algebraic features but is not a norm group of a finite extension, because finite-extension norm groups are closed. Nor can one classify extensions using all abstract finite-index subgroups without topology: in a profinite group, finite-index subgroups need not be open if no continuity hypothesis is imposed on arbitrary homomorphisms.

### 2.3 Norms and valuation coordinates

Let $L/K$ be finite, with residue degree $f=f(L/K)$. The norm valuation formula recalled from the extension theory is

$$
v_K(N_{L/K}x)=f\,v_L(x).
$$

Hence

$$
v_K(N_{L/K}(L^\times))=f\mathbf Z.
$$

The valuation coordinate contributes index $f$. What remains is the unit norm index:

$$
[K^\times:N_{L/K}(L^\times)]
=f\,[\mathcal O_K^\times:N_{L/K}(\mathcal O_L^\times)].
$$

To justify the formula, map both sides to $\mathbf Z/f\mathbf Z$. The kernel of the induced valuation map on the norm quotient is the quotient of $\mathcal O_K^\times$ by the unit norms. A norm of valuation zero comes from an element of $L$ of valuation zero, so no additional intersection appears.

For an unramified extension of degree $d$, norms are surjective on units and

$$
N_{L/K}(L^\times)=\pi^{d\mathbf Z}\mathcal O_K^\times.
$$

Thus its norm quotient is generated by the class of a uniformizer. For a totally ramified extension, $f=1$, so the valuation of a norm is unrestricted and every obstruction lies among the units. This clean contrast will reappear as the decomposition of the Galois group into an unramified quotient and inertia.

### 2.4 Norm groups are open and closed

The norm map is continuous. Its restriction

$$
N_{L/K}:\mathcal O_L^\times\longrightarrow\mathcal O_K^\times
$$

has compact domain, so its image is compact and therefore closed. To see openness, it is enough to show that sufficiently deep principal units of $K$ are norms.

**Proposition 2.2.** For every finite separable extension $L/K$, there exists $c\geq1$ such that

$$
U_K^c\subseteq N_{L/K}(U_L^1).
$$

**Proof strategy.** Far enough down the filtration, the multiplicative norm is controlled by the additive trace. The trace image is a nonzero fractional ideal of $K$, hence contains a deep power of $\mathfrak m_K$. Successive approximation then corrects a desired norm one layer at a time.

Choose $a\in L$ with $\operatorname{Tr}_{L/K}(a)=1$, possible because $L/K$ is separable. Multiplying by a sufficiently large power of $\pi_K$ shows that for some $r$,

$$
\mathfrak m_K^r\subseteq \operatorname{Tr}_{L/K}(\mathfrak m_L).
$$

More generally, after increasing depths linearly, every sufficiently small target $y$ has a preimage $x$ small enough that all quadratic terms in

$$
N(1+x)=1+\operatorname{Tr}(x)+O(x^2)
$$

lie at strictly greater depth than $y$. Start with $z\in U_K^c$ and choose $x_1$ so that $N(1+x_1)\equiv z$ modulo a deeper unit group. Divide the remaining error by this norm and repeat. The error depth tends to infinity, while the product $\prod_i(1+x_i)$ converges in $U_L^1$. Continuity of the norm gives norm $z$. $\square$

For a finite inseparable extension, pass through the maximal separable subextension and use the explicit power form of a purely inseparable norm. Local reciprocity itself concerns separable extensions, so the proposition above is the form needed later.

It follows that $N_{L/K}(L^\times)$ is open. Its valuation image has finite index and its unit image contains $U_K^c$, so the whole norm group has finite index. It is also closed: the unit part is compact, and the valuation separates its translates into a discrete family.

### 2.5 The index question

Topology proves finiteness but not the correct index. Direct unit calculations settle special cases, yet wild ramification defeats any formula depending only on $e$ and $f$. The desired equality

$$
[K^\times:N_{L/K}(L^\times)]=[L:K]
$$

is in fact false for arbitrary nonabelian $L/K$: the correct degree is that of its maximal abelian subextension. Even for a cyclic wildly ramified extension, direct calculation on all unit layers is possible only after developing substantial ramification machinery.

The way forward is to recognize $K^\times/NL^\times$ as a cohomology group and then compute it through a canonical invariant. This shifts the problem from tracking every unit norm separately to understanding one two-dimensional obstruction.

## 3. Cyclic extensions, norms, and Hilbert 90

### 3.1 Why cyclic extensions come first

Finite abelian groups are built from cyclic quotients. More importantly, a cyclic group has a two-periodic resolution, so kernels and cokernels of the norm alternate in a transparent way. This makes cyclic extensions the testing ground in which the form of reciprocity becomes unavoidable.

Let $L/K$ be cyclic of degree $n$, with

$$
G=\langle\sigma\rangle.
$$

Write the group ring operators

$$
D=\sigma-1,
\qquad
N_G=1+\sigma+\cdots+\sigma^{n-1}.
$$

They satisfy $DN_G=N_GD=0$. On the multiplicative group $L^\times$, the operator $D$ sends $y$ to $\sigma(y)/y$, while $N_G$ is the field norm.

### 3.2 Hilbert's Theorem 90 with proof

The equation $N_{L/K}(x)=1$ is necessary for $x$ to have the form $\sigma(y)/y$. Hilbert's Theorem 90 says it is sufficient.

**Theorem 3.1 (Hilbert 90).** If $L/K$ is finite cyclic with generator $\sigma$, then

$$
\ker(N_{L/K}:L^\times\to K^\times)
=\left\{\frac{\sigma(y)}y:y\in L^\times\right\}.
$$

**Proof strategy.** Construct $y$ by averaging with coefficients twisted by successive partial products of $x$. The norm-one condition makes the final index wrap around correctly.

Let $x\in L^\times$ have norm $1$, and set

$$
x_0=1,
\qquad
x_i=x\sigma(x)\cdots\sigma^{i-1}(x)\quad(1\leq i<n).
$$

For $a\in L$, put

$$
y_a=\sum_{i=0}^{n-1}x_i\sigma^i(a).
$$

Dedekind's independence of distinct field embeddings implies that the $K$-linear operator $a\mapsto y_a$ is not identically zero: its coefficients $x_i$ are not all zero. Choose $a$ with $y_a\ne0$. Since $x_n=N(x)=1$, shifting indices gives

$$
x\sigma(y_a)=y_a.
$$

Thus $x=y_a/\sigma(y_a)$. Replacing $y_a$ by $y_a^{-1}$ gives $x=\sigma(y)/y$ in the displayed convention. $\square$

This theorem is exactly the vanishing

$$
H^1(G,L^\times)=0.
$$

It is not a norm-surjectivity theorem. It describes the kernel of the norm, not its image. Confusing those two roles would incorrectly predict that every element of $K^\times$ is a norm.

### 3.3 Tate cohomology of a cyclic group

For a $G$-module $A$ written additively, cyclic Tate cohomology is

$$
\widehat H^0(G,A)=A^G/N_GA,
$$

and

$$
\widehat H^{-1}(G,A)=\ker N_G/DA.
$$

The periodic resolution

$$
\cdots\xrightarrow{N_G}\mathbf Z[G]
\xrightarrow{D}\mathbf Z[G]
\xrightarrow{N_G}\mathbf Z[G]
\xrightarrow{D}\mathbf Z[G]\longrightarrow\mathbf Z\longrightarrow0
$$

shows that $\widehat H^{r+2}(G,A)\cong\widehat H^r(G,A)$ for every integer $r$.

For $A=L^\times$, written multiplicatively,

$$
\widehat H^0(G,L^\times)=K^\times/N_{L/K}(L^\times),
$$

while Hilbert 90 gives

$$
\widehat H^{-1}(G,L^\times)=0.
$$

Periodicity therefore yields

$$
H^1(G,L^\times)=0,
\qquad
H^2(G,L^\times)\cong K^\times/N_{L/K}(L^\times).
$$

The second isomorphism can be made concrete through cyclic algebras.

### 3.4 Cyclic algebras

Given $a\in K^\times$, define the **cyclic algebra**

$$
(L/K,\sigma,a)
$$

to be the $K$-algebra generated by $L$ and a symbol $z$ subject to

$$
z^n=a,
\qquad
zx=\sigma(x)z\quad(x\in L).
$$

As a left $L$-vector space it has basis $1,z,\dots,z^{n-1}$. Its dimension over $K$ is $n^2$, its center is $K$, and after scalar extension to $L$ it becomes $M_n(L)$. Thus it is a central simple algebra split by $L$.

Why does the parameter $a$ occur only modulo norms? If $b\in L^\times$ and one replaces $z$ by $bz$, then

$$
(bz)^n=N_{L/K}(b)a.
$$

Conversely, comparing two such crossed-product presentations shows that isomorphic cyclic algebras have parameters in the same norm coset. In particular,

$$
(L/K,\sigma,a)\text{ is split}
\quad\Longleftrightarrow\quad
a\in N_{L/K}(L^\times).
$$

For the nontrivial direction, a splitting provides a one-dimensional $L$-eigenspace in the natural module. The action of $z$ carries it around the $\sigma$-conjugate eigenspaces; multiplying the transition scalars around the cycle expresses $a$ as their norm. This is the same telescoping mechanism as Hilbert 90.

Tensor product adds parameters:

$$
(L/K,\sigma,a)\otimes_K(L/K,\sigma,b)
\sim(L/K,\sigma,ab),
$$

where $\sim$ denotes equality in the Brauer group. Hence

$$
K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}
\operatorname{Br}(L/K),
\qquad
a\longmapsto[(L/K,\sigma,a)],
$$

where $\operatorname{Br}(L/K)$ is the kernel of restriction $\operatorname{Br}(K)\to\operatorname{Br}(L)$. The generator matters: replacing $\sigma$ by $\sigma^r$ changes the numerical invariant by the inverse of $r$ modulo $n$. This dependence is precisely why Frobenius normalization must be fixed.

### 3.5 The unramified cyclic computation

Let $L/K$ be unramified of degree $n$ and let $\sigma=\operatorname{Frob}_{L/K}$ be arithmetic Frobenius. Units are norms and valuations of norms are multiples of $n$, so

$$
K^\times/NL^\times\cong\mathbf Z/n\mathbf Z,
$$

generated by the class of $\pi$. The cyclic algebra

$$
(L/K,\operatorname{Frob},\pi)
$$

is therefore the basic nontrivial class split by $L$.

This computation fixes the orientation for everything that follows: the class of $\pi$ must correspond to arithmetic Frobenius, not its inverse. Once this one case is fixed, compatibility in towers determines the normalization of all fundamental classes.

## 4. The Brauer invariant of a local field

### 4.1 Why central simple algebras enter reciprocity

A norm quotient varies with the extension. To compare different extensions, we need a single ambient group in which all norm obstructions live and restriction through towers has a computable effect. The Brauer group provides exactly that setting.

A finite-dimensional $K$-algebra $A$ is **central simple** if its center is $K$ and it has no nontrivial two-sided ideals. Every such algebra is isomorphic to a matrix algebra $M_r(D)$ over a central division algebra $D$, unique up to isomorphism. Two central simple algebras are Brauer equivalent when their division algebras agree. Tensor product defines the abelian group $\operatorname{Br}(K)$; the inverse of $[A]$ is the class of the opposite algebra.

The central fact for a nonarchimedean local field is

$$
\operatorname{inv}_K:\operatorname{Br}(K)
\xrightarrow{\sim}\mathbf Q/\mathbf Z.
$$

We now construct this map locally. No global reciprocity theorem is used.

### 4.2 Valuations on division algebras

Let $D$ be a central division algebra over $K$ of degree $d$, so $[D:K]=d^2$. The reduced norm

$$
\operatorname{Nrd}_{D/K}:D^\times\to K^\times
$$

extends the ordinary determinant after passing to a splitting field. Define

$$
w_D(x)=\frac1d\,v_K(\operatorname{Nrd}(x)).
$$

The multiplicativity of reduced norm makes $w_D$ additive. The characteristic polynomial identities for $x+y$ imply the ultrametric inequality, so $w_D$ is a valuation on the skew field $D$. Its valuation ring

$$
\mathcal O_D=\{x:w_D(x)\geq0\}
$$

has a unique maximal two-sided ideal $\mathfrak P_D$, and the quotient

$$
\overline D=\mathcal O_D/\mathfrak P_D
$$

is a finite division ring. Wedderburn's theorem makes it a finite field.

The value group $w_D(D^\times)$ is a subgroup of $\frac1d\mathbf Z$ containing $\mathbf Z$. Let its index over $\mathbf Z$ be $e_D$, and let

$$
f_D=[\overline D:k].
$$

A lattice-length argument, parallel to the field equality $[L:K]=ef$ but using the full $K$-dimension of the skew field, gives

$$
d^2=e_Df_D.
$$

Here is the count in detail. Choose $x_1,\ldots,x_{e_D}$ whose values represent the cosets of $w_D(D^\times)/\mathbf Z$, and choose $y_1,\ldots,y_{f_D}\in\mathcal O_D$ lifting a $k$-basis of $\overline D$. After multiplying each $x_i$ by a power of $\pi$, assume its value lies in $[0,1)$. If

$$
\sum_{i,j}a_{ij}x_iy_j=0,
\qquad a_{ij}\in K,
$$

then terms belonging to different $i$ have values in different cosets modulo $\mathbf Z$. Among the terms in the least coset, scaling to value zero and reducing gives a $k$-linear relation among the residues of the $y_j$. Hence every coefficient in that coset vanishes; induction proves independence. Conversely, subtracting an appropriate $K$-linear combination of the $x_iy_j$ cancels the leading residue of any $z\in D$. Iteration raises the value without bound, and completeness gives a convergent expansion. Thus the $e_Df_D$ products form a $K$-basis and $[D:K]=e_Df_D$.

Centrality sharpens the equality. Conjugation by a value-coset representative preserves $\mathcal O_D$ and induces an automorphism of the finite field $\overline D$. This gives an injective homomorphism

$$
w_D(D^\times)/\mathbf Z
\longrightarrow\operatorname{Gal}(\overline D/k).
$$

For injectivity, an element acting trivially on $\overline D$ can be corrected successively by value-zero units until it commutes with every lift of $\overline D$; completeness makes the correction converge, and the resulting element lies in $K^\times$, so its value coset is trivial. The fixed field of the image is $k$. Indeed, a fixed residue element lifts by Hensel's lemma to an element commuting with the value-zero lifts and with a value parameter; these generate $D$, so the lift is central and belongs to $K$. Since $\operatorname{Gal}(\overline D/k)$ is cyclic, an image with fixed field $k$ is the whole group. Hence

$$
e_D=f_D.
$$

Together with $d^2=e_Df_D$, this gives

$$
e_D=f_D=d.
$$

Choose a primitive element of $\overline D/k$ and lift its separable minimal polynomial to $\mathcal O[T]$. Newton iteration takes place inside the complete ring $\mathcal O_D$ because the derivative is a unit and the coefficients are central. It produces a root whose field $E\subset D$ is unramified of degree $d$. Since $[E:K]=d$ equals the degree of $D$, $E$ is a maximal commutative subfield and its centralizer in $D$ is $E$.

A parameter $\Pi_D$ of least positive $D$-value normalizes $E$ and conjugates it by a generator of $\operatorname{Gal}(E/K)$, hence by $F^s$ for some $s$ prime to $d$, where $F$ is arithmetic Frobenius. Since this conjugation has order $d$, $\Pi_D^d$ centralizes $E$; it also commutes with $\Pi_D$, so it is central. Its value is one, and therefore $\Pi_D^d=c\pi$ for $c\in\mathcal O^\times$. Replacing $\Pi_D$ by $b\Pi_D$, with $b\in E^\times$, multiplies its $d$th power by $N_{E/K}(b)$. The unramified unit norm is surjective, so choose $b$ with norm $c^{-1}$. Then

$$
\Pi_D^d=\pi.
$$

The elements $1,\Pi_D,\ldots,\Pi_D^{d-1}$ are linearly independent over $E$ by their distinct value cosets and already account for dimension $d^2$. Consequently

$$
D\cong(E/K,F^s,\pi).
$$

If $r$ is inverse to $s$ modulo $d$, the same Brauer class is represented as $(E/K,F,\pi^r)$; replacing the crossed-product generator verifies this, with any extra factor $\pi^d$ absorbed as a norm. This is the local cyclic presentation of every central division algebra.

### 4.3 Unramified splitting and the invariant

Every central division algebra over $K$ is split by some finite unramified extension. To see this from the preceding structure, enlarge the residue field until it contains a maximal subfield of the residue division algebra and until the Frobenius conjugation cycle closes. The unramified lift then gives a maximal commutative subfield of degree $d$; a central simple algebra containing such a separable field is split after scalar extension to it.

Let $K_d/K$ be the unramified extension of degree $d$, with arithmetic Frobenius $F$. For $r\in\mathbf Z$, put

$$
A_{r,d}=(K_d/K,F,\pi^r).
$$

Its Brauer class depends only on $r$ modulo $d$, because $N_{K_d/K}(\pi)=\pi^d$ up to a unit and every unit is a norm. Define

$$
\operatorname{inv}_K(A_{r,d})=\frac rd\pmod{\mathbf Z}.
$$

If the same class is represented with denominator $md$, unramified base change and the tower relation replace $r/d$ by $mr/(md)$, so the value is independent of the presentation. Tensor products add the fractions. The splitting criterion says $A_{r,d}$ is split exactly when $d\mid r$, exactly when its proposed invariant is zero.

When $\gcd(r,d)=1$, the algebra $A_{r,d}$ is visibly a division algebra. Write its elements uniquely as

$$
x=x_0+x_1z+\cdots+x_{d-1}z^{d-1},
\qquad x_i\in K_d,
$$

and set

$$
w(x)=\min_i\left(v_{K_d}(x_i)+\frac{ri}{d}\right).
$$

The fractional parts $ri/d$ are distinct modulo $\mathbf Z$, so a nonzero sum has a unique least-valued term. In a product, the product of the two least terms remains uniquely least after using $zx=F(x)z$ and $z^d=\pi^r$. Hence $w(xy)=w(x)+w(y)$ and there are no zero divisors. A finite-dimensional central simple algebra without zero divisors is a division algebra. If $g=\gcd(r,d)$, the same argument after reducing the fraction shows that the underlying division algebra has degree $d/g$; the invariant is therefore naturally the reduced fraction $r/d$.

**Theorem 4.1 (local invariant theorem).** The preceding construction gives a canonical isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)\xrightarrow{\sim}\mathbf Q/\mathbf Z.
$$

For every finite extension $L/K$ of degree $n$,

$$
\operatorname{inv}_L(\operatorname{res}_{L/K}\alpha)
=n\operatorname{inv}_K(\alpha).
$$

**Proof.** Surjectivity follows because $A_{r,d}$ realizes $r/d$. The cyclic presentation just proved shows that every central division algebra has one of these classes. If its invariant is zero, the parameter is a norm and the cyclic splitting criterion makes it a matrix algebra; hence the invariant is injective.

It remains to verify restriction. First suppose $L/K$ is unramified of degree $m$. In $K_d\otimes_KL$, the common unramified part produces $g=\gcd(d,m)$ equal field factors. On each factor the relative arithmetic Frobenius is $F^m$, and rewriting it with the standard generator multiplies the numerator of $r/d$ by $m$. The matrix multiplicity from the $g$ factors does not change the Brauer class. Hence

$$
\operatorname{inv}_L(\operatorname{res}A_{r,d})=m\frac rd.
$$

Now suppose $L/K$ is totally ramified of degree $e$. It is linearly disjoint from $K_d$, so $LK_d/L$ remains unramified of degree $d$ with the same Frobenius. Write $\pi=u\pi_L^e$. The unit $u$ is a norm from the unramified extension $LK_d/L$, so the restricted cyclic algebra has parameter equivalent to $\pi_L^{er}$. Its invariant is $er/d$. Every finite extension is an unramified stage followed by a totally ramified stage, and multiplication of the two factors gives $[L:K]r/d$. $\square$

The proof also gives the corestriction formula

$$
\operatorname{inv}_K(\operatorname{cor}_{L/K}\beta)
=\operatorname{inv}_L(\beta).
$$

Indeed, restriction followed by corestriction is multiplication by $[L:K]$ on $\operatorname{Br}(K)$, and the displayed formulas agree on the generators $A_{r,d}$.

### 4.4 Relative Brauer groups and the norm index

Let $L/K$ be finite of degree $n$. The restriction formula shows that

$$
\operatorname{Br}(L/K)
=\ker(\operatorname{Br}(K)\to\operatorname{Br}(L))
\xrightarrow{\operatorname{inv}_K}
\frac1n\mathbf Z/\mathbf Z.
$$

Both inclusions are equalities: every class of invariant $r/n$ is split by the unramified extension of degree $n$, hence by any degree-$n$ extension after applying the restriction formula, since its invariant becomes $r=0$. Thus

$$
|\operatorname{Br}(L/K)|=n.
$$

When $L/K$ is cyclic, cyclic algebras identify this group with $K^\times/NL^\times$. We obtain the cyclic norm-index theorem:

**Theorem 4.2.** If $L/K$ is cyclic of degree $n$, then

$$
[K^\times:N_{L/K}(L^\times)]=n.
$$

This theorem includes wildly ramified cyclic extensions without computing their unit norms one layer at a time. The wild information is still present; it has been compressed into the invariant of a central simple algebra.

### 4.5 The fundamental class

Let $L/K$ now be finite Galois with group $G$ and degree $n$, not necessarily abelian. The relative Brauer group is canonically

$$
\operatorname{Br}(L/K)\cong H^2(G,L^\times).
$$

Under the invariant map it is cyclic of order $n$. The unique class

$$
u_{L/K}\in H^2(G,L^\times)
$$

with

$$
\operatorname{inv}_K(u_{L/K})=\frac1n
$$

is the **local fundamental class**.

Its normalization is compatible in towers. If $K\subseteq M\subseteq L$, restriction and corestriction of the fundamental classes differ by exactly the degree factors dictated by the invariant formulas. In an unramified cyclic extension, $u_{L/K}$ is represented by

$$
(L/K,\operatorname{Frob}_{L/K},\pi).
$$

Thus the abstract fraction $1/n$ retains the arithmetic Frobenius orientation chosen in Chapter 1.

## 5. From the fundamental class to finite reciprocity

### 5.1 Why abelianization appears

For a nonabelian Galois extension $L/K$, a homomorphism from the abelian group $K^\times$ cannot recover the whole group $G=\operatorname{Gal}(L/K)$. It can recover at most

$$
G^{\mathrm{ab}}=G/[G,G].
$$

The corresponding fixed field is the maximal abelian subextension

$$
L^{\mathrm{ab}/K}=L^{[G,G]}.
$$

The finite reciprocity theorem should therefore have the form

$$
K^\times/N_{L/K}(L^\times)\cong G^{\mathrm{ab}}.
$$

This is stronger than the cyclic norm-index theorem and immediately implies norm limitation: the norm group of $L$ depends only on its maximal abelian subextension.

The bridge is a cap product with $u_{L/K}$. We pause to explain why this operation has precisely the right source and target.

### 5.2 Tate homology in degree minus two

Take a complete resolution of the trivial $G$-module $\mathbf Z$. Its negative-degree cohomology is group homology shifted by one. In particular,

$$
\widehat H^{-2}(G,\mathbf Z)=H_1(G,\mathbf Z).
$$

The first homology group of a group is its abelianization:

$$
H_1(G,\mathbf Z)\cong G^{\mathrm{ab}}.
$$

Concretely, the bar resolution sends an element $g\in G$ to the one-chain $[g]$. The boundary relation

$$
[gh]=[g]+[h]
$$

holds in homology, and commutators vanish; this gives the map $G^{\mathrm{ab}}\to H_1(G,\mathbf Z)$. Reversing the construction proves it is an isomorphism.

The fundamental class $u\in H^2(G,L^\times)$ permits cap product

$$
-\frown u:
\widehat H^r(G,\mathbf Z)
\longrightarrow
\widehat H^{r+2}(G,L^\times).
$$

At $r=-2$ its target is

$$
\widehat H^0(G,L^\times)
=(L^\times)^G/N_{L/K}(L^\times)
=K^\times/N_{L/K}(L^\times).
$$

Thus the desired two groups occur naturally on opposite sides of the cap product.

### 5.3 The class-formation isomorphism

**Theorem 5.1 (fundamental-class isomorphism).** Let $L/K$ be finite Galois with group $G$. Capping with the local fundamental class gives isomorphisms

$$
\widehat H^r(G,\mathbf Z)
\xrightarrow{\sim}
\widehat H^{r+2}(G,L^\times)
$$

for every integer $r$.

The theorem is sometimes summarized by saying that $(G,L^\times)$ is a local class formation. The precise induction device is the following Tate–Nakayama lemma.

**Lemma 5.2 (Tate–Nakayama induction).** Let $C$ be a $G$-module and $u\in H^2(G,C)$. Suppose that for every subgroup $H\subseteq G$:

1. $H^1(H,C)=0$;
2. $H^2(H,C)$ is cyclic of order $|H|$;
3. $\operatorname{res}^G_H(u)$ generates $H^2(H,C)$.

Then cap product with $u$ gives

$$
\widehat H^r(H,\mathbf Z)
\xrightarrow{\sim}
\widehat H^{r+2}(H,C)
$$

for every $H$ and every integer $r$.

**Proof.** Represent $u$ by a two-extension of $G$-modules

$$
0\longrightarrow C\longrightarrow A
\longrightarrow \mathbf Z[G]
\xrightarrow{\varepsilon}\mathbf Z\longrightarrow0.
$$

Such a representative is obtained by taking the augmentation sequence, viewing $u$ as an extension of its augmentation kernel by $C$, and splicing. For a subgroup $H$, the connecting map across this two-extension is exactly cap product with $\operatorname{res}^G_H(u)$.

The module $\mathbf Z[G]$ is induced from the trivial group when restricted to $H$, hence has zero Tate cohomology. The long exact sequences attached to the two-extension show the following. At degree $-1$, both

$$
\widehat H^{-1}(H,\mathbf Z)=0
\quad\text{and}\quad
H^1(H,C)=0.
$$

At degree $0$ the connecting map is

$$
\mathbf Z/|H|\mathbf Z
\longrightarrow H^2(H,C),
\qquad
1\longmapsto\operatorname{res}^G_H(u),
$$

and is an isomorphism by assumptions 2 and 3. A diagram chase in the two long exact sequences therefore gives

$$
\widehat H^0(H,A)=\widehat H^1(H,A)=0
$$

for every subgroup $H$.

We use the elementary cohomological-triviality criterion: a $G$-module $A$ with $\widehat H^0(H,A)=\widehat H^1(H,A)=0$ for every subgroup $H$ has $\widehat H^r(H,A)=0$ for all $r$. To prove the criterion, take a surjection from a permutation module $P$ onto $A$. Its kernel $B$ has $\widehat H^{r+1}(H,B)\cong\widehat H^r(H,A)$ because $P$ is cohomologically trivial. The two assumed consecutive vanishings pass from $A$ to $B$ shifted by one. Repeating in positive and negative directions by kernels and cokernels of permutation modules moves any desired degree into one of the two vanishing degrees. Thus $A$ is cohomologically trivial.

With the Tate cohomology of both middle modules zero, the long exact sequence of the two-extension makes every connecting map an isomorphism. These connecting maps are cap products with $u$, proving the lemma. $\square$

**Proof of Theorem 5.1.** Let $H\subseteq G$ and put $E=L^H$. Hilbert 90 gives

$$
H^1(H,L^\times)=0.
$$

The local invariant identifies $H^2(H,L^\times)=\operatorname{Br}(L/E)$ with a cyclic group of order $|H|$. Moreover restriction multiplies invariants by $[E:K]$, so

$$
\operatorname{inv}_E(\operatorname{res}^G_Hu_{L/K})
=[E:K]\frac1{[L:K]}=\frac1{|H|}.
$$

Thus the restricted class is a generator for every subgroup, and Lemma 5.2 applies. $\square$

The proof explains why merely knowing that $H^2(G,L^\times)$ is cyclic is not enough. The restriction of its chosen generator must be normalized correctly at every subgroup. The invariant $1/[L:K]$ was designed precisely to provide that compatibility.

### 5.4 Definition of the finite Artin map

At $r=-2$, Theorem 5.1 gives an isomorphism

$$
G^{\mathrm{ab}}\xrightarrow{\sim}K^\times/N_{L/K}(L^\times).
$$

We define the **finite local Artin map** to be its inverse:

$$
\operatorname{rec}_{L/K}:K^\times
\longrightarrow G^{\mathrm{ab}}.
$$

Its kernel is $N_{L/K}(L^\times)$, and it induces

$$
K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}G^{\mathrm{ab}}.
$$

If $L/K$ is abelian, the target is $G$ itself. If $L/K$ is unramified, the cyclic-algebra normalization in Chapter 4 gives

$$
\operatorname{rec}_{L/K}(\pi)=\operatorname{Frob}_{L/K}.
$$

This verifies, rather than merely declares, the arithmetic convention.

The map is continuous because its kernel is an open norm group and its target is finite discrete. It is surjective because the induced map on the quotient is an isomorphism. Thus at every finite level there is genuine surjectivity; only at the infinite level will surjectivity become density.

### 5.5 Norm limitation

Let $M=L^{[G,G]}$ be the maximal abelian subextension of a finite Galois extension $L/K$. Since

$$
G^{\mathrm{ab}}\cong\operatorname{Gal}(M/K),
$$

finite reciprocity for $L$ and $M$ gives the same quotient of $K^\times$. Their kernels are therefore equal.

**Theorem 5.3 (norm limitation).** For a finite Galois extension $L/K$ with maximal abelian subextension $M/K$,

$$
N_{L/K}(L^\times)=N_{M/K}(M^\times).
$$

In particular,

$$
[K^\times:N_{L/K}(L^\times)]=[M:K]=|G^{\mathrm{ab}}|.
$$

The statement would be false with $[L:K]$ on the right when $G$ is nonabelian. For example, if $G$ is perfect, then $M=K$ and every element of $K^\times$ is a norm from $L$, despite $L\ne K$. This is a useful counterexample to the tempting claim that every finite extension has norm index equal to its degree.

For a finite separable extension $E/K$ that is not Galois, one may take a Galois closure $L$. The norm group of $E$ is not determined by an abelian subextension of $E$ through so simple a formula; norm limitation is a theorem about a Galois extension and its commutator fixed field.

### 5.6 The reciprocity theorem at finite level

We can now state the finite theorem in its cleanest form.

**Theorem 5.4 (finite local reciprocity).** If $L/K$ is finite abelian, there is a unique isomorphism

$$
\operatorname{rec}_{L/K}:K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}\operatorname{Gal}(L/K)
$$

compatible with the fundamental classes and satisfying

$$
\operatorname{rec}_{L/K}(\pi)=\operatorname{Frob}_{L/K}
$$

when $L/K$ is unramified. It is compatible with quotients and towers in the precise forms proved in Chapter 9.

The uniqueness clause should be read with all compatibility conditions included. A single cyclic quotient admits automorphisms that could change a chosen generator. The unramified Frobenius normalization and functoriality across all finite Galois extensions remove that ambiguity.

## 6. Constructing enough abelian extensions

### 6.1 Why a separate existence construction is necessary

Finite reciprocity starts with an extension and computes its norm quotient. The classification theorem asks the converse: given $H\subseteq K^\times$, where does the corresponding field come from? Cohomology alone does not display enough fields. We now construct a cofinal family of finite abelian extensions whose norm groups are

$$
\pi^{m\mathbf Z}U^n.
$$

The unramified factor realizes $\pi^{m\mathbf Z}$; a formal $\mathcal O$-module realizes $U^n$. Together they dominate every open finite-index subgroup by Proposition 2.1.

This is the one place where a power-series construction genuinely solves the existence problem, so it will be developed as part of the proof rather than mentioned as an alternative theory.

### 6.2 A formal module attached to a uniformizer

A one-dimensional commutative formal group law over $\mathcal O$ is a series

$$
F(X,Y)\in\mathcal O[[X,Y]]
$$

with $F(X,0)=X$, $F(0,Y)=Y$, symmetry, and associativity under formal substitution. Its points in $\mathfrak m_E$ for a finite extension $E/K$ form a group by $x+_F y=F(x,y)$, because the series converge there.

We need more: every $a\in\mathcal O$ should act by an endomorphism $[a]_F(T)$, compatibly with addition and multiplication in $\mathcal O$. Choose a power series

$$
f(T)\in\mathcal O[[T]]
$$

satisfying

$$
f(T)\equiv\pi T\pmod{T^2},
\qquad
f(T)\equiv T^q\pmod\pi.
$$

The simplest example is $f(T)=\pi T+T^q$.

**Theorem 6.1 (formal-module construction).** There is a unique formal group law $F_f$ over $\mathcal O$ and, for every $a\in\mathcal O$, a unique endomorphism $[a]_f(T)$ such that

$$
[\pi]_f(T)=f(T),
\qquad
[a]_f(T)\equiv aT\pmod{T^2},
$$

and

$$
[a]_f\circ f=f\circ[a]_f.
$$

Moreover $a\mapsto[a]_f$ is a ring homomorphism into the endomorphism ring of $F_f$.

The construction rests on a coefficient lemma that is useful well beyond this theorem.

**Lemma 6.2 (integral intertwining recursion).** Let $f,g\in\mathcal O[[T]]$ both satisfy the two displayed congruences, and let $a\in\mathcal O$. There is a unique $h(T)\in\mathcal O[[T]]$ such that

$$
h(T)\equiv aT\pmod{T^2},
\qquad
h\circ f=g\circ h.
$$

There is likewise a unique $H(X,Y)\in\mathcal O[[X,Y]]$ with linear part $X+Y$ satisfying

$$
H(f(X),f(Y))=f(H(X,Y)).
$$

**Proof.** Suppose the coefficients of $h$ through degree $r-1$ have been chosen and the functional equation holds modulo $T^r$. Let $cT^r$ be the degree-$r$ part of $h(f(T))-g(h(T))$. Replacing $h$ by $h+bT^r$ changes that coefficient by

$$
b(\pi^r-\pi).
$$

Indeed, the first composite gains $b(\pi T)^r$ at degree $r$, while in the second only the linear term $\pi T$ of $g$ can see the new coefficient at that degree. Reduction modulo $\pi$ gives

$$
\overline h(T^q)-\overline h(T)^q=0,
$$

because every coefficient of $\overline h$ lies in $k=\mathbf F_q$. Hence $c\in\pi\mathcal O$. Since

$$
\pi^r-\pi=\pi(\pi^{r-1}-1)
$$

is $\pi$ times a unit for $r\geq2$, there is a unique $b\in\mathcal O$ that kills the error. Induction constructs $h$ and proves uniqueness.

For $H$, order monomials by total degree. If all terms below degree $r$ have been chosen, correcting the coefficient of $X^iY^j$, where $i+j=r$, again changes the error by $b(\pi^r-\pi)$. Modulo $\pi$, every partial series satisfies

$$
\overline H(X^q,Y^q)=\overline H(X,Y)^q,
$$

so the error coefficient is divisible by $\pi$. The same division completes the recursion. $\square$

**Proof of Theorem 6.1.** Apply the two-variable part of the lemma and call the result $F_f$. The series $F_f(X,0)$ and $X$ have the same linear term and satisfy the same intertwining equation, so uniqueness makes them equal; likewise $F_f(0,Y)=Y$. Symmetry follows by comparing $F_f(X,Y)$ and $F_f(Y,X)$. The two series

$$
F_f(F_f(X,Y),Z),
\qquad
F_f(X,F_f(Y,Z))
$$

have linear part $X+Y+Z$ and both intertwine coordinatewise application of $f$ with $f$. The identical recursion in three variables makes them equal. Thus $F_f$ is an associative commutative formal group law.

Apply the one-variable part with $g=f$ and linear coefficient $a$ to obtain $[a]_f$. Uniqueness gives $[\pi]_f=f$. Both $[a]_f\circ[b]_f$ and $[ab]_f$ commute with $f$ and have linear term $abT$, so they agree. Likewise

$$
F_f([a]_f(T),[b]_f(T))=[a+b]_f(T).
$$

Finally, $[a]_f(F_f(X,Y))$ and $F_f([a]_f(X),[a]_f(Y))$ have the same linear part and satisfy the same two-variable intertwining equation, so uniqueness identifies them. These identities prove the ring laws and show that every $[a]_f$ is an endomorphism of $F_f$. $\square$

Everything here is a formal identity; no convergence of a logarithm has been assumed. In either equal or mixed characteristic the series may be evaluated on elements of positive valuation in a finite extension $E/K$, because monomials of increasing degree tend to zero. Completeness of $E$ gives convergence. Evaluation on elements of valuation zero is not asserted: the formal group naturally lives on $\mathfrak m_E$.

Different choices of $f$ produce isomorphic towers of fields, although not canonically without auxiliary choices. The uniformizer enters the construction; the resulting maximal totally ramified abelian extension will be intrinsic.

This is the Lubin–Tate formal-module construction. Here it is not an excursion: its torsion fields provide the cofinal ramified extensions needed in the proof of local existence.

### 6.3 Torsion points and Eisenstein polynomials

For $n\geq1$, define the $\pi^n$-torsion set

$$
F_f[\pi^n]
=\{x\in\mathfrak m_{\overline K}:[\pi^n]_f(x)=0\}.
$$

Put $S_n(T)=[\pi^n]_f(T)=f^{\circ n}(T)$. Induction gives

$$
S_n(T)\equiv T^{q^n}\pmod\pi,
\qquad
S_n'(0)=\pi^n.
$$

Formal Weierstrass preparation applies because the first coefficient of $S_n$ that is a unit is the coefficient of $T^{q^n}$. It gives a unique factorization

$$
S_n(T)=P_n(T)V_n(T),
$$

where $V_n\in\mathcal O[[T]]^\times$ and $P_n$ is monic of degree $q^n$, with every lower coefficient in $\mathfrak m$. Since

$$
S_n=f(S_{n-1})
=S_{n-1}\left(\pi+\text{terms divisible by }S_{n-1}\right),
$$

Weierstrass division gives $P_{n-1}\mid P_n$. Define

$$
Q_n(T)=P_n(T)/P_{n-1}(T).
$$

This primitive division polynomial is monic of degree

$$
q^{n-1}(q-1)=|(\mathcal O/\pi^n)^\times|,
$$

and its reduction is $T^{q^n-q^{n-1}}$. Thus every nonleading coefficient lies in $\mathfrak m$. Comparing the linear terms in $S_n=S_{n-1}(\pi+\cdots)$, or equivalently differentiating at zero before removing the Weierstrass units, shows

$$
v(Q_n(0))=v(S_n'(0))-v(S_{n-1}'(0))=1.
$$

Hence $Q_n$ is Eisenstein.

For the explicit existence tower we now choose $f(T)=\pi T+T^q$. Then $S_n$ itself is a monic polynomial, so $P_n=S_n$, and

$$
Q_n(T)=\pi+S_{n-1}(T)^{q-1}.
$$

In particular, $Q_n(0)=\pi$ exactly.

Choose a primitive point $\omega_n$, meaning

$$
[\pi^n]_f(\omega_n)=0,
\qquad
[\pi^{n-1}]_f(\omega_n)\ne0,
$$

and put

$$
K_n=K(\omega_n).
$$

Eisenstein's theorem gives

$$
[K_n:K]=q^{n-1}(q-1),
$$

$K_n/K$ is totally ramified, and $\omega_n$ is a uniformizer of $K_n$.

Every root of $P_n$ is simple. For $x\in\mathfrak m_{\overline K}$, the term $\pi$ in

$$
f'(x)=\pi+q x^{q-1}
$$

has strictly smaller valuation than the second term; in equal characteristic the second term is zero. The chain rule makes $S_n'(x)$ nonzero at every torsion point. Thus $P_n$ has exactly $q^n$ roots.

Every residue class $a\in\mathcal O/\pi^n$ gives a torsion point $[a]_f(\omega_n)$. If it is zero, write $a=\pi^ru$ with $u$ a unit and $0\leq r<n$. Applying $[u^{-1}]_f$ would give $[\pi^r]_f(\omega_n)=0$, contradicting primitivity. The map

$$
\mathcal O/\pi^n\longrightarrow F_f[\pi^n],
\qquad a\longmapsto[a]_f(\omega_n)
$$

is therefore injective between two sets of $q^n$ elements and hence bijective. The primitive points are precisely those with $a$ a unit. Consequently every primitive point has the form

$$
[a]_f(\omega_n),
\qquad a\in(\mathcal O/\pi^n)^\times.
$$

and their number is $(q-1)q^{n-1}=\deg Q_n$.

Since $Q_n$ is monic and these roots are simple, we have the exact factorization

$$
Q_n(T)=
\prod_{a\in(\mathcal O/\pi^n)^\times}
\bigl(T-[a]_f(\omega_n)\bigr).
$$

### 6.4 The Galois action on torsion

Because $Q_n$ is Eisenstein, it is the minimal polynomial of $\omega_n$. Every primitive root $[a]_f(\omega_n)$ already belongs to $K_n$, since $[a]_f$ has coefficients in $K$ and converges at $\omega_n$. Sending $\omega_n$ to that root therefore defines a $K$-embedding of $K_n$ into itself, hence an automorphism

$$
\sigma_a(\omega_n)=[a]_f(\omega_n).
$$

The relations $[ab]_f=[a]_f\circ[b]_f$ give

$$
\sigma_a\sigma_b=\sigma_{ab}.
$$

The distinct primitive points are all roots of the separable polynomial $Q_n$, so it splits in $K_n$ and these maps exhaust the Galois group. This simultaneously proves normality rather than assuming it.

**Theorem 6.3.** The extension $K_n/K$ is finite, totally ramified, and abelian, with canonical isomorphism

$$
\operatorname{Gal}(K_n/K)
\xrightarrow{\sim}(\mathcal O/\pi^n)^\times,
\qquad
\sigma_a\longmapsto a.
$$

The fields are nested. Choosing $\omega_n$ compatibly so that

$$
[\pi]_f(\omega_{n+1})=\omega_n
$$

gives $K_n\subset K_{n+1}$, and restriction of Galois groups is reduction modulo $\pi^n$.

The inverse convention often appears here. Under our arithmetic reciprocity normalization, a unit $a\in\mathcal O^\times$ will act on torsion as $[a^{-1}]_f$. The direct torsion parametrization above labels the automorphism $\sigma_a$ by $[a]_f$; consequently reciprocity sends $a$ to $\sigma_{a^{-1}}$. This inversion is not a contradiction. It is the price of choosing arithmetic rather than geometric Frobenius.

### 6.5 The norm group of the torsion extension

The crucial calculation is

$$
N_{K_n/K}(K_n^\times)=\pi^{\mathbf Z}U^n.
$$

We give the mechanism rather than infer it from the desired classification. For the existence proof we take $f(T)=\pi T+T^q$ as above. The monic primitive division polynomial $Q_n$ has constant term $\pi$ and degree $(q-1)q^{n-1}$. That degree is even except in the trivial case $q=2,n=1$. The product of its roots therefore shows

$$
N_{K_n/K}(\omega_n)=\pi;
$$

in the exceptional case $K_1=K$ and the assertion is immediate. Thus $\pi^{\mathbf Z}$ lies in the norm group. This is stronger than mere surjectivity of norm valuations: it identifies the chosen uniformizer itself as a norm.

The needed unit calculation is a special case of the following valuation lemma. We state it here because it is also the engine behind the full unit–ramification theorem.

**Lemma 6.4 (norm-depth index).** Let $M/K$ be a finite totally ramified abelian extension with group $G$. At a ramification break, take the value before the drop, as in the convention $G_t=G_{\lceil t\rceil}$ for nonintegral lower indices. For an integer $m\geq0$, put

$$
C_m=N_{M/K}(U_M^0)U_K^m.
$$

Then

$$
[U_K^0:C_m]=[G^0:G^m].
$$

In particular, if $G^m=1$, then $U_K^m\subseteq N_{M/K}(U_M^0)$.

**Proof.** We record the norm calculation, including its indexing. For $\sigma\ne1$ put

$$
i(\sigma)=v_M(\sigma(\pi_M)-\pi_M),
$$

and set $G_t=\{\sigma:i(\sigma)\geq t+1\}$ for real $t\geq0$. Define

$$
\varphi(u)=\int_0^u\frac{dt}{[G_0:G_t]},
\qquad
G^s=G_{\psi(s)},
$$

where $\psi=\varphi^{-1}$. These conventions put inertia at index $0$ and make a lower break $b$ occur at the upper index $\varphi(b)$.

Let $r\geq1$ and $x\in\mathfrak m_M^r$. In

$$
N(1+x)-1
=\sum_{\varnothing\ne S\subseteq G}\prod_{\sigma\in S}\sigma(x),
$$

group terms into orbits under $G_t$. If $t<r$ and $G_t$ fixes the residue of $x/\pi_M^r$, an orbit sum acquires one extra unit of $M$-valuation; if it does not, the orbit has size $[G_0:G_t]$. Moving from $t$ to $t+dt$ therefore consumes $[G_0:G_t]$ units of $M$-valuation for one unit of $K$-valuation. Summing these contributions gives the exact estimate

$$
N(U_M^r)\subseteq
U_K^{\lfloor\varphi(r-1)\rfloor+1}.
$$

At a positive lower break $b$, divide the expression by the predicted power of $\pi_K$ and reduce. The only surviving orbit sums are linear, and the induced map is

$$
\mathfrak m_M^{b+1}/\mathfrak m_M^{b+2}
\longrightarrow
\mathfrak m_K^{\varphi(b)+1}/
\mathfrak m_K^{\varphi(b)+2},
\qquad
\bar x\longmapsto
\sum_{\sigma\in G_b/G_{b+1}}\overline{\sigma(x)}.
$$

Its kernel is the image of the injective ramification map

$$
G_b/G_{b+1}\longrightarrow k^+,
\qquad
\sigma\longmapsto
\overline{\frac{\sigma(\pi_M)-\pi_M}{\pi_M^{b+1}}},
$$

and hence its image has index $|G_b/G_{b+1}|$ in the relevant additive residue layer. At $b=0$ the quotient $G_0/G_1$ instead injects into $k^\times$ by $\sigma\mapsto\overline{\sigma(\pi_M)/\pi_M}$; the residue of a unit norm is the corresponding power map, whose cokernel has order $|G_0/G_1|$. Consequently, as $m$ increases through the integer upper indices,

$$
[C_m:C_{m+1}]=[G^m:G^{m+1}].
$$

If no ramification jump occurs in $[m,m+1)$, both sides are $1$. At a jump the displayed residue calculation also shows that $\varphi(b)$ is an integer; this is the abelian integrality assertion needed here. Multiplication from $0$ to $m-1$ yields

$$
[U_K^0:C_m]=[G^0:G^m].
$$

Finally, the norm-index theorem gives $[U_K^0:N(U_M^0)]=|G^0|$. If $G^m=1$, the two subgroups $C_m$ and $N(U_M^0)$ have the same index and one contains the other, so they are equal. $\square$

We apply the lemma by computing the ramification of $K_n/K$. If $a\in U_K^r\setminus U_K^{r+1}$ with $1\leq r<n$, write $a-1=\pi^ru$ with $u$ a unit. Formal subtraction gives

$$
[a]_f(T)-_{F_f}T=[a-1]_f(T)=[u]_f([\pi^r]_f(T)).
$$

Ordinary subtraction and formal subtraction differ by a power-series unit, because $F_f(X,[-1]_f(Y))=(X-Y)$ times a unit. Hence $[a]_f(T)-T$ has Weierstrass degree $q^r$, and its zeros are exactly the $\pi^r$-torsion points. Since $\omega_n$ is a uniformizer,

$$
v_{K_n}([a]_f(\omega_n)-\omega_n)=q^r.
$$

If $a\not\equiv1\pmod\pi$, the value is $1$. It follows directly from the definition of $\varphi$ that

$$
G^r=\{\sigma_a:a\in U_K^r/U_K^n\}
\quad(0\leq r\leq n),
$$

and in particular $G^n=1$. Lemma 6.4 now gives

$$
U^n\subseteq N_{K_n/K}(K_n^\times).
$$

Now apply the already proved norm-index theorem. The subgroup $\pi^{\mathbf Z}U^n$ lies in the norm group and has index

$$
[\mathcal O^\times:U^n]
=(q-1)q^{n-1}
=[K_n:K].
$$

The norm group has the same index, forcing equality. This use is not circular: $K_n$ has already been constructed independently, and the norm-index theorem was proved from the Brauer invariant.

There remains an orientation check. Let $\chi$ be a character of $(\mathcal O/\pi^n)^\times$ with cyclic image, let $E$ be the fixed field of its kernel, and choose $\tau$ with $\chi(\tau)=1/d$ in $\mathbf Q/\mathbf Z$, where $d=[E:K]$. The cyclic-algebra description of the fundamental class says that $\operatorname{rec}_{E/K}(u)=\tau^j$ precisely when

$$
\operatorname{inv}_K(E/K,\tau,u)=j/d.
$$

Here is the sign calculation. At the first level,

$$
Q_1(T)=T^{q-1}+\pi.
$$

For a cyclic quotient of order $d\mid q-1$, the defining relation $z^d=u$ in the cyclic algebra and the factorization of $Q_1$ give

$$
\operatorname{inv}_K(E/K,\tau,u)
=\chi(u^{-1}).
$$

The minus sign comes from moving a coefficient past $z$ in the relation $zx=\tau(x)z$. For the passage from level $r-1$ to $r$, use

$$
Q_r(T)=\pi+S_{r-1}(T)^{q-1}
$$

and multiply its values at $T+_{F_f}[a]_f(\omega_r)$ over one coset modulo $\pi^{r-1}$. Adjacent formal translates cancel because

$$
[a+b]_f(\omega_r)
=[a]_f(\omega_r)+_{F_f}[b]_f(\omega_r),
$$

and the remaining endpoint is $[u^{-1}]_f(\omega_r)$. Induction on $r$ therefore gives the same invariant formula for every character $\chi$. Characters separate the finite abelian group, so

$$
\operatorname{rec}_{K_n/K}(u)=\sigma_{u^{-1}},
\qquad
\operatorname{rec}_{K_n/K}(\pi)=1.
$$

Replacing arithmetic Frobenius by geometric Frobenius reverses the crossed-product relation and removes the inverse on units. This verifies that the torsion action, the Brauer invariant, and the convention of Chapter 1 agree.

### 6.6 Adding the unramified direction

Let $K^{\mathrm{ur}}_m/K$ be the unramified extension of degree $m$. Its norm group is

$$
N_{K^{\mathrm{ur}}_m/K}((K^{\mathrm{ur}}_m)^\times)
=\pi^{m\mathbf Z}\mathcal O^\times.
$$

The totally ramified field $K_n$ and unramified field $K^{\mathrm{ur}}_m$ have trivial intersection, so their compositum

$$
E_{m,n}=K^{\mathrm{ur}}_mK_n
$$

is abelian with

$$
\operatorname{Gal}(E_{m,n}/K)
\cong\mathbf Z/m\mathbf Z\times(\mathcal O/\pi^n)^\times.
$$

The norm group of a compositum of finite abelian extensions is the intersection of their norm groups. This follows from finite reciprocity: the compositum corresponds to the common refinement of the two quotient maps. Therefore

$$
N_{E_{m,n}/K}(E_{m,n}^\times)
=\pi^{m\mathbf Z}U^n.
$$

These subgroups form a neighborhood basis of $1$ among open finite-index subgroups of $K^\times$.

### 6.7 The existence theorem

We can now reverse norm groups into fields.

**Theorem 6.5 (local existence theorem).** For every open finite-index subgroup $H\subseteq K^\times$, there is a unique finite abelian extension $L/K$ inside $K^{\mathrm{ab}}$ such that

$$
H=N_{L/K}(L^\times).
$$

Moreover

$$
[L:K]=[K^\times:H].
$$

**Proof.** Choose $m,n$ with $\pi^{m\mathbf Z}U^n\subseteq H$. Let $E=E_{m,n}$. Finite reciprocity identifies

$$
K^\times/N_{E/K}(E^\times)
\xrightarrow{\sim}\operatorname{Gal}(E/K).
$$

The image of $H$ is a subgroup of this finite abelian Galois group. Let $L$ be its fixed field. The quotient map to $\operatorname{Gal}(L/K)$ has kernel exactly $H$, so finite reciprocity for $L/K$ gives

$$
H=N_{L/K}(L^\times).
$$

The index formula follows from the order of the quotient. Suppose $L'$ has the same norm group. In the compositum $EL'$, finite reciprocity gives

$$
N_{EL'/K}((EL')^\times)
=N_{E/K}(E^\times)\cap N_{L'/K}((L')^\times)
=N_{E/K}(E^\times).
$$

The norm-index formula then gives $[EL':K]=[E:K]$, so $L'\subseteq E$. Inside $E$, the common norm subgroup $H$ determines one fixing subgroup and hence one field. Therefore $L'=L$. $\square$

The proof constructs $L$: first choose a finite precision $n$ and an unramified period $m$, then take an explicit fixed field in $E_{m,n}$. It does not appeal to a global class field or to an unnamed supply of abelian extensions.

## 7. The infinite reciprocity map

### 7.1 Passage through finite quotients

Let $K^{\mathrm{ab}}$ be the compositum in $K^s$ of all finite abelian extensions of $K$. Then

$$
G_K^{\mathrm{ab}}
=\operatorname{Gal}(K^{\mathrm{ab}}/K)
\cong\varprojlim_{L/K\text{ finite abelian}}
\operatorname{Gal}(L/K),
$$

where transition maps are restriction. The finite Artin maps are compatible with these restrictions, so for $x\in K^\times$ the tuple

$$
(\operatorname{rec}_{L/K}(x))_L
$$

defines an element of the inverse limit.

**Definition 7.1.** The **local reciprocity map**, in arithmetic normalization, is

$$
\operatorname{rec}_K:K^\times\longrightarrow G_K^{\mathrm{ab}},
\qquad
x\longmapsto(\operatorname{rec}_{L/K}(x))_L.
$$

For every finite abelian $L/K$, its composite with restriction to $L$ is the finite map $\operatorname{rec}_{L/K}$.

### 7.2 Continuity

A map to a profinite group is continuous if and only if all of its composites with finite continuous quotients are continuous. Each finite Artin map has open kernel $N_{L/K}(L^\times)$. Hence $\operatorname{rec}_K$ is continuous.

There is also a concrete neighborhood argument. A basic open neighborhood of the identity in $G_K^{\mathrm{ab}}$ is the subgroup fixing some finite abelian $L$. Its inverse image is precisely $N_{L/K}(L^\times)$, which is open in $K^\times$. Thus reciprocity translates Galois neighborhoods into norm neighborhoods.

### 7.3 Density and failure of literal surjectivity

The map $\operatorname{rec}_K$ is surjective onto every finite quotient. Therefore its image is dense in the inverse limit. Indeed, a subset of a profinite group is dense exactly when its image in every finite quotient is all of that quotient.

The image is generally not all of $G_K^{\mathrm{ab}}$. On the maximal unramified quotient,

$$
G_K^{\mathrm{ab}}\twoheadrightarrow
\operatorname{Gal}(K^{\mathrm{nr}}/K)\cong\widehat{\mathbf Z},
$$

reciprocity sends $x$ to $v(x)\in\mathbf Z\subset\widehat{\mathbf Z}$. The subgroup $\mathbf Z$ is dense but proper in $\widehat{\mathbf Z}$. Thus no element of $K^\times$ maps to a genuinely nonintegral profinite Frobenius exponent.

This also gives a quick compactness obstruction: $G_K^{\mathrm{ab}}$ is compact, whereas $K^\times$ is not. A continuous bijective topological isomorphism is impossible.

### 7.4 Injectivity

The kernel of the infinite map is the intersection of all finite abelian norm groups. The cofinal family from Chapter 6 gives

$$
\ker(\operatorname{rec}_K)
\subseteq
\bigcap_{m,n\geq1}\pi^{m\mathbf Z}U^n.
$$

An element in this intersection has valuation divisible by every $m$, hence valuation zero, and lies in every $U^n$, hence equals $1$. Therefore $\operatorname{rec}_K$ is injective.

So the exact infinite statement is:

**Theorem 7.2 (local reciprocity).** The map

$$
\operatorname{rec}_K:K^\times\hookrightarrow G_K^{\mathrm{ab}}
$$

is a continuous injective homomorphism with dense image. For every finite abelian $L/K$ it induces an isomorphism

$$
K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}\operatorname{Gal}(L/K).
$$

### 7.5 Profinite completion

The profinite completion of $K^\times$ is the inverse limit over open finite-index subgroups:

$$
\widehat{K^\times}
=\varprojlim_H K^\times/H.
$$

The existence theorem says that the norm groups of finite abelian extensions are exactly those $H$. Finite reciprocity identifies every quotient with the corresponding Galois group. Passing to inverse limits gives a topological isomorphism

$$
\widehat{K^\times}
\xrightarrow{\sim}G_K^{\mathrm{ab}}.
$$

This is the strongest concise form of local reciprocity. The original group sits densely in its profinite completion, and the Galois group is that completion.

Using $K^\times\cong\pi^{\mathbf Z}\times\mathcal O^\times$ and the fact that $\mathcal O^\times$ is already profinite,

$$
\widehat{K^\times}
\cong\widehat{\mathbf Z}\times\mathcal O^\times
$$

after choosing a uniformizer. Accordingly, noncanonically as a topological group,

$$
G_K^{\mathrm{ab}}\cong\widehat{\mathbf Z}\times\mathcal O^\times.
$$

The decomposition is noncanonical because changing the uniformizer changes the splitting between unramified and ramified coordinates. The inertia subgroup itself is canonical.

### 7.6 The reciprocity, existence, and norm theorems together

The three named theorems are different faces of one statement.

- **Reciprocity:** for finite abelian $L/K$,
  $$
  K^\times/NL^\times\cong\operatorname{Gal}(L/K).
  $$
- **Existence:** every open finite-index $H\subset K^\times$ is $NL^\times$ for a unique finite abelian $L/K$.
- **Norm limitation:** for finite Galois $E/K$, its norm group equals that of its maximal abelian subextension.

Together they give an inclusion-reversing bijection

$$
\left\{\begin{array}{c}
\text{finite abelian extensions }L/K\\
\text{inside }K^{\mathrm{ab}}
\end{array}\right\}
\longleftrightarrow
\left\{\begin{array}{c}
\text{open finite-index subgroups}\\
H\subset K^\times
\end{array}\right\},
$$

with $L\mapsto N_{L/K}(L^\times)$.

## 8. Uniformizers, units, and ramification

### 8.1 The unramified coordinate

The maximal unramified extension $K^{\mathrm{nr}}$ has Galois group

$$
\operatorname{Gal}(K^{\mathrm{nr}}/K)\cong\widehat{\mathbf Z},
$$

with arithmetic Frobenius corresponding to $1$. Projecting reciprocity to this quotient gives the completed valuation:

$$
\begin{array}{ccc}
K^\times & \xrightarrow{\operatorname{rec}_K} & G_K^{\mathrm{ab}}\\
v\downarrow && \downarrow\\
\mathbf Z & \longrightarrow & \widehat{\mathbf Z}.
\end{array}
$$

Thus

$$
\operatorname{rec}_K(x)|_{K^{\mathrm{nr}}}
=\operatorname{Frob}_K^{v(x)}.
$$

In particular, every unit acts trivially on $K^{\mathrm{nr}}$, while a uniformizer acts as arithmetic Frobenius. Changing the uniformizer from $\pi$ to $u\pi$ does not change the unramified action, because $u$ is a unit. It may change the action on ramified abelian extensions.

The norm criterion for a finite unramified extension $K_m/K$ is now immediate:

$$
x\in N_{K_m/K}(K_m^\times)
\quad\Longleftrightarrow\quad
m\mid v(x).
$$

No unit condition remains.

### 8.2 Units are the abelian inertia group

Let $I_K\subset G_K$ be the inertia subgroup, the kernel of the action on the separable closure of $k$. Its image in $G_K^{\mathrm{ab}}$ will be denoted $I_K^{\mathrm{ab,im}}$; this is more precise than the abstract abelianization $I_K^{\mathrm{ab}}$, because abelianization does not preserve every subgroup injection.

The preceding unramified formula gives

$$
\operatorname{rec}_K(\mathcal O^\times)
\subseteq I_K^{\mathrm{ab,im}}.
$$

The reverse inclusion follows after profinite completion: the valuation quotient accounts for all of $\widehat{\mathbf Z}$, so the kernel is the already complete group $\mathcal O^\times$. Therefore reciprocity restricts to a topological isomorphism

$$
\mathcal O^\times\xrightarrow{\sim}I_K^{\mathrm{ab,im}}.
$$

At a finite abelian level $L/K$, let $I(L/K)$ be inertia. Then

$$
\operatorname{rec}_{L/K}(\mathcal O_K^\times)=I(L/K).
$$

Indeed, the maximal unramified subextension $L^I/K$ has norm group

$$
\pi^{f\mathbf Z}\mathcal O_K^\times,
$$

so units lie in the kernel of the quotient map to $G/I$. Comparing orders shows that their image is all of $I$.

This gives an exact multiplicative description of the usual Galois sequence:

$$
\begin{array}{ccccccccc}
1&\to&\mathcal O_K^\times/N_{L/K}(\mathcal O_L^\times)
&\to&K^\times/N_{L/K}(L^\times)
&\xrightarrow{v}&\mathbf Z/f\mathbf Z&\to&0\\
&&\downarrow\wr&&\downarrow\wr&&\downarrow\wr\\
1&\to&I(L/K)&\to&\operatorname{Gal}(L/K)&\to&
\operatorname{Gal}(l/k)&\to&0.
\end{array}
$$

The right vertical map sends $1$ to arithmetic Frobenius. In particular,

$$
[\mathcal O_K^\times:N_{L/K}(\mathcal O_L^\times)]=e(L/K)
$$

for finite abelian $L/K$.

### 8.3 Why higher unit groups require upper numbering

The filtration $U^n$ measures congruence in the base field. To match it with a ramification filtration that behaves well under quotients, lower numbering is not sufficient: lower ramification groups behave naturally under subgroups, while reciprocity repeatedly passes to quotient extensions. Upper numbering is designed so that

$$
(G/H)^u=G^uH/H
$$

for every normal subgroup $H$.

For a finite Galois extension $L/K$ with group $G$, choose a uniformizer $\pi_L$ and define the lower function

$$
i_G(\sigma)=v_L(\sigma(\pi_L)-\pi_L)
$$

for $\sigma\ne1$, with the equivalent definition using all of $\mathcal O_L$. The lower groups are

$$
G_t=\{\sigma:i_G(\sigma)\geq t+1\}\qquad(t\geq0),
$$

with $G_{-1}=G$. Since $i_G(\sigma)$ is integral, this means $G_t=G_{\lceil t\rceil}$ for nonintegral $t$; at an integral break $b$, the notation $G_b$ retains the group before the drop immediately to its right. The Herbrand function is the continuous, increasing, piecewise-linear function

$$
\varphi_{L/K}(u)
=\int_0^u\frac{dt}{[G_0:G_t]},
$$

and its inverse is $\psi_{L/K}$. The upper group is

$$
G^v=G_{\psi_{L/K}(v)}.
$$

Then $G^{-1}=G$, $G^0=I$, and $G^{0+}$ is wild inertia. We need this much of the ramification filtration solely to state the exact compatibility with units.

### 8.4 The unit and ramification theorem

**Theorem 8.1.** Let $L/K$ be finite abelian with group $G$. Under arithmetic local reciprocity,

$$
\operatorname{rec}_{L/K}(U_K^n)=G^n
\qquad(n\geq0),
$$

where $G^n$ denotes the upper-numbering group at the integer $n$. Equivalently,

$$
\operatorname{rec}_{L/K}^{-1}(G^n)
=U_K^nN_{L/K}(L^\times).
$$

For $n=0$ this is the inertia statement just proved. For $n\geq1$ it says that successive principal-unit depth is exactly upper ramification depth after abelianization.

**Proof.** The case $n=0$ is Section 8.2. Assume $n\geq1$, let $I=G^0$, and let $K_0=L^I$ be the maximal unramified subextension. Norms from $K_0/K$ are surjective on every unit layer: on $U^r/U^{r+1}$ the norm is the finite-field trace, and successive approximation lifts a prescribed class. Thus Lemma 6.4, applied to the totally ramified extension $L/K_0$, gives

$$
[U_K^0:N_{L/K}(U_L^0)U_K^n]
=[G^0:G^n]. \tag{8.1}
$$

This is the required product of graded indices. To see it directly from the real indexing, let $b_1<\cdots<b_s$ be the lower breaks with upper values $c_j=\varphi(b_j)$. The residue calculation in Lemma 6.4 gives

$$
\frac{[U_K^0:N(U_L^0)U_K^{m+1}]}
{[U_K^0:N(U_L^0)U_K^m]}
=[G^m:G^{m+1}].
$$

The quotient is $1$ if $[m,m+1)$ contains no $c_j$. At a positive break it is the order of the image of

$$
G_{b_j}/G_{b_j+1}\hookrightarrow k^+,
\qquad
\sigma\longmapsto
\overline{(\sigma(\pi_L)-\pi_L)/\pi_L^{b_j+1}}.
$$

At the tame break $b=0$, the analogous map is $G_0/G_1\hookrightarrow k^\times$ and the residue norm supplies the same index equality. In an abelian extension the norm expansion forces every $c_j$ to be integral, so no jump is split between two unit layers. Multiplying from $m=0$ to $n-1$ gives (8.1).

It remains to identify the subgroup, not only its order. Put $E=L^{G^n}$. Quotient compatibility of upper numbering gives

$$
\operatorname{Gal}(E/K)^n=1.
$$

Apply the last assertion of Lemma 6.4 to the totally ramified part of $E/K$, and use surjectivity of unramified norms on $U_K^n$. We obtain

$$
U_K^n\subseteq N_{E/K}(E^\times).
$$

Finite reciprocity for $E/K$ therefore shows that every element of $\operatorname{rec}_{L/K}(U_K^n)$ restricts trivially to $E$, so

$$
\operatorname{rec}_{L/K}(U_K^n)\subseteq G^n.
$$

On the other hand, (8.1) says

$$
[G^0:\operatorname{rec}_{L/K}(U_K^n)]
=[G^0:G^n].
$$

The inclusion and equality of indices force equality. Taking inverse images under the quotient map $K^\times\to K^\times/N(L^\times)$ gives the equivalent formula. $\square$

The use of upper numbering is forced by functoriality, not by taste. If lower groups were placed on the right, the formula would fail after passing to a quotient extension.

### 8.5 Conductors

Let $L/K$ be finite abelian. Its conductor exponent is the least $n\geq0$ such that

$$
U_K^n\subseteq N_{L/K}(L^\times).
$$

By Theorem 8.1, this is equivalently the least $n$ with $G^n=1$. The extension is unramified exactly when the conductor exponent is $0$. A tamely ramified nontrivial abelian extension has conductor exponent $1$: inertia is nontrivial, but $G^1=1$. Wild extensions have conductor at least $2$.

For a finite-order character

$$
\chi:K^\times\to A
$$

into an abelian group, its conductor exponent is the least $n\geq0$ for which $\chi(U^n)=1$. Under reciprocity this is exactly the least $n$ at which the corresponding Galois character is trivial on $G_K^n$. Thus a congruence condition on units becomes a ramification condition on a representation.

### 8.6 Tame and wild pieces

Reduction gives

$$
\mathcal O^\times/U^1\cong k^\times,
$$

a cyclic group of order $q-1$, prime to $p$. Reciprocity identifies its finite quotients with tame abelian inertia. The principal-unit group $U^1$ is pro-$p$: all of its finite quotients have $p$-power order. It therefore corresponds to wild abelian inertia.

This yields the conceptual decomposition

$$
K^\times
\sim
\underbrace{\pi^{\mathbf Z}}_{\text{unramified}}
\times
\underbrace{k^\times}_{\text{tame inertia}}
\times
\underbrace{U^1}_{\text{wild inertia}},
$$

where the symbol $\sim$ suppresses the choice of Teichmüller representatives and uniformizer. The filtration of $U^1$ refines only the last factor.

## 9. Functoriality in finite extensions

### 9.1 Why directions are easy to reverse accidentally

Let $L/K$ be finite and place $K^s$ and $L^s$ in a common algebraic closure. Then

$$
G_L=\operatorname{Gal}(K^s/L)\subseteq
G_K=\operatorname{Gal}(K^s/K).
$$

There are two multiplicative maps, pointing in opposite directions:

$$
N_{L/K}:L^\times\to K^\times,
\qquad
\iota:L^\times\longleftarrow K^\times.
$$

There are likewise two Galois maps. Inclusion $G_L\hookrightarrow G_K$ induces

$$
i_*:G_L^{\mathrm{ab}}\to G_K^{\mathrm{ab}}.
$$

In the other direction there is the group-theoretic **transfer**

$$
\operatorname{Ver}_{L/K}:G_K^{\mathrm{ab}}\to G_L^{\mathrm{ab}}.
$$

The norm corresponds to inclusion of Galois groups; inclusion of fields' multiplicative groups corresponds to transfer. Remembering this crossed pattern prevents the common direction error.

### 9.2 Norm corresponds to Galois inclusion

**Theorem 9.1 (norm–inclusion compatibility).** The diagram

$$
\begin{array}{ccc}
L^\times&\xrightarrow{\operatorname{rec}_L}&G_L^{\mathrm{ab}}\\
N_{L/K}\downarrow&&\downarrow i_*\\
K^\times&\xrightarrow{\operatorname{rec}_K}&G_K^{\mathrm{ab}}
\end{array}
$$

commutes.

At finite level, choose a finite abelian extension $M/K$ large enough to see the image under consideration and compare with the compositum $ML/L$. Corestriction of fundamental classes on the cohomological side is the field norm on $H^0$ and is induced by subgroup inclusion on $H_1$. Naturality of cap product gives the square.

The unramified case checks the exponent. If $L/K$ has residue degree $f$ and $\pi_L$ is a uniformizer, then

$$
v_K(N_{L/K}\pi_L)=f.
$$

Hence the lower-left route acts on $K^{\mathrm{nr}}$ by $\operatorname{Frob}_K^f$. The upper-right route begins with $\operatorname{Frob}_L$, which acts on residues by $x\mapsto x^{q^f}$ and is exactly the same element after inclusion into $G_K$.

### 9.3 Multiplicative inclusion corresponds to transfer

Choose right coset representatives $r_1,\dots,r_d$ for $G_L$ in $G_K$. For $g\in G_K$, write

$$
r_i g=h_i r_{j(i)},
\qquad h_i\in G_L.
$$

The transfer is

$$
\operatorname{Ver}_{L/K}(g)=\prod_i h_i
\pmod{[G_L,G_L]}.
$$

Changing representatives changes the product by a commutator, so the class is well defined and factors through $G_K^{\mathrm{ab}}$.

**Theorem 9.2 (inclusion–transfer compatibility).** The diagram

$$
\begin{array}{ccc}
K^\times&\xrightarrow{\operatorname{rec}_K}&G_K^{\mathrm{ab}}\\
\iota\downarrow&&\downarrow\operatorname{Ver}_{L/K}\\
L^\times&\xrightarrow{\operatorname{rec}_L}&G_L^{\mathrm{ab}}
\end{array}
$$

commutes.

On cohomology, restriction of scalars on $H^0$ corresponds under cap product to transfer on $H_1$. Compatibility of the fundamental classes supplies the degree normalization. For an unramified extension of degree $d$, transfer sends arithmetic Frobenius $F_K$ to $F_K^d=F_L$, agreeing with the fact that the same element $\pi_K$, viewed in $L$, is a uniformizer when $e=1$.

### 9.4 Towers and finite quotient diagrams

Suppose $K\subseteq L\subseteq M$ are finite. Transitivity of norms and of group inclusion gives

$$
N_{M/K}=N_{L/K}\circ N_{M/L},
\qquad
i_{M/K,*}=i_{L/K,*}\circ i_{M/L,*}.
$$

Transfer is also transitive:

$$
\operatorname{Ver}_{M/K}
=\operatorname{Ver}_{M/L}\circ\operatorname{Ver}_{L/K}.
$$

The two reciprocity squares therefore stack coherently through any tower.

Now assume $M/K$ is finite abelian and let $L$ be intermediate. Restriction of automorphisms gives the quotient diagram

$$
\begin{array}{ccc}
K^\times/N_{M/K}(M^\times)&\xrightarrow{\sim}&\operatorname{Gal}(M/K)\\
\downarrow&&\downarrow\operatorname{res}\\
K^\times/N_{L/K}(L^\times)&\xrightarrow{\sim}&\operatorname{Gal}(L/K).
\end{array}
$$

The left arrow is the natural quotient because

$$
N_{M/K}(M^\times)\subseteq N_{L/K}(L^\times).
$$

Its kernel corresponds to $\operatorname{Gal}(M/L)$. This is the precise reason the field–norm correspondence reverses inclusions.

### 9.5 Base change and norm subgroups

Let $E/K$ be finite abelian and let $L/K$ be any finite extension. The compositum $EL/L$ is abelian. Norm–inclusion compatibility shows that the reciprocity character cutting out $EL/L$ is the restriction, along $K^\times\hookrightarrow L^\times$ and transfer on Galois groups, of the one cutting out $E/K$.

At the level of norm groups,

$$
N_{EL/L}((EL)^\times)
=\operatorname{rec}_L^{-1}(G_{EL}^{\mathrm{ab}})
$$

is best computed through the transfer square rather than through a naive scalar extension of $N_{E/K}(E^\times)$. Arbitrary base change may absorb ramification or split the extension; equality with a simple inverse image of the old norm subgroup is not automatic.

For unramified base change the picture is clean. Total ramification is preserved, and upper ramification groups are compatible with the Herbrand reindexing. The exact diagrams above remain valid without special cases and are safer than informal rules.

## 10. Explicit norm quotients and extension classes

### 10.1 Unramified extensions

Let $K_m/K$ be unramified of degree $m$. Then

$$
N_{K_m/K}(K_m^\times)
=\pi^{m\mathbf Z}\mathcal O^\times,
$$

and

$$
K^\times/N_{K_m/K}(K_m^\times)
\cong\mathbf Z/m\mathbf Z.
$$

The class of $\pi$ maps to arithmetic Frobenius. A unit is always a norm. Explicitly, solve its residue norm in $\mathbf F_{q^m}^\times$, then lift the remaining principal-unit error one layer at a time using the residue trace.

This example shows why the reciprocity image of a uniformizer cannot be defined merely as “a lift of Frobenius” in every ramified extension: only the restriction to the unramified part is canonical. In a ramified quotient, changing the uniformizer by a unit changes the inertia component.

### 10.2 Totally tamely ramified cyclic extensions

Let $e$ be prime to $p$, assume $\mu_e\subset K$, and set

$$
L=K(\alpha),
\qquad
\alpha^e=u\pi
$$

for a unit $u$. This is cyclic, totally ramified, and of degree $e$. Principal units are norms, while the residue of a unit norm is an $e$th power. Also

$$
N_{L/K}(\alpha)=(-1)^{e+1}u\pi.
$$

Consequently

$$
N_{L/K}(L^\times)
=\langle(-1)^{e+1}u\pi\rangle
\cdot\widetilde{(k^\times)^e}\cdot U^1,
$$

where $\widetilde{(k^\times)^e}$ denotes the Teichmüller lifts of the $e$th powers in $k^\times$. Since $\mu_e\subset K$ implies $e\mid q-1$, this subgroup has index $e$, as reciprocity requires.

The generator involving $u$ matters. Replacing it by $\pi$ without checking the unit factor can give the wrong norm subgroup, even though both elements have valuation one.

### 10.3 The three quadratic extensions for odd residue characteristic

Assume $p\ne2$ and choose a nonsquare unit $u$. Since the square map is an isomorphism on $U^1$,

$$
K^\times/(K^\times)^2
\cong (\mathbf Z/2\mathbf Z)\times
k^\times/(k^\times)^2
\cong(\mathbf Z/2\mathbf Z)^2.
$$

The three index-two subgroups correspond to the three quadratic extensions.

For the unramified quadratic extension $K(\sqrt u)$,

$$
N(L^\times)=\pi^{2\mathbf Z}\mathcal O^\times.
$$

For $K(\sqrt\pi)$,

$$
N(L^\times)
=\langle-\pi\rangle\cdot\widetilde{(k^\times)^2}\cdot U^1.
$$

For $K(\sqrt{u\pi})$,

$$
N(L^\times)
=\langle-u\pi\rangle\cdot\widetilde{(k^\times)^2}\cdot U^1.
$$

These norm groups are distinct. The first detects parity of valuation; the latter two combine valuation parity with the residue square class of the unit part. Their intersection is $(K^\times)^2$, corresponding to the biquadratic compositum of all three fields.

In residue characteristic $2$, $U^1/(U^1)^2$ is larger and higher unit layers contribute. The three-extension classification fails, illustrating that wild unit data cannot be read from $k^\times$ alone.

### 10.4 Formal-module layers

For the torsion extension $K_n/K$ of Chapter 6,

$$
K^\times/N_{K_n/K}(K_n^\times)
\cong\mathcal O^\times/U^n
\cong(\mathcal O/\pi^n)^\times.
$$

The extension is totally ramified of degree $(q-1)q^{n-1}$. At $n=1$ it captures all tame abelian inertia of order dividing $q-1$. Each passage from $n$ to $n+1$ adds an additive residue layer of order $q$, precisely matching

$$
U^n/U^{n+1}\cong k^+.
$$

Thus the construction is not merely a source of fields of the right degrees. Its Galois tower reproduces the entire unit filtration, one finite quotient at a time.

### 10.5 Composita and intersections

If $L_1,L_2/K$ are finite abelian with norm groups $H_1,H_2$, then

$$
N_{L_1L_2/K}((L_1L_2)^\times)=H_1\cap H_2,
$$

while

$$
N_{L_1\cap L_2/K}((L_1\cap L_2)^\times)=H_1H_2.
$$

The product $H_1H_2$ is open, hence closed. These formulas follow by applying the subgroup correspondence in a finite abelian extension containing both fields. They turn field operations into elementary subgroup operations, with the expected reversal:

$$
\text{compositum}\leftrightarrow\text{intersection},
\qquad
\text{intersection}\leftrightarrow\text{product}.
$$

The degree formulas become

$$
[L_1L_2:K]=[K^\times:H_1\cap H_2],
$$

and

$$
[L_1\cap L_2:K]=[K^\times:H_1H_2].
$$

### 10.6 Building an extension from congruence data

Suppose a subgroup is presented as

$$
H=\langle\pi^m a\rangle\,V,
$$

where $V\subseteq\mathcal O^\times$ is open and $a\in\mathcal O^\times$. Choose $n$ with $U^n\subseteq V$. The quotient $K^\times/H$ is computed from the finite group

$$
(\mathbf Z/m'\mathbf Z)\times(\mathcal O/\pi^n)^\times
$$

after imposing the single relation determined by $\pi^m a$; here $m'$ is any multiple large enough to contain the valuation relation. The field corresponding to $H$ is the fixed field of the resulting subgroup in $E_{m',n}$.

This procedure is usable: finite congruence arithmetic determines the subgroup, the unramified and torsion fields provide an explicit ambient abelian extension, and ordinary finite Galois theory extracts the desired field. The construction also shows that every finite abelian extension has finite conductor.

## 11. Continuous one-dimensional characters

### 11.1 The exact topological statement

A one-dimensional Galois character factors through $G_K^{\mathrm{ab}}$. Since this group is the profinite completion of $K^\times$, the cleanest coefficient hypothesis is that the target be profinite.

**Theorem 11.1.** Let $A$ be a profinite abelian group. Composition with reciprocity gives a natural bijection

$$
\operatorname{Hom}_{\mathrm{cont}}(G_K,A)
\xrightarrow{\sim}
\operatorname{Hom}_{\mathrm{cont}}(K^\times,A).
$$

On the left every map factors through $G_K^{\mathrm{ab}}$. On the right the universal property of profinite completion extends a continuous homomorphism uniquely from $K^\times$ to $\widehat{K^\times}\cong G_K^{\mathrm{ab}}$.

For multiplicative coefficients, take $A$ to be a profinite subgroup of a topological field's unit group. If $E/\mathbf Q_\ell$ is finite, $\mathcal O_E^\times$ is profinite, so continuous $\ell$-adic characters

$$
G_K\to\mathcal O_E^\times
$$

are exactly continuous characters $K^\times\to\mathcal O_E^\times$.

For a general Hausdorff abelian target $A$, not every continuous character of $K^\times$ comes from Galois. The exact condition is that it extend continuously to the profinite completion. Equivalently, for every identity neighborhood in the closure of its image, its inverse image contains an open finite-index subgroup of $K^\times$. A character $K^\times\to\mathbf C^\times$ sending $\pi$ to $2$ is continuous because $\pi^{\mathbf Z}$ is discrete, but it cannot come from $G_K$: its image is not relatively compact. This counterexample is why the coefficient topology must be stated.

### 11.2 Finite-order characters and cyclic extensions

Let $A$ be a finite cyclic group and let

$$
\chi:K^\times\to A
$$

be continuous. Its kernel is open of finite index. The existence theorem produces a finite abelian extension $L/K$ with

$$
N_{L/K}(L^\times)=\ker\chi.
$$

The quotient $K^\times/\ker\chi$ is the image of $\chi$, so $L/K$ is cyclic of degree $|\operatorname{im}\chi|$. Conversely, a cyclic extension and an embedding of its Galois group in $A$ produce such a character.

Thus finite-order local characters and cyclic extensions determine each other once a faithful character of the cyclic Galois group is chosen. Without that choice, the extension remembers the kernel but not a preferred generator of its character group.

### 11.3 Unramified characters

A character $\chi:K^\times\to A$ is unramified when it is trivial on $\mathcal O^\times$. It is then determined by the single value

$$
\alpha=\chi(\pi),
\qquad
\chi(x)=\alpha^{v(x)}.
$$

Under reciprocity, the corresponding Galois character is trivial on inertia and sends arithmetic Frobenius to $\alpha$. If geometric reciprocity were used, geometric Frobenius would be sent to the same $\alpha$, or arithmetic Frobenius to $\alpha^{-1}$.

For a profinite target, any allowed $\alpha$ lies in a compact procyclic subgroup and the formula extends from $\mathbf Z$ to $\widehat{\mathbf Z}$. For $A=\mathcal O_E^\times$, this includes infinite-order $\ell$-adic unramified characters. For $A=\mathbf C^\times$ and a genuine continuous character of the profinite Galois group, $\alpha$ must have finite order; arbitrary complex Satake-type parameters belong to a Weil-group formulation, not to continuous characters of $G_K$ itself.

### 11.4 Ramified characters and conductor

Let $A$ be finite or profinite and $\chi:K^\times\to A$ continuous. Its restriction to units determines ramification. Define

$$
a(\chi)=\min\{n\geq0:\chi(U^n)=1\}
$$

when such an $n$ exists. For finite-image characters it always exists. The reciprocity filtration theorem gives

$$
a(\chi)=\min\{n:\chi_{\mathrm{Gal}}(G_K^n)=1\}.
$$

Thus:

- $a(\chi)=0$ exactly when $\chi$ is unramified;
- $a(\chi)=1$ for a nontrivial tamely ramified character;
- $a(\chi)\geq2$ signals wild ramification.

For a continuous $\ell$-adic character with infinite image on $U^1$, there may be no finite $n$ on which it becomes trivial. One then speaks of finite conductor only under the additional hypothesis that inertia has finite image, or uses a more general analytic notion. Finite-order characters, which cut out finite abelian extensions, always have the integral conductor above.

### 11.5 Characters in towers

Let $L/K$ be finite. If $\chi:G_K\to A$ corresponds to $\chi_K:K^\times\to A$, then restriction to $G_L$ corresponds to precomposition with the norm:

$$
\chi|_{G_L}
\longleftrightarrow
\chi_K\circ N_{L/K}:L^\times\to A.
$$

This is exactly the norm–inclusion square of Chapter 9.

In the other direction, a character of $G_L$ can be transferred along the induced map $G_L^{\mathrm{ab}}\to G_K^{\mathrm{ab}}$ only when the desired operation on characters is specified. On multiplicative groups, restriction of a character of $L^\times$ to the embedded $K^\times$ corresponds to precomposition on Galois groups with transfer. The two operations should not be conflated:

$$
\begin{array}{c|c}
\text{Galois restriction }G_L\hookrightarrow G_K
&\text{multiplicative norm }L^\times\to K^\times\\
\text{Galois transfer }G_K^{\mathrm{ab}}\to G_L^{\mathrm{ab}}
&\text{multiplicative inclusion }K^\times\hookrightarrow L^\times.
\end{array}
$$

This dictionary is especially useful when changing the base local field of a one-dimensional representation.

## 12. The local reciprocity dictionary

### 12.1 Fields and subgroups

For a finite abelian extension $L/K$, put

$$
H_L=N_{L/K}(L^\times).
$$

Then

$$
\operatorname{Gal}(L/K)\cong K^\times/H_L,
\qquad
[L:K]=[K^\times:H_L].
$$

Every open finite-index subgroup is exactly one $H_L$. The order-reversing rules are

$$
L_1\subseteq L_2\iff H_{L_2}\subseteq H_{L_1},
$$

$$
H_{L_1L_2}=H_{L_1}\cap H_{L_2},
\qquad
H_{L_1\cap L_2}=H_{L_1}H_{L_2}.
$$

A cyclic extension corresponds to an open subgroup with cyclic quotient. An unramified extension of degree $m$ corresponds to

$$
\pi^{m\mathbf Z}\mathcal O^\times.
$$

A totally ramified extension corresponds to a norm subgroup whose valuation image is all of $\mathbf Z$; it need not contain the chosen $\pi$ itself, because the valuation-one norm may be $u\pi$.

### 12.2 Multiplicative pieces and Galois pieces

Under arithmetic reciprocity, the reusable identifications are

$$
\begin{array}{c|c}
K^\times/\mathcal O^\times\cong\mathbf Z
&\text{dense Frobenius powers in }\widehat{\mathbf Z}\\
\mathcal O^\times
&\text{abelian inertia}\\
\mathcal O^\times/U^1\cong k^\times
&\text{tame abelian inertia}\\
U^1
&\text{wild abelian inertia}\\
U^n
&\text{$n$th upper ramification subgroup}.
\end{array}
$$

At finite level, a uniformizer maps to an element whose image in the unramified quotient is arithmetic Frobenius. It need not select a canonical lift through inertia. Units map exactly to inertia, and $U^n$ maps exactly to $G^n$.

### 12.3 Norm tests

For finite abelian $L/K$ and $x\in K^\times$,

$$
x\in N_{L/K}(L^\times)
\quad\Longleftrightarrow\quad
\operatorname{rec}_{L/K}(x)=1.
$$

The test separates naturally:

1. The valuation of $x$ must be divisible by $f(L/K)$.
2. After removing a suitable norm of that valuation, the remaining unit must lie in $N(\mathcal O_L^\times)$.
3. Reduction detects the first unit obstruction; higher $U^n$ detect ramified obstructions invisible modulo $\mathfrak m$.

For unramified $L/K$, only step 1 remains. For tame total ramification, the valuation is unrestricted, principal units are norms, and the residue-unit class contains the elementary obstruction. In wild ramification, higher principal-unit layers contribute.

For a finite Galois but nonabelian extension $E/K$, first replace it by its maximal abelian subextension $M$. Then

$$
x\in N_{E/K}(E^\times)
\quad\Longleftrightarrow\quad
x\in N_{M/K}(M^\times).
$$

### 12.4 Functoriality at a glance

For every finite $L/K$, with $i_*$ induced by $G_L\subset G_K$ and $\operatorname{Ver}$ the transfer,

$$
\operatorname{rec}_K(N_{L/K}x)=i_*(\operatorname{rec}_L(x))
\qquad(x\in L^\times),
$$

and

$$
\operatorname{rec}_L(a)=
\operatorname{Ver}_{L/K}(\operatorname{rec}_K(a))
\qquad(a\in K^\times).
$$

The first formula pairs norm with Galois inclusion. The second pairs multiplicative inclusion with Galois transfer. Norms and transfers are transitive in towers.

### 12.5 Characters at a glance

For a profinite abelian coefficient group $A$,

$$
\{\text{continuous characters }G_K\to A\}
\cong
\{\text{continuous characters }K^\times\to A\}.
$$

Under this identification:

$$
\begin{array}{c|c}
\chi(\mathcal O^\times)=1&\chi\text{ is unramified}\\
\chi(\pi)&\chi(\operatorname{Frob}_{\mathrm{arith}})\\
\chi(U^n)=1&\chi\text{ is trivial on }G_K^n\\
\chi\circ N_{L/K}&\chi|_{G_L}.
\end{array}
$$

For a nonprofinite target, retain only the characters that extend continuously to $\widehat{K^\times}$; relative compactness of the image is necessary, and extension to the completion is the exact criterion.

### 12.6 Conclusion

Local class field theory begins with a striking mismatch. On one side lies the concrete topological group $K^\times$, decomposed by valuation, residue units, and infinitesimal units. On the other lies the apparently remote collection of all finite abelian extensions of $K$. Reciprocity proves that the mismatch is an illusion: every finite Galois quotient is already encoded by a norm quotient of $K^\times$.

The proof reveals why the correspondence is rigid. Hilbert 90 removes the first cohomological obstruction. The local Brauer invariant turns every remaining norm obstruction into a rational number modulo one. Its fundamental classes identify Galois abelianizations with norm quotients, while the explicit unramified and formal-module towers show that these quotients are cofinal and realize every open finite-index subgroup. Topology then assembles the finite maps into a dense embedding

$$
K^\times\hookrightarrow G_K^{\mathrm{ab}}
$$

and an isomorphism after profinite completion.

The final picture is exact at every scale. Valuation is Frobenius, units are inertia, deeper units are higher ramification, norms are kernels, and open subgroups are fields. A one-dimensional Galois character may therefore be read as a multiplicative character of $K^\times$, with its unramified value, conductor, restriction, and ramification all visible in elementary local coordinates. Reciprocity does not merely classify extensions; it turns the entire abelian Galois theory of a local field into the arithmetic of its own nonzero elements.
