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
    - [Coefficient fields and standard characters](#116-coefficient-fields-and-standard-characters)
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

The valuation-theoretic foundations are those of Books 1--2. In particular, we use the unique-extension and finite-completeness theorem of Book 1, Theorem 10.3, the fundamental equality of Book 2, Theorem 2.3,

$$
[L:K]=e(L/K)f(L/K),
$$

the norm-valuation formula of Book 2, Theorem 4.1,

$$
v_K(N_{L/K}x)=f(L/K)v_L(x),
$$

and the classification of unramified extensions in Book 2, Theorem 7.2. We also retain Book
2's arithmetic convention that $x\mapsto x^q$ is arithmetic Frobenius. These references fix
notation and prevent us from rebuilding finite-extension theory inside class field theory. The
norm-index theorem, local invariant, finite Artin map, and functoriality are proved below.
Existence, the higher-unit ramification match, and the character classification are proved
conditional on the exact norm-filtration input isolated in Section 6.5.

One boundary deserves emphasis. Book 3 develops ramification theory systematically and is
available in the cumulative reading order, but it does not prove the exact comparison between
norms of units and upper ramification groups needed in Chapters 6 and 8 below. Section 6.5
therefore isolates that comparison as **Hypothesis NF**. This is not a cosmetic citation:
Hypothesis NF is the Herbrand norm-filtration theorem, including its endpoint convention and
the exact cokernel at every step. The present book proves all deductions from NF, but it does
not claim to prove NF itself. Every later result that depends on it is marked **[NF]**.

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

First, compactness shows that norm images are closed and helps identify their topology. Second,
cyclic cohomology explains why a norm quotient is the natural degree-zero cohomology group and
why Hilbert's Theorem 90 removes a neighboring obstruction. Third, the Brauer group of a local
field supplies a canonical fundamental class of every finite Galois extension. Capping with
that class turns the abstract abelianization of the Galois group into a norm quotient. Finally,
conditional on NF, explicit unramified and formal-module extensions show that enough abelian
extensions exist to realize every open finite-index subgroup.

The order matters. Norm computations suggest reciprocity but cannot classify wild extensions by themselves. Cohomology produces the finite reciprocity maps but, without an existence construction, would not prove that all open subgroups arise. The explicit construction supplies that missing half rather than hiding it behind the name “existence theorem.”

There is also a logical danger in the opposite direction. It would be circular to define the
field belonging to an open subgroup by reciprocity and then use that field to prove
reciprocity. The conditional argument avoids this in two independent moves. The local
invariant and the fundamental class first construct the Artin isomorphism for an already given
finite Galois extension. Lubin–Tate division fields are then constructed directly from power
series and Eisenstein polynomials. Only after NF supplies their norm groups do we use them to
realize an arbitrary open subgroup. Keeping these two halves separate is the central proof
discipline of the book.

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

Choose $b\in L$ with $\operatorname{Tr}_{L/K}(b)=1$, possible because $L/K$ is separable, and consider the one-variable polynomial

$$
F(T)=N_{L/K}(1+bT)-1\in K[T].
$$

Its constant term is $0$ and its linear coefficient is $\operatorname{Tr}(b)=1$. Choose $c$ so large that $b\mathfrak m_K^c\subseteq\mathfrak m_L$ and, for every coefficient $a_i$ of $F(T)-T$, one has

$$
v_K(a_i)+(i-1)c\geq1\qquad(i\geq2).
$$

We claim that $F$ maps $\mathfrak m_K^c$ onto itself. Given $s\in\mathfrak m_K^c$, start with $t_0=s$ and define

$$
t_{j+1}=t_j+s-F(t_j).
$$

For $t,t'\in\mathfrak m_K^c$, factoring $t^i-(t')^i$ and using the choice of $c$ gives

$$
v_K\bigl((F(t)-t)-(F(t')-t')\bigr)
\geq v_K(t-t')+1.
$$

Thus the displayed iteration is a strict contraction of the complete ball $\mathfrak m_K^c$. It converges to the unique $t\in\mathfrak m_K^c$ with $F(t)=s$. Since $bt\in\mathfrak m_L$, the element $1+bt$ lies in $U_L^1$ and has norm $1+s$. Hence $U_K^c\subseteq N(U_L^1)$. $\square$

For a finite inseparable extension, pass through the maximal separable subextension and use the explicit power form of a purely inseparable norm. Local reciprocity itself concerns separable extensions, so the proposition above is the form needed later.

It follows that $N_{L/K}(L^\times)$ is open. Its valuation image has finite index and its unit image contains $U_K^c$, so the whole norm group has finite index. It is also closed: the unit part is compact, and the valuation separates its translates into a discrete family.

### 2.5 The index question

Topology proves finiteness but not the correct index. Direct unit calculations settle special cases, yet wild ramification defeats any formula depending only on $e$ and $f$. The desired equality

$$
[K^\times:N_{L/K}(L^\times)]=[L:K]
$$

is false outside the abelian case. If $L/K$ is finite Galois, the correct index is the degree of its maximal abelian subextension; for a finite separable nonnormal extension there is no comparable formula obtained merely by naming a maximal abelian intermediate field. Even for a cyclic wildly ramified extension, direct calculation on all unit layers is possible only after developing substantial ramification machinery.

For brevity write $NL^\times=N_{L/K}(L^\times)$. The way forward is to recognize $K^\times/NL^\times$ as a cohomology group and then compute it through a canonical invariant. This shifts the problem from tracking every unit norm separately to understanding one two-dimensional obstruction.

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

For completeness, surjectivity onto the relative Brauer group is part of the assertion and is not
being hidden in the word “cyclic.” Let $A$ be central simple over $K$ and split by $L$, and choose
$A\otimes_KL\cong\operatorname{End}_L(V)$. A lift of the semilinear action of $\sigma$ is an
invertible semilinear operator $T$ on $V$, unique up to an $L$-linear scalar after changing the
splitting. The operator $T^n$ is $L$-linear and commutes with the full matrix algebra, so it is
multiplication by some $a\in L^\times$. It also commutes with $T$, whose semilinearity sends
multiplication by $a$ to multiplication by $\sigma(a)$; hence $\sigma(a)=a$ and $a\in K^\times$.
Descent with respect to $T$ identifies $A$, up to a matrix factor, with $(L/K,\sigma,a)$.
Replacing $T$ by $bT$ changes $a$ to $N_{L/K}(b)a$, and every change of splitting has this form
after an inner conjugation. Thus the parameter is unique modulo norms, proving both surjectivity
and injectivity of the displayed map. This is the cyclic specialization of the crossed-product
descent written out for a general Galois group in Section 4.5.

### 3.5 The unramified cyclic computation

Let $L/K$ be unramified of degree $n$ and let $\sigma=\operatorname{Frob}_{L/K}$ be arithmetic Frobenius. Units are norms and valuations of norms are multiples of $n$, so

$$
K^\times/NL^\times\cong\mathbf Z/n\mathbf Z,
$$

generated by the class of $\pi$. The cyclic algebra

$$
(L/K,\operatorname{Frob},\pi)
$$

is therefore the basic class split by $L$. It is nontrivial when $n>1$; for $n=1$ the norm
quotient and the Brauer class are both trivial.

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

is obtained as follows. Over an algebraic closure, $D$ becomes $M_d$; a matrix presentation uses only finitely many coefficients and therefore descends to a finite splitting field $S/K$. For $x\in D$, take the determinant of its image in $M_d(S)$. A second matrix presentation differs after a common scalar extension by an inner automorphism, which leaves determinant unchanged. Galois conjugation also gives another presentation and therefore fixes the determinant, so it lies in $K$. This proves independence of $S$ and of the presentation. It also proves multiplicativity and shows that the resulting map extends the ordinary determinant after every splitting. The same construction applied to the characteristic polynomial defines the reduced characteristic polynomial. Define

$$
w_D(0)=+\infty,
\qquad
w_D(x)=\frac1d\,v_K(\operatorname{Nrd}(x))\quad(x\in D^\times).
$$

Here is the noncommutative triangle argument. For $a\in D$, the subalgebra $E=K(a)$ is a commutative field. If $m=[E:K]$, the reduced characteristic polynomial of $a$ is its field characteristic polynomial raised to the power $d/m$; after passing to a splitting field this follows by grouping the $d$ eigenvalues into the $m$ conjugates of $a$. Hence

$$
\operatorname{Nrd}_{D/K}(a)=N_{E/K}(a)^{d/m},
$$

and the norm-valuation formula for the finite local extension $E/K$ gives

$$
w_D(a)=\frac1m v_K(N_{E/K}(a))
=\frac1{e(E/K)}v_E(a).
$$

In particular, $w_D(a)\geq0$ exactly when $a$ is integral over $\mathcal O$. Now suppose $w_D(x)\leq w_D(y)$. If $x=0$, then also $y=0$ and the desired inequality is immediate, so assume $x\ne0$. Multiplicativity of reduced norm gives $w_D(x^{-1}y)\geq0$, so $x^{-1}y$ is integral. The element $1+x^{-1}y$ is integral in the same commutative field, and therefore has nonnegative $w_D$-value. Thus

$$
w_D(x+y)=w_D(x)+w_D(1+x^{-1}y)\geq w_D(x).
$$

This proves the ultrametric inequality; multiplicativity of reduced norm gives additivity. Thus $w_D$ is a valuation on the skew field $D$. Its valuation ring

$$
\mathcal O_D=\{x:w_D(x)\geq0\}
$$

has a unique maximal two-sided ideal $\mathfrak P_D$, and the quotient

$$
\overline D=\mathcal O_D/\mathfrak P_D
$$

is a division ring. The absolute value defined by $w_D$ is a nonarchimedean $K$-norm on the finite-dimensional vector space $D$. Equivalence of finite-dimensional norms over the complete field $K$ makes $\mathcal O_D$ compact, while $\mathfrak P_D$ is open. Hence the quotient is finite. Wedderburn's theorem makes it a finite field.

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

Centrality sharpens the equality. Conjugation by an element of $D^\times$ preserves $\mathcal O_D$ and $\mathfrak P_D$, hence induces an automorphism of the finite field $\overline D$ fixing $k$. If $x$ and $y$ have the same value modulo $\mathbf Z$, then, after multiplying $xy^{-1}$ by a power of the central element $\pi$, it is a unit. Conjugation by its residue is trivial because $\overline D$ is commutative. Thus there is a well-defined homomorphism

$$
\theta:w_D(D^\times)/\mathbf Z
\longrightarrow\operatorname{Gal}(\overline D/k). \tag{4.1}
$$

The decisive point is to prove, rather than presume, that this action is faithful and has fixed field $k$. We do this by constructing an inertial lift of $\overline D$ and then correcting conjugacy one valuation layer at a time.

**Graded-center lemma.** There is an unramified maximal subfield $E/K$ of $D$ with residue field $\overline D$ and an element $\Pi_D\in D^\times$ of least positive value such that

$$
\Pi_DE\Pi_D^{-1}=E.
$$

For this choice, conjugation by $\Pi_D$ induces a generator of $\operatorname{Gal}(\overline D/k)$. Consequently (4.1) is an isomorphism; in particular it is faithful and its fixed field in $\overline D$ is exactly $k$.

**Proof.** We first lift the whole residue field. Choose a primitive element $\bar a$ of the finite separable extension $\overline D/k$, let $\bar p\in k[T]$ be its minimal polynomial, and choose a monic lift $p\in\mathcal O[T]$. Pick any $a_0\in\mathcal O_D$ reducing to $\bar a$. The subfield $K(a_0)$ is commutative and complete. In its valuation ring,

$$
p(a_0)\in\mathfrak P_D\cap K(a_0),
\qquad
p'(a_0)\in\mathcal O_D^\times,
$$

because $\bar p$ is separable. Ordinary Hensel lifting inside the commutative field $K(a_0)$ therefore gives $a\equiv a_0\pmod{\mathfrak P_D}$ with $p(a)=0$. Since $\bar p$ is irreducible, so is $p$, and

$$
E=K(a)
$$

is unramified of degree $f_D$ with residue field $k(\bar a)=\overline D$.

Any separable commutative subfield of a central division algebra of degree $d$ has degree at most $d$: after extending scalars to a separable closure, its primitive idempotents embed as nonzero orthogonal idempotents in $M_d$, and there can be at most $d$ of them. Hence $f_D\leq d$. On the other hand,

$$
w_D(D^\times)\subseteq\frac1d\mathbf Z
$$

gives $e_D\leq d$, while $d^2=e_Df_D$ gives $f_D\geq d$. Thus

$$
e_D=f_D=d. \tag{4.2}
$$

In particular, $E$ has degree $d$ and is a maximal commutative subfield.

We next record and prove the close-conjugacy statement needed to make $E$ stable. Let $\phi,\psi:E\hookrightarrow D$ be two $K$-embeddings inducing the same map on residue fields. We claim that there is a $c\in1+\mathfrak P_D$ such that

$$
c\phi(x)c^{-1}=\psi(x)\qquad(x\in E). \tag{4.3}
$$

Choose an element $\Pi$ of least positive value $1/d$, and set

$$
\mathfrak P_D^r=\{x\in D:w_D(x)\geq r/d\}\qquad(r\geq1).
$$

These are the ordinary powers of $\mathfrak P_D$. We construct $c_r\in1+\mathfrak P_D$ such that, with $\phi_r=\operatorname{Ad}(c_r)\circ\phi$,

$$
\psi(x)-\phi_r(x)\in\mathfrak P_D^r
\qquad(x\in\mathcal O_E). \tag{4.4}
$$

For $r=1$, take $c_1=1$; equality of the residue embeddings gives (4.4). Suppose $c_r$ has been constructed. Modulo $\mathfrak P_D^{r+1}$, the discrepancy

$$
\delta_r(x)=\psi(x)-\phi_r(x)
$$

descends to a $k$-derivation from $\overline E=\overline D$ to the $\overline E$-bimodule

$$
M_r=\mathfrak P_D^r/\mathfrak P_D^{r+1}.
$$

Indeed, multiplication by $\pi$ carries $\mathfrak P_D^r$ into $\mathfrak P_D^{r+d}\subseteq\mathfrak P_D^{r+1}$, so the discrepancy depends only on the residue class of $x\in\mathcal O_E$. Expanding it on a product and using (4.4) gives

$$
\delta_r(xy)=x\delta_r(y)+\delta_r(x)y
$$

in $M_r$; the two embeddings give the same left and right residue actions there. Every derivation of the finite separable field $\overline E/k$ into an $\overline E$-bimodule is inner. To verify this explicitly, choose a separability idempotent

$$
\sum_i a_i\otimes b_i\in\overline E\otimes_k\overline E,
\qquad
\sum_i a_ib_i=1,
$$

with

$$
\sum_i xa_i\otimes b_i=\sum_i a_i\otimes b_ix
\qquad(x\in\overline E).
$$

Such an element is concrete here: since finite fields are Galois,

$$
\overline E\otimes_k\overline E
\xrightarrow{\sim}
\prod_{\tau\in\operatorname{Gal}(\overline E/k)}\overline E,
\qquad
x\otimes y\longmapsto(x\tau(y))_\tau.
$$

Take the idempotent that is $1$ in the identity component and $0$ in all the others. Its product under multiplication is $1$, and the displayed commutation identity follows componentwise.

For a derivation $\delta$, applying $a\otimes b\mapsto a\delta(b)$ to the last identity shows, with $m=\sum_i a_i\delta(b_i)$, that

$$
\delta(x)=xm-mx.
$$

Thus $\delta(x)=tx-xt$ with $t=-m$.

Apply this to $\delta_r$ and lift the resulting element of $M_r$ to $t_r\in\mathfrak P_D^r$. Put

$$
c_{r+1}=(1+t_r)c_r.
$$

Since $t_r^2\in\mathfrak P_D^{r+1}$,

$$
(1+t_r)\phi_r(x)(1+t_r)^{-1}
\equiv\phi_r(x)+t_r\phi_r(x)-\phi_r(x)t_r
\pmod{\mathfrak P_D^{r+1}}.
$$

The choice of $t_r$ cancels $\delta_r$, proving (4.4) with $r+1$. The infinite product of the factors $1+t_r$ converges because $t_r\in\mathfrak P_D^r$; its limit $c$ lies in $1+\mathfrak P_D$, and passage to the limit gives (4.3). This constructs and verifies every successive correction.

Return to the embedded field $E$ above and let $\Pi$ have value $1/d$. Conjugation by $\Pi$ induces some $\tau\in\operatorname{Gal}(\overline D/k)$. The unramified classification gives a unique $\sigma\in\operatorname{Gal}(E/K)$ inducing $\tau$ on residues. The two embeddings

$$
x\longmapsto\Pi x\Pi^{-1},
\qquad
x\longmapsto\sigma(x)
$$

have the same reduction, so (4.3) supplies $c\in1+\mathfrak P_D$ for which

$$
c\Pi x\Pi^{-1}c^{-1}=\sigma(x).
$$

Replacing $\Pi$ by $\Pi_D=c\Pi$ preserves its least positive value and gives

$$
\Pi_Dx\Pi_D^{-1}=\sigma(x)\qquad(x\in E). \tag{4.5}
$$

It remains to prove that $\sigma$ has full order $d$. If its order were $m<d$, then $\Pi_D^m$ would centralize $E$. Here the centralizer of $E$ is exactly $E$, as can be checked directly after a separable scalar extension splitting $D$. The algebra $E$ then becomes a product of $d$ copies of the splitting field, acting on a $d$-dimensional space through $d$ nonzero orthogonal idempotents. Each idempotent has one-dimensional image, so the commuting matrices are precisely the diagonal matrices, a space of dimension $d$. Descending gives a centralizer of $K$-dimension $d$, already filled by $E$. Hence $\Pi_D^m\in E$. But $E/K$ is unramified, so every value on $E^\times$ is integral, whereas

$$
w_D(\Pi_D^m)=m/d\notin\mathbf Z.
$$

This contradiction proves that $\sigma$ has order $d$. By (4.2), both the source and target of (4.1) have order $d$, and the least positive value class maps to the generator induced by $\sigma$. Thus (4.1) is an isomorphism. Its image is the full Galois group of the finite field $\overline D/k$, whose fixed field is $k$. This proves all assertions. $\square$

Let $F$ denote arithmetic Frobenius on $E/K$. By the lemma, conjugation by $\Pi_D$ acts as $F^s$ for some $s$ prime to $d$. The elements

$$
1,\Pi_D,\ldots,\Pi_D^{d-1}
$$

are linearly independent over $E$ because their values lie in distinct cosets modulo $\mathbf Z$. They account for $d^2$ dimensions over $K$, so $E$ and $\Pi_D$ generate all of $D$. Since conjugation by $\Pi_D$ has order $d$, the element $\Pi_D^d$ commutes with $E$; it also commutes with $\Pi_D$ and is therefore central. Its value is one, so $\Pi_D^d=c\pi$ for $c\in\mathcal O^\times$. Replacing $\Pi_D$ by $b\Pi_D$, with $b\in E^\times$, multiplies its $d$th power by $N_{E/K}(b)$. The unramified unit norm is surjective, so choose $b$ with norm $c^{-1}$. Then

$$
\Pi_D^d=\pi.
$$

Consequently

$$
D\cong(E/K,F^s,\pi).
$$

If $r$ is inverse to $s$ modulo $d$, write $rs=1+td$. In the cyclic algebra $(E/K,F,\pi^r)$, if $z$ is its crossed-product generator, then

$$
\Pi'=\pi^{-t}z^s
$$

conjugates $E$ by $F^s$ and satisfies $(\Pi')^d=\pi$. It therefore gives an isomorphism

$$
(E/K,F,\pi^r)\cong(E/K,F^s,\pi)\cong D.
$$

This is the local cyclic presentation of every central division algebra, with both the residue action and the parameter normalization now determined.

### 4.3 Unramified splitting and the invariant

Every central division algebra over $K$ is split by a finite unramified extension. Indeed, the field $E$ just constructed is a maximal subfield of degree $d$. The action

$$
D\otimes_KE\longrightarrow\operatorname{End}_E(D),
\qquad
(a\otimes b)(x)=axb,
$$

where $D$ is viewed as a right $E$-vector space, is a nonzero homomorphism between central simple $E$-algebras of the same dimension $d^2$. It is therefore an isomorphism, and $D\otimes_KE\cong M_d(E)$.

Let $K_d/K$ be the unramified extension of degree $d$, with arithmetic Frobenius $F$. For $r\in\mathbf Z$, put

$$
A_{r,d}=(K_d/K,F,\pi^r).
$$

Its Brauer class depends only on $r$ modulo $d$, because $N_{K_d/K}(\pi)=\pi^d$ up to a unit and every unit is a norm. Define

$$
\operatorname{inv}_K(A_{r,d})=\frac rd\pmod{\mathbf Z}.
$$

We make independence of the denominator explicit. If $d\mid N$, the cyclic tower relation gives

$$
[A_{r,d}]=[A_{rN/d,N}]. \tag{4.6}
$$

To see the relation without using an invariant, inflate the crossed-product cocycle from
$\operatorname{Gal}(K_d/K)$ to $\operatorname{Gal}(K_N/K)$. In the regular crossed-product module, the $N/d$ cosets of the subgroup give matrix units, while the product around one quotient cycle is still $\pi^r$. The inflated crossed product is therefore $M_{N/d}(A_{r,d})$; writing the same cocycle with the degree-$N$ Frobenius generator gives $A_{rN/d,N}$. Thus (4.6) is a Brauer equivalence proved at the algebra level.

Any two denominators have a common multiple. Equation (4.6) therefore identifies the union of the relative groups split by unramified extensions with the direct limit

$$
\varinjlim_d\frac1d\mathbf Z/\mathbf Z=\mathbf Q/\mathbf Z.
$$

Tensor products of cyclic algebras multiply their parameters after passage to a common denominator, so they add the corresponding fractions. The splitting criterion says $A_{r,d}$ is split exactly when $d\mid r$, exactly when its proposed invariant is zero.

When $\gcd(r,d)=1$, the algebra $A_{r,d}$ is visibly a division algebra. Write its elements uniquely as

$$
x=x_0+x_1z+\cdots+x_{d-1}z^{d-1},
\qquad x_i\in K_d,
$$

and set

$$
w(x)=\min_i\left(v_{K_d}(x_i)+\frac{ri}{d}\right).
$$

The fractional parts $ri/d$ are distinct modulo $\mathbf Z$, so a nonzero sum has a unique least-valued term. In a product, the product of the two least terms remains uniquely least after using $zx=F(x)z$ and $z^d=\pi^r$. Hence $w(xy)=w(x)+w(y)$ and there are no zero divisors. A finite-dimensional central simple algebra without zero divisors is a division algebra. If $g=\gcd(r,d)$, equation (4.6), applied in a common unramified splitting field, identifies the Brauer class with that of $A_{r/g,d/g}$. The latter is a division algebra by the preceding argument, so the underlying division algebra has degree $d/g$; the invariant is therefore naturally the reduced fraction $r/d$.

**Theorem 4.1 (local invariant theorem).** The preceding construction gives a canonical isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)\xrightarrow{\sim}\mathbf Q/\mathbf Z.
$$

For every finite extension $L/K$ of degree $n$,

$$
\operatorname{inv}_L(\operatorname{res}_{L/K}\alpha)
=n\operatorname{inv}_K(\alpha).
$$

**Proof.** Surjectivity follows because $A_{r,d}$ realizes $r/d$. The cyclic presentation just proved shows that every central division algebra has one of these classes. The common-denominator relation (4.6) proves that the assigned fraction is independent of every presentation and that addition agrees with tensor product. If the invariant is zero, a common-denominator parameter is a norm and the cyclic splitting criterion makes the algebra a matrix algebra; hence the invariant is injective.

It remains to verify restriction. We first treat finite separable extensions. Such an extension has
a maximal unramified subextension, followed by a totally ramified extension, and restriction is
transitive. It is therefore enough to handle those two cases. First suppose $L/K$ is unramified of
degree $m$. Put

$$
g=\gcd(d,m),\qquad d'=d/g,\qquad m'=m/g.
$$

The algebra $K_d\otimes_KL$ is a product of $g$ copies of the unramified extension of $L$ of degree $d'$. The crossed-product generator cyclically permutes these factors. Taking a full corner removes that permutation matrix factor; going once around the resulting degree-$d'$ cycle applies relative arithmetic Frobenius and contributes the parameter $\pi^{m'r}$. Thus

$$
\operatorname{res}_{L/K}A_{r,d}
\sim A^{\,L}_{m'r,d'},
$$

where the superscript indicates that the cyclic algebra is formed over $L$. This calculation includes both the common unramified factors and the change from base Frobenius to relative Frobenius. Hence

$$
\operatorname{inv}_L(\operatorname{res}A_{r,d})=m\frac rd.
$$

Now suppose $L/K$ is totally ramified and separable of degree $e$. It is linearly disjoint from
$K_d$, so $LK_d/L$ remains unramified of degree $d$ with the same arithmetic Frobenius. Write
$\pi=u\pi_L^e$. The unit $u$ is a norm from the unramified extension $LK_d/L$, so the restricted
cyclic algebra has parameter equivalent to $\pi_L^{er}$. Its invariant is $er/d$. Combining the
unramified and totally ramified stages gives the restriction formula for every finite separable
extension.

We next prove the missing purely inseparable case. We will use explicitly that scalar extension of
a central simple algebra remains central simple over an arbitrary field extension, not merely a
separable one. Indeed, after extending further to an algebraic closure it becomes a full matrix
algebra. Any two-sided ideal after the first scalar extension becomes either zero or the whole
matrix algebra after the second, and faithful scalar extension descends that conclusion. The same
conclusion holds for the center because commuting with a basis of the algebra is a system of linear
equations: its solution space commutes with scalar extension, and the center of a full matrix
algebra consists only of scalars. Thus the center has dimension one over the new ground field. The
scalar extension consequently has a Brauer class and a well-defined **index**, the degree of the
unique central division algebra in that class.

Let $P/K$ be finite purely inseparable of degree $a$. The case $a=1$ is immediate; a nontrivial
case occurs only in characteristic $p>0$. Its residue extension is purely inseparable, hence
trivial because the finite residue field $k$ is perfect. The fundamental equality therefore gives

$$
e(P/K)=a.
$$

The separable extension $K_d/K$ and the purely inseparable extension $P/K$ are linearly disjoint:
an element in their intersection is both separable and purely inseparable over $K$, and hence lies
in $K$. Consequently $P_d=PK_d$ has degree $d$ over $P$. It is the unramified extension of $P$ of
degree $d$. Indeed, the residue field $k_d$ of $K_d$ embeds in the residue field of $P_d$, while
the residue field of $P$ is still $k$. Thus $f(P_d/P)\geq d$; the opposite inequality follows from
$f(P_d/P)\leq[P_d:P]=d$. Hence $f=d$ and $e=1$. The automorphism that is the identity on $P$ and
arithmetic Frobenius $F$ on $K_d$ reduces to $x\mapsto x^{|k|}$, so it is precisely the arithmetic
Frobenius $F_P$ of $P_d/P$.

Scalar extension preserves the displayed cyclic presentation, not just its Brauer class. If $z$
is the crossed-product generator, its defining relations after base change are still

$$
zx=F_P(x)z\quad(x\in P_d),
\qquad z^d=\pi^r.
$$

Hence

$$
A_{r,d}\otimes_KP\cong(P_d/P,F_P,\pi^r).
$$

Choose a uniformizer $\varpi$ of $P$. Since $v_P(\pi)=a$, one has
$\pi=u\varpi^a$ for some $u\in\mathcal O_P^\times$. Units are norms from the unramified extension
$P_d/P$, and changing $z$ to $bz$ multiplies $z^d$ by $N_{P_d/P}(b)$. The unit factor can therefore
be removed, giving

$$
[A_{r,d}\otimes_KP]=[A^{\,P}_{ar,d}]
\quad\text{in }\operatorname{Br}(P).
$$

This also records exactly what happens to the Brauer index. If $h=\gcd(d,ar)$, the reduction of a
cyclic class to lowest terms proved above says that the division algebra in this class is
$A^{\,P}_{ar/h,d/h}$ and has degree, hence index, $d/h$. This is the order of $ar/d$ in
$\mathbf Q/\mathbf Z$. With the arithmetic Frobenius and uniformizer normalization used to define
$\operatorname{inv}_P$, the preceding scalar extension therefore has invariant

$$
\operatorname{inv}_P(A_{r,d}\otimes_KP)
=\frac{ar}{d}
=a\operatorname{inv}_K(A_{r,d}).
$$

Every class in $\operatorname{Br}(K)$ has an $A_{r,d}$ representative, so this proves the formula
for every finite purely inseparable extension.

Finally let $L/K$ be any finite extension, and let $S$ be the maximal separable subextension of
$L/K$. Then $S/K$ is separable and $L/S$ is purely inseparable: in characteristic $p$, a suitable
$p$-power of every element of $L$ is separable over $K$ and therefore belongs to $S$.
Transitivity of scalar extension, followed by the two cases just proved, gives

$$
\begin{aligned}
\operatorname{inv}_L(\operatorname{res}_{L/K}\alpha)
&=[L:S]\operatorname{inv}_S(\operatorname{res}_{S/K}\alpha)\\
&=[L:S][S:K]\operatorname{inv}_K(\alpha)\\
&=[L:K]\operatorname{inv}_K(\alpha).
\end{aligned}
$$

This proves the restriction formula for arbitrary finite extensions. $\square$

For a finite separable extension $L/K$, the proof also gives the corestriction formula

$$
\operatorname{inv}_K(\operatorname{cor}_{L/K}\beta)
=\operatorname{inv}_L(\beta).
$$

Multiplication by $[L:K]$ on $\mathbf Q/\mathbf Z$ is surjective. The restriction formula therefore shows that every $\beta\in\operatorname{Br}(L)$ has the form $\operatorname{res}_{L/K}(\alpha)$ for some $\alpha\in\operatorname{Br}(K)$. The defining restriction--corestriction identity gives

$$
\operatorname{cor}_{L/K}(\beta)
=\operatorname{cor}_{L/K}\operatorname{res}_{L/K}(\alpha)
=[L:K]\alpha,
$$

whose invariant is

$$
[L:K]\operatorname{inv}_K(\alpha)
=\operatorname{inv}_L(\operatorname{res}\alpha)
=\operatorname{inv}_L(\beta).
$$

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

We recall the construction so that this identification carries no hidden convention. A normalized two-cocycle

$$
c:G\times G\longrightarrow L^\times
$$

defines the crossed product

$$
A_c=\bigoplus_{g\in G}Lu_g,
$$

with multiplication

$$
u_gx=g(x)u_g,
\qquad
u_gu_h=c(g,h)u_{gh}.
$$

The cocycle identity is exactly associativity. Replacing $c$ by the coboundary of a one-cochain amounts to rescaling the basis elements $u_g$, so the Brauer class depends only on $[c]$. Multiplication of cocycles corresponds to tensor product after matrix factors are removed, giving a homomorphism

$$
H^2(G,L^\times)\longrightarrow\operatorname{Br}(L/K).
$$

Conversely, let $A$ be central simple over $K$ and split by $L$. Choose an isomorphism $A\otimes_KL\cong\operatorname{End}_L(V)$. For each $g\in G$, the two $g$-semilinear actions on this matrix algebra differ by conjugation by an element $T_g\in\operatorname{GL}_L(V)$; this is the elementary fact that every automorphism of a full matrix algebra is inner, proved by carrying a complete system of matrix units to its image. The products satisfy

$$
T_g,g(T_h)=c(g,h)T_{gh}
$$

for unique scalars $c(g,h)\in L^\times$. Associativity makes $c$ a cocycle, changing the $T_g$ changes it by a coboundary, and the fixed algebra reconstructed from these semilinear operators is Brauer equivalent to $A_c$. The two constructions are inverse. This proves the displayed identification and fixes its crossed-product convention.

Under the invariant map it is cyclic of order $n$. The unique class

$$
u_{L/K}\in H^2(G,L^\times)
$$

with

$$
\operatorname{inv}_K(u_{L/K})=\frac1n
$$

is the **local fundamental class**.

Its normalization is compatible in towers. More explicitly, suppose $L/K$ is Galois, put
$G=\operatorname{Gal}(L/K)$ and $H=\operatorname{Gal}(L/M)$, and regard
$u_{L/K}\in H^2(G,L^\times)$ and $u_{L/M}\in H^2(H,L^\times)$. Then

$$
\operatorname{res}_H^G(u_{L/K})=u_{L/M},
\qquad
\operatorname{cor}_H^G(u_{L/M})=[M:K]u_{L/K}.
$$

Indeed their local invariants are respectively $1/[L:M]$ and
$[M:K]/[L:K]$. In an unramified cyclic extension, $u_{L/K}$ is represented by

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

We use the elementary cohomological-triviality criterion: a $G$-module $A$ with $\widehat H^0(H,A)=\widehat H^1(H,A)=0$ for every subgroup $H$ has $\widehat H^r(H,A)=0$ for all $r$. For dimension shifting, map an induced module of the form $\mathbf Z[G]\otimes_{\mathbf Z}A$ onto $A$, and embed $A$ into the corresponding coinduced module. These induced and coinduced modules have zero Tate cohomology for every subgroup. Their kernels and cokernels shift Tate cohomology in the two directions, so iteration moves any desired degree into one of the two assumed vanishing degrees. Thus $A$ is cohomologically trivial.

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

Here is the sign check hidden in that sentence. For $G=\langle\sigma\rangle$, use the periodic resolution whose differentials alternate $\sigma-1$ and $1+\sigma+\cdots+\sigma^{n-1}$, identify the homology class of $[\sigma]$ with $1\in\mathbf Z/n\mathbf Z$, and represent the fundamental class by the crossed product

$$
(L/K,\sigma,a),
\qquad zx=\sigma(x)z,\qquad z^n=a.
$$

With these conventions, capping sends $[\sigma]$ to the class of $a$ in $K^\times/NL^\times$: on the periodic resolution the last relation is exactly multiplication by $a$. Taking $\sigma$ to be arithmetic Frobenius and $a=\pi$ therefore makes the inverse cap-product map send $\pi$ to arithmetic Frobenius. Reversing the crossed-product relation, or using $[\sigma^{-1}]$ as the homology generator, inverts reciprocity. Thus the convention is fixed at the chain level rather than by an ambiguous phrase about a lift of Frobenius.

The map is continuous because its kernel is an open norm group and its target is finite discrete. It is surjective because the induced map on the quotient is an isomorphism. Thus at every finite level there is genuine surjectivity; only at the infinite level will surjectivity become density.

### 5.5 Norm limitation

Let $M=L^{[G,G]}$ be the maximal abelian subextension of a finite Galois extension $L/K$. Since

$$
G^{\mathrm{ab}}\cong\operatorname{Gal}(M/K),
$$

norm transitivity first gives the inclusion

$$
N_{L/K}(L^\times)
=N_{M/K}\bigl(N_{L/M}(L^\times)\bigr)
\subseteq N_{M/K}(M^\times).
$$

The fundamental-class isomorphism for $L/K$ shows that the first subgroup has index
$|G^{\mathrm{ab}}|$. Finite reciprocity for the abelian extension $M/K$ shows that the second has index

$$
[M:K]=|G^{\mathrm{ab}}|.
$$

An inclusion of finite-index subgroups with equal index is equality. This proves norm limitation without anticipating the quotient-functoriality results of Chapter 9.

**Theorem 5.3 (norm limitation).** For a finite Galois extension $L/K$ with maximal abelian subextension $M/K$,

$$
N_{L/K}(L^\times)=N_{M/K}(M^\times).
$$

In particular,

$$
[K^\times:N_{L/K}(L^\times)]=[M:K]=|G^{\mathrm{ab}}|.
$$

The statement would be false with $[L:K]$ on the right when $G$ is nonabelian. For example, for a local Galois extension with group $S_3$, the maximal abelian subextension is the quadratic field fixed by $A_3$. Its norm group has index $2$, not $6$. This is a useful counterexample to the tempting claim that every finite extension has norm index equal to its degree.

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

Finite reciprocity starts with an extension and computes its norm quotient. The classification
theorem asks the converse: given $H\subseteq K^\times$, where does the corresponding field come
from? Cohomology alone does not display enough fields. Conditional on NF, we now construct a
cofinal family of finite abelian extensions whose norm groups are

$$
\pi^{m\mathbf Z}U^n.
$$

The unramified factor realizes $\pi^{m\mathbf Z}$; conditional on NF, a formal
$\mathcal O$-module realizes $U^n$. Together they dominate every open finite-index subgroup
by Proposition 2.1.

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

The construction is independent of the chosen Lubin–Tate series in the precise sense needed later. Let $f$ and $g$ satisfy the two congruences for the same uniformizer, and let $h_{f,g}$ be the series supplied by Lemma 6.2 with linear coefficient $1$. Construct $h_{g,f}$ in the other direction. The composites

$$
h_{g,f}\circ h_{f,g}
\quad\text{and}\quad
h_{f,g}\circ h_{g,f}
$$

commute with the relevant Lubin–Tate series and have linear term $T$. Uniqueness in the recursion makes both composites the identity. Hence $h_{f,g}$ is an invertible integral power series and

$$
h_{f,g}([a]_f(T))=[a]_g(h_{f,g}(T))
\qquad(a\in\mathcal O).
$$

The displayed identity follows by observing that both sides intertwine $f$ and $g$ and have linear term $aT$. Evaluation therefore carries $\pi^n$-torsion bijectively to $\pi^n$-torsion and primitive torsion to primitive torsion. Thus different choices of $f$ produce isomorphic finite-level towers, compatibly in $n$. The isomorphism depends on the chosen linear coefficient of the intertwiner, so no false canonical equality is asserted.

Changing the uniformizer changes the splitting of the unramified direction and hence changes the coordinate description of reciprocity. What will be intrinsic is the compositum of all totally ramified abelian extensions and, after adjoining the unramified tower, the full maximal abelian extension. The construction has coordinates; the resulting classification does not.

This is the Lubin–Tate formal-module construction. Here it is not an excursion: assuming NF,
its torsion fields provide the cofinal ramified extensions needed in the proof of local
existence.

### 6.3 Torsion points and Eisenstein polynomials

For the rest of the existence construction fix the explicit choice

$$
f(T)=\pi T+T^q.
$$

The general formal module of the preceding section explains why the construction is intrinsic, but this polynomial choice lets us prove every assertion about its torsion without invoking a separate preparation theorem for power series.

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

Each $S_n$ is a monic polynomial of degree $q^n$, and

$$
S_n(T)=S_{n-1}(T)\bigl(\pi+S_{n-1}(T)^{q-1}\bigr).
$$

Define the primitive division polynomial directly by

$$
Q_n(T)=\frac{S_n(T)}{S_{n-1}(T)}
=\pi+S_{n-1}(T)^{q-1}.
$$

It is monic of degree

$$
q^{n-1}(q-1)=|(\mathcal O/\pi^n)^\times|.
$$

Since $S_{n-1}(T)\equiv T^{q^{n-1}}\pmod\pi$, reduction gives

$$
Q_n(T)\equiv T^{q^{n-1}(q-1)}\pmod\pi,
$$

while $Q_n(0)=\pi$. Thus every nonleading coefficient lies in $\mathfrak m$ and the constant coefficient has valuation exactly one. Hence $Q_n$ is Eisenstein.

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

Every root of $S_n$ is simple. For $x\in\mathfrak m_{\overline K}$, the term $\pi$ in

$$
f'(x)=\pi+q x^{q-1}
$$

has strictly smaller valuation than the second term; in equal characteristic the second term is zero. The chain rule makes $S_n'(x)$ nonzero at every torsion point. Thus $S_n$ has exactly $q^n$ roots.

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

**Theorem 6.3.** Relative to the fixed uniformizer, Lubin--Tate series, and torsion-coordinate system, the extension $K_n/K$ is finite, totally ramified, and abelian, with an isomorphism

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

The direct torsion parametrization above is an algebraic labeling of the Galois group. It should not be silently identified with the reciprocity labeling: the latter is fixed by the fundamental class and the arithmetic-Frobenius convention. The existence argument below needs the norm subgroup, not an unproved comparison of these two labelings.

### 6.5 The norm group of the torsion extension

Conditional on the norm-filtration input stated below, the crucial calculation is

$$
N_{K_n/K}(K_n^\times)=\pi^{\mathbf Z}U^n.
$$

We give the mechanism rather than infer it from the desired classification. For the existence proof we take $f(T)=\pi T+T^q$ as above. The monic primitive division polynomial $Q_n$ has constant term $\pi$ and degree

$$
d=(q-1)q^{n-1}.
$$

The constant-term formula for the minimal polynomial gives

$$
N_{K_n/K}(\omega_n)=(-1)^d\pi.
$$

The degree $d$ is even unless $q$ is even and $n=1$. In the even-degree cases this gives

$$
N_{K_n/K}(\omega_n)=\pi.
$$

If $q$ is even and $n=1$, then $d=q-1$ is odd, so

$$
N_{K_1/K}(\omega_1)=-\pi,
\qquad
N_{K_1/K}(-\omega_1)=\pi.
$$

This includes the case $q=2$, when $K_1=K$ and $\omega_1=-\pi$. Thus in every case $\pi^{\mathbf Z}$ lies in the norm group. This is stronger than mere surjectivity of norm valuations: it identifies the chosen uniformizer itself as a norm.

The needed unit calculation is the hard norm–ramification comparison. The elementary
expansion of a product of conjugates does not by itself determine its first surviving term on
every unit layer: one must control all elementary symmetric terms, prove exact surjectivity
between breaks, and verify compatibility with Herbrand reindexing. We therefore state the
missing input explicitly.

**Hypothesis NF (Herbrand norm filtration).** Let $M/K$ be a finite abelian extension with
group $G$. At a ramification break retain the group before the drop, using
$G_t=G_{\lceil t\rceil}$ at nonintegral lower indices. For every integer $m\geq0$, put

$$
C_m=N_{M/K}(U_M^0)U_K^m.
$$

Then

$$
[U_K^0:C_m]=[G^0:G^m].
$$

The identities are required simultaneously for all $m$, and the quotient identity

$$
[C_m:C_{m+1}]=[G^m:G^{m+1}]
$$

must be induced by the actual norm maps on the corresponding source unit layers. Every upper
ramification break of $G$ is also required to be an integer. Thus NF includes the exact
source-to-target congruences, cancellation bounds for the lower-order symmetric terms,
surjectivity away from breaks, the exact cokernel at a break, and compatibility of successive
layers. Books 1--4 supply coarse norm-depth bounds and the residue norm and trace
calculations, but not this simultaneous exact statement.

**Why the earlier expansion was insufficient.** For $\sigma\ne1$ put

$$
i(\sigma)=\min_{a\in\mathcal O_M}v_M(\sigma(a)-a).
$$

Then $i(\sigma)=0$ outside inertia, while for $\sigma\in G_0$ one may compute it from any uniformizer:

$$
i(\sigma)=v_M(\sigma(\pi_M)-\pi_M).
$$

Set $G_t=\{\sigma:i(\sigma)\geq t+1\}$ for real $t\geq0$. Define

$$
\varphi(u)=\int_0^u\frac{dt}{[G_0:G_t]},
\qquad
G^s=G_{\psi(s)},
$$

where $\psi=\varphi^{-1}$. These conventions put inertia at index $0$ and make a lower break $b$ occur at the upper index $\varphi(b)$.

The unramified residue part contributes no unit obstruction: norm on finite residue-field units and trace on finite residue-field additive groups are both surjective. We may therefore perform the calculation on inertia and restore the residue-degree factor at the end. Write $l$ for the residue field of $M$. At a positive integral lower break $b$, the map

$$
c_b:G_b/G_{b+1}\hookrightarrow l^+,
\qquad
c_b(\sigma)=
\overline{\frac{\sigma(\pi_M)-\pi_M}{\pi_M^{b+1}}}
$$

is injective. Indeed, vanishing of $c_b(\sigma)$ is exactly the stronger congruence $\sigma(\pi_M)\equiv\pi_M\pmod{\mathfrak m_M^{b+2}}$, which says $\sigma\in G_{b+1}$. The identity

$$
\sigma\tau(\pi_M)-\pi_M
=\sigma(\tau(\pi_M)-\pi_M)+(\sigma(\pi_M)-\pi_M)
$$

shows that $c_b$ is additive, because inertia acts trivially on residues. At $b=0$, the same argument with $\overline{\sigma(\pi_M)/\pi_M}$ gives an injection $G_0/G_1\hookrightarrow l^\times$. Thus the tame quotient is cyclic of order prime to $p$, and every positive quotient is an elementary abelian $p$-group. These elementary ramification facts have now been proved inside the present argument.

There is no need to choose a Frobenius lift or to force these coordinates to descend from $l$
to $k$. Let $E=M^{G_0}$ be the maximal unramified subextension. The intended calculation first
treats the totally ramified extension $M/E$, whose source and target residue fields are both
$l$. The subsequent norm $N_{E/K}$ is surjective on residue units and has surjective trace on
each associated positive unit layer. Subject to the compatibility demanded in NF, it
therefore introduces no new unit index. This two-stage organization also avoids choosing a
splitting of $G\to G/G_0$.

The tempting one-step argument begins by expanding, for $x$ of positive valuation,

$$
N(1+x)=\prod_{\sigma\in G}(1+\sigma x),
$$

and grouping the factors first by $G_{b+1}$ and then by $G_b/G_{b+1}$. If the required
cancellation and depth estimates have already been proved, then away from a break the first
nonzero term is linear with nonzero coefficient and the induced residue-layer map is
bijective. At a positive break the expected leading coefficient is translated through the
finite additive subgroup

$$
C_b=c_b(G_b/G_{b+1})\subseteq l.
$$

After suitable nonzero changes of source and target coordinates, the expected surviving
polynomial is

$$
P_{C_b}(X)=\prod_{c\in C_b}(X+c).
$$

This polynomial is additive on $l$. Indeed, for fixed $y$ the polynomial

$$
P_{C_b}(X+y)-P_{C_b}(X)-P_{C_b}(y)
$$

has degree less than $|C_b|$ in $X$ and vanishes at every $X\in C_b$, because translation by
an element of $C_b$ permutes the factors. It is therefore zero. Its kernel on $l$ is exactly
$C_b$, so, because $l$ is finite, its image has index
$|C_b|=|G_b/G_{b+1}|$. At the tame break the analogous expected map is, up to nonzero
scalars, the $|G_0/G_1|$th-power map on $l^\times$. These polynomial calculations determine
the cokernel *once the norm has been shown to induce these maps*. They do not prove the
missing assertion that all earlier symmetric terms vanish at exactly the necessary depth, nor
that the resulting maps for successive layers are compatible. Those assertions are precisely
the content retained in NF.

Once the exact one-step maps in NF are available, the indexing is as follows. Suppose the
lower group is constant and equal to $H$ on an interval of lower length $d$. Traversing that
interval consumes $d$ source layers. The norm reaches one new target layer after
$[G_0:H]$ source layers, so the number of target layers traversed is

$$
\frac d{[G_0:H]}.
$$

Adding over all constant intervals from $0$ to a lower index $u$ gives exactly $\varphi(u)$. The residue calculation says that ordinary source layers contribute index $1$, while a break contributes the exact factor $|G_b/G_{b+1}|$. Induction through the finitely many lower layers therefore gives, away from integral endpoints,

$$
\left[U_K^0:N(U_M^0)U_K^{\lceil s\rceil}\right]
=\left[G^0:G^s\right]. \tag{6.1}
$$

The passage to this formula is not a proof from the displayed product expansion; it is the
exact compatibility assertion in NF. Given NF, the left side is constant when $s$ varies
inside an interval $(m,m+1)$, so the right side is constant there as well. Taking the left
limit at an integer endpoint, in accordance with our convention that a group is retained at
the break, gives

$$
[C_m:C_{m+1}]=[G^m:G^{m+1}].
$$

Multiplication from $0$ to $m-1$ recovers the index identity in NF. This explains the shape
of the hypothesis, but it does not replace the omitted congruence and compatibility proof.

**Lemma 6.4 (conditional consequence of NF).** Assuming Hypothesis NF, if $G^m=1$, then
$U_K^m\subseteq N_{M/K}(U_M^0)$.

**Proof.** NF gives

$$
[U_K^0:C_m]=[G^0:G^m].
$$

Finite reciprocity gives $[K^\times:N(M^\times)]=|G|$. The valuation of a norm is a multiple
of the residue degree $f=|G/G^0|$, so the valuation coordinate contributes index $f$ and
therefore

$$
[U_K^0:N(U_M^0)]=|G|/f=|G^0|.
$$

If $G^m=1$, the two subgroups $C_m$ and $N(U_M^0)$ have the same index and one contains the
other, so they are equal. $\square$

We apply the lemma by computing the ramification of $K_n/K$. If $a\in U_K^r\setminus U_K^{r+1}$ with $1\leq r<n$, write $a-1=\pi^ru$ with $u$ a unit. Formal subtraction gives

$$
[a]_f(T)-_{F_f}T=[a-1]_f(T)=[u]_f([\pi^r]_f(T)).
$$

Ordinary subtraction and formal subtraction differ by a power-series unit, because $F_f(X,[-1]_f(Y))=(X-Y)$ times a unit. With the compatible choice of torsion points,

$$
[\pi^r]_f(\omega_n)=\omega_{n-r}.
$$

The series $[u]_f(T)$ has unit linear coefficient, so it preserves the positive valuation of its argument. Moreover $K_n/K_{n-r}$ is totally ramified of degree $q^r$, and $\omega_{n-r}$ is a uniformizer of $K_{n-r}$. Therefore

$$
v_{K_n}([a]_f(\omega_n)-\omega_n)=q^r.
$$

If $a\not\equiv1\pmod\pi$, the value is $1$. Thus the positive lower breaks are $q^r-1$ for $1\leq r<n$. Between $q^{r-1}-1$ and $q^r-1$, both the interval length and the index $[G_0:G_t]$ are $q^{r-1}(q-1)$. Each interval therefore contributes exactly $1$ to the Herbrand integral, so

$$
\varphi(q^r-1)=r.
$$

It follows that

$$
G^r=\{\sigma_a:a\in U_K^r/U_K^n\}
\quad(0\leq r\leq n),
$$

and in particular $G^n=1$. Assuming NF, Lemma 6.4 now gives

$$
U^n\subseteq N_{K_n/K}(K_n^\times).
$$

Now apply the already proved norm-index theorem. The subgroup $\pi^{\mathbf Z}U^n$ lies in the norm group and has index

$$
[\mathcal O^\times:U^n]
=(q-1)q^{n-1}
=[K_n:K].
$$

The norm group has the same index, forcing equality. This deduction from NF is not circular:
$K_n$ has already been constructed independently, and the norm-index theorem was proved from
the Brauer invariant. Notice also what has, and has not, been normalized. The equality of norm
groups canonically identifies the kernel of finite reciprocity, while the
arithmetic-Frobenius convention fixes reciprocity on the unramified tower. No formula
identifying $\operatorname{rec}_{K_n/K}(u)$ with one of the auxiliary labels $\sigma_a$ is
needed for existence, so no unsupported sign convention is imported from the torsion
coordinates.

### 6.6 Adding the unramified direction

The assertions in this section that involve the ramified torsion field's norm group are
conditional on NF; the unramified norm calculation itself is unconditional.

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

**Theorem 6.5 [NF] (local existence theorem).** Assuming Hypothesis NF, for every open
finite-index subgroup $H\subseteq K^\times$, there is a unique finite abelian extension $L/K$
inside $K^{\mathrm{ab}}$ such that

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

This subsection is **[NF]**: it uses the cofinal precision family constructed in Chapter 6.

The kernel of the infinite map is the intersection of all finite abelian norm groups. The cofinal family from Chapter 6 gives

$$
\ker(\operatorname{rec}_K)
\subseteq
\bigcap_{m,n\geq1}\pi^{m\mathbf Z}U^n.
$$

An element in this intersection has valuation divisible by every $m$, hence valuation zero, and lies in every $U^n$, hence equals $1$. Therefore $\operatorname{rec}_K$ is injective.

So the exact infinite statement is:

**Theorem 7.2 [NF] (local reciprocity).** Assuming Hypothesis NF, the map

$$
\operatorname{rec}_K:K^\times\hookrightarrow G_K^{\mathrm{ab}}
$$

is a continuous injective homomorphism with dense image. For every finite abelian $L/K$ it induces an isomorphism

$$
K^\times/N_{L/K}(L^\times)
\xrightarrow{\sim}\operatorname{Gal}(L/K).
$$

### 7.5 Profinite completion

This subsection is **[NF]**, because identifying all open finite-index subgroups with norm
groups uses Theorem 6.5.

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

In the following package finite reciprocity and norm limitation are unconditional results of
Chapters 4--5; the existence assertion and the resulting bijection are **[NF]**.

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

For the particular Lubin–Tate tower attached to $\pi$, the complementary **[NF]** calculation
is

$$
\operatorname{rec}_K(\pi)|_{K_n}=1,
\qquad
\operatorname{rec}_K(u)(\omega_n)=[u^{-1}]_f(\omega_n).
$$

The first equality follows because $\pi$ is a norm from every $K_n$; the second is proved in Proposition 10.1 by comparing the fundamental-class and torsion labelings. Thus, after choosing $\pi$ and the compatible division points, the two coordinates of the Artin map are completely explicit:

$$
\pi^ru
\longmapsto
\left(\operatorname{Frob}_{\mathrm{arith}}^r,
\;\omega_n\mapsto[u^{-1}]_f(\omega_n)\right).
$$

This product description depends on the chosen uniformizer, but the resulting automorphism of each finite abelian extension does not.

### 8.2 Units are the abelian inertia group

Let $I_K\subset G_K$ be the inertia subgroup, the kernel of the action on the separable closure of $k$. Its image in $G_K^{\mathrm{ab}}$ will be denoted $I_K^{\mathrm{ab,im}}$; this is more precise than the abstract abelianization $I_K^{\mathrm{ab}}$, because abelianization does not preserve every subgroup injection.

The preceding unramified formula gives

$$
\operatorname{rec}_K(\mathcal O^\times)
\subseteq I_K^{\mathrm{ab,im}}.
$$

Assuming NF, the reverse inclusion follows after profinite completion: the valuation quotient
accounts for all of $\widehat{\mathbf Z}$, so the kernel is the already complete group
$\mathcal O^\times$. Therefore reciprocity restricts to a topological isomorphism

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

For a finite Galois extension $L/K$ with group $G$, define the lower function

$$
i_G(\sigma)=\min_{a\in\mathcal O_L}v_L(\sigma(a)-a)
$$

for $\sigma\ne1$. It is $0$ outside inertia. If $\sigma$ lies in inertia and $\pi_L$ is any uniformizer, then

$$
i_G(\sigma)=v_L(\sigma(\pi_L)-\pi_L),
$$

so the familiar uniformizer formula remains valid exactly where it is meant to be used. The lower groups are

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

Then $G^{-1}=G$, $G^0=I$, and $G^{0+}$ is wild inertia. We also need the quotient property, so we include its numerical proof. Let $H\triangleleft G$, put $E=L^H$, and write a bar for passage to $G/H$. For $\bar\sigma\ne1$, conjugate differences satisfy

$$
i_{E/K}(\bar\sigma)
=\frac1{e(L/E)}\sum_{\tau\mapsto\bar\sigma}i_{L/K}(\tau). \tag{8.1}
$$

To verify (8.1), choose an integral generator for $E/K$, lift it through an integral generator of $L/E$, and factor the norm of its conjugate difference over the $H$-orbit. Taking valuations gives the displayed sum; restriction of normalized valuations supplies the factor $e(L/E)$. The minimum over integral generators is unchanged, so the formula is intrinsic. Sum (8.1) over the cosets surviving at a fixed lower depth. On each interval where the lower groups are constant, the numerator counts the elements of $G_tH/H$ and the denominator is $[G_0:G_t]$. Integrating these constant slopes and then applying the inverse Herbrand functions gives

$$
(G/H)^v=G^vH/H \tag{8.2}
$$

for every real $v\geq-1$. Thus upper numbering, unlike lower numbering, passes unchanged to quotient extensions. We need precisely (8.2) below to state the exact compatibility with units.

### 8.4 The unit and ramification theorem

**Theorem 8.1 [NF].** Assuming Hypothesis NF, let $L/K$ be finite abelian with group $G$.
Under arithmetic local reciprocity,

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

**Proof.** The case $n=0$ is Section 8.2. For $n\geq1$, Hypothesis NF applied directly to
$L/K$ gives

$$
[U_K^0:N_{L/K}(U_L^0)U_K^n]
=[G^0:G^n]. \tag{8.3}
$$

It remains to identify the subgroup, not only its order. Put $E=L^{G^n}$. Quotient compatibility of upper numbering gives

$$
\operatorname{Gal}(E/K)^n=1.
$$

Lemma 6.4 applied to $E/K$ therefore gives

$$
U_K^n\subseteq N_{E/K}(E^\times).
$$

Finite reciprocity for $E/K$ therefore shows that every element of $\operatorname{rec}_{L/K}(U_K^n)$ restricts trivially to $E$, so

$$
\operatorname{rec}_{L/K}(U_K^n)\subseteq G^n.
$$

On the other hand, (8.3) says

$$
[G^0:\operatorname{rec}_{L/K}(U_K^n)]
=[G^0:G^n].
$$

The inclusion and equality of indices force equality. Taking inverse images under the quotient map $K^\times\to K^\times/N(L^\times)$ gives the equivalent formula. $\square$

The use of upper numbering is forced by functoriality, not by taste. If lower groups were placed on the right, the formula would fail after passing to a quotient extension.

### 8.5 Conductors

The multiplicative definition below is unconditional. Its identification with upper
ramification depth, and all consequences stated through that identification, are **[NF]**.

Let $L/K$ be finite abelian. Its conductor exponent is the least $n\geq0$ such that

$$
U_K^n\subseteq N_{L/K}(L^\times).
$$

By Theorem 8.1, this is equivalently the least $n$ with $G^n=1$. The extension is unramified exactly when the conductor exponent is $0$, even when the extension itself is nontrivial. An abelian extension with nontrivial tame inertia has conductor exponent $1$: $G^0$ is nontrivial, but $G^1=1$. Wild extensions have conductor at least $2$.

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

Let $L/K$ be finite separable and choose a separable closure containing $L$. Then the same field is a separable closure of $L$, and

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

Let $E/K$ be finite abelian and let $L/K$ be finite separable. The compositum $EL/L$ is abelian. Norm–inclusion compatibility shows that the reciprocity character cutting out $EL/L$ is obtained from the one cutting out $E/K$ by restriction to $G_L$; on multiplicative groups this is precomposition with $N_{L/K}:L^\times\to K^\times$.

At the level of norm groups,

$$
N_{EL/L}((EL)^\times)
=\ker\!\left(
L^\times\xrightarrow{\operatorname{rec}_L}G_L^{\mathrm{ab}}
\longrightarrow\operatorname{Gal}(EL/L)
\right).
$$

Equivalently, it is the inverse image under reciprocity of the image of $G_{EL}$ in $G_L^{\mathrm{ab}}$; the abstract group $G_{EL}^{\mathrm{ab}}$ is not canonically a subgroup of $G_L^{\mathrm{ab}}$. In multiplicative terms the same kernel is

$$
\{x\in L^\times:N_{L/K}(x)\in N_{E/K}(E^\times)\}.
$$

This exact inverse-image formula follows from Theorem 9.1. It also explains why arbitrary base change may absorb ramification or split the extension: one must apply the old norm condition after the field norm $N_{L/K}$, not after the inclusion $K^\times\hookrightarrow L^\times$.

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

This subsection is **[NF]**, since its first displayed norm quotient is the conditional norm
calculation of Section 6.5.

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

The auxiliary torsion labeling can now be compared with the Artin labeling. This is where the inverse forced by the arithmetic-Frobenius convention appears. Kernels and associated graded groups do not suffice for this comparison: a filtered automorphism can be the identity on every associated graded quotient without being the identity. We instead compare the two maps on actual Galois elements.

**Proposition 10.1 [NF] (finite-level Artin–torsion comparison).** Assuming Hypothesis NF,
fix arithmetic reciprocity, so that a uniformizer acts on the maximal unramified extension by
$x\mapsto x^q$ on residues. For $u\in\mathcal O^\times$ and a primitive level-$n$ point
$\omega_n$,

$$
\operatorname{rec}_{K_n/K}(u)(\omega_n)
=[u^{-1}]_f(\omega_n),
$$

where $u^{-1}$ is reduced modulo $\pi^n$. Moreover

$$
\operatorname{rec}_{K_n/K}(\pi)=1.
$$

**Proof.** The second formula follows from the direct norm calculation $\pi\in N_{K_n/K}(K_n^\times)$. For the first, let

$$
\theta_n:(\mathcal O/\pi^n)^\times
\xrightarrow{\sim}\operatorname{Gal}(K_n/K),
\qquad
\theta_n(a)(\omega_n)=[a]_f(\omega_n).
$$

Finite reciprocity and the equality of norm groups give another isomorphism from $\mathcal O^\times/U^n$ to the same Galois group. It remains to compare these two isomorphisms, not merely their kernels.

We make the comparison simultaneously at all levels. Put

$$
K_\pi^{\mathrm{LT}}=\bigcup_{r\geq1}K_r
$$

inside the fixed separable closure; when more than one uniformizer is in play, write $K_{\pi,r}=K_r$ and use $K_{\varpi,r}$ for the analogous level attached to $\varpi$. Let $K^{\mathrm{nr}}$ be the maximal unramified extension. The finite composita

$$
K_m^{\mathrm{ur}}K_r
$$

are cofinal among the finite abelian extensions of $K$. Indeed, if $L/K$ is finite abelian, its norm group is open, so it contains $\pi^{m\mathbf Z}U^r$ for some $m,r$. The field $E=K_m^{\mathrm{ur}}K_r$ has norm group $\pi^{m\mathbf Z}U^r$ by Section 6.6. Thus $N(E^\times)\subseteq N(L^\times)$, and the inclusion-reversing correspondence of Theorem 6.5, equivalently the quotient diagram of Section 9.4, gives $L\subseteq E$. Consequently

$$
K^{\mathrm{ab}}=K^{\mathrm{nr}}K_\pi^{\mathrm{LT}}. \tag{10.1}
$$

The intersection of the two fields on the right is $K$, because every finite subextension of the first is unramified and every finite subextension of the second is totally ramified.

For $x=u\pi^s$, with $u\in\mathcal O^\times$ and $s\in\mathbf Z$, define $\rho_\pi(x)$ on the two factors in (10.1) by

$$
\rho_\pi(x)|_{K^{\mathrm{nr}}}=\Phi^s,
\qquad
\rho_\pi(x)(\lambda)=[u^{-1}]_f(\lambda)
\quad(\lambda\in F_f[\pi^r],\ r\geq1), \tag{10.2}
$$

where $\Phi$ is **arithmetic** Frobenius, inducing $z\mapsto z^q$ on the residue field. The trivial intersection makes these two actions glue uniquely. The restriction maps in the torsion tower are reduction modulo $\pi^r$, so (10.2) is compatible in $r$ and defines a homomorphism

$$
\rho_\pi:K^\times\longrightarrow\operatorname{Gal}(K^{\mathrm{ab}}/K).
$$

It is continuous: on $K_m^{\mathrm{ur}}K_r$ its kernel is $\pi^{m\mathbf Z}U^r$. Notice that (10.2) is a construction from torsion, not an invocation of the Artin map.

We next prove the change-of-uniformizer statement that fixes its sign. Let $\varpi=v\pi$ be another uniformizer, with $v\in\mathcal O^\times$, and let $g$ be a Lubin–Tate series for $\varpi$. Write $\widehat{K^{\mathrm{nr}}}$ for the completion of $K^{\mathrm{nr}}$, $B$ for its valuation ring, and again $\Phi$ for the continuous extension of arithmetic Frobenius to $B$.

We first record the two elementary difference equations

$$
\Phi-1:B\longrightarrow B,
\qquad
b\longmapsto\frac{\Phi(b)}b:B^\times\longrightarrow B^\times. \tag{10.3}
$$

Both maps are surjective, with kernels $\mathcal O$ and $\mathcal O^\times$, respectively. Here is the proof. Modulo $\pi$, the first map is $z\mapsto z^q-z$ on the algebraic closure $\bar k$, hence is surjective. Lifting one power of $\pi$ at a time reduces every subsequent correction to the same equation on $\bar k$; completeness gives a solution in $B$. For the multiplicative map, modulo $\pi$ it is $z\mapsto z^{q-1}$ on $\bar k^\times$, which is surjective. Once a solution is correct modulo $\pi^j$, multiplying it by $1+\pi^jt$ changes its Frobenius quotient, modulo $\pi^{j+1}$, by

$$
1+\pi^j(\Phi(t)-t).
$$

The additive result therefore lifts the solution through all $j$. The same induction identifies the fixed elements modulo every $\pi^j$ with $\mathcal O/\pi^j$, giving the asserted kernels.

Choose $\varepsilon\in B^\times$ with

$$
\Phi(\varepsilon)=v\varepsilon.
$$

There is a power series $\theta_0(T)=\varepsilon T+\cdots\in B[[T]]$ satisfying

$$
\Phi(\theta_0)=\theta_0\circ[v]_f. \tag{10.4}
$$

This follows by an explicit coefficient recursion. If the equation has been achieved below degree $j$, add $bT^j$ and write $b=a\varepsilon^j$. The change in the degree-$j$ error is a nonzero unit multiple of $\Phi(a)-a$, so the first surjectivity statement in (10.3) supplies $a$. Thus every coefficient can be chosen; no reciprocity assertion enters the recursion.

Let

$$
h=(\Phi\theta_0)\circ f\circ\theta_0^{-1}.
$$

Equation (10.4), the commutation of $f$ with $[v]_f$, and

$$
(\Phi\theta_0)^{-1}=[v^{-1}]_f\circ\theta_0^{-1}
$$

give $\Phi(h)=h$. Explicitly,

$$
\Phi(h)
=\Phi^2(\theta_0)\circ f\circ(\Phi\theta_0)^{-1}
=(\Phi\theta_0)\circ[v]_f\circ f\circ[v^{-1}]_f\circ\theta_0^{-1}
=h.
$$

Hence $h\in\mathcal O[[T]]$ by (10.3). Its linear coefficient is

$$
\frac{\Phi(\varepsilon)\pi}{\varepsilon}=v\pi=\varpi,
$$

and $h(T)\equiv T^q\pmod\pi$. For the last assertion, reduce the definition of $h$ modulo $\pi$ and use

$$
r(T)^q=(\Phi r)(T^q)
$$

for a series $r$ over $\bar k$. More explicitly,

$$
\bar h
=\overline{\Phi\theta_0}\circ T^q\circ\bar\theta_0^{-1}
=\overline{\Phi\theta_0}\circ
  \overline{\Phi(\theta_0^{-1})}\circ T^q
=T^q.
$$

Thus $h$ is a Lubin–Tate series for $\varpi$.

Lemma 6.2, applied to the two series $h$ and $g$ for the same uniformizer, gives an invertible $j(T)\in\mathcal O[[T]]$ with linear coefficient $1$ and

$$
j\circ h=g\circ j.
$$

Set $\Theta=j\circ\theta_0$. Then

$$
\Phi(\Theta)=\Theta\circ[v]_f,
\qquad
g\circ\Theta=(\Phi\Theta)\circ f. \tag{10.5}
$$

The first identity follows because $j$ has coefficients in $\mathcal O$, and the second follows from

$$
g\circ j\circ\theta_0
=j\circ h\circ\theta_0
=j\circ(\Phi\theta_0)\circ f
=\Phi(j\circ\theta_0)\circ f.
$$

Moreover $\Theta$ is an $\mathcal O$-linear isomorphism from $F_f$ to $F_g$. To verify this rather than assume it, transport $F_f$ through $\Theta$:

$$
H(X,Y)=\Theta\bigl(F_f(\Theta^{-1}(X),\Theta^{-1}(Y))\bigr).
$$

The first equation in (10.5) and the fact that $[v]_f$ is an automorphism give

$$
\begin{aligned}
\Phi(H)(X,Y)
&=(\Phi\Theta)\bigl(
 F_f((\Phi\Theta)^{-1}(X),(\Phi\Theta)^{-1}(Y))
 \bigr)\\
&=\Theta\circ[v]_f\bigl(
 F_f([v^{-1}]_f\Theta^{-1}(X),[v^{-1}]_f\Theta^{-1}(Y))
 \bigr)\\
&=H(X,Y).
\end{aligned}
$$

Thus $H$ is defined over $\mathcal O$. Since

$$
g\circ\Theta=(\Phi\Theta)\circ f
=\Theta\circ[v]_f\circ f
=\Theta\circ[\varpi]_f,
$$

$g$ is its $\varpi$-endomorphism. The uniqueness in Theorem 6.1 therefore identifies the transported group with $F_g$. Similarly,

$$
J_a=\Theta\circ[a]_f\circ\Theta^{-1}
$$

is fixed by $\Phi$, because

$$
\Phi(J_a)
=\Theta\circ[v]_f\circ[a]_f\circ[v^{-1}]_f\circ\Theta^{-1}
=J_a.
$$

It has linear coefficient $a$ and commutes with $g$; uniqueness identifies it with $[a]_g$. Thus

$$
\Theta\circ[a]_f=[a]_g\circ\Theta
\qquad(a\in\mathcal O). \tag{10.6}
$$

Iterating the second identity in (10.5) gives

$$
g^{\circ r}\circ\Theta
=\Phi^r(\Theta)\circ f^{\circ r}. \tag{10.7}
$$

It follows that $\Theta$ bijects the level-$r$ $f$-torsion with the level-$r$ $g$-torsion and, by (10.6), preserves the full $\mathcal O/\pi^r$-module action; here $(\pi^r)=(\varpi^r)$. These convergent evaluations take place in the completion of the fixed separable closure. Applying $\Theta^{-1}$ gives the reverse inclusion, so first we obtain

$$
\widehat{K^{\mathrm{nr}}}K_{\pi,r}
=\widehat{K^{\mathrm{nr}}}K_{\varpi,r}.
$$

This equality descends to

$$
K^{\mathrm{nr}}K_{\pi,r}=K^{\mathrm{nr}}K_{\varpi,r}. \tag{10.8}
$$

Indeed, an algebraic subfield $E$ of $K^s$ is closed in $K^s$, since every element of $\operatorname{Gal}(K^s/E)$ fixes its topological closure and the fixed field is $E$. The algebraic compositum is dense in its completed compositum, so intersecting the latter with $K^s$ recovers the former.

We can now compare the maps $\rho_\pi$ and $\rho_\varpi$. Both $\rho_\pi(\varpi)$ and $\rho_\varpi(\varpi)$ restrict to $\Phi$ on $K^{\mathrm{nr}}$, while $\rho_\varpi(\varpi)$ is the identity on $K_\varpi^{\mathrm{LT}}$. If $\lambda$ is $f$-torsion, $\rho_\pi(\pi)$ applies $\Phi$ to the coefficients of $\Theta$ and fixes $\lambda$, whereas $\rho_\pi(v)$ fixes those coefficients and sends $\lambda$ to $[v^{-1}]_f(\lambda)$. Thus equations (10.2) and (10.5) give

$$
\begin{aligned}
\rho_\pi(\varpi)(\Theta(\lambda))
&=(\Phi\Theta)([v^{-1}]_f(\lambda))\\
&=\Theta([v]_f([v^{-1}]_f(\lambda)))\\
&=\Theta(\lambda).
\end{aligned} \tag{10.9}
$$

This cancellation is where the inverse in (10.2) is forced by arithmetic Frobenius: the descent relation contributes $[v]_f$, so uniformizer-independence requires the unit action $[v^{-1}]_f$.

Thus the two automorphisms agree on both factors of (10.1), with $\varpi$ in place of $\pi$, and

$$
\rho_\pi(\varpi)=\rho_\varpi(\varpi). \tag{10.10}
$$

Applying (10.10) to $(\pi',\varpi)$ and $(\pi,\varpi)$ for an arbitrary third uniformizer $\pi'$ shows that $\rho_{\pi'}$ and $\rho_\pi$ agree on every uniformizer. Uniformizers generate $K^\times$, since $u=(u\pi)\pi^{-1}$ for every unit $u$; hence $\rho_\pi$ is independent of the chosen uniformizer.

There are no hidden coordinate choices in this conclusion. Replacing a compatible primitive point by $\omega_r'=[c_r]_f(\omega_r)$ does not change (10.2), because all $[a]_f$ commute. Replacing $f$ by another Lubin–Tate series for the same $\pi$ uses the integral intertwiner of Section 6.2; it and its inverse identify the torsion fields and commute with every $[a]$. Different choices of $\varepsilon$, $\theta_0$, or $j$ in the descent argument still give (10.9), which is the only property used. The restriction maps in the tower remain reduction modulo $\pi^r$.

It remains to identify the intrinsic map $\rho_\pi$ with the Artin map already constructed from fundamental classes. We use the following exact uniqueness criterion: a homomorphism $\eta:K^\times\to\operatorname{Gal}(K^{\mathrm{ab}}/K)$ equals $\operatorname{rec}_K$ if, for every uniformizer $\varpi$,

$$
\eta(\varpi)|_{K^{\mathrm{nr}}}=\Phi
\quad\text{and}\quad
\eta(\varpi)|_{K_\varpi^{\mathrm{LT}}}=1. \tag{10.11}
$$

Indeed, (10.1), applied to $\varpi$, determines $\eta(\varpi)$ on all of $K^{\mathrm{ab}}$, and uniformizers generate $K^\times$. The Artin map has the two stated properties: for every uniformizer $\varpi$,

$$
\operatorname{rec}_K(\varpi)|_{K^{\mathrm{nr}}}=\Phi
$$

by the arithmetic-Frobenius normalization of Theorem 5.4. Also $\varpi$ belongs to

$$
N_{K_{\varpi,r}/K}(K_{\varpi,r}^\times)
=\varpi^{\mathbf Z}U^r,
$$

so finite reciprocity says that $\operatorname{rec}_K(\varpi)$ fixes every $K_{\varpi,r}$. Therefore $\operatorname{rec}_K(\varpi)$ and $\rho_\varpi(\varpi)$ agree on

$$
K^{\mathrm{ab}}=K^{\mathrm{nr}}K_\varpi^{\mathrm{LT}}.
$$

By (10.10), $\rho_\pi(\varpi)=\rho_\varpi(\varpi)$ for every $\varpi$. Uniformizers generate $K^\times$, so

$$
\operatorname{rec}_K=\rho_\pi. \tag{10.12}
$$

This uses exactly the earlier uniqueness data—the fundamental-class Artin map has the proved norm kernels and sends a uniformizer to arithmetic Frobenius on unramified quotients. It does not assume the desired torsion formula, and it never infers equality from agreement on graded quotients. Restricting (10.12) to $K_n$ gives

$$
\operatorname{rec}_{K_n/K}(u)(\omega_n)
=[u^{-1}]_f(\omega_n),
$$

as claimed. $\square$

Equivalently, in arithmetic normalization and for $x=\pi^su$,

$$
\operatorname{rec}_K(x)|_{K^{\mathrm{nr}}}=\Phi^s,
\qquad
\operatorname{rec}_K(x)(\omega_n)=[u^{-1}]_f(\omega_n).
$$

Thus units fix the unramified tower and $\pi$ fixes the Lubin–Tate tower. The inverse in the torsion formula is not a second normalization choice. If reciprocity were normalized by geometric Frobenius $\Phi^{-1}$, the entire Artin map would be inverted and the formula would become $\omega_n\mapsto[u]_f(\omega_n)$. This finite-level calculation is a reliable way to translate between the two conventions.

For later use, specialize this calculation to $K=\mathbf Q_p$ and the multiplicative formal
group, for which

$$
[a](T)=(1+T)^a-1.
$$

If $\zeta_{p^n}$ is a primitive $p^n$th root of unity, then
$\omega_n=\zeta_{p^n}-1$ is a primitive level-$n$ point. Hence, for
$u\in\mathbf Z_p^\times$,

$$
\boxed{\quad
\operatorname{rec}_{\mathbf Q_p}(u)(\zeta_{p^n})
=\zeta_{p^n}^{\,u^{-1}},
\quad}
$$

where $u^{-1}$ in the exponent means its reduction in
$(\mathbf Z/p^n\mathbf Z)^\times$. Indeed, Proposition 10.1 gives

$$
\operatorname{rec}_{\mathbf Q_p}(u)(\zeta_{p^n}-1)
=[u^{-1}](\zeta_{p^n}-1)
=\zeta_{p^n}^{\,u^{-1}}-1,
$$

and a field automorphism fixes $1$. Thus the inverse in the cyclotomic action is deduced
from the arithmetic-Frobenius normalization rather than imposed as a separate convention.

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

This construction is **[NF]**, because it uses the conditional equality
$N(E_{m',n}^\times)=\pi^{m'\mathbf Z}U^n$.

Suppose a subgroup is presented as

$$
H=\langle\pi^m a\rangle\,V,
$$

where $V\subseteq\mathcal O^\times$ is open and $a\in\mathcal O^\times$. Choose $n$ with $U^n\subseteq V$, and choose a positive multiple $m'=rm$ for which $a^r\in V$. Then

$$
\pi^{m'\mathbf Z}U^n\subseteq H.
$$

The quotient $K^\times/H$ is computed from the finite group

$$
(\mathbf Z/m'\mathbf Z)\times(\mathcal O/\pi^n)^\times
$$

after quotienting by the image of the whole subgroup $H/(\pi^{m'\mathbf Z}U^n)$. Equivalently,
one imposes both the relation determined by $\pi^m a$ and all relations contributed by
$V/U^n$. The field corresponding to $H$ is the fixed field of the resulting subgroup in $E_{m',n}$.

This procedure is usable: finite congruence arithmetic determines the subgroup, the unramified and torsion fields provide an explicit ambient abelian extension, and ordinary finite Galois theory extracts the desired field. The construction also shows that every finite abelian extension has finite conductor.

## 11. Continuous one-dimensional characters

The extension of multiplicative characters across
$\widehat{K^\times}\cong G_K^{\mathrm{ab}}$, the realization of finite kernels by fields, and
the comparison with higher ramification are all **[NF]**. Purely topological decompositions of
characters already defined on $K^\times$ are unconditional.

### 11.1 The exact topological statement

A one-dimensional Galois character factors through $G_K^{\mathrm{ab}}$. Since this group is the profinite completion of $K^\times$, the cleanest coefficient hypothesis is that the target be profinite.

**Theorem 11.1 [NF].** Assuming Hypothesis NF, let $A$ be a profinite abelian group.
Composition with reciprocity gives a natural bijection

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

For a general Hausdorff abelian target $A$, not every continuous character of $K^\times$
comes from Galois. Let $C=\overline{\chi(K^\times)}\subseteq A$. The exact condition is
that $\chi$ extend continuously to the profinite completion. Equivalently, the following two
requirements hold:

1. $C$ is complete for its topological-group uniformity;
2. for every identity neighborhood $V$ in $C$, the inverse image $\chi^{-1}(V)$ contains
   an open finite-index subgroup of $K^\times$.

The second condition says precisely that $\chi$ is continuous for the profinite topology on
$K^\times$; it also makes $C$ totally bounded. Together with completeness, it makes $C$
compact, so the uniformly continuous map from the dense subgroup $K^\times$ extends uniquely
to $\widehat{K^\times}$. Conversely, an extension has compact image, equal to $C$, and
continuity on the profinite group gives the finite-index neighborhood condition. Thus one may
equivalently require that $C$ be compact and that condition 2 hold. It is enough, but stronger,
to assume that $A$ itself is complete and impose condition 2; Hausdorffness alone does not
supply the missing limits.

A character $K^\times\to\mathbf C^\times$ sending $\pi$ to $2$ is continuous because
$\pi^{\mathbf Z}$ is discrete, but it cannot come from $G_K$: its image is not relatively
compact. This counterexample is why both the coefficient topology and the convergence
condition must be stated.

After choosing $\pi$, every continuous character into a profinite abelian group is described by a pair

$$
(\alpha,\eta),
\qquad
\alpha\in A,
\qquad
\eta:\mathcal O^\times\to A\text{ continuous},
$$

through

$$
\chi(\pi^ru)=\alpha^r\eta(u).
$$

There is no compatibility condition because $K^\times=\pi^{\mathbf Z}\times\mathcal O^\times$. The pair depends on $\pi$: replacing it by $a\pi$ replaces $\alpha$ by $\alpha\eta(a)$. The character itself is intrinsic. It has finite image precisely when $\alpha$ has finite order and $\eta$ has finite image.

### 11.2 Finite-order characters and cyclic extensions

Assuming NF, let $A$ be a finite cyclic group and let

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

For a profinite target, the closure $\overline{\langle\alpha\rangle}$ is a compact procyclic
subgroup, and the formula extends from $\mathbf Z$ to $\widehat{\mathbf Z}$. For $A=\mathcal O_E^\times$, this includes infinite-order $\ell$-adic unramified characters. For $A=\mathbf C^\times$ and a genuine continuous character of the profinite Galois group, $\alpha$ must have finite order; arbitrary complex Satake-type parameters belong to a Weil-group formulation, not to continuous characters of $G_K$ itself.

### 11.4 Ramified characters and conductor

Let $A$ be finite or profinite and $\chi:K^\times\to A$ continuous. Its restriction to units determines ramification. Define

$$
a(\chi)=\min\{n\geq0:\chi(U^n)=1\}
$$

when such an $n$ exists. For finite-image characters it always exists. Assuming NF, the
reciprocity filtration theorem gives

$$
a(\chi)=\min\{n:\chi_{\mathrm{Gal}}(G_K^n)=1\}.
$$

Thus:

- $a(\chi)=0$ exactly when $\chi$ is unramified;
- $a(\chi)=1$ exactly when $\chi|_{\mathcal O^\times}$ is nontrivial but
  $\chi|_{U^1}$ is trivial, that is, when its inertia character is nontrivial and tame;
- $a(\chi)\geq2$ signals wild ramification.

In particular, “nontrivial” in the middle line refers to the restriction to inertia. A
globally nontrivial unramified character can have $\chi(\pi)\ne1$ and still has conductor
exponent $0$.

For a continuous $\ell$-adic character with infinite image on $U^1$, there may be no finite $n$ on which it becomes trivial. One then speaks of finite conductor only under the additional hypothesis that inertia has finite image, or uses a more general analytic notion. Finite-order characters, which cut out finite abelian extensions, always have the integral conductor above.

### 11.5 Characters in towers

Let $L/K$ be finite separable, fix an embedding $L\hookrightarrow K^s$, and use $K^s$ as a
separable closure of $L$; this identifies $G_L=\operatorname{Gal}(K^s/L)$ with a subgroup of
$G_K$. If $\chi:G_K\to A$ corresponds to $\chi_K:K^\times\to A$, then restriction to $G_L$ corresponds to precomposition with the norm:

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

### 11.6 Coefficient fields and standard characters

The preceding classification becomes especially concrete when the target is the multiplicative group of a local coefficient field $E$. A continuous character

$$
\rho:G_K\longrightarrow E^\times
$$

has compact image because $G_K$ is compact. The valuation map $E^\times\to\mathbf Z$ sends that image to a finite subgroup of $\mathbf Z$, hence to zero. Therefore

$$
\rho(G_K)\subseteq\mathcal O_E^\times.
$$

Assuming NF, every continuous character $K^\times\to\mathcal O_E^\times$ extends uniquely
across the profinite completion. Thus

$$
\operatorname{Hom}_{\mathrm{cont}}(G_K,E^\times)
\cong
\operatorname{Hom}_{\mathrm{cont}}(K^\times,\mathcal O_E^\times).
$$

This is the usual classification of continuous one-dimensional $E$-valued Galois representations. It includes infinite-image characters when $E$ is nonarchimedean. By contrast, a continuous character $G_K\to\mathbf C^\times$ has finite image: its compact image lies in the circle, and a closed totally disconnected subgroup of the circle is finite. Hence the complex-valued Galois characters are exactly the finite-order multiplicative characters of $K^\times$. Continuous complex quasicharacters with a factor such as $|x|^s$ belong to the multiplicative or Weil-group theory, not to continuous characters of the profinite group $G_K$.

Two standard calculations test all normalizations. First suppose $\ell\ne p$ and let $\chi_\ell$ be the $\ell$-adic cyclotomic character. The extensions generated by $\ell$-power roots of unity are unramified over $K$, and arithmetic Frobenius raises those roots to the $q$th power. Consequently

$$
\chi_\ell(\operatorname{rec}_K(\pi^ru))=q^r.
$$

Second take $K=\mathbf Q_p$ and the $p$-adic cyclotomic character. Its extension is totally ramified, and $p$ acts trivially on the Lubin–Tate cyclotomic tower. For every primitive $p^n$th root $\zeta_{p^n}$, the finite-level calculation following Proposition 10.1 says

$$
\operatorname{rec}_{\mathbf Q_p}(u)(\zeta_{p^n})
=\zeta_{p^n}^{\,u^{-1}}
\qquad(u\in\mathbf Z_p^\times).
$$

By the definition of the cyclotomic character, passage through all $n$ therefore gives

$$
\chi_p(\operatorname{rec}_{\mathbf Q_p}(p^ru))=u^{-1}
\qquad(u\in\mathbf Z_p^\times).
$$

For a finite extension $K/\mathbf Q_p$, norm–inclusion compatibility gives the corresponding formula

$$
\chi_p(\operatorname{rec}_K(x))
=\left\langle N_{K/\mathbf Q_p}(x)\right\rangle^{-1},
$$

where $\langle y\rangle$ denotes the unit part of $y\in\mathbf Q_p^\times$. The unramified and $p$-adic formulas look different because prime-to-$p$ roots of unity lift from the residue field, whereas $p$-power roots of unity live in the deeply ramified unit tower.

Finally, a finite-order character $\chi$ cuts out the fixed field of the kernel of its Galois counterpart. Its degree is $|\operatorname{im}\chi|$, its norm group is $\ker\chi$, its residue degree is the order of the image of $\pi$ modulo the image of units, and its ramification groups are read from the successive images $\chi(U^n)$. Thus the pair $(\alpha,\eta)$ is not merely a parametrization: it recovers the unramified degree, inertia, conductor, and wild depth of the corresponding cyclic extension.

## 12. The local reciprocity dictionary

This chapter separates the unconditional finite reciprocity dictionary from its conditional
extensions. Statements that every open subgroup is realized, that higher units match upper
ramification, or that $G_K^{\mathrm{ab}}$ is the profinite completion of $K^\times$ are
**[NF]**. The finite norm-kernel and functoriality statements do not depend on NF.

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

Assuming NF, every open finite-index subgroup is exactly one $H_L$. The order-reversing rules
for fields already in a common finite abelian extension are unconditional:

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
&\text{$n$th upper ramification subgroup [NF]}.
\end{array}
$$

At finite level, a uniformizer maps to an element whose image in the unramified quotient is
arithmetic Frobenius. It need not select a canonical lift through inertia. Units map exactly
to inertia; assuming NF, $U^n$ maps exactly to $G^n$.

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

For every finite separable $L/K$, using the compatible separable closures fixed in Section 11.5, let $i_*$ be induced by $G_L\subset G_K$ and let $\operatorname{Ver}$ be the transfer. Then

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

Assuming NF, for a profinite abelian coefficient group $A$,

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

For a nonprofinite Hausdorff target, retain only the characters that extend continuously to
$\widehat{K^\times}$. Equivalently, their image closure is complete and their inverse images
of identity neighborhoods contain open finite-index subgroups; equivalently, the image closure
is compact and the character is continuous for the profinite topology. Relative compactness
alone is necessary but does not replace the finite-index neighborhood condition.

### 12.6 Conclusion

Local class field theory begins with a striking mismatch. On one side lies the concrete topological group $K^\times$, decomposed by valuation, residue units, and infinitesimal units. On the other lies the apparently remote collection of all finite abelian extensions of $K$. Reciprocity proves that the mismatch is an illusion: every finite abelian Galois quotient is already encoded by a norm quotient of $K^\times$.

The unconditional part of the proof reveals why finite reciprocity is rigid. Hilbert 90 removes
the first cohomological obstruction. The local Brauer invariant turns every remaining norm
obstruction into a rational number modulo one, and its fundamental classes identify finite
Galois abelianizations with norm quotients. Assuming NF, the unramified and formal-module
towers are cofinal and realize every open finite-index subgroup. Topology then assembles the
finite maps into a dense embedding

$$
K^\times\hookrightarrow G_K^{\mathrm{ab}}
$$

and an isomorphism after profinite completion.

The final picture is exact at finite level for norms, kernels, Frobenius, inertia, and
functoriality. Conditional on NF it is exact at every depth: deeper units are higher
ramification, open subgroups are fields, and one-dimensional Galois characters may be read as
multiplicative characters of $K^\times$ with conductor visible in local coordinates. Closing
NF is therefore the precise remaining task needed to turn this conditional existence and
ramification package into an unconditional one.
