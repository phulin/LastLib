# Rigid Uniformization of Abelian Varieties

## Contents

1. [Why abelian varieties acquire periods](#1-why-abelian-varieties-acquire-periods)
   - [From annuli to higher-dimensional groups](#11-from-annuli-to-higher-dimensional-groups)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [The three layers of uniformization](#13-the-three-layers-of-uniformization)
2. [Analytic tori and their characters](#2-analytic-tori-and-their-characters)
   - [Split tori](#21-split-tori)
   - [Laurent functions and units](#22-laurent-functions-and-units)
   - [Morphisms and character lattices](#23-morphisms-and-character-lattices)
   - [Nonsplit tori and descent](#24-nonsplit-tori-and-descent)
3. [Discrete lattices in analytic groups](#3-discrete-lattices-in-analytic-groups)
   - [What discreteness must mean](#31-what-discreteness-must-mean)
   - [The valuation map](#32-the-valuation-map)
   - [Fundamental polyannuli](#33-fundamental-polyannuli)
   - [The properness criterion](#34-the-properness-criterion)
4. [Quotients by lattices](#4-quotients-by-lattices)
   - [The quotient sheaf](#41-the-quotient-sheaf)
   - [Construction by annular charts](#42-construction-by-annular-charts)
   - [Separatedness and properness](#43-separatedness-and-properness)
   - [Functions, points, and base change](#44-functions-points-and-base-change)
5. [Automorphy factors and theta functions](#5-automorphy-factors-and-theta-functions)
   - [Line bundles on an infinite quotient](#51-line-bundles-on-an-infinite-quotient)
   - [Bilinear period data](#52-bilinear-period-data)
   - [Convergent theta series](#53-convergent-theta-series)
   - [Ampleness and positivity](#54-ampleness-and-positivity)
6. [Polarized analytic torus quotients](#6-polarized-analytic-torus-quotients)
   - [The nonarchimedean Riemann form](#61-the-nonarchimedean-riemann-form)
   - [The polarization homomorphism](#62-the-polarization-homomorphism)
   - [Algebraization](#63-algebraization)
   - [The Tate one-dimensional model](#64-the-tate-one-dimensional-model)
7. [Semiabelian schemes and formal groups](#7-semiabelian-schemes-and-formal-groups)
   - [The semiabelian middle ground](#71-the-semiabelian-middle-ground)
   - [Extensions of an abelian scheme by a torus](#72-extensions-of-an-abelian-scheme-by-a-torus)
   - [Formal completion and generic fiber](#73-formal-completion-and-generic-fiber)
   - [Extension data from the dual abelian scheme](#74-extension-data-from-the-dual-abelian-scheme)
8. [Raynaud extensions](#8-raynaud-extensions)
   - [Construction from semistable reduction](#81-construction-from-semistable-reduction)
   - [The analytic period lattice](#82-the-analytic-period-lattice)
   - [The uniformization exact sequence](#83-the-uniformization-exact-sequence)
   - [Independence and descent](#84-independence-and-descent)
9. [The Raynaud uniformization theorem](#9-the-raynaud-uniformization-theorem)
   - [Precise statement](#91-precise-statement)
   - [From an abelian variety to uniformizing data](#92-from-an-abelian-variety-to-uniformizing-data)
   - [From positive data to an abelian variety](#93-from-positive-data-to-an-abelian-variety)
   - [Uniqueness and functoriality](#94-uniqueness-and-functoriality)
10. [Line bundles and polarizations on Raynaud quotients](#10-line-bundles-and-polarizations-on-raynaud-quotients)
    - [Descent data on the extension](#101-descent-data-on-the-extension)
    - [The period pairing](#102-the-period-pairing)
    - [Positivity and principal polarizations](#103-positivity-and-principal-polarizations)
    - [Dual uniformization](#104-dual-uniformization)
11. [Reduction type and numerical invariants](#11-reduction-type-and-numerical-invariants)
    - [Good, semistable, and totally degenerate reduction](#111-good-semistable-and-totally-degenerate-reduction)
    - [Toric rank and potential semistability](#112-toric-rank-and-potential-semistability)
    - [Torsion away from the residue characteristic](#113-torsion-away-from-the-residue-characteristic)
    - [Isogenies and reduction data](#114-isogenies-and-reduction-data)
12. [Semistable Jacobians](#12-semistable-jacobians)
    - [The graph and the normalization](#121-the-graph-and-the-normalization)
    - [The generalized Jacobian of the special fiber](#122-the-generalized-jacobian-of-the-special-fiber)
    - [The Jacobian period pairing](#123-the-jacobian-period-pairing)
    - [Compact type and total degeneration](#124-compact-type-and-total-degeneration)
13. [Descent, base change, and morphisms](#13-descent-base-change-and-morphisms)
    - [Finite extensions of the ground field](#131-finite-extensions-of-the-ground-field)
    - [Galois descent of split data](#132-galois-descent-of-split-data)
    - [Morphisms in uniformizing coordinates](#133-morphisms-in-uniformizing-coordinates)
    - [A hypothesis ledger](#134-a-hypothesis-ledger)
14. [The uniformization package](#14-the-uniformization-package)
    - [The structural dictionary](#141-the-structural-dictionary)
    - [Conclusion](#142-conclusion)

## 1. Why abelian varieties acquire periods

### 1.1 From annuli to higher-dimensional groups

A smooth proper curve over a complete discretely valued field can degenerate into components joined at nodes. Analytically, a node contributes an annulus. For a genus-one curve with split multiplicative reduction, one can continue around that annulus indefinitely; returning to the same point amounts to multiplying a coordinate by a fixed element $q$ with $0<|q|<1$. The proper curve is therefore not the multiplicative group itself, but the quotient

$$
\mathbf G_m^{\mathrm{an}}/q^{\mathbf Z}.
$$

This is the nonarchimedean analogue of describing a complex elliptic curve by periods. In higher dimension two new features appear. Several independent annular directions form an analytic torus, and some directions may retain good reduction. The universal covering group is then an extension of a good-reduction abelian variety by a torus, while a discrete lattice supplies the periods.

The purpose of this book is to make that sentence exact. We first construct quotients of analytic tori by lattices and determine when they are proper. Automorphy factors then explain which line bundles descend and why positive period forms produce polarizations. Formal geometry supplies the integral extension from which the general analytic covering group arises. The resulting Raynaud uniformization characterizes abelian varieties with semistable reduction and describes the Jacobians of semistable curves.

### 1.2 Standing hypotheses and notation

Unless explicitly stated otherwise, $K$ is a complete discretely valued field with nontrivial absolute value $|\cdot|$, valuation ring $R=K^\circ$, maximal ideal $\mathfrak m$, and residue field $k$. We choose a uniformizer $\pi$ and normalize

$$
v:K^\times\longrightarrow\mathbf Z,
\qquad v(\pi)=1,
\qquad |a|=c^{v(a)}
$$

for a fixed $0<c<1$. Nothing requires $k$ to be finite or perfect unless said so. An algebraic $K$-group carries a superscript $\mathrm{an}$ after analytification. All analytic groups are separated and locally of finite type.

The rigid-analytic and formal results used from the preceding theory are these: affinoid spaces glue along rational domains; coherent objects descend over admissible covers; admissible formal blowups preserve generic fibers; proper rigid spaces admit useful formal models; and proper analytic varieties with ample line bundles algebraize. From the algebraic theory of abelian schemes we use dual abelian schemes, the Poincare bundle, isogenies, and the construction $L\mapsto\lambda_L$. We recall each interface when it is used.

A **lattice** always means a free abelian group of finite rank together with a specified embedding into an analytic group. It is not a lattice over $R$. A **torus** over a base is a smooth affine group which becomes a power of $\mathbf G_m$ after an étale extension. A **semiabelian scheme** is an extension of an abelian scheme by a torus. The word **semistable** for an abelian variety means that the identity component of its smooth integral model has semiabelian special fiber; in Chapter 8 we give the equivalent uniformization formulation that does not depend on having named that model in advance.

### 1.3 The three layers of uniformization

Uniformization separates degeneration into three pieces:

$$
0\longrightarrow T^{\mathrm{an}}
\longrightarrow E
\longrightarrow B^{\mathrm{an}}
\longrightarrow0,
\qquad
0\longrightarrow M\longrightarrow E
\longrightarrow A^{\mathrm{an}}\longrightarrow0. \tag{1.1}
$$

Here $T$ is a $K$-torus of rank $r$, $B$ is an abelian variety with good reduction, $E$ is the analytic generic fiber of a formal semiabelian extension, and $M\simeq\mathbf Z^r$ is discrete. The first sequence is algebraic or formal before taking its generic fiber; the second is genuinely analytic, because an infinite constant group cannot be the kernel of a finite-type algebraic morphism.

The dimensions add as expected:

$$
\dim A=\dim E=r+\dim B,
$$

but $M$ contributes no analytic dimension. It contributes compactness. Without $M$, the torus has unbounded valuation directions and is not proper. A full lattice identifies those directions and turns them into a compact real torus at the level of valuations. Positivity of a polarization is the additional assertion that the resulting period form is positive definite.

Good reduction is the case $r=0$: then $M=0$ and $A^{\mathrm{an}}=B^{\mathrm{an}}$. Totally degenerate reduction is the opposite case $B=0$: then $A^{\mathrm{an}}=T^{\mathrm{an}}/M$. The general theory interpolates between them.

## 2. Analytic tori and their characters

An analytic torus is the correct covering object because its characters turn multiplication into integral linear algebra. This chapter establishes that dictionary and also records precisely what is lost when a torus is not split over $K$.

### 2.1 Split tori

Let

$$
T=\mathbf G_{m,K}^r.
$$

Its character group and cocharacter group are

$$
X=X^*(T)=\operatorname{Hom}(T,\mathbf G_m)\simeq\mathbf Z^r,
\qquad
Y=X_*(T)=\operatorname{Hom}(\mathbf G_m,T)\simeq\mathbf Z^r.
$$

They are in perfect duality by composition. For $x=(n_1,\ldots,n_r)\in X$ and $z=(z_1,\ldots,z_r)$ we write

$$
x(z)=z^x=z_1^{n_1}\cdots z_r^{n_r}.
$$

The analytification $T^{\mathrm{an}}$ is not one affinoid. It is exhausted by polyannuli

$$
T[a,b]=\{z:a_i\leq v(z_i)\leq b_i\},
$$

where the integral endpoints may be replaced by rational ones after finite extension. Each is affinoid, and multiplication sends a product of two such polyannuli into the polyannulus obtained by adding bounds.

For any complete extension $L/K$, evaluation of characters gives a homomorphism

$$
\operatorname{trop}:T(L)\longrightarrow\operatorname{Hom}(X,\mathbf R),
\qquad
z\longmapsto(x\mapsto v_L(x(z))). \tag{2.1}
$$

For $K$ itself the image is $\operatorname{Hom}(X,\mathbf Z)$. The kernel is the maximal bounded subgroup

$$
T^\circ(K)=\{z:|x(z)|=1\text{ for all }x\in X\}=(R^\times)^r.
$$

Thus tropicalization forgets angular units and retains precisely the unbounded directions which a period lattice must control.

### 2.2 Laurent functions and units

On a closed polyannulus, analytic functions have Laurent expansions

$$
f=\sum_{x\in X}a_x\,x
$$

whose coefficients tend to zero after weighting by every boundary radius. On the entire torus, convergence on every bounded polyannulus is required. This elementary description gives a strong rigidity statement.

**Proposition 2.1.** Every analytic group homomorphism

$$
f:(\mathbf G_m^r)^{\mathrm{an}}\longrightarrow
(\mathbf G_m^s)^{\mathrm{an}}
$$

is the analytification of a unique algebraic homomorphism. Equivalently, each coordinate of $f$ is a Laurent monomial, and

$$
\operatorname{Hom}_{\mathrm{an}}(T_1^{\mathrm{an}},T_2^{\mathrm{an}})
\simeq\operatorname{Hom}_{\mathbf Z}(X^*(T_2),X^*(T_1)). \tag{2.2}
$$

**Proof.** It is enough to treat an analytic homomorphism $g:T^{\mathrm{an}}\to\mathbf G_m^{\mathrm{an}}$. On a polyannulus write $g=\sum a_xx$. The identity $g(zw)=g(z)g(w)$ holds on products of sufficiently small polyannuli and hence, by analytic continuation, wherever both sides are defined. Comparing the Laurent coefficient of $x(z)y(w)$ shows $a_xa_y=0$ for $x\ne y$. Since $g$ is invertible, exactly one coefficient is nonzero. The identity $g(1)=1$ makes that coefficient $1$, so $g=x$ is a character. Applying this to all target characters proves (2.2). Uniqueness follows because characters separate torus points. $\square$

Translation behaves differently: every analytic automorphism of the underlying space compatible with the group law up to a chosen origin is a monomial homomorphism followed by translation. Keeping the origin visible is therefore essential when descending group structures.

### 2.3 Morphisms and character lattices

Contravariance in (2.2) is easy to mishandle. If $f:T_1\to T_2$, then

$$
f^*:X^*(T_2)\longrightarrow X^*(T_1),
\qquad x\longmapsto x\circ f.
$$

The map is an isogeny precisely when $f^*$ is injective with finite cokernel. Indeed, after choosing bases it is represented by an integral matrix $C$. Smith normal form reduces $C$ to diagonal entries $d_i>0$. The corresponding group map is a product of $z_i\mapsto z_i^{d_i}$, which is finite faithfully flat with kernel $\prod_i\mu_{d_i}$. Its degree is $|\det C|$. This proof remains valid when the residue characteristic divides some $d_i$, because finite flatness is scheme-theoretic and does not count geometric points.

The tropical map transforms covariantly:

$$
\operatorname{trop}(f(z))(x)
=\operatorname{trop}(z)(f^*x).
$$

Thus an isogeny induces a finite-index linear map on integral valuation lattices. Later this will imply invariance of toric rank under isogeny.

### 2.4 Nonsplit tori and descent

Let $T/K$ be a torus and choose a finite Galois extension $L/K$ splitting it, with group $G$. Then $X^*(T_L)$ is a free $\mathbf Z$-module with a $G$-action, and $T$ is recovered from this module. A morphism of $K$-tori corresponds to a $G$-equivariant homomorphism of character lattices in the opposite direction.

Over $L$, tropicalization lands in $\operatorname{Hom}(X^*(T_L),\mathbf R)$ and is $G$-equivariant. A period lattice over $K$ is therefore not generally a set of $K$-rational points with chosen coordinates. It is a discrete subgroup after splitting, stable under the semilinear Galois action and equipped with effective descent data. All constructions below are first written in split coordinates because their proofs are transparent there. Chapter 13 proves that their canonical nature makes them descend.

One should not replace a nonsplit torus by its group of $K$-points. An anisotropic torus can have bounded $K$-points although it becomes unbounded over a splitting field. Properness of a quotient is geometric, so the full character module after finite separable extension is the correct invariant.

## 3. Discrete lattices in analytic groups

An infinite subgroup can be a quotient kernel only if its translates do not accumulate. For a torus, tropicalization converts this analytic requirement into the familiar condition that integral vectors form a full lattice in a real vector space.

### 3.1 What discreteness must mean

Let $G$ be a quasi-separated analytic group. An injective homomorphism $u:M\to G(K)$ from a free abelian group is **discrete** if every quasi-compact admissible subset of $G$ meets $u(M)$ in a finite set. Equivalently, the family of translates $u(m)U$, for $U$ relatively compact, is locally finite. This is stronger than saying that every point is isolated in a naive topology; local finiteness is what makes an analytic quotient possible.

If $G=T^{\mathrm{an}}$ is split, a subgroup contained in $T^\circ(K)$ cannot be an infinite discrete lattice. Indeed $T^\circ$ is affinoid, hence quasi-compact, and would meet it infinitely. Therefore periods must escape in valuation directions.

**Lemma 3.1.** For $u:M\to T(K)$, the image is discrete if and only if

$$
\ell=\operatorname{trop}\circ u:
M\longrightarrow N:=\operatorname{Hom}(X,\mathbf Z) \tag{3.1}
$$

has finite kernel and discrete image. If $u$ is injective and $M$ is torsion-free, this is equivalent to $\ell_\mathbf R:M_\mathbf R\to N_\mathbf R$ being injective.

**Proof.** A bounded polyannulus has tropical image in a compact polytope. If $\ell(M)$ is discrete and $\ker\ell$ finite, its inverse image in that polytope is finite, proving analytic discreteness. Conversely, infinitely many periods with bounded tropicalization lie in one fixed enlargement of a bounded polyannulus; this violates discreteness. A homomorphism between finite-rank free abelian groups has discrete image automatically, and has finite kernel exactly when its real extension is injective. $\square$

### 3.2 The valuation map

Pairing periods with characters gives the integral matrix

$$
b:M\times X\longrightarrow\mathbf Z,
\qquad b(m,x)=v(x(u(m))). \tag{3.2}
$$

It is bilinear. The associated map $M\to X^\vee$ is precisely $\ell$. If $\operatorname{rank}M=r=\operatorname{rank}X$ and $\det b\ne0$ in chosen bases, then $\ell(M)$ has finite index in $X^\vee$. We call such a period group **full**.

The sign of $b$ has no intrinsic meaning because replacing $v$ by $-\log|\cdot|$ rescales it positively, while replacing a basis of $M$ by its negative reverses rows. Positivity enters only after a homomorphism $M\to X$ has paired the two different lattices. Mere properness requires fullness, not symmetry or positive definiteness.

### 3.3 Fundamental polyannuli

Assume $M$ is full. Choose a bounded half-open parallelotope $P\subset N_\mathbf R$ meeting every coset of $N_\mathbf R/\ell(M)$ exactly once. Its inverse image under tropicalization is not usually an affinoid because of half-open faces, but it is covered by finitely many closed rational polyannuli. Enlarging $P$ slightly to $P^+$, only finitely many translates $P^++\ell(m)$ meet $P^+$. Consequently the corresponding analytic domains have only finitely many nonempty period overlaps.

This construction is the higher-dimensional replacement for choosing the annulus

$$
|q|\leq|z|\leq1
$$

as a fundamental region for $q^\mathbf Z\subset K^\times$. The two boundary circles are glued by multiplication by $q$. In several variables, pairs of parallel faces are glued by the corresponding periods, and corners satisfy the cocycle condition because $M$ is abelian.

### 3.4 The properness criterion

**Theorem 3.2.** Let $u:M\hookrightarrow T(K)$ be discrete, where $T$ is a split torus of rank $r$. The analytic quotient $T^{\mathrm{an}}/M$ is proper if and only if $M$ is full, equivalently

$$
\operatorname{rank}M=r
\quad\text{and}\quad
b_\mathbf R:M_\mathbf R\xrightarrow{\sim}X_\mathbf R^\vee. \tag{3.3}
$$

**Proof strategy.** Properness is detected by whether every valuation direction has a compact fundamental region. Fullness gives such a region; failure of fullness leaves an unbounded real direction and hence an analytic boundary.

Suppose first that (3.3) holds. The finitely many closed polyannuli covering $P$ descend to a finite affinoid cover of the quotient. After every complete extension $L/K$, tropicalization still identifies valuation vectors modulo the full lattice $\ell(M)$, so every point has a representative in the fixed compact polytope. The valuative criterion follows: a point over the fraction field of a complete valuation extension may be translated by a unique period up to bounded ambiguity so that its character valuations lie in $P$; its unit coordinates then extend to the valuation ring. Uniqueness follows from separatedness of the quotient, proved in Chapter 4. Thus the quotient is proper.

For completeness, representability is not being assumed in this step. Cover a slight enlargement of $P$ by finitely many closed rational polyannuli. Glue any two along the finitely many rational subdomains related by a period translation. Local finiteness follows because a bounded polytope meets only finitely many translates of $\ell(M)$. The cocycle is the addition law of $M$. Affinoid gluing therefore constructs the quotient used above. Chapter 4 verifies its universal sheaf property and separatedness; alternatively, separatedness here follows directly because the locally finite union of the closed translation graphs is closed.

Conversely, if the real span of $\ell(M)$ is proper in $N_\mathbf R$, choose a nonzero linear functional $h$ vanishing on it. Along a cocharacter ray $t\mapsto\lambda(t)$ with $h(\operatorname{trop}\lambda(t))$ unbounded, no period translate returns the ray to a bounded set. This defines a punctured valuation-disc map to the quotient whose tropical coordinate tends to infinity and which cannot extend across the puncture. Hence the quotient is not proper. If $\ell$ has a kernel, discreteness already fails by Lemma 3.1. $\square$

The theorem distinguishes compactness from projectivity. A full quotient is proper as an analytic group. To algebraize it as an abelian variety, one needs an ample line bundle, and that requires a positive Riemann form.

## 4. Quotients by lattices

Finite group quotients are constructed by invariant affine charts. A lattice quotient is subtler because no affinoid meets only finitely many translates globally. Local finiteness and a fundamental polyannulus replace finiteness of the group.

### 4.1 The quotient sheaf

Let $u:M\hookrightarrow G(K)$ be a discrete subgroup of an analytic group. On the admissible site define the sheafification

$$
(G/M)(S)=G(S)/M
$$

where $M$ acts by translation as a constant étale group. Sheafification matters even though the periods are $K$-rational: local representatives on an analytic base can differ by locally constant elements of $M$ and need not admit one global representative.

A representing quotient $p:G\to Q$ must satisfy

$$
M\times G\xrightarrow{\sim}G\times_QG,
\qquad(m,g)\longmapsto(u(m)g,g). \tag{4.1}
$$

Unlike an isogeny, $p$ is not finite or quasi-compact when $M\ne0$. It is an analytic covering with discrete fibers.

### 4.2 Construction by annular charts

For $G=T^{\mathrm{an}}$ and a full lattice, choose finitely many closed polyannuli $U_i$ covering an enlarged fundamental region. For each pair $(i,j)$ only finitely many $m\in M$ satisfy

$$
u(m)U_i\cap U_j\ne\varnothing.
$$

Each intersection is a finite union of rational domains, and translation gives the gluing isomorphisms. The group law on $M$ supplies the cocycle on triple overlaps. Affinoid gluing therefore produces a separated analytic space $Q$ and a map $T^{\mathrm{an}}\to Q$ satisfying (4.1).

The same argument works for a discrete lattice in an analytic group $E$ which is an extension of a proper analytic group by $T^{\mathrm{an}}$. Cover the proper base by finitely many affinoids on which the torsor is analytically trivial after refinement. Above each chart the construction is the toric one, and compatibility of torsor translations glues the local quotients.

**Theorem 4.1 (analytic lattice quotient).** If $E$ is an extension of a proper analytic group by a torus and $M\hookrightarrow E(K)$ has discrete image whose tropical projection is full, the sheaf $E/M$ is represented by a proper smooth analytic group. Formation of the quotient commutes with complete scalar extension.

**Proof.** Representability follows from the locally finite construction. Smoothness descends from $E$ because the covering is locally a disjoint union of isomorphisms. The group operations descend since translations by $M$ form a normal action; commutativity makes normality automatic here. Properness is proved exactly as in Theorem 3.2 after covering the proper abelian base. Base change preserves the finite overlap pattern after rational subdivision and represents the base-changed sheaf quotient, proving the last assertion. $\square$

### 4.3 Separatedness and properness

The diagonal of $Q=E/M$ pulls back along $E\times E\to Q\times Q$ to the union of the graphs of translations by $M$. Discreteness makes this union locally finite. Each graph is closed because $E$ is separated, so the union is closed. Faithfully flat local descent then makes the diagonal of $Q$ closed. This proves separatedness without appealing circularly to properness.

If the tropical image has smaller rank, the same construction may still represent a nonproper quotient. For instance $\mathbf G_m^{2,\mathrm{an}}/\langle(q,1)\rangle$ is the product of a proper one-dimensional quotient with $\mathbf G_m^{\mathrm{an}}$. One unquotiented valuation direction remains. Thus rank equality is a geometric necessity, not a convenient symmetry assumption.

### 4.4 Functions, points, and base change

An analytic function on $Q$ is an $M$-invariant analytic function on $E$. If $Q$ is proper and geometrically connected, it is constant. In the toric case this can be proved directly: write

$$
f=\sum_{x\in X}a_xx.
$$

Invariance under $u(m)$ gives $a_xx(u(m))=a_x$ for every $m$. If $a_x\ne0$, fullness implies $x(u(m))=1$ for all $m$ only when $x=0$. Thus $f=a_0$. This calculation is a useful preview of theta functions: a nontrivial line bundle replaces invariance by a controlled automorphy factor, permitting nonconstant sections.

For a complete extension $L/K$, one must quotient by the same abstract lattice mapped into $E(L)$, not by all new $L$-points that happen to have integral tropical coordinates. The canonical comparison is

$$
(E/M)_L\simeq E_L/M. \tag{4.2}
$$

If the original periods are defined only after a finite extension, Galois descent replaces this literal formula; the abstract lattice then carries an action and the quotient descends as a whole.

## 5. Automorphy factors and theta functions

Proper analytic quotients become algebraic only after one constructs ample line bundles. On a covering group, a line bundle on the quotient is a line bundle together with instructions for identifying all its period translates. Those instructions are automorphy factors.

### 5.1 Line bundles on an infinite quotient

Let $Q=T^{\mathrm{an}}/M$ with $T$ split and $M$ full. Trivialize the pullback of a line bundle $L$ to $T^{\mathrm{an}}$. Descent is then a family of invertible analytic functions $c_m(z)$ satisfying

$$
c_{m+n}(z)=c_m(u(n)z)c_n(z). \tag{5.1}
$$

Changing the trivialization by an invertible analytic function $h$ replaces

$$
c_m(z)\quad\text{by}\quad
h(u(m)z)c_m(z)h(z)^{-1}. \tag{5.2}
$$

Thus line bundles are represented by automorphy cocycles modulo coboundaries. This is ordinary descent along (4.1), applied on the locally finite annular cover. There is no hidden convergence condition on the cocycle beyond analyticity on the covering group and local finiteness of the action.

For polarizations it suffices to use cocycles of the form

$$
c_m(z)=a(m)\,\lambda(m)(z), \tag{5.3}
$$

where $\lambda:M\to X$ is a homomorphism and $a:M\to K^\times$ is a function. Substitution into (5.1) gives

$$
a(m+n)=a(m)a(n)\lambda(m)(u(n)). \tag{5.4}
$$

Interchanging $m$ and $n$ shows that such $a$ can exist only if

$$
\lambda(m)(u(n))=\lambda(n)(u(m)). \tag{5.5}
$$

Conversely, every symmetric bicharacter satisfying (5.5) has a quadratic refinement over the same field. For a basis $e_1,\ldots,e_r$ of $M$, choose arbitrary $a(e_i)\in K^\times$ and set, for $m=\sum_i n_ie_i$,

$$
a(m)=\prod_i a(e_i)^{n_i}
\prod_i\lambda(e_i)(u(e_i))^{n_i(n_i-1)/2}
\prod_{i<j}\lambda(e_i)(u(e_j))^{n_in_j}. \tag{5.6a}
$$

A direct expansion of the integer exponents proves (5.4); symmetry proves that cross-terms are independent of the chosen ordering convention. Diagonal square roots are needed only for the special normalization $a(m)^2=\lambda(m)(u(m))$, not for existence of a cocycle.

### 5.2 Bilinear period data

Define

$$
q_\lambda(m,n)
=v(\lambda(m)(u(n)))
=-\frac{\log|\lambda(m)(u(n))|}{-\log c}. \tag{5.6}
$$

It is an integral bilinear form, symmetric exactly when (5.5) holds. With our normalization $v(\pi)=1$, positivity means

$$
q_\lambda(m,m)>0\qquad(m\ne0). \tag{5.7}
$$

For the one-dimensional period $u(n)=q^n$ and $\lambda(n)=n$, one has $q_\lambda(m,n)=mnv(q)$, which is positive definite because $0<|q|<1$.

The function $a$ is a quadratic refinement of the multiplicative bicharacter. Taking valuations in (5.4) yields

$$
v(a(m+n))=v(a(m))+v(a(n))+q_\lambda(m,n). \tag{5.8}
$$

Consequently $m\mapsto v(a(m))$ has positive quadratic growth when $q_\lambda$ is positive definite, up to an additive linear function. This growth is exactly what makes theta series converge.

### 5.3 Convergent theta series

A section of $L$ corresponds, under the chosen trivialization, to an analytic function $f$ on $T^{\mathrm{an}}$ satisfying

$$
f(u(m)z)=c_m(z)f(z). \tag{5.9}
$$

Write $f=\sum_{x\in X}b_xx(z)$. Equation (5.9) gives a recurrence among coefficients along cosets of $\lambda(M)$ in $X$. For one representative $x_0$ in each coset, the remaining coefficients are forced. Up to the convention used to solve the recurrence, the resulting series has terms whose valuations contain

$$
\tfrac12q_\lambda(m,m)+\text{a linear function of }m. \tag{5.10}
$$

Positive definiteness makes (5.10) tend to $+\infty$ quadratically. Linear character growth on any fixed polyannulus cannot cancel it. Hence the series converges uniformly on every bounded polyannulus and defines an analytic theta function.

**Proposition 5.1.** If $q_\lambda$ is positive definite and $\lambda(M)$ has finite index in $X$, then the theta functions attached to (5.3) form a finite-dimensional space. After a sufficiently large tensor power, they have no common zero and separate points and tangent directions on $Q$.

**Proof strategy.** The coefficient recurrence leaves one free leading coefficient for each coset of $\lambda(M)$ in $X$, so finite index gives finite dimension. For $L^n$, the relevant cosets are those of $n\lambda(M)$, producing enough independent leading characters. Given two points not differing by a period, choose a character whose tropical or unit value distinguishes them; for $n$ large, select a theta function with that leading character. Quadratic convergence makes all other terms strictly smaller on a suitable rational neighborhood, so the leading term controls its value. The same argument with first-order differences separates tangent vectors. A finite affinoid cover of the proper quotient makes one value of $n$ work globally. $\square$

The proof explains why positive definiteness, rather than nondegeneracy, is required. An indefinite form makes coefficients grow in one direction and decay in another, so the formal theta expression fails to converge on fixed polyannuli.

### 5.4 Ampleness and positivity

**Theorem 5.2 (analytic Appell--Humbert criterion).** For automorphy data $(\lambda,a)$ satisfying (5.4), the descended line bundle $L$ on $Q$ is ample if and only if $q_\lambda$ is positive definite. It is numerically nondegenerate if and only if $q_\lambda$ is nondegenerate.

**Proof.** If $q_\lambda$ is positive definite, Proposition 5.1 gives a closed immersion into projective space from a high tensor power of $L$, so $L$ is ample. Conversely, choose a periodic rational polyhedral formal model of $Q$. For $m\ne0$, the segment from a point $n$ of the tropical space to $n+\ell(m)$ closes to a one-cycle in the quotient cell complex. After a rational subdivision, its inverse image is a chain of one-dimensional toric strata. The degree of $L$ on this effective closed chain is a positive integral multiple of $q_\lambda(m,m)$: across each face the change of the piecewise-linear support function of $L$ is the valuation of the automorphy factor, and summing the changes around the period gives (5.6). An ample bundle has positive degree on every such nonzero effective chain, so $q_\lambda(m,m)>0$.

If the form has a radical, the support function is affine along a nonzero tropical direction. After a rational subdivision, the corresponding toric stratum has degree zero, and the polarization has positive-dimensional kernel; hence $L$ is numerically degenerate. If the form is nondegenerate, the induced lattice map has finite cokernel and the polarization kernel is finite, proving numerical nondegeneracy. $\square$

This theorem is the decisive algebraization input. A proper analytic group need not have been presented algebraically, but a positive period form supplies an ample line bundle and hence a projective algebraic model.

## 6. Polarized analytic torus quotients

The preceding cocycles describe individual line bundles. We now extract the intrinsic object that survives a change of trivialization: a symmetric positive map between the period lattice and the character lattice. It is the nonarchimedean counterpart of a Riemann form.

### 6.1 The nonarchimedean Riemann form

Let $T$ be split with character lattice $X$, let $u:M\to T(K)$ be a full lattice, and let $Q=T^{\mathrm{an}}/M$. A **Riemann form** is a homomorphism

$$
\lambda:M\longrightarrow X \tag{6.1}
$$

such that the multiplicative pairing

$$
(m,n)\longmapsto\lambda(m)(u(n))
$$

is symmetric and its valuation $q_\lambda$ is positive definite. Fullness forces $\lambda$ to be injective with finite cokernel: if $\lambda(m)=0$, then $q_\lambda(m,m)=0$; equality of ranks then gives finite cokernel.

A Riemann form need not by itself choose a canonical line bundle over $K$. One must also choose a quadratic refinement $a$ satisfying (5.4). Formula (5.6a) constructs one in split coordinates, and different choices differ by a character of $M$. For nonsplit descent, an invariant Riemann form need not admit an invariant choice of refinement without passing to a cover. The resulting polarization homomorphism is nevertheless defined over $K$ whenever the Riemann form and its descent class are Galois-invariant. This distinction mirrors the algebraic fact that a polarization may be global even when no global ample bundle induces it.

### 6.2 The polarization homomorphism

For a descended ample line bundle $L$, translation produces

$$
\lambda_L:Q\longrightarrow Q^\vee,
\qquad z\longmapsto t_z^*L\otimes L^{-1}. \tag{6.2}
$$

The square identity for automorphy factors proves that this is a homomorphism. Its effect on periods and characters is governed by (6.1). More precisely, the kernel has a filtration whose two finite pieces are dual to one another and whose common order is $[X:\lambda(M)]$. Hence

$$
\deg\lambda_L=[X:\lambda(M)]^2. \tag{6.3}
$$

To justify the filtration, choose representatives in $T$ for a kernel point of (6.2). Translation preserves the automorphy class exactly when its character on $M$ belongs to the image of restriction $X\to\operatorname{Hom}(M,K^\times)$ modulo the subgroup generated by $\lambda(M)$. The connected multiplicative part and the quotient of character lattices each have order $[X:\lambda(M)]$; Cartier duality identifies the two. Multiplying their ranks gives (6.3). This is a scheme-theoretic statement and remains valid when the residue characteristic divides the index.

Thus $L$ gives a principal polarization precisely when

$$
\lambda:M\xrightarrow{\sim}X. \tag{6.4}
$$

The positivity condition is still essential: an abstract lattice isomorphism satisfying symmetry but not positivity does not define an ample class.

### 6.3 Algebraization

The algebraization step used here is not confined to curves.

**Projective algebraization lemma.** A closed analytic subspace $Z\hookrightarrow\mathbf P_K^{N,\mathrm{an}}$ is the analytification of a unique closed algebraic subspace of $\mathbf P_K^N$.

**Proof.** Let $\mathcal I$ be its coherent analytic ideal. Cover projective space by the standard affinoid charts and use analytic coherent descent to obtain a finite presentation on their intersections. Twist by $\mathcal O(n)$ for $n$ large. The usual monomial Čech complex computes analytic cohomology: convergent division splits every term involving a negative exponent exactly as in the algebraic computation. Hence $H^1(\mathcal I(n))=0$, and $\mathcal I(n)$ is generated by finitely many global analytic sections.

Global analytic sections of $\mathcal O(n)$ on projective space are homogeneous polynomials of degree $n$. Indeed, on each standard chart they have convergent power-series expansions; compatibility on the torus overlaps forbids all Laurent exponents outside the finite degree-$n$ simplex. Thus the chosen generators of $\mathcal I(n)$ are algebraic homogeneous forms. Let $I$ be the homogeneous ideal generated by all such forms, increasing $n$ finitely many times to capture the kernels of the presentations. Its analytification has ideal sheaf $\mathcal I$ on every standard chart by coherent generation. It therefore defines $Z$. Uniqueness follows because an algebraic homogeneous form vanishing analytically vanishes coefficientwise. $\square$

**Theorem 6.1 (algebraization of positive torus quotients).** Let $Q=T^{\mathrm{an}}/M$ be a full split torus quotient. If $Q$ admits a Riemann form, then there is a unique abelian variety $A/K$ with

$$
A^{\mathrm{an}}\simeq Q. \tag{6.5}
$$

Every analytic homomorphism between two such quotients is the analytification of a unique algebraic homomorphism.

**Proof.** A quadratic refinement gives, after finite extension, an ample analytic line bundle by Theorem 5.2. The theta sections of a high power embed $Q$ into projective space. Proper analytic algebraization turns the image and its coherent ideal into a projective algebraic variety $A$. The analytic group law is a morphism between proper analytifications, so its graph algebraizes uniquely; the same is true for inverse and identity. Smoothness and geometric connectedness may be checked after analytification and finite extension. Thus $A$ is an abelian variety. The construction and its uniqueness descend because the projective model, group law, and polarization carry effective finite Galois descent data.

For the last assertion, the graph of an analytic homomorphism is a closed analytic subspace of the proper product. Proper comparison algebraizes it. Its first projection is analytically an isomorphism, hence algebraically an isomorphism, and the second projection is the required homomorphism. Uniqueness follows from density of analytic points or faithfulness of analytification on proper varieties. $\square$

The theorem does not say every full lattice quotient is algebraizable. Positivity is the projectivity criterion. In the applications below the polarization of the original abelian variety supplies it automatically.

### 6.4 The Tate one-dimensional model

Take $q\in K^\times$ with $0<|q|<1$, put $T=\mathbf G_m$, and embed $M=\mathbf Z$ by $n\mapsto q^n$. Then

$$
E_q^{\mathrm{an}}=\mathbf G_m^{\mathrm{an}}/q^\mathbf Z \tag{6.6}
$$

is proper. The identity $\lambda(n)=n$ is a principal Riemann form because

$$
q_\lambda(m,n)=mnv(q).
$$

A standard theta function is obtained by choosing a quadratic refinement and summing its translates; one convenient normalization is

$$
\Theta(z)=\prod_{n\ge0}(1-q^nz)
\prod_{n\ge1}(1-q^nz^{-1}), \tag{6.7}
$$

which converges on every closed annulus and satisfies a one-period functional equation. Suitable quotients of theta functions give projective coordinates. The algebraized group is an elliptic curve with split multiplicative reduction.

The condition $|q|<1$ is not cosmetic. If $|q|=1$, the subgroup $q^\mathbf Z$ is contained in the bounded affinoid unit circle and is not discrete unless finite. If $|q|>1$, replacing $q$ by $q^{-1}$ returns to the chosen convention. The length $v(q)$ is the one-dimensional period form and later becomes the length of the loop in the reduction graph.

## 7. Semiabelian schemes and formal groups

Pure torus quotients describe total degeneration. A general semistable abelian variety retains an abelian part with good reduction. The covering group is therefore a semiabelian extension, and formal completion selects the bounded neighborhood in which its integral structure lives.

### 7.1 The semiabelian middle ground

Over a scheme $S$, a semiabelian scheme $G/S$ fits into an exact sequence of smooth commutative group schemes

$$
0\longrightarrow T\longrightarrow G\longrightarrow B\longrightarrow0, \tag{7.1}
$$

where $T/S$ is a torus and $B/S$ is an abelian scheme. The sequence is exact as fppf sheaves. Fibers are connected and smooth, but $G$ is proper exactly when $T=0$.

The dimensions are

$$
\dim(G/S)=\operatorname{rank}T+\dim(B/S).
$$

The torus is the maximal affine subgroup in every geometric fiber and is therefore intrinsic. The quotient $B$ is intrinsic as well. Under base change both pieces pull back, although the torus may become split only after an étale extension.

Over a complete DVR, the formal completion of $G$ along its special fiber contains bounded toric points. Its analytic generic fiber is not all of $G_K^{\mathrm{an}}$ when $T\ne0$; for $\mathbf G_{m,R}$ it is the unit circle $|z|=1$. Raynaud's construction enlarges this bounded formal group by translated formal charts so that its analytic generic fiber contains all valuation directions while retaining a formal group model.

### 7.2 Extensions of an abelian scheme by a torus

Assume first that $T=\mathbf G_{m,S}^r$ has character lattice $X$. An extension (7.1) determines, for every $x\in X$, the pushout along $x:T\to\mathbf G_m$. A $\mathbf G_m$-extension of $B$ is the complement of the zero section in a rigidified algebraically trivial line bundle on $B$. Thus the extension is classified by a homomorphism

$$
c:X\longrightarrow B^\vee(S). \tag{7.2}
$$

**Proposition 7.1.** The assignment (7.2) is an equivalence between extensions of $B$ by the split torus with character group $X$ and homomorphisms $X\to B^\vee$. It commutes with arbitrary base change.

**Proof.** Pushout gives the forward map. Conversely, pull back the Poincare bundle on $B\times B^\vee$ along each point $c(x)$; remove its zero section to obtain a $\mathbf G_m$-torsor. The additivity of $c$ and the biextension law identify the tensor product torsor for $x+y$ with those for $x$ and $y$. Taking the simultaneous spectrum of the resulting $X$-graded invertible algebra constructs a $T$-torsor $E\to B$. The biextension laws define its group law. The two constructions are inverse by characterwise detection of torus torsors. Base change compatibility follows from that of the Poincare bundle. $\square$

For a nonsplit torus, the same statement holds after an étale splitting cover with Galois-equivariant $X$. Effective descent recovers the extension over $S$.

### 7.3 Formal completion and generic fiber

Let $\mathcal B/R$ be an abelian scheme and let

$$
0\to\mathcal T\to\mathcal E\to\mathcal B\to0 \tag{7.3}
$$

be semiabelian. Completing along the special fiber gives formal groups

$$
0\to\widehat{\mathcal T}\to\widehat{\mathcal E}
\to\widehat{\mathcal B}\to0. \tag{7.4}
$$

The generic fiber of $\widehat{\mathcal B}$ is all of $B^{\mathrm{an}}$ because $\mathcal B$ is proper. The generic fiber of $\widehat{\mathcal T}$ is only the bounded subgroup. To recover the whole analytic torus, translate the formal toric charts by all cocharacters and glue them along rational subannuli. Doing this compatibly in the torsor $\mathcal E$ produces a formal object locally of finite type, usually denoted $\mathfrak E$, whose analytic generic fiber $E$ fits into

$$
0\longrightarrow T^{\mathrm{an}}
\longrightarrow E\longrightarrow B^{\mathrm{an}}
\longrightarrow0. \tag{7.5}
$$

The construction is independent of the choice of toric coordinates: two choices admit a common rational subdivision, hence a common admissible formal refinement. It also commutes with finite base change after normalization and removal of uniformizer torsion.

### 7.4 Extension data from the dual abelian scheme

Sequence (7.5) is controlled by the same map

$$
c:X\longrightarrow B^\vee(K) \tag{7.6}
$$

as its algebraic generic extension. Having good reduction in the abelian part means more: the points $c(x)$ extend to sections of $\mathcal B^\vee/R$. By the extension theorem for homomorphisms of abelian schemes, this integrality is independent of a chosen presentation once it holds generically.

The dual extension will use a second lattice $M$. A homomorphism $u:M\to E(K)$ projects to points of $B(K)$. The Poincare pairing between those projected points and $c(X)\subset B^\vee(K)$ supplies the cross-term which replaces the elementary evaluation $x(u(m))$ of the pure torus case. This is why the general period pairing is naturally expressed with a trivialization of a pulled-back Poincare bundle, not only with coordinates.

## 8. Raynaud extensions

We now pass from a semistable abelian variety to its covering group. The central geometric operation is to complete the smooth integral group along its semiabelian special fiber and then unfold the toric valuation directions. The kernel of the map back to the proper generic fiber is the period lattice.

### 8.1 Construction from semistable reduction

Let $A/K$ be an abelian variety. A **semistable model** for the purpose of uniformization is a smooth separated $R$-group $\mathcal G$ with generic fiber $A$ whose special-fiber identity component is semiabelian:

$$
0\longrightarrow T_s\longrightarrow\mathcal G_s^0
\longrightarrow B_s\longrightarrow0. \tag{8.1}
$$

The smooth model need not be proper; indeed a positive-dimensional torus in (8.1) obstructs properness. Smoothening and the group law make the identity component canonical among such models. The toric rank is $r=\dim T_s$.

After a finite unramified extension splitting $T_s$, the formal identity neighborhood admits a canonical structure theorem. It produces a formal Raynaud extension

$$
0\longrightarrow\mathfrak T\longrightarrow\mathfrak E
\longrightarrow\mathfrak B\longrightarrow0. \tag{8.2}
$$

Here $\mathfrak T$ is the formal torus together with its translated charts. Its generic fiber is the analytic extension (7.5), with $B$ having good reduction.

**Formal structure lemma.** Let $\mathcal G/R$ be smooth with generic fiber an abelian variety and with semiabelian identity component (8.1). There are a formal abelian scheme $\mathfrak B/R$, a formal torus $\mathfrak T/R$, and an extension (8.2) whose restriction to the special fiber is (8.1). The extension is unique up to unique isomorphism after admissible refinement.

**Proof strategy.** Work successively modulo $\pi^{n+1}$. The maximal torus in the special fiber is characterized as the maximal connected affine subgroup, so every automorphism preserves it. Smoothness lifts its characters and multiplication law through square-zero thickenings; the obstruction would lie in the deformation group of a split diagonalizable group, which vanishes because its Hopf algebra is graded by the free lattice $X$. Quotient the completed group by this lifted formal torus. The quotient is proper at level zero. A relatively ample cubical bundle on its special fiber lifts, after a fixed tensor power, together with the cube trivialization. Formal projectivity and the infinitesimal lifting criterion then make every thickened quotient proper and smooth. The compatible system is the formal abelian scheme $\mathfrak B$.

The original completed group is now a formal $\mathfrak T$-torsor over $\mathfrak B$. Characterwise pushout gives rigidified algebraically trivial formal line bundles. The formal Poincare bundle identifies these with a homomorphism $X\to\mathfrak B^\vee$, and its biextension law reconstructs (8.2). At each stage, two lifts differ by a homomorphism into an infinitesimal vector group. Properness of the abelian quotient makes such a homomorphism constant, and its value at the identity is zero. This gives uniqueness. Changes made to choose affine formal charts are reconciled by admissible blowups, which do not change the analytic generic fiber. $\square$

The lemma does not claim that an arbitrary abelian variety $B_s/k$ has a distinguished lift. The lift here is forced by the completed group $\mathcal G$; this dependence is essential.

### 8.2 The analytic period lattice

There is a canonical analytic homomorphism

$$
p:E\longrightarrow A^{\mathrm{an}} \tag{8.3}
$$

which is locally an isomorphism near the identity. It comes from comparing the formal completion of $\mathcal G$ with (8.2) on their common bounded identity neighborhood and then translating by the group law.

Its kernel $M$ is discrete. Indeed, a sufficiently small affinoid neighborhood $U$ of the identity maps isomorphically to its image in $A^{\mathrm{an}}$. Distinct kernel translates of $U$ are disjoint. Since a quasi-compact subset of $E$ is covered by finitely many translates of bounded formal charts, it meets only finitely many kernel points. Thus $M$ is a lattice in the analytic sense.

The tropical projection identifies

$$
M\otimes\mathbf R\xrightarrow{\sim}
\operatorname{Hom}(X^*(T),\mathbf R). \tag{8.4}
$$

Injectivity follows from discreteness and the properness of the bounded kernel: a period with zero tropicalization lies in the bounded formal group, where (8.3) is locally injective; a torsion-free discrete kernel has no nonzero such element. Surjectivity follows from properness of $A$: if a valuation direction were missing, the punctured-disc argument of Theorem 3.2 would give a nonextendable map to $A^{\mathrm{an}}$. Hence $M$ is free of rank $r$ and full.

### 8.3 The uniformization exact sequence

The local comparison extends to an exact sequence of analytic sheaves

$$
0\longrightarrow M\xrightarrow{u}E
\xrightarrow{p}A^{\mathrm{an}}\longrightarrow0. \tag{8.5}
$$

Surjectivity deserves explanation. The image of $p$ is an admissible open subgroup because $p$ is locally an isomorphism at the identity. Its complement, if nonempty, would be a union of cosets. But $A^{\mathrm{an}}$ is connected and quasi-compact; finitely many translates of the identity neighborhood cover it, and inductively each translate lifts through $E$. Thus $p$ is locally surjective and hence an epimorphism of analytic sheaves. The fiber identity

$$
M\times E\simeq E\times_{A^{\mathrm{an}}}E
$$

then identifies $A^{\mathrm{an}}$ with $E/M$.

**Theorem 8.1.** An abelian variety with semistable reduction admits (8.2) and (8.5), where $B$ has good reduction, $T$ has rank equal to the toric rank of the special fiber, and $M$ is a full lattice of the same rank.

The pure good-reduction and pure toric cases discussed earlier are recovered by setting $T=0$ or $B=0$.

### 8.4 Independence and descent

A ramified extension may split the torus or make semistability visible. Over such an extension, the construction carries a semilinear Galois action. The subtorus is intrinsic as the maximal affine part, the good-reduction quotient is intrinsic, and $M$ is the kernel of the canonical covering map. Therefore every automorphism of the ground extension preserves all three and their exact sequences.

If two semistable models are chosen, their formal completions admit a common refinement over the identity neighborhood. Translation spreads this refinement across $E$. Generic-fiber invariance then gives a unique isomorphism compatible with the maps to $A^{\mathrm{an}}$. Thus the Raynaud extension is independent of blowups, coordinates, and the chosen smooth model.

Descent is effective because the analytic quotient has an ample polarization inherited from $A$. The theta embedding turns its descent datum into projective algebraic descent. Consequently uniformization is available over $K$ with a possibly nonsplit torus; split formulas are merely coordinates after finite extension.

## 9. The Raynaud uniformization theorem

The constructions can now be assembled into an equivalence: semistable abelian varieties give positive Raynaud data, and positive Raynaud data give abelian varieties. Positivity is the condition preventing the analytic quotient from being merely proper without being projective.

### 9.1 Precise statement

A **polarizable Raynaud datum** over $K$ consists of:

- a torus $T/K$ with character lattice $X$ after finite separable splitting;
- an abelian variety $B/K$ with good reduction;
- an analytic extension $0\to T^{\mathrm{an}}\to E\to B^{\mathrm{an}}\to0$ arising from an integral formal semiabelian extension;
- a free abelian group $M$ of rank $\operatorname{rank}T$ and a discrete homomorphism $u:M\to E$ with full tropical image;
- descent data and a symmetric positive period datum inducing an ample line bundle on $E/M$.

Morphisms are compatible maps on $T,E,B$, and $M$. Finite extensions may be used to split the tori, but all data and compatibilities must descend.

**Theorem 9.1 (Raynaud uniformization).** Sending a semistable abelian variety $A/K$ to its Raynaud datum gives an equivalence between:

1. abelian varieties over $K$ with semistable reduction; and
2. polarizable Raynaud data over $K$.

Under the equivalence,

$$
A^{\mathrm{an}}\simeq E/M,\qquad
\dim A=\dim B+\operatorname{rank}T. \tag{9.1}
$$

The equivalence commutes with finite scalar extension, duality, products, and isogenies.

### 9.2 From an abelian variety to uniformizing data

**Proof strategy.** The formal identity neighborhood records good-reduction and toric parts. Properness forces the missing toric translations to close up by a full lattice. An ample algebraic bundle supplies positivity.

Starting from $A$, the formal structure lemma constructs $E$, $B$, and $T$. The local map (8.3) is continued by translations: if $V$ is a formal identity chart and $a\in A(L)$ for a finite complete extension, choose a lift of $a$ after an admissible extension of $V$ and translate the chart. On overlaps, two choices differ by a section of the formal torus; the group law makes the differences a cocycle. Gluing all translates gives $E\to A^{\mathrm{an}}$. Its kernel $M$ and exactness are established in Sections 8.2--8.3, and properness of $A$ proves fullness.

Choose an ample symmetric line bundle $L$ on $A$. Pull it back to $E$. Because $M$ is the kernel of $E\to A^{\mathrm{an}}$, the pullback has canonical $M$-descent data. Pushout by characters and the Poincare biextension decompose this descent datum into a lattice map and a bilinear period pairing. Symmetry of $L$ makes the pairing symmetric. The cocycle identity on triple period overlaps is exactly the biextension identity, so no extra associativity condition is being suppressed.

To prove positivity, restrict $L$ to analytic one-dimensional subquotients generated by nonzero period directions. Its degree is positive because $L$ is ample. The automorphy calculation of Theorem 5.2 identifies that degree with a positive multiple of the diagonal period value. Hence the period form is positive definite. All data are canonical under base change, and a polarization defined over $K$ makes their Galois descent effective.

This proves that every semistable abelian variety produces a polarizable datum. Notice that positivity was derived from ampleness rather than inferred from properness; the distinction closes a common logical gap.

### 9.3 From positive data to an abelian variety

Begin with a polarizable datum. The quotient theorem constructs

$$
Q=E/M
$$

as a smooth proper analytic group. The automorphy and Poincare data descend an ample line bundle $L$ to $Q$. Theta functions for a sufficiently high power embed $Q$ into projective space: locally over the good-reduction base their toric expansions converge by the same quadratic estimate (5.10), while proper coherent descent makes the finite collection global.

Proper algebraization produces a projective variety $A/K$ with $A^{\mathrm{an}}\simeq Q$. The analytic multiplication, inverse, and identity algebraize uniquely. Smoothness and connectedness descend from $Q$, so $A$ is an abelian variety.

It remains to prove semistable reduction. Choose a rational polyhedral decomposition $\Sigma$ of $N_\mathbf R=\operatorname{Hom}(X,\mathbf R)$ which is periodic under the tropical lattice $\ell(M)$. Such a decomposition is obtained by subdividing the translates of one rational parallelotope; only finitely many cells occur modulo $M$. For a cell cut out by inequalities $\langle x_i,n\rangle\ge c_i$, take the corresponding toric formal chart whose generic fiber is the inverse-image polyannulus. Twist this chart over the good-reduction model of $B$ using the extension class $c:X\to\mathcal B^\vee$ and the Poincare bundle. Face inclusions become formal open immersions, so the charts glue to an admissible formal scheme $\mathfrak Q_\Sigma$.

Translation by $M$ sends a chart to the chart indexed by the translated cell. The automorphy cocycle supplies the compatible descent on overlaps. Because $\Sigma/M$ is finite, the quotient is a quasi-compact proper formal scheme; the valuative argument is the same compact-fundamental-domain argument as Theorem 3.2. Its analytic generic fiber is $E/M=Q$. Near the identity cell the smooth locus is precisely the given formal extension of $\mathfrak B$ by $\mathfrak T$. Reduction therefore has semiabelian identity component. Changing $\Sigma$ only performs an admissible formal subdivision, so the conclusion is independent of this choice. The algebraization of the generic fiber is $A$, proving that $A$ has semistable reduction with toric rank $\operatorname{rank}T$.

### 9.4 Uniqueness and functoriality

Suppose two abelian varieties algebraize the same quotient. The analytic identity is a homomorphism between proper analytifications and therefore algebraizes uniquely, proving uniqueness. A compatible morphism of Raynaud data descends to an analytic homomorphism of quotients and then algebraizes. Conversely, a homomorphism $A_1\to A_2$ preserves bounded formal identity neighborhoods. It therefore maps maximal toric parts to maximal toric parts, induces a homomorphism $B_1\to B_2$, lifts uniquely to $E_1\to E_2$, and carries $M_1$ into $M_2$ because periods are kernels.

Compositions agree on the dense analytic covering groups, so the two constructions are inverse on morphisms. Products are componentwise. For an isogeny, all induced maps have finite kernel or finite cokernel in the appropriate sense, and rationally the toric ranks agree. Duality is treated explicitly in Chapter 10.

This proves existence, essential surjectivity, full faithfulness, and the asserted compatibilities in Theorem 9.1. $\square$

## 10. Line bundles and polarizations on Raynaud quotients

In a mixed extension $E$, a character alone no longer describes an automorphy factor: translating a lift can move its image in the good-reduction abelian variety. The Poincare bundle supplies exactly the missing cross-term.

### 10.1 Descent data on the extension

Let $c:X\to B^\vee$ classify $E$. A line bundle on $A^{\mathrm{an}}=E/M$ pulls back to a line bundle $\mathcal L_E$ on $E$ together with isomorphisms

$$
\alpha_m:t_{u(m)}^*\mathcal L_E\xrightarrow{\sim}\mathcal L_E,
\qquad
\alpha_{m+n}=\alpha_m\circ t_{u(m)}^*\alpha_n. \tag{10.1}
$$

Translation along the torus determines a homomorphism

$$
\lambda:M\longrightarrow X. \tag{10.2}
$$

The projection $\bar u:M\to B(K)$ and the classifying map $c$ pull the Poincare bundle back to $M\times X$. A rigidification of this pullback converts (10.1) into a multiplicative pairing

$$
\tau:M\times X\longrightarrow K^\times \tag{10.3}
$$

whose pure torus specialization is $\tau(m,x)=x(u(m))$. The cocycle law states that $\tau$ is a biextension trivialization, not an arbitrary function.

Conversely, a line bundle on $B$, the map (10.2), a compatible Poincare trivialization (10.3), and a quadratic refinement reconstruct $\mathcal L_E$ and its $M$-descent. This is proved by pushing out $E$ one character at a time, applying the universal property of the Poincare bundle, and then using effective coherent descent over the locally finite quotient cover.

### 10.2 The period pairing

The bilinear valuation form attached to $\lambda$ is

$$
q(m,n)=v\bigl(\tau(n,\lambda(m))\bigr). \tag{10.4}
$$

The symmetry condition on the polarization is equivalent to

$$
\tau(n,\lambda(m))=\tau(m,\lambda(n)) \tag{10.5}
$$

after the normalized Poincare identifications. A different rigidification changes $\tau$ by a unit-valued bilinear coboundary, so $q$ is unchanged. Thus the valuation pairing is intrinsic even though its multiplicative lift is not.

The rank of $M$ equals that of $X$, and positivity means $q(m,m)>0$ for $m\ne0$. It follows that $\lambda$ is injective with finite cokernel. The good-reduction component carries an ordinary polarization $\lambda_B:B\to B^\vee$, and compatibility says that $c\circ\lambda$ and $\lambda_B\circ\bar u$ are the two adjoint cross-terms under biduality.

### 10.3 Positivity and principal polarizations

**Theorem 10.1.** A symmetric line-bundle datum on $E/M$ is a polarization if and only if:

1. its abelian component $\lambda_B$ is a polarization of $B$; and
2. its period form $q$ is positive definite.

It is principal if and only if $\lambda_B$ is principal and $\lambda:M\to X$ is an isomorphism.

**Proof.** If the descended bundle is ample, its restriction to the good-reduction abelian part is ample, giving condition 1. Restriction to every period direction gives positive degree and hence condition 2. Conversely, choose a high tensor power. On formal charts above $B$, positivity of $\lambda_B$ gives enough sections in the horizontal directions. Theta sums over $M$ converge because $q$ has quadratic growth, and their leading toric characters separate vertical points and tangents. Products of the two types of sections embed the quotient, proving ampleness.

For principality, the polarization kernel has a filtration by the kernel on $B$, the finite cokernel of $\lambda$, and its Cartier dual. Its rank is

$$
\deg\lambda_A
=\deg\lambda_B\,[X:\lambda(M)]^2. \tag{10.6}
$$

This rank equals one exactly under the two stated conditions. A degree-one polarization is an isomorphism. $\square$

Formula (10.6) is a useful audit check: it specializes to (6.3) when $B=0$ and to the ordinary polarization degree when $T=0$.

### 10.4 Dual uniformization

The dual abelian variety has Raynaud data in which the two lattices exchange roles. If

$$
0\to T\to E\to B\to0,
$$

then the dual extension has abelian part $B^\vee$ and torus with character lattice $M$. Its period lattice is $X$. The Poincare trivialization transposes, so the period pairing is

$$
q^\vee(x,m)=q(m,x)
$$

after identifying the data correctly. Biduality returns the original extension.

For a polarization, the maps $\lambda_B:B\to B^\vee$ and $\lambda:M\to X$ assemble into the uniformized form of $A\to A^\vee$. Symmetry is literal transposition of these maps and the biextension trivialization. This proves compatibility of Raynaud uniformization with duality and explains geometrically why a principal polarization identifies the period and character lattices.

## 11. Reduction type and numerical invariants

Uniformization turns qualitative reduction statements into ranks and exact sequences. This chapter records the consequences needed later, while keeping separate what is true over $K$, what becomes true after finite extension, and what requires a polarization.

### 11.1 Good, semistable, and totally degenerate reduction

Let $A/K$ have semistable Raynaud datum $(T,E,B,M)$. Then:

- $A$ has good reduction if and only if $T=0$, equivalently $M=0$;
- $A$ is totally degenerate if and only if $B=0$;
- the toric rank is

$$
t(A)=\operatorname{rank}T=\operatorname{rank}M; \tag{11.1}
$$

- the abelian rank is $a(A)=\dim B$, and $\dim A=t(A)+a(A)$.

The first equivalence needs proof in both directions. If $A$ has good reduction, its proper abelian model already supplies the bounded formal group, so no unbounded toric direction and no periods occur. Conversely, if $T=0$, then $E=B^{\mathrm{an}}$ is proper. A discrete subgroup of a proper analytic space is finite; since $M$ is free abelian, it is zero. Thus $A^{\mathrm{an}}=B^{\mathrm{an}}$, and uniqueness of algebraization identifies $A$ with the good-reduction abelian variety $B$.

Total degeneration does not mean the special fiber is a proper union of tori. It means the identity component of the smooth model is a torus; compactness of the generic abelian variety still comes from quotienting by $M$.

### 11.2 Toric rank and potential semistability

When an abelian variety acquires semistable reduction after a finite extension $L/K$, its Raynaud datum over $L$ carries an action of the descent group if $L/K$ is Galois. The existence of such an extension is a separate semistable-reduction theorem and is not needed for the equivalence proved here. The integer $t(A_L)$ can change while passing from a nonsemistable field to one where semistability first appears, but once semistable reduction is present it is unchanged by further finite extensions: the identity torus base-changes and remains the maximal affine part.

**Proposition 11.1.** Suppose $A/K$ is semistable. For every finite extension $L/K$,

$$
t(A_L)=t(A),\qquad a(A_L)=a(A). \tag{11.2}
$$

**Proof.** Base change of the Raynaud extension gives a torus $T_L$ of the same rank and a good-reduction abelian variety $B_L$ of the same dimension. The base-changed lattice remains full. By uniqueness of uniformization this is the Raynaud datum of $A_L$. $\square$

The torus can change from nonsplit to split without changing rank. Therefore “split semistable reduction” is stronger than semistable reduction: it asks that the character module have trivial residue Galois action, not merely that its rank be defined.

### 11.3 Torsion away from the residue characteristic

Let $n$ be prime to the residue characteristic. Applying multiplication by $n$ to (8.5) gives a snake-lemma sequence on finite étale sheaves. Since $M$ is torsion-free and $[n]$ is surjective on $E$ after an étale cover,

$$
0\longrightarrow E[n]\longrightarrow A[n]
\longrightarrow M/nM\longrightarrow0. \tag{11.3}
$$

The Raynaud extension itself gives

$$
0\longrightarrow T[n]\longrightarrow E[n]
\longrightarrow B[n]\longrightarrow0. \tag{11.4}
$$

Ranks check the formulas:

$$
|E[n]|=n^{2\dim B+r},
\qquad |M/nM|=n^r,
\qquad |A[n]|=n^{2\dim A}. \tag{11.5}
$$

Indeed $2\dim B+2r=2\dim A$. The quotient $M/nM$ is the new torsion created by taking $n$th roots of periods. It is not a subgroup canonically; (11.3) is generally a nontrivial extension.

For a prime $\ell$ different from the residue characteristic, inverse limits give

$$
0\longrightarrow T_\ell E\longrightarrow T_\ell A
\longrightarrow M\otimes\mathbf Z_\ell\longrightarrow0, \tag{11.6}
$$

and

$$
0\longrightarrow X_*(T)\otimes\mathbf Z_\ell(1)
\longrightarrow T_\ell E\longrightarrow T_\ell B\longrightarrow0. \tag{11.7}
$$

These exact sequences expose two toric pieces, one with a cyclotomic twist and one without. A polarization pairs them through the period form. We do not develop monodromy operators or filtrations here; the exact sequences are the uniformization input from which that later theory begins.

### 11.4 Isogenies and reduction data

Let $f:A_1\to A_2$ be an isogeny between semistable abelian varieties. Functoriality gives maps

$$
T_1\to T_2,\qquad E_1\to E_2,
\qquad B_1\to B_2,\qquad M_1\to M_2. \tag{11.8}
$$

After tensoring character and period lattices with $\mathbf Q$, the toric maps are isomorphisms and $B_1\to B_2$ is an isogeny. Therefore

$$
t(A_1)=t(A_2),\qquad a(A_1)=a(A_2). \tag{11.9}
$$

To prove the rational isomorphism, choose a quasi-inverse $g$ and an integer $d>0$ with $gf=[d]$ and $fg=[d]$. Apply uniformization functorially. On $M_i\otimes\mathbf Q$ and $X_i\otimes\mathbf Q$, multiplication by $d$ is invertible, so the induced maps are inverse up to $d$. The same relation on $B_i$ proves it is an isogeny. No point-counting argument is involved.

An isogeny can alter the integral index of the period lattice and the splitting behavior of the torus. Thus the full Raynaud datum is not an isogeny invariant, while its rational ranks are.

## 12. Semistable Jacobians

Semistable curves provide the most geometric source of Raynaud data. Their dual graph records the torus and period lattice, the normalizations of their components record the good-reduction abelian part, and node thicknesses give the positive period form.

### 12.1 The graph and the normalization

Let $C/K$ be a smooth proper geometrically connected curve with a split semistable model $\mathcal C/R$. Write $C_s$ for its reduced nodal special fiber, let $\nu:\widetilde C_s\to C_s$ be its normalization, and let $\Gamma$ be the dual graph. Its vertices are the irreducible components of $C_s$, and we denote the corresponding smooth normalized components by $\widetilde C_v$. Its edges are nodes. Choose an orientation on each edge. Then

$$
C_1(\Gamma,\mathbf Z)=\bigoplus_e\mathbf Z e,
\qquad
C_0(\Gamma,\mathbf Z)=\bigoplus_v\mathbf Z v,
$$

with boundary $\partial e=t(e)-s(e)$. The cycle lattice is

$$
H_1(\Gamma,\mathbf Z)=\ker(\partial). \tag{12.1}
$$

Changing edge orientations changes signs of basis vectors but not this lattice or the forms below. Its rank is

$$
b_1(\Gamma)=|E|-|V|+1. \tag{12.2}
$$

The genus formula

$$
g(C)=\sum_v g(\widetilde C_v)+b_1(\Gamma) \tag{12.3}
$$

already predicts the uniformization dimensions.

### 12.2 The generalized Jacobian of the special fiber

The identity component of the Picard scheme of the nodal curve fits into

$$
0\longrightarrow T_\Gamma
\longrightarrow\operatorname{Pic}^0(C_s)
\longrightarrow\prod_v\operatorname{Jac}(\widetilde C_v)
\longrightarrow0, \tag{12.4}
$$

where

$$
X^*(T_\Gamma)\simeq H_1(\Gamma,\mathbf Z). \tag{12.5}
$$

**Proof.** A line bundle on $C_s$ is a line bundle on each normalized component together with an identification of the two fibers above every node. Rescaling the bundle on a component changes all adjacent gluing scalars simultaneously. Hence the group of gluing parameters is

$$
(\mathbf G_m)^E/(\mathbf G_m)^V/\mathbf G_m,
$$

where the final diagonal accounts for the common scalar. Applying characters identifies its character group with the kernel of the incidence boundary, namely $H_1(\Gamma,\mathbf Z)$. Forgetting the gluing maps gives the arrow to $\prod_v\operatorname{Pic}^0(C_v)$, and every collection of degree-zero bundles can be glued. This proves exactness. $\square$

Thus the good-reduction abelian part of the Jacobian uniformization is

$$
B=\prod_v\operatorname{Jac}(\widetilde C_v), \tag{12.6}
$$

and the toric rank is $b_1(\Gamma)$. The extension class remembers the pairs of points above each node through Abel--Jacobi differences on the component Jacobians.

### 12.3 The Jacobian period pairing

At a node $e$, the completed local equation has the form

$$
xy=\pi^{\ell_e}u_e,
\qquad u_e\in R^\times,
\qquad \ell_e>0. \tag{12.7}
$$

The integer $\ell_e$ is its thickness. It is the modulus of the corresponding annulus. On the cycle lattice define

$$
q_\Gamma(c,c')=
\sum_e\ell_e c_ec'_e,
\qquad
c=\sum_ec_ee. \tag{12.8}
$$

This form is symmetric and positive definite: if $c\ne0$, at least one $c_e\ne0$, so

$$
q_\Gamma(c,c)=\sum_e\ell_ec_e^2>0. \tag{12.9}
$$

**Theorem 12.1 (uniformization of a semistable Jacobian).** Let $J=\operatorname{Jac}(C)$. Its Raynaud datum has

$$
X^*(T)\simeq M\simeq H_1(\Gamma,\mathbf Z),
\qquad
B\simeq\prod_v\operatorname{Jac}(\widetilde C_v), \tag{12.10}
$$

and under these identifications the valuation of its period pairing is $q_\Gamma$. The map $M\to X^*(T)$ is the identity, so the induced polarization is principal.

**Proof strategy.** The normalization sequence computes the bounded semiabelian part, while the smoothing parameters at nodes compute the periods.

On the special fiber there is an exact sequence of fppf sheaves

$$
1\longrightarrow\mathbf G_m
\longrightarrow\nu_*\mathbf G_m
\longrightarrow\bigoplus_e i_{e,*}\mathbf G_m
\longrightarrow1, \tag{12.11a}
$$

where the last map takes the ratio of the two branch values. Taking cohomology and separating multidegrees gives (12.4). Its torus character sequence is the cellular complex of $\Gamma$, so (12.5) follows without a choice of coordinates. Formal deformation of this Picard sequence through the powers of $\pi$ supplies the Raynaud extension with abelian part (12.6).

To find its kernel, represent a cycle $c=\sum c_ee$ by gluing trivial bundles across the annuli with transition monomials of slopes $c_e$. Going once around the cycle returns the componentwise bundle to itself but changes its analytic gluing constants; this is a period. Every period arises this way because the quotient of gluing cochains by component rescalings has integral cocharacter lattice $H_1(\Gamma,\mathbf Z)$. Thus $M\simeq H_1(\Gamma,\mathbf Z)$.

At the node $e$, use $y=\pi^{\ell_e}u_ex^{-1}$ on the annulus. Pairing transitions of slopes $c_e$ and $c'_e$ contributes the factor $(\pi^{\ell_e}u_e)^{c_ec'_e}$. Its valuation is $\ell_ec_ec'_e$; the unit $u_e$ changes the multiplicative refinement but not the valuation. Multiplying over all nodes gives (12.8).

Finally, the theta polarization specializes on the normalization to the product of the canonical polarizations and on the gluing torus to the evaluation pairing between cycles and characters. It therefore identifies both $M$ and $X^*(T)$ with $H_1(\Gamma,\mathbf Z)$ by the identity. The period form is positive by (12.9), and the abelian component is principally polarized. The principal criterion of Theorem 10.1 proves the claim. $\square$

Blowing up a node subdivides an edge and distributes its thickness among the new edges. Sending a cycle constantly along the subdivided chain preserves (12.8). Hence the lattice and metric pairing are independent of the chosen semistable refinement.

### 12.4 Compact type and total degeneration

The curve $C_s$ is of **compact type** when $\Gamma$ is a tree. Then $H_1(\Gamma,\mathbf Z)=0$, so the Jacobian has toric rank zero and good reduction. Its special fiber is the product of the component Jacobians. The curve itself can still be singular; good reduction of its Jacobian does not imply smooth reduction of the curve.

At the opposite extreme, if every normalized component has genus zero, then $B=0$ and the Jacobian is totally degenerate. Formula (12.3) gives

$$
g(C)=b_1(\Gamma),
$$

and

$$
J^{\mathrm{an}}\simeq
\operatorname{Hom}(H_1(\Gamma,\mathbf Z),\mathbf G_m^{\mathrm{an}})
/H_1(\Gamma,\mathbf Z), \tag{12.11}
$$

with the embedding determined by annular periods. A one-loop graph recovers the Tate model. In the nonsplit case, the geometric graph and component Jacobians carry Galois action; taking equivariant data gives the torus and extension over $K$.

## 13. Descent, base change, and morphisms

Most proofs use split tori and rational periods after a finite extension. Those coordinates are legitimate only because the constructions commute with descent. This chapter makes that mechanism explicit and summarizes the exact hypotheses under which the formulas may be used.

### 13.1 Finite extensions of the ground field

Let $L/K$ be finite. If $A$ is already semistable over $K$, base change gives

$$
(T,E,B,M)_L=(T_L,E_L,B_L,M), \tag{13.1}
$$

where $u:M\to E(K)\subset E(L)$ is unchanged as an abstract homomorphism. Character lattices acquire the restricted Galois action, and valuations scale by the ramification index:

$$
v_L(a)=e(L/K)v_K(a). \tag{13.2}
$$

Thus the period form scales by the positive factor $e(L/K)$ if normalized to integral value groups. Symmetry, nondegeneracy, and positivity are unchanged. If one instead uses $-\log|\cdot|$ with the absolute value extended from $K$, the real period form is literally unchanged.

Formal base change can introduce nonnormal special fibers, so normalization or admissible modification may be required. Generic-fiber invariance ensures that these repairs do not alter $E_L/M$. The good-reduction abelian scheme and polarization base-change in the usual way.

### 13.2 Galois descent of split data

Suppose $L/K$ is finite Galois and splits $T$. The split datum over $L$ carries actions

$$
G\curvearrowright X,qquad G\curvearrowright M,
$$

and semilinear actions on $E_L$ and $B_L$. Compatibility means

$$
\sigma(u(m))=u(\sigma m),
\qquad
q(\sigma m,\sigma n)=q(m,n). \tag{13.3}
$$

The extension class $c:X\to B_L^\vee(L)$ and Poincare trivialization must also be equivariant. These conditions descend $T$, $E$, and the quotient sheaf. Positivity supplies an ample bundle after a tensor power; averaging its algebraic class over $G$ gives a $G$-invariant ample class, and projective descent produces the abelian variety over $K$.

Conversely, data obtained from an abelian variety over $K$ satisfy (13.3) automatically because the torus, bounded abelian quotient, and period kernel are intrinsic. Thus no choice of splitting field enters the resulting uniformization.

### 13.3 Morphisms in uniformizing coordinates

Let $A_i^{\mathrm{an}}=E_i/M_i$. A homomorphism $f:A_1\to A_2$ lifts uniquely to a homomorphism $F:E_1\to E_2$ carrying $M_1$ into $M_2$. Uniqueness follows because two lifts differ by a map from connected $E_1$ to discrete $M_2$, hence by a constant; equality at the identity makes it zero.

The lift induces

$$
f_T:T_1\to T_2,qquad
f_B:B_1\to B_2,qquad
f_M:M_1\to M_2, \tag{13.4}
$$

with compatibility

$$
F\circ u_1=u_2\circ f_M. \tag{13.5}
$$

On characters $f_T$ is recorded contravariantly by $f_T^*:X_2\to X_1$. If polarizations are present, the adjointness condition becomes

$$
q_2(f_Mm,n)=q_1(m,f_M^\dagger n), \tag{13.6}
$$

where the adjoint lattice map is induced through the character maps and the chosen polarizations.

Conversely, compatible maps (13.4)--(13.5) descend to an analytic homomorphism of quotients, which algebraizes uniquely. Therefore uniformizing coordinates lose no morphisms. This full faithfulness is crucial: the Raynaud datum is a structural description of the abelian variety, not merely an invariant attached to it.

### 13.4 A hypothesis ledger

The principal statements can be used safely with the following boundaries visible.

**Analytic quotients.** Discreteness means finite intersection with every quasi-compact analytic domain. A torus quotient is proper exactly when its tropical period image is full. Properness alone is not the asserted projectivity criterion; algebraization uses a positive Riemann form.

**Formal geometry.** The base is a complete DVR when formal semiabelian models and node thicknesses are used. Admissible blowups preserve generic fibers but can change special-fiber components. Statements about toric rank and period forms are invariant under common refinement.

**Raynaud uniformization.** Over $K$ itself the torus may be nonsplit and the lattice may be visible only as a Galois module after finite separable extension. Split coordinate formulas must be descended. Semistable reduction is required over the field in question; potential semistability after an extension does not silently imply semistability before it.

**Polarizations.** Symmetry and nondegeneracy do not imply positivity. A polarization requires positivity on the good-reduction abelian part and positive definiteness of the valuation period form. A polarization homomorphism may descend when a chosen inducing line bundle does not.

**Jacobians.** Formula (12.10) is stated for a split semistable model. In general one applies it geometrically with Galois action. Thicknesses scale under ramified extension, while the associated real metric is preserved after the compatible normalization.

**Torsion.** Sequences (11.3)--(11.7) require the torsion order to be invertible in the residue field. At the residue characteristic, finite group schemes can be nonreduced and those étale sequences are not a substitute for the connected theory.

## 14. The uniformization package

### 14.1 The structural dictionary

The constructions of the book can be read in both directions:

$$
\begin{array}{ccccc}
\text{semistable model}
&\longrightarrow&
0\to T\to E\to B\to0
&\longrightarrow&
A^{\mathrm{an}}=E/M,\\
&&\downarrow&&\downarrow\\
\text{toric special fiber}
&\longrightarrow&
\text{character lattice }X
&\longleftrightarrow&
\text{period lattice }M.
\end{array} \tag{14.1}
$$

The full tropical image of $M$ gives properness. A symmetric multiplicative period pairing gives a line-bundle descent class. Positive definiteness gives ampleness and hence algebraization. The good-reduction part $B$ carries the bounded abelian geometry, while $T$ and $M$ encode degeneration.

For a principally polarized variety, the dictionary sharpens to

$$
B\simeq B^\vee,
\qquad M\simeq X,
\qquad q:M\times M\to\mathbf Z
\text{ symmetric positive definite}. \tag{14.2}
$$

For a semistable Jacobian this is concrete:

$$
B=\prod_v\operatorname{Jac}(\widetilde C_v),
\qquad M=X=H_1(\Gamma,\mathbf Z),
\qquad q(c,c')=\sum_e\ell_ec_ec'_e. \tag{14.3}
$$

These formulas explain at once why compact-type curves have Jacobians with good reduction, why rational-component degenerations give toric uniformization, and why node thicknesses control the polarization in the degenerate directions.

### 14.2 Conclusion

Rigid uniformization replaces a semistable abelian variety by data adapted to its reduction. The analytic covering group is a Raynaud extension of a good-reduction abelian variety by a torus. Its period kernel is a full lattice, whose tropical image closes the unbounded toric directions and makes the quotient proper. Line bundles descend through automorphy factors; their valuations form symmetric bilinear period pairings; positive definiteness produces convergent theta functions, ample bundles, and projective algebraization.

The construction is reversible and canonical. Positive Raynaud data recover an abelian variety, morphisms lift uniquely to the covering groups, duality exchanges character and period lattices, and isogenies preserve the rational reduction ranks. For semistable Jacobians, the abstract pieces become the normalization Jacobians, the first homology of the dual graph, and the edge-length pairing. Uniformization therefore joins formal reduction, analytic annuli, algebraic polarizations, and graph geometry in one exact package—the package required for the later study of component groups and monodromy.
