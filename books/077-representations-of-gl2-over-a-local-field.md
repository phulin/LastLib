# Representations of $\mathrm{GL}_2(K)$

## Contents

1. [The local representation problem](#1-the-local-representation-problem)
   - [Why rank two is the first complete laboratory](#11-why-rank-two-is-the-first-complete-laboratory)
   - [Standing conventions](#12-standing-conventions)
   - [The classification in advance](#13-the-classification-in-advance)
2. [The geometry of $\mathrm{GL}_2(K)$](#2-the-geometry-of-mathrmgl_2k)
   - [The Borel, torus, and unipotent radical](#21-the-borel-torus-and-unipotent-radical)
   - [Compact and congruence subgroups](#22-compact-and-congruence-subgroups)
   - [Iwasawa, Cartan, and Bruhat decompositions](#23-iwasawa-cartan-and-bruhat-decompositions)
   - [Double-coset calculations at the first levels](#24-double-coset-calculations-at-the-first-levels)
   - [The lattice tree behind the formulas](#25-the-lattice-tree-behind-the-formulas)
3. [Characters, conductors, and twists](#3-characters-conductors-and-twists)
   - [Smooth characters of $K^\times$](#31-smooth-characters-of-ktimes)
   - [Additive characters and finite Fourier duality](#32-additive-characters-and-finite-fourier-duality)
   - [Characters of the torus and the center](#33-characters-of-the-torus-and-the-center)
   - [Twisting representations](#34-twisting-representations)
4. [Normalized principal series](#4-normalized-principal-series)
   - [Why normalized induction is the correct coordinate system](#41-why-normalized-induction-is-the-correct-coordinate-system)
   - [Spherical vectors in the induced model](#42-spherical-vectors-in-the-induced-model)
   - [The two-cell filtration](#43-the-two-cell-filtration)
   - [Isomorphism away from exceptional ratios](#44-isomorphism-away-from-exceptional-ratios)
   - [Isomorphism and uniqueness of inducing data](#45-isomorphism-and-uniqueness-of-inducing-data)
5. [The standard intertwining operator](#5-the-standard-intertwining-operator)
   - [The integral and its domain of convergence](#51-the-integral-and-its-domain-of-convergence)
   - [A convergence-free algebraic construction](#52-a-convergence-free-algebraic-construction)
   - [The spherical scalar](#53-the-spherical-scalar)
   - [Reducibility and the kernel-image calculation](#54-reducibility-and-the-kernel-image-calculation)
   - [A shell computation that locates the exceptional powers](#55-a-shell-computation-that-locates-the-exceptional-powers)
6. [Characters and special representations](#6-characters-and-special-representations)
   - [The Steinberg representation](#61-the-steinberg-representation)
   - [A concrete projective-line model](#62-a-concrete-projective-line-model)
   - [Why the Steinberg extension is nonsplit](#63-why-the-steinberg-extension-is-nonsplit)
   - [Matrix coefficients of Steinberg](#64-matrix-coefficients-of-steinberg)
   - [The complete nonsupercuspidal list so far](#65-the-complete-nonsupercuspidal-list-so-far)
7. [Jacquet modules and nonsupercuspidal classification](#7-jacquet-modules-and-nonsupercuspidal-classification)
   - [Why unipotent coinvariants detect induction](#71-why-unipotent-coinvariants-detect-induction)
   - [Jacquet modules of principal series](#72-jacquet-modules-of-principal-series)
   - [Every nonsupercuspidal irreducible is on the list](#73-every-nonsupercuspidal-irreducible-is-on-the-list)
   - [Admissibility of irreducible representations](#74-admissibility-of-irreducible-representations)
8. [Supercuspidal representations](#8-supercuspidal-representations)
   - [Equivalent ways of being cuspidal](#81-equivalent-ways-of-being-cuspidal)
   - [Compact induction from compact-mod-center subgroups](#82-compact-induction-from-compact-mod-center-subgroups)
   - [Depth-zero supercuspidals](#83-depth-zero-supercuspidals)
   - [Tame admissible pairs](#84-tame-admissible-pairs)
   - [Invariants of an admissible pair](#85-invariants-of-an-admissible-pair)
   - [What remains true in the wild case](#86-what-remains-true-in-the-wild-case)
9. [Spherical representations and Satake parameters](#9-spherical-representations-and-satake-parameters)
   - [One-dimensionality of the hyperspecial fixed space](#91-one-dimensionality-of-the-hyperspecial-fixed-space)
   - [The spherical Hecke eigenvalue](#92-the-spherical-hecke-eigenvalue)
   - [The elementary Satake transform](#93-the-elementary-satake-transform)
   - [Frobenius language without ambiguity](#94-frobenius-language-without-ambiguity)
10. [Iwahori fixed vectors](#10-iwahori-fixed-vectors)
    - [The two-dimensional principal-series space](#101-the-two-dimensional-principal-series-space)
    - [The Steinberg line](#102-the-steinberg-line)
    - [From $\mathcal K_0$ to $\mathcal K_1$](#103-from-mathcal-k_0-to-mathcal-k_1)
11. [Whittaker models and genericity](#11-whittaker-models-and-genericity)
    - [Why a Fourier coefficient sees the representation](#111-why-a-fourier-coefficient-sees-the-representation)
    - [Uniqueness and existence](#112-uniqueness-and-existence)
    - [The Whittaker model](#113-the-whittaker-model)
    - [The principal-series Jacquet integral in detail](#114-the-principal-series-jacquet-integral-in-detail)
12. [The Kirillov model](#12-the-kirillov-model)
    - [Restriction to the diagonal](#121-restriction-to-the-diagonal)
    - [The compactly supported core and asymptotic tails](#122-the-compactly-supported-core-and-asymptotic-tails)
    - [The normalized spherical Whittaker function](#123-the-normalized-spherical-whittaker-function)
    - [Ramified newform shapes](#124-ramified-newform-shapes)
    - [A useful support counterexample](#125-a-useful-support-counterexample)
13. [Conductors and the local newvector theorem](#13-conductors-and-the-local-newvector-theorem)
    - [What level should measure](#131-what-level-should-measure)
    - [The Kirillov filtration lemma](#132-the-kirillov-filtration-lemma)
    - [Existence, uniqueness, and oldvector growth](#133-existence-uniqueness-and-oldvector-growth)
    - [Principal-series conductors](#134-principal-series-conductors)
    - [Conductors of special representations](#135-conductors-of-special-representations)
    - [Conductors of constructed supercuspidals](#136-conductors-of-constructed-supercuspidals)
    - [Twisting: exact statements and limits](#137-twisting-exact-statements-and-limits)
14. [Contragredients, pairings, and duality](#14-contragredients-pairings-and-duality)
    - [Smooth duals of the four families](#141-smooth-duals-of-the-four-families)
    - [The invariant principal-series pairing](#142-the-invariant-principal-series-pairing)
15. [Local factors at the unramified boundary](#15-local-factors-at-the-unramified-boundary)
    - [Character and principal-series factors](#151-character-and-principal-series-factors)
    - [Special and supercuspidal factors](#152-special-and-supercuspidal-factors)
16. [Worked examples over $\mathbf Q_p$](#16-worked-examples-over-mathbf-q_p)
    - [Unramified principal series](#161-unramified-principal-series)
    - [The two exceptional orderings](#162-the-two-exceptional-orderings)
    - [Ramified principal series](#163-ramified-principal-series)
    - [Ramified Steinberg twists](#164-ramified-steinberg-twists)
    - [A depth-zero supercuspidal](#165-a-depth-zero-supercuspidal)
    - [A tame ramified dihedral example](#166-a-tame-ramified-dihedral-example)
    - [What changes at $p=2$](#167-what-changes-at-p2)
17. [The classification and invariant dictionary](#17-the-classification-and-invariant-dictionary)
    - [The four families with their invariants](#171-the-four-families-with-their-invariants)
    - [Data needed for local transfer](#172-data-needed-for-local-transfer)
    - [Interface with two-dimensional local Galois types](#173-interface-with-two-dimensional-local-galois-types)
    - [Scope of the classification](#174-scope-of-the-classification)
    - [Why characteristic zero is visible](#175-why-characteristic-zero-is-visible)
18. [Conclusion: one local representation, many visible shadows](#18-conclusion-one-local-representation-many-visible-shadows)

## 1. The local representation problem

### 1.1 Why rank two is the first complete laboratory

Let $K$ be a nonarchimedean local field. The group $\mathrm{GL}_2(K)$ is the first reductive group for which induction, cuspidality, Fourier expansion, congruence level, and noncommutative harmonic analysis all interact. Rank one phenomena already appear in $K^\times$, but there is no unipotent subgroup there and hence no analogue of a Fourier coefficient. In rank two the upper triangular subgroup provides induction from characters, its unipotent radical provides Whittaker coefficients, and the two Bruhat cells make both constructions explicitly calculable.

The aim of this book is to classify the irreducible smooth representations that are built from the Borel, isolate those that are genuinely cuspidal, and attach to every infinite-dimensional irreducible representation the local invariants needed later: central character, contragredient, conductor, newvector, Hecke parameters, and generic model. The theory is local throughout. Representations of a quaternion division group and the correspondence with them belong to the next two books; global automorphic representations belong after that.

The classification has a visible fault line. A representation whose unipotent coinvariants are nonzero is detected by a character of the diagonal torus and comes from principal-series induction. A representation whose unipotent coinvariants vanish is supercuspidal; its matrix coefficients are compact modulo the center and it must be constructed by different means. Much of the book explains why these apparently different criteria agree.

### 1.2 Standing conventions

Write

$$
\mathcal O=\mathcal O_K,\qquad \mathfrak p=(\varpi),\qquad
k=\mathcal O/\mathfrak p,\qquad |k|=q,
$$

and normalize the valuation and absolute value by

$$
v(\varpi)=1,\qquad |x|=q^{-v(x)}.
$$

The coefficient field $E$ has characteristic zero, is algebraically closed and uncountable for classification and scalar Schur statements, and contains a chosen square root $q^{1/2}$. The standard examples are $\mathbf C$ and an algebraic closure of a characteristic-zero local coefficient field. All characters are $E$-valued and smooth unless another coefficient field is explicitly named. Smooth representations are algebraic vector spaces with a left group action. We retain the function convention established in Book 76: induced representations are acted on by right translation,

$$
(\pi(g_0)f)(g)=f(gg_0).
$$

Set

$$
G=\mathrm{GL}_2(K),\qquad Z=\{zI_2:z\in K^\times\},
\qquad \mathcal K=\mathrm{GL}_2(\mathcal O).
$$

We use left Haar measure. On $G$ it is normalized only when needed; on $\mathcal K$ we usually impose $\operatorname{vol}(\mathcal K)=1$. Additive Haar measure $dx$ on $K$ has $\operatorname{vol}(\mathcal O)=1$. The symbol $\nu$ denotes the unramified character $|\cdot|$ of $K^\times$.

There are three normalizations whose separation is essential. Induction is normalized by the positive half-power of the parabolic modulus. Hecke operators may be either raw characteristic functions or divided by $q^{1/2}$. Local factors are written in the variable $X=q^{-s}$ and are not silently identified with a Frobenius polynomial until a reciprocity convention has been specified.

### 1.3 The classification in advance

Every irreducible smooth representation of $G$ is admissible and has a central character. Up to isomorphism it lies in exactly one of the following families:

1. a one-dimensional representation $\mu\circ\det$;
2. an irreducible principal series $I(\chi_1,\chi_2)$ with $\chi_1\chi_2^{-1}\ne\nu^{\pm1}$;
3. a special representation $\operatorname{St}\otimes(\mu\circ\det)$;
4. a supercuspidal representation.

The first three families are the nonsupercuspidal representations. This statement is simple to memorize but not yet explanatory. Why the exceptional ratios are exactly $\nu$ and $\nu^{-1}$, why a one-dimensional representation and a Steinberg representation occur together, and why nothing else can arise from the Borel will be proved rather than assumed. The supercuspidal family is described intrinsically and through the depth-zero and tame compact-induction constructions needed downstream. In residue characteristic two, and for the deepest wild representations more generally, we do not claim a construction-by-construction classification; the invariant theory developed here applies to them nonetheless.

## 2. The geometry of $\mathrm{GL}_2(K)$

### 2.1 The Borel, torus, and unipotent radical

The subgroup that stabilizes the line $Ke_1$ is the upper triangular Borel

$$
B=TN,\qquad
T=\left\{\begin{pmatrix}a&0\\0&d\end{pmatrix}:a,d\in K^\times\right\},
\qquad
N=\left\{n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}:x\in K\right\}.
$$

The diagonal torus records two multiplicative characters; the unipotent radical is a copy of the additive group of $K$. Conjugation is

$$
\begin{pmatrix}a&0\\0&d\end{pmatrix}n(x)
\begin{pmatrix}a&0\\0&d\end{pmatrix}^{-1}=n(ad^{-1}x).
$$

Thus the parabolic modulus is

$$
\delta_B\left(\begin{pmatrix}a&*\\0&d\end{pmatrix}\right)=|a/d|.
$$

This is the inverse of the group modular character of $B$ under our left-Haar convention. It is $\delta_B^{1/2}$, not its inverse, that appears in the covariance law for normalized induction below.

The opposite unipotent is

$$
\bar N=\left\{\bar n(y)=\begin{pmatrix}1&0\\y&1\end{pmatrix}:y\in K\right\},
$$

and the nontrivial Weyl element will be

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

Changing $w$ by a central scalar changes no Bruhat cell, but it can change signs inside Fourier formulas. Fixing it now prevents later ambiguity.

### 2.2 Compact and congruence subgroups

The maximal compact subgroup $\mathcal K$ is the integral stabilizer of the lattice $\mathcal O^2$. It is hyperspecial: reduction gives a surjection

$$
\mathcal K\longrightarrow \mathrm{GL}_2(k)
$$

whose kernel is the principal congruence subgroup

$$
\mathcal K(n)=1+\varpi^nM_2(\mathcal O),\qquad n\ge1.
$$

Level structures adapted to a chosen line use asymmetric congruences. For $n\ge0$ define

$$
\mathcal K_0(\mathfrak p^n)=
\left\{\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathcal K:
c\in\mathfrak p^n\right\},
$$

and

$$
\mathcal K_1(\mathfrak p^n)=
\left\{\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathcal K:
c\in\mathfrak p^n,\ d\equiv1\pmod{\mathfrak p^n}\right\}.
$$

At level zero both are $\mathcal K$. At level one, $\mathcal I=\mathcal K_0(\mathfrak p)$ is the standard Iwahori subgroup, the inverse image of the upper triangular Borel in $\mathrm{GL}_2(k)$. Its pro-unipotent radical is smaller than $\mathcal K_1(\mathfrak p)$; those groups solve different problems and will not be conflated.

The definition of $\mathcal K_1$ singles out the lower-right entry because it is the stabilizer of a primitive row vector modulo $\mathfrak p^n$. It is the subgroup for which a generic representation has a unique vector at its minimal level. By contrast, $\mathcal K_0$ stabilizes a line and is the natural group for Iwahori and Atkin--Lehner phenomena.

### 2.3 Iwasawa, Cartan, and Bruhat decompositions

Three decompositions reveal three different aspects of $G$.

**Proposition 2.1 (Iwasawa decomposition).** One has $G=B\mathcal K$.

**Proof strategy.** Interpret the columns of a matrix as a lattice basis and use an integral change of basis to make one column generate the least-valuation direction.

**Proof.** Let $g\in G$. Its bottom row is a nonzero vector of $K^2$. Multiplying on the right by an element of $\mathcal K$, elementary divisor theory makes that row $(0,d)$. The resulting matrix is upper triangular. Thus $g=bk$. $\square$

Consequently $B\backslash G\cong(B\cap\mathcal K)\backslash\mathcal K$, a compact space naturally identified with $\mathbf P^1(K)$. This compactness is why ordinary and compact induction from $B$ coincide.

**Proposition 2.2 (Cartan decomposition).** There is a disjoint union

$$
G=\coprod_{a\ge b}\mathcal K
\begin{pmatrix}\varpi^a&0\\0&\varpi^b\end{pmatrix}\mathcal K
=\coprod_{m\ge0}Z\mathcal K
\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\mathcal K.
$$

**Proof.** Apply the elementary divisor theorem to the map of lattices defined by $g$. The ordered pair $(a,b)$ is determined by the valuation of the determinant and the index of the largest common scalar lattice, so the double cosets are disjoint. Factoring out $\varpi^bI_2$ yields the second form. $\square$

Cartan decomposition measures distance in the tree of homothety classes of lattices. The integer $m=a-b$ is that distance. It turns compact-support-mod-center questions into boundedness of one nonnegative integer.

**Proposition 2.3 (Bruhat decomposition).** One has

$$
G=B\sqcup BwB.
$$

**Proof.** If the lower-left entry $c$ of $g$ is zero, then $g\in B$. If $c\ne0$, elementary multiplication by upper triangular matrices reduces $g$ to $w$. The two pieces are disjoint because $B$ preserves $Ke_1$ and $w$ does not. $\square$

The closed cell $B$ is a point in $B\backslash G/B$; the open cell $BwB$ is parametrized by $N$. The fact that there are only two cells is the structural reason principal series have length at most two and why their intertwiner can be written as a one-variable integral.

### 2.4 Double-coset calculations at the first levels

The raw spherical Hecke operator is supported on

$$
\mathcal K\begin{pmatrix}\varpi&0\\0&1\end{pmatrix}\mathcal K.
$$

A useful right-coset decomposition is

$$
\mathcal K\begin{pmatrix}\varpi&0\\0&1\end{pmatrix}\mathcal K
=\coprod_{u\in\mathcal O/\mathfrak p}
\begin{pmatrix}\varpi&u\\0&1\end{pmatrix}\mathcal K
\ \sqcup\ 
\begin{pmatrix}1&0\\0&\varpi\end{pmatrix}\mathcal K.
$$

There are $q+1$ cosets, the neighbors of one lattice vertex. This count later checks the Hecke eigenvalue on the trivial representation.

For the Iwahori, $\mathcal Iw\mathcal I$ has $q$ right $\mathcal I$-cosets. If $T_s=\mathbf1_{\mathcal Iw\mathcal I}$ and $\operatorname{vol}(\mathcal I)=1$, direct multiplication of cosets gives

$$
(T_s+1)(T_s-q)=0.
$$

The two eigenvalues $q$ and $-1$ will distinguish the character quotient from the Steinberg constituent.

### 2.5 The lattice tree behind the formulas

The vertices of the Bruhat--Tits tree are homothety classes $[L]$ of rank-two $\mathcal O$-lattices in $K^2$. Two vertices are adjacent if representatives may be chosen with

$$
\varpi L\subsetneq L'\subsetneq L.
$$

The quotient $L/\varpi L$ has $q+1$ lines, so every vertex has $q+1$ neighbors. The group $G$ acts transitively on vertices, the stabilizer of $[\mathcal O^2]$ is $Z\mathcal K$, and the stabilizer of the oriented edge from $[\mathcal O^2]$ toward $[\mathcal Oe_1+\varpi\mathcal Oe_2]$ is $Z\mathcal I$.

This tree translates several later statements into elementary geometry. Cartan distance is the integer $m$ in $\operatorname{diag}(\varpi^m,1)$. A spherical function is radial about a vertex. An Iwahori-fixed vector remembers an oriented edge. The Steinberg representation measures alternating boundary data and therefore assigns the sign eigenvalue $-1$ to reflection across an edge. Supercuspidal coefficients have bounded support in the tree after the center has been divided out.

The tree also warns against a common false inference. Although the quotient graph has one distance coordinate, $G$ itself is not compact modulo $\mathcal K$: scalar powers move in the determinant direction. Compactness modulo the center removes that direction and leaves bounded tree distance, exactly as Cartan decomposition states.

## 3. Characters, conductors, and twists

### 3.1 Smooth characters of $K^\times$

The decomposition

$$
K^\times=\varpi^{\mathbf Z}\times\mathcal O^\times
$$

separates an unbounded discrete direction from a compact direction. A smooth character $\chi:K^\times\to E^\times$ is determined by $\chi(\varpi)$ and a finite-order character on $\mathcal O^\times$ when $E$ has characteristic zero. Smoothness means precisely that $\chi$ is trivial on $1+\mathfrak p^n$ for some $n$.

The **conductor exponent** of $\chi$ is

$$
a(\chi)=\min\{n\ge0:\chi|_{1+\mathfrak p^n}=1\},
$$

where $1+\mathfrak p^0$ is interpreted as $\mathcal O^\times$. Thus $a(\chi)=0$ exactly when $\chi$ is unramified, and a nontrivial tamely ramified character has exponent $1$. The conductor ideal is $\mathfrak p^{a(\chi)}$.

An **unramified character** is trivial on $\mathcal O^\times$. It is determined by one scalar. Writing $z=\chi(\varpi)$, one may denote it by $\chi_z$ with $\chi_z(\varpi^m u)=z^m$ for $u\in\mathcal O^\times$. In particular $\nu^s$ means the unramified character taking $\varpi$ to $q^{-s}$; the notation is formal if $s$ is not naturally an exponent in $E$.

**Example.** Over $\mathbf Q_p$, a character inflated from $(\mathbf Z/p^r\mathbf Z)^\times$ and nontrivial on $1+p^{r-1}\mathbf Z_p$ has conductor exponent $r$. Multiplying it by $|\cdot|^s$ changes its value at $p$ but not its conductor.

**Counterexample.** The formula $a(\chi\chi')=\max(a(\chi),a(\chi'))$ is false when the exponents are equal: $\chi'=\chi^{-1}$ makes the product unramified. Equality does hold when the two conductor exponents are unequal, because the more deeply ramified character cannot be cancelled by the shallower one.

### 3.2 Additive characters and finite Fourier duality

Multiplicative conductors enter induction, while Whittaker theory uses an additive character. If $\psi$ is nontrivial, define its exponent $n(\psi)$ by requiring that its kernel contain $\mathfrak p^{-n(\psi)}$ but not $\mathfrak p^{-n(\psi)-1}$. Our standard choice has $n(\psi)=0$, so it is trivial on $\mathcal O$ and not on $\varpi^{-1}\mathcal O$.

For $a\in K^\times$, the character $\psi_a(x)=\psi(ax)$ has

$$
n(\psi_a)=n(\psi)+v(a).
$$

The sign follows from the kernel: multiplying by $\varpi$ makes the character less sensitive and enlarges its kernel. Additive Haar measure is self-dual for a suitable scaling. With $\operatorname{vol}(\mathcal O)=1$ and $n(\psi)=0$, it is already self-dual.

If $\chi$ has conductor $r>0$, the finite integral

$$
\tau(\chi,\psi)=
\int_{\mathcal O^\times}\chi(u)^{-1}\psi(\varpi^{-r}u)\,du
$$

is nonzero. Indeed finite Fourier transform on the additive quotient $\mathfrak p^{-r}/\mathcal O$ is invertible, and the $\chi$-isotypic unit function is nonzero; unit scaling shows that a nonzero transform value is a scalar multiple of the displayed integral. This Gauss sum converts ramification depth of a multiplicative character into support depth in a Kirillov newvector.

### 3.3 Characters of the torus and the center

A character of $T$ is a pair $(\chi_1,\chi_2)$ acting by

$$
\begin{pmatrix}a&0\\0&d\end{pmatrix}\longmapsto\chi_1(a)\chi_2(d).
$$

The center embeds by $z\mapsto\operatorname{diag}(z,z)$, so the corresponding central character is

$$
\omega=\chi_1\chi_2.
$$

The Weyl element exchanges the two characters. The unordered pair $\{\chi_1,\chi_2\}$ will classify an irreducible principal series, but the ordered pair matters at the reducibility points because it determines which constituent is the subrepresentation and which is the quotient.

A character $\mu$ of $K^\times$ also gives a character of $G$ by $g\mapsto\mu(\det g)$. On the center this becomes $z\mapsto\mu(z^2)=\mu^2(z)$. Thus a determinant twist multiplies a central character by $\mu^2$, not by $\mu$.

### 3.4 Twisting representations

For a representation $\pi$ and a character $\mu$ of $K^\times$, write

$$
\pi\otimes\mu=\pi\otimes(\mu\circ\det).
$$

Then

$$
I(\chi_1,\chi_2)\otimes\mu\cong I(\chi_1\mu,\chi_2\mu),
$$

and $\omega_{\pi\otimes\mu}=\omega_\pi\mu^2$. Unramified twisting preserves all compact-open fixed spaces and hence the conductor. Ramified twisting is more delicate: it can raise a conductor, leave it unchanged, or even lower it by cancellation. Exact family-by-family formulas will replace any false universal maximization rule.

## 4. Normalized principal series

### 4.1 Why normalized induction is the correct coordinate system

Induction from $B$ turns two characters of $K^\times$ into a representation of $G$. Unnormalized induction is categorical, but it places reducibility at the asymmetric ratios $1$ and $\nu^2$ and makes duality formulas awkward. The half-modular correction centers the two roots around zero: reducibility then occurs at the symmetric ratios $\nu^{\pm1}$, and contragredience simply inverts the inducing characters.

For smooth characters $\chi_1,\chi_2$, define

$$
I(\chi_1,\chi_2)=i_B^G(\chi_1\boxtimes\chi_2).
$$

It consists of locally constant functions $f:G\to E$ satisfying

$$
f\left(\begin{pmatrix}a&b\\0&d\end{pmatrix}g\right)
=|a/d|^{1/2}\chi_1(a)\chi_2(d)f(g),
$$

with $G$ acting by $(\pi(g_0)f)(g)=f(gg_0)$. Since $B\backslash G$ is compact, no separate support condition is needed.

If $\operatorname{Ind}_B^G(\rho_1\boxtimes\rho_2)$ denotes unnormalized induction, then explicitly

$$
I(\chi_1,\chi_2)
=\operatorname{Ind}_B^G(\chi_1\nu^{1/2}\boxtimes
\chi_2\nu^{-1/2}).
$$

Consequently the normalized exceptional ratios $\chi_1\chi_2^{-1}=\nu^{\pm1}$ become the unnormalized ratios $\rho_1\rho_2^{-1}=\nu^2$ and $1$. This conversion is the safe way to compare statements written in different conventions.

The central character is $\chi_1\chi_2$. Indeed the modulus is trivial on scalar matrices. Restriction to $\mathcal K$ identifies the representation with the **compact picture**

$$
\{F:\mathcal K\to E:F(tnk)=\chi_1(t_{11})\chi_2(t_{22})F(k)
\text{ for }tn\in B\cap\mathcal K\},
$$

because $|a|=|d|=1$ on $B\cap\mathcal K$. This shows immediately that $I(\chi_1,\chi_2)$ is admissible: invariance under a fixed compact open subgroup reduces the function to finitely many double cosets.

### 4.2 Spherical vectors in the induced model

Suppose $\chi_1$ and $\chi_2$ are unramified. Iwasawa decomposition defines a vector $f^\circ$ by $f^\circ(1)=1$ and

$$
f^\circ(bk)=\delta_B(b)^{1/2}\chi_1(a)\chi_2(d).
$$

It is well defined because the inducing character is trivial on $B\cap\mathcal K$, and it is right $\mathcal K$-invariant. Conversely a $\mathcal K$-fixed function is determined by its value at $1$, so

$$
\dim I(\chi_1,\chi_2)^{\mathcal K}=1.
$$

If either inducing character is ramified, the compact-picture covariance on $B\cap\mathcal K$ prevents a nonzero constant function, and the spherical fixed space is zero. This is an early example of a general principle: fixed vectors turn a representation-theoretic condition into a finite character compatibility test.

### 4.3 The two-cell filtration

Restrict a principal-series function to the open Bruhat cell by

$$
\Phi_f(x)=f(wn(x)).
$$

Functions supported in the open cell correspond, after the covariance law is imposed, to locally constant compactly supported functions of $x\in K$. The quotient by this subspace records the value on the closed cell. Thus Bruhat decomposition gives a two-step filtration as a $B$-representation rather than merely a set-theoretic partition. It is not a filtration by $G$-subrepresentations: the Weyl element moves information between the two cells.

The filtration nevertheless limits the possible $G$-submodules once the action of $w$ is imposed. The rank-one boundary-distribution calculation says that a proper $G$-submodule must give a nonzero dilation-equivariant functional on the open-cell functions whose boundary value is compatible with the closed cell. There are only two such exceptional dilation exponents. This additional calculation, not the number of cells alone, gives the length bound used below. The same mechanism later computes the Jacquet module.

### 4.4 Isomorphism away from exceptional ratios

The Weyl group suggests that $I(\chi_1,\chi_2)$ and $I(\chi_2,\chi_1)$ should usually be isomorphic. They are not canonically identical: the intertwining operator that exchanges them has zeros and poles at exactly the reducibility points. Away from those points it will be an isomorphism. Consequently the unordered pair of inducing characters, rather than their order, classifies irreducible principal series.

The exceptional cases should not be guessed from equality $\chi_1=\chi_2$. In normalized induction $I(\chi,\chi)$ is irreducible. The exceptional ratios are $\chi_1\chi_2^{-1}=\nu$ and $\nu^{-1}$; missing the absolute-value factor is the most common normalization error in this theory.

### 4.5 Isomorphism and uniqueness of inducing data

**Proposition 4.1.** Suppose both principal series are irreducible. Then

$$
I(\chi_1,\chi_2)\cong I(\eta_1,\eta_2)
$$

if and only if

$$
\{\chi_1,\chi_2\}=\{\eta_1,\eta_2\}.
$$

**Proof strategy.** One implication uses the standard intertwiner. For the other, take Jacquet modules: their semisimplifications remember exactly the two ordered torus characters and their Weyl conjugates.

**Proof.** Equality of unordered pairs gives equality or reversal of the ordered pair. Equality is tautological, and reversal is supplied by the invertible regularized intertwiner away from the exceptional ratios. Conversely an isomorphism gives an isomorphism of normalized Jacquet modules. Proposition 7.1 below then identifies the two multisets of torus characters. Restricting the first coordinate recovers the unordered pair of characters of $K^\times$. $\square$

The irreducibility hypothesis matters. At an exceptional point reversing the pair does not identify the two indecomposable principal series: it reverses their nonsplit extension structures. They have the same Jordan--Hölder constituents but different subrepresentations.

## 5. The standard intertwining operator

### 5.1 The integral and its domain of convergence

The open Bruhat cell permits one to average across the opposite root. Formally set

$$
(M(\chi_1,\chi_2)f)(g)=\int_K f(wn(x)g)\,dx.
$$

For a general smooth character this integral need not converge: the integrand is locally constant but need not be compactly supported as $|x|\to\infty$. If the characters are complex-valued, absolute convergence holds in the chamber

$$
|\chi_1\chi_2^{-1}(\varpi)|<1,
$$

with the present choice of $w$ and $|\varpi|=q^{-1}$; an equivalent statement is $\operatorname{Re}(s_1-s_2)>0$ when $\chi_i=\chi_i^0\nu^{s_i}$ and the $\chi_i^0$ are unitary. A change of Weyl representative may insert a harmless central scalar but does not change the chamber.

Change of variables shows that $Mf$ satisfies the covariance law for $I(\chi_2,\chi_1)$, and right translation commutes with the integral. Thus, where it converges,

$$
M(\chi_1,\chi_2):I(\chi_1,\chi_2)\longrightarrow I(\chi_2,\chi_1)
$$

is a $G$-homomorphism.

### 5.2 A convergence-free algebraic construction

For classification, analytic convergence is an unnecessary restriction. Fix the restrictions of $\chi_1$ and $\chi_2$ to $\mathcal O^\times$ and vary only

$$
z=(\chi_1\chi_2^{-1})(\varpi).
$$

In the compact picture every vector is fixed by some principal congruence subgroup. Split $K$ into a compact set and valuation shells $\varpi^{-m}\mathcal O^\times$. On each sufficiently distant shell the covariance law converts the integral into a geometric series in $z$ and $q^{-1}$. Hence every matrix coefficient of $M$ on a fixed finite-dimensional invariant space is a rational function of $z$.

This yields an algebraic continuation: compute the finite compact part as a finite sum and replace the tail by its rational geometric-series expression. The result is a rational family of intertwiners over $E(z)$. At a zero or pole one multiplies by the least power of the local parameter that makes the family regular and then specializes. The resulting nonzero **regularized standard intertwiner** is unique up to scalar.

This construction is convergence-free in the needed sense. It neither integrates a divergent function nor appeals to complex analysis; it uses agreement with the integral in one chamber to identify a rational expression and then specializes algebraically. The possible denominators are exactly the elementary geometric-series factors. It also makes clear why kernels and images can jump only at finitely many values of $z$.

### 5.3 The spherical scalar

When both characters are unramified and $f^\circ(1)=1$, direct shell summation gives

$$
M(\chi_1,\chi_2)f^\circ
=c(\chi_1\chi_2^{-1})f^{\circ,\mathrm{op}},
$$

where, up to the fixed choice of $w$ and Haar measure,

$$
c(\eta)=\frac{1-q^{-1}\eta(\varpi)}{1-\eta(\varpi)}.
$$

The precise scalar is less important for reducibility than its numerator and denominator. Normalizing $M$ by this scalar produces an operator that takes the normalized spherical vector to the normalized spherical vector and whose composition with the opposite operator is the identity away from exceptional parameters.

One must distinguish a pole of the chosen unnormalized integral from reducibility. A scalar normalization may move poles and zeros, but it cannot remove the rank drop of every regularized intertwiner. The intrinsic exceptional values are detected by the existence of a proper subrepresentation, not by the location of a removable scalar singularity.

### 5.4 Reducibility and the kernel-image calculation

**Theorem 5.1 (principal-series reducibility).** The normalized principal series $I(\chi_1,\chi_2)$ is reducible if and only if

$$
\chi_1\chi_2^{-1}=\nu^{\pm1}.
$$

At either exceptional ratio it has length two. Away from them the regularized standard intertwiner is an isomorphism

$$
I(\chi_1,\chi_2)\cong I(\chi_2,\chi_1).
$$

**Proof strategy.** Use the two-cell filtration to show that a proper subrepresentation forces a one-dimensional boundary functional. Its equivariance gives an equation between the two inducing characters. Conversely, at either solution construct the one-dimensional constituent explicitly; the remaining constituent is forced by the two-cell filtration. The rational intertwiner then identifies its kernel and image.

**Proof.** A nonzero proper submodule cannot be supported only on the closed cell, since the closed cell is not $G$-stable. Its intersection with the open-cell subspace is therefore controlled by a translation-invariant distribution on $K$. Up to scalar, the only boundary distributions compatible with translation, the dilation action of $T$, and passage through $w$ are integration and evaluation of the Fourier transform at zero. The same calculation makes the compatible boundary-functional space one-dimensional at either endpoint and zero otherwise, so a principal series has length at most two. Comparing the dilation factor with the normalized covariance law gives

$$
\chi_1\chi_2^{-1}=\nu\quad\text{or}\quad\nu^{-1}.
$$

This is the decisive step: the two powers arise from the Jacobian $|a/d|$ of dilation, while the half-modulus has already contributed $|a/d|^{1/2}$.

For the converse write the characters in terms of a single $\mu$. If

$$
(\chi_1,\chi_2)=(\mu\nu^{-1/2},\mu\nu^{1/2}),
$$

then the covariance multiplier is simply $\mu(ad)$. Hence

$$
f_\mu(g)=\mu(\det g)
$$

spans a $G$-stable line in $I(\mu\nu^{-1/2},\mu\nu^{1/2})$, isomorphic to $\mu\circ\det$. The quotient is irreducible by the first paragraph and the two-cell length bound.

Interchanging the characters gives the opposite extension. The regularized intertwiner

$$
I(\mu\nu^{1/2},\mu\nu^{-1/2})\longrightarrow
I(\mu\nu^{-1/2},\mu\nu^{1/2})
$$

has one-dimensional image $\mu\circ\det$ and irreducible kernel. The reverse regularized operator has the corresponding irreducible image and one-dimensional kernel. Thus each exceptional principal series has exactly two constituents. $\square$

The proof also fixes subrepresentation versus quotient placement. It is worth displaying it separately:

$$
0\longrightarrow \mu\circ\det\longrightarrow
I(\mu\nu^{-1/2},\mu\nu^{1/2})
\longrightarrow \operatorname{St}\otimes\mu\longrightarrow0,
$$

$$
0\longrightarrow \operatorname{St}\otimes\mu\longrightarrow
I(\mu\nu^{1/2},\mu\nu^{-1/2})
\longrightarrow \mu\circ\det\longrightarrow0.
$$

Neither sequence splits. A splitting would put both constituents as subrepresentations, contradicting the one-dimensionality of the relevant intertwining and boundary-functional spaces.

### 5.5 A shell computation that locates the exceptional powers

The reducibility theorem can be checked on an elementary family of vectors. Choose $f$ supported on the open cell so that $x\mapsto f(wn(x))$ is the characteristic function of $\mathcal O$. Translating by $a_m=\operatorname{diag}(\varpi^m,1)$ rescales the additive coordinate by $\varpi^m$. The integral of the translate acquires two factors: $q^{-m}$ from additive measure and

$$
q^{m/2}(\chi_1\chi_2^{-1})(\varpi)^m
$$

from normalized covariance. The opposite Bruhat passage produces the reciprocal family. A linear relation can persist for every $m$ only when the total ratio equals $1$ in one direction, namely when

$$
(\chi_1\chi_2^{-1})(\varpi)=q^{-1}
\quad\text{or}\quad q.
$$

For characters with the same unit restriction these are precisely $\nu$ and $\nu^{-1}$. If the unit restrictions differ, finite Fourier orthogonality makes the boundary functional vanish before any geometric tail appears, so reducibility is impossible. This calculation exhibits both sources of rigidity: unit characters are separated by finite Fourier theory, and unramified parameters are separated by a one-variable geometric progression.

The same shell calculation shows that the composite of the two regularized intertwiners is a nonzero scalar away from the exceptional values. Since each map is nonzero and their composite is invertible, both are isomorphisms. At an exceptional value the scalar vanishes, the rank drops by one constituent, and the kernel-image description in Theorem 5.1 follows.

## 6. Characters and special representations

### 6.1 The Steinberg representation

The **Steinberg representation** is the quotient

$$
\operatorname{St}=
I(\nu^{-1/2},\nu^{1/2})/\mathbf1.
$$

Equivalently it is the unique irreducible subrepresentation of $I(\nu^{1/2},\nu^{-1/2})$. These are equivalent descriptions by the intertwiner, but they place $\operatorname{St}$ on opposite sides of the two exceptional extensions. A **special representation** is a determinant twist

$$
\operatorname{St}\otimes\mu
=\operatorname{St}\otimes(\mu\circ\det).
$$

Its central character is $\mu^2$. The representation is infinite-dimensional and generic, while $\mu\circ\det$ is one-dimensional and nongeneric. Their occurrence in the same reducible principal series reflects two ways of collapsing the open Bruhat cell: constants collapse all directions, while the Steinberg quotient retains the boundary variation.

### 6.2 A concrete projective-line model

Unnormalized induction of the trivial character may be viewed as locally constant functions on $\mathbf P^1(K)$. After translating between normalized and unnormalized induction, the Steinberg representation becomes

$$
\operatorname{St}\cong C^\infty(\mathbf P^1(K),E)/E,
$$

where $E$ denotes the constant functions and $G$ acts by fractional linear transformations. This model makes infinite dimensionality evident: characteristic functions of smaller and smaller compact-open balls give independent classes modulo constants.

It also explains the Iwahori line. The Iwahori has two orbits on $\mathbf P^1(K)$, one reducing to $\infty$ and its complement. Iwahori-fixed functions are therefore two-dimensional before quotienting by constants and one-dimensional afterward.

### 6.3 Why the Steinberg extension is nonsplit

The projective-line model gives a geometric proof of nonsplitting. A splitting of

$$
0\to E\to C^\infty(\mathbf P^1(K),E)\to\operatorname{St}\to0
$$

would give a $G$-equivariant projection from locally constant functions to constants. Such a projection would be a $G$-invariant finitely additive averaging functional on the compact projective line. Restrict it to the $q+1$ residue balls and use transitivity to assign them equal mass. Refine one ball into $q$ smaller balls while an element of $G$ identifies its complement with a ball of another scale. The required equalities are incompatible with a nonzero total mass in characteristic zero. Equivalently, the stabilizer modulus obstructs an invariant measure for the full $G$-action.

Thus Steinberg is not a direct summand of its defining induction. The failure is not caused by an inability to average over the compact space itself; it is caused by the noncompact group changing the quasi-invariant measure by a modulus.

### 6.4 Matrix coefficients of Steinberg

Let $v_{\mathcal I}$ span $\operatorname{St}^{\mathcal I}$ and let $\lambda_{\mathcal I}$ be its dual fixed vector. Along the Cartan ray $a_m=\operatorname{diag}(\varpi^m,1)$, the normalized coefficient is a scalar multiple of $q^{-m}$ up to the central twist. It does not have compact support modulo $Z$, so Steinberg is not supercuspidal, but it decays along the tree. This places special representations between principal-series behavior and supercuspidal compactness.

The distinction matters for local transfer. Steinberg belongs to the discrete-series side because its coefficients are square-integrable modulo the center after a unitary twist, even though they are not compactly supported there. Supercuspidals satisfy the stronger compact-support condition. Square-integrability will be used by the transfer theory; the present book needs only this explicit rank-one observation.

### 6.5 The complete nonsupercuspidal list so far

We have produced one-dimensional representations, irreducible principal series, and special representations. What remains is to prove completeness: any irreducible representation visible to the Borel must occur in this list. The right invariant for visibility is the Jacquet module, because it removes the unipotent direction without discarding the torus action.

## 7. Jacquet modules and nonsupercuspidal classification

### 7.1 Why unipotent coinvariants detect induction

Let $(\pi,V)$ be a smooth representation of $G$. Its unnormalized $N$-coinvariants are

$$
V_N=V/\langle\pi(n)v-v:n\in N,\ v\in V\rangle.
$$

Conjugation makes this a $T$-representation. To match normalized induction define the normalized Jacquet module

$$
r_N(V)=\delta_B^{-1/2}\otimes V_N.
$$

The inverse half-modulus is forced by adjunction. With this normalization, the right-adjoint form of normalized Frobenius reciprocity is

$$
\operatorname{Hom}_G(V,I(\chi_1,\chi_2))
\cong
\operatorname{Hom}_T(r_N(V),\chi_1\boxtimes\chi_2).
$$

This is the ordinary right adjunction for induction after the half-modulus has been moved to the Jacquet module. The other orientation, with a map from an induced representation into $V$, uses the opposite-unipotent Jacquet module. For $\mathrm{GL}_2$ the Weyl element identifies the two orientations after exchanging the diagonal characters, but suppressing that exchange would reverse subrepresentation and quotient statements.

### 7.2 Jacquet modules of principal series

**Proposition 7.1.** The semisimplification of the normalized Jacquet module is

$$
r_N(I(\chi_1,\chi_2))^{\mathrm{ss}}
\cong(\chi_1\boxtimes\chi_2)\oplus
(\chi_2\boxtimes\chi_1).
$$

When the two displayed characters of $T$ are distinct, the module is their direct sum: choose an element of $T$ on which their eigenvalues differ and split the two-step filtration. If $\chi_1=\chi_2$, the two characters coincide and the unsimplified module may carry extension data. Reducibility of the principal series occurs at different parameters and does not change this semisimplified formula.

**Proof strategy.** Apply $N$-coinvariants to the closed-cell/open-cell filtration. The closed cell contributes the original inducing character. On the open cell, conjugation through $w$ exchanges the diagonal entries, and the normalization cancels the dilation Jacobian.

**Proof.** Evaluation at the identity descends to one quotient of the Jacquet module and transforms under $T$ by $\chi_1\boxtimes\chi_2$. On functions supported in $BwB$, integration over the $N$-coordinate kills differences $n(x)f-f$ and gives the second quotient. Since $wtw^{-1}$ interchanges the diagonal entries, it transforms by $\chi_2\boxtimes\chi_1$. The two-cell filtration has no further pieces. $\square$

From the exceptional exact sequences and exactness of normalized Jacquet functors in this rank-one setting one obtains

$$
r_N(\mu\circ\det)=\mu\nu^{-1/2}\boxtimes\mu\nu^{1/2},
$$

and

$$
r_N(\operatorname{St}\otimes\mu)
=\mu\nu^{1/2}\boxtimes\mu\nu^{-1/2}.
$$

The order depends on our choice of upper Borel. Replacing $B$ by the opposite Borel exchanges the entries.

### 7.3 Every nonsupercuspidal irreducible is on the list

Call an irreducible smooth representation **supercuspidal** if $r_N(\pi)=0$. For $G=\mathrm{GL}_2(K)$ there is only one proper parabolic up to conjugacy, so no additional Jacquet modules need be tested.

**Theorem 7.2 (nonsupercuspidal classification).** If $\pi$ is irreducible and $r_N(\pi)\ne0$, then $\pi$ is a one-dimensional representation, an irreducible principal series, or a special representation.

**Proof strategy.** Extract a character quotient from the nonzero Jacquet module, use the right adjunction to embed $\pi$ in a principal series, and then use the complete length calculation of Chapter 5.

**Proof.** A rank-one consequence of Bruhat decomposition is that the Jacquet module of a finitely generated smooth $G$-representation is finitely generated as a smooth $T$-representation. Here $\pi$ is cyclic. Concretely, writing $G=B\sqcup BwB$ shows that, modulo $N$-differences, the images of the closed-cell and open-cell translates of one generator give a finite set of $T$-generators. Hence the nonzero module $r_N(\pi)$ has an irreducible quotient. Smooth irreducible representations of the abelian group $T$ are characters under the standing coefficient hypotheses, so write this quotient as $\chi_1\boxtimes\chi_2$.

The displayed right adjunction now gives a nonzero map

$$
\pi\longrightarrow I(\chi_1,\chi_2).
$$

It is injective because $\pi$ is irreducible. If the principal series is irreducible, the map is an isomorphism. If it is reducible, Theorem 5.1 says its only irreducible subquotients are $\mu\circ\det$ and $\operatorname{St}\otimes\mu$. Thus $\pi$ is on the stated list. Using the opposite adjunction instead gives the equivalent quotient formulation, with the inducing characters exchanged. $\square$

The theorem is not a black-box classification. Its content is divided between two transparent mechanisms: Jacquet adjunction forces induction, and the two Bruhat cells force length at most two with exactly computed exceptional ratios.

### 7.4 Admissibility of irreducible representations

The general language of Book 76 separated irreducibility from admissibility. For $G$ they come together.

**Theorem 7.3.** Every irreducible smooth $E$-representation of $G$ is admissible. Over the standing algebraically closed coefficient field it has a central character.

**Proof strategy.** Nonsupercuspidals are subquotients of admissible principal series. In the cuspidal case, the rank-one finiteness lemma says that an infinite tail in a compact-open fixed space produces a nonzero boundary class, hence a nonzero Jacquet module. The lattice tree makes this lemma a finite double-coset calculation.

**Proof.** First, the smooth Schur argument applies to an irreducible representation of this second-countable group over the standing uncountable algebraically closed field: an irreducible smooth representation is cyclic and hence countably dimensional, so every central operator is scalar. Thus $Z$ acts through a smooth central character.

Principal-series admissibility was proved from finite compact-picture double cosets, and exactness of compact-open invariants passes it to subquotients. Suppose now that $r_N(\pi)=0$. Replace a chosen compact open $C$ by a normal principal congruence subgroup contained in it. A nonzero $C$-fixed vector generates $\pi$, so compact Frobenius reciprocity presents $\pi$ as a quotient of $\mathrm{c\text{-}Ind}_C^G\mathbf1$.

We use the rank-one finiteness lemma. After fixing the central character, grade $C\backslash G/C$ by the distance $m$ of the corresponding lattice vertices. Every fixed ball contains only finitely many double cosets. On the horosphere of distance $m$, average first over

$$
N\cap\mathcal K
\quad\text{and then over}\quad
a_m(N\cap\mathcal K)a_m^{-1},
\qquad
a_m=\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}.
$$

For $m$ deeper than the level of $C$, the first average identifies values on each residue branch and the second compares that common value with the preceding horosphere. The only part not expressed by the preceding horosphere is the stable value along a ray. Changing the ray by an upper-unipotent element changes that stable value by an $N$-difference, so these stable values are exactly the image in $V_N$. Thus, in any quotient $V$ of the compact induction, either the images of all sufficiently distant spheres are generated by a fixed finite ball, or $V_N\ne0$. This is the tree form of the rank-one finiteness lemma.

Apply it to $V=\pi$. The second alternative is excluded by $r_N(\pi)=0$. Hence $\pi^C$ is spanned by the images of finitely many $C$-double cosets in a fixed ball and is finite dimensional. Since the original compact open contains such a $C$, its fixed space is a subspace of $\pi^C$ and is finite dimensional as well. This proves admissibility. $\square$

This theorem closes a logical loop. All cuspidality criteria in Chapter 8 may now be stated for every irreducible smooth representation, not merely for a separately assumed admissible subclass.

## 8. Supercuspidal representations

### 8.1 Equivalent ways of being cuspidal

The vanishing definition is algebraically efficient, but other forms reveal geometry and analysis.

**Theorem 8.1 (cuspidality criteria).** Let $\pi$ be an irreducible admissible representation of $G$ with central character. The following are equivalent:

1. $r_N(\pi)=0$;
2. $\pi$ is not a subquotient of any principal series;
3. every matrix coefficient $g\mapsto\lambda(\pi(g)v)$ is compactly supported modulo $Z$;
4. one nonzero matrix coefficient is compactly supported modulo $Z$.

Such a representation is called supercuspidal.

**Proof strategy.** The equivalence of the first two is Jacquet adjunction. For the support criterion, use Cartan decomposition: failure of compactness modulo $Z$ means that a coefficient remains nonzero along an unbounded sequence $\operatorname{diag}(\varpi^m,1)$. Averaging on sufficiently deep unipotent subgroups turns that persistent tail into a nonzero Jacquet class. Conversely a nonzero Jacquet class creates such a tail.

**Proof.** Theorem 7.2 proves that $r_N(\pi)\ne0$ exactly when $\pi$ is a principal-series subquotient, giving (1)$\Leftrightarrow$(2).

Fix $v$ and $\lambda$ stabilized by compact opens. Cartan decomposition reduces support modulo $Z$ to the integers $m\ge0$. For large $m$, conjugation by $a_m=\operatorname{diag}(\varpi^m,1)$ sends a fixed compact subgroup of $N$ into the stabilizer of $v$. If the Jacquet module is zero, $v$ is a finite sum of differences $n(x)u-u$; averaging the coefficient over a sufficiently large compact piece of $N$ then makes its value at $a_m$ vanish. Hence coefficients have bounded Cartan support.

Conversely, if the image of $v$ in $V_N$ is nonzero, choose a functional on a finite-dimensional stabilized quotient that does not kill it. The same conjugation calculation makes the resulting coefficient constant along an infinite Cartan tail, so it is not compact modulo $Z$. Thus (1)$\Leftrightarrow$(3). Clearly (3) implies (4). If one nonzero compact-mod-center coefficient exists, irreducibility makes translates of its vector and functional span; every coefficient is a finite linear combination of two-sided translates and is therefore compact modulo $Z$. Thus (4) implies (3). $\square$

The admissibility and central-character hypotheses are not decoration. They make the finite averaging and passage from one coefficient to all coefficients legitimate. In arbitrary smooth representations a single compactly supported coefficient need not control unrelated summands.

### 8.2 Compact induction from compact-mod-center subgroups

The support criterion suggests a construction. Let $J\subset G$ be open with $J/Z$ compact, and let $\Lambda$ be a finite-dimensional irreducible smooth representation of $J$ whose restriction to $Z$ is a character. Consider

$$
\pi=\mathrm{c\text{-}Ind}_J^G\Lambda.
$$

Its coefficients are compact modulo $Z$ whenever it is admissible, so irreducibility will make it supercuspidal. The central question is whether elements outside $J$ intertwine $\Lambda$.

For $g\in G$ define

$$
I_g(\Lambda)=
\operatorname{Hom}_{J\cap J^g}(\Lambda,\Lambda^g),
\qquad J^g=g^{-1}Jg.
$$

**Theorem 8.2 (intertwining criterion).** Suppose $J/Z$ is compact, $\Lambda$ is finite dimensional and irreducible, and

$$
I_g(\Lambda)=0\qquad\text{for every }g\notin J.
$$

Then $\mathrm{c\text{-}Ind}_J^G\Lambda$ is irreducible, admissible, and supercuspidal.

**Proof strategy.** Mackey decomposition identifies endomorphisms with the direct sum of the intertwining spaces. The hypothesis leaves only the identity coset. A support-minimization argument upgrades scalar endomorphisms to irreducibility in this compact-induction setting; this extra argument is essential because scalar endomorphisms alone do not imply irreducibility in an arbitrary category.

**Proof.** Mackey theory gives

$$
\operatorname{End}_G(\mathrm{c\text{-}Ind}_J^G\Lambda)
\cong\bigoplus_{JgJ\in J\backslash G/J}I_g(\Lambda).
$$

Only $J$ survives, and Schur's lemma gives $E$. If a nonzero subrepresentation is chosen, take a vector in it with the smallest number of $J$-cosets in its support. Translating and applying a matrix coefficient projector for the compact quotient of a stabilizer isolates one coset unless a second coset intertwines $\Lambda$. The hypothesis excludes that possibility, so the subrepresentation contains a function supported on $J$. Its $G$-translates generate the whole compact induction. Hence the representation is irreducible.

Theorem 7.3 now gives admissibility; compactness of $J/Z$ alone would not have done so before irreducibility was known. A coefficient of two compactly supported inducing functions is supported in a finite union of products of their supports, hence in a compact set modulo $Z$. Theorem 8.1 therefore gives supercuspidality. $\square$

The condition is sufficient, not necessary in this literal form for every inducing datum. A representation may be irreducibly compactly induced from data whose intertwining algebra is nontrivial but acts through a simple module. The clean criterion is exactly what the depth-zero and tame constructions below are designed to satisfy.

### 8.3 Depth-zero supercuspidals

Reduction modulo $\mathfrak p$ supplies the first genuinely cuspidal representations. A supercuspidal has **depth zero** here if it contains a nonzero $\mathcal K(1)$-fixed vector after a suitable conjugation of the hyperspecial subgroup. Let $\sigma$ be an irreducible cuspidal representation of the finite group $\mathrm{GL}_2(k)$. Inflate it to $\mathcal K$. Its central character on $k^\times$ must be extended to a smooth character of $K^\times$; after choosing the scalar by which $\varpi I_2$ acts, one obtains a representation $\Lambda$ of

$$
J=K^\times\mathcal K.
$$

Define

$$
\pi(\sigma,\Lambda)=\mathrm{c\text{-}Ind}_{K^\times\mathcal K}^{G}\Lambda.
$$

**Theorem 8.3.** This compact induction is irreducible and supercuspidal. Every depth-zero supercuspidal representation of $G$ arises in this way.

**Proof strategy.** Cartan decomposition reduces possible intertwiners to $\operatorname{diag}(\varpi^m,1)$. For $m>0$, the intersection of $\mathcal K$ with its conjugate maps modulo $\mathfrak p$ into a proper parabolic subgroup. Intertwining would therefore give a nonzero unipotent coinvariant of the finite cuspidal representation $\sigma$, which is impossible.

**Proof.** Let $g$ intertwine $\Lambda$. After multiplying by $J$ on both sides, Cartan decomposition lets us take $g=a_m=\operatorname{diag}(\varpi^m,1)$ with $m\ge0$. If $m>0$, $\mathcal K\cap\mathcal K^{a_m}$ contains a subgroup whose reduction is the upper unipotent group of $\mathrm{GL}_2(k)$ on one side and whose conjugate acts as the corresponding opposite filtration on the other. A nonzero intertwiner would descend to a nonzero map through the unipotent coinvariants of $\sigma$. Finite-group cuspidality says those coinvariants vanish. Hence $m=0$ and $g\in J$. Theorem 8.2 applies. Conversely, a depth-zero supercuspidal contains vectors fixed by $\mathcal K(1)$; the resulting representation of $\mathrm{GL}_2(k)$ cannot have a parabolic constituent, for that would give a nonzero $N$-Jacquet module upstairs. An irreducible cuspidal summand and compact Frobenius reciprocity recover the displayed induction. $\square$

Finite cuspidal representations of $\mathrm{GL}_2(k)$ may be parametrized by regular characters $\bar\theta:k_2^\times\to E^\times$, where $k_2/k$ is quadratic and regular means $\bar\theta^q\ne\bar\theta$. Inflating a lift $\theta$ to the units of the unramified quadratic extension $L/K$ connects this construction with the admissible-pair language below.

The regularity condition is indispensable. If $\bar\theta^q=\bar\theta$, then $\bar\theta$ factors through the norm $k_2^\times\to k^\times$. The associated finite representation belongs to a principal series rather than being cuspidal, and compact induction from $K^\times\mathcal K$ acquires intertwiners along nonzero Cartan distance. Thus “a character of a quadratic extension” is not by itself cuspidal data; failure of Galois invariance is the essential condition.

### 8.4 Tame admissible pairs

Positive-depth supercuspidals require a character on a nonsplit torus together with enough compact unipotent data to make it irreducible. Let $L/K$ be a quadratic extension with nontrivial automorphism $\tau$. A pair $(L/K,\theta)$ is **admissible** when

- $\theta:L^\times\to E^\times$ does not factor through $N_{L/K}$, equivalently $\theta\ne\theta^\tau$;
- if $\theta|_{1+\mathfrak p_L}$ factors through the norm on principal units, then $L/K$ is unramified.

The second condition excludes ramified data whose positive-depth information has really descended to $K$. Call the pair **minimal** when no twist $\theta(\chi\circ N_{L/K})$ has smaller conductor exponent. Pairs differing by a $K$-isomorphism or Galois conjugacy give the same representation; a norm twist gives the corresponding determinant twist.

Embed $L^\times$ as an elliptic torus in $G$. From the conductor of $\theta/\theta^\tau$ one chooses a hereditary-order filtration $U^m$ and sets

$$
J=L^\times U^m.
$$

The character $\theta$ does not in general extend as a character of $J$. On the finite quotient between two adjacent filtration groups its commutator gives a nondegenerate alternating pairing. The unique irreducible representation with the prescribed central character is a finite Heisenberg representation; extending its torus action gives a finite-dimensional representation $\Lambda_\theta$ of $J$. Then

$$
\pi(L,\theta)=\mathrm{c\text{-}Ind}_J^G\Lambda_\theta.
$$

**Theorem 8.4 (tame construction).** If $L/K$ is tamely ramified or unramified and $(L/K,\theta)$ is admissible, then $\pi(L,\theta)$ is irreducible supercuspidal. Two such representations are isomorphic exactly when their pairs are carried to one another by a $K$-isomorphism of the quadratic extensions, allowing the nontrivial Galois conjugation of $\theta$. A norm twist is not an additional isomorphism relation: it changes the representation by the corresponding determinant twist. Every essentially tame supercuspidal representation of $G$ arises from such a pair.

**Proof strategy.** The alternating commutator pairing makes the Heisenberg representation irreducible. An element of $G$ intertwining it must preserve the associated lattice chain and the embedded torus; admissibility then reduces the normalizer to $L^\times$ and its Galois element, the latter accounting only for $\theta\sim\theta^\tau$. Thus the intertwining is precisely $J$, and Theorem 8.2 applies.

**Proof.** On the finite quotient of adjacent filtration groups, the commutator pairing is nondegenerate after its center is divided out. Induction from a maximal isotropic subgroup therefore gives the unique Heisenberg representation with the prescribed central character. The torus action preserves the pairing and extends this representation to $\Lambda_\theta$.

Suppose $g\in G$ intertwines $\Lambda_\theta$. Comparing the smallest filtration groups on which the defining character is nontrivial forces $g$ to preserve their lattice chain. Comparing the resulting trace-zero characters then forces $g$ to normalize the embedded quadratic algebra $L$. Its normalizer is generated by $L^\times$ and an element inducing $\tau$. The second possibility intertwines $\theta$ with $\theta^\tau$ and is excluded inside one inducing datum by admissibility. Hence the self-intertwining of $\Lambda_\theta$ is exactly $J$, so Theorem 8.2 proves irreducibility and supercuspidality.

If two compact inductions are isomorphic, Mackey theory supplies an element intertwining their inducing representations. The same filtration argument conjugates one embedded quadratic field to the other, and restriction to the torus identifies the characters up to $\tau$. The converse follows by conjugating the inducing data. Finally, an essentially tame positive-depth supercuspidal has a minimal compact type whose first noncentral filtration character has a quadratic field as its centralizer; tameness makes that field separable of the stated kind, and the preceding Heisenberg construction recovers the type. Depth zero was handled in Theorem 8.3. This proves the exhaustion assertion within the essentially tame range. $\square$

The construction is deliberately described at the level needed later: its torus character, central character, contragredient, twists, and conductor are all explicit. A full enumeration of wild simple types, especially in residue characteristic two, requires additional strata and extension choices. We do not claim that enumeration. Nevertheless every wild supercuspidal is generic, has a unique newvector, a conductor, a contragredient, and compact-mod-center coefficients, so the invariant dictionary and the statement of local transfer do not depend on having listed its inducing data.

To make the filtration choice less mysterious, consider the unramified quadratic case. After an integral embedding $\mathcal O_L\subset M_2(\mathcal O)$, put

$$
U^r=1+\varpi^rM_2(\mathcal O).
$$

If $a_L(\theta)=2r+1$ or $2r+2$, the group $J=L^\times U^{r+1}$ contains the depth at which $\theta$ first detects the trace-zero direction. The quotient of $U^r$ by $U^{r+1}$ is an additive matrix space over $k$, and the commutator pairing induced by $\psi\circ\operatorname{tr}_{M_2(K)/K}$ becomes alternating on the relevant trace-zero quotient. Nondegeneracy is the matrix form of $\theta\ne\theta^\tau$.

For a ramified quadratic extension, the lattice chain has period two over $K$ and period one over $L$. The hereditary order consists of endomorphisms preserving that chain. Its radical replaces $\varpi M_2(\mathcal O)$, and successive quotients alternate in size. This alternation is why the conductor formula has coefficient $f(L/K)=1$ and an added different exponent, rather than twice the character conductor as in the unramified case.

At the finite Heisenberg step, let $H$ be the quotient of the chosen filtration group and $Z_H$ its commutator center. A nontrivial character of $Z_H$ determines a unique irreducible representation of $H$ in which $Z_H$ acts by that character. One proves uniqueness by inducing a character of a maximal isotropic subgroup; any two such subgroups give isomorphic inductions because their characters have the same central restriction. This finite argument supplies the representation $\Lambda_\theta$ without an infinite-dimensional analytic construction.

### 8.5 Invariants of an admissible pair

We normalize the extension $\Lambda_\theta$ so that its restriction to the central copy of $K^\times$ is $\theta|_{K^\times}$. Consequently

$$
\omega_{\pi(L,\theta)}=\theta|_{K^\times}.
$$

Some parameterizations insert a tamely ramified rectifying character when comparing $\theta$ with a Weil-group character. That correction belongs to the comparison map, not to the central action just defined. Stating which side carries the correction is essential in later Galois comparisons.

Twisting is transparent:

$$
\pi(L,\theta)\otimes\chi
\cong\pi(L,\theta(\chi\circ N_{L/K})).
$$

Contragredience is equally simple:

$$
\pi(L,\theta)^\vee\cong\pi(L,\theta^{-1}).
$$

These formulas follow already on the compact inducing representation and then from compact induction. They will later match restriction, tensoring, and duality on two-dimensional local parameters.

### 8.6 What remains true in the wild case

Suppose now that the residue characteristic is two, or that the depth is beyond the essentially tame range. The internal construction may require a simple stratum $[\mathfrak A,n,0,\beta]$, a character on a filtration subgroup determined by $\beta$, a Heisenberg extension, and a choice of extension to its normalizer. Different strata can encode the same representation, so listing raw data without an equivalence theorem would not be a classification.

The intrinsic classification statement does not fail. A wild irreducible representation with zero Jacquet module is supercuspidal, and Theorem 8.1 recognizes it without a type. Its compact-mod-center coefficients imply admissibility. The Whittaker argument of Chapter 11 applies without a tame hypothesis. The Kirillov proof of Chapter 13 assigns a finite conductor and a unique newvector. Contragredience and twisting preserve supercuspidality. These results are sufficient to place a wild representation on the discrete-series side and to formulate preservation of central character, conductor, and twists under a later correspondence.

What is not supplied here is an explicit bijection between all wild supercuspidals and equivalence classes of compact inducing data. Any downstream claim requiring the internal type of a wild representation must therefore add that theory; a claim involving only the invariants just listed may use this book directly.

## 9. Spherical representations and Satake parameters

### 9.1 One-dimensionality of the hyperspecial fixed space

A representation is **spherical** if it has a nonzero $\mathcal K$-fixed vector. Among irreducible representations, sphericality is extremely restrictive.

**Theorem 9.1.** If $\pi$ is irreducible and spherical, then $\dim\pi^{\mathcal K}=1$. Moreover $\pi$ is the unique spherical irreducible subquotient of $I(\chi_1,\chi_2)$ for an unordered pair of unramified characters.

**Proof strategy.** The spherical Hecke algebra is commutative and generated by one noncentral double coset together with the central scalar cosets. A simultaneous eigencharacter reconstructs a quotient of an unramified principal series. The calculation of Chapter 5 shows that only one constituent can be spherical at a reducibility point.

**Proof.** An irreducible representation generated by a nonzero $\mathcal K$-fixed vector is a simple module in the spherical block. The Satake transform identifies its Hecke character with evaluation at an unordered pair $(\alpha,\beta)$ of nonzero scalars. Choose unramified $\chi_i$ with $\chi_i(\varpi)=\alpha,\beta$. Compact Frobenius reciprocity gives a nonzero map from the universal spherical module, hence realizes $\pi$ as the spherical constituent of $I(\chi_1,\chi_2)$. The induced representation has a one-dimensional spherical space. Exactness of $\mathcal K$-invariants in characteristic zero shows that the sum of fixed-space dimensions of its constituents is one. Thus precisely one constituent is spherical, with a one-dimensional fixed space. $\square$

At the exceptional pair $(\nu^{-1/2},\nu^{1/2})$, the one-dimensional constituent is spherical and Steinberg is not. In the reversed extension the spherical vector maps to the same one-dimensional quotient. This is an efficient check that reducibility does not create two spherical constituents.

### 9.2 The spherical Hecke eigenvalue

Let

$$
T=\mathbf1_{\mathcal K\operatorname{diag}(\varpi,1)\mathcal K},
\qquad S=\mathbf1_{\mathcal K(\varpi I_2)\mathcal K},
$$

with $\operatorname{vol}(\mathcal K)=1$. Put

$$
\alpha=\chi_1(\varpi),\qquad\beta=\chi_2(\varpi).
$$

Using the $q+1$ cosets of Section 2.4 and the covariance of $f^\circ$, one finds

$$
Tf^\circ=q^{1/2}(\alpha+\beta)f^\circ,
\qquad Sf^\circ=\alpha\beta f^\circ.
$$

For the normalized operator $\mathsf T=q^{-1/2}T$, the eigenvalue is $\alpha+\beta$. The trivial representation occurs at the exceptional pair $\alpha=q^{1/2}$ and $\beta=q^{-1/2}$ in one ordering; the raw eigenvalue is then $q+1$, exactly the number of right cosets. This sanity check fixes both the half-power and the absolute-value direction.

The unordered pair $\{\alpha,\beta\}$ is the pair of **Satake parameters** in our representation-theoretic normalization. Its Hecke polynomial is

$$
P_\pi(X)=(1-\alpha X)(1-\beta X)
=1-(\alpha+\beta)X+\alpha\beta X^2.
$$

### 9.3 The elementary Satake transform

The commutativity used above can be seen without a general structure theorem. For a bi-$\mathcal K$-invariant compactly supported function $h$, define its constant term on the diagonal by

$$
\mathcal S(h)(t)=\delta_B(t)^{1/2}\int_Nh(tn)\,dn.
$$

Cartan decomposition makes the integral a finite sum. Convolution on $G$ becomes multiplication in the Weyl-invariant Laurent-polynomial algebra generated by two diagonal variables. For the raw operator $T$ one obtains

$$
\mathcal S(T)=q^{1/2}(X_1+X_2),
$$

while the central operator $S$ maps to $X_1X_2$. Evaluation at $(\alpha,\beta)$ yields the eigenvalues of Section 9.2.

Why is there a Weyl invariance? The double coset does not remember an ordering of the two elementary divisors. Interchanging the two lattice directions therefore exchanges $X_1$ and $X_2$ without changing the spherical operator. This is the Hecke-algebra explanation for the unordered inducing pair.

The half-modulus in $\mathcal S$ matches the half-modulus in induction. If both are omitted, one obtains a valid unnormalized convention, but the displayed generator becomes $qX_1+X_2$ in an ordered chamber and symmetry is hidden. Mixing one normalized convention with the other gives an incorrect eigenvalue.

### 9.4 Frobenius language without ambiguity

The parameters above are values of characters at the chosen uniformizer. Books 2 and 5 fix the arithmetic reciprocity convention: local reciprocity sends $\varpi$ to **arithmetic Frobenius**. Consequently the corresponding unramified one-dimensional Galois characters have arithmetic-Frobenius eigenvalues $\alpha$ and $\beta$. Their geometric-Frobenius eigenvalues are $\alpha^{-1}$ and $\beta^{-1}$. Under the alternative geometric reciprocity normalization the roles reverse.

Thus the phrase “the Satake parameters are the Frobenius eigenvalues” is incomplete on its own. The invariant representation-theoretic statement is the polynomial $P_\pi(X)$ defined from $\chi_i(\varpi)$. Later comparison theorems must state whether their Galois polynomial uses arithmetic or geometric Frobenius and insert inverses if necessary.

## 10. Iwahori fixed vectors

### 10.1 The two-dimensional principal-series space

Because $B\backslash G/\mathcal I$ has two elements, represented by $1$ and $w$, an unramified principal series has

$$
\dim I(\chi_1,\chi_2)^{\mathcal I}=2.
$$

Choose basis vectors $f_1,f_w$ supported on $B\mathcal I$ and $Bw\mathcal I$, normalized at $1$ and $w$. Convolution with $T_s=\mathbf1_{\mathcal Iw\mathcal I}$ is computed from $q$ cosets. In a basis adapted to the two Bruhat cells its matrix has characteristic polynomial

$$
(X+1)(X-q).
$$

More explicitly, after rescaling $f_w$ to absorb the chosen Weyl representative, the elementary coset calculation reads

$$
T_sf_1=f_w,
\qquad
T_sf_w=qf_1+(q-1)f_w.
$$

Thus the matrix is

$$
\begin{pmatrix}0&q\\1&q-1\end{pmatrix},
$$

which visibly satisfies $T_s^2=(q-1)T_s+q$. A different choice of left rather than right Hecke action transposes the matrix but leaves the relation and the two eigenlines unchanged.

This is the representation-level shadow of the Iwahori-Hecke relation $(T_s+1)(T_s-q)=0$.

The remaining affine generator, represented by a diagonal translation, records $\alpha$ and $\beta$ and exchanges the two chambers. Together the reflection and translation recover the ordered inducing data; after passing to irreducible principal series only the Weyl orbit remains.

### 10.2 The Steinberg line

In the projective-line model, $\mathcal I$ has two orbits. Quotienting the two-dimensional invariant space by constants leaves one line, so

$$
\dim\operatorname{St}^{\mathcal I}=1.
$$

On this line the elementary Iwahori operator acts by

$$
T_s=-1.
$$

The constant line acts by $T_s=q$. Hence the two roots of the quadratic relation have direct geometric meanings: $q$ is the trivial constituent, while $-1$ is the Steinberg constituent. Under an unramified determinant twist, the finite reflection eigenvalue remains $-1$ and the translation eigenvalue is multiplied by the appropriate value of the twist on $\varpi$.

No supercuspidal representation has an Iwahori-fixed vector. Indeed the Iwahori-Hecke module would produce a subquotient of an unramified principal series, contradicting vanishing of the Jacquet module. Thus an irreducible Iwahori-spherical representation is an unramified principal-series constituent or an unramified Steinberg twist.

### 10.3 From $\mathcal K_0$ to $\mathcal K_1$

The quotient

$$
\mathcal K_0(\mathfrak p^n)/\mathcal K_1(\mathfrak p^n)
$$

is detected by the lower-right entry modulo $\mathfrak p^n$. If $v$ is a newvector of central character $\omega$, then in the standard nebentype form it obeys

$$
\pi\left(\begin{pmatrix}a&b\\c&d\end{pmatrix}\right)v
=\omega(d)v
\qquad
\left(\begin{pmatrix}a&b\\c&d\end{pmatrix}\in
\mathcal K_0(\mathfrak p^{a(\pi)})\right),
$$

after choosing the convention compatible with right-translation Whittaker functions. On $\mathcal K_1$, $d\equiv1$ at the conductor level and this becomes literal invariance. The formula also agrees on scalar matrices because $a(\omega)\le a(\pi)$.

The matrix

$$
w_n=\begin{pmatrix}0&1\\-\varpi^n&0\end{pmatrix}
$$

normalizes the level structure up to the central character. Since the newvector line is one-dimensional, $w_n$ acts between the newvector lines of $\pi$ and a naturally conjugate or dual level character by a scalar. This is the local Atkin--Lehner scalar. Its exact normalization depends on $\psi$, Haar measure, and the chosen generator of the newvector line; the existence of the line and its one-dimensionality do not.

At Iwahori level $n=1$ with unramified central character, the Steinberg line is the clearest instance: reflection acts through the sign character of the finite Hecke generator. At higher level the same idea is encoded by the Weyl transform in the Kirillov model.

## 11. Whittaker models and genericity

### 11.1 Why a Fourier coefficient sees the representation

Fix a nontrivial additive character $\psi:K\to E^\times$ of conductor $\mathcal O$: it is trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. A **Whittaker functional** on $\pi$ is a linear map $\lambda:V\to E$ satisfying

$$
\lambda(\pi(n(x))v)=\psi(x)\lambda(v).
$$

The representation is **generic** if such a nonzero functional exists. A functional turns a vector into a function

$$
W_v(g)=\lambda(\pi(g)v),
$$

which satisfies $W_v(n(x)g)=\psi(x)W_v(g)$. Because our representation action is on the left, right translation of functions corresponds to acting on vectors:

$$
W_{\pi(h)v}(g)=W_v(gh).
$$

This handedness will be used repeatedly in the newvector calculation.

### 11.2 Uniqueness and existence

**Theorem 11.1 (multiplicity one).** For every irreducible admissible representation $\pi$ of $G$,

$$
\dim\operatorname{Hom}_N(\pi,\psi)\le1.
$$

Every infinite-dimensional irreducible representation is generic. The one-dimensional representations are precisely the irreducible nongeneric ones.

**Proof strategy.** Uniqueness uses the open Bruhat cell: two Whittaker functionals give two distributions on $N\backslash G$ with the same equivariance, and inversion exchanges the two sides. On the open cell finite-level Fourier uniqueness leaves one scalar; the closed cell cannot support a nontrivial $\psi$-equivariant distribution. Existence is explicit for principal series and Steinberg. For a supercuspidal, a rank-one Fourier lemma says that vanishing of ordinary $N$-coinvariants forces a nonzero twisted $N$-coinvariant.

**Proof.** For uniqueness, pair a putative left $(N,\psi)$-equivariant distribution with its transpose under $g\mapsto wg^{-1}w^{-1}$. Bruhat decomposition reduces the comparison to $BwB$, parametrized by one additive coordinate. Fourier inversion says an additive distribution with prescribed nontrivial character is determined by one value. On the closed cell, the stabilizer contains $N$, on which the prescribed character is nontrivial, so the distribution vanishes. Hence the Hom space has dimension at most one.

For $I(\chi_1,\chi_2)$ the integral

$$
\lambda(f)=\int_K f(wn(x))\psi(-x)\,dx
$$

on compactly supported open-cell vectors is nonzero and extends algebraically to the whole representation. It descends to the Steinberg constituent and vanishes on the one-dimensional constituent.

For completeness, the rank-one Fourier lemma is applied to the twisted coinvariants

$$
V_{N,\psi_a}
=V/\langle\pi(n(x))v-\psi(ax)v:x\in K,\ v\in V\rangle.
$$

Fixing a vector by $n(\mathfrak p^m)$ and enlarging to $n(\mathfrak p^{-r})$ reduces each stage to Fourier decomposition on the finite additive group $\mathfrak p^{-r}/\mathfrak p^m$. The transition maps between stages carry a nontrivial character orbit either to the next nontrivial orbit or to the boundary term represented by ordinary $N$-coinvariants. If every $V_{N,\psi_a}$ with $a\ne0$ vanished, these finite Fourier decompositions would therefore leave a nonzero stable boundary class in $V_N$, unless $N$ acted trivially. In the latter case the normal closure of $N$ and $\bar N$ is $\mathrm{SL}_2(K)$, so an irreducible $\pi$ would be a determinant character. Thus an infinite-dimensional representation with $V_N=0$ has $V_{N,\psi_a}\ne0$ for some $a\ne0$. Conjugation by $\operatorname{diag}(a,1)$ identifies this quotient with $V_{N,\psi}$. A nonzero linear functional on it is a Whittaker functional. This proves existence for supercuspidals without assuming compact-induction data. $\square$

### 11.3 The Whittaker model

For generic irreducible $\pi$, the map $v\mapsto W_v$ is injective: its kernel is a subrepresentation and the functional is nonzero. Its image $\mathcal W(\pi,\psi)$ is the **Whittaker model**. Uniqueness makes this model canonical up to a scalar choice of $\lambda$.

Changing the additive character to $\psi_a(x)=\psi(ax)$ does not change genericity. Indeed conjugation by $\operatorname{diag}(a,1)$ transports one Whittaker model to the other. Conductors defined using a fixed $\psi$ must nevertheless record its conductor if formulas involve Fourier transform; we keep $a(\psi)=0$ throughout.

### 11.4 The principal-series Jacquet integral in detail

Let $f$ be supported in the open cell and suppose $x\mapsto f(wn(x))$ is compactly supported. Then

$$
\lambda(f)=\int_Kf(wn(x))\psi(-x)\,dx
$$

is a finite Fourier integral. For $b\in K$, use $n(x)n(b)=n(x+b)$ and change variables to obtain

$$
\lambda(\pi(n(b))f)=\psi(b)\lambda(f).
$$

Thus the sign in $\psi(-x)$ is forced by our right-translation action. Replacing it by $\psi(x)$ would produce the $\psi^{-1}$-model.

At an exceptional point the integral vanishes on the determinant character. Indeed a Whittaker functional on a one-dimensional representation would have to satisfy $\lambda(v)=\psi(x)\lambda(v)$ for every $x$. It therefore descends to or restricts to the Steinberg constituent according to the ordering. This explicitly proves that Steinberg is generic and the character constituent is not.

For a compactly induced supercuspidal, begin with a matrix coefficient of $\Lambda$ on $J$ and extend it by zero. Fourier projection along a compact quotient of $J\cap N$ produces a nonzero $(N,\psi)$-equivariant functional when the restriction contains the corresponding finite additive character. The intertwining criterion prevents all nontrivial projections from vanishing. Thus the abstract existence proof has a concrete finite-sum realization for every supercuspidal constructed in Chapter 8.

## 12. The Kirillov model

### 12.1 Restriction to the diagonal

The Whittaker function is determined much more efficiently than an arbitrary function on $G$. Define

$$
\phi_v(y)=W_v\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right),
\qquad y\in K^\times.
$$

The resulting space of locally constant functions on $K^\times$ is the **Kirillov model** $\mathcal K(\pi,\psi)$. The action of the mirabolic subgroup is explicit:

$$
(\pi(n(b))\phi)(y)=\psi(by)\phi(y),
$$

$$
\left(\pi\begin{pmatrix}a&0\\0&d\end{pmatrix}\phi\right)(y)
=\omega_\pi(d)\phi(ya/d).
$$

These formulas follow by multiplying matrices on the right inside $W_v(gh)$. They are an immediate check on all inverses and central-character factors.

The Weyl element acts by a Fourier-type transform. Its exact kernel depends on $\pi$, $\psi$, and Haar normalization; conceptually it is the local functional equation. Newvector uniqueness will need only two consequences: the Kirillov model contains $C_c^\infty(K^\times)$, and the quotient by that subspace is controlled by the Jacquet module.

### 12.2 The compactly supported core and asymptotic tails

**Proposition 12.1.** For every infinite-dimensional irreducible generic $\pi$,

$$
C_c^\infty(K^\times)\subseteq\mathcal K(\pi,\psi).
$$

Moreover

$$
\mathcal K(\pi,\psi)/C_c^\infty(K^\times)
$$

is naturally controlled by $r_N(\pi)$. It is zero for supercuspidal $\pi$, has two character-exponential tails for an irreducible principal series, and one tail for a special representation.

**Proof strategy.** Project a vector to a prescribed character of a compact quotient of $N$ by finite Fourier averaging. Diagonal conjugation moves the support to any valuation shell. Summing shells builds all compactly supported functions. What remains at $y\to0$ is unchanged by sufficiently small unipotents and therefore descends to $N$-coinvariants.

For a supercuspidal representation this gives the particularly simple identity

$$
\mathcal K(\pi,\psi)=C_c^\infty(K^\times).
$$

For $I(\chi_1,\chi_2)$, tail functions are linear combinations, outside a compact set, of

$$
y\longmapsto |y|^{1/2}\chi_1(y)
\quad\text{and}\quad
y\longmapsto |y|^{1/2}\chi_2(y),
$$

with a logarithmic valuation factor when the characters coincide in the extension case. For Steinberg only the appropriate single tail survives. This asymptotic description is the bridge from Jacquet classification to conductor theory.

### 12.3 The normalized spherical Whittaker function

Let $\pi=I(\chi_1,\chi_2)$ be unramified and irreducible, normalize $W^\circ(1)=1$, and put $\alpha=\chi_1(\varpi)$, $\beta=\chi_2(\varpi)$. Upper-unipotent invariance implies

$$
W^\circ\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right)=0
\qquad(m<0).
$$

The $q+1$ spherical Hecke cosets give a second-order recurrence. Solving it with $W_{-1}=0$ and $W_0=1$ yields, for $m\ge0$ and $\alpha\ne\beta$,

$$
W_m=q^{-m/2}
\frac{\alpha^{m+1}-\beta^{m+1}}{\alpha-\beta}.
$$

When $\alpha=\beta$, the limiting value is

$$
W_m=q^{-m/2}(m+1)\alpha^m.
$$

This is the concrete meeting point of the Satake and Kirillov pictures. Its generating series is

$$
\sum_{m\ge0}W_mq^{m/2}X^m
=\frac1{(1-\alpha X)(1-\beta X)},
$$

which recovers the Hecke polynomial. The factor $q^{-m/2}$ comes from normalized induction, not from a Frobenius convention.

### 12.4 Ramified newform shapes

If exactly one inducing character, say $\chi_1$, is unramified, the newvector Whittaker function has a single noncompact tail and its diagonal generating series is $(1-\chi_1(\varpi)X)^{-1}$ after the same $q^{m/2}$ rescaling. If both inducing characters are ramified, the newvector Kirillov function is compactly supported in $K^\times$ and the standard local factor is $1$.

For an unramified Steinberg twist, only one of the two exceptional principal-series tails survives. This yields one Euler factor even though the ambient reducible induction has two. For a ramified Steinberg twist the surviving character is ramified and the tail becomes compact. Supercuspidal Kirillov functions are always compactly supported.

The Gauss sum of Section 3.2 locates the first nonzero shell when a multiplicative character is ramified. Finite Fourier orthogonality kills all shallower shells, while nonvanishing at the conductor shell constructs the newvector. This is the computational heart of the conductor formulas rather than merely a prediction from a parameter.

### 12.5 A useful support counterexample

It is tempting to say that every Whittaker function of a supercuspidal is compactly supported on $G$. That is false because the center acts by $\omega_\pi$ and is noncompact. What is true is compact support modulo $ZN$ on the Whittaker quotient, or compact support in $K^\times$ after passage to the Kirillov coordinate. Keeping the quotient visible avoids confusing supercuspidality with literal compact support.

## 13. Conductors and the local newvector theorem

### 13.1 What level should measure

For a character, conductor measures the first unit group on which the character becomes trivial. For a two-dimensional representation of $G$, the correct replacement is the first congruence level at which one distinguished vector appears. Principal congruence invariants are too large and do not choose a direction. The subgroup $\mathcal K_1(\mathfrak p^n)$ remembers a primitive vector modulo $\mathfrak p^n$ and is exactly asymmetric enough to produce multiplicity one.

Let $\pi$ be an infinite-dimensional irreducible smooth representation. Its **conductor exponent** is

$$
a(\pi)=\min\{n\ge0:\pi^{\mathcal K_1(\mathfrak p^n)}\ne0\}.
$$

A nonzero vector at this minimal level is a **newvector**. Vectors at higher levels generated from it are oldvectors. This definition is made for generic infinite-dimensional representations. A ramified one-dimensional character $\mu\circ\det$ has no $\mathcal K_1(\mathfrak p^n)$-fixed vector at any level, because $\operatorname{diag}(u,1)\in\mathcal K_1(\mathfrak p^n)$ for every $u\in\mathcal O^\times$. It would therefore be misleading to assign it a newvector conductor by the same minimum.

If $v$ is fixed by $\mathcal K_1(\mathfrak p^n)$, scalar matrices $uI_2$ with $u\in1+\mathfrak p^n$ fix $v$. Hence

$$
a(\omega_\pi)\le a(\pi).
$$

This necessary compatibility is often useful when a prescribed central character is imposed.

### 13.2 The Kirillov filtration lemma

The newvector theorem rests on a concrete rank-one calculation.

**Lemma 13.1 (Kirillov filtration).** Let $\pi$ be infinite dimensional, irreducible, and generic, and take $a(\psi)=0$. Suppose $\pi^{\mathcal K_1(\mathfrak p^m)}$ is nonzero for at least one $m$, and let $n_0$ be the least such integer. Then

$$
\dim \pi^{\mathcal K_1(\mathfrak p^m)}=
\begin{cases}
0,&m<n_0,\\
m-n_0+1,&m\ge n_0.
\end{cases}
$$

If $v_0$ spans the fixed space at $n_0$, then for $m\ge n_0$ the vectors

$$
v_j=\pi\left(\begin{pmatrix}\varpi^{-j}&0\\0&1\end{pmatrix}\right)v_0,
\qquad 0\le j\le m-n_0,
$$

form a basis of $\pi^{\mathcal K_1(\mathfrak p^m)}$.

**Proof strategy.** Translate invariance under the three elementary pieces of $\mathcal K_1$ into support, unit-invariance, and Fourier-transform conditions on a Kirillov function. These conditions leave an interval of valuation shells. The first nonempty interval defines $n_0$; increasing the level lengthens it by exactly one shell.

**Proof.** Let $\phi$ be the Kirillov function of $v$. Invariance under $n(b)$ for $b\in\mathcal O$ gives

$$
\psi(by)\phi(y)=\phi(y)\quad\text{for all }b\in\mathcal O,
$$

so $\phi(y)=0$ unless $y\in\mathcal O$. Invariance under $\operatorname{diag}(u,1)$ for $u\in\mathcal O^\times$ makes $\phi$ constant, with the appropriate central-character adjustment already trivial here, on each valuation shell $\varpi^r\mathcal O^\times$. Finally the lower-unipotent elements

$$
\bar n(c)=w n(-c)w^{-1},\qquad c\in\mathfrak p^m,
$$

impose the corresponding upper-support bound on the Weyl transform of $\phi$. Fourier duality turns this into a lower bound on the shell index of $\phi$, shifted by a constant depending only on $\pi$ and $\psi$.

Thus the invariant space is represented by functions constant on the integer shells in one interval. For $m<n_0$ the interval is empty by definition. At the first nonempty value $n_0$ the two support bounds meet in one shell, and each increase of $m$ adds one shell. This proves the dimension formula.

It remains to identify the displayed basis. If $a_j=\operatorname{diag}(\varpi^{-j},1)$ and $k\in\mathcal K_1(\mathfrak p^m)$, then

$$
a_j^{-1}ka_j\in\mathcal K_1(\mathfrak p^{n_0})
\quad\text{whenever }0\le j\le m-n_0.
$$

Indeed the upper-right entry gains $j$ powers of $\varpi$, the lower-left loses $j$ but remains in $\mathfrak p^{m-j}\subseteq\mathfrak p^{n_0}$, and the lower-right congruence remains strong enough. Hence each $v_j$ is fixed. Their Kirillov functions begin on distinct valuation shells, so they are linearly independent; the dimension count makes them a basis. $\square$

This proof is genuinely rank two. The one-dimensional valuation line in $K^\times$ makes the interval grow by one. For higher rank, oldform dimensions are governed by a multidimensional cone and require more elaborate combinatorics.

### 13.3 Existence, uniqueness, and oldvector growth

**Theorem 13.2 (local newvector theorem).** Every infinite-dimensional irreducible smooth representation $\pi$ of $G$ has a finite conductor exponent. At the minimal level,

$$
\dim\pi^{\mathcal K_1(\mathfrak p^{a(\pi)})}=1.
$$

For every $m\ge a(\pi)$,

$$
\dim\pi^{\mathcal K_1(\mathfrak p^m)}=m-a(\pi)+1,
$$

and the translates in Lemma 13.1 form an oldvector basis.

**Proof.** By Theorem 11.1, $\pi$ is generic. Proposition 12.1 places a nonzero compactly supported function, for example the characteristic function of one sufficiently small unit coset, in its Kirillov model. Finite averaging over units makes this function invariant under $\operatorname{diag}(\mathcal O^\times,1)$, and its compact support makes it invariant under $n(\mathcal O)$ after a diagonal translate. Smoothness of the Weyl action then makes it invariant under $\bar n(\mathfrak p^m)$ for all sufficiently large $m$. These elementary subgroups generate $\mathcal K_1(\mathfrak p^m)$, with the lower-right congruence absorbed by the central character. Thus the Kirillov filtration is nonempty at a finite level. Lemma 13.1 gives the theorem with $a(\pi)=n_0$. $\square$

The theorem simultaneously proves existence and uniqueness. It also distinguishes $\mathcal K_1$ from $\mathcal K_0$: a representation with central character $\omega$ naturally has vectors transforming under $\mathcal K_0(\mathfrak p^n)$ by a character on the lower-right entry, while literal fixed vectors belong to $\mathcal K_1$. When $a(\omega)>0$, replacing one convention by the other without the character produces a false statement.

### 13.4 Principal-series conductors

**Theorem 13.3.** If $I(\chi_1,\chi_2)$ is irreducible, then

$$
a(I(\chi_1,\chi_2))=a(\chi_1)+a(\chi_2).
$$

**Proof strategy.** In the compact picture, a $\mathcal K_1(\mathfrak p^n)$-fixed function is supported on finitely many double cosets indexed by a valuation parameter. Compatibility on the stabilizer of a coset forces $\chi_1$ and $\chi_2$ to be trivial at complementary depths. The smallest possible sum is their conductor sum, and at equality exactly one coset survives.

**Proof.** Write $r_i=a(\chi_i)$. Representatives for

$$
(B\cap\mathcal K)\backslash\mathcal K/
\mathcal K_1(\mathfrak p^n)
$$

may be chosen so that the intersection of the left stabilizer with the conjugate right stabilizer tests $\chi_1$ on $1+\mathfrak p^j$ and $\chi_2$ on $1+\mathfrak p^{n-j}$ for some $0\le j\le n$. A nonzero value is possible precisely if

$$
j\ge r_1,\qquad n-j\ge r_2.
$$

Such a $j$ exists if and only if $n\ge r_1+r_2$. At equality it is uniquely $j=r_1$, giving a one-dimensional invariant space. At level $n+m$, the allowed integers form an interval of length $m+1$, agreeing with Theorem 13.2. $\square$

This calculation also handles the generic constituent at an exceptional ratio by passage through the exact sequence, but the special formula below is more informative because ramified twists cause the two character conductors to cancel differently from the irreducible principal-series case.

### 13.5 Conductors of special representations

**Theorem 13.4.** For a smooth character $\mu$,

$$
a(\operatorname{St}\otimes\mu)=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
$$

**Proof strategy.** Realize the special representation inside the exceptional principal series. If $\mu$ is unramified, the spherical line belongs to the character constituent and disappears, while the remaining Iwahori line begins at level one. If $\mu$ is ramified, both inducing characters $\mu\nu^{\pm1/2}$ have conductor $a(\mu)$ and the one-dimensional constituent has no $\mathcal K_1$-fixed vectors, so all fixed vectors of the principal series lie in the generic constituent.

**Proof.** In the unramified case Chapter 10 gives an Iwahori-fixed Steinberg line but Chapter 9 shows no $\mathcal K$-fixed line, hence the exponent is one. In the ramified case Theorem 13.3's double-coset calculation applies to the ambient exceptional induction and gives first fixed level $2a(\mu)$. The quotient or subrepresentation $\mu\circ\det$ has no $\mathcal K_1$-fixed vector, so exactness of compact-open invariants places that entire fixed line in $\operatorname{St}\otimes\mu$. $\square$

### 13.6 Conductors of constructed supercuspidals

Depth-zero supercuspidals have

$$
a(\pi)=2.
$$

They have no $\mathcal K_1(\mathfrak p)$-fixed vector because their reduction is cuspidal, while the Kirillov model or the finite cuspidal Whittaker function supplies a unique vector at level two.

For a minimal tame admissible pair $(L/K,\theta)$, let $\mathfrak D_{L/K}\subseteq\mathcal O_L$ be the different and

$$
\Delta(L/K)
=v_K\!\left(N_{L/K}(\mathfrak D_{L/K})\right)
$$

the discriminant exponent. Thus $\Delta(L/K)=f(L/K)v_L(\mathfrak D_{L/K})$. With conductor on $L^\times$ normalized by $1+\mathfrak p_L^n$, one has

$$
a(\pi(L,\theta))=\Delta(L/K)+f(L/K)a_L(\theta).
$$

Thus for an unramified quadratic extension,

$$
a(\pi(L,\theta))=2a_L(\theta),
$$

and for a tamely ramified quadratic extension,

$$
a(\pi(L,\theta))=a_L(\theta)+1.
$$

**Proof strategy.** The compact inducing subgroup is built from a lattice-chain filtration. Intersecting its conjugates with $\mathcal K_1(\mathfrak p^n)$ counts $f(L/K)$ base-field conditions for each $L$-unit depth. The failure of the trace pairing to identify the two dual lattice chains contributes the different exponent. Minimality prevents a norm twist from cancelling the leading character.

**Proof.** Conjugate the embedded torus so that its hereditary order is in standard lattice-chain position. Mackey decomposition for the restriction of $\mathrm{c\text{-}Ind}_J^G\Lambda_\theta$ to $\mathcal K_1(\mathfrak p^n)$ reduces fixed vectors to intersections

$$
J\cap g\mathcal K_1(\mathfrak p^n)g^{-1}.
$$

Along the Cartan representatives, the character on the last nontrivial $L$-unit quotient disappears only after $f(L/K)a_L(\theta)$ base-field steps. Dualizing that quotient by the trace pairing shifts the opposite endpoint by

$$
v_K\!\left(N_{L/K}(\mathfrak D_{L/K})\right)=\Delta(L/K).
$$

Before the sum of these two lengths, every possible double-coset value is killed by a nontrivial stabilizer character. At the sum, one Cartan representative survives, and the Heisenberg uniqueness used in Theorem 8.4 makes its invariant line one dimensional. This proves the displayed formula and agrees with the general newvector theorem. Minimality ensures that the last nontrivial unit character has not disappeared earlier through a norm twist. $\square$

This is the representation-theoretic form of the conductor formula for induction from a quadratic local extension. For depth zero, take $L/K$ unramified and $a_L(\theta)=1$, recovering $2$. For a nonminimal pair one must first minimize under norm twists or simply use the exact twist formula

$$
a(\pi(L,\theta)\otimes\chi)
=\Delta(L/K)+f(L/K)a_L(\theta(\chi\circ N_{L/K}))
$$

whenever the twisted pair remains in the stated admissible normalization.

### 13.7 Twisting: exact statements and limits

Unramified twists preserve conductor. For principal series the exact rule is

$$
a(I(\chi_1,\chi_2)\otimes\mu)
=a(\chi_1\mu)+a(\chi_2\mu).
$$

For special representations Theorem 13.4 applies to the product twist. For admissible-pair supercuspidals the norm-twist formula above is exact. These formulas show why there is no universal expression in terms of only $a(\pi)$ and $a(\mu)$: equal-depth characters may cancel.

There is, however, stable behavior. Once $\mu$ is more deeply ramified than all characters visible in the Kirillov asymptotics of $\pi$, cancellation is impossible and

$$
a(\pi\otimes\mu)=2a(\mu).
$$

At the boundary where $2a(\mu)=a(\pi)$ exceptional cancellation may occur. Any use of a maximum formula must therefore include a minimality or unequal-depth hypothesis.

## 14. Contragredients, pairings, and duality

### 14.1 Smooth duals of the four families

The smooth contragredient reverses the central character:

$$
\omega_{\pi^\vee}=\omega_\pi^{-1}.
$$

For normalized principal series,

$$
I(\chi_1,\chi_2)^\vee
\cong I(\chi_1^{-1},\chi_2^{-1}).
$$

Since an irreducible principal series is unchanged by swapping the two inducing characters, this is equivalently $I(\chi_2^{-1},\chi_1^{-1})$. At reducibility, retaining the displayed order correctly reverses the exact sequences. The other formulas are

$$
(\mu\circ\det)^\vee=\mu^{-1}\circ\det,
$$

$$
(\operatorname{St}\otimes\mu)^\vee
=\operatorname{St}\otimes\mu^{-1},
$$

$$
\pi(L,\theta)^\vee\cong\pi(L,\theta^{-1}).
$$

For an arbitrary supercuspidal, the contragredient is again supercuspidal with the same conductor. Compact-mod-center support is preserved under inversion, and $\mathcal K_1$-fixed spaces dualize at each level.

### 14.2 The invariant principal-series pairing

In the compact picture there is a pairing

$$
\langle f,f'\rangle
=\int_{\mathcal K}f(k)f'(k)\,dk
$$

between $I(\chi_1,\chi_2)$ and $I(\chi_1^{-1},\chi_2^{-1})$. Although $dk$ is only Haar measure on $\mathcal K$, Iwasawa decomposition and the opposite half-modular factors show that the pairing is $G$-invariant. The normalization is exactly what cancels the Radon--Nikodym factor on $B\backslash G$.

The pairing is nondegenerate for all inducing data in the smooth sense: every nonzero smooth vector is detected on some finite compact-open quotient. At an exceptional point it is the annihilators, not the full pairing, that record the extension structure. For example, the annihilator of the character subrepresentation in

$$
I(\mu\nu^{-1/2},\mu\nu^{1/2})
$$

is the Steinberg subrepresentation of the contragredient induction

$$
I(\mu^{-1}\nu^{1/2},\mu^{-1}\nu^{-1/2}).
$$

Thus duality reverses subrepresentation and quotient and gives perfect pairings

$$
\operatorname{St}\otimes\mu\ \times\
\operatorname{St}\otimes\mu^{-1}\longrightarrow E.
$$

Whittaker models have a parallel pairing. With dual additive character $\psi^{-1}$, a regularized integral over $K^\times$

$$
\int_{K^\times}W\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
W'\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)d^\times y
$$

pairs $\mathcal W(\pi,\psi)$ with $\mathcal W(\pi^\vee,\psi^{-1})$. For supercuspidals it is a finite sum over valuation shells; for principal series asymptotic tails require the usual algebraic regularization. Fixed-vector duality then identifies the newvector lines of $\pi$ and $\pi^\vee$.

## 15. Local factors at the unramified boundary

### 15.1 Character and principal-series factors

Only a small amount of local-factor notation is needed downstream. For a character $\chi$ define

$$
L(s,\chi)=
\begin{cases}
(1-\chi(\varpi)q^{-s})^{-1},&a(\chi)=0,\\
1,&a(\chi)>0.
\end{cases}
$$

For an irreducible principal series set

$$
L(s,I(\chi_1,\chi_2))=L(s,\chi_1)L(s,\chi_2).
$$

In the spherical case this is

$$
L(s,\pi)=P_\pi(q^{-s})^{-1}
=\frac1{(1-\alpha q^{-s})(1-\beta q^{-s})}.
$$

This normalization uses the Satake parameters $\chi_i(\varpi)$ from Chapter 9. It is independent of Frobenius vocabulary until a reciprocity convention is chosen.

### 15.2 Special and supercuspidal factors

In the unitary representation normalization adopted by normalized induction,

$$
L(s,\operatorname{St}\otimes\mu)
=L(s+1/2,\mu).
$$

Thus if $\mu$ is unramified the factor is

$$
(1-\mu(\varpi)q^{-s-1/2})^{-1},
$$

and if $\mu$ is ramified it is $1$. An algebraically normalized automorphic representation is often twisted by $\nu^{-1/2}$; that shifts $s$ and removes the visible $1/2$. Many apparent discrepancies in Steinberg Euler factors are only this twist.

For a supercuspidal representation of $\mathrm{GL}_2(K)$, the standard local factor is $1$. The richer information is carried by its conductor, central character, and epsilon factor; the latter will be introduced only when a later transfer theorem needs it. No division-algebra representation is used in defining anything in this chapter.

## 16. Worked examples over $\mathbf Q_p$

### 16.1 Unramified principal series

Let $K=\mathbf Q_p$ and choose unramified characters with

$$
\chi_1(p)=A,\qquad\chi_2(p)=B.
$$

If $A/B\notin\{p,p^{-1}\}$, then $I(\chi_1,\chi_2)$ is irreducible, spherical, and has conductor zero. Its raw spherical Hecke eigenvalue and polynomial are

$$
p^{1/2}(A+B),
\qquad
1-(A+B)X+ABX^2.
$$

The representation depends only on the unordered pair $\{A,B\}$. Equality $A=B$ is not exceptional: $I(\chi,\chi)$ remains irreducible.

### 16.2 The two exceptional orderings

Take $\mu=1$. Since $\nu(p)=p^{-1}$,

$$
I(\nu^{-1/2},\nu^{1/2})
=I(|\cdot|^{-1/2},|\cdot|^{1/2})
$$

contains the trivial representation as a subrepresentation and has Steinberg quotient. Reversing the order gives Steinberg as a subrepresentation and the trivial representation as quotient:

$$
0\to\operatorname{St}\to
I(|\cdot|^{1/2},|\cdot|^{-1/2})\to\mathbf1\to0.
$$

In the first ordering the spherical vector spans the trivial subrepresentation. In the reversed ordering its image spans the trivial quotient; it does not lie in the Steinberg subrepresentation. The Steinberg constituent has no $\mathrm{GL}_2(\mathbf Z_p)$-fixed vector, but it has a one-dimensional $\mathcal K_0(p)$-fixed line on which $T_s$ acts by $-1$. Its conductor exponent is one.

### 16.3 Ramified principal series

Let $\chi$ have conductor exponent $r>0$ and let $\eta$ be unramified. Provided $\chi\eta^{-1}\ne|\cdot|^{\pm1}$, which is automatic because the left side is ramified, the principal series $I(\chi,\eta)$ is irreducible and

$$
a(I(\chi,\eta))=r.
$$

It has no spherical vector. Its newvector is fixed by $\mathcal K_1(p^r)$, and the fixed-space dimensions at higher levels are

$$
\dim I(\chi,\eta)^{\mathcal K_1(p^m)}=m-r+1,
\qquad m\ge r.
$$

If both inducing characters have conductor $r$ but are inverses on $1+p^{r-1}\mathbf Z_p$, their product may have smaller central-character conductor even though the representation conductor remains the sum $2r$. Central conductor therefore does not determine representation conductor.

### 16.4 Ramified Steinberg twists

Let $\mu$ have conductor $r\ge1$. Then

$$
a(\operatorname{St}\otimes\mu)=2r,
\qquad
a(\omega)=a(\mu^2)\le r.
$$

For odd $p$ and a quadratic tame $\mu$, one has $r=1$ but $\mu^2=1$, so the special representation has trivial central character and conductor two. This is a useful counterexample to any attempt to recover level from the central character alone.

### 16.5 A depth-zero supercuspidal

Let $k_2=\mathbf F_{p^2}$ and choose a character

$$
\bar\theta:k_2^\times\to E^\times
$$

with $\bar\theta^p\ne\bar\theta$. It gives a cuspidal representation $\sigma_{\bar\theta}$ of $\mathrm{GL}_2(\mathbf F_p)$. Inflate it to $\mathrm{GL}_2(\mathbf Z_p)$, extend across $\mathbf Q_p^\times$, and compactly induce. The result is irreducible supercuspidal with conductor exponent two. It has no Iwahori-fixed vector, and its Kirillov model is $C_c^\infty(\mathbf Q_p^\times)$.

If $L/\mathbf Q_p$ is the unramified quadratic extension and $\theta$ is the corresponding character of $L^\times$ with $a_L(\theta)=1$, the admissible-pair formula gives

$$
a(\pi(L,\theta))=2a_L(\theta)=2,
$$

in agreement with the finite-group construction.

### 16.6 A tame ramified dihedral example

Assume $p$ is odd and let $L/\mathbf Q_p$ be a ramified quadratic extension. Its different exponent is one and residue degree is one. If $\theta$ is a minimal admissible character of conductor $m$, then

$$
a(\pi(L,\theta))=m+1.
$$

Twisting by $\chi\circ N_{L/K}$ replaces $\theta$ by $\theta(\chi\circ N_{L/K})$. If the two characters have the same depth, cancellation can lower the conductor; if the twist is sufficiently deeper, the result has conductor $2a(\chi)$. This example displays both the exact pair formula and the danger of a naive maximum rule.

### 16.7 What changes at $p=2$

The principal-series, Steinberg, Whittaker, and newvector theorems are unchanged over $\mathbf Q_2$. The reducibility ratios remain $|\cdot|^{\pm1}$, and the depth-zero construction from regular characters of $\mathbf F_4^\times$ still gives conductor-two supercuspidals.

What changes is the reach of the tame quadratic construction. Every ramified quadratic extension of $\mathbf Q_2$ is wildly ramified, so its different exponent need not be one and the simple tame lattice-chain formula $a_L(\theta)+1$ is unavailable. The general induction-shaped expression still suggests

$$
\Delta(L/K)+f(L/K)a_L(\theta),
$$

but constructing the representation and identifying the correct character may require wild type data. This is exactly the scope boundary of Section 8.6, not an exception to the intrinsic classification or newvector theorem.

## 17. The classification and invariant dictionary

### 17.1 The four families with their invariants

For quick downstream use, the irreducible representations and their basic data are:

| family | condition | central character | conductor/newvector | contragredient |
|---|---|---|---|---|
| $\mu\circ\det$ | always irreducible, nongeneric | $\mu^2$ | level $0$ if $\mu$ is unramified; no $\mathcal K_1$-fixed vector if ramified | $\mu^{-1}\circ\det$ |
| $I(\chi_1,\chi_2)$ | $\chi_1\chi_2^{-1}\ne\nu^{\pm1}$ | $\chi_1\chi_2$ | $a(\chi_1)+a(\chi_2)$ | $I(\chi_1^{-1},\chi_2^{-1})$ |
| $\operatorname{St}\otimes\mu$ | generic special | $\mu^2$ | $1$ if $a(\mu)=0$, else $2a(\mu)$ | $\operatorname{St}\otimes\mu^{-1}$ |
| supercuspidal $\pi$ | $r_N(\pi)=0$ | $\omega_\pi$ | unique at $a(\pi)$ | supercuspidal, central character $\omega_\pi^{-1}$ |

For $m\ge a(\pi)$ and every infinite-dimensional row,

$$
\dim\pi^{\mathcal K_1(\mathfrak p^m)}=m-a(\pi)+1.
$$

A representation is spherical precisely when it is the spherical constituent of an unramified principal series; its hyperspecial fixed space is one-dimensional. It is Iwahori-spherical precisely when it is an unramified principal-series constituent or an unramified Steinberg twist. Every infinite-dimensional irreducible representation is generic, and supercuspidality is equivalent to compact support of coefficients modulo the center.

### 17.2 Data needed for local transfer

The discrete-series side of $G$ consists of special representations and supercuspidals. These are the representations that will be eligible for comparison with representations of a quaternion division group. The following data are now defined without reference to that group:

- the central character $\omega_\pi$ on $K^\times$;
- determinant twisting $\pi\mapsto\pi\otimes\chi$;
- the contragredient $\pi^\vee$;
- the conductor exponent $a(\pi)$ and newvector line;
- compact support of coefficients modulo $Z$ for supercuspidals;
- special versus supercuspidal type;
- Satake parameters and a Hecke polynomial in the spherical case;
- tame admissible-pair data $(L/K,\theta)$ where available.

No correspondence has been asserted. In particular, no representation of a division algebra has been constructed or assigned to a $G$-representation here. Book 82 develops that other representation theory, and Book 84 will state and prove the matching.

### 17.3 Interface with two-dimensional local Galois types

The representation families already suggest the later parameter shapes:

$$
\begin{array}{c|c}
\text{representation-theoretic family}&\text{expected two-dimensional local shape}\\ \hline
I(\chi_1,\chi_2)&\text{sum of two characters}\\
\operatorname{St}\otimes\mu&\text{one character with nonzero monodromy}\\
\pi(L,\theta)&\text{induction of a character from a quadratic extension}\\
\text{wild supercuspidal}&\text{irreducible wild parameter}
\end{array}
$$

This table is a comparison target, not a construction of a Galois representation. Its normalizations must later respect three checks. Determinants must match central characters. Artin conductors must match the exponents computed in Chapter 13. At unramified places, the eigenvalues of the declared arithmetic or geometric Frobenius must match either $\alpha,\beta$ or their inverses according to the reciprocity convention of Section 9.4.

The tame admissible-pair conductor formula

$$
\Delta(L/K)+f(L/K)a_L(\theta)
$$

is designed precisely to match induction of local parameters. The depth-zero value two and the ramified-tame value $a_L(\theta)+1$ are decisive normalization tests. Likewise, the special conductor $1$ in the unramified case records nonzero monodromy even though inertia acts through an unramified character.

### 17.4 Scope of the classification

The classification into four families is complete: “supercuspidal” is an intrinsic fourth family. The construction-level classification in this book is intentionally narrower. It completely treats depth zero and the essentially tame quadratic cases needed for downstream examples and transfer invariants. It does not enumerate every wild supercuspidal by simple strata or types, especially in residue characteristic two.

This boundary loses none of the formal data required to formulate local Jacquet--Langlands or local-global compatibility. For every wild supercuspidal, the vanishing Jacquet module, compact-mod-center criterion, central character, twist, contragredient, Whittaker model, conductor, and unique newvector remain available. A later theorem may characterize its transfer by characters and these invariants without first choosing an explicit compact-induction label.

### 17.5 Why characteristic zero is visible

The standing coefficient hypothesis enters at decisive points. Averaging over compact opens is exact because finite quotient orders are invertible. Finite-group representations used at depth zero are semisimple. The Iwahori relation has distinct roots $q$ and $-1$ unless the coefficient characteristic makes them coincide. Smooth contragredient duality and the dimension count for fixed spaces use admissibility together with exact averaging.

If the coefficient field has characteristic $p$, where $p$ is the residue characteristic of $K$, principal series can have additional reducibility and extensions, compact-open invariants are not exact, and supersingular representations appear whose relationship to characteristic-zero supercuspidals is not a literal reduction of this classification. Even in characteristic different from $p$, special coincidences can occur when $q+1$ vanishes in the coefficient field. Those modular theories are substantial subjects of their own.

Thus every classification, conductor, and one-dimensionality theorem in this book is a characteristic-zero statement unless its proof explicitly says otherwise. This is not merely a convenience for square roots of $q$; it is part of the mathematical content.

## 18. Conclusion: one local representation, many visible shadows

The representation theory of $\mathrm{GL}_2(K)$ is governed by two geometries. The projective line has two Bruhat cells, and this makes normalized induction from the Borel almost completely explicit. The lattice tree has one Cartan distance, and this turns support modulo the center, congruence level, and Hecke action into one-dimensional calculations. Their intersection explains the exceptional reducibility ratios $|\cdot|^{\pm1}$ and fixes the exact placement of the character and Steinberg constituents.

The Jacquet module draws the classification boundary. If it is nonzero, adjunction forces the representation into a principal series, whose two-cell filtration leaves only irreducible principal series, characters, and special representations. If it vanishes, matrix coefficients become compact modulo the center. Compact induction from a compact-mod-center subgroup then supplies supercuspidals, with the depth-zero and tame admissible-pair cases concrete enough to calculate all relevant invariants.

Whittaker uniqueness gives every infinite-dimensional irreducible representation a canonical functional model. The Kirillov coordinate reduces that model to functions on $K^\times$; congruence invariance becomes an interval of valuation shells. From that elementary picture come the existence and uniqueness of the newvector, the exact oldvector growth formula, and the conductor calculations for principal, special, and constructed supercuspidal representations.

The final dictionary is therefore coherent rather than merely classificatory. Central character records scalar action, contragredience inverts it, twisting changes both inducing characters together, the conductor identifies minimal integral level, and the spherical Hecke polynomial records the two unramified parameters with its Frobenius convention left explicit. These are exactly the stable shadows through which later local transfer, global automorphic representations, and two-dimensional Galois representations will recognize the same local object.
