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
   - [The selected nonsupercuspidal list so far](#65-the-selected-nonsupercuspidal-list-so-far)
7. [Jacquet modules and Borel-generated classification](#7-jacquet-modules-and-borel-generated-classification)
   - [Why unipotent coinvariants detect induction](#71-why-unipotent-coinvariants-detect-induction)
   - [Jacquet modules of principal series](#72-jacquet-modules-of-principal-series)
   - [Every Borel-generated irreducible is on the list](#73-every-borel-generated-irreducible-is-on-the-list)
   - [Admissibility in the selected range](#74-admissibility-in-the-selected-range)
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
15. [Local factors from Whittaker models](#15-local-factors-from-whittaker-models)
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
    - [The selected families with their invariants](#171-the-selected-families-with-their-invariants)
    - [Data needed for local transfer](#172-data-needed-for-local-transfer)
    - [Interface with two-dimensional local Galois types](#173-interface-with-two-dimensional-local-galois-types)
    - [Scope of the classification](#174-scope-of-the-classification)
    - [Why characteristic zero is visible](#175-why-characteristic-zero-is-visible)
18. [Representation-side synthesis](#18-representation-side-synthesis)
19. [Weil--Deligne parameters in dimension two](#19-weil--deligne-parameters-in-dimension-two)
    - [Why a representation needs a second language](#191-why-a-representation-needs-a-second-language)
    - [The definition and the monodromy relation](#192-the-definition-and-the-monodromy-relation)
    - [Determinants, duals, and twists](#193-determinants-duals-and-twists)
    - [Conductors and Euler factors](#194-conductors-and-euler-factors)
20. [The selected local Langlands correspondence](#20-the-selected-local-langlands-correspondence)
    - [The matching problem and the reducibility wall](#201-the-matching-problem-and-the-reducibility-wall)
    - [Rectified quadratic induction](#202-rectified-quadratic-induction)
    - [Bijectivity in the selected range](#203-bijectivity-in-the-selected-range)
    - [Central characters, twists, and contragredients](#204-central-characters-twists-and-contragredients)
21. [Conductors and local constants under the correspondence](#21-conductors-and-local-constants-under-the-correspondence)
    - [Two conductor definitions become one](#211-two-conductor-definitions-become-one)
    - [Rank-one Fourier constants](#212-rank-one-fourier-constants)
    - [Epsilon factors of parameters](#213-epsilon-factors-of-parameters)
    - [Principal and special functional equations](#214-principal-and-special-functional-equations)
    - [Quadratic induction and the lambda factor](#215-quadratic-induction-and-the-lambda-factor)
22. [Base change to a finite extension](#22-base-change-to-a-finite-extension)
    - [Restriction is the organizing principle](#221-restriction-is-the-organizing-principle)
    - [Principal, character, and special base change](#222-principal-character-and-special-base-change)
    - [Mackey theory for a quadratic parameter](#223-mackey-theory-for-a-quadratic-parameter)
    - [What base change preserves and what it transforms](#224-what-base-change-preserves-and-what-it-transforms)
23. [Jacquet--Langlands and the preserved invariant package](#23-jacquet--langlands-and-the-preserved-invariant-package)
    - [Quaternion structure and matching tori](#231-quaternion-structure-and-matching-tori)
    - [Selected division-side types](#232-selected-division-side-types)
    - [The split--division character calculation](#233-the-split--division-character-calculation)
    - [The selected Jacquet--Langlands correspondence](#234-the-selected-jacquet--langlands-correspondence)
    - [Conductors, local factors, and levels](#235-conductors-local-factors-and-levels)
    - [What is preserved, transformed, or not comparable](#236-what-is-preserved-transformed-or-not-comparable)
24. [Worked parameter calculations and final synthesis](#24-worked-parameter-calculations-and-final-synthesis)
    - [An unramified principal series](#241-an-unramified-principal-series)
    - [The two objects at the reducibility wall](#242-the-two-objects-at-the-reducibility-wall)
    - [An unramified quadratic dihedral representation](#243-an-unramified-quadratic-dihedral-representation)
    - [A tamely ramified quadratic example](#244-a-tamely-ramified-quadratic-example)
    - [The complete reusable dictionary](#245-the-complete-reusable-dictionary)
    - [Conclusion](#246-conclusion)

## 1. The local representation problem

### 1.1 Why rank two is the first complete laboratory

Let $K$ be a nonarchimedean local field. The group $\mathrm{GL}_2(K)$ is the first reductive group for which induction, cuspidality, Fourier expansion, congruence level, and noncommutative harmonic analysis all interact. Rank one phenomena already appear in $K^\times$, but there is no unipotent subgroup there and hence no analogue of a Fourier coefficient. In rank two the upper triangular subgroup provides induction from characters, its unipotent radical provides Whittaker coefficients, and the two Bruhat cells make both constructions explicitly calculable.

The aim of this book is to classify the irreducible smooth representations needed in the selected local theory: those built from the Borel, the special representations on the reducibility wall, and the depth-zero and tame dihedral supercuspidals built from quadratic tori. We attach central characters, contragredients, conductors, newvectors, Hecke parameters, Whittaker models, Weil--Deligne parameters, and local constants. Primitive wild supercuspidals are outside the selected classification: the book neither constructs them nor imports their type, genericity, or newvector theory. The final chapters prove compatibility with finite base change and construct Jacquet--Langlands, including its division-side character and local-factor comparisons, in exactly this selected range.

The selected classification has a visible fault line. A representation whose Jacquet module has a character quotient is detected by the diagonal torus and comes from principal-series induction. The constructed quadratic types have zero unipotent coinvariants, compact-mod-center coefficients, and must be built by different means. Much of the book explains why these criteria separate the selected families.

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

The selected irreducible representations treated in this book lie in exactly one of the following families:

1. a one-dimensional representation $\mu\circ\det$;
2. an irreducible principal series $I(\chi_1,\chi_2)$ with $\chi_1\chi_2^{-1}\ne\nu^{\pm1}$;
3. a special representation $\operatorname{St}\otimes(\mu\circ\det)$;
4. a depth-zero or tame dihedral supercuspidal representation $\pi(L,\theta)$.

The first three families are generated from the Borel. This statement is simple to memorize but not yet explanatory. Why the exceptional ratios are exactly $\nu$ and $\nu^{-1}$, why a one-dimensional representation and a Steinberg representation occur together, and why nothing else can arise once the Jacquet module has a character quotient will be proved rather than assumed. The selected supercuspidal family is constructed from depth-zero and tame quadratic types. Primitive wild representations, including the additional ramified quadratic constructions required in residue characteristic two, remain outside every theorem that needs an explicit type, genericity, a conductor, or a parameter.

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

This tree translates several later statements into elementary geometry. Cartan distance is the integer $m$ in $\operatorname{diag}(\varpi^m,1)$. A spherical function is radial about a vertex. An Iwahori-fixed vector remembers an oriented edge. The Steinberg representation measures alternating boundary data and therefore assigns the sign eigenvalue $-1$ to reflection across an edge. Coefficients of the selected compactly induced supercuspidals have bounded support in the tree after the center has been divided out.

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

### 6.5 The selected nonsupercuspidal list so far

We have produced one-dimensional representations, irreducible principal series, and special representations. What remains is to prove completeness: any irreducible representation visible to the Borel must occur in this list. The right invariant for visibility is the Jacquet module, because it removes the unipotent direction without discarding the torus action.

## 7. Jacquet modules and Borel-generated classification

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

### 7.3 Every Borel-generated irreducible is on the list

Call an irreducible smooth representation **supercuspidal** if $r_N(\pi)=0$. For $G=\mathrm{GL}_2(K)$ there is only one proper parabolic up to conjugacy, so no additional Jacquet modules need be tested.

**Theorem 7.2 (Borel-generated classification).** Let $\pi$ be irreducible. If $r_N(\pi)$ has a character quotient, then $\pi$ is a one-dimensional representation, an irreducible principal series, or a special representation.

**Proof strategy.** Use the stated character quotient and right adjunction to embed $\pi$ in a principal series, and then use the complete length calculation of Chapter 5.

**Proof.** Write the character quotient as $\chi_1\boxtimes\chi_2$. The displayed right adjunction gives a nonzero map

$$
\pi\longrightarrow I(\chi_1,\chi_2).
$$

It is injective because $\pi$ is irreducible. If the principal series is irreducible, the map is an isomorphism. If it is reducible, Theorem 5.1 says its only irreducible subquotients are $\mu\circ\det$ and $\operatorname{St}\otimes\mu$. Thus $\pi$ is on the stated list. Using the opposite adjunction instead gives the equivalent quotient formulation, with the inducing characters exchanged. $\square$

The character-quotient hypothesis is essential. Bruhat decomposition computes the Jacquet module of a principal series, but it does not by itself prove that the Jacquet module of an arbitrary cyclic smooth representation is finitely generated over $T$. Book 78 deliberately leaves that stronger assertion outside its rank-one proof. Thus the theorem classifies exactly the Borel-generated spectrum established by the dependency chain, without silently promoting a conditional result to a classification of primitive wild representations.

### 7.4 Admissibility in the selected range

The general language of Book 76 separated irreducibility from admissibility. In the selected range each construction supplies the missing finiteness, but the proof is different for induction and compact induction.

**Theorem 7.3.** Every irreducible principal series, determinant character, special representation, depth-zero supercuspidal, and tame dihedral supercuspidal constructed in this book is admissible and has a central character.

**Proof strategy.** Principal series are admissible by the compact picture, and exactness of compact-open invariants passes admissibility to their constituents. For a compact induction, Mackey decomposition identifies a fixed space with a direct sum indexed by inducing double cosets; the type calculations in Chapter 8 show that only finitely many summands survive at each level.

**Proof.** Principal-series admissibility was proved from the finite compact-picture double-coset set, and exactness of compact-open invariants passes it to the determinant and special constituents. Their displayed construction also gives their central characters.

For a selected supercuspidal $\pi=\mathrm{c\text{-}Ind}_J^G\Lambda$, let $C$ be compact open. Mackey decomposition gives

$$
\pi^C\cong
\bigoplus_{JgC\in J\backslash G/C}
\operatorname{Hom}_{J\cap gCg^{-1}}(\Lambda,\mathbf1).
\tag{7.1}
$$

The depth-zero calculation of Section 8.3 and the lattice-chain calculation of Section 8.4 prove that the summand vanishes once the Cartan distance of $JgC$ is sufficiently large. A bounded Cartan ball contains only finitely many double cosets, and every surviving Hom space is finite dimensional because $\Lambda$ is. Hence (7.1) is finite dimensional. The scalar action specified in the inducing datum supplies the central character. $\square$

Nothing here asserts admissibility for a primitive wild representation whose type has not been constructed. That general theorem is true in the full representation theory of reductive $p$-adic groups, but it is neither an output of Book 76 nor proved by the two-cell calculation in Book 78, so it is not used below.

## 8. Supercuspidal representations

### 8.1 Equivalent ways of being cuspidal

The vanishing definition is algebraically efficient, but other forms reveal geometry and analysis.

**Theorem 8.1 (cuspidality criteria in the selected range).** Let $\pi$ be a selected infinite-dimensional irreducible admissible representation of $G$ with central character. The following are equivalent:

1. $r_N(\pi)=0$;
2. $\pi$ is not a subquotient of any principal series;
3. every matrix coefficient $g\mapsto\lambda(\pi(g)v)$ is compactly supported modulo $Z$;
4. one nonzero matrix coefficient is compactly supported modulo $Z$.

Such a representation is called supercuspidal.

**Proof strategy.** The equivalence of the first two is Jacquet adjunction. For the support criterion, use Cartan decomposition: failure of compactness modulo $Z$ means that a coefficient remains nonzero along an unbounded sequence $\operatorname{diag}(\varpi^m,1)$. Averaging on sufficiently deep unipotent subgroups turns that persistent tail into a nonzero Jacquet class. Conversely a nonzero Jacquet class creates such a tail.

**Proof.** For the selected Borel-generated representations, Proposition 7.1 and the exceptional exact sequences give a nonzero Jacquet module. The compact-support calculation for the selected compact inductions gives zero Jacquet module. This proves (1)$\Leftrightarrow$(2) within the stated range.

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

**Theorem 8.2 (compact-induction criterion).** Suppose $J/Z$ is compact, $\Lambda$ is finite dimensional and irreducible,

$$
I_g(\Lambda)=0\qquad\text{for every }g\notin J,
$$

every nonzero $G$-subrepresentation of $\mathrm{c\text{-}Ind}_J^G\Lambda$ contains a nonzero function supported on the identity coset $J$, and, for every compact open $C\subseteq G$, only finitely many double cosets $JgC$ satisfy

$$
\operatorname{Hom}_{J\cap gCg^{-1}}(\Lambda,\mathbf1)\ne0.
\tag{8.1}
$$

Then $\mathrm{c\text{-}Ind}_J^G\Lambda$ is irreducible, admissible, and supercuspidal.

**Proof strategy.** Mackey decomposition identifies endomorphisms with the direct sum of the intertwining spaces. The first hypothesis computes the endomorphism algebra, the support-reduction hypothesis proves irreducibility, and the separate condition (8.1) makes every compact-open fixed space a finite direct sum. These are logically different conclusions and require different hypotheses.

**Proof.** Mackey theory gives

$$
\operatorname{End}_G(\mathrm{c\text{-}Ind}_J^G\Lambda)
\cong\bigoplus_{JgJ\in J\backslash G/J}I_g(\Lambda).
$$

Only $J$ survives, and Schur's lemma gives $E$. Let $V$ be a nonzero subrepresentation. By support reduction, $V$ contains a nonzero function supported on $J$. Such functions form one copy of the irreducible $J$-representation $\Lambda$, so the $J$-span of that function contains the whole identity-coset copy. Its $G$-translates generate the compact induction, and hence $V$ is the whole representation.

For a compact open $C$, Mackey decomposition gives the fixed-space formula (7.1). Condition (8.1) leaves finitely many summands, each finite dimensional, and therefore proves admissibility. A coefficient of two compactly supported inducing functions is supported in a finite union of products of their supports, hence in a compact set modulo $Z$. The support implication in Theorem 8.1 therefore gives supercuspidality. $\square$

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

**Proof.** Let $g$ intertwine $\Lambda$. After multiplying by $J$ on both sides, Cartan decomposition lets us take $g=a_m=\operatorname{diag}(\varpi^m,1)$ with $m\ge0$. If $m>0$, $\mathcal K\cap\mathcal K^{a_m}$ contains a subgroup whose reduction is the upper unipotent group of $\mathrm{GL}_2(k)$ on one side and whose conjugate acts as the corresponding opposite filtration on the other. A nonzero intertwiner would descend to a nonzero map through the unipotent coinvariants of $\sigma$. Finite-group cuspidality says those coinvariants vanish. Hence $m=0$ and $g\in J$.

For support reduction, take a nonzero vector in a subrepresentation with the fewest inducing cosets in its support and then choose a coset of maximal Cartan radius. Averaging against a matrix coefficient of the finite cuspidal representation on the unipotent quotient at that outermost vertex kills every other outer branch. Cuspidality makes the surviving projection nonzero. If more than the identity coset remained, its stabilizer would give precisely an intertwiner at positive radius, which the preceding paragraph excluded. Translation therefore produces a nonzero identity-coset vector.

For fixed compact open $C$, choose a principal congruence subgroup contained in $C$. If the Cartan radius of $JgC$ is larger than its level plus one, the same intersection contains a nontrivial finite upper or lower unipotent subgroup, and $\sigma$ has no invariants there. Thus only finitely many radii, and finitely many double cosets at each radius, contribute to (8.1). Theorem 8.2 applies. Conversely, a selected depth-zero supercuspidal contains vectors fixed by $\mathcal K(1)$; the resulting representation of $\mathrm{GL}_2(k)$ cannot have a parabolic constituent, for that would give a nonzero $N$-Jacquet module upstairs. An irreducible cuspidal summand and compact Frobenius reciprocity recover the displayed induction. $\square$

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

**Theorem 8.4 (tame construction).** If $L/K$ is tamely ramified or unramified and $(L/K,\theta)$ is admissible, then $\pi(L,\theta)$ is irreducible supercuspidal. Two such representations are isomorphic exactly when their pairs are carried to one another by a $K$-isomorphism of the quadratic extensions, allowing the nontrivial Galois conjugation of $\theta$. A norm twist is not an additional isomorphism relation: it changes the representation by the corresponding determinant twist. Conversely, every irreducible supercuspidal containing a regular depth-zero nonsplit-torus type or a positive-depth tame quadratic type arises from such a pair.

**Proof strategy.** The alternating commutator pairing makes the Heisenberg representation irreducible. An element of $G$ intertwining it must preserve the associated lattice chain and the embedded torus; admissibility then reduces the normalizer to $L^\times$ and its Galois element, the latter accounting only for $\theta\sim\theta^\tau$. Thus the intertwining is precisely $J$, and Theorem 8.2 applies.

**Proof.** On the finite quotient of adjacent filtration groups, the commutator pairing is nondegenerate after its center is divided out. Induction from a maximal isotropic subgroup therefore gives the unique Heisenberg representation with the prescribed central character. The torus action preserves the pairing and extends this representation to $\Lambda_\theta$.

Suppose $g\in G$ intertwines $\Lambda_\theta$. Comparing the smallest filtration groups on which the defining character is nontrivial forces $g$ to preserve their lattice chain. Comparing the resulting trace-zero characters then forces $g$ to normalize the embedded quadratic algebra $L$. Its normalizer is generated by $L^\times$ and an element inducing $\tau$. The second possibility intertwines $\theta$ with $\theta^\tau$ and is excluded inside one inducing datum by admissibility. Hence the self-intertwining of $\Lambda_\theta$ is exactly $J$.

The same lattice calculation proves the two further hypotheses of Theorem 8.2, neither of which follows from the intertwining equality alone. For support reduction, choose a nonzero vector of minimal inducing support and an outermost lattice-chain coset. Fourier projection against the defining character on the last nontrivial quotient removes the other outer branches. If the projected vector retained a second coset, its stabilizer would intertwine the leading character across two lattice chains, contradicting the normalizer calculation. Iteration produces a nonzero identity-coset vector. For fixed-level finiteness, sufficiently distant Cartan translates make $J\cap gCg^{-1}$ meet the last nontrivial lattice-chain quotient in a direction on which the defining character is nontrivial, so the Hom space in (8.1) vanishes. Only a bounded set of Cartan radii survives, with finitely many double cosets at each radius. Theorem 8.2 now proves irreducibility, admissibility, and supercuspidality.

If two compact inductions are isomorphic, Mackey theory supplies an element intertwining their inducing representations. The same filtration argument conjugates one embedded quadratic field to the other, and restriction to the torus identifies the characters up to $\tau$. The converse follows by conjugating the inducing data. Finally, a representation containing one of the types named in the theorem has a minimal compact type whose first noncentral filtration character has the displayed quadratic field as its centralizer; the preceding Heisenberg construction recovers that type. Depth zero was handled in Theorem 8.3. This proves the qualified exhaustion assertion. $\square$

The construction is deliberately described at the level needed later: its torus character, central character, contragredient, twists, and conductor are all explicit. A full enumeration of wild simple types, especially in residue characteristic two, requires additional strata and extension choices. We do not claim that enumeration or import the genericity and newvector theorems for those omitted representations.

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

The definition still makes sense: an irreducible representation with zero Jacquet module is called supercuspidal. What is not supplied here is an explicit bijection between wild supercuspidals and compact inducing data, a proof that every such representation is admissible or generic, or its newvector theorem. Those facts require the omitted wild type theory or a general admissibility-and-genericity theorem not present in the dependency chain. No downstream claim in this book uses them.

## 9. Spherical representations and Satake parameters

### 9.1 One-dimensionality of the hyperspecial fixed space

A representation is **spherical** if it has a nonzero $\mathcal K$-fixed vector. Among irreducible representations, sphericality is extremely restrictive.

**Theorem 9.1.** If $\pi$ is a selected irreducible spherical representation, then $\dim\pi^{\mathcal K}=1$. Moreover $\pi$ is the unique spherical irreducible subquotient of $I(\chi_1,\chi_2)$ for an unordered pair of unramified characters.

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

The parameters above are values of characters at the chosen uniformizer. Books 2 and 5 fix arithmetic reciprocity: a uniformizer maps to **arithmetic Frobenius**. With that identification, the corresponding unramified one-dimensional Galois characters have arithmetic-Frobenius eigenvalues $\alpha$ and $\beta$, and geometric-Frobenius eigenvalues $\alpha^{-1}$ and $\beta^{-1}$.

The parameter chapters will follow Books 80 and 81 instead. There we invert the arithmetic reciprocity map and use geometric reciprocity, so the Weil character denoted by the same multiplicative character $\chi$ satisfies $\chi(\Phi)=\chi(\varpi)$ for geometric Frobenius $\Phi$. Thus the geometric-convention Weil characters used from Chapter 19 onward are obtained through a different identification; they are not the arithmetic-convention Galois characters of the preceding paragraph with their Frobenius eigenvalues left unchanged.

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

No selected supercuspidal representation has an Iwahori-fixed vector. Indeed its Iwahori-Hecke module would produce a subquotient of an unramified principal series, contradicting the zero Jacquet module already proved for the selected compact inductions. Thus a selected irreducible Iwahori-spherical representation is an unramified principal-series constituent or an unramified Steinberg twist.

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

Every infinite-dimensional representation in the selected principal, special, depth-zero, or tame dihedral classes is generic. The selected one-dimensional representations are nongeneric.

**Proof strategy.** Uniqueness uses the open Bruhat cell: two Whittaker functionals give two distributions on $N\backslash G$ with the same equivariance, and inversion exchanges the two sides. On the open cell finite-level Fourier uniqueness leaves one scalar; the closed cell cannot support a nontrivial $\psi$-equivariant distribution. Existence is explicit for principal series and Steinberg, and finite Fourier projection on the inducing type proves it for the selected supercuspidals.

**Proof.** For uniqueness, pair a putative left $(N,\psi)$-equivariant distribution with its transpose under $g\mapsto wg^{-1}w^{-1}$. Bruhat decomposition reduces the comparison to $BwB$, parametrized by one additive coordinate. Fourier inversion says an additive distribution with prescribed nontrivial character is determined by one value. On the closed cell, the stabilizer contains $N$, on which the prescribed character is nontrivial, so the distribution vanishes. Hence the Hom space has dimension at most one.

For $I(\chi_1,\chi_2)$ the integral

$$
\lambda(f)=\int_K f(wn(x))\psi(-x)\,dx
$$

on compactly supported open-cell vectors is nonzero and extends algebraically to the whole representation. It descends to the Steinberg constituent and vanishes on the one-dimensional constituent.

For a depth-zero type, restriction to the finite upper-unipotent group contains every nontrivial additive character with multiplicity one; Fourier projection produces a nonzero functional and extension by zero from the identity inducing coset gives the required functional on the compact induction. For a positive-depth tame type, the last nontrivial lattice quotient carries the Heisenberg representation of Section 8.4. Choosing a polarization containing the upper-nilpotent line produces the required one-dimensional $\psi$-eigenspace. The compact-induction formula

$$
\lambda(f)=
\sum_{n\in(N\cap J)\backslash N}
\ell(f(n))\psi(-n)
$$

has only finitely many nonzero terms for each $f$ and satisfies $\lambda(\pi(n_0)f)=\psi(n_0)\lambda(f)$. A function supported on $J$ shows that it is nonzero. These are exactly the genericity calculations proved for the selected types in Book 79. $\square$

A finite Fourier decomposition at each compact $N$-orbit does not by itself prove genericity for an arbitrary primitive wild representation: a nonzero-frequency quotient need not survive the direct limit. Book 78 marks this boundary explicitly, and the present theorem does not cross it.

### 11.3 The Whittaker model

For generic irreducible $\pi$, the map $v\mapsto W_v$ is injective: its kernel is a subrepresentation and the functional is nonzero. Its image $\mathcal W(\pi,\psi)$ is the **Whittaker model**. Uniqueness makes this model canonical up to a scalar choice of $\lambda$.

Changing the additive character to $\psi_a(x)=\psi(ax)$ does not change genericity. Indeed conjugation by $\operatorname{diag}(a,1)$ transports one Whittaker model to the other. Conductors defined using a fixed $\psi$ must nevertheless record its conductor if formulas involve Fourier transform; we keep $n(\psi)=0$ throughout.

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

**Lemma 13.1 (selected oldform filtration).** Let $\pi$ be an infinite-dimensional representation in the selected principal, special, depth-zero, or tame dihedral classes, and take $n(\psi)=0$. Suppose $\pi^{\mathcal K_1(\mathfrak p^m)}$ is nonzero for at least one $m$, and let $n_0$ be the least such integer. Then

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

**Proof strategy.** Compute the fixed lines directly in each selected construction. Principal-series double cosets leave an interval bounded by the two character conductors; exactness separates the special constituent at the reducibility wall. For a tame quadratic type, Mackey decomposition leaves an interval shifted by the trace-dual defect. The Kirillov coordinate identifies the surviving lines with successive valuation shells.

**Proof.** First let $\pi=I(\chi_1,\chi_2)$ be irreducible and put $r_i=a(\chi_i)$. In the compact picture the double cosets

$$
(B\cap\mathcal K)\backslash\mathcal K/
\mathcal K_1(\mathfrak p^m)
$$

are indexed by integers $j=0,\ldots,m$, measuring the relative position of a primitive row. On the stabilizer of the $j$th representative, covariance tests $\chi_1$ on $1+\mathfrak p^j$ and $\chi_2$ on $1+\mathfrak p^{m-j}$. A value on that coset is therefore free precisely when

$$
r_1\le j\le m-r_2.
\tag{13.1}
$$

The allowed cosets have disjoint support. Hence the fixed-space dimension is

$$
\max\{0,m-r_1-r_2+1\}.
\tag{13.2}
$$

Thus $n_0=r_1+r_2$, and each higher level adds exactly one endpoint coset.

The same calculation applies to the two reducible inductions. Compact-open invariants are exact. If $\mu$ is ramified, the determinant constituent $\mu\circ\det$ has no $\mathcal K_1$-fixed vectors, so the special constituent inherits all the fixed lines and begins at $2a(\mu)$. If $\mu$ is unramified, the determinant constituent contributes one line at every level; subtracting it from the $m+1$ lines of the induced representation leaves dimension zero at $m=0$ and dimension $m$ for $m\ge1$. This is the formula with $n_0=1$.

Now let $\pi=\pi(L,\theta)$ be selected supercuspidal. Mackey decomposition gives

$$
\pi^{\mathcal K_1(\mathfrak p^m)}
\cong
\bigoplus_{Jg\mathcal K_1}
\operatorname{Hom}_{J\cap g\mathcal K_1g^{-1}}
(\Lambda_\theta,\mathbf1).
\tag{13.3}
$$

The lattice-chain intersection calculation of Book 79 compares the upper and lower root lattices through the trace annihilator. Before

$$
n_0=v_K(\mathfrak d_{L/K})+f(L/K)a_L(\theta)
$$

one intersection contains a unit layer on which the type character is nontrivial, so every summand vanishes. At level $m\ge n_0$, exactly the $m-n_0+1$ consecutive Cartan positions survive. At each position the intersection is a polarization of the finite Heisenberg quotient, whose fixed space is one dimensional. This proves the dimension formula for the selected supercuspidals.

In the Whittaker model the surviving principal or type cosets restrict to consecutive valuation shells. At the first level there is one shell and hence one vector $v_0$. Increasing the level exposes one new shell at a time. This is the Kirillov interpretation of the three direct calculations, not an assumption that an arbitrary shell function is fixed.

It remains to identify the displayed basis. If $a_j=\operatorname{diag}(\varpi^{-j},1)$ and $k\in\mathcal K_1(\mathfrak p^m)$, then

$$
a_j^{-1}ka_j\in\mathcal K_1(\mathfrak p^{n_0})
\quad\text{whenever }0\le j\le m-n_0.
$$

Indeed the upper-right entry gains $j$ powers of $\varpi$, the lower-left loses $j$ but remains in $\mathfrak p^{m-j}\subseteq\mathfrak p^{n_0}$, and the lower-right congruence remains strong enough. Hence each $v_j$ is fixed. Their Kirillov functions occupy distinct newly exposed endpoint shells, so they are linearly independent; the dimension count makes them a basis. $\square$

This proof is genuinely rank two. The one-dimensional valuation line in $K^\times$ makes the interval grow by one. For higher rank, oldform dimensions are governed by a multidimensional cone and require more elaborate combinatorics.

### 13.3 Existence, uniqueness, and oldvector growth

**Theorem 13.2 (selected local newvector theorem).** Every infinite-dimensional irreducible representation $\pi$ in the selected principal, special, depth-zero, or tame dihedral classes has a finite conductor exponent. At the minimal level,

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

For a selected supercuspidal, the displayed formula shows directly that the contragredient is again selected supercuspidal with the same conductor. Compact-mod-center support is preserved under inversion, and the conductor formula for $\theta^{-1}$ equals that for $\theta$.

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

## 15. Local factors from Whittaker models

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

For a selected depth-zero or tame dihedral supercuspidal representation of $\mathrm{GL}_2(K)$, the standard local factor is $1$. The richer information is carried by its conductor, central character, and epsilon factor; Chapter 21 constructs the latter and proves its compatibility with quadratic induction. No division-algebra representation is used in defining anything in this chapter.

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

What changes is the reach of the tame quadratic construction. Every ramified quadratic extension of $\mathbf Q_2$ is wildly ramified, so its different exponent need not be one and the simple tame lattice-chain formula $a_L(\theta)+1$ is unavailable. For the induced Weil parameter, the exact conductor formula is still

$$
\Delta(L/K)+f(L/K)a_L(\theta),
$$

but constructing the matching representation and identifying the correct rectified character require wild type data not developed here. This is exactly the scope boundary of Section 8.6; neither the selected classification nor the selected newvector theorem includes this case.

## 17. The classification and invariant dictionary

### 17.1 The selected families with their invariants

For quick downstream use, the irreducible representations and their basic data are:

| family | condition | central character | conductor/newvector | contragredient |
|---|---|---|---|---|
| $\mu\circ\det$ | always irreducible, nongeneric | $\mu^2$ | epsilon-conductor $2a(\mu)$; $\mathcal K_1$-fixed only when $\mu$ is unramified | $\mu^{-1}\circ\det$ |
| $I(\chi_1,\chi_2)$ | $\chi_1\chi_2^{-1}\ne\nu^{\pm1}$ | $\chi_1\chi_2$ | $a(\chi_1)+a(\chi_2)$ | $I(\chi_1^{-1},\chi_2^{-1})$ |
| $\operatorname{St}\otimes\mu$ | generic special | $\mu^2$ | $1$ if $a(\mu)=0$, else $2a(\mu)$ | $\operatorname{St}\otimes\mu^{-1}$ |
| $\pi(L,\theta)$ | selected depth-zero or tame admissible pair | $\theta|_{K^\times}$ | unique at $a(\pi)$ | $\pi(L,\theta^{-1})$ |

For $m\ge a(\pi)$ and every selected infinite-dimensional row,

$$
\dim\pi^{\mathcal K_1(\mathfrak p^m)}=m-a(\pi)+1.
$$

A selected representation is spherical precisely when it is the spherical constituent of an unramified principal series; its hyperspecial fixed space is one-dimensional. It is Iwahori-spherical precisely when it is an unramified principal-series constituent or an unramified Steinberg twist. Every selected infinite-dimensional representation is generic, and for the selected compact inductions supercuspidality is equivalent to compact support of coefficients modulo the center.

### 17.2 Data needed for local transfer

The selected discrete-series side of $G$ consists of special representations and the constructed depth-zero and tame dihedral supercuspidals. These are the representations considered in the later parameter comparison. The following data are now defined without reference to a quaternion division group:

- the central character $\omega_\pi$ on $K^\times$;
- determinant twisting $\pi\mapsto\pi\otimes\chi$;
- the contragredient $\pi^\vee$;
- the conductor exponent $a(\pi)$ and newvector line;
- compact support of coefficients modulo $Z$ for the selected supercuspidals;
- special versus supercuspidal type;
- Satake parameters and a Hecke polynomial in the spherical case;
- tame admissible-pair data $(L/K,\theta)$ where available.

At this representation-side stage no correspondence has yet been asserted, and no division-algebra representation was used to define these invariants. Chapters 19--23 now construct the selected parameter matching, prove its compatibility properties, construct the matching quaternionic types, and prove the Jacquet--Langlands invariant package.

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

The selected classification is complete: it treats the Borel-generated representations and the depth-zero and tame quadratic supercuspidals needed downstream. It does not claim that every nonzero Jacquet module has a character quotient, enumerate primitive wild supercuspidals by simple strata, or attach Whittaker and newvector data to omitted wild representations. In particular, ramified quadratic type constructions in residue characteristic two remain outside the selected correspondence.

This is an interface boundary, not a suggestion that primitive wild representations do not exist. A later book may add general admissibility and genericity, wild types, and their transfer. None of those later results is used to prove a statement here.

### 17.5 Why characteristic zero is visible

The standing coefficient hypothesis enters at decisive points. Averaging over compact opens is exact because finite quotient orders are invertible. Finite-group representations used at depth zero are semisimple. The Iwahori relation has distinct roots $q$ and $-1$ unless the coefficient characteristic makes them coincide. Smooth contragredient duality and the dimension count for fixed spaces use admissibility together with exact averaging.

If the coefficient field has characteristic $p$, where $p$ is the residue characteristic of $K$, principal series can have additional reducibility and extensions, compact-open invariants are not exact, and supersingular representations appear whose relationship to characteristic-zero supercuspidals is not a literal reduction of this classification. Even in characteristic different from $p$, special coincidences can occur when $q+1$ vanishes in the coefficient field. Those modular theories are substantial subjects of their own.

Thus every classification, conductor, and one-dimensionality theorem in this book is a characteristic-zero statement unless its proof explicitly says otherwise. This is not merely a convenience for square roots of $q$; it is part of the mathematical content.

## 18. Representation-side synthesis

The representation theory of $\mathrm{GL}_2(K)$ is governed by two geometries. The projective line has two Bruhat cells, and this makes normalized induction from the Borel almost completely explicit. The lattice tree has one Cartan distance, and this turns support modulo the center, congruence level, and Hecke action into one-dimensional calculations. Their intersection explains the exceptional reducibility ratios $|\cdot|^{\pm1}$ and fixes the exact placement of the character and Steinberg constituents.

The Jacquet module draws the selected classification boundary. If it has a character quotient, adjunction forces the representation into a principal series, whose two-cell filtration leaves only irreducible principal series, characters, and special representations. The constructed depth-zero and tame types instead have zero Jacquet module and compact-mod-center coefficients. These two mechanisms cover exactly the selected range, not the omitted primitive wild spectrum.

Whittaker uniqueness, together with the separate existence calculations for the selected families, gives every selected infinite-dimensional representation a canonical functional model. The Kirillov coordinate reduces that model to functions on $K^\times$; congruence invariance becomes an interval of valuation shells. From that elementary picture come the existence and uniqueness of the newvector, the exact oldvector growth formula, and the conductor calculations for principal, special, and constructed supercuspidal representations.

The preceding dictionary is coherent rather than merely classificatory. Central character records scalar action, contragredience inverts it, twisting changes both inducing characters together, the conductor identifies minimal integral level, and the spherical Hecke polynomial records two unramified roots. We now prove that these are not merely analogous to Galois-theoretic data: in the selected range they are the invariants of a precise Weil--Deligne parameter.

## 19. Weil--Deligne parameters in dimension two

### 19.1 Why a representation needs a second language

The group-theoretic classification answers the question “from which geometric source does $\pi$ come?” It does not by itself explain why the conductor found from congruence subgroups is also the exponent in a functional equation, why a Steinberg representation has only one Euler root, or how a representation should behave when $K$ is replaced by a finite extension. Weil--Deligne parameters put Frobenius, inertia, and monodromy in one finite-dimensional object and answer all three questions at once.

This chapter develops only the two-dimensional objects needed here. The general theory, including the local monodromy theorem and the construction of epsilon factors for arbitrary finite-inertia representations, was established in Book 80. We recall every definition and specialize every formula, so that no normalization is hidden.

Fix a separable closure $\overline K$. Under the quotient map $G_K\to G_K/I_K$, let $W_K$ be the inverse image of the ordinary infinite cyclic subgroup generated by geometric Frobenius. There is an exact sequence

$$
1\longrightarrow I_K\longrightarrow W_K
\xrightarrow{\nu_K}\mathbf Z\longrightarrow0,
\qquad \nu_K(\Phi)=1,
$$

where $I_K$ is inertia and $\Phi$ is a lift of geometric Frobenius. Give $I_K$ its profinite topology and $\mathbf Z$ the discrete topology. Put

$$
|w|=q^{-\nu_K(w)}.
$$

For Chapters 19--24, invert the arithmetic reciprocity map of Books 2 and 5 and denote the resulting geometric reciprocity map by $\operatorname{rec}_K$. Thus

$$
\operatorname{rec}_K(\varpi)=\Phi.
\tag{19.1}
$$

Thus a smooth character of $K^\times$ and its corresponding Weil character have the same value on $\varpi$ and $\Phi$. This is the deliberate convention change announced in Section 9.4 and used in Books 80 and 81. Returning to the earlier arithmetic reciprocity identification would invert every displayed unramified root.

### 19.2 The definition and the monodromy relation

A two-dimensional **Weil--Deligne representation** is a pair $D=(r,N)$ on a two-dimensional complex vector space $V$ such that

1. $r:W_K\to\operatorname{GL}(V)$ is continuous and has finite image on inertia;
2. $N\in\operatorname{End}(V)$ is nilpotent; and
3. one has

$$
r(w)Nr(w)^{-1}=|w|N
\qquad(w\in W_K).
\tag{19.2}
$$

We work with Frobenius-semisimple parameters: the semisimple part of $r(\Phi)$ is retained and its commuting unipotent part is discarded. This operation does not discard $N$. That distinction is essential, because $N$ will separate the character and Steinberg constituents at the reducibility wall.

The monodromy relation is forced by tame inertia. On a sufficiently small tame subgroup a potentially unipotent action has the form $\exp(t(\sigma)N)$, and geometric Frobenius changes the tame coordinate by $q^{-1}$. Conjugating the exponential therefore changes $N$ by $q^{-1}=|\Phi|$. This explains both the direction and the power in (19.2).

There are three two-dimensional shapes in the selected range.

- A **split parameter** is $\chi_1\oplus\chi_2$ with $N=0$.
- A **special parameter** is $\operatorname{Sp}_2(\mu)=\mu\otimes\operatorname{Sp}_2$, where on a basis $e_0,e_1$,

  $$
  r(w)e_0=\mu(w)|w|^{1/2}e_0,
  \qquad
  r(w)e_1=\mu(w)|w|^{-1/2}e_1,
  $$

  $$
  Ne_1=e_0,
  \qquad Ne_0=0.
  \tag{19.3}
  $$

- A **dihedral parameter** is $\operatorname{Ind}_{W_L}^{W_K}\theta$ with $L/K$ separable quadratic and $\theta\ne\theta^\tau$.

The centered powers in (19.3) satisfy (19.2), because the eigenvalue on $e_0$ is $|w|$ times the eigenvalue on $e_1$. They also make $\det\operatorname{Sp}_2(\mu)=\mu^2$.

**Proposition 19.1 (classification of the selected shapes).** Let $D=(r,N)$ be a two-dimensional Frobenius-semisimple parameter. If $r$ is reducible or is induced from a character of a quadratic subgroup, then exactly one of the following holds:

1. $N=0$ and $D=\chi_1\oplus\chi_2$;
2. $N\ne0$ and $D\simeq\operatorname{Sp}_2(\mu)$ for a unique $\mu$;
3. $N=0$ and $r\simeq\operatorname{Ind}_{W_L}^{W_K}\theta$ with $\theta\ne\theta^\tau$.

**Proof strategy.** Separate the cases $N=0$ and $N\ne0$. In dimension two, nonzero monodromy has rank one and its kernel supplies the centered character. In the induced case, the two conjugate character lines become visible after restriction to $W_L$.

**Proof.** If $N=0$ and $r$ is reducible, Frobenius semisimplicity makes it a direct sum of characters. If $N\ne0$, choose $e_1$ with $Ne_1=e_0\ne0$. The stable line $\ker N=\mathbf Ce_0$ carries a character $\xi$. Relation (19.2) makes the quotient line carry $\xi|\cdot|^{-1}$. Setting $\mu=\xi|\cdot|^{-1/2}$ gives (19.3), and the character on $\ker N$ shows uniqueness.

Finally, restrict $\operatorname{Ind}_{W_L}^{W_K}\theta$ to $W_L$. It becomes $\theta\oplus\theta^\tau$. If the two characters are distinct, the element outside $W_L$ exchanges their lines, so no line is $W_K$-stable and the induction is irreducible. If they coincide, the induction splits. An irreducible $r$ cannot have $N\ne0$, because $\ker N$ would be a nonzero proper $W_K$-stable line. The three cases are therefore disjoint. $\square$

### 19.3 Determinants, duals, and twists

The elementary operations on parameters are designed to match operations already visible on representations. One has

$$
(r,N)^\vee=(r^\vee,-{}^tN),
\qquad
(r,N)\otimes\chi=(r\otimes\chi,N\otimes1).
$$

The sign in the dual nilpotent operator is forced by differentiating the contragredient action. Up to isomorphism it does not change a two-dimensional special block. Direct calculation gives

$$
(\chi_1\oplus\chi_2)^\vee
=\chi_1^{-1}\oplus\chi_2^{-1},
$$

$$
\operatorname{Sp}_2(\mu)^\vee
\simeq\operatorname{Sp}_2(\mu^{-1}),
$$

$$
(\operatorname{Ind}_{W_L}^{W_K}\theta)^\vee
\simeq\operatorname{Ind}_{W_L}^{W_K}\theta^{-1}.
\tag{19.4}
$$

For quadratic induction the determinant contains a sign that must not be lost:

**Proposition 19.2.** If $L/K$ is separable quadratic, then

$$
\det\operatorname{Ind}_{W_L}^{W_K}\theta
=\theta|_{K^\times}\,\omega_{L/K},
\tag{19.5}
$$

where characters are transported by reciprocity and $\omega_{L/K}$ is the quadratic character attached to $L/K$.

**Proof.** In an induced basis, an element of $W_L$ acts diagonally through $\theta$ and $\theta^\tau$. Its determinant descends, under transfer and reciprocity, to $\theta|_{K^\times}$. An element in the other coset exchanges the two basis vectors and contributes the sign of the permutation representation of $W_K/W_L$. That sign is $\omega_{L/K}$. $\square$

Formula (19.5) is the reason the direct tame type $\pi(L,\theta)$ from Chapter 8 cannot be matched naively with $\operatorname{Ind}\theta$: its central character is only $\theta|_{K^\times}$. The rectification in Chapter 20 will repair exactly this discrepancy.

### 19.4 Conductors and Euler factors

Let $a(r)$ be the Artin conductor of the finite-inertia Weil action. The conductor of $D=(r,N)$ is

$$
a(D)=a(r)+\dim V^{I_K}-\dim(\ker N)^{I_K}.
\tag{19.6}
$$

The second term is the monodromy defect. It vanishes when $N=0$. For $\operatorname{Sp}_2(\mu)$ it gives one when $\mu$ is unramified and zero when $\mu$ is ramified. Consequently

$$
a(\chi_1\oplus\chi_2)=a(\chi_1)+a(\chi_2),
$$

$$
a(\operatorname{Sp}_2(\mu))=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
\tag{19.7}
$$

Book 80 proves the induction formula

$$
a_K(\operatorname{Ind}_{W_L}^{W_K}\theta)
=f(L/K)\bigl(a_L(\theta)+d(L/K)\bigr),
\tag{19.8}
$$

where $d(L/K)=v_L(\mathfrak D_{L/K})$. Since

$$
v_K(\mathfrak d_{L/K})=f(L/K)d(L/K),
$$

(19.8) is exactly the conductor formula proved from types in Section 13.6.

The Euler factor sees fewer directions than the conductor. Define

$$
L(s,D)=
\det\left(1-q^{-s}r(\Phi)\mid(\ker N)^{I_K}\right)^{-1}.
\tag{19.9}
$$

This is independent of the lift of $\Phi$, since inertia acts trivially on the displayed space. The basic calculations are

$$
L(s,\chi_1\oplus\chi_2)=L(s,\chi_1)L(s,\chi_2),
$$

$$
L(s,\operatorname{Sp}_2(\mu))=L(s+1/2,\mu),
\tag{19.10}
$$

and

$$
L_K(s,\operatorname{Ind}_{W_L}^{W_K}\theta)=L_L(s,\theta).
\tag{19.11}
$$

For an admissible quadratic character the last factor is $1$. Indeed an inertia-fixed vector in the irreducible two-dimensional induction would make all of it unramified, but a semisimple representation of the cyclic quotient $W_K/I_K$ is a sum of characters. This parameter-side argument matches the compact Kirillov model of a supercuspidal representation.

## 20. The selected local Langlands correspondence

### 20.1 The matching problem and the reducibility wall

The two classifications now have the same shapes, but a resemblance of lists is not yet a correspondence. We must specify the matching, account for the exceptional principal series, and prove that it preserves the invariants already constructed. The reducibility wall is the decisive test: a character and a Steinberg representation have the same two semisimple Weil characters, but only Steinberg has monodromy.

Define the centered special block as in (19.3). For the principal and boundary classes set

$$
\operatorname{rec}_2(I(\chi_1,\chi_2))=\chi_1\oplus\chi_2
\quad\text{if }\chi_1\chi_2^{-1}\ne\nu^{\pm1},
\tag{20.1}
$$

$$
\operatorname{rec}_2(\mu\circ\det)
=\mu\nu^{1/2}\oplus\mu\nu^{-1/2},
\qquad N=0,
\tag{20.2}
$$

$$
\operatorname{rec}_2(\operatorname{St}\otimes\mu)
=\operatorname{Sp}_2(\mu).
\tag{20.3}
$$

The unordered pair in (20.1) is intrinsic by Proposition 4.1. At the wall, the two exact sequences of Theorem 5.1 show why there must be two parameter objects: the nongeneric character gets zero monodromy, and the generic special constituent gets the unique nonzero monodromy compatible with the same two characters.

This assignment immediately explains four observations made earlier. When $\mu$ is unramified, $\mu\circ\det$ is spherical but $\operatorname{St}\otimes\mu$ is only Iwahori-spherical. Their conductors are respectively $0$ and $1$. Their Euler factors have respectively two roots and one root. Finally, only the second is generic. Erasing $N$ would erase all four distinctions.

### 20.2 Rectified quadratic induction

For a tame admissible pair $(L/K,\theta)$, the direct type of Chapter 8 has central character $\theta|_{K^\times}$, whereas (19.5) has the extra factor $\omega_{L/K}$. A **tame rectifier** is a character

$$
\Delta_{L/K,\theta}:L^\times\longrightarrow\mathbf C^\times
$$

characterized by

$$
\Delta_{L/K,\theta}|_{K^\times}=\omega_{L/K}
\tag{20.4}
$$

and by the quadratic Gauss-sum normalization that makes the induction formula for epsilon factors hold. Book 81 proves existence and uniqueness in the selected tame range. In the unramified quadratic case it is the unramified character with $\Delta(\varpi)=-1$. In the tamely ramified case it is tamely ramified, and its uniformizer value is fixed by the normalized quadratic Gauss sum.

The rectifier obeys

$$
\Delta_{\theta^\tau}=\Delta_\theta^\tau,
\qquad
\Delta_{\theta(\chi\circ N_{L/K})}=\Delta_\theta,
\qquad
\Delta_{\theta^{-1}}=\Delta_\theta^{-1}.
\tag{20.5}
$$

The first identity follows by changing the embedding of $L$. The second follows because a norm twist multiplies both sides of the quadratic induction equation by the same rank-one twist factor. The third follows by applying Fourier duality. These properties make the following definition independent of every auxiliary choice:

$$
\operatorname{AI}_{L/K}(\theta)
=\pi(L,\theta\Delta_{L/K,\theta}).
\tag{20.6}
$$

Now (20.4) gives

$$
\omega_{\operatorname{AI}_{L/K}(\theta)}
=\theta|_{K^\times}\omega_{L/K},
$$

which agrees with (19.5). The rectifier has at most tame conductor. It is unramified in the unramified case, and admissibility forces $a_L(\theta)\ge2$ in the ramified tame case. It therefore does not change the conductor in the type formula.

Define

$$
\operatorname{rec}_2(\operatorname{AI}_{L/K}(\theta))
=\operatorname{Ind}_{W_L}^{W_K}\theta.
\tag{20.7}
$$

Primitive wild supercuspidals and wildly ramified quadratic constructions in residue characteristic two are not included in (20.7). This is the scope boundary announced in the catalog, not an implicit claim that those representations do not exist.

### 20.3 Bijectivity in the selected range

**Theorem 20.1 (selected local Langlands correspondence).** Equations (20.1)--(20.3) and (20.7) give a bijection between

- irreducible principal series, determinant characters, special representations, and tame dihedral supercuspidals of $G$; and
- split, special, and tame quadratic-induced two-dimensional Frobenius-semisimple Weil--Deligne parameters.

**Proof strategy.** Match structural classes before numerical invariants. Reducibility of the Weil action and vanishing of $N$ distinguish the three parameter shapes; Jacquet modules, genericity, and compact-mod-center coefficients distinguish the representation shapes.

**Proof.** A split parameter $\chi_1\oplus\chi_2$ with ratio different from $\nu^{\pm1}$ comes from the irreducible principal series $I(\chi_1,\chi_2)$. The standard intertwiner and Proposition 4.1 make the unordered pair the exact isomorphism invariant. At an exceptional unordered pair there is a unique $\mu$ with

$$
\{\chi_1,\chi_2\}=\{\mu\nu^{1/2},\mu\nu^{-1/2}\}.
$$

Zero monodromy gives $\mu\circ\det$ by (20.2), while nonzero monodromy gives $\operatorname{St}\otimes\mu$ by (20.3). Proposition 19.1 shows that every nonzero-monodromy parameter occurs uniquely this way.

For a regular quadratic induction, restriction to $W_L$ recovers the unordered pair $\{\theta,\theta^\tau\}$. The projective kernel recovers the quadratic extension inside the selected dihedral class. The equivalence theorem for tame types says that $\operatorname{AI}_{L/K}(\theta)$ has exactly the same ambiguity: $K$-isomorphism and Galois conjugation. Thus (20.7) is bijective on the dihedral class.

The classes are disjoint. A principal or special representation has nonzero Jacquet module; a dihedral supercuspidal has zero Jacquet module. A determinant character is nongeneric; the infinite-dimensional selected representations are generic. On the parameter side, the corresponding distinctions are reducible with $N=0$, reducible with $N\ne0$, and irreducible. $\square$

### 20.4 Central characters, twists, and contragredients

**Theorem 20.2.** For every selected irreducible representation $\pi$ and smooth character $\chi$ of $K^\times$,

$$
\omega_\pi=\det\operatorname{rec}_2(\pi),
\tag{20.8}
$$

$$
\operatorname{rec}_2(\pi\otimes(\chi\circ\det))
=\operatorname{rec}_2(\pi)\otimes\chi,
\tag{20.9}
$$

$$
\operatorname{rec}_2(\pi^\vee)
=\operatorname{rec}_2(\pi)^\vee.
\tag{20.10}
$$

**Proof.** For a principal series these identities reduce to multiplication or inversion of the two inducing characters. For a determinant character and a special representation, they follow from (20.2), (20.3), and the formulas of Chapter 14. For a dihedral representation, (20.8) is Proposition 19.2 together with rectification. Restriction of $\chi\circ\det$ to the elliptic torus is $\chi\circ N_{L/K}$, so (20.5) gives

$$
\operatorname{AI}_{L/K}(\theta)\otimes(\chi\circ\det)
=\operatorname{AI}_{L/K}(\theta(\chi\circ N_{L/K})),
$$

matching tensor product of the induced parameter. Inversion in (20.5) and (19.4) proves duality. $\square$

The proof reveals why the rectifier is structural rather than decorative. Without it, (20.8) would fail; without its twist and inverse compatibilities, (20.9) and (20.10) would fail.

## 21. Conductors and local constants under the correspondence

### 21.1 Two conductor definitions become one

The representation conductor was defined by the first $\mathcal K_1$-fixed line, while the parameter conductor was defined by ramification and monodromy. Their equality is the most concrete test of the correspondence: it identifies a visible subgroup level with an apparently remote Galois invariant.

For a nongeneric determinant character, literal $\mathcal K_1$-fixed vectors are not the right definition. If $\mu$ is ramified, the matrices $\operatorname{diag}(u,1)$ with $u\in\mathcal O^\times$ lie in every $\mathcal K_1(\mathfrak p^n)$ and act by $\mu(u)$, so no level has fixed vectors. Its standard conductor is instead the conductor of its two-dimensional parameter, namely $2a(\mu)$. The newvector statement below is therefore restricted, correctly, to infinite-dimensional representations.

**Theorem 21.1 (conductor and newvector compatibility).** For every selected $\pi$,

$$
a(\pi)=a(\operatorname{rec}_2(\pi)),
\tag{21.1}
$$

where the left side is the first newvector level for infinite-dimensional $\pi$ and the standard epsilon-conductor for $\mu\circ\det$. If $\pi$ is infinite dimensional and $n=a(\pi)$, then

$$
\dim\pi^{\mathcal K_1(\mathfrak p^r)}=
\begin{cases}
0,&r<n,\\
r-n+1,&r\ge n.
\end{cases}
\tag{21.2}
$$

**Proof.** For an irreducible principal series, Theorem 13.3 and (19.6) both give $a(\chi_1)+a(\chi_2)$. For a determinant character, the split parameter in (20.2) has conductor $2a(\mu)$. For Steinberg, Theorem 13.4 and (19.7) agree.

For a tame admissible pair, the type calculation gives

$$
v_K(\mathfrak d_{L/K})+f(L/K)a_L(\theta)
=f(L/K)\bigl(d(L/K)+a_L(\theta)\bigr),
$$

which is (19.8). Rectification does not change the conductor, as explained after (20.6). This proves (21.1). Formula (21.2) is the local newvector theorem, Theorem 13.2; its Kirillov proof shows that the conductor is precisely the displacement between the support bound of a function and the support bound of its Weyl transform. $\square$

This equality also explains conductor cancellation under twists. There is no formula depending only on $a(\pi)$ and $a(\chi)$. The exact formulas are

$$
a(I(\chi_1,\chi_2)\otimes\chi)
=a(\chi_1\chi)+a(\chi_2\chi),
$$

$$
a(\operatorname{St}\otimes\mu\chi)
=\begin{cases}1,&a(\mu\chi)=0,\\2a(\mu\chi),&a(\mu\chi)>0,\end{cases}
$$

and

$$
a(\operatorname{AI}_{L/K}(\theta)\otimes\chi)
=f(L/K)\left(a_L(\theta(\chi\circ N_{L/K}))+d(L/K)\right).
\tag{21.3}
$$

Characters of equal depth can cancel on their last nontrivial unit quotient. Formula (21.3), not a maximum rule, retains that information.

### 21.2 Rank-one Fourier constants

Local constants originate in the one-dimensional Fourier equation. From this point coefficients are complex. Let $\psi:K\to\mathbf C^\times$ be nontrivial, and define its conductor exponent by the requirement that

$$
\mathfrak p^{-n(\psi)}
\text{ is the largest fractional ideal on which $\psi$ is trivial}.
$$

Equivalently, $\psi$ is trivial on $\mathfrak p^{-n(\psi)}$ and nontrivial on $\mathfrak p^{-n(\psi)-1}$. The qualification by fractional ideals matters because the additive kernel itself need not be an $\mathcal O$-submodule.

Use the self-dual additive Haar measure for $\psi$ and give $\mathcal O^\times$ multiplicative volume one. For a Schwartz--Bruhat function $\Phi$ and a quasicharacter $\chi$, set

$$
Z(s,\chi,\Phi)=
\int_{K^\times}\Phi(x)\chi(x)|x|^s\,d^\times x.
$$

Book 78 proves rationality in $q^{-s}$ and the functional equation

$$
Z(1-s,\chi^{-1},\widehat\Phi)
=\gamma(s,\chi,\psi)Z(s,\chi,\Phi),
\tag{21.4}
$$

where $\widehat\Phi(y)=\int_K\Phi(x)\psi(xy)\,dx$. Writing

$$
\gamma(s,\chi,\psi)
=\epsilon(s,\chi,\psi)
\frac{L(1-s,\chi^{-1})}{L(s,\chi)}
\tag{21.5}
$$

defines the rank-one epsilon factor. If $a(\chi)=a>0$ and $n(\psi)=0$, choosing $c$ with $v(c)=a$ reduces it to a primitive finite Gauss sum on $\mathcal O^\times/(1+\mathfrak p^a)$. Orthogonality shows that its absolute value at $s=1/2$ is one for unitary $\chi$ and that its monomial degree is $a$.

Two transformations will be used repeatedly. For $b\in K^\times$, put $\psi_b(x)=\psi(bx)$ and use its self-dual measure. Then

$$
\epsilon(s,\chi,\psi_b)
=\chi(b)|b|^{s-1/2}\epsilon(s,\chi,\psi).
\tag{21.6}
$$

Fourier inversion gives

$$
\gamma(s,\chi,\psi)
\gamma(1-s,\chi^{-1},\psi^{-1})=1.
\tag{21.7}
$$

Using $\psi$ in both factors replaces the right side by $\chi(-1)$. The distinction is the reflection in the square of the Fourier transform.

### 21.3 Epsilon factors of parameters

For a parameter $D=(r,N)$ on $V$, Book 80 constructs $\epsilon(s,r,\psi)$ from rank-one constants by induction and multiplicativity. Monodromy adds the determinant correction

$$
\epsilon(s,D,\psi)
=\epsilon(s,r,\psi)
\det\left(-q^{-s}r(\Phi)\mid
V^{I_K}/(\ker N)^{I_K}\right).
\tag{21.8}
$$

This correction is forced: monodromy removes invariant directions from the Euler factor, and (21.8) restores their contribution to the functional equation. One obtains

$$
\epsilon(s,D,\psi)
=W(D,\psi)
q^{-[a(D)+n(\psi)\dim V](s-1/2)}.
\tag{21.9}
$$

Define

$$
\gamma(s,D,\psi)
=\epsilon(s,D,\psi)
\frac{L(1-s,D^\vee)}{L(s,D)}.
\tag{21.10}
$$

The determinant in (21.8) also gives the change-of-character formula

$$
\epsilon(s,D,\psi_b)
=\det D(b)|b|^{\dim V(s-1/2)}
\epsilon(s,D,\psi).
\tag{21.11}
$$

For two-dimensional $D$ the exponent is $2s-1$. Duality reads

$$
\gamma(s,D,\psi)
\gamma(1-s,D^\vee,\psi^{-1})=1.
\tag{21.12}
$$

The root number $W(D,\psi)=\epsilon(1/2,D,\psi)$ has absolute value one when $D$ is unitary. It is not an invariant of $D$ alone: (21.11) changes it by $\det D(b)$. Calling it a sign is justified only under additional self-duality and determinant hypotheses.

### 21.4 Principal and special functional equations

For a generic $\pi$ define the Whittaker zeta integral

$$
Z(s,W)=\int_{K^\times}
W\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
|y|^{s-1/2}\,d^\times y.
\tag{21.13}
$$

The half-power makes a principal-series tail $|y|^{1/2}\chi(y)$ become the usual Tate integrand $\chi(y)|y|^s$. The transpose-inverse Whittaker function $\widetilde W$ belongs to the $\psi^{-1}$-model of $\pi^\vee$, and Whittaker uniqueness gives

$$
Z(1-s,\widetilde W)
=\gamma(s,\pi,\psi)Z(s,W).
\tag{21.14}
$$

**Theorem 21.2 (principal factorization).** If $I(\chi_1,\chi_2)$ is generic, then

$$
\gamma(s,I(\chi_1,\chi_2),\psi)
=\gamma(s,\chi_1,\psi)\gamma(s,\chi_2,\psi),
\tag{21.15}
$$

and the same product holds for epsilon factors.

**Proof strategy.** Unfold the Jacquet integral over the open Bruhat cell. At finite level its two coordinates separate into products of one-dimensional Schwartz functions, so the two Tate functional equations apply independently.

**Proof.** A locally constant section on a compact part of the two open-cell coordinates is a finite sum $\sum_j\Phi_{1,j}(x_1)\Phi_{2,j}(x_2)$. Inserting the Jacquet integral into (21.13), moving the two diagonal scalars through the induction covariance, and applying Fubini expresses the result as a finite sum of products

$$
Z(s,\chi_1,\Phi_{1,j})Z(s,\chi_2,\Phi_{2,j}).
$$

The Weyl transform replaces both Schwartz functions by their Fourier transforms. Equation (21.4) contributes the two gamma factors. Compact open-cell sections and their translates span the induction, and rationality extends the identity to all sections. Combining with the Euler-factor product proves the epsilon statement. $\square$

At the reducibility wall the Whittaker functional kills the determinant constituent, so (21.15) specializes to $\operatorname{St}\otimes\mu$. If $\mu$ is unramified, $n(\psi)=0$, and $a=\mu(\varpi)$, (21.8) gives

$$
\epsilon(s,\operatorname{St}\otimes\mu,\psi)
=-a q^{1/2-s}.
\tag{21.16}
$$

The factor $-a$ is the root number and the power $q^{1/2-s}$ records conductor one. If $\mu$ is ramified, $V^{I_K}=0$ and the monodromy quotient in (21.8) vanishes; the epsilon factor is simply the product of the two ramified character factors. Together with (19.10), this proves equality of all local factors for principal, character, and special rows.

### 21.5 Quadratic induction and the lambda factor

Let $L/K$ be finite separable and put

$$
\psi_L=\psi\circ\operatorname{Tr}_{L/K}.
$$

If $d=d(L/K)$ and $e=e(L/K)$, trace duality gives

$$
n(\psi_L)=e\,n(\psi)+d.
\tag{21.17}
$$

Define the induction constant

$$
\lambda(L/K,\psi)
=\frac{\epsilon_K(s,\operatorname{Ind}_{W_L}^{W_K}1,\psi)}
{\epsilon_L(s,1,\psi_L)}.
\tag{21.18}
$$

The conductor induction formula and (21.17) show that numerator and denominator have the same degree in $q^{-s}$; hence $\lambda$ is independent of $s$.

**Theorem 21.3 (induction of local constants).** For a Weil--Deligne representation $U$ of $W_L$,

$$
L_K(s,\operatorname{Ind}_{W_L}^{W_K}U)=L_L(s,U),
\tag{21.19}
$$

$$
\epsilon_K(s,\operatorname{Ind}_{W_L}^{W_K}U,\psi)
=\lambda(L/K,\psi)^{\dim U}
\epsilon_L(s,U,\psi_L).
\tag{21.20}
$$

**Proof strategy.** Frobenius orbits on the cosets give (21.19). For epsilon factors, compare the finite Fourier transform on the induced space with the trace Fourier transform over $L$; the discrepancy for the trivial representation is exactly the constant in (21.18).

**Proof.** On inertia invariants, an orbit of relative Frobenius of length $f(L/K)$ contributes the characteristic polynomial of $r(\Phi_L)$ with variable $q_L^{-s}=q^{-f(L/K)s}$. Multiplying the orbit contributions proves (21.19).

For characters, the local functional equation over $L$ uses the pairing $\psi\circ\operatorname{Tr}_{L/K}$. Identifying the induced $K$-space with the underlying $K$-vector space of $L$ compares two self-dual measures and two finite Fourier transforms. Dividing by the same calculation for the trivial character leaves precisely (21.18), proving (21.20) in dimension one. Character induction and multiplicativity extend it to finite-inertia Weil representations; the monodromy determinant obeys the same orbit calculation as the Euler factor. $\square$

For a tame admissible quadratic pair, Theorem 21.3 becomes

$$
\epsilon_K(s,\operatorname{AI}_{L/K}(\theta),\psi)
=\lambda(L/K,\psi)\epsilon_L(s,\theta,\psi_L).
\tag{21.21}
$$

On the representation side, unfolding the toric Whittaker function turns its Weyl transform into Fourier transform on $L$ with character $\psi_L$. The Gauss-sum condition defining the rectifier makes the remaining scalar exactly $\lambda$. This is the content of the dihedral matching theorem in Book 81, and it proves equality of epsilon and gamma factors in the last selected row.

Combining the preceding results yields the full local-factor compatibility:

**Corollary 21.4.** For every selected $\pi$,

$$
L(s,\pi)=L(s,\operatorname{rec}_2(\pi)),
$$

$$
\epsilon(s,\pi,\psi)
=\epsilon(s,\operatorname{rec}_2(\pi),\psi),
$$

$$
\gamma(s,\pi,\psi)
=\gamma(s,\operatorname{rec}_2(\pi),\psi).
\tag{21.22}
$$

The additive-character scaling law on the representation side is therefore

$$
\epsilon(s,\pi,\psi_b)
=\omega_\pi(b)|b|^{2s-1}\epsilon(s,\pi,\psi),
\tag{21.23}
$$

which agrees with (21.11) by central-character compatibility.

## 22. Base change to a finite extension

### 22.1 Restriction is the organizing principle

Base change asks how a representation of $\mathrm{GL}_2(K)$ should be transported to $\mathrm{GL}_2(M)$ for a finite separable extension $M/K$. Trying to move inducing subgroups directly obscures the answer: a quadratic torus may remain elliptic or may split after scalar extension. On parameters there is one canonical operation—restriction—and it automatically distinguishes the cases.

If $D=(r,N)$ is a parameter over $K$, define

$$
D_M=(r|_{W_M},N).
\tag{22.1}
$$

If $f=f(M/K)$, the degree maps satisfy $\nu_K(w)=f\nu_M(w)$ and $q_M=q^f$. Hence

$$
|w|_K=q^{-f\nu_M(w)}=q_M^{-\nu_M(w)}=|w|_M.
$$

Thus the same $N$ still satisfies the monodromy relation. Whenever $D_M$ remains in the selected range, define

$$
\operatorname{BC}_{M/K}(\pi)
=\operatorname{rec}_{2,M}^{-1}
(\operatorname{rec}_{2,K}(\pi)|_{W_M}).
\tag{22.2}
$$

Rank-one reciprocity turns restriction into the norm:

$$
\chi|_{W_M}\longleftrightarrow\chi\circ N_{M/K}.
\tag{22.3}
$$

This simple rule drives every explicit formula below.

### 22.2 Principal, character, and special base change

Put $\chi_{i,M}=\chi_i\circ N_{M/K}$ and $\mu_M=\mu\circ N_{M/K}$. Restriction of a direct sum gives

$$
\operatorname{BC}_{M/K}(I(\chi_1,\chi_2))
=I(\chi_{1,M},\chi_{2,M})
\tag{22.4}
$$

provided the right side is irreducible. If its ratio becomes $|\cdot|_M^{\pm1}$, restriction has not created monodromy. Therefore the base change is the determinant character $\eta\circ\det$ determined by

$$
\{\chi_{1,M},\chi_{2,M}\}
=\{\eta|\cdot|_M^{1/2},\eta|\cdot|_M^{-1/2}\},
\tag{22.5}
$$

not the Steinberg constituent.

Similarly,

$$
\operatorname{BC}_{M/K}(\mu\circ\det)=\mu_M\circ\det,
\tag{22.6}
$$

and

$$
\operatorname{BC}_{M/K}(\operatorname{St}_K\otimes\mu)
=\operatorname{St}_M\otimes\mu_M.
\tag{22.7}
$$

Equation (22.7) is more than a mnemonic. Restriction preserves the centered norm powers because $|w|_K=|w|_M$ on $W_M$, and it leaves $N$ unchanged. Thus $\operatorname{Sp}_{2,K}(\mu)|_{W_M}=\operatorname{Sp}_{2,M}(\mu_M)$.

### 22.3 Mackey theory for a quadratic parameter

Let $L/K$ be quadratic, let $\theta$ be admissible, and put

$$
D=\operatorname{Ind}_{W_L}^{W_K}\theta.
$$

There are two geometrically different outcomes.

First suppose $L\not\subseteq M$ and put $R=LM$. Then $R/M$ is quadratic. Mackey decomposition gives

$$
D|_{W_M}
\simeq\operatorname{Ind}_{W_R}^{W_M}
(\theta\circ N_{R/L}).
\tag{22.8}
$$

If the new character remains admissible in the tame selected range, then

$$
\operatorname{BC}_{M/K}(\operatorname{AI}_{L/K}(\theta))
=\operatorname{AI}_{R/M}(\theta\circ N_{R/L}).
\tag{22.9}
$$

If regularity is lost, the parameter in (22.8) splits and base change moves to the principal row.

Now suppose $L\subseteq M$. Then the quadratic algebra splits after scalar extension, and restriction yields

$$
D|_{W_M}
\simeq
(\theta\circ N_{M/L})
\oplus
(\theta^\tau\circ N_{M/L}).
\tag{22.10}
$$

Thus a dihedral supercuspidal can become a principal series after base change to a field containing its inducing quadratic extension.

**Proof of (22.8) and (22.10).** Mackey decomposition is indexed by

$$
W_M\backslash W_K/W_L.
$$

If $L\not\subseteq M$, there is one double coset and $W_M\cap W_L=W_R$, which gives (22.8); reciprocity turns restriction of $\theta$ into composition with $N_{R/L}$. If $L\subseteq M$, there are two double cosets and restriction exposes the two conjugate character lines, giving (22.10). $\square$

This calculation is the clearest reason to define base change by parameters. Cuspidality is not an invariant under arbitrary finite extension: it is the ellipticity of the torus after scalar extension that decides.

### 22.4 What base change preserves and what it transforms

Restriction commutes with determinants, tensor products, and duals. Therefore

$$
\omega_{\operatorname{BC}_{M/K}(\pi)}
=\omega_\pi\circ N_{M/K},
\tag{22.11}
$$

$$
\operatorname{BC}_{M/K}(\pi\otimes\chi)
=\operatorname{BC}_{M/K}(\pi)
\otimes(\chi\circ N_{M/K}),
\tag{22.12}
$$

$$
\operatorname{BC}_{M/K}(\pi^\vee)
=\operatorname{BC}_{M/K}(\pi)^\vee.
\tag{22.13}
$$

Conductors require care. If $M/K$ is unramified, inertia and its upper filtration are unchanged, so

$$
a_M(D_M)=a_K(D).
\tag{22.14}
$$

The first newvector exponent is consequently unchanged for generic selected representations. The newvector spaces are not literally the same: they live in different groups with different residue fields.

For tame ramification index $e$, positive Swan depth is multiplied by $e$, while the tame fixed-space term must be recomputed because $I_M$ may kill a tame character. For wild base change the full Herbrand transition is needed. There is no formula depending only on $[M:K]$.

Euler factors transform visibly under unramified base change. If $M/K$ has residue degree $f$, then

$$
L_M(s,D_M)=
\det\left(1-q^{-fs}r(\Phi)^f
\mid(\ker N)^{I_K}\right)^{-1}.
\tag{22.15}
$$

Thus Frobenius roots are raised to the $f$th power; the Euler factor is generally transformed, not numerically preserved.

When $M/K$ is cyclic, let

$$
X_{M/K}=\operatorname{Hom}
(K^\times/N_{M/K}M^\times,\mathbf C^\times).
$$

Induction followed by restriction gives

$$
\operatorname{Ind}_{W_M}^{W_K}(D_M)
\simeq\bigoplus_{\eta\in X_{M/K}}D\otimes\eta.
\tag{22.16}
$$

Applying Theorem 21.3 yields the exact product identities

$$
L_M(s,D_M)=
\prod_{\eta\in X_{M/K}}L_K(s,D\otimes\eta),
\tag{22.17}
$$

and, for $\psi_M=\psi\circ\operatorname{Tr}_{M/K}$,

$$
\epsilon_M(s,D_M,\psi_M)
=\lambda(M/K,\psi)^{-\dim D}
\prod_{\eta\in X_{M/K}}
\epsilon_K(s,D\otimes\eta,\psi).
\tag{22.18}
$$

The same identities hold for selected representations by Corollary 21.4. Trace compatibility of the additive characters is essential in (22.18); unrelated conductor-zero characters introduce the scaling factor (21.23).

Finally, restriction is transitive. Hence, whenever all intermediate parameters remain selected,

$$
\operatorname{BC}_{R/M}
(\operatorname{BC}_{M/K}(\pi))
=\operatorname{BC}_{R/K}(\pi).
\tag{22.19}
$$

Norm transitivity proves this directly in the principal and special formulas, while Mackey theory proves it in the dihedral case.

## 23. Jacquet--Langlands and the preserved invariant package

### 23.1 Quaternion structure and matching tori

The formal quaternionic interface of Book 76 deliberately stopped before the local-algebra and representation-theoretic calculations needed for transfer. We now supply them in the selected range. Let $K_2/K$ be the unramified quadratic extension, let $\sigma$ be its nontrivial automorphism, and choose the following concrete model:

$$
D_K=K_2\oplus K_2\Pi,
\qquad
\Pi^2=\varpi,
\qquad
\Pi a=\sigma(a)\Pi.
\tag{23.1}
$$

For $x=a+b\Pi$, the canonical involution and reduced norm are

$$
\overline x=\sigma(a)-b\Pi,
\qquad
\operatorname{Nrd}(x)
=a\sigma(a)-\varpi b\sigma(b).
\tag{23.2}
$$

This algebra is a division algebra. Indeed, if the last expression vanished with $b\ne0$, then

$$
v_K(N_{K_2/K}(a))
=1+v_K(N_{K_2/K}(b)),
$$

but the left side is even and the right side is odd. If $b=0$, vanishing forces $a=0$. Thus every nonzero element has nonzero reduced norm and hence an inverse. The same parity prevents cancellation between the two terms of (23.2), so

$$
v_K(\operatorname{Nrd}(a+b\Pi))
=\min\{2v_{K_2}(a),1+2v_{K_2}(b)\}.
$$

It follows directly that the maximal order, radical, and residue field are

$$
\mathcal O_D=\mathcal O_{K_2}\oplus\mathcal O_{K_2}\Pi,
\qquad
\mathfrak P_D=\Pi\mathcal O_D,
\qquad
\mathcal O_D/\mathfrak P_D\simeq k_2.
\tag{23.3}
$$

Put

$$
v_D(x)=v_K(\operatorname{Nrd}(x)),
\qquad
U_D^r=1+\mathfrak P_D^r\quad(r\ge1).
\tag{23.4}
$$

Then $v_D(\Pi)=1$, while $v_D(z)=2v_K(z)$ for $z\in K^\times$. The quotient $D_K^\times/K^\times$ is compact, as proved in Book 76; (23.3) also exhibits it as the union of the two compact images of $\mathcal O_D^\times$ and $\Pi\mathcal O_D^\times$.

We henceforth use $D_K$ for this standard quaternionic inner form. This explicit choice is enough for every construction and character comparison below; no classification theorem for arbitrary central simple algebras is being inserted as an unstated input.

We also need the embedding statement left open in Book 76.

**Lemma 23.1 (selected quadratic tori embed).** Every tame separable quadratic extension $L/K$ embeds in $D_K$. Any two embeddings are conjugate by $D_K^\times$. For $x\in L^\times$ one has

$$
\operatorname{Trd}(x)=\operatorname{Tr}_{L/K}(x),
\qquad
\operatorname{Nrd}(x)=N_{L/K}(x).
\tag{23.5}
$$

Consequently every regular elliptic conjugacy class in the selected range has a unique matching class in $D_K^\times$, characterized by equality of reduced characteristic polynomials.

**Proof strategy.** The unramified field is already visible in (23.1). A tame ramified quadratic extension is generated by a square root of a unit times $\varpi$, and the unit can be obtained as a norm from $K_2$.

**Proof.** The unramified case is the displayed copy of $K_2$. Suppose $L/K$ is ramified and tame. Then the residue characteristic is odd and

$$
L=K(\sqrt{u\varpi})
$$

for some $u\in\mathcal O^\times$. The norm $\mathcal O_{K_2}^\times\to\mathcal O^\times$ is surjective: it is surjective on residue fields, and successive lifting across principal-unit quotients is surjective because the residue trace $k_2\to k$ is. Choose $b\in\mathcal O_{K_2}^\times$ with $N_{K_2/K}(b)=u$. Then

$$
(b\Pi)^2=b\sigma(b)\varpi=u\varpi,
$$

so $\sqrt{u\varpi}\mapsto b\Pi$ gives the required embedding. Formula (23.5) follows by restricting (23.2). If two embeddings are given, choose a generator of $L$. Its two images have the same reduced trace and norm, hence the same reduced characteristic polynomial. The quaternionic conjugacy calculation of Book 76 then conjugates one image to the other. The same calculation proves uniqueness of a matching class. $\square$

Split regular polynomials do not occur in $D_K$: a root would generate a subalgebra with a zero divisor. This is why principal series and determinant characters have no division-side transfer. In the selected spectrum, the transfer domain is precisely the special and tame dihedral discrete-series rows.

### 23.2 Selected division-side types

Characters give the division-side special row immediately. For a smooth character $\mu$ of $K^\times$, put

$$
\rho_D^{\mathrm{sp}}(\mu)=\mu\circ\operatorname{Nrd}.
\tag{23.6}
$$

Its central character is $\mu^2$ because $\operatorname{Nrd}(z)=z^2$ on the center. The dihedral row requires an actual type construction.

Let $(L/K,\theta)$ be a tame admissible pair and set

$$
\vartheta=\theta\Delta_{L/K,\theta},
\tag{23.7}
$$

where $\Delta_{L/K,\theta}$ is the rectifier of Section 20.2. The same direct type character $\vartheta$ is used on the split and division sides. This point is essential: using $\theta$ directly would miss the quadratic factor in the central character on both sides.

At depth zero, $L/K$ is unramified and $\vartheta$ is trivial on $U_L^1$. Put

$$
J_D=K^\times\mathcal O_D^\times.
$$

There is a character $\Lambda^D_\vartheta$ of $J_D$ whose restriction to $\mathcal O_D^\times$ is the inflation of the residue character $\overline\vartheta:k_2^\times\to\mathbf C^\times$ and whose restriction to $K^\times$ is $\vartheta|_{K^\times}$. The two prescriptions agree on $\mathcal O^\times$. Define

$$
\rho_D(L,\theta)
=\operatorname{Ind}_{J_D}^{D_K^\times}\Lambda^D_\vartheta.
\tag{23.8}
$$

The subgroup has index two. Conjugation by $\Pi$ changes $\overline\vartheta$ to $\overline\vartheta^q$, so regularity and elementary Clifford theory show that (23.8) is irreducible of dimension two.

For positive depth, use the conductor-zero additive character fixed in Chapter 11, first remove a norm twist as in the minimal-twist decomposition of Chapter 8, and assume that $\theta$ is minimal. Put $m=a_L(\theta)-1$. The rectifier has smaller conductor and therefore does not alter the leading character. Choose $\beta\in L$ so that, for $x\in\mathfrak p_L^{\lfloor m/2\rfloor+1}$,

$$
\vartheta(1+x)
=\psi\bigl(\operatorname{Tr}_{L/K}(\beta x)\bigr).
\tag{23.9}
$$

Trace duality gives

$$
v_L(\beta)=-a_L(\theta)-d(L/K).
$$

Minimality says that the leading class of $\beta$ is not scalar; hence $K[\beta]=L$. Put $n=-v_D(\beta)$ and define

$$
H_D^1=U_L^1U_D^{\lfloor n/2\rfloor+1},
\qquad
J_D^1=U_L^1U_D^{\lfloor(n+1)/2\rfloor},
\qquad
J_D=L^\times J_D^1.
\tag{23.10}
$$

On $H_D^1$ set

$$
\xi_\beta(u(1+x))
=\vartheta(u)\psi(\operatorname{Trd}(\beta x)).
\tag{23.11}
$$

The two expressions agree on the intersection by (23.9), and the omitted product terms lie beyond the conductor, so (23.11) is a well-defined character. The commutator pairing

$$
(\overline x,\overline y)
\longmapsto\xi_\beta([x,y])
\tag{23.12}
$$

on $J_D^1/H_D^1$ is nondegenerate. Indeed, expansion of the commutator turns its radical into the graded centralizer of $\beta$ under the reduced-trace pairing. The centralizer of a noncentral element of a quaternion algebra is $L$, and the $L$-part has already been divided out by $U_L^1$. The finite Heisenberg argument therefore gives a unique irreducible representation $\eta_\beta^D$ of $J_D^1$ containing $\xi_\beta$.

Extend $\eta_\beta^D$ to $J_D$. The normalization is the same finite one used for the split tame type: realize the Heisenberg representation from a maximal isotropic subgroup, choose determinant-one averaging intertwiners on the prime-to-residue-character cyclic orbits, fix the remaining central sign, and then prescribe the torus character $\vartheta$. The quotient that acts on the finite symplectic space is

$$
L^\times/K^\times U_L^1,
$$

which is cyclic of order $q+1$ in the unramified case and of order two in the tamely ramified case. Thus its projective action linearizes and the prescription determines an irreducible extension $\Lambda^D_\vartheta$. Set

$$
\rho_D(L,\theta)
=\operatorname{Ind}_{J_D}^{D_K^\times}\Lambda^D_\vartheta.
\tag{23.13}
$$

This induction is finite dimensional because $D_K^\times/K^\times$ is compact.

**Theorem 23.2 (division-side tame induction).** The representation (23.8) or (23.13), according to its depth, is irreducible and is not a reduced-norm character. It is independent of the embedding and the auxiliary choices, and

$$
\rho_D(L,\theta)\simeq\rho_D(L',\theta')
$$

if and only if the admissible pairs are $K$-isomorphic. Moreover

$$
\omega_{\rho_D(L,\theta)}
=\theta|_{K^\times}\omega_{L/K},
\tag{23.14}
$$

$$
\rho_D(L,\theta)\otimes(\chi\circ\operatorname{Nrd})
\simeq
\rho_D\bigl(L,\theta(\chi\circ N_{L/K})\bigr),
\tag{23.15}
$$

and

$$
\rho_D(L,\theta)^\vee
\simeq\rho_D(L,\theta^{-1}).
\tag{23.16}
$$

**Proof strategy.** The decisive calculation is exact intertwining of the simple character and its Heisenberg enlargement. Compactness modulo the center then turns the endomorphism calculation into irreducibility without a hidden admissibility assumption.

**Proof.** At depth zero, $J_D$ is normal of index two and the two conjugate characters on $J_D$ are distinct. Clifford theory proves irreducibility and shows that an isomorphism recovers the Frobenius orbit of the residue character and the central scalar. This proves the theorem in that case, including the assertion that the two-dimensional representation is not a character.

Now suppose the depth is positive. Let $h\in D_K^\times$ intertwine the type. Comparing (23.11) on the common deep unit subgroup places

$$
h^{-1}\beta h-\beta
$$

in the appropriate trace-dual radical. On the first nonzero graded quotient, $h$ therefore normalizes the centralizer of the leading class of $\beta$, namely $L$. Multiplying by an element of $L^\times$ removes that graded part. Repeating the argument moves $h$ through the successive radical layers. At the middle layer, nondegeneracy of (23.12) excludes every remaining class outside $J_D^1$. Hence

$$
I_{D_K^\times}(\Lambda^D_\vartheta)=J_D.
\tag{23.17}
$$

Mackey theory now gives a one-dimensional endomorphism algebra. After dividing out the scalar central action, the representation is a smooth projective representation of the compact group $D_K^\times/K^\times$ and hence factors through a finite quotient. Averaging makes the corresponding finite-dimensional representation semisimple. A semisimple representation with scalar endomorphism algebra is irreducible.

The same first-graded-layer argument applied to an intertwiner between two types conjugates their quadratic fields and identifies their torus characters up to the nontrivial field automorphism. This proves the equivalence assertion. Regularity makes the two torus characters distinct on the first noncentral layer, whereas a reduced-norm character is scalar there, so the resulting representation is not a character. Lemma 23.1 removes dependence on the chosen embedding, while the uniqueness of the Heisenberg representation and normalized extension removes the other choices. Finally $\vartheta|_{K^\times}=\theta|_{K^\times}\omega_{L/K}$ gives (23.14); reduced norm restricts to $N_{L/K}$, and the rectifier identities (20.5) give (23.15) and (23.16). A nonminimal pair is defined by (23.15) from a minimal one, and the same equivalence argument makes this independent of the minimal-twist decomposition. $\square$

No claim has been made about primitive wild types or ramified quadratic types in residue characteristic two. The division-side construction has exactly the same tame boundary as the split construction.

### 23.3 The split--division character calculation

The construction alone does not prove Jacquet--Langlands. The missing statement is the sign in the regular-elliptic character identity, including elements close to the center where more than two compact-induction cosets can contribute.

For an admissible representation, write $\Theta$ for the locally constant function representing its distribution character on the regular set. On $D_K^\times$ this is the ordinary trace because the selected representations are finite dimensional. Matching elements $g\in G$ and $g_D\in D_K^\times$ have the same reduced characteristic polynomial.

**Lemma 23.3 (paired tame-type trace calculation).** Let $(L/K,\theta)$ be a tame admissible pair. For every pair of matching regular elements,

$$
\Theta_{\operatorname{AI}_{L/K}(\theta)}(g)
=-\operatorname{tr}\rho_D(L,\theta)(g_D).
\tag{23.18}
$$

**Proof strategy.** Apply the compact-induction character formula on both sides at a common finite level. The split calculation is indexed by lattice chains in $K^2$ fixed to that level; the division calculation is indexed by the two valuation orientations in $D_K$. Interior split chains cancel in pairs. The terminal finite Fourier sum is hyperbolic on $M_2(K)$ and anisotropic on $D_K$, and their normalized Gauss sums are $1$ and $-1$.

**Proof.** Fix a sufficiently small regular neighborhood of $g$ on which its centralizer and all contributing compact-induction double cosets are constant. Book 76's character formula and the fixed-subtree argument of Chapter 8 express the split character as the finite sum

$$
S_{M_2}(g)
=\sum_{\substack{z\in J\backslash G/C_G(g)\\
zgz^{-1}\in J}}
\operatorname{tr}\Lambda_\vartheta(zgz^{-1}).
\tag{23.19}
$$

The same formula for (23.8) or (23.13) gives a finite sum $S_D(g_D)$ with $J_D$, $D_K^\times$, and $\Lambda^D_\vartheta$. Equality of characteristic polynomials identifies the two centralizer fields and their norm and trace filtrations.

At depth zero, filter the $g$-fixed subtree by distance from its central segment. At a scalar interior vertex, the $q-1$ transverse directions have nontrivial-unipotent reduction. The scalar contribution is $(q-1)\overline\vartheta(z)$, while the sum of the transverse contributions is

$$
(q-1)(-\overline\vartheta(z)).
$$

Thus removal of an outer shell does not change the total. Repeating this removal reduces the finite tree to its terminal vertex or edge; its two orientations are the two cosets of $K^\times\mathcal O_D^\times$ in $D_K^\times$. If the original reduction is elliptic regular, there was only the terminal vertex to begin with, and the two formulas are visibly

$$
S_{M_2}(g)
=-\overline\vartheta(t)-\overline\vartheta(t^q),
\qquad
S_D(g_D)
=\overline\vartheta(t)+\overline\vartheta(t^q).
\tag{23.20}
$$

If the reduction is scalar, the shell removal just described performs the required telescoping; its terminal values are again the right side of (23.20). Thus the calculation includes regular elements arbitrarily close to the center rather than assuming that only two torus cosets contribute.

At positive depth, use the radical filtration in (23.10) and its split analogue. Conjugates entering the next radical layer are parametrized by its additive quotient: replacing a representative by $(1+x)z$ changes the simple-character trace by

$$
\psi\bigl(\operatorname{Trd}(\beta[x,y])\bigr)
$$

for the corresponding graded displacement $y$. Thus the sum over all representatives in that fiber is the finite Fourier transform of the commutator pairing (23.12). If $y$ is not in the graded centralizer, nondegeneracy makes the displayed character nontrivial and the whole fiber sums to zero. If $y$ is centralizing, its $L$-part is absorbed into the torus coset and the calculation descends to the next layer. This gives an explicit pairing of every nonterminal split and division contribution.

The only unpaired layer is the first two-dimensional complement to the graded centralizer. After a common nonzero scalar and compatible coordinates, reduced norm is the hyperbolic form $(u,v)\mapsto uv$ on the split complement and the anisotropic form $z\mapsto N_{k_2/k}(z)$ on the division complement. For any nontrivial additive character $\overline\psi$ of $k$,

$$
q^{-1}\sum_{u,v\in k}\overline\psi(uv)=1,
\qquad
q^{-1}\sum_{z\in k_2}\overline\psi(N_{k_2/k}(z))=-1.
\tag{23.21}
$$

The first equality follows by summing over $v$. For the second, the zero norm has one preimage and every nonzero norm has $q+1$ preimages, so the sum is

$$
1+(q+1)\sum_{a\in k^\times}\overline\psi(a)=-q.
$$

This argument is valid in residue characteristic two as well. It is precisely the relative sign between the two Heisenberg traces. The determinant-one normalization of the averaging intertwiners removes projective scalar ambiguity, and using the common character $\vartheta$ removes torus scalar ambiguity. All earlier layers occur in identical Fourier-orthogonality pairs. Consequently

$$
S_{M_2}(g)+S_D(g_D)=0.
$$

If the element is closer to the center, the first Fourier layer can be scalar. The zero-term alternative above then descends one layer and repeats; termination is guaranteed by regularity. Hence the argument covers every regular elliptic neighborhood for a minimal pair. A norm twist multiplies the two character values by $\chi(\det g)$ and $\chi(\operatorname{Nrd}(g_D))$, which are equal on matching elements. The minimal-twist decomposition therefore proves the formula for every tame admissible pair. Equations (23.19) and its division analogue prove (23.18). $\square$

The special row has an independent and simpler sign calculation.

**Proposition 23.4 (the special character identity).** If $g$ and $g_D$ match and are regular, then

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\operatorname{tr}(\mu\circ\operatorname{Nrd})(g_D).
\tag{23.22}
$$

**Proof.** In the projective-line realization, the unnormalized induction of the trivial character is $C^\infty(\mathbf P^1(K))$. A regular elliptic element has no $K$-rational eigenline. On a sufficiently small regular neighborhood its action kernel therefore has no diagonal fixed point, so the induced character is zero there. Removing the constant subrepresentation gives

$$
\Theta_{\operatorname{St}}(g)=-1.
$$

Twisting multiplies this value by $\mu(\det g)$. Matching gives $\det g=\operatorname{Nrd}(g_D)$, which proves (23.22). $\square$

The minus sign has now been calculated in both selected rows; it has not been imported from a later transfer theorem.

### 23.4 The selected Jacquet--Langlands correspondence

Let the selected spectrum of $D_K^\times$ consist of the reduced-norm characters (23.6) and the tame dihedral representations (23.8), (23.13). Define

$$
\boxed{
\begin{aligned}
\operatorname{JL}(\operatorname{St}\otimes\mu)
&=\mu\circ\operatorname{Nrd},\\
\operatorname{JL}(\operatorname{AI}_{L/K}(\theta))
&=\rho_D(L,\theta).
\end{aligned}}
\tag{23.23}
$$

This definition follows the constructions, not a parameter label.

**Theorem 23.5 (selected local Jacquet--Langlands).** The map (23.23) is a bijection from the selected discrete-series representations of $G$ to the selected irreducible representations of $D_K^\times$. It is characterized by

$$
\boxed{
\Theta_\pi(g)
=-\Theta_{\operatorname{JL}(\pi)}(g_D)}
\tag{23.24}
$$

on matching regular elliptic elements. If one now defines the division-side parameter on the constructed representations by

$$
\operatorname{rec}_D(\mu\circ\operatorname{Nrd})
=\operatorname{Sp}_2(\mu),
\tag{23.25}
$$

$$
\operatorname{rec}_D(\rho_D(L,\theta))
=\operatorname{Ind}_{W_L}^{W_K}\theta,
\tag{23.26}
$$

then

$$
\operatorname{rec}_D(\operatorname{JL}(\pi))
=\operatorname{rec}_2(\pi).
\tag{23.27}
$$

**Proof.** Irreducibility, equivalence of tame pairs, and disjointness from reduced-norm characters were proved in Theorem 23.2. Thus the two rows of (23.23) are bijections onto the selected division-side classes. Proposition 23.4 and Lemma 23.3 prove (23.24).

It remains to justify the word “characterized.” Suppose two selected division-side representations have the same trace on the regular set. That set is dense: its complement is the center $K^\times$, which has empty interior in the four-dimensional $K$-space $D_K$. The representations are finite dimensional and smooth, so their trace functions are locally constant. Their traces consequently agree on all of $D_K^\times$. Evaluation at the identity gives equal dimensions, and evaluation at central elements then gives equal central characters. After that common central action is divided out, both representations are smooth projective representations of the compact group $D_K^\times/K^\times$ and factor through a common finite quotient with the same multiplier. The corresponding finite twisted group algebra is semisimple, and independence of its irreducible characters shows that the representations are isomorphic. Thus (23.24) determines the image of every selected split representation and characterizes (23.23) without a hidden reconstruction theorem.

Finally (23.25)--(23.26) are well defined by Theorem 23.2 and the pair-equivalence proved on the split side, and comparison with (20.3), (20.7) gives (23.27). The character theorem was proved before these parameter labels were assigned, so this last step is not circular. $\square$

Primitive wild supercuspidals are excluded from both the domain and the asserted division-side range. The theorem is complete for the catalog's special, depth-zero, and tame dihedral classes and makes no exhaustivity assertion beyond them.

### 23.5 Conductors, local factors, and levels

It remains to prove that the division-side analytic invariants in the catalog are the ones predicted by (23.25)--(23.26), rather than declaring this by definition. From this point coefficients are complex. For a matrix coefficient $f$ of a selected representation $\rho$ of $D_K^\times$ and $\Phi\in C_c^\infty(D_K)$, use the normalized coefficient integral

$$
Z_D(s,\Phi,f)
=\int_{D_K^\times}
\Phi(x)f(x)|\operatorname{Nrd}(x)|^{s+1/2}\,d^\times x.
\tag{23.28}
$$

The ordinary additive Fourier transform on the four-dimensional space $D_K$ uses the self-dual measure for

$$
(x,y)\longmapsto\psi(\operatorname{Trd}(xy)).
$$

The standard inner-form functional equation uses the normalized operator

$$
\mathcal F_D\Phi(y)
=-\int_{D_K}\Phi(x)
\psi(\operatorname{Trd}(xy))\,dx.
\tag{23.28a}
$$

The sign is the anisotropic rank-two Hasse sign. It is forced already by the special row: with conductor-zero $\psi$, the trace-dual lattice of $\mathcal O_D$ is $\mathfrak P_D^{-1}$. The quotient $\mathfrak P_D^{-1}/\mathcal O_D$ has $q^2$ elements, so a self-dual measure gives $\operatorname{vol}(\mathcal O_D)=q^{-1}$ and hence

$$
\mathcal F_D\mathbf1_{\mathcal O_D}
=-q^{-1}\mathbf1_{\mathfrak P_D^{-1}}.
$$

Without the displayed minus sign, the trivial representation of $D_K^\times$ would have endpoint constant $+q^{1/2-s}$ instead of the Steinberg constant $-q^{1/2-s}$. Thus (23.28a) fixes the normalization from a direct lattice calculation, not from a parameter label.

Shell decomposition in $v_D$ makes every integral a rational function of $q^{-s}$. Smoothness of the finite-dimensional coefficient space reduces the unit calculations to a finite quotient, so the resulting fractional ideal in the principal ring $\mathbf C[q^s,q^{-s}]$ is finitely generated and hence principal. Its normalized generator is $L_D(s,\rho)$.

The functional-equation scalar is also a consequence of the construction rather than an extra assumption. Under left and right multiplication by $D_K^\times$, the open orbit in the additive space $D_K$ is $D_K^\times$ itself. Frobenius reciprocity and Schur's lemma make the space of bilinear forms with the equivariance of (23.28) one dimensional. The operator $\mathcal F_D$ exchanges that equivariance with the contragredient one. Thus, first in a convergence half-plane and then as a rational identity, if $\check f(x)=f(x^{-1})$ there is a scalar $\gamma_D(s,\rho,\psi)$ satisfying

$$
Z_D(1-s,\mathcal F_D\Phi,\check f)
=\gamma_D(s,\rho,\psi)Z_D(s,\Phi,f).
$$

Define $\epsilon_D$ by

$$
\gamma_D(s,\rho,\psi)
=\epsilon_D(s,\rho,\psi)
\frac{L_D(1-s,\rho^\vee)}{L_D(s,\rho)}.
$$

**Theorem 23.6 (division local-factor calculation).** For every smooth $\mu$ and every tame admissible pair $(L/K,\theta)$,

$$
L_D(s,\mu\circ\operatorname{Nrd})
=L(s+1/2,\mu),
\tag{23.29}
$$

$$
\epsilon_D(s,\mu\circ\operatorname{Nrd},\psi)
=\epsilon(s,\operatorname{Sp}_2(\mu),\psi),
\tag{23.30}
$$

and

$$
L_D(s,\rho_D(L,\theta))=1,
\tag{23.31}
$$

$$
\epsilon_D(s,\rho_D(L,\theta),\psi)
=\lambda(L/K,\psi)
\epsilon_L(s,\theta,\psi\circ\operatorname{Tr}_{L/K}).
\tag{23.32}
$$

Consequently, if the conductor is the exponent of $q^{-(s-1/2)}$ after the additive-character shift is removed, then

$$
a_D(\mu\circ\operatorname{Nrd})
=\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0,
\end{cases}
\tag{23.33}
$$

and

$$
a_D(\rho_D(L,\theta))
=f(L/K)\bigl(a_L(\theta)+d(L/K)\bigr).
\tag{23.34}
$$

**Proof strategy.** For a reduced-norm character, sum (23.28) over the valuation shells of $D_K$. For a dihedral type, insert a matrix coefficient supported on $J_D$, use a Heisenberg polarization, and reduce the four-dimensional Fourier transform to the one-dimensional Fourier transform over $L$.

**Proof.** Choose $b_0\in\mathcal O_{K_2}^\times$ with $N_{K_2/K}(b_0)=-1$ and put $\Pi_D=b_0\Pi$. Then $\operatorname{Nrd}(\Pi_D)=\varpi$. Write

$$
D_K^\times=\coprod_{m\in\mathbf Z}\Pi_D^m\mathcal O_D^\times.
$$

For $\mu\circ\operatorname{Nrd}$, unit averaging removes every ramified Euler tail. If $\mu$ is unramified, the surviving shell sum is the geometric series with root $\mu(\varpi)q^{-1/2}$, proving (23.29). The trace-dual of $\mathfrak P_D^r$ is the corresponding opposite radical power. Fourier reversal of the shell interval leaves one endpoint when $\mu$ is unramified; the sign in (23.28a) makes its scalar

$$
-\mu(\varpi)q^{1/2-s}
$$

when $n(\psi)=0$. If $\mu$ is ramified, the two boundary unit sums are the rank-one Gauss sums for $\mu\nu^{1/2}$ and $\mu\nu^{-1/2}$. These are exactly the unramified and ramified cases of the monodromy formula in Section 21.4. Changing variables in additive Fourier transform replaces $\psi$ by $\psi_b$ and multiplies both sides by $\mu(b)^2|b|^{2s-1}$, so (23.30) holds for every nontrivial $\psi$.

At depth zero, take a coefficient in the two-coset induced model (23.8). Averaging over $\mathcal O_D^\times/U_D^1\simeq k_2^\times$ is zero by regularity, so the zeta ideal has no Euler denominator. Fourier transform of the two coset coefficients is the finite-field norm Gauss sum in (23.21). After the normalization sign in (23.28a), it is the rank-one Tate sum for $\theta$ over the unramified field $L$; the measure quotient is $\lambda(L/K,\psi)=1$ when $n(\psi)=0$. This proves (23.31)--(23.32) at depth zero.

At positive depth, choose a coefficient of $\Lambda^D_\vartheta$ and extend it by zero to the inducing cosets. Frobenius reciprocity reduces (23.28) to $J_D$. On $H_D^1$, formula (23.11) turns additive Fourier transform into the finite Heisenberg transform. Choosing a maximal isotropic subgroup cancels the complementary variables in pairs and leaves the transform on the field $L$ with additive character $\psi_L=\psi\circ\operatorname{Tr}_{L/K}$ and multiplicative character $\theta$. Regularity makes the unit average zero, so there is no Euler denominator and (23.31) follows. The rank-one functional equation over $L$ supplies $\epsilon_L(s,\theta,\psi_L)$. Comparing the self-dual measure on $L$ with the one induced from the reduced-trace pairing supplies the quadratic Gauss quotient $\lambda(L/K,\psi)$. The anisotropic finite transform contributes the sign $-1$ calculated in (23.21), and the normalization sign in (23.28a) cancels it. The common rectifier in (23.7) removes the remaining torus Gauss scalar, leaving exactly $\lambda(L/K,\psi)$ and proving (23.32) for a minimal pair and conductor-zero $\psi$. If $\theta=\theta_0(\chi\circ N_{L/K})$, multiplying the coefficient by $\chi\circ\operatorname{Nrd}$ inserts precisely the same norm twist in the remaining Tate sum, so the calculation gives (23.32) for the original $\theta$. Replacing $\psi$ by $\psi_b$ and using (23.14) gives the same change-of-additive-character factor on both sides, so the formula holds for every nontrivial $\psi$. No character identity or parameter equality is used in either coefficient calculation.

Taking the monomial degrees in (23.30), (23.32), and using the conductor induction formula (19.8) gives (23.33)--(23.34). $\square$

Combining Theorems 21.1, 21.3, 23.5, and 23.6 proves, rather than assumes, the full selected invariant package. For $\rho=\operatorname{JL}(\pi)$,

$$
\omega_\rho=\omega_\pi,
\tag{23.35}
$$

$$
\operatorname{JL}(\pi\otimes(\chi\circ\det))
=\rho\otimes(\chi\circ\operatorname{Nrd}),
\qquad
\operatorname{JL}(\pi^\vee)=\rho^\vee,
\tag{23.36}
$$

and

$$
a_D(\rho)=a(\pi),
\qquad
L_D(s,\rho)=L(s,\pi),
\qquad
\epsilon_D(s,\rho,\psi)=\epsilon(s,\pi,\psi).
\tag{23.37}
$$

The gamma factors and root numbers therefore agree as well.

The newvector interface needs a separate sentence. The group $U_D^r$ is normal in $D_K^\times$, so for an irreducible $\rho$ its fixed space is either zero or all of $\rho$. It is not a quaternionic analogue of the one-dimensional $\mathcal K_1$-newvector line. The raw order level is the first $r$ for which the whole representation is trivial on $U_D^{r+1}$; the type construction reads it from the simple-character and Heisenberg filtrations in (23.10)--(23.12). The epsilon-conductor is instead (23.33) or (23.34). Their conversion depends on the row and on the reduced-norm filtration. In particular an unramified $\mu\circ\operatorname{Nrd}$ is already fixed by $\mathcal O_D^\times$ while its transferred Steinberg representation has conductor one. What Jacquet--Langlands preserves is the epsilon-conductor, not a fixed vector or an unshifted subgroup index.

### 23.6 What is preserved, transformed, or not comparable

The distinction among these three words prevents several common mistakes.

Under the selected Jacquet--Langlands correspondence, the base field and the parameter do not change. Equations (23.35)--(23.37) show that central character, determinant or reduced-norm twists, duality, conductor, Euler factors, epsilon factors, gamma factors, and root numbers are preserved. This is an equality of invariants calculated independently on the two groups, with (23.27) explaining the result afterward.

Genericity is not preserved as a literal property: $D_K^\times$ has no unipotent subgroup and hence no Whittaker model. Spherical vectors are not preserved: an unramified Steinberg twist has no $\mathrm{GL}_2(\mathcal O)$-fixed vector, while its reduced-norm character is fixed by $\mathcal O_D^\times$. Newvectors are not transported, and raw congruence levels require the class-specific translation just described. The regular-elliptic character relation (23.24) replaces these nonexistent comparisons.

Under base change, by contrast, the parameter is restricted. Central characters, twists, and duals are transported functorially by norms. Conductor is preserved for unramified extension but must otherwise be recomputed from ramification. Euler and epsilon factors transform by (22.15), (22.17), and (22.18); they are not usually numerically unchanged. Cuspidality can disappear when an elliptic torus splits.

Thus the two transfer operations have different logical forms. Selected Jacquet--Langlands has now been constructed by explicit division types and a character calculation and preserves the common invariant package. Selected base change was constructed by restriction and transforms that package according to the ramification and Mackey formulas.

## 24. Worked parameter calculations and final synthesis

### 24.1 An unramified principal series

Let $K=\mathbf Q_p$, let $\chi_1,\chi_2$ be unramified, and put

$$
\alpha=\chi_1(p),
\qquad
\beta=\chi_2(p).
$$

If $\alpha/\beta\notin\{p,p^{-1}\}$, the principal series is irreducible, spherical, and has parameter $\chi_1\oplus\chi_2$. Its conductor is zero, its newvector is the spherical line, and

$$
L(s,\pi)=
\frac1{(1-\alpha p^{-s})(1-\beta p^{-s})}.
$$

For conductor-zero $\psi$, its epsilon factor is one. Under the unramified extension of residue degree $f$, its roots become $\alpha^f,\beta^f$ and

$$
L_M(s,\operatorname{BC}_{M/K}\pi)
=\frac1{(1-\alpha^f p^{-fs})(1-\beta^f p^{-fs})}.
$$

This example exhibits the difference between preservation and functorial transformation: base change preserves the rule, not the literal polynomial.

### 24.2 The two objects at the reducibility wall

Let $\mu$ be unramified and put $a=\mu(p)$. The character $\mu\circ\det$ and $\operatorname{St}\otimes\mu$ have the same semisimple Weil action

$$
\mu\nu^{1/2}\oplus\mu\nu^{-1/2}.
$$

For the character, $N=0$; its conductor is zero and it has two Euler roots. For Steinberg, $N\ne0$; its conductor is one and

$$
L(s,\operatorname{St}\otimes\mu)
=(1-a p^{-s-1/2})^{-1},
$$

$$
\epsilon(s,\operatorname{St}\otimes\mu,\psi)
=-a p^{1/2-s}.
$$

Theorem 23.5 sends the latter, but not the former, to the character $\mu\circ\operatorname{Nrd}$ of the division algebra. Proposition 23.4 proves the required character sign, and Theorem 23.6 proves equality of conductors and local factors. The example simultaneously tests reducibility, monodromy, conductor, local factors, and the discrete-series boundary.

### 24.3 An unramified quadratic dihedral representation

Let $L/K$ be unramified quadratic and let $\theta$ have conductor one with regular residue character. Then

$$
a_K(\operatorname{AI}_{L/K}(\theta))=2,
\qquad
L(s,\operatorname{AI}_{L/K}(\theta))=1.
$$

The first newvector is fixed by $\mathcal K_1(\mathfrak p^2)$ and has diagonal Kirillov function $\mathbf1_{\mathcal O^\times}$. Its parameter is $\operatorname{Ind}_{W_L}^{W_K}\theta$, and its determinant is

$$
\theta|_{K^\times}\omega_{L/K}.
$$

The rectifier in (20.6) is what makes this equal to the central character. For conductor-zero $\psi$, $\lambda(L/K,\psi)=1$, so

$$
\epsilon_K(s,\pi,\psi)
=\epsilon_L(s,\theta,\psi\circ\operatorname{Tr}_{L/K}).
$$

Base change to $L$ splits the parameter into $\theta\oplus\theta^\tau$ and therefore turns the supercuspidal into a principal series. Jacquet--Langlands, by contrast, keeps the parameter unchanged and carries it to the constructed quaternionic dihedral representation $\rho_D(L,\theta)$; Lemma 23.3 proves the regular-character identity that distinguishes this statement from a parameter-only definition.

### 24.4 A tamely ramified quadratic example

Assume the residue characteristic is odd and let $L=K(\Pi)$ with $\Pi^2=u\varpi$ for a unit $u$. Then

$$
e(L/K)=2,
\qquad f(L/K)=1,
\qquad d(L/K)=1.
$$

Admissibility forces the genuinely quadratic information to occur on principal units. If $a_L(\theta)=2$, then

$$
a_K(\operatorname{AI}_{L/K}(\theta))=3.
$$

The Euler factor is one, but the epsilon factor is not trivial:

$$
\epsilon_K(s,\pi,\psi)
=\lambda(L/K,\psi)
\epsilon_L(s,\theta,\psi\circ\operatorname{Tr}_{L/K}).
$$

Here $\lambda$ is a normalized quadratic Gauss sum and can be a nontrivial fourth root of unity. The conductor records the size of the finite Fourier quotient; $\lambda$ records a phase invisible to that integer.

### 24.5 The complete reusable dictionary

The selected theory may now be summarized without suppressing any hypothesis.

| representation $\pi$ | condition | $\operatorname{rec}_2(\pi)$ | conductor | Euler factor |
|---|---|---|---|---|
| $I(\chi_1,\chi_2)$ | $\chi_1\chi_2^{-1}\ne\nu^{\pm1}$ | $\chi_1\oplus\chi_2$, $N=0$ | $a(\chi_1)+a(\chi_2)$ | $L(s,\chi_1)L(s,\chi_2)$ |
| $\mu\circ\det$ | nongeneric boundary | $\mu\nu^{1/2}\oplus\mu\nu^{-1/2}$, $N=0$ | $2a(\mu)$ | product of the two character factors |
| $\operatorname{St}\otimes\mu$ | generic boundary | $\operatorname{Sp}_2(\mu)$ | $1$ if $a(\mu)=0$, else $2a(\mu)$ | $L(s+1/2,\mu)$ |
| $\operatorname{AI}_{L/K}(\theta)$ | tame admissible quadratic pair | $\operatorname{Ind}_{W_L}^{W_K}\theta$ | $f(a_L(\theta)+d)$ | $1$ |

In every row the central character is the parameter determinant; determinant twist is tensor product; contragredient is dual; conductor is Artin plus monodromy defect; and representation-theoretic local factors equal the parameter factors. For every infinite-dimensional row, the common conductor is the first $\mathcal K_1$-level and the first fixed space is a line.

The selected discrete-series rows extend across the inner form as follows:

| split representation | division representation | common parameter |
|---|---|---|
| $\operatorname{St}\otimes\mu$ | $\mu\circ\operatorname{Nrd}$ | $\operatorname{Sp}_2(\mu)$ |
| $\operatorname{AI}_{L/K}(\theta)$ | $\rho_D(L,\theta)$ | $\operatorname{Ind}_{W_L}^{W_K}\theta$ |

Their regular characters differ by the sign $-1$, while their central characters, twists, duals, epsilon-conductors, Euler factors, epsilon factors, gamma factors, and root numbers agree. The split newvector line and the division maximal-order filtration are not identified.

The classification boundary is now exact. Principal series, special representations, and tame dihedral supercuspidals are completely constructed and matched. Primitive wild supercuspidals are excluded, as are wild quadratic type constructions in residue characteristic two. No theorem in the selected correspondence silently includes them.

### 24.6 Conclusion

The selected representation theory of $\mathrm{GL}_2(K)$ begins with two elementary geometries. The two Bruhat cells control induction, Jacquet modules, reducibility, and Whittaker functionals. The one-dimensional apartment in the lattice tree controls spherical Hecke operators, compact-mod-center support, and congruence level. In the selected range those geometries divide the irreducible representations into principal, character, special, and tame dihedral supercuspidal families.

Fourier analysis then makes the classification arithmetic. Whittaker uniqueness produces a canonical functional model. The Kirillov coordinate turns newvectors into a finite interval of valuation shells and turns the Weyl action into a local functional equation. The first nonempty interval gives the conductor; Mellin transforms of its tails give Euler factors; the reversal of the interval gives epsilon factors.

Weil--Deligne parameters explain why these calculations agree. Split character lines give principal series. The same centered lines joined by a nilpotent arrow give Steinberg. Two conjugate lines visible only over a quadratic extension give a dihedral supercuspidal, with the rectifier correcting the sign of induction. Determinants, duals, twists, conductors, Euler factors, and epsilon factors then match because each is computed from the same finite-dimensional object.

Finally, the parameter tells us exactly how the two local transfers differ. Base change restricts it, so norms transport characters, quadratic tori may split, and local factors obey induction--restriction product formulas. Selected Jacquet--Langlands was constructed directly from reduced-norm characters and tame quaternionic types. Its split--division Gauss calculation proves the negative regular-character identity, while its coefficient Fourier equation proves equality of conductors and local factors. The parameter is therefore unchanged as a theorem rather than as a definition, even though Whittaker, spherical, and newvector models are not literally comparable.

This is the durable content of the classification. A local representation is not merely assigned a family name. Its geometric origin, minimal level, Fourier equation, ramification, and transfer behavior are different visible shadows of one coherent local object.
