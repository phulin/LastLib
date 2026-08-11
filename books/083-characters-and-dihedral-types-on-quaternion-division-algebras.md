# Characters and Dihedral Types on Quaternion Division Algebras

## Contents

1. [The inner form at one place](#1-the-inner-form-at-one-place)
   - [Why the division group is the right laboratory](#11-why-the-division-group-is-the-right-laboratory)
   - [Standing conventions](#12-standing-conventions)
   - [The selected range and its boundary](#13-the-selected-range-and-its-boundary)
2. [The compact-mod-center geometry of $D^\times$](#2-the-compact-mod-center-geometry-of-dtimes)
   - [The valuation and the maximal order](#21-the-valuation-and-the-maximal-order)
   - [A cyclic model and its two valuation classes](#22-a-cyclic-model-and-its-two-valuation-classes)
   - [Quadratic tori and their normalizers](#23-quadratic-tori-and-their-normalizers)
   - [Finite dimensionality from compactness](#24-finite-dimensionality-from-compactness)
3. [Filtrations, duality, and leading characters](#3-filtrations-duality-and-leading-characters)
   - [Principal-unit layers](#31-principal-unit-layers)
   - [Reduced-trace duality](#32-reduced-trace-duality)
   - [Linearizing a multiplicative character](#33-linearizing-a-multiplicative-character)
   - [Why a noncentral leading term finds a quadratic field](#34-why-a-noncentral-leading-term-finds-a-quadratic-field)
4. [Admissible pairs and normalization](#4-admissible-pairs-and-normalization)
   - [Regularity and admissibility](#41-regularity-and-admissibility)
   - [Minimal pairs and norm twists](#42-minimal-pairs-and-norm-twists)
   - [Direct and quadratic-induction normalizations](#43-direct-and-quadratic-induction-normalizations)
   - [Equivalence of embedded data](#44-equivalence-of-embedded-data)
5. [Special representations on the division side](#5-special-representations-on-the-division-side)
   - [Reduced-norm characters](#51-reduced-norm-characters)
   - [Levels and conductors of special twists](#52-levels-and-conductors-of-special-twists)
   - [Characters, pairings, and the transfer sign](#53-characters-pairings-and-the-transfer-sign)
6. [Depth-zero dihedral types](#6-depth-zero-dihedral-types)
   - [The unramified torus in the residue algebra](#61-the-unramified-torus-in-the-residue-algebra)
   - [The index-two induction](#62-the-index-two-induction)
   - [Irreducibility and equivalence](#63-irreducibility-and-equivalence)
   - [A finite-field example and a failure of regularity](#64-a-finite-field-example-and-a-failure-of-regularity)
7. [Positive-depth quaternionic types](#7-positive-depth-quaternionic-types)
   - [The simple character](#71-the-simple-character)
   - [The Heisenberg enlargement](#72-the-heisenberg-enlargement)
   - [Extension to the compact-mod-center type](#73-extension-to-the-compact-mod-center-type)
   - [What tameness contributes](#74-what-tameness-contributes)
8. [Intertwining and compact induction](#8-intertwining-and-compact-induction)
   - [The intertwining calculation](#81-the-intertwining-calculation)
   - [Irreducibility](#82-irreducibility)
   - [Classification inside the selected class](#83-classification-inside-the-selected-class)
   - [Why induction from the bare torus is insufficient](#84-why-induction-from-the-bare-torus-is-insufficient)
9. [Levels and conductors](#9-levels-and-conductors)
   - [An intrinsic level on $D^\times$](#91-an-intrinsic-level-on-dtimes)
   - [The conductor formula for a quadratic pair](#92-the-conductor-formula-for-a-quadratic-pair)
   - [Unramified and ramified patterns](#93-unramified-and-ramified-patterns)
   - [Exact behavior under twists](#94-exact-behavior-under-twists)
10. [Regular conjugacy and character formulas](#10-regular-conjugacy-and-character-formulas)
    - [Every noncentral element is elliptic](#101-every-noncentral-element-is-elliptic)
    - [The exact induced-character formula](#102-the-exact-induced-character-formula)
    - [Depth-zero values](#103-depth-zero-values)
    - [Positive-depth Gauss traces](#104-positive-depth-gauss-traces)
    - [The near-central warning](#105-the-near-central-warning)
11. [Haar measures and the local comparison interface](#11-haar-measures-and-the-local-comparison-interface)
    - [Compatible quotient measures](#111-compatible-quotient-measures)
    - [Weyl discriminants and orbital integrals](#112-weyl-discriminants-and-orbital-integrals)
    - [The character sign on matching classes](#113-the-character-sign-on-matching-classes)
    - [What remains for local transfer](#114-what-remains-for-local-transfer)
12. [Central characters, contragredients, and twists](#12-central-characters-contragredients-and-twists)
    - [The central-character test](#121-the-central-character-test)
    - [Twist compatibility](#122-twist-compatibility)
    - [Contragredients and self-duality](#123-contragredients-and-self-duality)
    - [Recovering the admissible pair from the character](#124-recovering-the-admissible-pair-from-the-character)
13. [Invariant pairings and formal degree](#13-invariant-pairings-and-formal-degree)
    - [Pairings on an induced model](#131-pairings-on-an-induced-model)
    - [Schur orthogonality modulo the center](#132-schur-orthogonality-modulo-the-center)
    - [Toric multiplicity and conjugation](#133-toric-multiplicity-and-conjugation)
14. [Integral type lattices](#14-integral-type-lattices)
    - [Coefficient rings and integral inducing data](#141-coefficient-rings-and-integral-inducing-data)
    - [Finite free induction](#142-finite-free-induction)
    - [Dual lattices and integral pairings](#143-dual-lattices-and-integral-pairings)
    - [Reduction and the nonbanal warning](#144-reduction-and-the-nonbanal-warning)
15. [Examples, diagnostics, and exclusions](#15-examples-diagnostics-and-exclusions)
    - [Five quick calculations](#151-five-quick-calculations)
    - [A diagnostic table](#152-a-diagnostic-table)
    - [The primitive wild boundary](#153-the-primitive-wild-boundary)
16. [The quaternionic dihedral package](#16-the-quaternionic-dihedral-package)
    - [Construction theorem](#161-construction-theorem)
    - [Normalization checks](#162-normalization-checks)
    - [Conclusion](#163-conclusion)

## 1. The inner form at one place

### 1.1 Why the division group is the right laboratory

Let $F$ be a nonarchimedean local field of characteristic zero and let $D$ be the quaternion division algebra over $F$. The group $D^\times$ looks at first less accessible than $\operatorname{GL}_2(F)$ because its elements are not matrices over $F$. In representation theory it is, in an important sense, the smaller object. The quotient $D^\times/F^\times$ is compact. Consequently every irreducible smooth complex representation is finite-dimensional and has a central character, every inducing subgroup containing the center has finite index, and every character calculation reduces to a finite sum. The proof of the first assertion is included in Section 2.4; compactness modulo the center alone does not supply it without an argument.

This compactness does not make the theory trivial. It concentrates all the structure into three related questions. Which quadratic field inside $D$ carries the torus character? How far down the principal-unit filtration is that character visible? Which elements outside the chosen torus can intertwine it? The answers produce precisely the special and tame dihedral representations that correspond to the selected discrete series on $\operatorname{GL}_2(F)$.

The route has two endpoints. A character of $F^\times$, pulled back by the reduced norm, is the division-side companion of a special representation. A regular character of a quadratic extension, enlarged to a suitable compact-mod-center type and induced, is the companion of a quadratic-induced supercuspidal. The special and depth-zero formulas make the expected minus sign on matching regular elliptic classes visible. At positive depth this book supplies the exact division-side Gauss traces, while the cross-group sign comparison remains a separate transfer theorem.

### 1.2 Standing conventions

Write $\mathcal O=\mathcal O_F$, $\mathfrak p=(\varpi)$, let $v_F(\varpi)=1$, and let the residue field $k$ have cardinality $q$ and characteristic $p$. Reduced trace and reduced norm on $D$ are denoted by $\operatorname{Trd}$ and $\operatorname{Nrd}$. Put

$$
G=D^\times,\qquad Z=F^\times.
$$

Complex representations are smooth. When coefficients are changed, the coefficient field and its valuation ring will be stated. The general theory of smooth representations supplies induction from open subgroups, Mackey decomposition, intertwiners, contragredients, and finite-index trace formulas. The quaternion-algebra theory supplies local classification, reduced norm and trace, quadratic embeddings, and conjugacy of embeddings. The split-group tame theory supplies quadratic descent, minimal norm twists, trace-dual leading characters, and the character-dependent tame rectifier. All division-side filtrations, types, intertwining, conductors, and lattices used below are constructed here.

For a finite extension $L/F$, set

$$
U_L^0=\mathcal O_L^\times,qquad U_L^r=1+\mathfrak p_L^r\quad(r\geq1),
$$

and for a smooth character $\xi$ of $L^\times$ set

$$
a_L(\xi)=\min\{r\geq0:\xi|_{U_L^r}=1\}.
$$

Thus an unramified character has conductor exponent $0$, while a nontrivial residue-field character has exponent $1$.

Fix an additive character $\psi:F\to\mathbf C^\times$ trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. Put $\psi_D=\psi\circ\operatorname{Trd}$ and $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$. The additive measure on $F$ is self-dual for $\psi$. Multiplicative and quotient measures will be fixed in Chapter 11; no earlier pointwise character formula depends on their scale.

### 1.3 The selected range and its boundary

The quadratic constructions in this book use tame separable quadratic extensions. Hence every quadratic extension is allowed when $p\ne2$, and the unramified quadratic extension is allowed in every residue characteristic. Depth zero and tame positive depth are both included. Nonminimal characters are included by twisting a minimal pair.

Two exclusions must remain explicit. A ramified quadratic extension in residue characteristic two is wild and requires extra extension data not developed here. More decisively, a primitive wild representation is one whose first noncentral leading stratum is not obtained from a quadratic field character by the construction below. Such representations are not classified, constructed, or used here. Calling every irreducible representation of $D^\times$ “dihedral” would therefore be false in the excluded residue characteristics.

The word “packet” will be used sparingly. On the division side each datum constructed here gives one irreducible representation. The packet language records its relationship with the corresponding discrete-series datum on the split group, not a hidden multiplicity inside $D^\times$.

## 2. The compact-mod-center geometry of $D^\times$

### 2.1 The valuation and the maximal order

The reduced norm supplies the valuation that organizes the entire group:

$$
v_D(x)=v_F(\operatorname{Nrd}x),\qquad x\in D^\times.
$$

Its image is $\mathbf Z$, while $v_D(a)=2v_F(a)$ for $a\in F^\times$. Define

$$
\mathcal O_D=\{x\in D:v_D(x)\geq0\},\qquad
\mathfrak P_D=\{x\in D:v_D(x)\geq1\}.
$$

Then $\mathcal O_D$ is the unique maximal order of $D$, $\mathfrak P_D$ is its unique maximal two-sided ideal, and

$$
U_D^0=\mathcal O_D^\times,qquad U_D^r=1+\mathfrak P_D^r\quad(r\geq1)
$$

is a normal filtration of $G$. Conjugation invariance follows immediately from invariance of the reduced norm. This normality has a strong consequence used later: if an irreducible representation has one nonzero $U_D^r$-fixed vector, then $U_D^r$ acts trivially on the whole representation.

The valuation assertions can be checked in the cyclic model of the next section. If $x=a+b\Pi_D$, then

$$
\operatorname{Nrd}(x)=N_{F_2/F}(a)-\varpi N_{F_2/F}(b),
$$

and the two summands have valuations of opposite parity. They cannot cancel, so

$$
v_D(x)=\min\{2v_{F_2}(a),,2v_{F_2}(b)+1\}.
$$

This proves the valuation law, the image statement, and the descriptions of $\mathcal O_D$ and $\mathfrak P_D$ below. It also proves maximality: every element of an $\mathcal O$-order is integral over $\mathcal O$, hence has integral reduced norm and nonnegative $v_D$, so every order lies in $\mathcal O_D$. The elements of positive valuation form its unique maximal ideal. Thus none of the order structure is being inferred merely from notation.

Choose $\Pi_D\in D^\times$ with $v_D(\Pi_D)=1$. Every element is $\Pi_D^n u$ with $u\in\mathcal O_D^\times$, so

$$
D^\times=\bigsqcup_{n\in\mathbf Z}\Pi_D^n\mathcal O_D^\times.
$$

Since central elements have even $D$-valuation, only two valuation classes remain modulo $Z$. Thus $G/Z$ is the union of the images of $\mathcal O_D^\times$ and $\Pi_D\mathcal O_D^\times$, hence is compact.

### 2.2 A cyclic model and its two valuation classes

Let $F_2/F$ be the unramified quadratic extension, with Frobenius $\sigma$. There is a model

$$
D=F_2\oplus F_2\Pi_D,qquad
\Pi_D^2=\varpi,qquad
\Pi_D a=\sigma(a)\Pi_D.
$$

After multiplying $\Pi_D$ by a unit one can always arrange the displayed square. In this model

$$
\mathcal O_D=\mathcal O_{F_2}\oplus\mathcal O_{F_2}\Pi_D,qquad
\mathfrak P_D=\Pi_D\mathcal O_D,qquad
\mathcal O_D/\mathfrak P_D\simeq k_2,
$$

where $k_2/k$ is quadratic. Conjugation by $\Pi_D$ induces $x\mapsto x^q$ on $k_2$.

This model explains both depth-zero induction and the ubiquitous two conjugate character values. The subgroup $F_2^\times U_D^1$ consists of the even valuation class, while multiplication by $\Pi_D$ supplies the other class. The quotient

$$
D^\times/(F_2^\times U_D^1)
$$

has order two. A character of $k_2^\times$ and its Frobenius conjugate are therefore the two diagonal entries of an induced two-dimensional representation.

The model is a coordinate device, not additional structure. Any two unramified quadratic embeddings are conjugate in $D^\times$. The representation obtained from the model is consequently independent of its choice, up to isomorphism.

### 2.3 Quadratic tori and their normalizers

Every separable quadratic extension $E/F$ embeds in $D$. Its centralizer is exactly $E$ and hence

$$
C_G(E^\times)=E^\times.
$$

Indeed the centralizer has dimension two over $F$ by the central-simple dimension formula, and it already contains $E$. Conjugacy of embeddings shows that an $F$-automorphism of $E$ is implemented by an element of $G$. Therefore

$$
1\longrightarrow E^\times\longrightarrow N_G(E^\times)
\longrightarrow\operatorname{Gal}(E/F)\longrightarrow1.
$$

If $j_E$ maps to the nontrivial automorphism $\sigma$, then $j_Eej_E^{-1}=\sigma(e)$. This normalizer quotient is the source of the equivalence $\theta\sim\theta^\sigma$ and of the two-term character formula.

The quotient $E^\times/F^\times$ is compact. In the unramified case its valuation quotient is trivial; in the ramified case it has order two. Its unit quotient is compact in both cases. Consequently every open subgroup containing $E^\times$ is compact modulo $Z$ and has finite index in $G$.

### 2.4 Finite dimensionality from compactness

**Proposition 2.1.** Every irreducible smooth complex representation of $G$ has a central character and is finite-dimensional. If $J$ is open and contains $Z$, every compact induction from a finite-dimensional representation of $J$ is ordinary finite-index induction.

**Proof strategy.** First pass to a discrete quotient by a normal principal-unit subgroup. Its group algebra is finite over the Laurent algebra generated by a central uniformizer. A simple module over this finite algebra has a central character and is finite-dimensional. Compactness modulo the center then gives the elementary finite-orbit proof.

**Proof.** Choose $0\ne v\in V$. Smoothness and the fact that the groups $U_D^r$ form a neighborhood basis give $r$ with $v\in V^{U_D^r}$. Since $U_D^r$ is normal in $G$, the fixed space is $G$-stable and hence is all of $V$. Thus $V$ is a simple module over $A=\mathbf C[G/U_D^r]$.

Put $R=\mathbf C[Z/(Z\cap U_D^r)]$. Up to the finite unit quotient, $R$ is a Laurent polynomial algebra in the class of $\varpi$. The quotient $G/ZU_D^r$ is finite, so finitely many coset representatives span $A$ as an $R$-module. The standard determinant argument for an algebra finite over a central commutative ring now applies: the annihilator $\mathfrak m=\operatorname{Ann}_R(V)$ is maximal, $R/\mathfrak m$ is a finite algebraic extension of $\mathbf C$, hence is $\mathbf C$, and the cyclic module $V=Av$ is finite-dimensional over it. Therefore $Z$ acts through a smooth character $\omega$.

For clarity, the determinant argument can be seen without any finiteness theorem: if $\mathfrak m$ were contained properly in a maximal ideal $\mathfrak n$, then the finite $R$-module $V$ would have $V/\mathfrak nV\ne0$ by Nakayama. The subspace $\mathfrak nV$ is an $A$-submodule, so simplicity makes it zero; hence $\mathfrak n$ annihilates $V$, a contradiction. The residue field is generated over $\mathbf C$ by the image of the Laurent generator and is finite over $\mathbf C$, so it equals $\mathbf C$.

One may now also use compactness directly. Choose a compact open subgroup $K$ fixing $v$ and representatives $g_1,\ldots,g_m$ for $Z\backslash G/K$. Every translate of $v$ is a scalar multiple of one of $g_iv$. Their span is nonzero and $G$-stable, hence equals $V$.

If $J$ contains $Z$, its image is open in the compact group $G/Z$, so it has finite index. A function in the induced model has support on a finite coset set automatically; compact and ordinary induction coincide. $\square$

This proposition is the basic simplification peculiar to the division group. It also warns against importing infinite-dimensional intuition from the split group: a quaternionic dihedral representation can correspond to an infinite-dimensional supercuspidal while itself having finite dimension.

There is a second useful consequence. After fixing the central character, a finite-dimensional smooth representation factors through a finite quotient of a compact open subgroup together with one valuation operator. Indeed choose a basis, intersect its open stabilizers, and take the normal core inside $\mathcal O_D^\times$; the resulting open normal subgroup acts trivially. The remaining compact quotient is finite. This observation justifies ordinary finite-group trace arguments and the integral lattice constructions used later.

## 3. Filtrations, duality, and leading characters

### 3.1 Principal-unit layers

The filtration $U_D^r$ is the noncommutative analogue of the unit filtration of a local field. For $r\geq1$, multiplication gives

$$
(1+x)(1+y)\equiv1+x+y\pmod{\mathfrak P_D^{r+1}}
$$

when $x,y\in\mathfrak P_D^r$. Hence

$$
U_D^r/U_D^{r+1}\simeq
\mathfrak P_D^r/\mathfrak P_D^{r+1}
$$

as additive groups. Each quotient is one-dimensional over $k_2$ and two-dimensional over $k$. Conjugation by $\Pi_D$ acts through Frobenius, with a parity shift coming from the chosen generator of $\mathfrak P_D^r$.

Commutators move deeper:

$$
[U_D^r,U_D^s]\subseteq U_D^{r+s}.
$$

More precisely,

$$
[1+x,1+y]\equiv1+(xy-yx)\pmod{\mathfrak P_D^{r+s+1}}.
$$

This first commutator term is the alternating form behind the Heisenberg representation. It is also why merely extending a torus character by the trivial character on a large unit subgroup does not always work: the middle quotient can be nonabelian at exactly the visible depth.

### 3.2 Reduced-trace duality

The bilinear form

$$
(x,y)\longmapsto\psi_D(xy)
$$

is nondegenerate on the additive group of $D$. Its lattice annihilators satisfy

$$
(\mathfrak P_D^r)^\perp=\mathfrak P_D^{-r-1}.
$$

The shift by $-1$ is the inverse different of the maximal order. One can verify it in the cyclic model. Write $x=a+b\Pi_D$ and $y=c+d\Pi_D$. The scalar summand of $xy$ is $ac+b\sigma(d)\varpi$, so integrality of $\operatorname{Trd}(xy)$ for every $y\in\mathcal O_D$ requires $a\in\mathcal O_{F_2}$ and $b\in\varpi^{-1}\mathcal O_{F_2}$. Hence

$$
\mathcal O_D^\perp
=\mathcal O_{F_2}\oplus\varpi^{-1}\mathcal O_{F_2}\Pi_D
=\mathfrak P_D^{-1}.
$$

Multiplying either lattice by $\Pi_D^r$ and using cyclicity of reduced trace gives the general formula. The indices of the proposed annihilator and the actual annihilator agree, so no larger lattice can occur.

For an embedded quadratic field $E$, restriction is ordinary trace duality:

$$
(\mathfrak p_E^r)^\perp
=\mathfrak p_E^{-r-d(E/F)}
$$

under $\psi_E$, where $d(E/F)=v_E(\mathfrak D_{E/F})$. The distinction between the ambient inverse-different shift and $d(E/F)$ is crucial. The first belongs to the division algebra; the second belongs to the embedded field. Their comparison produces the conductor formula rather than an arbitrary convention.

There is also a useful intersection calculation. If $E/F$ is unramified, then $v_D(e)=2v_E(e)$ and

$$
\mathfrak P_D^r\cap E=\mathfrak p_E^{\lceil r/2\rceil}.
$$

If $E/F$ is ramified quadratic, then $v_D(e)=v_E(e)$ and

$$
\mathfrak P_D^r\cap E=\mathfrak p_E^r.
$$

These two formulas explain the residue-degree factor in the conductor calculation. An $E$-unit step costs two ambient half-steps in the unramified case and one in the ramified case.

### 3.3 Linearizing a multiplicative character

Suppose $\theta$ is a character of $E^\times$ with $a_E(\theta)=a>0$, and put $m=a-1$. On the deep half of the unit filtration, multiplication is additive to the required precision. There is then $\beta\in E^\times$, determined modulo the annihilator of $\mathfrak p_E^{\lfloor m/2\rfloor+1}$, such that

$$
\theta(1+x)=\psi_E(\beta x)
$$

for $x\in\mathfrak p_E^{\lfloor m/2\rfloor+1}$, and

$$
v_E(\beta)=-a-d(E/F).
$$

Indeed the annihilator of $\mathfrak p_E^r$ is $\mathfrak p_E^{-r-d(E/F)}$, and nontriviality on the last unit layer forces the displayed valuation. The purpose of $\beta$ is not to replace the whole character; it records its last nontrivial layer.

If $\theta$ is altered by a norm character $\chi\circ N_{E/F}$, then its leading coefficient is altered by a scalar from $F$. Indeed

$$
N_{E/F}(1+x)\equiv1+\operatorname{Tr}_{E/F}(x)
$$

on the relevant graded piece. Thus the genuinely quadratic information is the class of $\beta$ modulo the scalar line and the dual error lattice.

This explains minimality. A nonminimal pair has a leading coefficient whose scalar part can be cancelled by a character of $F^\times$. A minimal pair is one for which the final visible coefficient remains noncentral.

### 3.4 Why a noncentral leading term finds a quadratic field

**Lemma 3.1.** Let $\beta\in D\setminus F$. Then $F[\beta]$ is a separable quadratic field and $C_D(\beta)=F[\beta]$. For a minimal tame admissible pair, the leading class may be represented by such a $\beta\in E\setminus F$ with the valuation specified in Section 3.3.

**Proof.** The reduced characteristic polynomial of $\beta$ has degree two. If it split with a root in $F$, then $\beta$ would have a zero divisor after subtracting that root, impossible in a division algebra. Thus it is irreducible; characteristic zero makes it separable, and $F[\beta]$ is quadratic. The centralizer dimension formula gives dimension two for $C_D(\beta)$, forcing equality with $F[\beta]$.

For the final assertion, suppose every representative of the leading class were scalar at the decisive precision. The associated additive character would factor through $\operatorname{Tr}_{E/F}$. Tame trace surjectivity on the graded layer would lift it to a character of $F^\times$ whose norm pullback cancels the last layer of $\theta$, contradicting minimality. $\square$

The lemma is the conceptual heart of the positive-depth construction. Intertwining an additive character forces an element to preserve its centralizer. Thus the leading oscillation remembers the very quadratic torus from which the representation came.

## 4. Admissible pairs and normalization

### 4.1 Regularity and admissibility

Let $E/F$ be separable quadratic, with nontrivial automorphism $\sigma$, and let $\theta:E^\times\to\mathbf C^\times$ be smooth. Write $\theta^\sigma(x)=\theta(\sigma x)$. The pair $(E,\theta)$ is **admissible** when

1. $\theta\ne\theta^\sigma$;
2. if $\theta/\theta^\sigma$ is trivial on $U_E^1$, then $E/F$ is unramified.

The first condition excludes norm descent. Indeed $\theta=\theta^\sigma$ exactly when $\theta=\chi\circ N_{E/F}$ for some character $\chi$ of $F^\times$. The proof uses Hilbert's cyclic argument to identify $\ker N$ with elements $y/\sigma(y)$ and then extends a character from the open norm subgroup.

The second condition is a ramification safeguard. For a ramified torus, a character whose asymmetry appears only in valuation or residue data has extra normalizer intertwining; the expected positive-depth type is not obtained. For an unramified torus, asymmetry on $k_E^\times$ is exactly the regular depth-zero case.

Admissibility is unchanged by conjugating $\theta$ or multiplying it by a norm pullback. These two operations will account respectively for equivalence and twisting.

### 4.2 Minimal pairs and norm twists

A positive-depth admissible pair is **minimal** when no character $\chi$ of $F^\times$ lowers

$$
a_E\bigl(\theta(\chi\circ N_{E/F})^{-1}\bigr).
$$

Every tame admissible pair has a decomposition

$$
\theta=\theta_0(\chi\circ N_{E/F})
$$

with $\theta_0$ minimal. To prove it, cancel a norm-derived last layer whenever possible. The conductor strictly decreases, so the process terminates. Tame trace surjectivity ensures that an invariant additive character on the last layer really comes from $F$. The least conductor attained in the norm-twist orbit is intrinsic, even though $\theta_0$ and $\chi$ need not be unique.

This reduction is more than bookkeeping. The type is first constructed for $\theta_0$, where the leading centralizer calculation is sharp, and the original representation is then recovered by twisting with $\chi\circ\operatorname{Nrd}$.

### 4.3 Direct and quadratic-induction normalizations

There are two useful labels for the same geometric construction. In the **direct normalization**, the inducing type has the prescribed $\theta$-torus line and central character $\theta|_{F^\times}$. At depth zero the type is one-dimensional and literally restricts to $\theta$; at positive depth the Heisenberg action is also present, so scalar restriction would be false. In the **quadratic-induction normalization**, one replaces $\theta$ by

$$
\theta^\natural=\theta\Delta_{E/F,\theta},
$$

where $\Delta_{E/F,\theta}$ is the tame rectifier constructed in the quadratic-induction theory by its normalized finite Gauss sum. In the ramified case it genuinely depends on $\theta$; suppressing this dependence reverses some Gauss phases and is incompatible with duality. Its relevant properties are

$$
\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F},
$$

$$
\Delta_{E/F,\theta^\sigma}
=\Delta_{E/F,\theta}^\sigma,
\qquad
\Delta_{E/F,\theta(\chi\circ N)}
=\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta^{-1}}
=\Delta_{E/F,\theta}^{-1}.
$$

It does not change the conductor in the admissible range. Here $\omega_{E/F}$ is the quadratic character with kernel $N_{E/F}(E^\times)$. The rectifier is unramified when $E/F$ is unramified. When $E/F$ is tamely ramified, it has conductor at most one, whereas admissibility forces $a_E(\theta)\geq2$.

Rectification is injective on admissible equivalence classes. In the unramified case this is immediate from the fixed unramified rectifier. In the ramified case suppose, after identifying the fields, that

$$
\theta\Delta_{E/F,\theta}
=\theta'\Delta_{E/F,\theta'}.
$$

The two rectifiers have the same restriction to $\mathcal O_E^\times$ and to $F^\times$, so their ratio is either trivial or the unramified quadratic character $\nu$ of $E^\times$ trivial on $F^\times$. Hence $\theta'=\theta\nu$. The character $\nu$ is a norm pullback from the unramified quadratic character of $F^\times$. Norm-twist invariance of the rectifier gives $\Delta_{E/F,\theta'}=\Delta_{E/F,\theta}$, and the displayed equality then forces $\nu=1$. Conjugating the same argument proves

$$
\theta\Delta_{E/F,\theta}
\sim\theta'\Delta_{E'/F,\theta'}
\quad\Longleftrightarrow\quad
(E,\theta)\sim(E',\theta').
$$

We write

$$
\Pi_D^{\mathrm{dir}}(E,\theta)
\quad\text{and}\quad
\Pi_D(E,\theta)=\Pi_D^{\mathrm{dir}}(E,\theta^\natural).
$$

Then

$$
\omega_{\Pi_D^{\mathrm{dir}}}=\theta|_{F^\times},
\qquad
\omega_{\Pi_D}=\theta|_{F^\times}\omega_{E/F}.
$$

Keeping the subscript $\theta$ prevents two persistent errors: the determinant of a quadratic induced two-dimensional parameter contains $\omega_{E/F}$, and the ramified Gauss phase is not determined by $E/F$ alone. All character comparisons below use $\Pi_D(E,\theta)$ unless “direct” is explicitly written.

### 4.4 Equivalence of embedded data

Pairs $(E,\theta)$ and $(E',\theta')$ are equivalent if an $F$-isomorphism $i:E\to E'$ satisfies $\theta'=\theta\circ i^{-1}$. Once embedded in $D$, conjugacy of quadratic embeddings turns such an isomorphism into conjugation by an element of $G$. Thus equivalent pairs give conjugate types and isomorphic induced representations.

For fixed $E$, the equivalence orbit is $\{\theta,\theta^\sigma\}$. There is no choice of a preferred member: selecting one embedding of $E$ into $D$ selects one, and applying the normalizer element selects the other. Every invariant formula must therefore be symmetric in these two characters.

One should distinguish equivalence from twisting. Replacing $\theta$ by $\theta^\sigma$ changes only the presentation of the same representation. Replacing it by $\theta(\chi\circ N)$ usually changes the representation, although in a controlled way: it tensors by $\chi\circ\operatorname{Nrd}$. Finally, replacing $E$ by a nonisomorphic quadratic field changes the centralizer of the leading term and cannot be achieved by conjugation. These three operations—conjugation, twisting, and changing the torus—play different roles even when some elementary invariants happen to agree.

For example, an unramified pair and a ramified pair can have the same central character after a suitable twist. They are still inequivalent because their leading centralizer fields have different ramification. Likewise, equal conductor does not imply equivalence: many regular residue characters have conductor $1$ and produce distinct depth-zero representations. The character on regular torus elements, not the numerical conductor alone, separates them.

## 5. Special representations on the division side

### 5.1 Reduced-norm characters

For any smooth character $\chi:F^\times\to\mathbf C^\times$, define

$$
\operatorname{Sp}_D(\chi)=\chi\circ\operatorname{Nrd}.
$$

This is a one-dimensional irreducible representation of $G$. It is the division-side member attached to the special representation $\operatorname{St}\otimes\chi$ on the split group. Its central character is

$$
\operatorname{Sp}_D(\chi)(z)=\chi(z^2)=\chi^2(z),
$$

which agrees with the central character of $\operatorname{St}\otimes\chi$.

Reduced-norm surjectivity shows that $\operatorname{Sp}_D(\chi_1)\simeq\operatorname{Sp}_D(\chi_2)$ only when $\chi_1=\chi_2$. Thus the special family has no hidden quadratic ambiguity.

### 5.2 Levels and conductors of special twists

The reduced norm on unit layers satisfies

$$
\operatorname{Nrd}(U_D^r)=U_F^{\lceil r/2\rceil}\qquad(r\geq1).
$$

Containment follows by expanding $\operatorname{Nrd}(1+x)$ and using reduced-trace duality; surjectivity follows successively on graded quotients, with the quadratic term supplying the odd layers where the trace vanishes. Hensel lifting completes the passage from graded quotients to units.

Here is the graded calculation. In the cyclic model, for $x=a+b\Pi_D$ one has

$$
\operatorname{Nrd}(1+x)=1+\operatorname{Trd}(x)+\operatorname{Nrd}(x).
$$

If $r=2s$, an element of $\mathfrak P_D^r$ has scalar leading part $\varpi^sa$. If $r=2s-1$, its two leading summands are $\varpi^{s-1}b\Pi_D$ and $\varpi^sa$. The first has trace zero, while the second again has trace in $\mathfrak p^s$. In both cases the trace term fills $\mathfrak p^s/\mathfrak p^{s+1}$ because $\operatorname{Tr}_{k_2/k}$ is onto. The norm term is deeper except at $r=1$, where it lies in the same first layer but does not obstruct surjectivity because the independent scalar trace term already fills that layer. Thus the image begins at $U_F^s$. Induction down the complete filtration proves

$$
\operatorname{Nrd}(U_D^{2s-1})
=\operatorname{Nrd}(U_D^{2s})=U_F^s.
$$

This proof works in residue characteristic two as a norm statement; the later restriction at $p=2$ concerns ramified quadratic type data, not the reduced norm of $D$.

If $a_F(\chi)=m>0$, the least $r\geq1$ on which $\chi\circ\operatorname{Nrd}$ is trivial is $r=2m-1$. If $\chi$ is unramified, it is already trivial on $U_D^0$. The conductor convention of Chapter 9 therefore gives

$$
a_D(\operatorname{Sp}_D(\chi))=
\begin{cases}
1,&m=0,\\
2m,&m>0.
\end{cases}
$$

This is exactly the conductor of $\operatorname{St}\otimes\chi$. The exceptional unramified value $1$ is why “twice the character conductor” is not a uniform formula.

### 5.3 Characters, pairings, and the transfer sign

The trace character is simply

$$
\Theta_{\operatorname{Sp}_D(\chi)}(d)=\chi(\operatorname{Nrd}d).
$$

On a matching regular elliptic matrix $g$ with $\det g=\operatorname{Nrd}d$, the special character is

$$
\Theta_{\operatorname{St}\otimes\chi}(g)=-\chi(\det g).
$$

Hence the expected inner-form sign is already exact:

$$
\Theta_{\operatorname{St}\otimes\chi}(g)
=-\Theta_{\operatorname{Sp}_D(\chi)}(d).
$$

The pairing between $\operatorname{Sp}_D(\chi)$ and $\operatorname{Sp}_D(\chi^{-1})$ is ordinary multiplication. It becomes a positive invariant Hermitian form when $\chi$ is unitary. This elementary packet is the normalization anchor for every later sign.

## 6. Depth-zero dihedral types

### 6.1 The unramified torus in the residue algebra

Let $E/F$ be unramified quadratic and embed $E$ as the field $F_2$ in the cyclic model. Suppose $a_E(\theta)=1$ and let $\overline\theta:k_2^\times\to\mathbf C^\times$ be its residue character. Admissibility says

$$
\overline\theta\ne\overline\theta^q.
$$

Put $J=E^\times U_D^1$. Because $E^\times\cap U_D^1=U_E^1$, the rule

$$
\lambda_\theta(eu)=\theta(e),qquad e\in E^\times, u\in U_D^1,
$$

is well defined. The subgroup $J$ is normal of index two in $G$, and conjugation by $\Pi_D$ changes $\lambda_\theta$ to $\lambda_{\theta^\sigma}$.

The direct depth-zero representation is

$$
\Pi_D^{\mathrm{dir}}(E,\theta)
=\operatorname{Ind}_J^G\lambda_\theta.
$$

It has dimension two. In quadratic-induction normalization, replace $\theta$ by $\theta^\natural$.

### 6.2 The index-two induction

Choose coset representatives $1,\Pi_D$. In the induced model a vector is a pair $(v_0,v_1)$. For $e\in E^\times$,

$$
e\cdot(v_0,v_1)
=\bigl(\theta(e)v_0,\theta^\sigma(e)v_1\bigr),
$$

while $\Pi_D$ exchanges the two lines, up to the scalar forced by $\Pi_D^2=\varpi$. This gives the character without any integration:

$$
\Theta(e)=\theta(e)+\theta^\sigma(e),
\qquad e\in E^\times\setminus F^\times,
$$

and

$$
\Theta(g)=0,qquad g\notin J.
$$

At a central element $z$, the value is $2\theta(z)$ in direct normalization. These formulas also show that the construction depends on the unordered orbit $\{\theta,\theta^\sigma\}$.

### 6.3 Irreducibility and equivalence

**Theorem 6.1.** If $\overline\theta$ is regular, $\operatorname{Ind}_J^G\lambda_\theta$ is irreducible. Two such representations are isomorphic exactly when their admissible pairs are equivalent.

**Proof strategy.** For a normal subgroup of index two, restriction of an induced character is the direct sum of the character and its conjugate. Irreducibility is therefore the assertion that these two characters differ.

**Proof.** Mackey theory gives

$$
\operatorname{End}_G(\operatorname{Ind}_J^G\lambda_\theta)
\simeq
\operatorname{Hom}_J(\lambda_\theta,\lambda_\theta)
\oplus
\operatorname{Hom}_J(\lambda_\theta,\lambda_{\theta^\sigma}).
$$

The first summand is one-dimensional. The second vanishes because regularity is visible on $k_2^\times$. Hence the endomorphism algebra is scalar, and the finite-dimensional induced representation is irreducible.

An isomorphism between two such inductions identifies their restrictions to $J$, so the unordered pairs of characters agree after conjugating the embedded unramified tori. Conjugacy of embeddings then gives equivalence of admissible pairs. The converse was established in Section 4.4. $\square$

### 6.4 A finite-field example and a failure of regularity

Choose a generator of the character group of $k_2^\times$ and write $\overline\theta_m(x)=x^m$ after choosing compatible roots of unity. Frobenius sends $m$ to $qm$ modulo $q^2-1$. Regularity fails precisely when

$$
(q-1)m\equiv0\pmod{q^2-1},
$$

or equivalently when $q+1$ divides $m$. Every other $m$ gives a two-dimensional depth-zero representation, with $m$ and $qm$ giving the same one.

If $q+1$ divides $m$, the two characters in the restriction coincide. The induced representation is then reducible: $\lambda_\theta$ extends to $G$ in two ways, distinguished by the sign assigned to $\Pi_D$. This is an explicit counterexample to the claim that induction from an index-two subgroup is automatically irreducible. Regularity, not index, is decisive.

## 7. Positive-depth quaternionic types

### 7.1 The simple character

Let $(E,\theta)$ be a minimal tame admissible pair of positive depth and choose a noncentral leading element $\beta\in E$ as in Chapter 3. The construction begins on a deep subgroup where the formula

$$
1+x\longmapsto\psi_D(\beta x)
$$

is multiplicative. Put

$$
n=-v_D(\beta),\qquad
r_H=\left\lfloor\frac n2\right\rfloor+1,
\qquad
r_J=\left\lfloor\frac{n+1}{2}\right\rfloor,
$$

and define

$$
H^1=U_E^1U_D^{r_H},
\qquad
J^1=U_E^1U_D^{r_J}.
$$

The product notation denotes subgroups: $E^\times$ normalizes every $U_D^r$, and $U_E^1$ lies in $U_D^1$. On $H^1$ set

$$
\vartheta_\beta\bigl(u(1+x)\bigr)
=\theta(u)\psi_D(\beta x),
\qquad
u\in U_E^1,\qquad x\in\mathfrak P_D^{r_H}.
$$

This is well defined. On the intersection of the two factors it is exactly the trace-dual formula of Section 3.3, while products $xy$ and the commutators needed to change a factorization lie in the annihilator of $\beta$ by the definition of $r_H$. Thus the displayed rule is a character.

The floor formulas are interpreted using the two different intersection laws

$$
\mathfrak P_D^r\cap E=
\begin{cases}
\mathfrak p_E^{\lceil r/2\rceil},&E/F\text{ unramified},\\
\mathfrak p_E^r,&E/F\text{ ramified}.
\end{cases}
$$

and the equality $v_D|_{E^\times}=2v_E$ in the unramified case and $v_D|_{E^\times}=v_E$ in the ramified case. Substitution of $v_E(\beta)=-a_E(\theta)-d(E/F)$ verifies the agreement and multiplicativity separately in the two cases. Minimality says that the preceding visible layer is noncentral, so the datum retains rather than erases the field $E$.

### 7.2 The Heisenberg enlargement

The floor inequalities and the commutator estimate of Section 3.1 give $H^1\triangleleft J^1$ and $[J^1,J^1]\subseteq H^1$. The subgroup $J^1$ normalizes $\vartheta_\beta$. On the finite abelian quotient $J^1/H^1$, define

$$
\langle \bar x,\bar y\rangle_\beta
=\vartheta_\beta([x,y]).
$$

This is alternating. Its radical would consist of a leading class commuting with $\beta$; by Lemma 3.1 that centralizer is $E$, and the $E$-part has already been absorbed into $H^1$. Hence the form is nondegenerate.

**Proposition 7.1.** There is a unique irreducible representation $\eta_\beta$ of $J^1$ containing $\vartheta_\beta$. Its dimension is

$$
\dim\eta_\beta=[J^1:H^1]^{1/2}.
$$

**Proof strategy.** Choose a maximal isotropic subgroup and induce an extension of $\vartheta_\beta$. Nondegeneracy makes the induced representation irreducible and independent of the polarization.

**Proof.** Let $L/H^1$ be maximal isotropic. The character extends from $H^1$ to $L$ because commutators in $L$ lie in its kernel and $\mathbf C^\times$ is divisible, so a character of the resulting abelian subgroup extends across the finite quotient. Induce that extension to $J^1$. Mackey's criterion says that an element intertwines the extension only when its class lies in the orthogonal complement of $L/H^1$, which equals $L/H^1$. Thus the induction is irreducible. Its dimension is $[J^1:L]$, whose square is $[J^1:H^1]$. Any two maximal isotropic choices yield irreducibles with the same central character, and the finite Heisenberg uniqueness argument identifies them. $\square$

When $J^1=H^1$, there is no noncommutative middle layer and $\eta_\beta=\vartheta_\beta$. Keeping this degenerate-looking case is important at the first positive level.

### 7.3 Extension to the compact-mod-center type

Put

$$
J=E^\times J^1.
$$

The group $E^\times$ normalizes the filtration and the simple character. The Heisenberg representation therefore extends to a representation $\Lambda_\theta$ of $J$ whose restriction to $E^\times$ contains the prescribed character and whose central action is $\theta|_{F^\times}$ in direct normalization.

**Proposition 7.2.** Under the minimal tame hypotheses, such an extension exists and is unique after the value on $E^\times$ and the fixed tame normalization are imposed.

**Proof strategy.** Conjugation by $E^\times$ acts symplectically on $J^1/H^1$. Lift that finite symplectic action to the Heisenberg model, then remove the remaining scalar cocycle using the prescribed torus character.

**Proof.** Uniqueness of $\eta_\beta$ gives an intertwining operator for every $e\in E^\times$, unique up to scalar. These operators define a projective action. The quotient that acts nontrivially after $F^\times U_E^1$ is removed is cyclic: it is $k_E^\times/k^\times$ of order $q+1$ in the unramified case and the valuation quotient of order two in the ramified case. Both orders are prime to $p$ in the tame range. A projective representation of a cyclic group is linearized by rescaling the operator attached to a generator so that its defining power relation holds. The Heisenberg model supplies the action of the pro-$p$ part.

Two linearizations differ by a character of $E^\times/(E^\times\cap J^1)$. Prescribing the torus character $\theta$ and its value on $F^\times$ removes this ambiguity. The resulting action together with $\eta_\beta$ is $\Lambda_\theta$. Changing $\beta$ within the trace-dual coset that defines the same simple character changes neither the Heisenberg representation nor the normalized cyclic operator, so it gives an isomorphic type. $\square$

The direct quaternionic type is $(J,\Lambda_\theta)$. For quadratic-induction normalization it is $(J,\Lambda_{\theta^\natural})$.

### 7.4 What tameness contributes

Tameness enters three times and nowhere cosmetically. First, trace on the decisive graded quotient is nonzero, so a norm-derived leading term can be removed. Second, centralizers lift from the graded algebra without inseparable collapse. Third, the projective extension of the Heisenberg representation can be normalized through a quotient whose prime-to-$p$ part is controlled.

In residue characteristic two, an unramified quadratic extension remains tame and the depth-zero construction works unchanged. A ramified quadratic extension is wild: trace can vanish on the layer where it was used above, and the extension scalar is no longer determined by this argument. The correct conclusion is not that no representations exist, but that the present type datum does not construct them.

## 8. Intertwining and compact induction

### 8.1 The intertwining calculation

For a representation $\Lambda$ of $J$, define

$$
I_G(\Lambda)=
\left\{g\in G:
\operatorname{Hom}_{J\cap g^{-1}Jg}
(\Lambda,\Lambda^g)\ne0
\right\}.
$$

Here $\Lambda^g$ is a representation of $g^{-1}Jg$ and

$$
\Lambda^g(x)=\Lambda(gxg^{-1}).
$$

This is the conjugation convention of the general smooth theory; using $gJg^{-1}$ with the same superscript would reverse the variance.

**Theorem 8.1.** For a positive-depth minimal tame type,

$$
I_G(\Lambda_\theta)=J.
$$

**Proof strategy.** Restrict an intertwiner to the last visible unit layer. It must preserve the leading additive character, hence the centralizer field $E$. The normalizer ambiguity is then tested against $\theta/\theta^\sigma$, and the remaining congruence error is eliminated one layer at a time by the nondegenerate commutator form.

**Proof.** Let $g$ intertwine $\Lambda_\theta$. On a sufficiently deep common subgroup, equality of the simple characters gives

$$
\psi_D(\beta x)=\psi_D(g^{-1}\beta gx)
$$

for every $x$ in a trace-dual test lattice. Thus $g^{-1}\beta g$ agrees with $\beta$ to the precision that determines its centralizer. The lifting step is explicit. On each relevant quotient of the $\mathfrak P_D$-filtration, the kernel of

$$
\operatorname{ad}(\beta):x\longmapsto\beta x-x\beta
$$

is the image of $E$; this is the graded cyclic-model form of $C_D(\beta)=E$, and tameness keeps the two conjugate directions distinct on the decisive layer. The commutator map is therefore invertible on a complementary graded line. If a representative normalizes $E$ modulo $\mathfrak P_D^t$, solve the corresponding linear commutator equation on that complement and multiply by $1+h$, with $h\in\mathfrak P_D^t$, to improve the congruence by one layer. Completeness iterates this correction to the depth defining $J^1$. Hence $g$, modulo $J^1$, lies in $N_G(E^\times)$.

If its normalizer image is $\sigma$, intertwining on $E^\times\cap J$ would identify the last genuinely quadratic layer of $\theta$ with that of $\theta^\sigma$. Admissibility rules this out. Hence, after left multiplication by $E^\times$, the element is congruent to $1$.

Suppose its first nontrivial class lies outside $J^1$. Commuting with elements of the complementary filtration produces a nontrivial character in the form $\langle\ ,\ \rangle_\beta$. Nondegeneracy supplies a test element on which the two restrictions differ, contradicting intertwining. Repeating through the finite number of layers forces the error into $J^1$. Therefore $g\in E^\times J^1=J$. The reverse inclusion is immediate. $\square$

### 8.2 Irreducibility

Define

$$
\Pi_D^{\mathrm{dir}}(E,\theta)
=\operatorname{c\mbox{-}Ind}_J^G\Lambda_\theta.
$$

Because $J$ contains $Z$ and is open, this is finite-index induction. The endomorphism algebra decomposes over $J\backslash G/J$, and the summand at $JgJ$ is precisely the intertwining space at $g$. Theorem 8.1 leaves only the identity double coset, where Schur's lemma gives the scalars. Thus the endomorphism algebra is one-dimensional.

It remains to justify the semisimplicity needed here; a scalar endomorphism algebra alone would not suffice. The induced representation is trivial on some normal $U_D^s$, and the center acts by scalars. The quotient $G/ZU_D^s$ is finite. Invariant subspaces are therefore exactly invariant subspaces for a finite group acting projectively, or equivalently for its finite central extension. Maschke's theorem makes this category semisimple in characteristic zero. A semisimple reducible representation has a nonscalar projection onto a proper summand, so the one-dimensional endomorphism algebra forces irreducibility. We have proved:

**Theorem 8.2.** The compact induction attached to a minimal tame admissible pair is irreducible. The same holds for every tame admissible pair after norm twisting, and

$$
\Pi_D(E,\theta)=
\Pi_D^{\mathrm{dir}}(E,\theta^\natural)
$$

is the quadratic-induction-normalized representation.

More explicitly, if $\theta=\theta_0(\chi\circ N_{E/F})$ with $\theta_0$ minimal, set

$$
J_\theta=J_{\theta_0},
\qquad
\Lambda_\theta
=\Lambda_{\theta_0}\otimes(\chi\circ\operatorname{Nrd})|_{J_{\theta_0}}.
$$

Different minimal decompositions give isomorphic types: their quotient is a norm character, and the displayed tensor identity identifies the two actions on both $E^\times$ and the principal-unit subgroup. This defines the notation $\Lambda_\theta$ for every tame admissible pair. Since the rectifier is invariant under norm twists, the same definition applies without ambiguity to $\theta^\natural$.

### 8.3 Classification inside the selected class

**Theorem 8.3.** Two direct-normalized depth-zero or positive-depth tame quadratic representations are isomorphic if and only if their admissible pairs are equivalent. The same assertion holds for the quadratic-induction-normalized representations labeled by the original pairs. Conversely, every irreducible representation containing one of the quaternionic types constructed in Chapters 6 and 7 arises from its admissible pair.

**Proof strategy.** Restriction and Mackey theory turn an isomorphism into an intertwiner between two types. The leading character recovers the quadratic centralizer, and the torus restriction recovers the character up to conjugation.

**Proof.** If the direct-normalized induced representations are isomorphic, Frobenius reciprocity gives a nonzero intertwiner between one type and a conjugate of the other. At depth zero, the residue-field restriction recovers the regular Frobenius orbit. At positive depth, equality on the last unit layer makes the leading elements conjugate, hence makes their centralizer fields conjugate. After identifying the fields, the type extension restricts to either $\theta$ or $\theta^\sigma$. Thus the pairs are equivalent. The converse follows by conjugating the embedded datum.

For quadratic-induction normalization, apply the direct assertion to $\theta^\natural$ and $(\theta')^\natural$, then use the invertibility of rectification proved in Section 4.3. The final assertion is immediate from Frobenius reciprocity and Theorem 8.1. $\square$

The qualification “containing one of the constructed types” is essential. The theorem is an exact classification of the selected tame quadratic class, not a classification of primitive wild representations.

### 8.4 Why induction from the bare torus is insufficient

Since $E^\times/Z$ is compact, it is tempting to induce $\theta$ directly from $E^\times$. That subgroup is not open, so the usual smooth compact-induction model has continuous families of nearby cosets rather than a finite type calculation. More seriously, the bare character does not record the leading commutator behavior. Elements close to $E^\times$ can intertwine it without belonging to its normalizer.

The subgroup $J^1$ repairs both problems. It makes $J=E^\times J^1$ open and encodes the last nontrivial unit layer. The Heisenberg representation then forbids precisely the extra intertwiners. Compactness of the torus is necessary, but the congruence neighborhood is what makes induction irreducible.

## 9. Levels and conductors

### 9.1 An intrinsic level on $D^\times$

For an irreducible representation $\Pi$ of $G$, define its normalized level by

$$
\ell_D(\Pi)=
\begin{cases}
-1,&\Pi|_{U_D^0}=1,\\
\min\{r\geq0:\Pi|_{U_D^{r+1}}=1\},&\text{otherwise}.
\end{cases}
$$

Because every $U_D^r$ is normal, “acts trivially” may equivalently be replaced by “has a nonzero fixed vector.” Define the conductor exponent

$$
a_D(\Pi)=\ell_D(\Pi)+2.
$$

The shift is not arbitrary. The unramified reduced-norm character then has conductor $1$, depth-zero dihedral representations have conductor $2$, and positive-depth pair conductors agree with their split companions. This is the normalization used in local comparison.

The convention also clarifies the difference between depth and conductor. A depth-zero dihedral representation is trivial on $U_D^1$ but not on $U_D^0$, so $\ell_D=0$ and $a_D=2$. An unramified special character is already trivial on $U_D^0$, so it receives the exceptional level $-1$ and conductor $1$. Calling both objects “level zero” would erase the distinction between the special and supercuspidal blocks.

Because $U_D^r$ is normal, the level can be read from any nonzero vector. There is no separate newvector multiplicity problem on the division side: once one vector is fixed, the entire irreducible representation is fixed. What replaces a newvector is the distinguished type or toric line inside restriction to $J$, treated in Chapters 13 and 14.

### 9.2 The conductor formula for a quadratic pair

**Theorem 9.1.** Let $(E,\theta)$ be a tame admissible pair in quadratic-induction normalization. Then

$$
\boxed{
a_D(\Pi_D(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).
}
$$

The same formula holds in direct normalization because the rectifier does not change the conductor in the admissible range.

**Proof strategy.** Find the first ambient unit group contained in the kernel of the type. The $E$-part is controlled by $a_E(\theta)$; comparing $E$-trace duality with $D$-trace duality contributes the discriminant shift.

**Proof.** Restriction of the type to the last visible subgroup contains $x\mapsto\psi_D(\beta x)$. It is trivial on $U_D^r$ exactly when $\mathfrak P_D^r$ lies in the annihilator of $\beta$ and its intersection with $E$ lies in the kernel of $\theta$. By Section 3.2, moving one $E$-unit layer changes the $F$-length by $f(E/F)$, while the trace-dual origin is displaced by $v_F(\mathfrak d_{E/F})$.

Put

$$
r_0=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta)-1.
$$

The intersection formulas show directly that $U_D^{r_0}\cap E=U_E^{a_E(\theta)}$: for an unramified pair, $r_0=2a_E(\theta)-1$; for a tame ramified pair, $r_0=a_E(\theta)$. At this stage both the torus character and the ambient simple character vanish. The Heisenberg quotient causes no further shift: its nontrivial commutator character persists exactly until this annihilator threshold and vanishes at it. For a minimal pair, minimality shows nontriviality on $U_D^{r_0-1}$.

For a nonminimal pair, write $\theta=\theta_0(\chi\circ N_{E/F})$ with $\theta_0$ minimal. Tensoring the inducing type by $\chi\circ\operatorname{Nrd}$ replaces its torus restriction by the actual product $\theta$ and replaces the scalar leading term by the sum of the two leading functionals. Repeating the same annihilator test therefore uses $a_E(\theta)$, including any cancellation, rather than $a_E(\theta_0)$. It gives the same triviality and nontriviality assertions with the displayed $r_0$. Hence $\ell_D=r_0-1$, and $a_D=\ell_D+2=r_0+1$, which is the formula. $\square$

This argument also proves that the formula is intrinsic, although its right side is expressed using an admissible pair.

### 9.3 Unramified and ramified patterns

If $E/F$ is unramified, then $v_F(\mathfrak d_{E/F})=0$ and $f(E/F)=2$, so

$$
a_D(\Pi_D(E,\theta))=2a_E(\theta).
$$

The depth-zero case $a_E(\theta)=1$ gives conductor $2$; positive-depth conductors are even.

If $E/F$ is tamely ramified quadratic, then $v_F(\mathfrak d_{E/F})=1$ and $f(E/F)=1$, so

$$
a_D(\Pi_D(E,\theta))=a_E(\theta)+1.
$$

Admissibility forces $a_E(\theta)\geq2$, so the first such conductor is $3$. The parity pattern is a useful diagnostic for a minimal pair, but it is not an invariant of an arbitrary twist orbit: twisting can change the visible conductor and can create cancellation.

### 9.4 Exact behavior under twists

Let $\chi$ be a character of $F^\times$. Since $\operatorname{Nrd}|_{E^\times}=N_{E/F}$,

$$
\boxed{
\Pi_D(E,\theta)\otimes(\chi\circ\operatorname{Nrd})
\simeq
\Pi_D(E,\theta(\chi\circ N_{E/F})).
}
$$

Consequently

$$
a_D\bigl(\Pi_D(E,\theta)\otimes(\chi\circ\operatorname{Nrd})\bigr)
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E\bigl(\theta(\chi\circ N_{E/F})\bigr).
$$

This exact expression is preferable to a maximum rule. If the two last-layer characters cancel, a twist can lower the conductor. For example, write $\theta=\theta_0(\chi^{-1}\circ N)$ with $\theta_0$ minimal but shallower. Twisting by $\chi$ exposes $\theta_0$ and strictly lowers the conductor. Two characters $\chi$ of equal conductor can therefore act differently on the same representation.

## 10. Regular conjugacy and character formulas

### 10.1 Every noncentral element is elliptic

For $d\in D^\times$, its reduced characteristic polynomial is

$$
P_d(X)=X^2-\operatorname{Trd}(d)X+\operatorname{Nrd}(d).
$$

If $d\notin F^\times$, this polynomial is irreducible over $F$: a root in $F$ would make $d-a$ a nonzero zero divisor. Thus $F[d]$ is a quadratic field and

$$
C_G(d)=F[d]^\times.
$$

Every noncentral element of $G$ is therefore regular elliptic. Two elements of $D^\times$ are conjugate exactly when they have the same reduced trace and norm. One direction is clear. For the other, identify their quadratic fields by sending one generator to the other and use conjugacy of embeddings.

This is simpler than regular conjugacy in $\operatorname{GL}_2(F)$, where split and elliptic classes coexist. The matching locus between the two groups consists precisely of elliptic matrices whose characteristic polynomial equals $P_d$.

### 10.2 The exact induced-character formula

Let $\Pi=\operatorname{Ind}_J^G\Lambda$ be any type constructed above. Since $J\backslash G$ is finite, its character at $g\in G$ is

$$
\boxed{
\Theta_\Pi(g)
=\sum_{x\in J\backslash G\atop xgx^{-1}\in J}
\operatorname{tr}\Lambda(xgx^{-1}).
}
$$

Terms may be organized by $J\backslash G/C_G(g)$ only after retaining the number of fixed left cosets represented by each double coset. The ungrouped formula counts each invariant induced summand once and is safest for computation.

**Proof.** Decompose the induced space as the direct sum of copies of the inducing space indexed by $J\backslash G$. The operator $g$ permutes these summands. A permuted cycle of length greater than one contributes zero to the trace. A coset $Jx$ is fixed exactly when $xgx^{-1}\in J$, and the trace on its fixed summand is $\operatorname{tr}\Lambda(xgx^{-1})$. Summing gives the formula. $\square$

There is no hidden volume factor: this is the trace of a finite-dimensional group operator. Haar measure enters only when the pointwise character represents the distribution $f\mapsto\operatorname{tr}\Pi(f)$.

For example, suppose $J$ has three left cosets with representatives $1,x,y$. If $g$ fixes the first and third cosets but exchanges the second with another coset, only two diagonal blocks remain, and

$$
\Theta_\Pi(g)=\operatorname{tr}\Lambda(g)
+\operatorname{tr}\Lambda(ygy^{-1}).
$$

This elementary permutation picture prevents two common mistakes. One must test conjugacy into $J$, not membership of $g$ in $J$ alone when $J$ is not normal; and one must not divide by the size or volume of a centralizer. Grouping into double cosets is convenient only after the multiplicity represented by the original left cosets has been retained.

If $f$ is locally constant and compactly supported, choose a normal compact open subgroup on which both $f$ and the representation are constant. Finite summation then gives

$$
\operatorname{tr}\Pi(f)
=\int_G f(g)\Theta_\Pi(g)\,d^\times g.
$$

This verifies directly that the finite trace function represents the distribution character with the chosen Haar measure.

### 10.3 Depth-zero values

For the depth-zero representation of Chapter 6, the formula becomes completely explicit. In direct normalization,

$$
\Theta_{\Pi_D^{\mathrm{dir}}(E,\theta)}(g)=
\begin{cases}
\lambda_\theta(g)+\lambda_\theta(\Pi_Dg\Pi_D^{-1}),
&g\in E^\times U_D^1,\\
0,&g\notin E^\times U_D^1.
\end{cases}
$$

The first line is well typed even when $g$ has a nontrivial $U_D^1$ component, since $\lambda_\theta$ is a character of the whole subgroup. For $g\in E^\times$ it becomes $\theta(g)+\theta^\sigma(g)$; with regular reduction this is $\overline\theta(\bar g)+\overline\theta(\bar g^q)$ times the central valuation scalar. On the split side the corresponding depth-zero cuspidal character at the matching elliptic element is the negative of this sum. The two formulas therefore have the required inner-form sign.

At a central element $z$, the value is $2\theta(z)$, not the two-term regular formula interpreted with two distinct conjugates. Central elements are singular and must be kept out of regular character identities.

### 10.4 Positive-depth Gauss traces

For a positive-depth type, the trace of $\Lambda_\theta$ is an exact finite Heisenberg trace. Choose a maximal isotropic subgroup $L/H^1$, extend $\vartheta_\beta$ to $L$, and use the induced basis indexed by $L\backslash J^1$. The matrices of $J^1$ are monomial. For $y_E\in E^\times$, the normalized cyclic operator from Proposition 7.2 is the unique, normalized solution $A_{y_E}$ of

$$
A_{y_E}\eta_\beta(h)
=\eta_\beta(y_Ehy_E^{-1})A_{y_E}
\qquad(h\in J^1).
$$

Thus for $y=y_Eh\in J$ one computes

$$
\boxed{
\operatorname{tr}\Lambda_\theta(y)
=\theta(y_E)\operatorname{tr}\bigl(A_{y_E}\eta_\beta(h)\bigr),
}
$$

where the quotient character implicit in the normalization of $A_{y_E}$ prevents double counting the action of $E^\times\cap J^1$. This is a finite linear system followed by a finite diagonal sum, hence an explicit Gauss-trace formula. Changing the polarization conjugates all matrices through the unique Heisenberg intertwiner and leaves the trace unchanged. A bare average of $\vartheta_\beta([y,x])$ over an isotropic space would in general give the wrong trace because it omits the permutation and extension operators.

Suppose $g\in E^\times$ is regular and its conjugacy class meets $J$ only through the two normalizer embeddings. Then the exact induced formula reduces to

$$
\boxed{
\Theta_{\Pi_D^{\mathrm{dir}}(E,\theta)}(g)
=\operatorname{tr}\Lambda_\theta(g)
+\operatorname{tr}\Lambda_\theta(g^\sigma).
}
$$

Thus the regular value is a sum of two conjugate torus values weighted by explicit finite Gauss traces. In quadratic-induction normalization replace $\theta$ by $\theta^\natural$. This is the form needed for term-by-term comparison with the split type.

### 10.5 The near-central warning

The two-term formula is not valid at every noncentral element merely because every such element is regular. If $g$ is sufficiently close to the center, its conjugacy class can meet $J$ through additional congruence embeddings. The exact formula of Section 10.2 then has more terms. Dropping them produces a character that fails local constancy near the singular set.

There is a reliable procedure: determine $F[g]$, enumerate the finite double-coset set

$$
J\backslash\{x\in G:xgx^{-1}\in J\}/F[g]^\times,
$$

and evaluate the finite traces. Away from the near-central range this set has the two normalizer representatives; inside it, the additional representatives encode the depth-dependent correction. The finite algorithm, rather than an unjustified universal two-term slogan, is the full regular-elliptic character formula.

## 11. Haar measures and the local comparison interface

### 11.1 Compatible quotient measures

Fix multiplicative Haar measures by

$$
\operatorname{vol}(\mathcal O_F^\times,d^\times z)=1,
\qquad
\operatorname{vol}(\mathcal O_D^\times,d^\times d)=1.
$$

For every quadratic extension $E/F$, normalize $d^\times e$ by $\operatorname{vol}(\mathcal O_E^\times)=1$. When the same $E^\times$ is viewed as a centralizer in $D^\times$ or in $\operatorname{GL}_2(F)$, use this same measure. Quotient measures are defined by Weil's formula, for example

$$
\int_{D^\times}\Phi(d)\,d^\times d
=\int_{E^\times\backslash D^\times}
\int_{E^\times}\Phi(ed)\,d^\times e\,d\dot d.
$$

One should not separately declare every quotient compact subgroup to have volume one; those declarations can conflict with Weil's formula. The three unit normalizations above, followed by quotient construction, are sufficient.

If a central character is fixed, use the quotient measure on $G/Z$ induced from $d^\times d$ and $d^\times z$. Formal degrees and matrix-coefficient pairings in Chapter 13 refer to this measure.

### 11.2 Weyl discriminants and orbital integrals

For regular $d\in D^\times$, define

$$
\Delta(d)=\operatorname{Trd}(d)^2-4\operatorname{Nrd}(d)
$$

and

$$
D_G(d)=\left|\frac{\Delta(d)}{\operatorname{Nrd}(d)}\right|_F.
$$

If $g\in\operatorname{GL}_2(F)$ matches $d$, then trace and determinant equality gives $D_{\operatorname{GL}_2}(g)=D_G(d)$. This common discriminant is the normalization factor used when passing between ordinary and normalized orbital integrals.

With centralizer measure fixed as above, set

$$
O_d(f)=\int_{E^\times\backslash D^\times}
f(x^{-1}dx)\,d\dot x,
$$

and similarly on the split group. A normalized orbital integral is $D_G(d)^{1/2}O_d(f)$. Matching test functions must use the same choice—ordinary or normalized—on both sides. Mixing them inserts an unwanted factor $D_G(d)^{1/2}$ into the character identity.

### 11.3 The character sign on matching classes

For matching regular elliptic elements $g$ and $d$, the desired pointwise identity is

$$
\boxed{
\Theta_{\pi}(g)=-\Theta_{\Pi_D}(d).
}
$$

The sign is $(-1)^{2-1}=-1$. The special calculation of Section 5.3 fixes it. At depth zero, the split finite cuspidal value is minus the two torus characters while the division value is plus their sum. These two families prove the identity directly.

This identity is pointwise and is unaffected by rescaling Haar measure. Its distributional consequence is measure-sensitive because both convolution operators and orbital integrals contain measures. That is why the preceding normalizations are part of the theorem's data rather than decorative preliminaries.

At positive depth the present book has constructed both the exact division-side trace matrices and the rectifier normalization, but it has not identified them with the split-side matrices. The displayed identity is therefore the comparison target there, not an input and not yet a theorem. In particular no sign is inferred from an unspecified “orientation” of complementary spaces.

### 11.4 What remains for local transfer

The present book supplies the division-side inputs: representations, exact induced-character algorithms, special and depth-zero signs, positive-depth Gauss traces, central characters, conductors, twists, pairings, and integral lattices. To obtain the full local correspondence one must additionally prove that the split and division Gauss traces agree with the displayed sign on every regular range, including the near-central correction terms, and then show that this character identity uniquely determines the representation.

That comparison is a separate theorem because it simultaneously involves both groups and their matching orbital integrals. Nothing here assumes it as a definition. The formulas above make it a finite calculation with fixed measures and the character-dependent rectifier.

## 12. Central characters, contragredients, and twists

### 12.1 The central-character test

In direct normalization,

$$
\omega_{\Pi_D^{\mathrm{dir}}(E,\theta)}=\theta|_{F^\times}.
$$

In quadratic-induction normalization,

$$
\boxed{
\omega_{\Pi_D(E,\theta)}
=\theta|_{F^\times}\omega_{E/F}.
}
$$

This follows by restricting the inducing type to $Z$ and using $\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F}$. It agrees with the determinant of the quadratic induced datum. A proposed construction giving only $\theta|_{F^\times}$ while claiming quadratic-induction normalization has omitted the rectifier.

### 12.2 Twist compatibility

The twist identity of Section 9.4 also checks central characters. On the left, twisting by $\chi\circ\operatorname{Nrd}$ multiplies the central character by $\chi(z^2)=\chi^2(z)$. On the right,

$$
(\chi\circ N_{E/F})(z)=\chi(z^2)=\chi^2(z).
$$

Thus both sides change by the same square. The quadratic character $\omega_{E/F}$ remains fixed.

Special representations obey the identical rule:

$$
\operatorname{Sp}_D(\chi_0)\otimes(\chi\circ\operatorname{Nrd})
=\operatorname{Sp}_D(\chi_0\chi).
$$

The parallel behavior is one reason reduced norm, not an arbitrary extension of the central character, is the correct twisting operation on $D^\times$.

### 12.3 Contragredients and self-duality

Dualizing a finite-index induced representation gives

$$
\Pi_D^{\mathrm{dir}}(E,\theta)^\vee
\simeq\Pi_D^{\mathrm{dir}}(E,\theta^{-1}).
$$

The rectifier inversion identity gives the exact normalized statement

$$
\Pi_D(E,\theta)^\vee
\simeq\Pi_D(E,\theta^{-1}),
$$

because

$$
(\theta\Delta_{E/F,\theta})^{-1}
=\theta^{-1}\Delta_{E/F,\theta^{-1}}.
$$

Thus duality inverts the underlying admissible orbit without changing normalization.

Therefore either the direct-normalized or the quadratic-induction-normalized representation is self-dual precisely when

$$
(E,\theta^{-1})\sim(E,\theta),
$$

that is, when $\theta^{-1}=\theta$ or $\theta^{-1}=\theta^\sigma$. The first alternative generally violates regularity unless a deeper layer remains nontrivial; the second is the familiar conjugate-self-dual condition. Essential self-duality is tested after multiplying by a norm character.

### 12.4 Recovering the admissible pair from the character

On a type-regular subset of $E^\times$, the character is a symmetric sum of the two conjugate type traces. Orthogonality of characters on a sufficiently fine finite quotient of $E^\times$ recovers the unordered orbit $\{\theta,\theta^\sigma\}$. The leading Gauss trace simultaneously identifies the centralizer field.

More concretely, if two positive-depth characters agree, their restrictions near a regular element have the same smallest nonconstant unit layer. Fourier inversion on that layer identifies the conjugacy orbit of $\beta$. Its centralizer recovers $E$; then dividing away the common Gauss factor recovers $\theta$ up to $\sigma$. This gives a character-theoretic proof of injectivity independent of the Mackey proof in Chapter 8.

## 13. Invariant pairings and formal degree

### 13.1 Pairings on an induced model

Let $\Lambda$ be a representation of $J$ and $\Lambda^\vee$ its contragredient, with evaluation pairing $\langle\ ,\ \rangle_\Lambda$. For induced functions $f$ and $f^\vee$, define

$$
\langle f,f^\vee\rangle
=\sum_{x\in J\backslash G}
\langle f(x),f^\vee(x)\rangle_\Lambda.
$$

The sum is finite and independent of coset representatives because the two transformation laws cancel. Right translation permutes the cosets, so the pairing is $G$-invariant. If the inducing pairing is perfect, so is the induced pairing.

For a unitary type, replace evaluation by its invariant Hermitian form. The same sum is positive definite. Thus every unitary quaternionic type produces a unitary representation without convergence questions: the quotient set is finite.

### 13.2 Schur orthogonality modulo the center

Assume $\Pi$ is unitary with central character $\omega$, and let $d\dot g$ be the fixed measure on $G/Z$. Matrix coefficients satisfy

$$
\int_{G/Z}
\langle\Pi(g)v_1,w_1\rangle
\overline{\langle\Pi(g)v_2,w_2\rangle}\,d\dot g
=d(\Pi)^{-1}
\langle v_1,v_2\rangle
\overline{\langle w_1,w_2\rangle}.
$$

For $\Pi=\operatorname{Ind}_J^G\Lambda$ with irreducible unitary $\Lambda$,

$$
\boxed{
d(\Pi)=\frac{\dim\Lambda}{\operatorname{vol}(J/Z)}.
}
$$

To prove it, choose vectors supported on the identity coset. The integral vanishes off $J/Z$ and reduces there to compact-group Schur orthogonality for $\Lambda$. Comparing coefficients gives the formula; $G$-invariance extends it to all vectors.

Formal degree scales inversely with $d\dot g$. This dependence is expected and is another reason to record quotient measures before comparing trace formulas.

### 13.3 Toric multiplicity and conjugation

Restriction of an induced representation to $E^\times$ is governed by Mackey double cosets. The identity coset carries the prescribed torus functional; the normalizer coset carries its conjugate. In fact the familiar multiplicity-one bound holds:

$$
\dim\operatorname{Hom}_{E^\times}(\Pi,\Omega)\leq1
$$

for every irreducible $\Pi$ and every character $\Omega$ whose restriction to $F^\times$ is the central character of $\Pi$.

Here is the double-coset calculation behind the bound. Write

$$
D=E\oplus Ej_E,
\qquad j_Ee=\sigma(e)j_E,
\qquad j_E^2=c\in F^\times,
$$

and define $\tau=\operatorname{Ad}(j_E)\circ\overline{\phantom{x}}$, where the bar is reduced conjugation. Then $\tau$ is an anti-involution fixing $E$ pointwise and

$$
\tau(a+bj_E)=a-\sigma(b)j_E.
$$

Every double coset is $\tau$-stable. If $ab\ne0$, Hilbert's cyclic argument gives $x\in E^\times$ with

$$
\frac{x}{\sigma(x)}=-\frac{\sigma(b)}b.
$$

Taking $y=x^{-1}$ gives $x(a+bj_E)y=\tau(a+bj_E)$. If $a=0$ or $b=0$, the same assertion follows by taking one of $x,y$ equal to $1$ and solving the remaining scalar equation.

For completeness, the resulting multiplicity criterion is finite-dimensional here. At a common principal-unit level, matrix coefficients and the $E^\times$-equivariance conditions factor through a finite central extension. On that finite group, transpose by $\tau$ carries an operator from an $\Omega$-functional followed by an $\Omega^{-1}$-functional to the reversed composition. Double-coset stability makes the two operators equal. If two independent functionals existed, suitable rank-one compositions would give two independent endomorphisms of the irreducible representation, contrary to Schur's lemma. Thus

$$
\dim\operatorname{Hom}_{E^\times}(\Pi,\Omega)\,
\dim\operatorname{Hom}_{E^\times}(\Pi^\vee,\Omega^{-1})\leq1.
$$

Duality identifies the two dimensions, proving the displayed bound.

For the representation attached to $(E,\theta)$ in direct normalization, the functional built into the inducing model is nonzero for the prescribed compatible torus character; multiplicity one makes its line canonical. A different character on the decisive unit layer has multiplicity zero by the simple-character calculation. For a different quadratic torus, existence of a functional is a separate question, even though uniqueness still holds.

The pairing identifies the $\theta$-line with the dual of the $\theta^{-1}$-line in the contragredient. If $\theta^\sigma=\theta^{-1}$, the normalizer element exchanges these two lines. Its square is central, so after fixing the central character its action determines whether the resulting self-dual pairing is symmetric or alternating. This sign is intrinsic, while the choice of a generator of either line is not.

Formal degree and toric multiplicity measure different things. Formal degree records the volume of the whole inducing subgroup and the dimension of its type. Toric multiplicity records one character inside restriction to $E^\times$. Equal formal degrees therefore do not force equal admissible pairs, and a one-dimensional toric line does not imply that the representation itself has dimension one.

## 14. Integral type lattices

### 14.1 Coefficient rings and integral inducing data

Let $L$ be a finite extension of $\mathbf Q_\ell$, let $R$ be its valuation ring, and assume $\ell\ne p$. We call the inducing datum **integral over $R$** when the type is defined over $L$ and all scalar characters occurring in it take values in $R^\times$. After a finite coefficient extension this condition includes all finite-order tame data and every chosen unramified scalar that is already an $\ell$-adic unit. It does not include an arbitrary transcendental complex character, nor a character whose central value has nonzero $\ell$-adic valuation.

An integral model of $\Lambda$ is a finite free $R$-module $\Lambda_R$ stable under $J$ with

$$
\Lambda_R\otimes_RL\simeq\Lambda.
$$

For depth zero, take the rank-one lattice on which $\lambda_\theta$ acts through units. At positive depth, realize the Heisenberg and tame extension over $L$. After the central unit-valued character is removed, smoothness makes an open subgroup of the compact group $J/Z$ act trivially. Start with any full lattice and replace it by the sum of its translates under representatives of the resulting finite quotient. This orbit sum is again full, finite, torsion-free, and stable, hence finite free over the DVR $R$. No averaging denominator, and therefore no banality hypothesis, is needed for existence.

Thus every selected integral type has an integral model. Existence does not assert uniqueness: two stable lattices in the same irreducible $L$-representation can differ at primes dividing a finite quotient order.

### 14.2 Finite free induction

Define

$$
\Pi_R=\operatorname{Ind}_J^G\Lambda_R.
$$

Because $J\backslash G$ is finite,

$$
\Pi_R\simeq\bigoplus_{J\backslash G}\Lambda_R
$$

as an $R$-module. Hence it is finite free of rank

$$
[G:J]\operatorname{rank}_R\Lambda_R,
$$

is stable under $G$, and satisfies

$$
\Pi_R\otimes_RL\simeq\Pi.
$$

This is stronger than the corresponding assertion for the split group, where compact induction has infinitely many cosets and only fixed modules are finite. Compactness modulo the center turns the full quaternionic representation lattice into a finite module.

For an integral special representation, the lattice is simply $R$ with action through the unit-valued character $\chi\circ\operatorname{Nrd}$. If $\chi(\varpi)$ is not a unit, no nonzero finite $R$-lattice can be stable under both $\varpi$ and $\varpi^{-1}$; this gives a sharp counterexample to an unconditional lattice claim.

### 14.3 Dual lattices and integral pairings

Let $\Lambda_R^\#=\operatorname{Hom}_R(\Lambda_R,R)$ with contragredient action. The coset-sum pairing of Chapter 13 is perfect between

$$
\Pi_R=\operatorname{Ind}_J^G\Lambda_R
\quad\text{and}\quad
\Pi_R^\#=\operatorname{Ind}_J^G\Lambda_R^\#.
$$

No denominator occurs because the formula is a finite sum, not an average. If $\Pi$ is self-dual, a stable lattice and its dual are commensurable and their intersection is again stable, but this does not by itself produce a self-dual lattice. A self-dual lattice exists precisely when the invariant form admits a unimodular stable integral model; discriminant and parity obstructions can prevent one. Whenever such a model exists, the same coset sum induces its perfect symmetric or alternating pairing.

The toric line is integral as well. Its intersection with $\Pi_R$ is a rank-one direct summand whenever the projector onto that line is defined over $R$. A generator is then primitive and unique up to $R^\times$. This is the division-side integral type line used in level comparison.

### 14.4 Reduction and the nonbanal warning

Suppose in addition that the coefficient and residue fields split the finite central extension through which the projective action factors, and that $\ell$ does not divide its order. Averaging is exact, ordinary and modular irreducibles correspond under reduction, and the intertwining calculation survives reduction. Under this **banal** hypothesis, reduction of a suitable stable lattice is irreducible and formation of the prescribed type line commutes with extension of residue fields.

If $\ell$ divides $q+1$, the depth-zero warning is immediate. Two distinct regular characters of $k_2^\times$ can become congruent to their Frobenius conjugates, and the reduced index-two induction can split or acquire extra endomorphisms. Similarly, if $\ell$ divides a finite symplectic quotient order, isotropic averaging need not be exact. The characteristic-zero lattice still exists, but irreducibility and multiplicity one after reduction are no longer automatic.

This is a genuine arithmetic phenomenon, not a failure of the construction. Integral compatibility must always state which finite orders have been inverted.

Coefficient extension is cleaner. If $R\to R'$ is a finite extension of valuation rings, then finite direct sums give a canonical equality

$$
\Pi_R\otimes_RR'
\simeq\operatorname{Ind}_J^G(\Lambda_R\otimes_RR').
$$

The induced pairing and contragredient lattice commute with this operation. If the banal hypotheses hold for the residue characteristic of $R'$, the same is true after reduction. Thus the integral type is insensitive to enlarging the coefficient field to contain missing character values; the only delicate change is passage to the residue field.

## 15. Examples, diagnostics, and exclusions

### 15.1 Five quick calculations

**Unramified special twist.** Let $\chi$ be unramified with $\chi(\varpi)=c$. Then $\operatorname{Sp}_D(\chi)$ is trivial on $\mathcal O_D^\times$, has conductor $1$, and takes the value $c^n$ on every element of reduced-norm valuation $n$. It is one-dimensional even though its split companion is infinite-dimensional.

**Depth-zero unramified pair.** Let $q=3$. The group $k_2^\times$ has order $8$, and Frobenius sends an exponent $m$ to $3m$. The regular orbits are $\{1,3\}$, $\{2,6\}$, and $\{5,7\}$; the exponents $0$ and $4$, precisely those divisible by $q+1=4$, are irregular. Each regular orbit gives a two-dimensional representation of conductor $2$. At a regular residue element $t$, its character is $t^m+t^{3m}$ after the chosen root-of-unity identification.

**First tame ramified level.** Assume $p\ne2$, let $E/F$ be ramified quadratic, and choose an admissible $\theta$ with $a_E(\theta)=2$. Then

$$
a_D(\Pi_D(E,\theta))=1+2=3.
$$

The leading character lives on $U_E^1/U_E^2$. Conjugation changes the uniformizer direction by a sign, so a noninvariant leading additive character detects the ramified torus. A norm-derived leading character is trace-controlled and would be removable, contradicting minimality.

**A cancelling twist.** Let $E/F$ be unramified and let $\theta_0$ be minimal with $a_E(\theta_0)=2$. Choose $\chi$ so that $a_E(\chi\circ N_{E/F})=4$, and put

$$
\theta=\theta_0(\chi^{-1}\circ N_{E/F}).
$$

Then $a_E(\theta)=4$ and $a_D(\Pi_D(E,\theta))=8$. Twisting by $\chi\circ\operatorname{Nrd}$ cancels the deeper norm layer and leaves conductor $4$. A maximum formula would incorrectly predict that the conductor stays $8$.

**A near-central character.** Take a positive-depth representation and $g=z(1+x)$ with $z\in F^\times$ and $x$ deeper than the defining simple-character layer. Many conjugates of $g$ can lie in $J$ because the leading class of $x$ has not yet distinguished one embedding of its centralizer. The two normalizer terms alone need not give $\Theta_\Pi(g)$. Enumerating the finite double cosets restores the missing locally constant contribution.

### 15.2 A diagnostic table

| datum | representation dimension pattern | conductor | central character |
|---|---:|---:|---|
| $\operatorname{Sp}_D(\chi)$, $a_F(\chi)=0$ | $1$ | $1$ | $\chi^2$ |
| $\operatorname{Sp}_D(\chi)$, $a_F(\chi)=m>0$ | $1$ | $2m$ | $\chi^2$ |
| unramified depth-zero pair | $2$ | $2$ | $\theta|_{F^\times}\omega_{E/F}$ |
| unramified positive-depth pair | finite, type-dependent | $2a_E(\theta)$ | $\theta|_{F^\times}\omega_{E/F}$ |
| tame ramified pair | finite, type-dependent | $a_E(\theta)+1$ | $\theta|_{F^\times}\omega_{E/F}$ |

Three checks catch most normalization errors. The special unramified conductor must be $1$, not $0$. The depth-zero dihedral conductor must be $2$, although the type is trivial on $U_D^1$. A norm twist must multiply the central character by $\chi^2$ and must compute its conductor from the twisted torus character, allowing cancellation.

### 15.3 The primitive wild boundary

The theory stops at a precise frontier. It includes regular depth-zero types and types whose first noncentral leading term has a tame quadratic centralizer. It does not include a ramified quadratic construction in residue characteristic two, and it does not include irreducible representations whose leading stratum has no quadratic-character description of the preceding form.

Such primitive wild representations may have more delicate filtration jumps, degenerate trace behavior on the first visible layer, and extension data not determined by a tame Heisenberg quotient. None of the intertwining, conductor, or integral-reduction assertions in this book is claimed for them. They are excluded exactly, not treated heuristically.

This boundary also prevents a misleading inference. Compactness of $D^\times/Z$ proves finite dimensionality for every irreducible representation, but it does not imply that every irreducible arises from the tame types constructed here.

## 16. The quaternionic dihedral package

### 16.1 Construction theorem

**Theorem 16.1 (selected quaternionic packets).** Let $F$ be a nonarchimedean local field of characteristic zero and $D/F$ its quaternion division algebra.

1. Every smooth character $\chi$ of $F^\times$ gives the special representation $\operatorname{Sp}_D(\chi)=\chi\circ\operatorname{Nrd}$, with conductor $1$ if $\chi$ is unramified and $2a_F(\chi)$ otherwise.
2. Every tame admissible quadratic pair $(E,\theta)$ gives an irreducible finite-dimensional representation

$$
\Pi_D(E,\theta)
=\operatorname{Ind}_{E^\times J^1}^{D^\times}
\Lambda_{\theta^\natural}.
$$

At depth zero, $J^1=U_D^1$ and the representation is the explicit index-two induction. At positive depth, $J^1$, the simple character, and its Heisenberg enlargement are determined by the leading element of a minimal norm twist.
3. The representation depends only on the equivalence class of the pair, and two selected dihedral representations are isomorphic only for equivalent pairs.
4. Its central character, twist rule, and conductor are

$$
\omega_{\Pi_D}=\theta|_{F^\times}\omega_{E/F},
$$

$$
\Pi_D(E,\theta)\otimes(\chi\circ\operatorname{Nrd})
\simeq\Pi_D(E,\theta(\chi\circ N_{E/F})),
$$

$$
a_D(\Pi_D(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).
$$

5. At every regular element its character is the finite induced sum of Section 10.2. On the type-regular torus range it is the sum of the two conjugate finite type traces. With compatible centralizer measures and the character-dependent rectifier, the negative sign relative to the matching split character is proved here for special and depth-zero packets; positive-depth comparison is left to the local transfer theorem.
6. If $\ell\ne p$ and the inducing datum is integral over the coefficient ring, the representation has a finite free stable lattice. Dual lattices pair perfectly; under the stated banal hypotheses, irreducibility and the toric type line survive reduction.

**Proof.** The special assertions were proved in Chapter 5. Depth-zero construction, irreducibility, and equivalence are Theorem 6.1. Positive-depth existence is Proposition 7.2, and exact intertwining gives Theorems 8.2 and 8.3. The invariant formulas are Theorem 9.1 and Chapters 10–12. Pairings and lattices are Chapters 13 and 14. $\square$

### 16.2 Normalization checks

The package checks itself in several independent ways. Conjugating $\theta$ exchanges the two elliptic contributions and changes no invariant. Multiplying by a norm character produces the same result as a reduced-norm twist. Restricting to the center introduces the square $z\mapsto z^2$ and the rectifier contributes precisely $\omega_{E/F}$. Dualizing inverts the pair. The discriminant exponent measures trace-dual displacement, while the residue degree counts the $F$-length of each $E$-unit layer.

The character side gives two further tests. Depth-zero values have a plus sign on the division group and a minus sign on the split group. Positive-depth values are actual finite Gauss traces, not unspecified constants. Near the center, the full double-coset sum must replace the two-normalizer approximation.

Finally, measure dependence is confined to the right places. Pointwise characters and finite induced traces do not change when Haar measure is rescaled. Orbital integrals, formal degrees, and distribution identities do change, and therefore use the quotient measures derived from the fixed unit normalizations.

### 16.3 Conclusion

The representation theory developed here is governed by one geometric compression: $D^\times$ is compact modulo its center. That compression turns induction into finite algebra, but the decisive arithmetic remains visible. The maximal-order filtration measures depth, reduced-trace duality measures conductor, a noncentral leading character recovers a quadratic field, and the normalizer produces the conjugate pair of character values.

Special twists and tame dihedral types now form a single coherent division-side package. Their central characters, twists, contragredients, conductors, character sums, invariant pairings, formal degrees, and integral lattices are mutually compatible. Compatible Haar and centralizer measures place these data in the exact normalization needed for local comparison. The remaining transfer theorem can therefore focus on matching the split and division character calculations rather than rebuilding either representation.

The excluded boundary remains equally clear. No primitive wild packet has been smuggled into a tame argument, and no ramified dyadic type has been inferred from a trace calculation that fails there. Within the selected range, quadratic induction has acquired its quaternionic type, its regular-elliptic character, and its integral structure.
