# Dihedral Supercuspidals, Types, and Newvectors for $\mathrm{GL}_2$

## Contents

1. [The quadratic route to cuspidality](#1-the-quadratic-route-to-cuspidality)
   - [Why elliptic tori produce discrete representations](#11-why-elliptic-tori-produce-discrete-representations)
   - [Standing conventions](#12-standing-conventions)
   - [The exact scope](#13-the-exact-scope)
2. [Quadratic extensions and admissible characters](#2-quadratic-extensions-and-admissible-characters)
   - [The embedded torus](#21-the-embedded-torus)
   - [Conductors and conjugation](#22-conductors-and-conjugation)
   - [Admissible and minimal pairs](#23-admissible-and-minimal-pairs)
   - [Norm twists and reduction to minimal level](#24-norm-twists-and-reduction-to-minimal-level)
3. [Compact induction as an irreducibility machine](#3-compact-induction-as-an-irreducibility-machine)
   - [Intertwining is the decisive invariant](#31-intertwining-is-the-decisive-invariant)
   - [The compact-mod-center criterion](#32-the-compact-mod-center-criterion)
   - [Cuspidality and admissibility](#33-cuspidality-and-admissibility)
   - [Characters of compactly induced representations](#34-characters-of-compactly-induced-representations)
4. [The finite-field cuspidal seed](#4-the-finite-field-cuspidal-seed)
   - [Regular characters of the nonsplit torus](#41-regular-characters-of-the-nonsplit-torus)
   - [A concrete model](#42-a-concrete-model)
   - [Irreducibility and the character table](#43-irreducibility-and-the-character-table)
   - [Why regularity is necessary](#44-why-regularity-is-necessary)
5. [Depth-zero supercuspidals](#5-depth-zero-supercuspidals)
   - [Inflation and extension across the center](#51-inflation-and-extension-across-the-center)
   - [The depth-zero induction theorem](#52-the-depth-zero-induction-theorem)
   - [The depth-zero type](#53-the-depth-zero-type)
   - [A first worked family](#54-a-first-worked-family)
6. [Tame positive-depth types](#6-tame-positive-depth-types)
   - [The quadratic lattice chain](#61-the-quadratic-lattice-chain)
   - [Extracting an additive leading term](#62-extracting-an-additive-leading-term)
   - [The simple character and its Heisenberg enlargement](#63-the-simple-character-and-its-heisenberg-enlargement)
   - [The maximal tame type](#64-the-maximal-tame-type)
7. [The tame induction theorem](#7-the-tame-induction-theorem)
   - [Intertwining of the type](#71-intertwining-of-the-type)
   - [Irreducibility and supercuspidality](#72-irreducibility-and-supercuspidality)
   - [Equivalence and exhaustivity](#73-equivalence-and-exhaustivity)
   - [Types and inertial classes](#74-types-and-inertial-classes)
8. [Character calculations](#8-character-calculations)
   - [The compact-induction formula](#81-the-compact-induction-formula)
   - [Depth-zero regular elements](#82-depth-zero-regular-elements)
   - [Positive-depth elliptic elements](#83-positive-depth-elliptic-elements)
   - [What the character detects](#84-what-the-character-detects)
9. [Whittaker and Kirillov models](#9-whittaker-and-kirillov-models)
   - [Genericity from cuspidality](#91-genericity-from-cuspidality)
   - [The compact Kirillov model](#92-the-compact-kirillov-model)
   - [A toric Whittaker function](#93-a-toric-whittaker-function)
10. [Conductors](#10-conductors)
    - [Congruence subgroups and the conductor](#101-congruence-subgroups-and-the-conductor)
    - [The quadratic conductor formula](#102-the-quadratic-conductor-formula)
    - [Depth zero and the two tame ramification patterns](#103-depth-zero-and-the-two-tame-ramification-patterns)
    - [Minimality and old levels](#104-minimality-and-old-levels)
11. [Twists and central characters](#11-twists-and-central-characters)
    - [Twisting an admissible pair](#111-twisting-an-admissible-pair)
    - [Exact conductor under twisting](#112-exact-conductor-under-twisting)
    - [Central characters and self-duality](#113-central-characters-and-self-duality)
    - [Counterexamples to naive conductor rules](#114-counterexamples-to-naive-conductor-rules)
12. [Local constants and quadratic induction](#12-local-constants-and-quadratic-induction)
    - [Normalization and the quadratic factor](#121-normalization-and-the-quadratic-factor)
    - [The induction formula](#122-the-induction-formula)
    - [Gauss sums and root numbers](#123-gauss-sums-and-root-numbers)
    - [Changes of additive character](#124-changes-of-additive-character)
13. [The newvector theorem](#13-the-newvector-theorem)
    - [The unique first fixed line](#131-the-unique-first-fixed-line)
    - [Proof in the Kirillov model](#132-proof-in-the-kirillov-model)
    - [The normalized Whittaker newform](#133-the-normalized-whittaker-newform)
    - [Higher fixed spaces](#134-higher-fixed-spaces)
14. [Integral newvectors](#14-integral-newvectors)
    - [Integral inducing data](#141-integral-inducing-data)
    - [The integral compact-induction lattice](#142-the-integral-compact-induction-lattice)
    - [A primitive integral newvector](#143-a-primitive-integral-newvector)
    - [Base change and reduction](#144-base-change-and-reduction)
15. [Examples and boundary cases](#15-examples-and-boundary-cases)
    - [Unramified depth zero](#151-unramified-depth-zero)
    - [Unramified positive depth](#152-unramified-positive-depth)
    - [Tamely ramified quadratic induction](#153-tamely-ramified-quadratic-induction)
    - [The primitive wild boundary](#154-the-primitive-wild-boundary)
16. [The reusable local package](#16-the-reusable-local-package)
   - [Construction and invariants](#161-construction-and-invariants)
   - [Final synthesis](#162-final-synthesis)

## 1. The quadratic route to cuspidality

### 1.1 Why elliptic tori produce discrete representations

The principal series of $\mathrm{GL}_2(F)$ is built from the split diagonal torus. Its vectors remember two one-dimensional characters of $F^\times$, and its matrix coefficients retain a noncompact direction coming from the upper triangular subgroup. A supercuspidal representation must behave in the opposite way: no nonzero quotient may be assembled from a proper parabolic subgroup, and its matrix coefficients must be compact after the center is ignored.

A quadratic field $E/F$ supplies exactly the missing geometry. After choosing an $F$-basis of $E$, multiplication embeds

$$
E^\times\hookrightarrow \mathrm{GL}_F(E)\simeq \mathrm{GL}_2(F).
$$

The quotient $E^\times/F^\times$ is compact. Thus a character of $E^\times$, enlarged by a sufficiently small compact subgroup around the torus and then compactly induced, has a chance to produce coefficients compact modulo the center. The character must distinguish the two $F$-embeddings of $E$. If it does not, the construction sees only norm data and falls back toward the split theory.

This book turns that geometric picture into a precise machine. There are two visibly different starting points. At depth zero, reduction modulo the maximal ideal gives the nonsplit torus $k_{q^2}^\times$ inside $\mathrm{GL}_2(k_q)$, and a finite-field cuspidal representation is inflated. At positive depth, a character is first linearized on a deep unit group; its leading additive term determines the quadratic field and a representation of a compact-mod-center subgroup. The two constructions obey the same principles of intertwining, compact induction, and conjugacy.

### 1.2 Standing conventions

Throughout, $F$ is a nonarchimedean local field with ring of integers $\mathcal O$, maximal ideal $\mathfrak p=(\varpi)$, normalized valuation $v_F$, residue field $k$ of cardinality $q$, and residue characteristic $p$. Put

$$
G=\mathrm{GL}_2(F),\qquad Z=F^\times,
$$

with $Z$ embedded as scalar matrices. Representations are smooth complex representations unless an integral coefficient ring is explicitly introduced. Haar measure on $G/Z$ is fixed once and for all. The earlier general theory supplies smooth and compact induction, Frobenius reciprocity, Mackey decomposition, contragredients, trace characters, Whittaker uniqueness, and Kirillov models.

For a finite extension $L/F$, write $\mathcal O_L$, $\mathfrak p_L$, $U_L^0=\mathcal O_L^\times$, and

$$
U_L^r=1+\mathfrak p_L^r\quad(r\geq1).
$$

For a smooth character $\chi:L^\times\to\mathbf C^\times$, its conductor exponent is

$$
a_L(\chi)=\min\{r\geq0:\chi|_{U_L^r}=1\}.
$$

Thus $a_L(\chi)=0$ means unramified, while a nontrivial character of $k_L^\times$ inflated to $U_L^0$ has conductor exponent $1$. Its level is $\ell_L(\chi)=\max\{a_L(\chi)-1,0\}$.

Fix a nontrivial additive character $\psi:F\to\mathbf C^\times$ trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. Additive Haar measure is self-dual for $\psi$. For $E/F$ put $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$. If $d(E/F)=v_E(\mathfrak D_{E/F})$, then the annihilator of $\mathcal O_E$ under $(x,y)\mapsto\psi_E(xy)$ is $\mathfrak D_{E/F}^{-1}=\mathfrak p_E^{-d(E/F)}$.

### 1.3 The exact scope

The main construction assumes that $E/F$ is separable quadratic and tame. This includes every quadratic extension when $p\ne2$ and the unramified quadratic extension in every residue characteristic. We treat depth-zero and positive-depth admissible pairs, their maximal types, compact inductions, characters on the ranges needed for comparison, conductors, twists, central characters, local constants, and integral newvectors.

The boundary is structural, not cosmetic. A primitive wild supercuspidal is one whose first irreducible leading term does not come from a quadratic field character by the construction below. Such representations require additional wild strata and are outside this volume. Wildly ramified quadratic extensions in residue characteristic two also require extra choices in the type construction and are not used here. Nothing proved below claims to classify those cases.

## 2. Quadratic extensions and admissible characters

### 2.1 The embedded torus

Let $E/F$ be separable quadratic and let $\sigma$ be its nontrivial $F$-automorphism. Choosing an $F$-basis identifies the multiplication action of $E$ with an embedding $E\hookrightarrow A=M_2(F)$. Any two such embeddings are conjugate by $G$: an intertwining map between the two one-dimensional $E$-modules is an invertible $F$-linear map. Consequently the representation eventually constructed depends on the pair $(E,\theta)$ up to $F$-isomorphism, not on a basis.

The centralizer of $E^\times$ in $G$ is $E^\times$. Indeed an $F$-linear endomorphism commuting with every multiplication map is multiplication by its value at $1$. Its normalizer fits into

$$
1\longrightarrow E^\times\longrightarrow N_G(E^\times)
\longrightarrow\langle\sigma\rangle\longrightarrow1.
$$

To prove surjectivity on the right, view $\sigma:E\to E$ as an invertible $F$-linear map. For the kernel, use the centralizer calculation. This two-element quotient explains why $\theta$ and $\theta^\sigma$, where $\theta^\sigma(x)=\theta(\sigma x)$, must define the same induced representation and why no further generic equivalence should occur.

Finally, $E^\times/F^\times$ is compact. Write $E^\times=\varpi_E^{\mathbf Z}\mathcal O_E^\times$. In the unramified case $\varpi_E=\varpi$; in the ramified quadratic case $\varpi_E^2$ is a scalar times a unit. Hence the valuation quotient is finite, while $\mathcal O_E^\times/\mathcal O^\times$ is compact.

### 2.2 Conductors and conjugation

The ratio

$$
\theta/\theta^\sigma
$$

measures the failure of $\theta$ to descend through the norm. If $\theta=\chi\circ N_{E/F}$, then $N_{E/F}(x)=N_{E/F}(\sigma x)$ gives $\theta=\theta^\sigma$. The converse also holds.

**Proposition 2.1 (quadratic descent).** A smooth character $\theta$ of $E^\times$ satisfies $\theta=\theta^\sigma$ if and only if $\theta=\chi\circ N_{E/F}$ for a smooth character $\chi$ of $F^\times$.

**Proof strategy.** An invariant character is trivial on elements $x/\sigma x$. Hilbert's cyclic argument identifies those elements with the kernel of the norm, and then the character descends to the norm subgroup. A character of the open finite-index norm subgroup extends to $F^\times$ because $\mathbf C^\times$ is divisible.

**Proof.** If $N(x)=1$, the usual two-dimensional cyclic calculation gives $x=y/\sigma y$ for some $y\in E^\times$: when $x\ne-1$, take $y=1+x$; the remaining case follows by choosing any $z$ with $z\ne\sigma z$ and taking $y=z-\sigma z$. Thus invariance gives $\theta(x)=1$ on $\ker N$. It follows that $\theta$ factors through $N(E^\times)$. This norm subgroup is open in $F^\times$, as is seen on a sufficiently deep unit group from the linearized norm $1+u\mapsto1+\operatorname{Tr}(u)$ and on valuations from $v_F(Nx)=f(E/F)v_E(x)$. Extend the resulting character across the finite quotient $F^\times/N(E^\times)$ by choosing roots in $\mathbf C^\times$. The reverse implication was already observed. $\square$

This proposition also gives a useful warning: the inequality $\theta\ne\theta^\sigma$ is essential, but at positive depth it is not by itself the most convenient minimality condition. A norm twist may hide the first genuinely quadratic layer.

### 2.3 Admissible and minimal pairs

An **admissible pair** is a separable quadratic extension $E/F$ together with a smooth character $\theta:E^\times\to\mathbf C^\times$ satisfying:

1. $\theta\ne\theta^\sigma$;
2. if $\theta/\theta^\sigma$ is trivial on $U_E^1$, then $E/F$ is unramified.

The second condition excludes a tamely ramified quadratic torus whose character becomes quadratic only through valuation data. Such a pair has too much normalizer intertwining and does not yield the desired irreducible induction. In the unramified case it permits the depth-zero construction: regularity can already be visible on $k_E^\times$.

Two admissible pairs $(E,\theta)$ and $(E',\theta')$ are **equivalent** if an $F$-isomorphism $j:E\to E'$ satisfies $\theta'=\theta\circ j^{-1}$. For a fixed $E$, this says precisely that $\theta'$ is $\theta$ or $\theta^\sigma$.

A positive-level admissible pair is **minimal** if no character $\chi$ of $F^\times$ makes

$$
a_E\bigl(\theta(\chi\circ N_{E/F})^{-1}\bigr)<a_E(\theta).
$$

Minimality says that the highest nontrivial unit layer of $\theta$ is genuinely quadratic. It is the hypothesis under which one leading additive term determines $E$.

### 2.4 Norm twists and reduction to minimal level

**Proposition 2.2 (minimal twist decomposition).** Let $(E,\theta)$ be a tame admissible pair. There are a minimal admissible character $\theta_0$ of $E^\times$ and a character $\chi$ of $F^\times$ such that

$$
\theta=\theta_0(\chi\circ N_{E/F}).
$$

The minimal conductor $a_E(\theta_0)$ is determined by $\theta$, although $\theta_0$ and $\chi$ need not be unique.

**Proof strategy.** Repeatedly remove any norm character visible on the last nontrivial unit quotient. Conductors are nonnegative integers, so the process terminates. The only issue is extending a character from a norm image; tame trace surjectivity on the relevant unit layer supplies that extension.

**Proof.** If $\theta$ is not minimal, choose $\chi_1$ lowering its conductor. Replace $\theta$ by $\theta(\chi_1\circ N)^{-1}$ and repeat. The conductor strictly decreases each time, so after finitely many steps it reaches a minimal character $\theta_0$. Multiplying the successive $\chi_i$ gives $\chi$.

For completeness, the character needed at each step can be seen on the last unit layer. For $r\ge1$, multiplication identifies $U_E^r/U_E^{r+1}$ with the additive group of $k_E$, and

$$
N(1+x)\equiv1+\operatorname{Tr}_{E/F}(x)
$$

at the corresponding first-order precision. In a tame extension the trace on the needed graded quotient has the expected nonzero image; an invariant additive character therefore descends to the $F$-layer. Lift it to a smooth character of $F^\times$ and cancel it. Since the set of conductors attained by norm twists is a nonempty subset of $\mathbf Z_{\ge0}$, its minimum is intrinsic. $\square$

The nonuniqueness is harmless. The representation attached below satisfies a twist identity, so different decompositions lead to the same result.

## 3. Compact induction as an irreducibility machine

### 3.1 Intertwining is the decisive invariant

Let $J\subseteq G$ be open and compact modulo $Z$, and let $\Lambda$ be a finite-dimensional irreducible smooth representation of $J$. For $g\in G$, put

$$
J^g=g^{-1}Jg,\qquad \Lambda^g(x)=\Lambda(gxg^{-1}),
$$

and define the intertwining set

$$
I_G(\Lambda)=\left\{g\in G:
\operatorname{Hom}_{J\cap J^g}(\Lambda,\Lambda^g)\ne0\right\}.
$$

This set measures every possible overlap between two translates of the inducing datum. If it is no larger than $J$, the induced representation has no hidden self-correspondence.

### 3.2 The compact-mod-center criterion

**Theorem 3.1 (irreducibility criterion).** Suppose $J/Z$ is compact, $\Lambda$ is irreducible, the central action of $Z$ on $\Lambda$ is a character, and

$$
I_G(\Lambda)=J.
$$

Then $\mathrm{c\mbox{-}Ind}_J^G\Lambda$ is irreducible and admissible. Its endomorphism algebra is $\mathbf C$.

**Proof strategy.** Mackey theory decomposes an endomorphism by double cosets $JgJ$. Intertwining eliminates every double coset except $J$. A nonzero subrepresentation then has a nonzero map back to the inducing representation, forcing it to contain all translates of one copy of $\Lambda$.

**Proof.** Frobenius reciprocity and Mackey decomposition give

$$
\operatorname{End}_G(\mathrm{c\mbox{-}Ind}_J^G\Lambda)
\simeq
\bigoplus_{JgJ\in J\backslash G/J}
\operatorname{Hom}_{J\cap J^g}(\Lambda,\Lambda^g),
$$

with the usual compact-support condition. The intertwining hypothesis leaves only $g\in J$, and Schur's lemma makes that summand $\mathbf C$.

For irreducibility, use the standard minimal-support argument behind the Mackey criterion. If $V$ is a nonzero subrepresentation, choose a nonzero vector in $V$ with the least possible number of supporting $J$-cosets. If more than one coset occurs, apply a matrix coefficient of $\Lambda$ supported on $J$ to kill the value on one coset while retaining another. The only obstruction would be an intertwiner supported on a double coset outside $J$, which the hypothesis excludes. Minimality therefore forces a vector supported on $J$. Its $J$-span contains the inducing representation, and its $G$-span is the whole compact induction. Thus $V$ is the whole representation.

Admissibility follows from the compact-induction admissibility criterion: for a fixed compact open $K$, the possible contributing double cosets are bounded by the image of the intertwining support in $J\backslash G/J$. Here that support is the single coset $J$, and each remaining intersection-invariant space is finite-dimensional. Hence the $K$-fixed space is finite-dimensional. $\square$

The intertwining equality is therefore the central calculation in both depth zero and positive depth.

### 3.3 Cuspidality and admissibility

**Proposition 3.2.** Under the hypotheses of Theorem 3.1, every matrix coefficient of $\mathrm{c\mbox{-}Ind}_J^G\Lambda$ is compactly supported modulo $Z$. Consequently its Jacquet module for the upper triangular unipotent subgroup is zero, and the representation is supercuspidal.

**Proof.** A compactly induced vector is supported on finitely many right $J$-cosets modulo $Z$. Pairing two such vectors shows that their coefficient is supported in a finite union of sets $JgJ$, each compact modulo $Z$. If the Jacquet module were nonzero, the rank-one adjunction theorem would place the representation in a subquotient of a principal series. Matrix coefficients of such a subquotient have a noncompact split-torus tail, contradicting compact support modulo $Z$. Thus the Jacquet module vanishes. $\square$

This proof also explains why induction from $E^\times$ alone is usually insufficient. Although $E^\times/Z$ is compact, a character of the bare torus generally has extra intertwiners. The surrounding congruence subgroup in the type removes them.

### 3.4 Characters of compactly induced representations

At a regular semisimple element $g$, the trace character has the induced form

$$
\Theta_{\mathrm{c\mbox{-}Ind}\Lambda}(g)
=\sum_{x\in J\backslash G,\;xgx^{-1}\in J}
\operatorname{tr}\Lambda(xgx^{-1}),
$$

where terms are grouped modulo the centralizer of $g$. The sum is finite when $g$ is regular and $J/Z$ is compact. This is proved by applying the operator to functions supported on individual cosets and taking the trace on a sufficiently small compact-open invariant space. We shall use the formula in Chapter 8; it is safer than guessing a character from the inducing torus, because it retains both conjugate embeddings and every finite-level sign.

## 4. The finite-field cuspidal seed

### 4.1 Regular characters of the nonsplit torus

Let $k_2/k$ be the quadratic extension and let $\tau(x)=x^q$. A character $\vartheta:k_2^\times\to\mathbf C^\times$ is **regular** if

$$
\vartheta\ne\vartheta^\tau.
$$

Equivalently, $\vartheta$ does not factor through the finite-field norm $x\mapsto x^{q+1}$. Indeed the quotient $k_2^\times/k^\times$ is cyclic of order $q+1$, and $\tau$ acts there by inversion. Equality with the conjugate is precisely triviality on the norm-one subgroup.

Regularity is the finite shadow of admissibility. It ensures that the nonsplit torus has only its obvious two normalizer symmetries on the character.

### 4.2 A concrete model

Put $\overline G=\mathrm{GL}_2(k)$ and identify $k_2^\times$ with a nonsplit maximal torus $\overline T$. Let $\overline B$ be the upper triangular subgroup and $\overline U$ its unipotent radical. Consider the space of functions $f:\overline G\to\mathbf C$ satisfying

$$
f(tg)=\vartheta(t)f(g)\qquad(t\in\overline T),
$$

and impose the single relation that the sum of $f$ along each right $\overline U$-orbit is zero. Right translation preserves these relations. The resulting representation, denoted $\rho_\vartheta$, has dimension $q-1$.

To see the dimension, identify $\overline T\backslash\overline G$ with the complement of the $k$-rational points in the projective line over $k_2$, modulo conjugation. The orbit-sum relation removes one dimension from each affine fiber; the elementary count leaves $q-1$. More invariantly, the same space is the $\vartheta$-isotypic part of functions on the norm-one conic with constants removed.

### 4.3 Irreducibility and the character table

**Theorem 4.1 (finite cuspidal representation).** If $\vartheta$ is regular, $\rho_\vartheta$ is irreducible and cuspidal, depends only on the orbit $\{\vartheta,\vartheta^\tau\}$, and has character

$$
\begin{array}{c|c}
\text{element of }\overline G&\operatorname{tr}\rho_\vartheta\\ \hline
zI&(q-1)\vartheta(z)\\
z\begin{pmatrix}1&1\\0&1\end{pmatrix}&-\vartheta(z)\\
\operatorname{diag}(a,b),\ a\ne b&0\\
t\in k_2^\times\setminus k^\times&-\vartheta(t)-\vartheta(t^q).
\end{array}
$$

Here $z,a,b\in k^\times$, and the last row uses the nonsplit-torus embedding.

**Proof strategy.** The four rows exhaust conjugacy types. Compute fixed points of each element on the conic model, with the orbit-sum relation subtracting the constant contribution. Orthogonality of the resulting character proves irreducibility, while vanishing of $\overline U$-coinvariants proves cuspidality.

**Proof.** A scalar fixes every point and acts through $\vartheta(z)$, giving $(q-1)\vartheta(z)$. A nontrivial unipotent fixes one rational direction; the removed orbit sum contributes the single value $-\vartheta(z)$. A split regular element has two rational eigenlines and no point in the nonsplit torus orbit after the two constant contributions cancel, giving zero. A regular elliptic element has its two eigenlines over $k_2$, interchanged by $\tau$; the weighted fixed-point contributions are $-\vartheta(t)$ and $-\vartheta(t^q)$.

Now use the class sizes

$$
1,\qquad q^2-1,\qquad q(q+1),\qquad q(q-1)
$$

for the centralizer patterns of scalar, unipotent, split regular, and elliptic regular classes, respectively, together with orthogonality of characters of $k_2^\times$. Substitution gives

$$
\frac1{|\overline G|}\sum_{g\in\overline G}
|\operatorname{tr}\rho_\vartheta(g)|^2=1.
$$

Hence the representation is irreducible. Averaging the character over $\overline U$ gives zero, so $\rho_\vartheta{}_{\overline U}=0$. Finally the displayed table is unchanged when $\vartheta$ is replaced by $\vartheta^\tau$, and character equality for irreducible finite-group representations gives the asserted equivalence. $\square$

### 4.4 Why regularity is necessary

If $\vartheta=\chi\circ N_{k_2/k}$, the last row becomes $-2\chi(Nt)$. The conic construction then splits; it is no longer an irreducible cuspidal representation. This is not a minor exceptional parameter. It is the finite-field manifestation of a character descending to the split torus. Thus a depth-zero construction that omits regularity can accidentally produce principal-series constituents.

## 5. Depth-zero supercuspidals

### 5.1 Inflation and extension across the center

Let $E/F$ be unramified quadratic. Then $\mathcal O_E^\times/U_E^1=k_2^\times$, and we may choose the embedding so that $\mathcal O_E^\times\subset K=\mathrm{GL}_2(\mathcal O)$. Suppose $\theta$ has level zero and its residue character $\overline\theta$ is regular. Inflate $\rho_{\overline\theta}$ from $\mathrm{GL}_2(k)$ to $K$.

Set

$$
J=ZK.
$$

The intersection $Z\cap K=\mathcal O^\times$ acts on the inflated representation by $\theta|_{\mathcal O^\times}$. There is therefore a unique extension $\Lambda_\theta$ to $J$ on which $z\in Z$ acts by $\theta(z)$. Explicitly,

$$
\Lambda_\theta(zk)=\theta(z)\rho_{\overline\theta}(\overline k).
$$

Well-definedness follows from the agreement on $Z\cap K$.

### 5.2 The depth-zero induction theorem

**Theorem 5.1.** The representation

$$
\pi(E,\theta)=\mathrm{c\mbox{-}Ind}_{ZK}^{G}\Lambda_\theta
$$

is irreducible, admissible, and supercuspidal. Moreover

$$
\pi(E,\theta)\simeq\pi(E',\theta')
$$

if and only if the depth-zero admissible pairs are equivalent.

**Proof strategy.** Reduce an intertwiner modulo $\mathfrak p$. Cartan decomposition shows that a double coset outside $ZK$ forces invariants under a nontrivial unipotent subgroup of the finite quotient, which cuspidality forbids.

**Proof.** Cartan decomposition gives

$$
G=\bigsqcup_{r\ge0}K
\begin{pmatrix}\varpi^r&0\\0&1\end{pmatrix}KZ.
$$

For $r>0$, the intersection of $K$ with its conjugate contains a subgroup whose reduction is the upper unipotent group on one side and the lower unipotent group on the other. A nonzero intertwiner of the inflated representations would therefore give a nonzero Jacquet quotient of $\rho_{\overline\theta}$, contradicting Theorem 4.1. Hence $I_G(\Lambda_\theta)=ZK$, and Theorem 3.1 and Proposition 3.2 prove the first assertion.

An isomorphism of compact inductions intertwines their inducing data after a $G$-conjugacy, again by Mackey theory and the same intertwining calculation. Reduction identifies the two nonsplit tori and their regular characters up to finite-field conjugation. Lifting that conjugacy gives an $F$-isomorphism of pairs. Conversely an equivalence of pairs conjugates the inducing data and hence the compact inductions. $\square$

### 5.3 The depth-zero type

The pair $(K,\rho_{\overline\theta})$ is a type for the unramified-twist class of $\pi(E,\theta)$.

**Proposition 5.2.** For an irreducible smooth representation $\Pi$ of $G$,

$$
\operatorname{Hom}_K(\rho_{\overline\theta},\Pi)\ne0
$$

if and only if $\Pi\simeq\pi(E,\theta)\otimes(\chi\circ\det)$ for an unramified character $\chi$ of $F^\times$.

**Proof.** A nonzero map and Frobenius reciprocity place $\Pi$ in an induction from $ZK$ after choosing the scalar by which $\varpi I$ acts. The intertwining calculation makes that induction irreducible, so the map is an isomorphism. Changing the scalar action while keeping the $K$-representation fixed is exactly twisting by an unramified determinant character. The converse is immediate because such a twist is trivial on $K$. $\square$

Thus a type remembers ramified behavior and deliberately forgets the unramified scalar parameter.

### 5.4 A first worked family

Choose a generator $\zeta$ of $k_2^\times$ and write $\overline\theta(\zeta)=e^{2\pi i m/(q^2-1)}$. Frobenius sends $m$ to $qm$. Regularity is

$$
m\not\equiv qm\pmod{q^2-1},
$$

or equivalently $q+1\nmid m$. The two exponents $m$ and $qm$ give the same representation. Its finite type has dimension $q-1$, its central character on $\mathcal O^\times$ is the restriction of $\overline\theta$, and its conductor will be shown to equal $2$.

For $q=3$, the group $k_2^\times$ has order $8$. Exponents $m=1$ and $3$ form one regular orbit; exponents divisible by $4$ are nonregular. This tiny example already displays the conjugate-pair parametrization.

## 6. Tame positive-depth types

### 6.1 The quadratic lattice chain

Let $E/F$ now be tame quadratic and embedded in $A=M_2(F)$. Regard $E$ as a two-dimensional $F$-space and set $L_i=\mathfrak p_E^i$. Define

$$
\mathfrak A=\{x\in A:xL_i\subseteq L_i\text{ for every }i\},
$$

and

$$
\mathfrak P=\{x\in A:xL_i\subseteq L_{i+1}\text{ for every }i\}.
$$

Then $\mathfrak A$ is a hereditary order, $\mathfrak P$ is its Jacobson radical, and

$$
\mathfrak P^{e(E/F)}=\varpi\mathfrak A.
$$

Put $U_{\mathfrak A}^r=1+\mathfrak P^r$ for $r\ge1$. Multiplication by $E^\times$ translates the lattice chain, so $E^\times$ normalizes $\mathfrak A$ and every $U_{\mathfrak A}^r$. This basis-free definition simultaneously gives the maximal order in the unramified case and the Iwahori order in the ramified case.

The trace pairing $\langle x,y\rangle=\psi(\operatorname{tr}_A(xy))$ identifies the annihilator of $\mathfrak P^r$ with a corresponding negative power of $\mathfrak P$. This converts a multiplicative character on a deep congruence quotient into a matrix $\beta\in E$.

### 6.2 Extracting an additive leading term

Let $(E,\theta)$ be minimal of positive level $m=a_E(\theta)-1$. On a sufficiently deep unit group multiplication is additive to first order:

$$
(1+x)(1+y)\equiv1+x+y
\pmod{\mathfrak p_E^{m+1}}
$$

whenever $x,y\in\mathfrak p_E^{\lfloor m/2\rfloor+1}$. Therefore there is $\beta\in E$ such that

$$
\theta(1+x)=\psi_E(\beta x)
\quad
\left(x\in\mathfrak p_E^{\lfloor m/2\rfloor+1}\right),
$$

with

$$
v_E(\beta)=-m-1-d(E/F)=-a_E(\theta)-d(E/F).
$$

The valuation follows from the fact that the annihilator of $\mathcal O_E$ is $\mathfrak p_E^{-d(E/F)}$. The element $\beta$ is determined modulo the annihilator of the displayed deep ideal.

**Lemma 6.1 (minimality of the leading term).** The leading class of $\beta$ does not lie in $F$ modulo that annihilator. In particular $F[\beta]=E$.

**Proof.** If $\beta$ were congruent to $b\in F$, then on the last nontrivial unit layer

$$
\psi_E(\beta x)=\psi\bigl(b\operatorname{Tr}_{E/F}(x)\bigr).
$$

This character is pulled back from the first-order norm, since $N(1+x)\equiv1+\operatorname{Tr}(x)$. A character of $F^\times$ with this leading term would cancel the last layer of $\theta$, lowering its conductor and contradicting minimality. Because $E/F$ is quadratic, any element of $E\setminus F$ generates $E$. $\square$

This is the decisive point of the construction: the highest oscillation of $\theta$ recovers the elliptic torus.

### 6.3 The simple character and its Heisenberg enlargement

Put $n=-v_{\mathfrak A}(\beta)$, where $v_{\mathfrak A}(x)$ is the largest $r$ with $x\in\mathfrak P^r$. Define

$$
H^1=U_E^1U_{\mathfrak A}^{\lfloor n/2\rfloor+1},
\qquad
J^1=U_E^1U_{\mathfrak A}^{\lfloor(n+1)/2\rfloor}.
$$

On $H^1$ define

$$
\vartheta_\beta\bigl(u(1+x)\bigr)
=\theta(u)\psi(\operatorname{tr}_A(\beta x)),
$$

for $u\in U_E^1$ and $x$ in the indicated radical power. The two formulas agree on the intersection by the choice of $\beta$. Terms $xy$ lie beyond the conductor, so the displayed rule is multiplicative and well defined.

The quotient $J^1/H^1$ carries the alternating form

$$
(\overline x,\overline y)\longmapsto
\vartheta_\beta([x,y]).
$$

**Lemma 6.2 (Heisenberg lemma).** This alternating form is nondegenerate. There is a unique irreducible representation $\eta_\beta$ of $J^1$ whose restriction contains $\vartheta_\beta$. Its dimension is $[J^1:H^1]^{1/2}$. If $J^1=H^1$, then $\eta_\beta=\vartheta_\beta$.

**Proof strategy.** The commutator becomes $\psi(\operatorname{tr}_A(\beta(xy-yx)))$ on the associated graded space. Its radical is exactly the graded centralizer of $\beta$, which is the image of $E$; that part has already been included in $U_E^1$.

**Proof.** Expanding commutators at the relevant precision gives

$$
[1+x,1+y]\equiv1+xy-yx.
$$

If $x$ pairs trivially with every $y$, trace duality says that its graded class centralizes the leading class of $\beta$. Lemma 6.1 and the elementary centralizer calculation in $M_2(F)$ identify this centralizer with $E$. Modulo the $U_E^1$ factor, the class of $x$ is therefore zero. Hence the form is nondegenerate. Choose a maximal isotropic subgroup, extend $\vartheta_\beta$ to it, and induce to $J^1$. Finite-group Mackey theory proves irreducibility and gives the square-root dimension. Any two choices have the same character and are isomorphic. $\square$

### 6.4 The maximal tame type

Set

$$
J=E^\times J^1.
$$

This group is open and compact modulo $Z$. Conjugation by $E^\times$ preserves the Heisenberg representation. The extension problem from $J^1$ to $J$ has a transparent ambiguity: two extensions differ by a character of $E^\times/(E^\times\cap J^1)$. Fix the extension $\Lambda_\theta$ whose central character is $\theta|_{F^\times}$ and whose action on the $E^\times$-normalization of the Heisenberg model agrees with $\theta$ on the common scalar and deep-unit subgroup.

**Proposition 6.3 (existence and uniqueness of the tame extension).** Under the tame minimal hypotheses above, $\eta_\beta$ extends to an irreducible representation $\Lambda_\theta$ of $J$. The conditions just stated determine it uniquely up to isomorphism, and replacing $\beta$ by another representative of the same leading character gives an isomorphic pair $(J,\Lambda_\theta)$.

**Proof strategy.** The quotient acting on the finite symplectic space $J^1/H^1$ is cyclic-by-prime-to-$p$. The Heisenberg representation has a canonical linear action of this quotient once its scalar on $E^\times$ is prescribed.

**Proof.** Realize $\eta_\beta$ by induction from a maximal isotropic subgroup as in Lemma 6.2. An element of $E^\times$ permutes the isotropic models. The averaging intertwiner between two such models is nonzero and unique up to scalar; normalize it to be the identity on the common central line. Composition scalars form a cocycle on the cyclic quotient $E^\times/F^\times U_E^1$. In the unramified case this quotient is generated by a uniformizer, and in the ramified case it has order at most two after the scalar valuation is removed. Rescaling one generator kills the cocycle. Prescribing its scalar according to $\theta$ removes the remaining ambiguity. Changing $\beta$ within its allowed coset changes $\vartheta_\beta$ by a character trivial on $H^1$, hence changes neither the Heisenberg representation nor the normalized extension. $\square$

The positive-depth representation will be $\mathrm{c\mbox{-}Ind}_J^G\Lambda_\theta$. Its irreducibility is not automatic; it rests on the intertwining calculation next.

## 7. The tame induction theorem

### 7.1 Intertwining of the type

The leading term $\beta$ should force every intertwiner to preserve the quadratic lattice chain. That expectation is exact.

**Theorem 7.1 (tame intertwining).** Let $(E,\theta)$ be a minimal tame admissible pair of positive level, and let $(J,\Lambda_\theta)$ be the type of Chapter 6. Then

$$
I_G(\Lambda_\theta)=J.
$$

**Proof strategy.** First intertwine the simple character. Commutators show that an intertwiner must conjugate the leading class of $\beta$ to itself at the relevant precision. Successive approximation then moves it into $E^\times$ times a deep congruence subgroup. The Heisenberg representation removes the final possible cosets.

**Proof.** Suppose $g$ intertwines $\Lambda_\theta$. It then intertwines a constituent $\vartheta_\beta$ of the restriction to $H^1$. For every sufficiently deep $x$ for which both $1+x$ and $g(1+x)g^{-1}$ lie in $H^1$, equality of the two characters gives

$$
\psi\!\left(\operatorname{tr}_A((g^{-1}\beta g-\beta)x)\right)=1.
$$

Trace duality places $g^{-1}\beta g-\beta$ in the dual radical power. On the first nonzero graded quotient, $g$ therefore normalizes the centralizer of the leading class of $\beta$. By Lemma 6.1 that centralizer is the image of $E$. Thus the leading graded part of $g$ belongs to $E^\times$.

Multiply $g$ on the left by a suitable element of $E^\times$. The remainder is congruent to $1$ at the first relevant lattice precision. Repeating the argument one radical layer at a time moves the remainder into $U_{\mathfrak A}^{\lfloor(n+1)/2\rfloor}$. At the layers where the commutator pairing is nontrivial, nondegeneracy in Lemma 6.2 says that a class outside $J^1/H^1$ cannot intertwine $\eta_\beta$. Hence the remainder lies in $J^1$. We have shown $g\in E^\times J^1=J$. Every element of $J$ plainly intertwines $\Lambda_\theta$, proving equality. $\square$

Tameness enters twice: it makes trace duality on the decisive graded layer nondegenerate in the required form, and it ensures that the successive centralizer lift has no inseparable residue obstruction.

### 7.2 Irreducibility and supercuspidality

**Theorem 7.2 (tame quadratic induction).** For a minimal tame admissible pair of positive level,

$$
\pi(E,\theta)=\mathrm{c\mbox{-}Ind}_{J}^{G}\Lambda_\theta
$$

is irreducible, admissible, and supercuspidal. Its central character is $\theta|_{F^\times}$.

**Proof.** The group $J/Z$ is compact, Proposition 6.3 gives an irreducible inducing representation, and Theorem 7.1 gives the exact intertwining set. Theorem 3.1 proves irreducibility and admissibility; Proposition 3.2 proves supercuspidality. Scalars act on the compact induction exactly as they act on $\Lambda_\theta$, namely through $\theta|_{F^\times}$. $\square$

For a nonminimal admissible pair, choose $\theta=\theta_0(\chi\circ N_{E/F})$ as in Proposition 2.2 and define

$$
\pi(E,\theta)=\pi(E,\theta_0)\otimes(\chi\circ\det).
$$

This is independent of the chosen decomposition. Indeed the determinant of the multiplication action of $x\in E^\times$ is $N_{E/F}(x)$, so a determinant twist changes the torus character by $\chi\circ N$; the same equality holds on the full inducing group.

### 7.3 Equivalence and exhaustivity

**Theorem 7.3 (classification within the tame quadratic class).** Let $(E,\theta)$ and $(E',\theta')$ be tame admissible pairs. Then

$$
\pi(E,\theta)\simeq\pi(E',\theta')
$$

if and only if the pairs are equivalent. Conversely, every irreducible supercuspidal representation containing either a regular depth-zero nonsplit-torus type or a positive-depth tame quadratic type is $\pi(E,\theta)$ for a unique equivalence class of admissible pairs.

**Proof strategy.** An isomorphism forces the types to intertwine. The leading character recovers the embedded quadratic field as its matrix centralizer, and then the normalizer has only the identity and $\sigma$. Exhaustivity is Frobenius reciprocity followed by irreducibility of compact induction.

**Proof.** The depth-zero case is Theorem 5.1. At positive depth, Mackey theory applied to a nonzero map between the compact inductions supplies $g\in G$ intertwining the two simple characters. The first graded calculation in Theorem 7.1 gives

$$
gE g^{-1}=E'.
$$

After conjugating, assume $E=E'$. The normalizer quotient is $\{1,\sigma\}$, so comparison on $E^\times$ gives $\theta'=\theta$ or $\theta^\sigma$. Thus the pairs are equivalent. The converse follows by conjugating the type.

If an irreducible $\Pi$ contains one of the displayed types, Frobenius reciprocity gives a nonzero map $\mathrm{c\mbox{-}Ind}_J^G\Lambda_\theta\to\Pi$. The source is irreducible, and the image is a nonzero subrepresentation of $\Pi$; hence the map is an isomorphism. Uniqueness follows from the first part. $\square$

The exhaustivity statement is deliberately qualified by the type contained in $\Pi$. It is not a classification of primitive wild supercuspidals.

### 7.4 Types and inertial classes

Let $J^0$ be the maximal compact subgroup of $J$, and let $\lambda_\theta=\Lambda_\theta|_{J^0}$, taking an irreducible constituent if the restriction splits. The conjugates of the constituents form one $J$-orbit, so the choice does not affect typicality.

**Proposition 7.4.** An irreducible smooth representation $\Pi$ contains $\lambda_\theta$ if and only if

$$
\Pi\simeq\pi(E,\theta)\otimes(\chi\circ\det)
$$

for an unramified character $\chi$ of $F^\times$.

**Proof.** The argument is the same as Proposition 5.2. The compact datum fixes the action of $J^0$ but not the scalar assigned to a valuation generator of $J/J^0Z$. Choosing that scalar extends $\lambda_\theta$ to $J$. Two choices differ by a character trivial on $J^0$, hence by an unramified determinant character. Intertwining and irreducibility then identify $\Pi$ with the corresponding compact induction. $\square$

## 8. Character calculations

### 8.1 The compact-induction formula

For a regular semisimple $g\in G$, the formula of Section 3.4 specializes to

$$
\Theta_{\pi(E,\theta)}(g)
=\sum_{x\in J\backslash G/C_G(g)\atop xgx^{-1}\in J}
\operatorname{tr}\Lambda_\theta(xgx^{-1}).
$$

Every set in this formula is finite. It is an exact character algorithm: decide which conjugates of $g$ enter the compact-mod-center subgroup, then take finite-dimensional traces. Its most important qualitative consequence is immediate.

**Proposition 8.1.** Let $(E,\theta)$ be a tame admissible pair and let $J$ be its inducing subgroup. If the conjugacy class of a regular semisimple $g$ does not meet $J$, then $\Theta_{\pi(E,\theta)}(g)=0$.

**Proof.** Every term in the compact-induction formula is indexed by a conjugate of $g$ lying in $J$. Under the stated hypothesis the index set is empty, so the sum is zero. $\square$

This vanishing is often more useful than a closed formula. Split elements sufficiently far from the center do not meet the elliptic inducing subgroup, whereas elliptic elements in the matching torus do.

### 8.2 Depth-zero regular elements

Let $\pi(E,\theta)$ have depth zero. If $g\in K$ has regular reduction $\overline g$, only the $ZK$-coset contributes. The finite table of Theorem 4.1 gives

$$
\Theta_\pi(g)=
\begin{cases}
0,&\overline g\text{ split regular},\\
-\overline\theta(t)-\overline\theta(t^q),
&\overline g\text{ elliptic with eigenvalue }t\in k_2^\times.
\end{cases}
$$

For scalar or nonsemisimple reduction one must retain the scalar and unipotent rows of that table and, near the center, possibly more compact-induction cosets. The regular-reduction hypothesis is therefore essential.

These values already distinguish the orbit $\{\overline\theta,\overline\theta^q\}$. Orthogonality on $k_2^\times$ shows that two regular characters producing the same elliptic values lie in the same Frobenius orbit.

### 8.3 Positive-depth elliptic elements

For a positive-depth type, traces reduce to a finite Heisenberg calculation. If $y\in J$ is regular elliptic and its image acts on $J^1/H^1$ without fixed vectors, the induced-model trace is

$$
\operatorname{tr}\Lambda_\theta(y)
=\theta(y_E)\,\gamma_\beta(y),
$$

where $y_E$ is the $E^\times$ component of $y$ modulo $J^1$ and

$$
\gamma_\beta(y)
=\frac{1}{|L|}
\sum_{x\in L}\vartheta_\beta([y,x])
$$

for any maximal isotropic subgroup $L/H^1$ used in the Heisenberg model. The quotient is finite, and changing $L$ leaves the trace unchanged. Thus $\gamma_\beta(y)$ is an explicit finite Gauss sum, not an unspecified scalar.

**Proposition 8.2 (two conjugate contributions).** Suppose $g\in E^\times$ is regular and its $G$-conjugacy class meets $J$ only through the two normalizer embeddings of $E$. Then

$$
\Theta_{\pi(E,\theta)}(g)
=\operatorname{tr}\Lambda_\theta(g)
+\operatorname{tr}\Lambda_\theta(g^\sigma).
$$

**Proof.** The centralizer of $g$ is $E^\times$. The relevant double-coset set in the compact-induction formula is therefore the quotient of the normalizer by $E^\times$, which has the two representatives $1$ and $\sigma$. Substitution gives the formula. $\square$

The stated meeting hypothesis matters near the center, where additional congruence cosets can occur. Away from that singular range, the formula makes the symmetry $\theta\leftrightarrow\theta^\sigma$ visible.

### 8.4 What the character detects

The character calculations serve three purposes. First, they verify equivalence of conjugate pairs without choosing an inducing model. Second, they recover the torus and its character on a dense regular set, giving an independent proof of injectivity in Theorem 7.3. Third, finite Gauss sums are the bridge to root numbers. They do not produce a uniform elementary formula at elements arbitrarily close to the center; there the character is locally integrable but can have several depth-dependent terms.

## 9. Whittaker and Kirillov models

### 9.1 Genericity from cuspidality

Every irreducible supercuspidal representation of $G$ is generic.

**Theorem 9.1.** Let $\pi=\pi(E,\theta)$. Then

$$
\dim\operatorname{Hom}_N(\pi,\psi)=1,
$$

where $N$ is the upper unipotent subgroup and $\psi\!\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)=\psi(x)$.

**Proof strategy.** Existence follows by restricting the compact induction to $N$ and finding an open orbit on which the inducing character matches $\psi$. Uniqueness is the rank-one Whittaker theorem.

**Proof.** Mackey decomposition for $N\backslash G/J$ expresses $\operatorname{Hom}_N(\pi,\psi)$ as a sum of

$$
\operatorname{Hom}_{N\cap xJx^{-1}}(\Lambda_\theta^x,\psi).
$$

Choose $x$ so that the linear functional $u\mapsto\operatorname{tr}_A(\beta u)$ on the relevant upper-nilpotent lattice has conductor zero. The simple-character formula then makes the displayed Hom space nonzero. Thus a Whittaker functional exists. The previously established uniqueness theorem for $\mathrm{GL}_2$ makes its dimension one. $\square$

### 9.2 The compact Kirillov model

For $W$ in the Whittaker model put

$$
\kappa_W(y)=W\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right).
$$

Because the Jacquet module of $\pi$ is zero, the Kirillov theorem gives

$$
\mathcal K(\pi,\psi)=C_c^\infty(F^\times).
$$

This equality is a sharp analytic signature of supercuspidality. Principal and special representations have asymptotic character tails near $0$; a supercuspidal Kirillov function has compact support in both valuation directions. Consequently every standard zeta integral is a Laurent polynomial and

$$
L(s,\pi\otimes\chi)=1
$$

for every character $\chi$ of $F^\times$ in the standard degree-two zeta theory.

### 9.3 A toric Whittaker function

Choose a nonzero vector $v$ in the inducing space and a compactly induced function $f_v$ supported on $J$ with $f_v(1)=v$. Averaging against $\psi^{-1}$ over the compact quotient of $N\cap J$ gives

$$
W_v(g)=\int_{N\cap J\backslash N}
\ell\bigl(f_v(ng)\bigr)\psi(-n)\,dn,
$$

where $\ell$ is a nonzero matching functional on the inducing space. Compact support of $f_v$ makes the integral a finite sum after choosing a sufficiently small open subgroup. This formula supplies explicit Whittaker functions whose values are finite sums of values of $\theta$ and $\vartheta_\beta$. It will be used to choose an integral normalization in Chapter 14.

## 10. Conductors

### 10.1 Congruence subgroups and the conductor

For $r\ge0$, define

$$
K_1(\mathfrak p^r)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathcal O):
c\in\mathfrak p^r,\ d\equiv1\pmod{\mathfrak p^r}
\right\}.
$$

For an irreducible generic representation $\Pi$, its conductor exponent is

$$
a_F(\Pi)=\min\{r\ge0:\Pi^{K_1(\mathfrak p^r)}\ne0\}.
$$

The subgroup fixes a vector rather than merely a line, so its lower-right congruence is needed to accommodate a ramified central character. Replacing it by the larger subgroup with only $c\equiv0$ would measure a different level.

### 10.2 The quadratic conductor formula

**Theorem 10.1 (conductor of a tame admissible pair).** Let $(E,\theta)$ be a tame admissible pair. Then

$$
\boxed{\ a_F(\pi(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).\ }
$$

Here $\mathfrak d_{E/F}$ is the discriminant ideal and $f(E/F)$ is the residue degree.

**Proof strategy.** Intersect the type with conjugates of $K_1(\mathfrak p^r)$ and apply Mackey theory. A fixed vector can first appear only when the congruence lattice annihilates the simple character. The trace-dual shift contributes the discriminant exponent, and each $E$-unit layer contributes its residue degree.

**Proof.** Frobenius reciprocity and Mackey decomposition give

$$
\pi(E,\theta)^{K_1(\mathfrak p^r)}
\simeq
\bigoplus_{JgK_1}
\operatorname{Hom}_{J\cap gK_1g^{-1}}(\Lambda_\theta,1).
$$

Use the lattice-chain basis in which $g$ is represented by a relative shift of the two adjacent lattices. If $r<v_F(\mathfrak d_{E/F})+f,a_E(\theta)$, one of the intersections contains a unit $1+x$ on which

$$
\Lambda_\theta(1+x)=\psi_E(\beta x)\ne1.
$$

The inequality is exactly the failure of the congruence lattice to lie in the annihilator $\mathfrak p_E^{-d(E/F)}\beta^{-1}$. Hence every Hom space vanishes.

At

$$
r_0=v_F(\mathfrak d_{E/F})+f,a_E(\theta),
$$

choose the lattice shift for which the lower row of $K_1(\mathfrak p^{r_0})$ lands in that annihilator. The simple character is then trivial on the intersection. The quotient of the intersection acting on the Heisenberg model is maximal isotropic, so its fixed space is one-dimensional. The matching double coset therefore contributes one line. All other double cosets either contain a nontrivial simple-character element or are excluded by the intertwining theorem. Thus the first invariant occurs exactly at $r_0$. $\square$

The proof is a conductor computation entirely inside lattices. The formula separates field ramification from character ramification.

### 10.3 Depth zero and the two tame ramification patterns

For the unramified quadratic extension, $v_F(\mathfrak d_{E/F})=0$ and $f(E/F)=2$. Hence

$$
a_F(\pi(E,\theta))=2a_E(\theta).
$$

A regular depth-zero character has $a_E(\theta)=1$, giving conductor $2$. Positive-depth unramified examples have even conductor.

For a tamely ramified quadratic extension, $v_F(\mathfrak d_{E/F})=1$ and $f(E/F)=1$, so

$$
a_F(\pi(E,\theta))=a_E(\theta)+1.
$$

Admissibility forces genuine ramification on $U_E^1$, hence $a_E(\theta)\ge2$ and the representation has conductor at least $3$. These parity patterns often identify the quadratic source from the conductor, though twisting can change the visible parity.

### 10.4 Minimality and old levels

For a minimal pair, Theorem 10.1 gives the minimal conductor in its determinant-twist family. For $r\ge a_F(\pi)$, vectors fixed by $K_1(\mathfrak p^r)$ are oldforms obtained by translating the newvector. The exact dimension will be proved in Chapter 13. Before the first level, the obstruction is not a dimension count: it is the nontrivial leading character exhibited in the proof of Theorem 10.1.

## 11. Twists and central characters

### 11.1 Twisting an admissible pair

Let $\chi:F^\times\to\mathbf C^\times$ be smooth. Since $\det(x)=N_{E/F}(x)$ for multiplication by $x\in E^\times$, the inducing data give the exact identity

$$
\boxed{\ \pi(E,\theta)\otimes(\chi\circ\det)
\simeq\pi(E,\theta(\chi\circ N_{E/F})).\ }
$$

The ratio with the conjugate is unchanged:

$$
\frac{\theta(\chi\circ N)}{\theta^\sigma(\chi\circ N)}
=\frac{\theta}{\theta^\sigma}.
$$

Thus admissibility survives every determinant twist.

### 11.2 Exact conductor under twisting

Combining the twist identity with Theorem 10.1 gives a formula that automatically records cancellation:

$$
\boxed{\ a_F(\pi(E,\theta)\otimes\chi)
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E(\theta(\chi\circ N_{E/F})).\ }
$$

Here and below $\otimes\chi$ abbreviates $\otimes(\chi\circ\det)$. This is more accurate than a formula using only $a_F(\pi)$ and $a_F(\chi)$, because two characters of the same conductor can cancel on the last unit layer.

If $\theta$ is minimal and $\chi$ is more deeply ramified than $\theta$ after pullback, then the pullback dominates and

$$
a_E(\theta(\chi\circ N))=a_E(\chi\circ N).
$$

If the conductors are equal, either the same equality holds or cancellation lowers the result; one must inspect the leading characters.

### 11.3 Central characters and self-duality

The construction gives

$$
\omega_{\pi(E,\theta)}=\theta|_{F^\times}.
$$

After twisting,

$$
\omega_{\pi\otimes\chi}=\omega_\pi\chi^2.
$$

The contragredient follows by dualizing the compact induction:

$$
\pi(E,\theta)^\vee\simeq\pi(E,\theta^{-1}).
$$

Consequently $\pi(E,\theta)$ is self-dual precisely when the admissible pairs $(E,\theta)$ and $(E,\theta^{-1})$ are equivalent, that is, when

$$
\theta^{-1}=\theta
\quad\text{or}\quad
\theta^{-1}=\theta^\sigma.
$$

The first alternative is usually incompatible with admissibility; the second says $\theta|_{\ker N_{E/F}}$ has the expected conjugate-inverse symmetry. Essential self-duality is tested after multiplying by a norm character in the same way.

### 11.4 Counterexamples to naive conductor rules

It is false that twisting always replaces $a_F(\pi)$ by the larger of $a_F(\pi)$ and $2a_F(\chi)$. Take $\theta=\theta_0(\chi^{-1}\circ N)$ with $\theta_0$ minimal. Then twisting by $\chi$ lowers the torus character to $\theta_0$, and the conductor drops. Conversely, two twists of equal conductor can yield different representation conductors when their leading additive characters cancel in one case and not in the other. The exact pair formula is the reliable rule.

## 12. Local constants and quadratic induction

### 12.1 Normalization and the quadratic factor

The Whittaker functional equation defines $\epsilon(s,\pi,\psi)$. Since every supercuspidal standard factor is $1$, gamma and epsilon coincide. For conductor-zero $\psi$,

$$
\epsilon(s,\pi,\psi)
=\epsilon(1/2,\pi,\psi)
q^{-a_F(\pi)(s-1/2)}.
$$

To compare this with a character of $E^\times$, one normalization issue must be made explicit. The norm subgroup has index two in $F^\times$ for a quadratic local extension. Denote by $\omega_{E/F}$ the nontrivial character of $F^\times/N(E^\times)$. The index statement follows directly in the tame case: valuations give the unramified quotient when $E/F$ is unramified, while the residue norm and the first unit layer give the ramified quotient when $E/F$ is ramified.

Choose the **tame rectifier** $\Delta_{E/F}:E^\times\to\mathbf C^\times$ characterized by

$$
\Delta_{E/F}|_{F^\times}=\omega_{E/F}
$$

and by the Gauss-sum normalization in Theorem 12.1 below. In the unramified case it is the unramified character with $\Delta_{E/F}(\varpi)=-1$. In the tamely ramified case it is a tamely ramified extension of $\omega_{E/F}$; the Gauss-sum condition fixes its remaining value on a uniformizer.

Define the quadratic-induction normalization by

$$
\operatorname{AI}_{E/F}(\theta)
=\pi(E,\theta\Delta_{E/F}).
$$

Then

$$
\omega_{\operatorname{AI}_{E/F}(\theta)}
=\theta|_{F^\times}\omega_{E/F}.
$$

The rectifier changes neither a positive conductor nor admissibility. It is necessary because the direct type normalization and the induction normalization assign different tame signs.

### 12.2 The induction formula

Let one-dimensional local constants over $E$ use $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$ and the self-dual measure. Put

$$
\lambda(E/F,\psi)=\epsilon(1/2,\omega_{E/F},\psi).
$$

This is a root-number constant, independent of $s$. The discriminant power in the induction formula is carried by the conductor of $\psi_E$, not by an extra variable hidden in $\lambda(E/F,\psi)$.

**Theorem 12.1 (quadratic induction formula).** For every tame admissible character $\theta$,

$$
\boxed{
\epsilon(s,\operatorname{AI}_{E/F}(\theta),\psi)
=\lambda(E/F,\psi)\epsilon(s,\theta,\psi_E).
\ }
$$

Moreover the exponent of $q^{-s}$ on the right is

$$
v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta),
$$

in agreement with Theorem 10.1.

**Proof strategy.** Use the toric Whittaker function of Section 9.3 and unfold its functional equation. The integral over the two-dimensional $F$-space $E$ becomes the one-dimensional Fourier transform over $E$. Comparing self-dual measures contributes the quadratic factor.

**Proof.** Choose the Whittaker function induced from the simple character and decompose $E$ into valuation shells. On each shell the determinant is $N_{E/F}$ and the upper-unipotent phase is $\psi_E$. The Weyl transform is therefore the additive Fourier transform on $E$. Applying the one-dimensional functional equation over $E$ contributes $\epsilon(s,\theta,\psi_E)$.

The $F$-self-dual measure transported to the two-dimensional space $E$ differs from the $\psi_E$-self-dual measure by the square root of the discriminant. On finite unit quotients the remaining ratio is the quadratic Gauss sum $\lambda(E/F,\psi)$. The definition of $\Delta_{E/F}$ makes the torus action agree with this sign. Thus the proportionality scalar is the displayed product.

Finally the annihilator of $\mathcal O_E$ is $\mathfrak D_{E/F}^{-1}$. The Fourier transform of a conductor-$a_E(\theta)$ unit character is supported at the dual valuation shifted by $d(E/F)$. Counting an $E$-valuation shell as an $F$-space multiplies its length by $f(E/F)$. Hence the total exponent is the stated discriminant-plus-conductor expression. $\square$

### 12.3 Gauss sums and root numbers

If $\theta$ is unitary, then $\epsilon(1/2,\operatorname{AI}_{E/F}(\theta),\psi)$ has absolute value one. It is explicitly the product of two normalized finite sums. If $a=a_E(\theta)\ge1$ and $c\in E^\times$ has

$$
v_E(c)=a+d(E/F),
$$

then

$$
\epsilon(1/2,\theta,\psi_E)
=\theta(c)q_E^{-a/2}
\sum_{u\in U_E^0/U_E^a}
\theta(u)^{-1}\psi_E(u/c),
$$

with the quotient sum interpreted using representatives and the standard unit-volume normalization. The analogous quadratic sum computes $\lambda(E/F,\psi)$. Character orthogonality proves that each normalized sum has absolute value one: multiplying the sum by its complex conjugate leaves only pairs with equal quotient class.

This formula is useful computationally and also explains why root numbers can vary while conductors remain fixed. The conductor records the size of the finite quotient; the Gauss sum records the phase of the character on it.

Two elementary cases calibrate the factor $\lambda(E/F,\psi)$. If $E/F$ is unramified and $\psi$ has conductor zero, $\omega_{E/F}$ is unramified and the chosen normalization gives $\lambda(E/F,\psi)=1$. If $E/F$ is tamely ramified, $\omega_{E/F}$ has conductor one and $\lambda(E/F,\psi)$ is the normalized quadratic Gauss sum of $k^\times$. Its square is $\omega_{E/F}(-1)$. Indeed, if

$$
G_\omega=\sum_{u\in k^\times}\omega(u)\overline\psi(u),
$$

then a change of variables followed by additive-character orthogonality gives $G_\omega^2=q\omega(-1)$. Division by $q^{1/2}$ proves the assertion. This is the only new tame sign contributed by a ramified quadratic extension; all deeper phase information belongs to the character sum over $E$.

### 12.4 Changes of additive character

For $c\in F^\times$, let $\psi_c(x)=\psi(cx)$ and use its self-dual measure. The degree-two scaling law gives

$$
\epsilon(s,\pi,\psi_c)
=\omega_\pi(c)|c|^{2s-1}\epsilon(s,\pi,\psi).
$$

On the right side of Theorem 12.1, the one-dimensional scaling law over $E$ contributes

$$
\theta(c)|N_{E/F}(c)|^{s-1/2}
=\theta(c)|c|^{2s-1},
$$

while the quadratic factor contributes $\omega_{E/F}(c)$. Their product is the central character of $\operatorname{AI}_{E/F}(\theta)$, so the induction formula is compatible with every change of additive character.

## 13. The newvector theorem

### 13.1 The unique first fixed line

The conductor theorem located the first congruence subgroup with fixed vectors. Newvector theory strengthens existence to uniqueness and then describes every higher level.

**Theorem 13.1 (newvector and oldforms).** Let $\pi=\pi(E,\theta)$ and put $n=a_F(\pi)$. Then

$$
\dim_\mathbf C\pi^{K_1(\mathfrak p^r)}=
\begin{cases}
0,&r<n,\\
r-n+1,&r\ge n.
\end{cases}
$$

In particular $\pi^{K_1(\mathfrak p^n)}$ is a line, called the newvector line.

The word “new” refers to first occurrence. At level $n+j$, the additional $j$ dimensions arise from diagonal translates of the newvector; no new torus character appears.

### 13.2 Proof in the Kirillov model

**Proof strategy for Theorem 13.1.** Translate the congruence invariance into support and Fourier-support conditions on a Kirillov function. The uncertainty interval has length $r-n+1$. At first occurrence it contains a single valuation shell.

**Proof.** Use the Kirillov model $C_c^\infty(F^\times)$. Right translation by

$$
n(b)=\begin{pmatrix}1&b\\0&1\end{pmatrix}
$$

acts by

$$
(n(b)\phi)(y)=\psi(by)\phi(y).
$$

Invariance under $b\in\mathcal O$ therefore forces no additional restriction because $\psi$ is trivial on $\mathcal O$ when $y\in\mathcal O$. Invariance under the diagonal unit part of $K_1$ makes the relevant functions constant on unit cosets after the central character has been accounted for.

The lower unipotent subgroup is conjugate to the upper one by the Weyl element. Its invariance becomes a support condition on the Weyl transform of $\phi$. The functional equation shows that the Weyl transform reverses valuations and shifts them by exactly $n$. Thus at level $r$ a fixed Kirillov function is supported on valuation shells in an interval

$$
0\le j\le r-n.
$$

For each $j$ the characteristic function of $\varpi^j\mathcal O^\times$, with the required unit character when the central character is ramified, satisfies both conditions. These functions have disjoint support and are linearly independent. Conversely, upper invariance decomposes any fixed function into such shell functions, and lower invariance excludes shells outside the interval. Hence the dimension is the number of integers in it, namely $r-n+1$ when $r\ge n$ and zero otherwise. $\square$

This argument also reproves Theorem 10.1 once the Weyl shift is calculated from the toric type. The earlier lattice proof was retained because it displays separately the discriminant and character contributions.

### 13.3 The normalized Whittaker newform

Let $W^{\mathrm{new}}$ span the newvector line in the $\psi$-Whittaker model and normalize it by

$$
W^{\mathrm{new}}(1)=1.
$$

**Proposition 13.2 (essential Whittaker values).** For a supercuspidal $\pi(E,\theta)$,

$$
W^{\mathrm{new}}\!\left(
\begin{pmatrix}y&0\\0&1\end{pmatrix}
\right)=\mathbf 1_{\mathcal O^\times}(y).
$$

The equality uses the conductor-zero additive character and the displayed normalization.

**Proof.** The proof of Theorem 13.1 shows that the first fixed space corresponds to the single valuation shell $\mathcal O^\times$. Diagonal-unit invariance makes the function constant there, and $W(1)=1$ fixes that constant. It vanishes on all other shells because the allowed interval has length one. $\square$

Consequently

$$
Z(s,W^{\mathrm{new}},1)
=\int_{\mathcal O^\times}d^\times y=1,
$$

which is the standard local factor of a supercuspidal representation. For a ramified twist in the zeta integral, this same vector can give zero by unit-character orthogonality; an adapted translate in the Kirillov core is then the correct test vector.

The Weyl transform of $W^{\mathrm{new}}$ spans the dual newvector line. Evaluating the functional equation on it recovers

$$
\epsilon(s,\pi,\psi)
=\epsilon(1/2,\pi,\psi)q^{-n(s-1/2)}.
$$

Thus the newvector simultaneously records the conductor and the root-number scalar.

### 13.4 Higher fixed spaces

Let $v_0$ be a nonzero newvector and put

$$
v_j=\pi\!\left(\begin{pmatrix}\varpi^{-j}&0\\0&1\end{pmatrix}\right)v_0
\qquad(0\le j\le r-n).
$$

Then $v_0,\ldots,v_{r-n}$ form a basis of $\pi^{K_1(\mathfrak p^r)}$. In the Kirillov model their supports occupy the distinct shells $\varpi^j\mathcal O^\times$, up to the harmless common shift determined by the chosen action convention. This basis makes degeneracy maps transparent: passing from level $r$ to $r+1$ retains the old basis and adds one endpoint shell.

## 14. Integral newvectors

### 14.1 Integral inducing data

Let $R$ be a discrete valuation ring of characteristic zero with fraction field $L\subset\mathbf C$, maximal ideal $\mathfrak m_R$, and residue field of characteristic $\ell$. Assume that all values of the finite-order part of $\theta$ lie in $R^\times$ and that every unramified value used in the central action is also a unit. After a finite extension of $L$, this always holds for a unitary $\theta$.

An **integral model** of the inducing representation is a finite free $R$-module $\Lambda_R$ carrying $J$ such that

$$
\Lambda_R\otimes_R L\simeq\Lambda_\theta.
$$

At depth zero, take the function model of Chapter 4 with $R$-valued functions and the orbit-sum relation. At positive depth, take the induced Heisenberg model from a maximal isotropic subgroup. All action matrices are permutation matrices multiplied by values of $\theta$ and $\vartheta_\beta$, hence have entries in $R$ and determinant in $R^\times$. The resulting module is finite free and stable.

### 14.2 The integral compact-induction lattice

Define

$$
\Pi_R=\mathrm{c\mbox{-}Ind}_{J}^{G}\Lambda_R.
$$

It consists of compactly supported functions modulo $J$ with values in $\Lambda_R$ and the usual covariance. It is torsion-free, stable under $G$, and

$$
\Pi_R\otimes_R L\simeq\pi(E,\theta)_L.
$$

**Proposition 14.1.** The lattice $\Pi_R$ is admissible over $R$: for every compact open subgroup $C\subseteq G$, the module $\Pi_R^C$ is finite over $R$.

**Proof.** The tame intertwining calculation bounds the relative position of a lattice chain supporting a $C$-fixed vector. In Cartan coordinates, a double coset beyond that bound would make $J\cap gCg^{-1}$ contain a radical element on which the simple character is nontrivial; the corresponding invariant module is zero. Thus only finitely many double cosets $J\backslash G/C$ contribute. On each, the value lies in the finite module of invariants of an intersection subgroup acting on $\Lambda_R$. Hence $\Pi_R^C$ embeds in a finite direct sum of copies of $\Lambda_R$ and is finite. Since $R$ is a DVR and $\Pi_R$ is torsion-free, each fixed module is finite free. $\square$

### 14.3 A primitive integral newvector

**Theorem 14.2 (integral newvector).** Assume $\ell\ne p$ and put $n=a_F(\pi(E,\theta))$. The intersection

$$
\Pi_R^{K_1(\mathfrak p^n)}
=\Pi_R\cap\pi(E,\theta)_L^{K_1(\mathfrak p^n)}
$$

is a free rank-one $R$-module. It has a generator whose normalized Whittaker function takes the value $1$ at the identity and takes values in $R$ on all of $G$.

**Proof strategy.** Intersect a one-dimensional $L$-space with a full lattice, then use the explicit toric Whittaker sum to make the generator primitive rather than merely integral up to a denominator.

**Proof.** The fixed line over $L$ is one-dimensional by Theorem 13.1. Its intersection with the torsion-free admissible lattice is a nonzero fractional ideal of $R$, hence free of rank one. Choose a generator $v$ not divisible by $\mathfrak m_R$.

The Whittaker functional of Section 9.3 is a finite sum of unit-valued inducing characters. Scale it so that the corresponding Kirillov function is $\mathbf1_{\mathcal O^\times}$. Every nonzero finite Fourier sum occurring here has norm a power of $p$; the assumption $\ell\ne p$ makes it a unit of $R$. It follows that the value on $v$ at the identity is a unit: if it lay in $\mathfrak m_R$, Fourier inversion on the finite $p$-group layers would put every value of $v$ in $\mathfrak m_R\Lambda_R$, contradicting primitivity. Dividing by that unit gives $W(1)=1$ without leaving $R$. Translates of a compactly induced $R$-valued function remain $R$-valued, so the entire Whittaker function is integral. $\square$

This is the integral content needed in global applications: the first local fixed line has a canonical primitive generator up to $R^\times$, not merely up to $L^\times$.

### 14.4 Base change and reduction

Fixed vectors do not commute with arbitrary reduction unless the relevant finite quotient orders are invertible. We state the safe form.

**Theorem 14.3 (coefficient change at banal residue characteristic).** Assume

$$
\ell\nmid q(q-1)(q+1).
$$

Let $R\to R'$ be a homomorphism to a DVR or a field. Then, for every $r\ge n$,

$$
\Pi_R^{K_1(\mathfrak p^r)}\otimes_R R'
\xrightarrow{\sim}
(\Pi_R\otimes_R R')^{K_1(\mathfrak p^r)}.
$$

In particular the reduction of a primitive newvector is nonzero and spans the first fixed line.

**Proof strategy.** At a fixed level the action factors through a finite quotient. The displayed numerical hypothesis makes its order invertible, so averaging is an idempotent projection onto invariants and commutes with coefficient change.

**Proof.** Restrict to the finite sum of double cosets supporting the level-$r$ fixed space. Smoothness makes the action factor through a quotient whose prime divisors are among $p$ and those dividing $q^2-1$. Under the hypothesis its order is a unit in $R$. The averaging operator

$$
e_C=|C|^{-1}\sum_{c\in C}c
$$

projects onto invariants. Tensor products commute with this idempotent image, proving the isomorphism. The rank-one assertion follows from Theorem 14.2. $\square$

When $\ell$ divides one of these orders, the integral newvector still exists, but reduction can acquire extra fixed vectors because averaging is no longer exact. This is a genuine phenomenon, not a defect of the lattice.

## 15. Examples and boundary cases

### 15.1 Unramified depth zero

Let $E/F$ be unramified quadratic and let $\theta$ be trivial on $U_E^1$ with regular residue character. Then

$$
a_E(\theta)=1,\qquad a_F(\pi(E,\theta))=2.
$$

The type is the inflation of the $(q-1)$-dimensional finite cuspidal representation. Its regular split character values vanish, while an elliptic unit with residue $t\in k_2^\times\setminus k^\times$ has value

$$
-\overline\theta(t)-\overline\theta(t^q).
$$

The newvector is fixed by $K_1(\mathfrak p^2)$ and by no $K_1(\mathfrak p^r)$ with $r<2$. This example is the cleanest warning that “depth zero” does not mean “conductor zero.” Supercuspidality already costs two congruence levels.

### 15.2 Unramified positive depth

Let $E/F$ be unramified and choose a minimal character with $a_E(\theta)=m+1\ge2$. Then

$$
a_F(\pi(E,\theta))=2m+2.
$$

The leading element $\beta$ has valuation $-m-1$ and residue-centralizer $k_2$. Even conductors arise naturally because one $E$-unit layer has $F$-dimension two. If $\chi$ is a character of $F^\times$, the twisted conductor is

$$
2a_E(\theta(\chi\circ N)).
$$

Choosing $\chi$ whose leading norm pullback cancels that of $\theta$ can lower the conductor by more than a superficial maximum rule predicts.

For a concrete residue calculation, take $q=5$ and compose the trace $k_2\to k$ with a nontrivial additive character of $k$. A class $b\in k_2\setminus k$ gives the genuinely quadratic leading term

$$
x\longmapsto\psi\bigl(\operatorname{Tr}_{k_2/k}(bx)\bigr).
$$

Replacing $b$ by $b+c$ with $c\in k$ multiplies this by a norm-derived leading character; the class of $b$ in $k_2/k$ is what survives minimal twisting. Its centralizer in $M_2(k)$ is exactly $k_2$. This finite calculation is the residue shadow of the minimal-leading-term and intertwining arguments.

### 15.3 Tamely ramified quadratic induction

Assume $p\ne2$ and let $E=F(\Pi)$ with $\Pi^2=u\varpi$ for a unit $u$. Then $E/F$ is totally and tamely ramified,

$$
f(E/F)=1,\qquad v_F(\mathfrak d_{E/F})=1.
$$

An admissible character must be nontrivial in a genuinely quadratic way on $U_E^1$; in particular $a_E(\theta)\ge2$. For $a_E(\theta)=2$,

$$
a_F(\pi(E,\theta))=3.
$$

This is the first positive-depth conductor. The lattice chain has period two, the hereditary order is Iwahori, and the Heisenberg quotient is visible at the middle radical layer. The direct type has central character $\theta|_{F^\times}$; the quadratic-induction normalization has central character $\theta|_{F^\times}\omega_{E/F}$.

At this first positive level the character on $U_E^1/U_E^2\simeq k$ is additive. Conjugation sends $\Pi$ to $-\Pi$ modulo the next layer, so a leading character changed by that sign is regular. A norm-derived character, in contrast, is controlled by the trace and has invariant leading coefficient. This gives a quick test for admissibility at conductor two and explains why the resulting representation has odd conductor three.

### 15.4 The primitive wild boundary

When the residue characteristic divides the ramification degree governing the leading stratum, trace on the decisive graded layer can degenerate and the centralizer-lifting argument of Theorem 7.1 no longer applies as written. In residue characteristic two, a ramified quadratic extension is wild; even though it is still a quadratic field, the tame rectifier and congruence calculations above do not cover it.

More importantly, some wild supercuspidals have no quadratic character whose leading term recovers their type. Those are primitive wild types. They require a separate analysis of wild strata, additional extension data, and different intertwining calculations. They remain outside the selected route. The results of this book apply exactly to regular depth-zero types and tame quadratic admissible pairs, and make no exhaustivity assertion beyond that class.

## 16. The reusable local package

### 16.1 Construction and invariants

The theory can be summarized without suppressing its hypotheses. Let $E/F$ be a tame separable quadratic extension and let $\theta$ be admissible.

- At depth zero, $E/F$ is unramified and a regular character of $k_E^\times$ produces a cuspidal representation of $\mathrm{GL}_2(k)$, which is inflated and compactly induced from $Z\mathrm{GL}_2(\mathcal O)$.

- At positive depth, a minimal norm twist of $\theta$ has a leading additive term $\beta$. The centralizer of $\beta$ is $E$, its quadratic lattice chain defines a hereditary order, and a simple character together with its Heisenberg enlargement gives a maximal compact-mod-center type.

- Exact intertwining proves irreducibility and supercuspidality. Equivalent pairs are precisely $F$-isomorphic pairs, so for fixed $E$ the only ambiguity is $\theta\leftrightarrow\theta^\sigma$.

- The central character, twists, contragredient, and conductor are

$$
\omega_\pi=\theta|_{F^\times},
\qquad
\pi^\vee=\pi(E,\theta^{-1}),
$$

$$
\pi(E,\theta)\otimes\chi
=\pi(E,\theta(\chi\circ N)),
$$

$$
a_F(\pi(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).
$$

- In quadratic-induction normalization, a tame rectifier supplies the expected extra quadratic central character and the local-constant formula

$$
\epsilon(s,\operatorname{AI}_{E/F}(\theta),\psi)
=\lambda(E/F,\psi)\epsilon(s,\theta,\psi_E).
$$

- The first $K_1$-fixed space occurs at the conductor and is one-dimensional. Its normalized Whittaker function restricts on the diagonal to $\mathbf1_{\mathcal O^\times}$. Integral inducing data give a primitive integral generator, with coefficient change under the stated invertibility hypothesis.

These assertions contain several internal consistency checks. Conjugating $\theta$ by $\sigma$ changes none of the displayed invariants and exchanges the two elliptic character contributions. Replacing $\theta$ by $\theta(\chi\circ N)$ changes the central character by $\chi^2$, exactly as a determinant twist should, and the conductor formula sees any cancellation on the last unit layer. Dualizing inverts every character, while the conductor and the dimension of the newvector line remain unchanged. Changing $\psi$ multiplies the epsilon factor by the degree-two central-character scalar and leaves the conductor subgroup untouched. Finally, the exponent of $q^{-s}$ in the epsilon factor agrees with the first level at which the Kirillov uncertainty interval is nonempty. A proposed construction failing any one of these checks has almost certainly mixed the direct type normalization with quadratic induction, confused level with conductor exponent, or omitted the discriminant shift.

There is also a practical order for calculations. First minimize the pair by a norm twist. Next determine whether the quadratic extension is unramified or ramified and record its residue degree and discriminant exponent. Then compute the character conductor and apply the boxed conductor formula. Only after these discrete invariants are fixed should one evaluate the finite Gauss sums for the root number. The newvector is then obtained from the single allowed Kirillov shell, and its integral normalization is chosen last. This order separates structural decisions from phase calculations and prevents a choice of uniformizer or additive character from being mistaken for an invariant of the representation.

### 16.2 Final synthesis

The construction begins with a compact geometric fact: a quadratic torus is compact modulo the center. That fact alone is not enough. Regularity removes norm-descended characters; a congruence neighborhood records the leading oscillation; the Heisenberg representation resolves the noncommutative middle layer; and the intertwining calculation certifies that no unwanted symmetry survives. Compact induction then turns finite-level data into an irreducible supercuspidal representation.

Every numerical invariant retains this origin. The discriminant term in the conductor measures the displacement of trace duality. The factor $f(E/F)a_E(\theta)$ counts the size of the character layers as $F$-spaces. The two conjugate embeddings explain the character symmetry. Norm pullback explains determinant twists. The quadratic Gauss factor measures the discrepancy between direct type normalization and quadratic induction. Finally, the one-shell Kirillov function explains both uniqueness of the newvector and the unit-normalized integral lattice.

Thus the tame dihedral class is not merely a list of examples. It is a coherent local package in which torus characters, types, compact induction, character values, conductors, epsilon data, twists, central characters, and newvectors determine and check one another. The package is exactly strong enough for the auxiliary automorphic representations in the chosen route, while the primitive wild boundary remains explicit and untouched.
