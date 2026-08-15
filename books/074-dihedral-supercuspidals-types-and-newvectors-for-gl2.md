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

with $Z$ embedded as scalar matrices. Representations are smooth complex representations unless an integral coefficient ring is explicitly introduced. Haar measure on $G/Z$ is fixed once and for all. The earlier general theory supplies smooth and compact induction, Frobenius reciprocity, Mackey decomposition, contragredients, and distribution characters. The rank-one theory supplies Whittaker uniqueness, the Kirillov core, the identification of the quotient of a Kirillov model by its compact core with the normalized Jacquet module, the one-dimensional local functional equation, and the Whittaker functional equation for an irreducible admissible generic representation with finite-length Jacquet module. It does **not** supply irreducibility from a scalar endomorphism ring, genericity of a cuspidal representation, pointwise character formulas, conductors, or newvectors. Those inputs are proved below for the types constructed here.

For a finite extension $L/F$, write $\mathcal O_L$, $\mathfrak p_L$, $U_L^0=\mathcal O_L^\times$, and

$$
U_L^r=1+\mathfrak p_L^r\quad(r\geq1).
$$

For a smooth character $\chi:L^\times\to\mathbf C^\times$, its conductor exponent is

$$
a_L(\chi)=\min\{r\geq0:\chi|_{U_L^r}=1\}.
$$

Thus $a_L(\chi)=0$ means unramified, while a nontrivial character of $k_L^\times$ inflated to $U_L^0$ has conductor exponent $1$. Its level is $\ell_L(\chi)=\max\{a_L(\chi)-1,0\}$.

Fix a nontrivial additive character $\psi:F\to\mathbf C^\times$ trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. Additive Haar measure is self-dual for $\psi$. For $E/F$ put $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$.

We record the exact trace-duality input because it is not part of the earlier local-extension volume. For a separable quadratic extension define

$$
\mathfrak D_{E/F}^{-1}
=\{x\in E:\operatorname{Tr}_{E/F}(x\mathcal O_E)\subseteq\mathcal O\},
\qquad
d(E/F)=v_E(\mathfrak D_{E/F}).
$$

Then the annihilator of $\mathcal O_E$ under $(x,y)\mapsto\psi_E(xy)$ is precisely $\mathfrak D_{E/F}^{-1}$. Indeed annihilation is equivalent to integral trace because $\psi$ is trivial on $\mathcal O$ and nontrivial on $\varpi^{-1}\mathcal O$. In the tame quadratic cases used here,

$$
d(E/F)=
\begin{cases}
0,&E/F\text{ unramified},\\
1,&E/F\text{ ramified}.
\end{cases}
$$

For an unramified extension, a lift of a separable residue basis has trace-pairing determinant a unit. In the ramified case $p\ne2$ and one may write $E=F(\Pi)$ with $\Pi^2=u\varpi$; the basis $(1,\Pi)$ has trace matrix $\operatorname{diag}(2,2u\varpi)$, so its dual lattice is generated by $1/2$ and $1/(2\Pi)$ and the different is $(2\Pi)=\mathfrak p_E$. The determinant $4u\varpi$ also shows directly that the discriminant has valuation one. In both tame quadratic cases this proves

$$
v_F(\mathfrak d_{E/F})=f(E/F)d(E/F).
$$

Thus no unproved different or discriminant formula is being imported.

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

**Theorem 3.1 (compact-induction criterion).** Suppose $J/Z$ is compact, $\Lambda$ is irreducible, and $Z$ acts on $\Lambda$ through a character. Put $P=\mathrm{c\mbox{-}Ind}_J^G\Lambda$. Assume the following three statements.

1. $I_G(\Lambda)=J$.
2. Every nonzero $G$-subrepresentation of $P$ contains a nonzero vector supported on the identity coset $J$.
3. For every compact open $C\subseteq G$, only finitely many $JgC$ satisfy

   $$
   \operatorname{Hom}_{J\cap gCg^{-1}}(\Lambda,1)\ne0.
   $$

Then $P$ is irreducible and admissible, and $\operatorname{End}_G(P)=\mathbf C$.

**Proof strategy.** The first condition computes the endomorphism algebra. The second is the support-reduction assertion needed to pass from scalar endomorphisms to irreducibility. The third is exactly the separate finiteness assertion needed for admissibility. Keeping them distinct prevents either conclusion from being smuggled into the intertwining calculation.

**Proof.** Frobenius reciprocity and Mackey decomposition give

$$
\operatorname{End}_G(P)
\simeq
\bigoplus_{JgJ\in J\backslash G/J}
\operatorname{Hom}_{J\cap J^g}(\Lambda,\Lambda^g),
$$

with compact support in the double-coset variable. The first hypothesis leaves only $g\in J$, and Schur's lemma makes that summand $\mathbf C$.

Let $0\ne V\subseteq P$. By the second hypothesis, $V$ contains a nonzero function supported on $J$. The functions supported on $J$ form one copy of $\Lambda$ as a $J$-representation. Since $\Lambda$ is irreducible, the $J$-span of that function contains this whole copy; its $G$-span is all of $P$. Hence $V=P$.

Finally Mackey decomposition at level $C$ gives

$$
P^C\simeq
\bigoplus_{JgC\in J\backslash G/C}
\operatorname{Hom}_{J\cap gCg^{-1}}(\Lambda,1).
$$

The third hypothesis leaves finitely many summands, each finite-dimensional because $\Lambda$ is finite-dimensional. Thus $P^C$ is finite-dimensional. $\square$

The earlier general theory proves the endomorphism formula but explicitly does not infer irreducibility or admissibility from it. In Chapters 5 and 7 the same lattice calculation that proves exact intertwining will also prove support reduction and fixed-level finiteness, so all three hypotheses will be discharged rather than assumed.

The intertwining equality is therefore the central calculation in both depth zero and positive depth.

### 3.3 Cuspidality and admissibility

**Proposition 3.2.** Under the hypotheses of Theorem 3.1, every matrix
coefficient of $P$ is compactly supported modulo $Z$. Thus $P$ is
supercuspidal in the compact-coefficient sense. For the types in this book,
vanishing of the Jacquet module will be proved after genericity in Theorem 9.1.

**Proof.** The invariant finite-coset pairing gives an injective map
$\mathrm{c\mbox{-}Ind}_J^G\Lambda^\vee\to P^\vee$. Its image is nonzero, and
$P^\vee$ is irreducible because $P$ is irreducible and admissible. Hence the
map is surjective. A vector on either side is supported on finitely many
$J$-cosets. Pairing two such vectors shows that their coefficient is supported
in a finite union of sets $JgJ$, each compact modulo $Z$.

$\square$

This proof also explains why induction from $E^\times$ alone is usually insufficient. Although $E^\times/Z$ is compact, a character of the bare torus generally has extra intertwiners. The surrounding congruence subgroup in the type removes them.

### 3.4 Characters of compactly induced representations

On an open regular set where the set of fixed inducing cosets is finite and locally constant, the distribution character is represented by the induced formula

$$
\Theta_{\mathrm{c\mbox{-}Ind}\Lambda}(g)
=\sum_{x\in J\backslash G,\;xgx^{-1}\in J}
\operatorname{tr}\Lambda(xgx^{-1}),
$$

where terms are grouped modulo the centralizer of $g$. Regularity alone does
not make this set finite: a compact split element may fix an infinite
apartment. An elliptic regular element has a finite fixed subtree. Indeed its
fixed set is convex; if it were unbounded in the locally finite lattice tree,
it would contain a ray, whose end would be an $F$-rational eigenline. That
would make the element split. This elementary tree argument gives the
finiteness used in Chapter 8. The formula is proved there by applying the
operator to functions supported on individual cosets and taking the trace at
one common compact-open level. The qualification prevents a finite-index
character formula from being applied blindly to an infinite coset space.

## 4. The finite-field cuspidal seed

### 4.1 Regular characters of the nonsplit torus

Let $k_2/k$ be the quadratic extension and let $\tau(x)=x^q$. A character $\vartheta:k_2^\times\to\mathbf C^\times$ is **regular** if

$$
\vartheta\ne\vartheta^\tau.
$$

Equivalently, $\vartheta$ does not factor through the finite-field norm $x\mapsto x^{q+1}$. Indeed the quotient $k_2^\times/k^\times$ is cyclic of order $q+1$, and $\tau$ acts there by inversion. Equality with the conjugate is precisely triviality on the norm-one subgroup.

Regularity is the finite shadow of admissibility. It ensures that the nonsplit torus has only its obvious two normalizer symmetries on the character.

### 4.2 A concrete model

Put $\overline G=\mathrm{GL}_2(k)$ and identify $k_2^\times$ with a nonsplit maximal torus $\overline T$. The tempting quotient of $\operatorname{Ind}_{\overline T}^{\overline G}\vartheta$ obtained by imposing one orbit-sum relation does **not** have dimension $q-1$ and will not be used. Instead we construct the finite cuspidal representation directly from a primitive central idempotent.

Define the class function $\chi_\vartheta$ by the four rows displayed in Theorem 4.1 below and put

$$
e_\vartheta
=\frac{q-1}{|\overline G|}
\sum_{g\in\overline G}\chi_\vartheta(g^{-1})g
\in\mathbf C[\overline G].
$$

The following finite calculation is the construction step.

**Finite idempotent lemma.** If $\vartheta$ is regular, then $e_\vartheta$ is a primitive central idempotent, the left ideal $\mathbf C[\overline G]e_\vartheta$ is a matrix block of dimension $(q-1)^2$, and every minimal left ideal in that block has dimension $q-1$.

**Proof.** Conjugacy in $\overline G$ has four forms: scalar, nontrivial unipotent, split regular, and elliptic regular. Their centralizer orders are respectively

$$
|\overline G|,\qquad q(q-1),\qquad(q-1)^2,\qquad q^2-1.
$$

Write $d=q-1$. Multiplying two class sums and counting a product by its two
eigenlines gives the following explicit convolution table:

$$
\sum_{x\in\overline G}
\chi_\vartheta(x^{-1})\chi_\vartheta(xh)
=\frac{|\overline G|}{d}\chi_\vartheta(h),
$$

and, for the class sum $C_{\mathcal C}$ of any conjugacy class
$\mathcal C$ with representative $c$,

$$
C_{\mathcal C}e_\vartheta
=\frac{|\mathcal C|\chi_\vartheta(c)}{d}e_\vartheta.
$$

Here is the count rather than an appeal to a pre-existing character table.
For a split regular $h$, its two ordered rational eigenlines divide the
$x$-sum into two equal families; summing $\vartheta$ over
$k_2^\times/k^\times$ makes their contributions cancel. For elliptic $h$ with
eigenvalue $t\in k_2^\times\setminus k^\times$, the two eigenlines over $k_2$
give

$$
-\vartheta(t)-\vartheta(t^q).
$$

For a nontrivial unipotent $h$, there is one fixed rational line and $q$ affine
translates; their sum is $-1$. A scalar $z$ contributes $d\vartheta(z)$ on
every diagonal term. Substitution of the four centralizer orders above gives,
respectively,

$$
|\overline G|\vartheta(z),\qquad
-\frac{|\overline G|}{d}\vartheta(z),\qquad
0,\qquad
-\frac{|\overline G|}{d}
\bigl(\vartheta(t)+\vartheta(t^q)\bigr),
$$

which is exactly the first displayed convolution identity. The same partition
with $x$ restricted to one class gives the second identity. Only the elementary
orthogonality sums

$$
\sum_{u\in k^\times}\alpha(u)=0,\qquad
\sum_{u\in k_2^\times}\vartheta(u)\vartheta'(u)^{-1}=0
$$

for unequal characters are used.

The first identity gives $e_\vartheta^2=e_\vartheta$. Its trace in the left
regular representation is

$$
|\overline G|\,[1]e_\vartheta=d^2,
$$

so $\dim_\mathbf C\mathbf C[\overline G]e_\vartheta=d^2$.

The second identity shows that every central class sum acts on
$\mathbf C[\overline G]e_\vartheta$ by a scalar. Thus
$e_\vartheta\mathbf Z(\mathbf C[\overline G])=\mathbf C e_\vartheta$, so the
central idempotent is primitive. Maschke's theorem identifies its block with
$M_d(\mathbf C)$, and the dimension calculation gives $d=q-1$. A minimal left
ideal therefore has dimension $q-1$. $\square$

Choose a minimal left ideal and call it $\rho_\vartheta$. This is a concrete finite-dimensional representation because $\overline G$ acts by left multiplication. The central idempotent, and hence the isomorphism class of the minimal left ideal, is unchanged by $\vartheta\mapsto\vartheta^\tau$.

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

**Proof strategy.** The primitive block constructed in the finite idempotent lemma supplies existence and irreducibility. Its regular character is $(q-1)\chi_\vartheta$, so a minimal left ideal has character $\chi_\vartheta$. Averaging this character over the upper unipotent group proves cuspidality.

**Proof.** A primitive block $M_{q-1}(\mathbf C)$ has one irreducible module of dimension $q-1$, and its regular module is the direct sum of $q-1$ copies of that module. The trace of left multiplication by $g$ on $\mathbf C[\overline G]e_\vartheta$ is $(q-1)\chi_\vartheta(g)$ by the coefficient definition of $e_\vartheta$. Hence a minimal left ideal has the displayed character.

Let $\overline U$ be the upper unipotent group. Its invariant and coinvariant dimensions agree in characteristic zero, and the character average is

$$
\frac1q\left((q-1)+(q-1)(-1)\right)=0.
$$

Thus $\rho_\vartheta{}_{\overline U}=0$, so the representation is cuspidal. The table is unchanged by $\vartheta\mapsto\vartheta^\tau$, proving the last assertion. $\square$

### 4.4 Why regularity is necessary

If $\vartheta=\chi\circ N_{k_2/k}$, the last row becomes $-2\chi(Nt)$. The class-sum multiplication in the finite idempotent lemma then no longer makes $e_\vartheta$ primitive: it joins the blocks generated from the split Borel. This is not a minor exceptional parameter. It is the finite-field manifestation of a character descending to the split torus. Thus a depth-zero construction that omits regularity can accidentally produce principal-series constituents.

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

For $r>0$, the intersection of $K$ with its conjugate contains a subgroup whose reduction is the upper unipotent group on one side and the lower unipotent group on the other. A nonzero intertwiner of the inflated representations would therefore give a nonzero Jacquet quotient of $\rho_{\overline\theta}$, contradicting Theorem 4.1. Hence $I_G(\Lambda_\theta)=ZK$.

The same Cartan calculation supplies the two additional hypotheses of Theorem 3.1. Let a nonzero subrepresentation of the compact induction contain a vector of minimal Cartan radius. At an outermost coset with radius $r>0$, average against the finite matrix coefficients of $\rho_{\overline\theta}$ on the unipotent subgroup just exhibited. Cuspidality makes the average zero at that outer coset and leaves a nonzero value at an inner one, contradicting minimality. Thus the radius is zero and the subrepresentation meets the functions supported on $ZK$.

For a fixed compact open $C$, conjugate a principal congruence subgroup $K(s)$ into $C$. If the Cartan radius $r$ exceeds $s+1$, the intersection $ZK\cap gCg^{-1}$ again reduces onto a nontrivial upper or lower unipotent subgroup, and its invariant space in $\rho_{\overline\theta}$ is zero. Hence only finitely many Cartan radii and finitely many double cosets contribute to the $C$-fixed space. Theorem 3.1 and Proposition 3.2 now prove irreducibility, admissibility, and supercuspidality.

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

This group is open and compact modulo $Z$. Conjugation by $E^\times$ preserves
the Heisenberg representation. The extension problem from $J^1$ to $J$ has a
transparent ambiguity: two extensions differ by a character of
$E^\times/(E^\times\cap J^1)$. Normalize the Heisenberg intertwiners as in the
proof below and call the resulting extension $\kappa_\beta$. The quotient
character of $E^\times$ obtained from
$\theta\,\kappa_\beta^{-1}$ on the scalar intertwining lines is trivial on
$E^\times\cap J^1$, so it inflates to $J/J^1$. Define

$$
\Lambda_\theta=\kappa_\beta\otimes
\bigl(\theta\,\kappa_\beta^{-1}\bigr).
$$

This notation on the second factor means the inflated quotient character, not
a quotient of matrices. It makes the central character
$\theta|_{F^\times}$ and records the whole torus character.

**Proposition 6.3 (existence and uniqueness of the tame extension).** Under the tame minimal hypotheses above, $\eta_\beta$ extends to an irreducible representation $\Lambda_\theta$ of $J$. The conditions just stated determine it uniquely up to isomorphism, and replacing $\beta$ by another representative of the same leading character gives an isomorphic pair $(J,\Lambda_\theta)$.

**Proof strategy.** The quotient of $E^\times$ that acts nontrivially on the finite symplectic space is cyclic of order prime to $p$. The Heisenberg intertwiners give a projective action of this cyclic quotient; divisibility of $\mathbf C^\times$ kills its cocycle. Prescribing the torus character removes the remaining linear-character ambiguity.

**Proof.** Realize $\eta_\beta$ by induction from a maximal isotropic subgroup as in Lemma 6.2. An element of $E^\times$ permutes the isotropic models. The intertwiner between two such models is nonzero and unique up to scalar by the Heisenberg lemma, so these intertwiners give a projective action.

The relevant quotient is

$$
E^\times/F^\times U_E^1.
$$

If $E/F$ is unramified, its valuation part is killed by $F^\times$ and it is

$$
k_E^\times/k^\times,
$$

cyclic of order $q+1$. If $E/F$ is ramified, its residue-unit part is killed by $F^\times U_E^1$ and its valuation part has order two. Both orders are prime to $p$ in the tame range. A projective representation of a cyclic group has cocycle represented by the scalar attached to one generator relation; rescaling that generator by a suitable root in $\mathbf C^\times$ makes the relation exact. Thus the projective action linearizes.

Two linearizations differ by a character of the displayed quotient. Fix the
one whose averaging operator has determinant one on each prime-to-$p$ cyclic
orbit; if an orbit has even order, fix the remaining sign by requiring the
operator on the common central line to be $1$. This is $\kappa_\beta$.
Multiplying it by the quotient character displayed before the proposition
gives $\Lambda_\theta$ and shows uniqueness. Changing $\beta$ within the coset
defining the same character on $H^1$ gives the same Heisenberg representation,
the same normalized averaging operators, and hence the same extension.
$\square$

The positive-depth representation will be $\mathrm{c\mbox{-}Ind}_J^G\Lambda_\theta$. Its irreducibility is not automatic; it rests on the intertwining calculation next.

## 7. The tame induction theorem

### 7.1 Intertwining of the type

The leading term $\beta$ should force every intertwiner to preserve the quadratic lattice chain. That expectation is exact.

**Theorem 7.1 (tame intertwining and support reduction).** Let $(E,\theta)$ be a minimal tame admissible pair of positive level, and let $(J,\Lambda_\theta)$ be the type of Chapter 6. Then

$$
I_G(\Lambda_\theta)=J.
$$

Moreover every nonzero subrepresentation of $\mathrm{c\mbox{-}Ind}_J^G\Lambda_\theta$ meets the functions supported on $J$, and for every compact open $C$ only finitely many $JgC$ support $C$-fixed vectors.

**Proof strategy.** First intertwine the simple character. Commutators show that an intertwiner must conjugate the leading class of $\beta$ to itself at the relevant precision. Successive approximation then moves it into $E^\times$ times a deep congruence subgroup. The Heisenberg representation removes the final possible cosets.

**Proof.** Suppose $g$ intertwines $\Lambda_\theta$. It then intertwines a constituent $\vartheta_\beta$ of the restriction to $H^1$. For every sufficiently deep $x$ for which both $1+x$ and $g(1+x)g^{-1}$ lie in $H^1$, equality of the two characters gives

$$
\psi\!\left(\operatorname{tr}_A((g^{-1}\beta g-\beta)x)\right)=1.
$$

Trace duality places $g^{-1}\beta g-\beta$ in the dual radical power. On the first nonzero graded quotient, $g$ therefore normalizes the centralizer of the leading class of $\beta$. By Lemma 6.1 that centralizer is the image of $E$. Thus the leading graded part of $g$ belongs to $E^\times$.

Multiply $g$ on the left by a suitable element of $E^\times$. The remainder is congruent to $1$ at the first relevant lattice precision. To justify the successive step, suppose the remainder has first nonzero class $c$ in $\mathfrak P^r/\mathfrak P^{r+1}$. The intertwining identity says

$$
\operatorname{tr}_A(\beta[c,y])=0
$$

for every complementary graded class $y$. Trace duality makes $c$ centralize the leading class of $\beta$; its $E$-part is removed by another element of $E^\times$, and the remaining class is zero. Induction on $r$ moves the remainder into $U_{\mathfrak A}^{\lfloor(n+1)/2\rfloor}$. At the middle layer, nondegeneracy in Lemma 6.2 says that a class outside $J^1/H^1$ cannot intertwine $\eta_\beta$. Hence the remainder lies in $J^1$, proving $g\in J$. The reverse containment is immediate.

The same graded elimination proves support reduction. Given a nonzero vector in a subrepresentation, choose one for which the largest relative distance between its supporting lattice chains and the $E$-chain is minimal. At an outermost support coset, project successively to the $\vartheta_\beta$-isotypic line on $H^1$ and then to the Heisenberg isotypic part on $J^1$. If the distance is positive, the first nonzero graded displacement supplies a class $c$ outside the centralizer of $\beta$; averaging over a complementary $y$ multiplies the outer value by a nontrivial character and kills it, while a suitable matrix coefficient retains an inner value. This lowers the chosen distance, a contradiction. The distance is therefore zero and the subrepresentation meets the copy supported on $J$.

Finally fix $C$ and choose $s$ with a conjugate of $U_{\mathfrak A}^s$ contained in $C$. A lattice chain farther than $s+n+1$ from the $E$-chain has in $J\cap gCg^{-1}$ a graded class pairing nontrivially with $\beta$. Its invariant space in $\Lambda_\theta$ is zero. Only the finite ball of radius $s+n+1$ in the locally finite lattice tree can contribute, proving fixed-level finiteness. $\square$

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

Its inducing type is

$$
\left(J_{\theta_0},
\Lambda_{\theta_0}\otimes(\chi\circ\det)|_{J_{\theta_0}}\right).
$$

This and the resulting representation are independent of the chosen
decomposition. Indeed the determinant of the multiplication action of
$x\in E^\times$ is $N_{E/F}(x)$, so a determinant twist changes the torus
character by $\chi\circ N$; the same equality holds on the full inducing group.

### 7.3 Equivalence and exhaustivity

**Theorem 7.3 (classification within the tame quadratic class).** Let $(E,\theta)$ and $(E',\theta')$ be tame admissible pairs. Then

$$
\pi(E,\theta)\simeq\pi(E',\theta')
$$

if and only if the pairs are equivalent. Conversely, every irreducible supercuspidal representation containing either a regular depth-zero nonsplit-torus type or a positive-depth tame quadratic type is $\pi(E,\theta)$ for a unique equivalence class of admissible pairs.

**Proof strategy.** An isomorphism forces the types to intertwine. The leading character recovers the embedded quadratic field as its matrix centralizer, and then the normalizer has only the identity and $\sigma$. Exhaustivity is Frobenius reciprocity followed by irreducibility of compact induction.

**Proof.** The depth-zero case is Theorem 5.1. At positive depth, Mackey theory applied to a nonzero map between the compact inductions supplies $g\in G$ intertwining the two types. First restrict to commutators in the deep congruence group. Determinant characters are trivial there, so this restriction is unchanged by every norm twist used in Proposition 2.2. Its first nontrivial graded functional is the class of

$$
\beta-\beta^\sigma,
$$

equivalently the leading character of $\theta/\theta^\sigma$. Admissibility
makes its centralizer the quadratic field. The first graded calculation in
Theorem 7.1 therefore gives

$$
gE g^{-1}=E'.
$$

After conjugating, assume $E=E'$. The normalizer quotient is
$\{1,\sigma\}$. The extension $\Lambda_\theta$ records the full action of
$E^\times$, including its units, scalars, and a valuation generator; comparison
of the intertwined types therefore gives
$\theta'=\theta$ or $\theta^\sigma$ directly. Thus the pairs are equivalent.
The converse follows by conjugating the type.

If an irreducible $\Pi$ contains one of the displayed types, Frobenius reciprocity gives a nonzero map $\mathrm{c\mbox{-}Ind}_J^G\Lambda_\theta\to\Pi$. The source is irreducible, and the image is a nonzero subrepresentation of $\Pi$; hence the map is an isomorphism. Uniqueness follows from the first part. $\square$

The exhaustivity statement is deliberately qualified by the type contained in $\Pi$. It is not a classification of primitive wild supercuspidals.

### 7.4 Types and inertial classes

Let $J^0$ be the maximal compact subgroup of $J$, and let $\lambda_\theta=\Lambda_\theta|_{J^0}$, taking an irreducible constituent if the restriction splits. The conjugates of the constituents form one $J$-orbit, so the choice does not affect typicality.

**Proposition 7.4.** An irreducible smooth representation $\Pi$ contains $\lambda_\theta$ if and only if

$$
\Pi\simeq\pi(E,\theta)\otimes(\chi\circ\det)
$$

for an unramified character $\chi$ of $F^\times$.

**Proof.** The argument is the same as Proposition 5.2. The compact datum
fixes the action of $J^0$ but not the scalar assigned to a generator of the
infinite cyclic valuation quotient of $J$ (in the unramified case this freedom
is carried by the scalar subgroup $Z$). Choosing that scalar extends
$\lambda_\theta$ to $J$. Two choices differ by a character of $J$ trivial on
$J^0$. Since $\det(E^\times)$ is the norm group and $\mathbf C^\times$ is
divisible, that character is the restriction of an unramified determinant
character of $G$. Intertwining and irreducibility then identify $\Pi$ with the
corresponding compact induction. $\square$

## 8. Character calculations

### 8.1 The compact-induction formula

For a regular elliptic $g\in G$ in a neighborhood on which the contributing cosets are finite and constant, the formula of Section 3.4 specializes to

$$
\Theta_{\pi(E,\theta)}(g)
=\sum_{x\in J\backslash G/C_G(g)\atop xgx^{-1}\in J}
\operatorname{tr}\Lambda_\theta(xgx^{-1}).
$$

The set in this formula is finite by the finite-fixed-subtree argument of
Section 3.4: the condition $xgx^{-1}\in J$ places the lattice chain represented
by $x$ in a fixed finite neighborhood of that subtree. It is an exact
character algorithm on this elliptic range: decide which conjugates of $g$
enter the compact-mod-center subgroup, then take finite-dimensional traces.

**Proposition 8.1.** Let $(E,\theta)$ be a tame admissible pair and let $J$ be its inducing subgroup. On every regular elliptic neighborhood where the character formula above applies, if the conjugacy class of $g$ does not meet $J$, then $\Theta_{\pi(E,\theta)}(g)=0$.

**Proof.** Every term in the compact-induction formula is indexed by a conjugate of $g$ lying in $J$. Under the stated hypothesis the index set is empty, so the sum is zero. $\square$

This vanishing is often more useful than a closed formula. Split elements sufficiently far from the center do not meet the elliptic inducing subgroup, whereas elliptic elements in the matching torus do.

### 8.2 Depth-zero regular elements

Let $\pi(E,\theta)$ have depth zero. If $g\in K$ has elliptic regular reduction $\overline g$, its fixed vertex in the lattice tree is the vertex of $K$, so only the $ZK$-coset contributes. The finite table of Theorem 4.1 gives

$$
\Theta_\pi(g)
=-\overline\theta(t)-\overline\theta(t^q),
$$

where $t\in k_2^\times\setminus k^\times$ is either eigenvalue of $\overline g$.

For split regular reduction the element fixes an apartment, so the preceding finite elliptic sum is unavailable. At every fixed test-function level, however, the operator decomposes into finitely many blocks and each block has trace zero by the split row of Theorem 4.1; hence the distribution character is represented by zero on that open split-regular reduction set. For scalar or nonsemisimple reduction one must retain the scalar and unipotent rows and, near the center, possibly more compact-induction cosets. The reduction hypotheses are therefore essential.

These values already distinguish the orbit $\{\overline\theta,\overline\theta^q\}$. Orthogonality on $k_2^\times$ shows that two regular characters producing the same elliptic values lie in the same Frobenius orbit.

### 8.3 Positive-depth elliptic elements

For a positive-depth type, traces reduce to a finite Heisenberg calculation.
Choose a maximal isotropic subgroup $M/H^1$ and an extension
$\widetilde\vartheta_\beta$ of $\vartheta_\beta$ to $M$. The model

$$
\eta_\beta=\operatorname{Ind}_M^{J^1}\widetilde\vartheta_\beta
$$

has a basis $e_{Mx}$ indexed by the finite set $M\backslash J^1$. Its matrices
are monomial: if $xh=mx'$ with $m\in M$, then

$$
\eta_\beta(h)e_{Mx}
=\widetilde\vartheta_\beta(m)e_{Mx'}.
$$

For $y\in E^\times$, conjugation carries this model to the model attached to
$yMy^{-1}$. The normalized averaging intertwiner used in Proposition 6.3 is
the unique matrix $A_y$, with its prescribed scalar on the central line,
satisfying

$$
A_y\eta_\beta(h)
=\eta_\beta(yhy^{-1})A_y
\qquad(h\in J^1).
$$

The displayed monomial matrices turn this into a finite linear system with a
one-dimensional solution space; summing the diagonal entries of its normalized
solution is therefore an exact finite Gauss-sum algorithm. Write that trace,
after removing the prescribed torus scalar, as $\gamma_\beta(y)$. If
$y=y_Eh$ with $y_E\in E^\times$ and $h\in J^1$, then

$$
\operatorname{tr}\Lambda_\theta(y)
=\theta(y_E)\,\gamma_\beta(y),
$$

with the action of $h$ inserted in the same finite matrix. Changing $M$
conjugates the resulting matrix through the unique Heisenberg intertwiner, so
the trace is unchanged. This is the positive-depth character algorithm; in the
fixed-point-free regular case the displayed average is the usual nonzero
finite symplectic Gauss sum.

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

where $N$ is the upper unipotent subgroup and $\psi\!\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right)=\psi(x)$. Moreover every Kirillov function is compactly supported and $\pi_N=0$.

**Proof strategy.** At depth zero, finite Fourier projection gives the nontrivial unipotent character in the finite cuspidal seed. At positive depth, a change of basis puts the leading trace functional in the prescribed upper-unipotent orbit, and a polarization of the Heisenberg representation supplies the matching functional. Compact support then extends it to the induction. Uniqueness is the earlier rank-one Whittaker theorem.

**Proof.** In depth zero, the character average

$$
\frac1q\sum_{u\in k}
\operatorname{tr}\rho_{\overline\theta}
\left(\begin{pmatrix}1&u\\0&1\end{pmatrix}\right)
\overline\psi(-u)
$$

equals $1$ for every nontrivial additive character $\overline\psi$ of $k$: the identity contributes $q-1$ and the $q-1$ nonidentity elements contribute
$-\overline\psi(-u)$, whose sum is $1$. Hence the finite type has a unique
$\overline\psi$-line. Inflate it, conjugate by a diagonal matrix so that its
conductor matches $\psi$, and extend a matching functional by zero from the
identity inducing coset.

At positive depth, the map

$$
X\longmapsto\operatorname{tr}_A(\beta X)
$$

is a nonzero functional on the two-dimensional space of off-diagonal graded
classes. Conjugating the embedding of $E$ and then scaling by
$\operatorname{diag}(c,1)$ makes its restriction to the upper-nilpotent line
equal to $x\mapsto x$ at conductor zero. Choose the maximal isotropic subgroup
in Lemma 6.2 to contain that line. The induced Heisenberg model then has a
one-dimensional functional on which $N\cap J^1$ acts by $\psi$; the extension
$\Lambda_\theta$ preserves it on $N\cap J$.

In either case define, for a compactly induced function $f$,

$$
\lambda(f)=
\sum_{n\in (N\cap J)\backslash N}
\ell(f(n))\psi(-n).
$$

Only finitely many terms meet the support of $f$, so the sum is defined. A
change of variable gives $\lambda(\pi(n_0)f)=\psi(n_0)\lambda(f)$, and a
function supported on $J$ with value outside the kernel of $\ell$ shows that
$\lambda\ne0$. Whittaker uniqueness gives dimension one.

It remains to verify the Jacquet assertion without circularly assuming that
all cuspidals are generic. For fixed $f$, only finitely many $J$-cosets occur
in its support. If

$$
W_f\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)\ne0,
$$

then one of those cosets contains
$n(x)\operatorname{diag}(y,1)$ for some $x$. Its distance from the $E$-lattice
chain is at least $|v_F(y)|$ up to a constant depending only on $J$.
Consequently $v_F(y)$ lies in a finite interval depending on the support of
$f$. Thus every Kirillov function is compactly supported. The earlier
Kirillov asymptotic theorem identifies

$$
\mathcal K(\pi,\psi)/C_c^\infty(F^\times)
\simeq r_N(\pi).
$$

The quotient is zero, so $\pi_N=0$. $\square$

### 9.2 The compact Kirillov model

For $W$ in the Whittaker model put

$$
\kappa_W(y)=W\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right).
$$

By Theorem 9.1 the Jacquet module of $\pi$ is zero, so the Kirillov theorem gives

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

The decisive calculation is recorded once in a form that will also prove the
oldform theorem.

**Lemma 10.1 (congruence-intersection calculation).** Let $(E,\theta)$ be a
tame admissible pair, let $\pi=\pi(E,\theta)$, and put

$$
c=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).
$$

Choose the lattice shift $g_*$ that places the upper-root character of the type
in the conductor-zero $\psi$-orbit. Equivalently, at the first possible level
the intersection $J\cap g_*K_1g_*^{-1}$ is the polarization selected in the
genericity proof. For $r\ge0$, all summands in the Mackey decomposition of
$\pi^{K_1(\mathfrak p^r)}$ vanish except, when $r\ge c$, the summands represented
by

$$
g_j=g_*\begin{pmatrix}\varpi^{j}&0\\0&1\end{pmatrix},
\qquad 0\le j\le r-c.
$$

Each surviving summand is one-dimensional.

**Proof strategy.** The upper and lower root entries of a conjugated
$K_1$ impose two opposite bounds on the relative lattice position. Their gap is
the length of the character lattice plus the trace-dual displacement. At an
endpoint the intersection is a polarization of the Heisenberg group.

**Proof.** In depth zero, $E/F$ is unramified and $c=2$. With the standard
embedding one may take $g_*=\operatorname{diag}(\varpi,1)$. At $r=2$ the
reduction of $ZK\cap g_*K_1(\mathfrak p^2)g_*^{-1}$ is the diagonal subgroup
$\{\operatorname{diag}(a,1):a\in k^\times\}$. The character table of Theorem
4.1 gives

$$
\frac1{q-1}\sum_{a\in k^\times}
\operatorname{tr}\rho_{\overline\theta}
\left(\begin{pmatrix}a&0\\0&1\end{pmatrix}\right)=1,
$$

because the identity contributes $q-1$ and every $a\ne1$ is split regular.
Thus the endpoint Hom space is one-dimensional. After the shift by $g_*$,
reduction of the intersection contains a nontrivial upper unipotent unless
$j\ge0$, and a nontrivial lower unipotent unless $j\le r-2$. Cuspidality kills
the Hom space outside that interval. Inside it, successive root quotients act
through the same one-dimensional diagonal-invariant line just computed, so
each Hom space is one-dimensional. This proves the lemma at depth zero and
also explains why omitting the initial shift would reverse the endpoint.

Now suppose the level is positive and first suppose the pair is minimal.
Elementary divisors move any double coset to a relative shift of the two
lattices in the $E$-chain. Left multiplication by $E^\times$ removes
simultaneous translation of the chain, and right multiplication by
$K_1(\mathfrak p^r)$ removes the integral upper-root coordinate. Normalize the
origin by the unique shift $g_*$ at which the upper simple character is the
conductor-zero character used in Theorem 9.1. A remaining representative is
therefore $g_j$ for one integer $j$.

Relative to $g_*$, conjugation by $g_j$ changes the upper and lower matrix ideals by $j$ and $-j$,
respectively. Intersecting with $H^1$ and using

$$
\theta(1+x)=\psi_E(\beta x),\qquad
v_E(\beta)=-a_E(\theta)-d(E/F),
$$

shows that the upper intersection is annihilated by the simple character
exactly when $j\ge0$, while the lower intersection is annihilated exactly when

$$
j\le r-f(E/F)a_E(\theta)-f(E/F)d(E/F)=r-c.
$$

To see the factor $f$, filter an $E$-ideal between two consecutive
$F$-lattice bounds. Each $E$-valuation layer has $k$-dimension $f(E/F)$.
The trace-dual lattice is $\mathfrak p_E^{-d(E/F)}$, so its displacement
contributes $f(E/F)d(E/F)=v_F(\mathfrak d_{E/F})$. These two filtered-length
counts give the displayed lower bound with no choice of basis.

If either inequality fails, the intersection contains a class $1+x$ on which
$\psi_E(\beta x)\ne1$, so the corresponding Hom space is zero. If both hold,
the intersection with $J^1$ maps to an isotropic subgroup of $J^1/H^1$.
At either endpoint it is maximal isotropic; between the endpoints it is its
translate by a diagonal lattice shift. The Heisenberg induction of Lemma 6.2
has a one-dimensional fixed space under every such polarization. The action of
$E^\times\cap g_jK_1g_j^{-1}$ is trivial precisely because the same two
inequalities include the last nontrivial unit layer of $\theta$. Thus the Hom
space is one-dimensional.

For a nonminimal pair write
$\theta=\theta_0(\chi\circ N_{E/F})$. Twisting the intersection action by
$\chi\circ\det$ replaces the last unit character by the product
$\theta_0(\chi\circ N)$; repeating the identical annihilator calculation
replaces $a_E(\theta_0)$ by the actual conductor $a_E(\theta)$. This also shows
directly why cancellation, rather than the maximum of two conductors, controls
the answer. $\square$

**Theorem 10.1 (conductor of a tame admissible pair).** Let $(E,\theta)$ be a tame admissible pair. Then

$$
\boxed{\ a_F(\pi(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).\ }
$$

Here $\mathfrak d_{E/F}$ is the discriminant ideal and $f(E/F)$ is the residue degree.

**Proof.** Frobenius reciprocity and Mackey decomposition give

$$
\pi(E,\theta)^{K_1(\mathfrak p^r)}
\simeq
\bigoplus_{JgK_1}
\operatorname{Hom}_{J\cap gK_1g^{-1}}(\Lambda_\theta,1).
$$

Lemma 10.1 says that the sum is zero for $r<c$ and has one nonzero line for
$r=c$. Hence its first occurrence is exactly $c$, which is the asserted
formula. $\square$

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

The first alternative says that $\theta$ itself is quadratic and must still be
checked against admissibility; it is not discarded by a general slogan. The
second says $\theta|_{\ker N_{E/F}}$ has conjugate-inverse symmetry. Essential
self-duality is tested after multiplying by a norm character in the same way.

### 11.4 Counterexamples to naive conductor rules

It is false that twisting always replaces $a_F(\pi)$ by the larger of $a_F(\pi)$ and $2a_F(\chi)$. Take $\theta=\theta_0(\chi^{-1}\circ N)$ with $\theta_0$ minimal. Then twisting by $\chi$ lowers the torus character to $\theta_0$, and the conductor drops. Conversely, two twists of equal conductor can yield different representation conductors when their leading additive characters cancel in one case and not in the other. The exact pair formula is the reliable rule.

## 12. Local constants and quadratic induction

### 12.1 Normalization and the quadratic factor

Theorem 9.1 makes every $\pi(E,\theta)$ irreducible, admissible, generic, and
of zero Jacquet module. It therefore satisfies all hypotheses of the earlier
Whittaker functional equation, which defines $\epsilon(s,\pi,\psi)$. Since the
Kirillov core is all of the model, the zeta ideal is the unit ideal and the
standard factor is $1$; hence gamma and epsilon coincide. For conductor-zero
$\psi$,

$$
\epsilon(s,\pi,\psi)
=\epsilon(1/2,\pi,\psi)
q^{-a_F(\pi)(s-1/2)}.
$$

To compare this with a character of $E^\times$, one normalization issue must be made explicit. The norm subgroup has index two in $F^\times$ for a quadratic local extension. Denote by $\omega_{E/F}$ the nontrivial character of $F^\times/N(E^\times)$. Here is the direct tame calculation. In the unramified case norm valuations are even, the finite-field norm $k_E^\times\to k^\times$ is surjective, and trace surjectivity lifts this to every principal-unit layer; hence the valuation parity is the whole quotient. In the ramified case norm valuations are unrestricted, the norm on $U_E^1$ is surjective because its first graded map is multiplication by $2$, and the residue of a unit norm is a square in $k^\times$. Thus the residue-square class is the whole quotient. In either case its order is two.

Put

$$
\lambda(E/F,\psi)=\epsilon(1/2,\omega_{E/F},\psi).
$$

The rectifier in the ramified case depends on the admissible character. Suppressing
that dependence would break inversion and can change the Gauss sign. We now
construct it without using the induction theorem as a definition.

**Rectifier lemma.** For every tame admissible $\theta$ there is a unique tame
character

$$
\Delta_{E/F,\theta}:E^\times\longrightarrow\mathbf C^\times
$$

such that

$$
\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F}
$$

and such that the finite Fourier transform of the toric Whittaker function has
the same normalized Gauss sum as
$\lambda(E/F,\psi)\epsilon(1/2,\theta,\psi_E)$. It satisfies

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

**Proof.** In the unramified case require the rectifier to be unramified.
Restriction to $F^\times$ then forces
$\Delta_{E/F,\theta}(\varpi)=-1$, so it is unique and independent of $\theta$.

In the ramified tame case, let $\delta_0$ be the character on
$\mathcal O_E^\times$ that is trivial on $U_E^1$ and is forced on
$\mathcal O_E^\times/U_E^1=k^\times$ by
$\omega_{E/F}|_{\mathcal O^\times}$. If $\Pi$ is a uniformizer of $E$, the
relation $\Pi^2\in F^\times$ leaves exactly two extensions of $\delta_0$ to
$E^\times$ with the required restriction. Compute the Weyl transform of the
toric vector from Section 9.3 on the finite quotient

$$
U_E^0/U_E^{a_E(\theta)}.
$$

Put $\alpha_\theta$ equal to $\lambda(E/F,\psi)^{-1}$ times the following
ratio. The finite quadratic Gauss identity is

$$
\frac{
\sum_{u\in U_E^0/U_E^{a_E(\theta)}}
\theta(u)^{-1}\delta_0(u)^{-1}\psi_E(u/c)}
{\sum_{u\in U_E^0/U_E^{a_E(\theta)}}
\theta(u)^{-1}\psi_E(u/c)}
=\lambda(E/F,\psi)\alpha_\theta,
$$

where $v_E(c)=a_E(\theta)+d(E/F)$; it asserts in particular that
$\alpha_\theta^2=\omega_{E/F}(\Pi^2)$. To verify it, split the unit quotient
into residue classes, complete the square in the residue variable, and use

$$
\left(\sum_{x\in k^\times}\omega_{E/F}(x)\overline\psi(x)\right)^2
=q\,\omega_{E/F}(-1).
$$

The remaining principal-unit sums cancel by orthogonality. Both multiplicative
characters in the two sums have conductor $a_E(\theta)$, because admissibility
gives $a_E(\theta)\ge2$ and $\delta_0$ has conductor at most one. The usual
one-line Fourier inversion on the finite additive quotient therefore makes
both Gauss sums nonzero. The two allowed values at
$\Pi$ are the two square roots of $\omega_{E/F}(\Pi^2)$; choose
$\Delta_{E/F,\theta}(\Pi)=\alpha_\theta^{-1}$. This gives exactly the
normalized quadratic factor and proves existence and uniqueness.

Conjugating $u$ by $\sigma$, multiplying $\theta$ by a norm character, and
replacing $u$ by $-u$ in the dual sum give the three displayed identities,
respectively. These are changes of variables in a finite sum, so no induction
formula is being assumed. $\square$

Define the quadratic-induction normalization by

$$
\operatorname{AI}_{E/F}(\theta)
=\pi(E,\theta\Delta_{E/F,\theta}).
$$

Then

$$
\omega_{\operatorname{AI}_{E/F}(\theta)}
=\theta|_{F^\times}\omega_{E/F}.
$$

The rectifier changes neither a positive conductor nor admissibility. In the
ramified case admissibility gives $a_E(\theta)\ge2$, while the rectifier has
conductor at most one; in the unramified case it is unramified. It is necessary
because the direct type normalization and the induction normalization assign
different tame signs.

### 12.2 The induction formula

Let one-dimensional local constants over $E$ use $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$ and the self-dual measure.

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

The $F$-self-dual measure transported to the two-dimensional space $E$ differs from the $\psi_E$-self-dual measure by the square root of the discriminant. On finite unit quotients the remaining ratio is the quadratic Gauss sum $\lambda(E/F,\psi)$. The rectifier lemma makes the torus action agree with this sign. Thus the proportionality scalar is the displayed product.

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

**Proof strategy for Theorem 13.1.** Lemma 10.1 already identifies every
surviving double coset and proves that it contributes one line. The Kirillov
model identifies those lines with distinct valuation shells.

**Proof.** Put $C=K_1(\mathfrak p^r)$. The Mackey decomposition used in
Theorem 10.1 is

$$
\pi^C\simeq
\bigoplus_{JgC}
\operatorname{Hom}_{J\cap gCg^{-1}}(\Lambda_\theta,1).
$$

Lemma 10.1 says that it is zero for $r<n$ and, for $r\ge n$, has exactly the
$r-n+1$ one-dimensional summands represented by
$g_0,\ldots,g_{r-n}$. This proves the dimension formula and uniqueness at first
occurrence.

For interpretation in the Kirillov model, upper-unipotent invariance and
diagonal-unit invariance make the $j$th line constant on
$\varpi^j\mathcal O^\times$ and zero on the other surviving shells. Lower-root
invariance gives the upper endpoint $j\le r-n$; this is the second inequality
in the proof of Lemma 10.1. Hence the double-coset lines are precisely the
distinct shell lines. $\square$

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

Let $R$ be a discrete valuation ring of characteristic zero with fraction field $L\subset\mathbf C$, maximal ideal $\mathfrak m_R$, and residue field of characteristic $\ell$. Assume that all values of the finite-order part of $\theta$ lie in $R^\times$ and that every unramified value used in the central action is also a unit. Once the unramified value belongs to $L$, adjoining the finitely many roots of unity occurring in the compact part and taking the integral closure supplies this situation after a finite extension.

An **integral model** of the inducing representation is a finite free $R$-module $\Lambda_R$ carrying $J$ such that

$$
\Lambda_R\otimes_R L\simeq\Lambda_\theta.
$$

At depth zero, start with any full lattice in the minimal left ideal
$\rho_{\overline\theta}$ and replace it by the sum of its finitely many
$\mathrm{GL}_2(k)$-translates. That sum is again a full finitely generated
torsion-free $R$-module, hence a stable finite free lattice. This construction uses no division by
$|\mathrm{GL}_2(k)|$. At positive depth, the induced Heisenberg model and the
chosen torus intertwiners define $\Lambda_\theta$ over $L$. Smoothness gives an
open subgroup of the compact group $J/Z$ acting trivially after the central
scalar has been removed. Start with any full lattice and sum its translates by
representatives of the resulting finite quotient. Central and unramified
scalars preserve the sum because their values are units. Again the result is a
full finitely generated torsion-free, hence finite free, stable lattice. No
averaging denominator is required in either construction.

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

**Proof.** The depth-zero Cartan calculation of Theorem 5.1 and the
positive-depth lattice calculation of Theorem 7.1 bound the relative position
of a lattice chain supporting a $C$-fixed vector. Beyond that bound the
intersection $J\cap gCg^{-1}$ contains either a finite unipotent subgroup with
no invariants or a radical element on which the simple character is nontrivial;
the corresponding invariant module is zero. Thus only finitely many double
cosets $J\backslash G/C$ contribute. On each, the value lies in the finite
module of invariants of an intersection subgroup acting on $\Lambda_R$. Hence
$\Pi_R^C$ embeds in a finite direct sum of copies of $\Lambda_R$ and is finite.
Since $R$ is a DVR and $\Pi_R$ is torsion-free, each fixed module is finite
free. $\square$

### 14.3 A primitive integral newvector

**Theorem 14.2 (integral newvector).** Put
$n=a_F(\pi(E,\theta))$. The intersection

$$
\Pi_R^{K_1(\mathfrak p^n)}
=\Pi_R\cap\pi(E,\theta)_L^{K_1(\mathfrak p^n)}
$$

is a free rank-one $R$-module. If

$$
\ell\nmid q(q-1)(q+1),
$$

it has a generator whose normalized Whittaker function takes the value $1$ at
the identity and takes values in $R$ on all of $G$.

**Proof strategy.** Intersect a one-dimensional $L$-space with a full lattice, then use the explicit toric Whittaker sum to make the generator primitive rather than merely integral up to a denominator.

**Proof.** The fixed line over $L$ is one-dimensional by Theorem 13.1. Its intersection with the torsion-free admissible lattice is a nonzero fractional ideal of $R$, hence free of rank one. Choose a generator $v$ not divisible by $\mathfrak m_R$.

For the Whittaker normalization, use the sole Mackey summand at first
occurrence from Lemma 10.1. Both its intersection-invariant line and the
matching upper-unipotent character line occur in a representation of a finite
subquotient of $\mathrm{GL}_2(\mathcal O/\mathfrak p^s)$ for some $s$. The
prime divisors of its order are among $p$ and those dividing $q^2-1$. Under the
displayed hypothesis its order is a unit in $R$, so averaging makes each of
these multiplicity-one lines a direct summand over $R$.

The finite Fourier matrix between the intersection model and the
upper-unipotent character model has inverse equal to its conjugate matrix
divided by the order of the finite additive quotient. Its determinant is
therefore a unit. The one-dimensional endpoint calculation in Lemma 10.1 and
Theorem 9.1 says that its entry on the two displayed direct summands is
nonzero; invertibility after reduction says that entry is a unit. Consequently
the identity Whittaker coefficient of the primitive fixed vector is a unit.
Dividing the functional by this unit gives $W(1)=1$ without leaving $R$.
Proposition 13.2 gives $\mathbf1_{\mathcal O^\times}$ on the diagonal, and
$G$-translates of the finite Fourier construction remain $R$-valued.
$\square$

Thus the first local fixed line always has a primitive generator up to
$R^\times$, not merely up to $L^\times$. The unit-normalized integral
Whittaker realization is asserted under the exact banal-prime hypothesis that
makes the finite projectors integral.

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

**Proof.** Restrict to the finite sum of double cosets supporting the level-$r$ fixed space. Smoothness makes the action of $C=K_1(\mathfrak p^r)$ factor through a finite quotient $\overline C$ whose prime divisors are among $p$ and those dividing $q^2-1$. Under the hypothesis its order is a unit in $R$. The averaging operator

$$
e_{\overline C}=|\overline C|^{-1}
\sum_{c\in\overline C}c
$$

projects onto invariants. Tensor products commute with this idempotent image, proving the isomorphism. The rank-one assertion follows from Theorem 14.2. $\square$

When $\ell$ divides one of these orders, the primitive rank-one integral
newvector module still exists, but its Whittaker value at the identity need not
be a unit and reduction can acquire extra fixed vectors because averaging is no
longer exact. This is a genuine phenomenon, not a defect of the lattice.

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
