# Normalization and Regular Models of Arithmetic Curves

## Contents

1. [The problem of integral models](#1-the-problem-of-integral-models)
   - [From a curve over a field to a surface](#11-from-a-curve-over-a-field-to-a-surface)
   - [The hierarchy of hypotheses](#12-the-hierarchy-of-hypotheses)
   - [Standing conventions](#13-standing-conventions)
2. [Integral closure and normalization](#2-integral-closure-and-normalization)
   - [The affine construction](#21-the-affine-construction)
   - [Localization and gluing](#22-localization-and-gluing)
   - [The universal property](#23-the-universal-property)
   - [Birational invariance and components](#24-birational-invariance-and-components)
3. [Why normalization is finite](#3-why-normalization-is-finite)
   - [Japanese and Nagata rings](#31-japanese-and-nagata-rings)
   - [Excellent rings](#32-excellent-rings)
   - [The one-dimensional proof](#33-the-one-dimensional-proof)
   - [The two-dimensional cases used here](#34-the-two-dimensional-cases-used-here)
   - [What fails without finiteness hypotheses](#35-what-fails-without-finiteness-hypotheses)
4. [Normality and regularity in low dimension](#4-normality-and-regularity-in-low-dimension)
   - [Depth and codimension](#41-depth-and-codimension)
   - [The dimension-one coincidence](#42-the-dimension-one-coincidence)
   - [Normal surfaces need not be regular](#43-normal-surfaces-need-not-be-regular)
   - [Jacobian and fiberwise criteria](#44-jacobian-and-fiberwise-criteria)
5. [Arithmetic surfaces over Dedekind schemes](#5-arithmetic-surfaces-over-dedekind-schemes)
   - [Definitions and local dimensions](#51-definitions-and-local-dimensions)
   - [Flatness from torsion-freeness](#52-flatness-from-torsion-freeness)
   - [Horizontal and vertical geometry](#53-horizontal-and-vertical-geometry)
   - [Local equations over a discrete valuation ring](#54-local-equations-over-a-discrete-valuation-ring)
6. [Constructing proper normal models](#6-constructing-proper-normal-models)
   - [Spreading equations](#61-spreading-equations)
   - [Projective closure](#62-projective-closure)
   - [Removing unwanted components](#63-removing-unwanted-components)
   - [Normalization of the closure](#64-normalization-of-the-closure)
   - [Existence and uniqueness up to modification](#65-existence-and-uniqueness-up-to-modification)
7. [Blowups and normalized blowups](#7-blowups-and-normalized-blowups)
   - [The universal remedy for an ideal](#71-the-universal-remedy-for-an-ideal)
   - [Charts and exceptional curves](#72-charts-and-exceptional-curves)
   - [Normalized blowups](#73-normalized-blowups)
   - [Locality and projectivity](#74-locality-and-projectivity)
8. [Resolving surface singularities](#8-resolving-surface-singularities)
   - [The resolution theorem in the required setting](#81-the-resolution-theorem-in-the-required-setting)
   - [Preparing the singular locus](#82-preparing-the-singular-locus)
   - [Finite differentials and exterior trace](#83-finite-differentials-and-exterior-trace)
   - [Quadratic transformations](#84-quadratic-transformations)
   - [The remaining local resolution chain](#85-the-remaining-local-resolution-chain)
   - [Why a three-entry local invariant is insufficient](#86-why-a-three-entry-local-invariant-is-insufficient)
   - [Termination](#87-termination)
   - [Examples of the local procedure](#88-examples-of-the-local-procedure)
9. [Regular proper models](#9-regular-proper-models)
   - [Existence over excellent Dedekind bases](#91-existence-over-excellent-dedekind-bases)
   - [Keeping a prescribed good open](#92-keeping-a-prescribed-good-open)
   - [Dominating finitely many models](#93-dominating-finitely-many-models)
   - [Sections and closures of points](#94-sections-and-closures-of-points)
10. [Finite extensions and base change](#10-finite-extensions-and-base-change)
    - [Integral closure of the base](#101-integral-closure-of-the-base)
    - [Base change can destroy normality](#102-base-change-can-destroy-normality)
    - [The normalize-after-base-change rule](#103-the-normalize-after-base-change-rule)
    - [Ramification and vertical multiplicities](#104-ramification-and-vertical-multiplicities)
    - [Descent of models](#105-descent-of-models)
11. [Minimal regular models](#11-minimal-regular-models)
    - [Exceptional curves and contraction](#111-exceptional-curves-and-contraction)
    - [Existence in positive genus](#112-existence-in-positive-genus)
    - [Uniqueness and its limits](#113-uniqueness-and-its-limits)
    - [Marked and semistable variants](#114-marked-and-semistable-variants)
12. [Models for modular, Shimura, and semistable problems](#12-models-for-modular-shimura-and-semistable-problems)
    - [The exact reusable model theorem](#121-the-exact-reusable-model-theorem)
    - [Modular curves](#122-modular-curves)
    - [Shimura curves](#123-shimura-curves)
    - [Semistable reduction input](#124-semistable-reduction-input)
    - [Finite correspondences](#125-finite-correspondences)
13. [Synthesis](#13-synthesis)
    - [A hypothesis ledger](#131-a-hypothesis-ledger)
    - [The construction pipeline](#132-the-construction-pipeline)
    - [Conclusion](#133-conclusion)
14. [Depth, Cohen–Macaulay rings, and Serre's criteria](#14-depth-cohenmacaulay-rings-and-serres-criteria)
    - [Regular sequences and the depth invariant](#141-regular-sequences-and-the-depth-invariant)
    - [The depth calculus](#142-the-depth-calculus)
    - [The Auslander–Buchsbaum formula](#143-the-auslanderbuchsbaum-formula)
    - [Cohen–Macaulay local rings](#144-cohenmacaulay-local-rings)
    - [Serre's conditions and the normality criterion](#145-serres-conditions-and-the-normality-criterion)
    - [Freeness in dimension two](#146-freeness-in-dimension-two)
    - [Finite free resolutions and the homological criterion for regularity](#147-finite-free-resolutions-and-the-homological-criterion-for-regularity)
    - [Regular local rings are factorial](#148-regular-local-rings-are-factorial)
    - [What the criteria return to the models](#149-what-the-criteria-return-to-the-models)

## 1. The problem of integral models

### 1.1 From a curve over a field to a surface

A smooth projective curve over a number field is only the generic member of an arithmetic family. Questions about reduction, congruences, special fibers, and extension of maps require a space over the ring of integers, or over a localization of it, whose generic fiber is the original curve. Such a space has relative dimension one and absolute dimension two. It is therefore an **arithmetic surface**.

Passing from the generic curve to a surface introduces two new phenomena. First, equations that define a smooth curve over the fraction field may acquire singularities after reduction modulo a prime. Second, the closure of the generic curve may acquire extra components or fail to be integrally closed. The two repairs are different. Normalization repairs missing integral functions and separates branches in codimension one. Resolution repairs the remaining singular local rings, which on a normal surface are concentrated in codimension two.

The basic route is consequently

$$
C/K
\longrightarrow \overline C/S
\longleftarrow \overline C^{\mathrm{nor}}
\longleftarrow \mathcal X,
$$

where $S$ is a Dedekind scheme, $\overline C$ is a projective closure, $\overline C^{\mathrm{nor}}$ is its normalization in $K(C)$, and $\mathcal X$ is regular. The arrows pointing left are proper birational morphisms. Every step has a distinct hypothesis: projective closure uses an embedding; finiteness of normalization uses a Nagata condition; resolution uses excellence in dimension two.

This book establishes precisely that route. The focus is not arbitrary high-dimensional resolution. It is the low-dimensional geometry actually needed when modular or Shimura curves are extended across arithmetic primes and when semistable reduction is reached after a finite extension.

### 1.2 The hierarchy of hypotheses

Several adjectives that are harmlessly interchangeable over a perfect field separate sharply over arithmetic bases.

A scheme is **normal** if all its local rings are integrally closed domains, with the usual componentwise interpretation when the scheme is not connected. It is **regular** if each noetherian local ring $A$ has

$$
\dim A=\dim_{\kappa(\mathfrak m)}\mathfrak m/\mathfrak m^2.
$$

A morphism is **smooth** if it is locally of finite presentation, flat, and has geometrically regular fibers. Thus regularity belongs to the total space, while smoothness belongs to a morphism. A regular arithmetic surface can have a singular special fiber: $xy=\pi$ has regular total space but a nodal fiber. Conversely, a smooth fiber says nothing about singularities elsewhere.

A domain $A$ is **Japanese** if the integral closure of $A$ in every finite extension of its fraction field is a finite $A$-module. A noetherian ring is **Nagata** if each quotient by a prime is Japanese, and **universally Japanese** if in addition every finite-type algebra over it is Nagata. The latter is the finiteness condition for normalization of finite-type schemes. An excellent ring is, in particular, universally catenary, has geometrically regular formal fibers, and satisfies a uniform openness condition for regular loci; all three properties pass to every algebra essentially of finite type over it, and an excellent ring is universally Japanese. Excellence supplies more than normalization finiteness: it permits completion and localization to reflect the regularity information used in surface resolution. Section 3.2 states the package precisely and fixes the reading of the word "excellent" used throughout.

A morphism is **proper** if it is separated, of finite type, and universally closed. It is **projective** if it factors as a closed immersion into a projective space over the base. Projective implies proper. The converse holds in many curve situations after extra arguments, but it is not a definition and is not assumed silently.

The logical implications needed later are

$$
\text{smooth over a regular base}\Longrightarrow\text{regular},
$$

$$
\text{regular}\Longrightarrow\text{normal},
\qquad
\text{excellent}\Longrightarrow\text{universally Japanese}.
$$

None of the reverse implications is valid in this generality.

### 1.3 Standing conventions

Unless otherwise specified, rings are commutative and schemes are noetherian. A **curve over a field** is a separated finite-type scheme of pure dimension one. A **smooth proper curve** is also assumed geometrically connected when a single function field is used. If $S$ is integral, its generic point is $\eta$ and its function field is $K=\kappa(\eta)$. For an $S$-scheme $X$, write $X_K=X\times_S\operatorname{Spec}K$.

A **model** of a $K$-scheme $C$ is a flat finite-type $S$-scheme $X$ together with an identification $X_K\simeq C$. A proper, projective, normal, or regular model has the indicated additional property. Flatness is part of the word “model”: without it, vertical embedded components can be added without changing the generic fiber.

The valuation and Dedekind facts developed in Book 1 will be used freely. Relative projective constructions and their base-change behavior come from Book 8. Effective faithfully flat descent, when invoked, is the descent theory of Book 10. The permanence theory of excellent rings — geometrically regular formal fibers, openness of regular loci, finiteness of normalization, and the propagation of all three to algebras essentially of finite type — is Book 10a, and is imported in Section 3.2 in the single package used here. All local algebra specific to normalization and two-dimensional regularity is proved here.

## 2. Integral closure and normalization

### 2.1 The affine construction

Let $A$ be a domain with fraction field $F$, and let $L/F$ be a field extension. The **integral closure** of $A$ in $L$ is

$$
A_L=\{x\in L:x^n+a_{n-1}x^{n-1}+\cdots+a_0=0
\text{ for some }a_i\in A\}.
$$

The definition asks which rational functions must be added if every monic equation already soluble in the ambient field is to have its solution available. The monic condition is decisive: it implies that $A[x]$ is generated over $A$ by $1,x,\ldots,x^{n-1}$. Hence integrality is the elementwise shadow of a finite algebra.

**Lemma 2.1.** The elements of $L$ integral over $A$ form a subring. Integrality is transitive, and if an $A$-algebra is generated by finitely many integral elements, it is finite as an $A$-module.

**Proof.** If $x$ is integral, $A[x]$ is finite over $A$. If $x$ and $y$ are integral, then $A[x,y]$ is finite: first it is finite over $A[x]$, which is finite over $A$. Multiplication by $x+y$ or $xy$ is an endomorphism of this finite module. The determinant relation for that endomorphism gives a monic equation over $A$; thus $x+y$ and $xy$ are integral. The same finite-module argument proves transitivity. Finally, adjoining the generators one at a time proves the last claim. $\square$

For a reduced ring $A$ with finitely many minimal primes, the total ring of fractions is

$$
Q(A)=\prod_{\mathfrak p\in\operatorname{Min}(A)}\operatorname{Frac}(A/\mathfrak p).
$$

Its integral closure is the product of the closures of the components. This is the correct normalization of a reduced affine scheme. Nilpotents must first be discarded: a normal scheme is reduced, so the normalization cannot retain nilpotent structure.

**Example.** For $A=k[t^2,t^3]\subset k(t)$, the element $t$ is integral because it satisfies $T^2-t^2=0$, and $k[t]$ is the integral closure. Geometrically the cusp is replaced by a line. For $A=k[x,y]/(xy)$, reduction is already present but there are two minimal primes; normalization is $k[x]\times k[y]$, separating the two branches.

### 2.2 Localization and gluing

Normalization is useful geometrically only because it localizes.

**Proposition 2.2.** Let $S\subset A$ be multiplicatively closed and let $B$ be the integral closure of $A$ in $L$. Then $S^{-1}B$ is the integral closure of $S^{-1}A$ in $L$.

**Proof.** Every element of $S^{-1}B$ is plainly integral over $S^{-1}A$. Conversely, suppose $x\in L$ satisfies

$$
x^n+\frac{a_{n-1}}{s_{n-1}}x^{n-1}+\cdots+\frac{a_0}{s_0}=0.
$$

Choose one $s\in S$ divisible by all denominators. After multiplying the equation by $s^n$, the element $sx$ satisfies a monic equation over $A$. Thus $sx\in B$ and $x\in S^{-1}B$. $\square$

Let $X$ be an integral scheme with function field $F$, and let $L/F$ be finite. On an affine open $U=\operatorname{Spec}A$, form the integral closure $A_L$. Proposition 2.2 identifies the constructions on principal overlaps. They glue to an integral morphism

$$
\nu:X_L^{\mathrm{nor}}\longrightarrow X,
$$

called the **normalization of $X$ in $L$**. When $L=F$, this is simply the normalization of $X$. The morphism is affine and integral by construction. It is finite precisely when the local integral closures are finite modules.

### 2.3 The universal property

The normalization is not merely a repair chosen from equations. It is characterized by every dominant map from a normal source.

**Theorem 2.3 (universal property).** Let $X$ be integral with function field $F$, let $L/F$ be finite, and let $\nu:X'\to X$ be the normalization in $L$. Suppose $Y$ is normal and integral, $f:Y\to X$ is dominant, and an $F$-embedding $L\hookrightarrow K(Y)$ is fixed. Then there is a unique $X$-morphism $Y\to X'$ inducing that embedding.

**Proof strategy.** A map to an affine normalization amounts contravariantly to showing that every integral element is regular on the normal source. This can be checked in its local rings.

Take $U=\operatorname{Spec}A\subset X$ and a point $y\in f^{-1}(U)$. Every $b\in A_L$ satisfies a monic equation over $A$, hence its image in $K(Y)$ satisfies the same equation over $\mathcal O_{Y,y}$. Since the normal local domain $\mathcal O_{Y,y}$ is integrally closed in $K(Y)$, that image lies in $\mathcal O_{Y,y}$. It is therefore regular near $y$. As this holds at every point of $f^{-1}(U)$, the embedding $A_L\hookrightarrow K(Y)$ lands in $\Gamma(f^{-1}(U),\mathcal O_Y)$ and defines a map $f^{-1}(U)\to\operatorname{Spec}A_L$. These maps agree on overlaps by Proposition 2.2. Uniqueness follows because $X'\to X$ is separated and two $X$-maps from an integral scheme that agree at its generic point agree everywhere. $\square$

The normality of $Y$ cannot be omitted. The identity map from the cusp to itself does not factor through its normalization: such a factorization would place $t$ in $k[t^2,t^3]$.

**Corollary 2.4.** A finite birational morphism $Y\to X$ between normal integral schemes is an isomorphism.

Indeed, the universal property gives an inverse, first generically and then everywhere. This is the rigidity that makes normalization canonical.

### 2.4 Birational invariance and components

If $U\subset X$ is a dense open, then the normalization of $U$ is the inverse image of $U$ in the normalization of $X$. In particular normalization changes only the nonnormal locus. If $X$ is already normal, its normalization is itself.

For a reduced scheme $X$ with finitely many irreducible components $X_i$, normalization is the disjoint union of the normalizations of the reduced components. This may disconnect a connected scheme: the node $xy=0$ is connected, while its normalization has two components. Normalization separates branches because normal local rings are domains.

Finite birational morphisms are stable under composition, but normality is not stable under arbitrary field extension. Consequently one must distinguish the normalization of a base change from the base change of a normalization. Chapter 10 makes the difference precise.

## 3. Why normalization is finite

### 3.1 Japanese and Nagata rings

An integral morphism need not be finite, even over a noetherian base. For arithmetic geometry, mere integrality is inadequate: a non-finite normalization may not be of finite type and therefore may fall outside proper geometry. The finiteness issue is encoded in the following definitions.

A domain $A$ is Japanese if for every finite field extension $L/\operatorname{Frac}(A)$, its integral closure in $L$ is finite over $A$. A noetherian ring $A$ is Nagata if $A/\mathfrak p$ is Japanese for every prime $\mathfrak p$. A noetherian scheme is Nagata when its affine coordinate rings are.

**Theorem 3.1 (finite normalization criterion).** Let $X$ be a reduced noetherian Nagata scheme. Then the normalization $X^{\mathrm{nor}}\to X$ is finite. More generally, the normalization of each irreducible component of $X$ in a finite extension of its function field is finite.

**Proof.** The assertion is affine-local on $X$. Write $X=\operatorname{Spec}B$. After quotienting $B$ by each of its finitely many minimal primes, the Japanese condition says exactly that the integral closure in the relevant finite field extension is module-finite. A finite product of these closures is finite over the reduced ring $B$. Hence the componentwise normalization is finite. $\square$

To apply the criterion to a finite-type scheme over a base, one still needs a permanence statement for the base condition: the Nagata property of a ring says nothing by itself about finite-type algebras over it. Call a noetherian ring **universally Japanese** if every finite-type algebra over it is Nagata. The notion of an excellent ring is designed precisely to make such permanence statements available, and Section 3.2 records the form in which they are used here.

### 3.2 Excellent rings

Excellence is a package designed to make local algebra survive completion and finite-type passage. A noetherian ring $A$ is **excellent** when:

1. $A$ is **universally catenary**: every finite-type $A$-algebra is catenary, that is, between any two nested primes all saturated chains of primes have the same length;
2. $A$ is a **$G$-ring**: for each prime $\mathfrak p$, the fibres of $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ are geometrically regular;
3. $A$ satisfies **$J_2$**: for every finite-type $A$-algebra, the regular locus is open.

A ring satisfying (2) and (3) alone is **quasi-excellent**. A locally noetherian scheme is excellent, respectively quasi-excellent, when its affine coordinate rings are.

The first condition controls dimensions in chains of specializations; the second controls completion; the third lets singular points be isolated in a closed set. These are exactly the three roles excellence plays in resolving arithmetic surfaces.

What makes the package usable, however, is not the definition but its permanence. The rings that the constructions of this book actually touch are never the base: they are the affine charts of a projective model, the charts of a blowup, the local rings at generic points of exceptional divisors, and the finite covers produced by a normalization. Each of these is an algebra essentially of finite type over the base, and each must inherit all three conditions if an induction on blowups is to be legitimate. Establishing that permanence — above all the propagation of geometrically regular formal fibres from a base to its finite-type algebras, which is by far the hardest of the three — is the subject of Book 10a, and we import its conclusions rather than reproving them.

**The residue-field condition.** Book 10a proves its permanence theorems under one standing hypothesis. Say that a ring has **$p$-finite residue fields** if every residue field $\kappa$ of characteristic $p>0$ occurring in it satisfies $[\kappa:\kappa^p]<\infty$; a scheme has $p$-finite residue fields when its affine coordinate rings do. The condition is vacuous in characteristic zero; it holds for every perfect field, in particular for every finite field, and for every field finitely generated over a perfect field; and it propagates through every operation performed in this book. Indeed the residue fields of a quotient or a localization are residue fields of the original ring, those of a finite algebra are finite extensions of them, and those of an algebra essentially of finite type are finitely generated extensions of them, and in each case the $p$-degree is unchanged or merely multiplied by a power of $p$ (Book 10a, Lemma 7.5 and Corollary 7.6). Every base that occurs in this book satisfies it: $\mathbf Z$, the ring of integers of a number field and every localization of one, a discrete valuation ring whose residue field is finite or finitely generated over a perfect field, a complete discrete valuation ring with perfect residue field, a field finitely generated over its prime field, and anything essentially of finite type over one of these. The condition concerns residue fields only and asserts nothing by itself about excellence; which rings are excellent is the content of Theorem 3.2(5).

We therefore build the condition into the word. **Throughout this book, _excellent_ — applied to a noetherian ring or to a locally noetherian scheme — means excellent with $p$-finite residue fields, and _quasi-excellent_ is read the same way.** This is a genuine, if small, narrowing: a field of infinite $p$-degree such as $\mathbf F_p(u_1,u_2,\ldots)$, and the power series ring $k[[t]]$ over such a $k$, are excellent in the classical sense but are excluded here. No base of that kind occurs below, and no statement of this book is applied to one. The convention is consistent, because the narrowed class is closed under all the operations used: by the previous paragraph the $p$-finiteness of residue fields survives localization, quotients, finite algebras, algebras essentially of finite type, and completion, exactly as excellence itself does.

With that convention in place, the entire content of excellence needed downstream is the following four-clause package, together with the list of bases that satisfy it.

**Theorem 3.2 (the excellence package).**

1. _(Permanence.)_ Let $A$ be an excellent noetherian ring. Then every algebra essentially of finite type over $A$, every quotient of $A$, every localization of $A$, every finite $A$-algebra and every completion $\widehat{A_{\mathfrak p}}$ is again excellent. Consequently every scheme locally of finite type over an excellent locally noetherian scheme is excellent, as is every local ring of such a scheme, every affine chart of one, and every finite algebra over such a chart.
2. _(Finiteness of normalization.)_ An excellent noetherian ring $A$ is universally Japanese: for every finite-type $A$-algebra domain $D$ and every finite extension $L$ of $\operatorname{Frac}(D)$, the integral closure of $D$ in $L$ is a finite $D$-module; hence every finite-type $A$-algebra, and every localization of one, is Nagata. In particular $A$ itself is Nagata. Independently of the residue-field convention, every complete noetherian local ring is Nagata.
3. _(Completion is a faithful probe.)_ Let $X$ be an excellent locally noetherian scheme and $x\in X$. Then $\mathcal O_{X,x}\to\widehat{\mathcal O_{X,x}}$ is faithfully flat and regular. Consequently $\widehat{\mathcal O_{X,x}}$ is regular if and only if $\mathcal O_{X,x}$ is, reduced if and only if $\mathcal O_{X,x}$ is, and normal if and only if $\mathcal O_{X,x}$ is; and every formal fibre of $\mathcal O_{X,x}$ is regular, reduced and normal.
4. _(Openness of singularities.)_ Let $X$ be an excellent locally noetherian scheme. Then the regular locus of $X$ is open, and so is the regular locus of every scheme locally of finite type over $X$. The singular locus is therefore closed; if $X$ is normal of dimension two, it meets every quasi-compact open in a finite set of closed points.
5. _(The bases.)_ The following noetherian rings are excellent in the sense of this book: every field $k$ with $[k:k^p]<\infty$ in characteristic $p$, in particular every perfect field, every finite field and every field of characteristic zero; every complete noetherian local ring whose residue field has finite $p$-degree, in particular every complete discrete valuation ring with perfect residue field, such as $\mathbf Z_p$, $\mathbf F_q[[t]]$ and $k[[t]]$ with $k$ perfect; and $\mathbf Z$, the ring of integers of a number field, every localization of such a ring, and more generally every Dedekind domain of characteristic zero with $p$-finite residue fields. By (1) so is every algebra essentially of finite type over one of them — for instance every finite-type $\mathbf F_q$-algebra, hence the coordinate ring of every affine curve over a finite field, together with all of its localizations and completions.

**Proof.** Every clause is proved in Book 10a. Clause (1) is Theorem 10.5 there, the scheme-theoretic restatement being the affine-local one; clause (2) is Theorem 9.8, whose hypothesis is quasi-excellence with $p$-finite residue fields, applied to $A$ and to its finite-type algebras, the final sentence being Proposition 9.5; clause (3) is Theorem 4.13 applied to the local ring $\mathcal O_{X,x}$, which is a localization of an excellent ring and hence a $G$-ring by (1); clause (4) is the $J_2$ condition supplied by (1), the last assertion following as in Theorem 10.7(4) there, since on a normal scheme the singular locus is closed and, by Serre's criterion $R_1$ recalled in Section 14.5, contains no point of codimension at most one, so that in dimension two it consists of closed points and is finite on each quasi-compact open. For clause (5), Theorem 10.6 of Book 10a establishes excellence for the three listed families and Corollary 7.6 there establishes the $p$-finiteness of their residue fields. $\square$

For the three families of clause (5) all four assertions are collected in Book 10a, Theorem 10.7, in exactly the form used here; the statement above simply frees them from the choice of a particular base.

It is worth recording, once, which clause is consumed where, since the four are logically independent and are used for quite different purposes.

- Clause (2) is the finiteness of normalization. It is what makes Theorem 3.3 below true, and through Theorem 3.3 it underlies every model construction of Chapters 6, 7, 9, 10 and 12: the normalization of a model is again a model, proper if the original was proper and projective if the original was projective.
- Clause (3) is used whenever a two-dimensional normal local ring on a model is replaced by its completion in order to classify or resolve a singularity, in Sections 8.5 and 8.7. The completion is again normal, and it is regular exactly when the original ring was, so the passage neither creates nor destroys the object being studied. It is also what licenses the descent of a normalized-blowup sequence from the completion in Lemma 8.20.
- Clause (4) turns the sentence "the model is singular somewhere" into a closed subscheme that can be blown up, and combined with clause (2) it produces the finite singular set of Lemma 8.2.
- Clause (1) is what makes an induction on blowups legitimate at all: each chart of each blowup of a finite-type scheme over the base is again such a scheme, so the hypotheses under which the procedure operates are reproduced at every stage rather than assumed anew.

Universal catenarity, the first of the three defining conditions, is used only indirectly, through the dimension formula for finite-type domains over the base; it is the clause that never causes difficulty, since it holds for every quotient of a regular ring and hence for every ring occurring here.

### 3.3 The one-dimensional proof

The relevant one-dimensional finiteness can be seen more concretely, and here the Nagata property alone is enough. Let $A$ be a Nagata one-dimensional noetherian domain and $L/K$ finite. Choose a $K$-basis of $L$ and clear denominators so that an $A$-subalgebra $B_0\subset L$, finite over $A$, has fraction field $L$. Its normalization $B$ is finite by the Nagata property. Localizing at a nonzero prime $\mathfrak p$ of $A$ gives a finite semilocal normal one-dimensional algebra.

Every local factor $B_{\mathfrak q}$ is a noetherian normal local domain of dimension one, hence a discrete valuation ring. Therefore the integral closure of a Nagata Dedekind domain in a finite extension is again Dedekind and finite over the original ring; by Theorem 3.2(2) this covers every excellent Dedekind domain, in particular every Dedekind domain of characteristic zero with $p$-finite residue fields, and in the separable case the trace argument below covers every Dedekind domain whatsoever. This recovers, in the global form needed here, the local valuation picture of Book 1.

There is also a useful trace argument when $L/K$ is separable. Choose a $K$-basis $e_1,\ldots,e_n$ of $L$ and multiply its elements by nonzero scalars of $A$ so that every $e_i$ is integral over $A$. If $e_1^*,\ldots,e_n^*$ is the trace-dual basis and $x$ is integral over $A$, then every product $xe_i$ is integral. Its field trace, being a coefficient of the characteristic polynomial of multiplication by $xe_i$, is integral over $A$ and lies in $K$; because $A$ is integrally closed, $\operatorname{Tr}_{L/K}(xe_i)\in A$. Hence

$$
x=\sum_i\operatorname{Tr}_{L/K}(xe_i)e_i^*
$$

lies in the finite free fractional $A$-module $\sum_iAe_i^*$. The integral closure, as an $A$-submodule of that module, is finite because $A$ is noetherian. Thus every Dedekind domain is Japanese for finite separable extensions. The trace form degenerates for inseparable extensions, which is why the Japanese formulation is the correct general hypothesis.

### 3.4 The two-dimensional cases used here

Let $R$ be a Dedekind domain and $A$ a finite-type $R$-domain whose generic fiber has dimension one. Then $A$ has dimension at most two, and it has dimension two when $\operatorname{Spec}A$ dominates $\operatorname{Spec}R$. What we need of $A$ is exactly that it be Nagata, so that its normalization in any finite extension of its fraction field is finite. Theorem 3.2(2) delivers this as soon as $R$ is excellent, and by Theorem 3.2(5) that covers every base used below. This is the hypothesis under which the finiteness statement for arithmetic surfaces is available.

**Theorem 3.3.** Let $S$ be an excellent Dedekind scheme, or more generally a noetherian scheme whose affine coordinate rings are universally Japanese. If $X$ is a reduced finite-type $S$-scheme, then $X^{\mathrm{nor}}\to X$ is finite. If $X\to S$ is proper, respectively projective, then its normalization is proper, respectively projective, over $S$.

**Proof.** Every affine coordinate ring of $X$ is a finite-type algebra over a universally Japanese ring, hence is Nagata: for an excellent base this is Theorem 3.2(2), and universal Japaneseness says it directly. Finiteness is now Theorem 3.1. A finite morphism is projective and proper. Composing it with a proper morphism gives a proper morphism. If $X\hookrightarrow\mathbf P^n_S$, a finite morphism $Y\to X$ is projective; composing projective morphisms proves projectivity of $Y/S$. $\square$

The theorem covers every base of Theorem 3.2(5) at a stroke: a perfect field, which is the case of the local surface charts in equal characteristic with perfect residue field; a complete discrete valuation ring, which is the case of the local analysis at one place; and $\mathbf Z$ or a localized ring of integers, which is the global arithmetic case. No hypothesis beyond excellence of the base is needed, and by Theorem 3.2(1) the conclusion is inherited by every chart, localization and finite cover produced later.

### 3.5 What fails without finiteness hypotheses

Noetherian does not imply Japanese. There exist one-dimensional noetherian domains whose integral closure in a finite extension of the fraction field is not finite. Their normalizations are integral and affine but not finite type. Thus the sentence “normalization of a noetherian scheme is finite” is false.

Even when normalization is finite, it need not commute with arbitrary base change. And even for an excellent surface, normalization need not resolve singularities. These failures divide the later work cleanly: Nagata controls finiteness, excellence controls the local resolution process, and geometric regularity controls base change.

## 4. Normality and regularity in low dimension

### 4.1 Depth and codimension

Normalization corrects codimension-one defects, but regularity also sees closed points on a surface. The bridge is Serre's criterion. For a noetherian ring $A$, condition $(R_1)$ says that $A_{\mathfrak p}$ is regular whenever $\operatorname{ht}\mathfrak p\leq1$. Condition $(S_2)$ says

$$
\operatorname{depth}A_{\mathfrak p}\geq
\min\{2,\dim A_{\mathfrak p}\}
$$

for every prime $\mathfrak p$.

**Theorem 4.1 (Serre's criterion).** A noetherian ring is normal if and only if it is reduced and satisfies $(R_1)$ and $(S_2)$.

**Proof.** Work componentwise after using the minimal primes. An integrally closed domain is the intersection of its height-one valuation rings inside its fraction field. Condition $(R_1)$ identifies those local rings as discrete valuation rings, while $(S_2)$ ensures that functions regular away from codimension at least two extend.

For the forward implication, a noetherian normal local domain has depth at least two when its dimension is at least two: if a nonzero $a\in\mathfrak m$ were such that every element of $\mathfrak m$ were a zero divisor modulo $a$, prime avoidance would force an associated height-one prime incompatible with integral closedness. Height-one localizations are one-dimensional noetherian normal local domains and hence discrete valuation rings. Conversely, assume $(R_1)$ and $(S_2)$. If $x$ in the fraction field is integral over $A$, it belongs to every height-one localization. The intersection theorem supplied by $(S_2)$ gives

$$
A=\bigcap_{\operatorname{ht}\mathfrak p=1}A_{\mathfrak p}
\quad\text{inside }K(A),
$$

Here is the intersection argument. Put
$I=\{r\in A:rx\in A\}$. Membership at every height-one localization says that $I$ is contained
in no height-one prime. Choose a nonzerodivisor $r\in I$. Every associated prime of $A/rA$ has
depth one; $(S_2)$ makes it height one. Prime avoidance therefore chooses
$s\in I$ which is a nonzerodivisor on $A/rA$. Write $rx=u$ and $sx=v$. The equality $su=rv$
and regularity of $s$ modulo $r$ give $u=rw$, hence $x=w\in A$. The identical local argument
also shows that an $(R_1),(S_2)$ local ring has only one minimal prime: two minimal primes would
give, at a prime minimal over their sum, depth at most one but dimension at least two, while in
dimension at most one $(R_1)$ makes the localization a domain. Thus the argument applies at every
localization and proves the ring statement. $\square$

The later surface arguments need the following consequences now, rather than by a forward
reference to the final algebra chapter.

**Proposition 4.1A (chronological local-algebra package).** The following hold.

1. If $(P,\mathfrak n)$ is regular local of dimension $n$, every minimal generating sequence of
   $\mathfrak n$ is regular, the Koszul complex on it resolves the residue field, and every finite
   $P$-module has projective dimension at most $n$.
2. A quotient of a Cohen--Macaulay local ring by a regular sequence is Cohen--Macaulay of the
   expected dimension. In particular a hypersurface in a regular local ring is
   Cohen--Macaulay.
3. A two-dimensional normal local domain is Cohen--Macaulay. A finite module of depth two over a
   two-dimensional regular local ring is free. Consequently a finite normal local domain of
   dimension two over a two-dimensional regular local ring is free as a module.
4. Completion preserves dimension, depth, regularity, and Cohen--Macaulayness.

**Proof.** We include the homological steps used below. Induct on $n$ to see that a regular local
ring is a domain and that a parameter $x\in\mathfrak n\setminus\mathfrak n^2$ is a
nonzerodivisor with regular quotient of dimension $n-1$. Indeed the quotient is regular by the
dimension and cotangent-space count; by induction it is a domain. A minimal prime below $(x)$
then satisfies $\mathfrak p=x\mathfrak p$, hence is zero by Nakayama. Iteration makes a minimal
parameter sequence regular, and its Koszul complex resolves the residue field $k$.

For a finite $P$-module $M$, take a minimal free resolution. Its differentials vanish after
tensoring with $k$, so its module in degree $i$ is nonzero precisely when
$\operatorname{Tor}^P_i(k,M)$ is nonzero. The Koszul resolution of $k$, used in the other
variable, has length $n$; hence these Tor groups vanish for $i>n$, proving (1).

If $x$ is a nonzerodivisor on a finite local module $M$, the long exact Ext sequence associated
to $0\to M\xrightarrow{x}M\to M/xM\to0$ shows

$$
\operatorname{depth}(M/xM)=\operatorname{depth}(M)-1.       \tag{4.1a}
$$

The principal ideal theorem gives the identical drop in dimension. Iteration proves (2), since
(1) says a regular local ring has depth equal to its dimension.

Theorem 4.1 says that a normal local domain satisfies $(S_2)$, so in dimension two it has depth
two. Now let $M$ have depth two over a two-dimensional regular local ring $P$. Choose
$x\in\mathfrak n\setminus\mathfrak n^2$ avoiding the associated primes of $M$. Formula (4.1a)
makes $M/xM$ a depth-one module over the discrete valuation ring $P/(x)$, hence torsion-free and
free. Lift a basis to a map $P^r\to M$. Nakayama makes it surjective, and the Tor sequence for
$P/(x)$ says that its kernel $N$ has $N/xN=0$; Nakayama gives $N=0$. Thus $M$ is free.

If $P\to B$ is finite local with $B$ a normal domain of dimension two, a parameter pair of $P$
is a system of parameters of the Cohen--Macaulay ring $B$ and hence a $B$-regular sequence
(successively avoid the associated primes, which in a Cohen--Macaulay local ring have the
expected dimension). Thus $B$ has depth two as a $P$-module and is free by the preceding
paragraph.

Finally $P\to\widehat P$ is faithfully flat, has the same residue field and cotangent space, and
the completed Koszul complexes compute the same first nonzero Ext degree. Hence depth and
embedding dimension are unchanged; faithful flatness and the dimension theorem for completion
give the assertions in (4). $\square$

This criterion explains a major feature of normal surfaces: their nonregular locus has codimension at least two and therefore consists of closed points locally. If the surface is of finite type over an excellent Dedekind scheme, the singular locus is closed by the $J_2$ property, supplied for every chart by Theorem 3.2(1) and (4); on a quasi-compact surface it is a finite set whenever it contains no curve.

### 4.2 The dimension-one coincidence

**Proposition 4.2.** For a noetherian local domain $A$ of dimension one, the following are equivalent:

1. $A$ is normal;
2. $A$ is a discrete valuation ring;
3. $A$ is regular.

**Proof.** Normality implies that every nonzero ideal has a factor of least valuation, giving a principal maximal ideal; this is the discrete valuation characterization. A one-dimensional local ring with principal maximal ideal has embedding dimension one and is regular. Conversely, a regular local ring is factorial by Theorem 14.43, and a factorial domain is integrally closed in its fraction field by Corollary 14.44; so a regular local ring is normal, in every dimension and in particular in dimension one. $\square$

Consequently a normal curve over a perfect field is regular, and because its residue extensions are separable, it is smooth. Over an imperfect field, regular need not imply smooth: geometric regularity can fail after a purely inseparable field extension. This is the first reason to keep “regular” and “smooth” separate.

### 4.3 Normal surfaces need not be regular

Let $k$ have characteristic different from $2$ and consider

$$
A=k[x,y,z]/(xy-z^2).
$$

This two-dimensional domain is singular at the origin because its maximal ideal needs three
generators. Yet it is normal. Indeed, Proposition 4.1A makes it Cohen--Macaulay because it is a
hypersurface, so it satisfies $(S_2)$. Outside the origin, inverting $x$ or $y$ identifies the
ring with a localization of $k[x,x^{-1},z]$ or $k[y,y^{-1},z]$; hence its only singular point has
codimension two and $(R_1)$ holds. Theorem 4.1 applies.

This quadratic cone is the model warning. Normalization does nothing to it. Blowing up its singular point replaces the vertex by a projective line and yields a regular surface. On an arithmetic surface the same distinction appears at isolated points of bad fibers.

Regularity itself does not imply regular fibers. If $R$ is a discrete valuation ring with uniformizer $\pi$, then

$$
A=R[x,y]/(xy-\pi)
$$

is regular at $(x,y,\pi)$: the relation makes $\pi=xy$, so the maximal ideal is generated by $x,y$, equal to the dimension. Its special fiber is $k[x,y]/(xy)$, a nodal curve. The morphism is flat but not smooth at the node.

### 4.4 Jacobian and fiberwise criteria

For a finite-type algebra over a field, the Jacobian criterion tests smoothness when the field and presentation satisfy the usual separability hypotheses. For a hypersurface $A=P/(f)$ in a regular local ring $(P,\mathfrak n)$, the quotient is regular exactly when

$$
f\notin\mathfrak n^2.
$$

Indeed, $\dim A=\dim P-1$, while its embedding dimension drops by one precisely when the initial linear form of $f$ is nonzero. For $xy-\pi$, the element $\pi$ is part of a regular parameter system in $P=R[x,y]_{(\pi,x,y)}$, so the quotient is regular. For $xy-z^2$ over a field, the equation lies in $\mathfrak n^2$, so the vertex is singular.

Let $f:X\to S$ be flat and locally of finite presentation, with $S$ regular. If every geometric fiber is regular, then $f$ is smooth and $X$ is regular. If $X$ is regular, the fibers need not be. A useful local criterion over a discrete valuation ring $R$ says: if $A$ is flat and essentially of finite type over $R$, then $A$ is regular at $x$ provided the fiber local ring is regular and the image of $\pi$ is not in the square of the maximal ideal in the wrong way; more invariantly, one uses the dimension formula and the exact cotangent sequence. Smoothness is equivalent to flatness plus geometric regularity of the fiber.

## 5. Arithmetic surfaces over Dedekind schemes

### 5.1 Definitions and local dimensions

Let $S$ be an **excellent Dedekind scheme**: a connected, normal, noetherian scheme of dimension one whose local rings at closed points are discrete valuation rings and whose affine coordinate rings are excellent in the sense of Section 3.2 — that is, universally catenary $G$-rings satisfying $J_2$, with $p$-finite residue fields. Theorem 3.2(5) lists the examples that matter: $\operatorname{Spec}\mathbf Z$; the spectrum of the ring of integers of a number field, or of any localization of one, and more generally of any characteristic-zero Dedekind domain with $p$-finite residue fields; the spectrum of a complete discrete valuation ring with perfect residue field, such as $\mathbf Z_p$ or $\mathbf F_q[[t]]$; a smooth affine curve over a field of finite $p$-degree, for instance over a finite field, together with the spectrum of any of its local rings at closed points; and any open subscheme of these. By Theorem 3.2(1) every scheme locally of finite type over such an $S$ is again excellent, so the hypothesis is reproduced on every chart, blowup and finite cover constructed below and never has to be reimposed.

An **arithmetic surface over $S$** is an integral, normal, flat, finite-type $S$-scheme $X$ of relative dimension one. When $X$ is proper, it is a proper arithmetic surface.

At the generic point of $X$, the local ring has dimension zero. At the generic point of a horizontal prime divisor, or at the generic point of a component of a special fiber, it has dimension one. At a closed point lying over a closed point of $S$, it has dimension two. Universal catenarity gives the expected dimension formula and prevents chains from changing length after localization.

Normality ensures that every codimension-one local ring is a discrete valuation ring. Thus rational functions have orders along both horizontal and vertical prime divisors. Regularity asks additionally that every two-dimensional local ring at a closed point have a two-element regular system of parameters.

### 5.2 Flatness from torsion-freeness

Over a Dedekind domain, torsion-freeness is the practical flatness test.

**Proposition 5.1.** Let $R$ be a Dedekind domain and $M$ an $R$-module. Then $M$ is flat if and only if it is torsion-free.

**Proof.** Flat modules are torsion-free because multiplication by a nonzero $r\in R$ is injective on $R$ and remains so after tensoring. Conversely flatness is local on $R$, so reduce to a discrete valuation ring. Every finitely generated torsion-free module over it is free by elementary divisors. An arbitrary torsion-free module is the filtered union of its finitely generated torsion-free submodules, and filtered colimits of flat modules are flat. $\square$

**Corollary 5.2.** If $X$ is integral and dominates $S$, then $X\to S$ is flat.

On an affine chart, the map from the domain $R$ into the domain $A$ is injective; hence $A$ is torsion-free. This is why taking the closure of the generic fiber and then removing vertical components produces a model automatically.

Flatness rules out irreducible components supported entirely in a special fiber, but special fibers themselves may be reducible or nonreduced. The equation $x^2-\pi=0$ is flat over $R$ although its special fiber is a doubled point in residue characteristic different from two. Relative dimension one has analogous multiple components.

### 5.3 Horizontal and vertical geometry

An integral closed subscheme $Z\subset X$ is **horizontal** if it dominates $S$, and **vertical** if its image lies in a closed point. On a proper arithmetic surface, a horizontal prime divisor is the closure of a closed point of the generic curve. It is finite over $S$: properness makes it proper, quasi-finiteness follows from dimension, and proper plus quasi-finite is finite.

For a closed point $s\in S$ with uniformizer $\pi_s$, the fiber is the Cartier divisor

$$
X_s=\operatorname{div}(\pi_s)=\sum_i m_i\Gamma_i,
$$

where the $\Gamma_i$ are the irreducible vertical components and

$$
m_i=\operatorname{ord}_{\Gamma_i}(\pi_s)>0.
$$

The multiplicities record how the base valuation extends to the divisorial valuations of the function field. A fiber is generically reduced exactly when all $m_i=1$ and the residue extensions at the generic points are reduced. It is geometrically reduced only after the corresponding condition over an algebraic closure of the residue field.

Horizontal and vertical are relative notions. After a finite extension of the base, a horizontal divisor remains horizontal but may split. A vertical component remains vertical, though ramification can change its multiplicity and normalization can split its residue-field branches.

### 5.4 Local equations over a discrete valuation ring

Let $(R,\pi)$ be a discrete valuation ring. Several local equations distinguish the main geometric conditions.

- $R[x]$ is smooth and regular; the special fiber is a smooth affine line.
- $R[x,y]/(xy-\pi)$ is regular and flat; the special fiber has an ordinary node. It is the basic semistable equation.
- $R[x,y]/(xy-\pi^n)$ for $n>1$ is normal but singular at the origin. Its resolution produces a chain between the two branches.
- $R[x,y]/(y^2-x^3-\pi)$ can be regular even though the special fiber is cuspidal; regular total space does not make the fiber nodal.
- $R[x]/(\pi x)$ has vertical torsion and is not flat.

For the third example, normality follows from the hypersurface $(S_2)$ property and regularity in codimension one. At the closed point the embedding dimension is three while the dimension is two. Repeated blowups reduce the exponent $n$, exhibiting both the local procedure and its termination.

## 6. Constructing proper normal models

### 6.1 Spreading equations

Let $C$ be a smooth projective geometrically connected curve over $K=K(S)$. Book 8 supplies a very ample line bundle, hence an embedding

$$
C\hookrightarrow\mathbf P^N_K.
$$

Choose finitely many homogeneous equations for its image and clear their denominators. They define a closed subscheme over a nonempty open $U\subset S$. This is **spreading out**: any finite list of coefficients, morphisms, and identities over $K$ extends after removing finitely many closed points of $S$.

Over a still smaller $U$, generic flatness makes the family flat. Smoothness is open for a finite-presentation morphism, so it may also be made smooth. This produces the good model away from finitely many primes. The task is to fill in the omitted fibers properly and then repair them.

### 6.2 Projective closure

Take the schematic closure $\overline C$ of $C$ in $\mathbf P^N_S$. Because closed immersions and projective space are projective, $\overline C\to S$ is projective. The closure is the smallest closed subscheme whose generic fiber is $C$.

On an affine chart with coordinate algebra $A$, the schematic closure corresponds to the image of $A$ in $A\otimes_RK$. Consequently the coordinate ring injects into its generic fiber and is $R$-torsion-free. Proposition 5.1 gives flatness. Equivalently, schematic closure automatically discards sections killed by a nonzero element of the base.

**Proposition 6.1.** The schematic closure of an integral projective $K$-scheme in projective space over a Dedekind domain is an integral flat projective $S$-scheme with the prescribed generic fiber.

**Proof.** The topological closure of the generic integral space is irreducible. Its scheme-theoretic closure is reduced on each affine chart because its coordinate ring is a subring of the generic domain. It is therefore integral. Projectivity is inherited from the ambient projective space, and flatness follows from torsion-freeness. $\square$

Different embeddings generally give different closures. That is not a defect: models form a birational system, and regular models later dominate common refinements.

### 6.3 Removing unwanted components

If one begins with arbitrary cleared equations rather than schematic closure, vertical components and embedded torsion may appear. The correct cleanup is to take the closure of the generic fiber, algebraically the quotient by the kernel of

$$
A\longrightarrow A\otimes_RK.
$$

This operation is sometimes called saturation with respect to $R\setminus\{0\}$. Over a discrete valuation ring it removes precisely the elements annihilated by a power of $\pi$. It should precede normalization: normalizing a space with irrelevant vertical components faithfully preserves those components instead of removing them.

### 6.4 Normalization of the closure

Let $X_0$ be the integral projective closure. Normalize it in $K(C)$. Since $S$ is excellent and $X_0$ is of finite type over $S$, Theorem 3.3 makes

$$
\nu:X_1\longrightarrow X_0
$$

finite. Therefore $X_1$ is projective over $S$. It is integral and normal by construction, and it remains flat because it dominates $S$. Its generic fiber is $C$: a smooth curve is normal, so normalization is an isomorphism there.

**Theorem 6.2 (normal model theorem).** Every smooth projective geometrically connected curve over the function field of an excellent Dedekind scheme has a normal flat projective model. Given a smooth projective model over a nonempty open $U\subset S$, the normal model may be chosen to restrict to it.

For the relative clause, choose a relatively very ample bundle on the given projective $U$-model, embed it in $\mathbf P^N_U$, and extend its finitely many equations after shrinking the ambient trivializations only outside $U$. The schematic closure in $\mathbf P^N_S$ then restricts exactly to the given model. Since that model is normal, normalization changes nothing there. The word projective is necessary: the restriction of a projective $S$-model is projective, so an arbitrary nonprojective regular model over $U$ cannot be prescribed in this statement.

### 6.5 Existence and uniqueness up to modification

A **modification** is a proper birational morphism. Normal models are not unique, but any two proper models of $C$ admit a common proper model dominating both.

**Proposition 6.3.** Let $X$ and $Y$ be proper $S$-models of $C$. The closure $Z_0$ of the diagonal copy of $C$ in $X\times_SY$ is proper over $S$, and its two projections are modifications. Since $S$ is excellent, the normalization $Z$ of $Z_0$ is finite by Theorem 3.3 and gives a normal proper common domination.

**Proof.** The product is proper. The closure of the diagonal generic fiber is closed and hence proper. Each projection restricts to the identity on $C$, so it is birational. Normalization preserves properness and the generic fiber. $\square$

This common-domination principle replaces false uniqueness by a useful directedness. Rational maps between proper models become honest after passing to the normalized closure of their graphs.

## 7. Blowups and normalized blowups

### 7.1 The universal remedy for an ideal

Let $X$ be a scheme and $\mathcal I\subset\mathcal O_X$ a coherent ideal. The blowup is

$$
\operatorname{Bl}_{\mathcal I}X
=\operatorname{Proj}_X\bigoplus_{n\geq0}\mathcal I^n.
$$

Its purpose is to make $\mathcal I$ invertible. There is a canonical invertible ideal
$\mathcal I\mathcal O_{\operatorname{Bl}_{\mathcal I}X}\simeq\mathcal O(1)$, up to the conventional sign for the exceptional divisor.

**Theorem 7.1 (universal property of blowup).** A morphism $g:Y\to X$ factors uniquely through $\operatorname{Bl}_{\mathcal I}X$ if $\mathcal I\mathcal O_Y$ is an invertible ideal generated locally by one nonzerodivisor.

**Proof strategy.** A locally principal quotient of $g^*\mathcal I$ defines a point of relative Proj. On an affine chart $X=\operatorname{Spec}A$ with $I=(f_0,\ldots,f_r)$, wherever $f_i$ generates $I\mathcal O_Y$, the ratios $f_j/f_i$ are regular. They define a map to the chart

$$
\operatorname{Spec}A[f_0/f_i,\ldots,f_r/f_i].
$$

The chart maps agree because the ratios satisfy the same identities. Uniqueness holds on these covering charts. $\square$

Blowing up the unit ideal does nothing. More generally, blowing up an invertible ideal is an isomorphism. Thus a center supported on finitely many closed points leaves their complement unchanged.

### 7.2 Charts and exceptional curves

For $X=\operatorname{Spec}A$ and $I=(a,b)$, the blowup has two main charts

$$
\operatorname{Spec}A[b/a]
\quad\text{and}\quad
\operatorname{Spec}A[a/b],
$$

where these are subalgebras of the appropriate localization, not polynomial rings with an unconstrained new variable. If $A=k[x,y]$ and $I=(x,y)$, the first chart is $k[x,t]$ with $y=xt$ and the second is $k[s,y]$ with $x=sy$. The inverse image of the origin is $\mathbf P^1_k$.

Blowing up a regular surface at a closed regular point preserves regularity. In the chart above, regular parameters $(x,y)$ become $(x,t)$ or $(s,y)$. If the residue field is not algebraically closed, the exceptional curve is $\mathbf P^1_{\kappa(x)}$. The exceptional curve records tangent directions at the center.

Blowup commutes with **flat** base change, but not with arbitrary base change. On affine rings, for a map $A\to B$ and an ideal $I\subset A$, multiplication gives a natural graded map

$$
\left(\bigoplus_{n\geq0}I^n\right)\otimes_A B
\longrightarrow
\bigoplus_{n\geq0}(IB)^n,
$$

whose degree-$n$ component is

$$
I^n\otimes_A B\longrightarrow(IB)^n.
$$

Its image is $I^nB=(IB)^n$, but for a nonflat map it can have a kernel: tensoring need not preserve the inclusion $I^n\hookrightarrow A$. If $B$ is flat, every degree map is an isomorphism, so the base-changed Rees algebra is the Rees algebra of $IB$ and relative Proj gives

$$
\operatorname{Bl}_I(\operatorname{Spec}A)\times_{\operatorname{Spec}A}
\operatorname{Spec}B
\simeq
\operatorname{Bl}_{IB}(\operatorname{Spec}B).
$$

The failure can be drastic. If $A=k[x]$, $I=(x)$, and $B=A/(x)$, then $I\otimes_A B\simeq B$ maps to $IB=0$. The original blowup is $\operatorname{Spec}A$ because $I$ is invertible, so its base change is $\operatorname{Spec}B$, whereas the blowup of the zero ideal on $\operatorname{Spec}B$ is empty. Strict transforms have a further saturation issue: one must remove components created inside the exceptional divisor. None of the resolution arguments below transports a chosen blowup through a nonflat base change; after ramified base change, Chapter 10 instead normalizes and resolves the new model afresh.

### 7.3 Normalized blowups

If $X$ is normal and $\operatorname{Bl}_{\mathcal I}X$ is not normal, define the **normalized blowup** as its normalization. For a scheme of finite type over an excellent base, this normalization is finite by Theorem 3.3. Hence the normalized blowup remains projective and birational over $X$.

The construction combines two corrections. Blowup changes the birational geometry so that an ideal becomes invertible; normalization then restores integrally closed local rings. For a surface, normalized blowups centered at closed singular points keep all codimension-one local rings under valuation control.

There is a valuation interpretation. Let $A$ be a normal domain and $I$ a nonzero ideal. The normalization of the Rees algebra $A[It]$ in $A[t]$ is graded; its degree-$n$ part is the integral closure $\overline{I^n}$. The normalized blowup is therefore

$$
\operatorname{Proj}\bigoplus_{n\geq0}\overline{I^n}.
$$

It depends only on the integral-closure class of the ideal. Divisorial valuations appearing on the exceptional locus measure the asymptotic orders of the powers $I^n$.

We will need the corresponding statement about contraction, not just the description of the
graded normalization.

**Proposition 7.2A (contraction from a normalized blowup).** Let $A$ be a normal noetherian
domain, let $I\ne0$ be an ideal, and let
$f:X\to\operatorname{Spec}A$ be a proper normal modification which dominates
$\operatorname{Bl}_I A$. Then, for every $n\geq0$,

$$
H^0(X,I^n\mathcal O_X)=\overline{I^n}.                       \tag{7.1a}
$$

The same assertion holds after localization and for a coherent ideal on a normal scheme.

**Proof.** We use the valuation criterion for integral dependence of ideals: for
$z\in\operatorname{Frac}(A)$,

$$
z\in\overline{I^n}
\quad\Longleftrightarrow\quad
z\in I^nV
\quad\text{for every valuation ring }A\subseteq V\subseteq\operatorname{Frac}(A).
\tag{7.1b}
$$

This is the elementwise valuation criterion applied to the Rees algebra: $z$ is integral over
$I^n$ exactly when $zt^n$ is integral over $A[It]$, and an element of a fraction field is
integral over a domain exactly when it belongs to every valuation overring. Thus (7.1b) is the
valuation theorem of Book 1 applied to one graded domain, not a surface-intersection statement.

If $z$ is a section of $I^n\mathcal O_X$, properness gives a center on $X$ for every such
valuation $V$, and the local inclusion at that center gives $z\in I^nV$. Hence
$z\in\overline{I^n}$. Conversely, if $z\in\overline{I^n}$, then in every normal local domain
$\mathcal O_{X,x}$ it is integral over the invertible ideal
$I^n\mathcal O_{X,x}$. After choosing a generator, this reduces to integrality over a principal
ideal. Principal ideals in a normal domain are integrally closed, so
$z\in I^n\mathcal O_{X,x}$ for every $x$. These local memberships glue to a global section and
prove (7.1a). $\square$

### 7.4 Locality and projectivity

Blowing up is local on the target and projective over it. If an ideal is supported in a closed subset $Z$, the blowup is an isomorphism over $X\setminus Z$. Thus resolutions may be performed one singular point at a time and glued with the unchanged regular open.

For arithmetic surfaces, every chosen center will be vertical and disjoint from the generic fiber. The resulting morphism is then an isomorphism on the generic curve. A composite of finitely many blowups and finite normalizations is projective. Consequently resolving a projective model keeps it projective, not merely proper.

## 8. Resolving surface singularities

### 8.1 The resolution theorem in the required setting

The central low-dimensional theorem is not a formal consequence of normalization, excellence, or
the elementary blowup calculations above. We therefore isolate exactly the additional result used
from this point onward.

**Theorem 8.1 (surface resolution).** Let $X$ be a reduced excellent noetherian
scheme of dimension at most two, and let $U\subseteq X$ be a regular open subscheme. There exists a projective
birational morphism

$$
r:X'\longrightarrow X
$$

such that $X'$ is regular and $r$ is an isomorphism over $U$.

Projectivity keeps projective models projective, and the relative clause preserves every
prescribed regular open. The proof occupies Sections 8.2--8.7.

### 8.2 Preparing the singular locus

We first record the elementary reduction that any proof of Theorem 8.1 must use.

**Lemma 8.2 (surface preparation).** Let $X$ be a reduced excellent noetherian scheme of dimension at most two, let $U=X_{\mathrm{reg}}$, and let $\nu:X^{\nu}\to X$ be its componentwise normalization. Then $\nu$ is finite and is an isomorphism over $U$. The singular locus of $X^{\nu}$ is a closed subset of codimension at least two, and hence is finite.

**Proof.** Reduce $X$, separate its irreducible components by normalization, and use finiteness from the Nagata property, available by Theorem 3.2(2). A normal noetherian surface satisfies $(R_1)$, so every codimension-zero or codimension-one point is regular. The $J_2$ half of excellence makes the regular locus open, by Theorem 3.2(4). Hence the singular locus is closed and consists of dimension-zero points. A noetherian zero-dimensional closed space has finitely many points. $\square$

Thus the new input needed for Theorem 8.1 is local at the finitely many singular points: one must resolve $\operatorname{Spec}A$ for a two-dimensional excellent normal local domain $(A,\mathfrak m)$; such a ring is excellent because it is a local ring of the excellent scheme $X^{\nu}$, by Theorem 3.2(1). A modification supported at $\mathfrak m$ glues to the identity away from that point. If the required local modifications exist and terminate, those over the finitely many prepared points can be composed without disturbing the regular open.

Completion is a powerful diagnostic but must be used with care. Excellence gives that
$A\to\widehat A$ is a regular faithfully flat map, so $A$ is regular if and only if $\widehat A$
is, and normal if and only if $\widehat A$ is; this is Theorem 3.2(3). It does not follow merely from excellence that a center constructed in $\widehat A$ descends to
$A$, nor that numerical inequalities proved after completion survive an approximation. Those are
parts of a proof of Theorem 8.1, not consequences of the preparation lemma.

### 8.3 Finite differentials and exterior trace

The reduction argument must work over an imperfect coefficient field and through purely
inseparable extensions. Ordinary Kähler differentials of a power-series ring are too large for
this purpose, while ordinary field trace is zero in a purely inseparable extension. We construct
the finite differential module and its exterior trace together, including ramified and
inseparable-residue extensions of height-one discrete valuation rings.

#### 8.3.1 Finite differentials and admissible coefficient fields

Let $k$ have characteristic $p>0$. A **coefficient subfield** is a field

$$
k^p\subseteq k_0\subseteq k,\qquad [k:k_0]=p^e<\infty.
$$

For a complete local $k$-algebra $(R,\mathfrak n)$ with residue field finite over $k$, put

$$
Q(R/k_0)=\varprojlim_j\Omega_{(R/\mathfrak n^j)/k_0}.
$$

If $B$ is a localization of a finite-type $R$-algebra, define $Q(B/k_0)$ from the exact
presentation

$$
B\otimes_RQ(R/k_0)\longrightarrow Q(B/k_0)
   \longrightarrow\Omega_{B/R}\longrightarrow0                 \tag{8.1}
$$

by imposing $d_Br=1\otimes d_Rr$. Thus $Q(B/k_0)$ represents those $k_0$-derivations into
finite $B$-modules whose restriction to $R$ is $\mathfrak n$-adically continuous. A change of
complete presentation gives the same representing functor and hence the same pair
$(Q(B/k_0),d_B)$. If $R=k[[u_1,\ldots,u_s]]$, direct passage to the inverse limit gives

$$
Q(R/k_0)=
 (R\otimes_k\Omega_{k/k_0})\oplus R\,du_1\oplus\cdots\oplus R\,du_s,
\tag{8.2}
$$

and, equivalently in characteristic $p$, $Q(B/k_0)$ is the usual module of
$k_0[[u_1^p,\ldots,u_s^p]]$-differentials. Formula (8.2), followed by (8.1), proves that all
these modules are finite. We write $Q^r(B/k_0)=\bigwedge_B^rQ(B/k_0)$.

For a domain $B$ essentially of finite type over a power-series ring, let $n(B)$ be the
dimension of a finite power-series subring and let $t(B)$ be the transcendence degree of its
fraction field over that subring. These numbers are independent of the chosen subring by the
dimension formula. We call $k_0$ **admissible for $B$** when $B$ is regular and
$Q(B/k_0)$ is free of rank $n(B)+t(B)+e$; it is admissible for a field when the corresponding
vector-space dimension has that value.

**Lemma 8.3 (existence and spreading of admissible fields).** Let
$R=k[[u_1,\ldots,u_s]]$, let $K=\operatorname{Frac}R$, and let $L/K$ be finitely generated.
Every coefficient subfield $k_*\subseteq k$ contains one admissible for $L$. More generally, if
$X$ is reduced and finite type over $R$, one may choose $k_0\subseteq k_*$ for which
$Q(X/k_0)$ is locally free of the expected rank at every regular point of $X$.

**Proof.** Work in a fixed algebraic closure of $K$ and put

$$
k_0^{1/p}=\{c:c^p\in k_0\},\qquad
G_0=\operatorname{Frac}\bigl(k_0^{1/p}[[u_1,\ldots,u_s]]\bigr).
$$

The inclusion $k^p\subseteq k_0$ gives $k\subseteq k_0^{1/p}$, and hence
$K\subseteq G_0$. The $p$-degree formula says

$$
\dim_LQ(L/k_0)\ge s+t(L)+e,
$$

with equality exactly when $G_0$ and $L$ are linearly disjoint over $K$. To see both assertions,
choose $F=K(v_1,\ldots,v_t)\subset L$ with $L/F$ finite. For successively smaller coefficient
fields $k_0$, their fields $k_0^{1/p}$, and therefore the $G_0$, shrink. The integer
$[G_0L:G_0F]$ is nondecreasing and bounded by $[L:F]$, hence
stabilizes. Moreover

$$
\bigcap_{k_0\subseteq k_*}G_0F=F.                              \tag{8.3}
$$

Indeed, after taking a $p$-power, an element of the intersection is a rational function in the
$v_i$ with coefficients in $k[[u_1,\ldots,u_s]]$; clearing one common denominator reduces to
polynomials. A coefficient in $k_0^{1/p}[[u_1,\ldots,u_s]]$ but outside $K$ is excluded by
removing from $k_0$ the $p$-th power of one member of a $p$-basis occurring in that coefficient.
Thus every surviving coefficient lies in $K$, proving (8.3). At a stabilized field, a
$G_0F$-basis of $G_0L$ consequently spans $L$ over $F$ by (8.3), so equality holds and $k_0$ is
admissible for $L$.

For the scheme assertion let $Z(k_0)$ be the closed nonfree locus of $Q(X/k_0)$ at the expected
rank and choose $k_0$ for which this closed set is minimal. If $x\in Z(k_0)$ were regular, apply
the field assertion to $\kappa(x)$. Shrinking $k_0$ makes $Q(\kappa(x)/k_0)$ have the expected
dimension. The cotangent exact sequence

$$
\mathfrak m_x/\mathfrak m_x^2\longrightarrow
 Q(\mathcal O_{X,x}/k_0)\otimes\kappa(x)\longrightarrow
 Q(\kappa(x)/k_0)\longrightarrow0
$$

and the dimension formula show, by Nakayama, that $Q(\mathcal O_{X,x}/k_0)$ is free of the
expected rank. Passing to a smaller coefficient field only adds the differentials of a finite
$p$-basis, so it preserves freeness and contradicts minimality of $Z(k_0)$. $\square$

This construction is the equicharacteristic part of the finite regular-subring theorem used
later, which for a two-dimensional complete normal local domain $A$ is exactly Book 1,
Theorem 13.34. In equal characteristic a coefficient field $K\cong k$ exists by Book 1,
Theorem 13.15, and a parameter ideal $(x,y)$ makes $A/(x,y)$ of finite length, so Book 1,
Theorem 13.34(1) gives $k[[x,y]]\hookrightarrow A$ finite. In mixed characteristic a Cohen ring
$C$ for $k$ exists by Book 1, Theorem 13.21 and maps to $A$ inducing the identity on residue
fields by Book 1, Theorem 13.25; choosing $x$ so that $(p,x)$ is a parameter ideal, Book 1,
Theorem 13.34(2) gives $C[[x]]\hookrightarrow A$ finite. In either case the source is a complete
regular local domain of dimension two by Book 1, Lemma 13.29, and injectivity is the closing
clause of Book 1, Theorem 13.34: it follows from equality of dimensions and the fact that $A$ is
a domain.

#### 8.3.2 Exterior trace without a separability hypothesis

Suppose $k_0$ is admissible for the fields in a finite tower. For a finite separable step
$L'/L$, define

$$
\tau:Q^r(L'/k_0)=L'\otimes_LQ^r(L/k_0)\longrightarrow Q^r(L/k_0)
$$

by field trace on the first factor. For a purely inseparable step $L'=L(a)$ of degree $p$, with
$a^p=b\in L$, define

$$
\tau\bigl((c_0+c_1a+\cdots+c_{p-1}a^{p-1})\,da\wedge\eta\bigr)
 =c_{p-1}\,db\wedge\eta,                                    \tag{8.3a}
$$

and make $\tau$ zero on $L'\otimes_LQ^r(L/k_0)$. The cotangent relation is $db=0$ after
extension to $L'$, so (8.3a) descends to exterior powers.

**Lemma 8.4 (coordinate independence).** Formula (8.3a) is independent of the generator $a$ and
is functorial in towers of degree-$p$ extensions.

**Proof.** If $a=\lambda_0+\lambda_1c+\cdots+\lambda_{p-1}c^{p-1}$ and $c^p=d$, then

$$
b=\lambda_0^p+\lambda_1^pd+\cdots+\lambda_{p-1}^pd^{p-1}.
$$

For $i<p-1$, every coefficient of degree $mp-1$ in
$a^i(da/dc)=(i+1)^{-1}d(a^{i+1})/dc$ vanishes. For $i=p-1$, calculate before reduction modulo
$p$: the coefficient surviving after $c^p=d$ is
$\lambda_1^p+2\lambda_2^pd+\cdots+(p-1)\lambda_{p-1}^pd^{p-2}$, whose product with $d(d)$ is
$db$. This verifies (8.3a) on a basis; composition gives functoriality. $\square$

The essential point is integrality at a height-one ring.

**Lemma 8.5 (integral exterior trace).** Let $f:Y\to X$ be a finite morphism of noetherian normal
integral schemes in characteristic $p$, whose function-field extension is purely inseparable of
degree $p$. If the finite differential modules relative to $k_0$ are coherent, there is a
canonical map

$$
\tau:f_*Q^i(Y/k_0)\longrightarrow Q^i(X/k_0)^{**}             \tag{8.3b}
$$

whose generic stalk is (8.3a).

**Proof.** Coherence and reflexivity reduce extension of the generic map to codimension one.
There the local rings $D\subset D'$ are DVRs and $D'$ is finite free of rank $p$ over $D$.
The equality of that rank with the product of ramification index and residue degree leaves two
cases. In the ramified case a uniformizer $a$ of $D'$ satisfies $a^p=b$ for a uniformizer $b$ of
$D$, and $D'=D[a]$. In the residue-inseparable case choose a unit $a\in D'$ whose residue
generates the degree-$p$ residue extension; again $D'=D[a]$ and $a^p=b\in D$. Formula (8.3a),
applied over $D$ in either presentation, sends integral differentials to integral differentials.
Lemma 8.4 makes the maps agree on overlaps. Their codimension-one extensions therefore intersect
to the asserted map into the reflexive hull. $\square$

**Lemma 8.5A (canonical comparison under point blowups).** Let $R=k[[u,v]]$ and let $k_0$ be
admissible for $R$. If $f:X\to\operatorname{Spec}R$ is an iterated blowup at closed points, put

$$
\Omega_X^r=\left(\bigwedge^r Q(X/k_0)/\text{torsion}\right)^{**}.
$$

There is a morphism $\phi_X:\Omega_X^r\to\omega_X$ which is the chosen identification
$Q^r(R/k_0)\simeq\omega_R$ at the generic point. This holds in every characteristic; the map need
not be an isomorphism.

**Proof.** Both sheaves are invertible because $X$ is regular. Start with the chosen isomorphism
on $R$. Suppose $b:X'\to X$ is the blowup of a closed point with exceptional curve $E$. On the
chart $y=xt$, the relative differential is generated by $dt$ with
$xdt=dy-t\,dx$. Taking the top exterior power and removing torsion shows

$$
\Omega_{X'}^r\simeq b^*\Omega_X^r(E)
\quad\text{or}\quad
\Omega_{X'}^r\simeq b^*\Omega_X^r.                           \tag{8.3c0}
$$

The second alternative can occur in characteristic $p$; no equality with the canonical transform
is asserted. In either case $Rb_*\Omega_{X'}^r=\Omega_X^r$. Indeed this is clear in the second
case, while in the first it follows from
$0\to\mathcal O_{X'}\to\mathcal O_{X'}(E)\to\mathcal O_E(-1)\to0$ and the elementary
cohomology of the projective line. Proper duality for $b$ therefore identifies a map
$\Omega_{X'}^r\to b^!\omega_X=\omega_{X'}$ with a map
$Rb_*\Omega_{X'}^r\to\omega_X$. Compose the displayed identification with $\phi_X$.
Induction constructs $\phi_{X'}$ and preserves its generic identification. $\square$

### 8.4 Quadratic transformations

Let $(A,\mathfrak m,k)$ be a two-dimensional regular local ring and let
$b:X=\operatorname{Bl}_{\mathfrak m}\operatorname{Spec}A\to\operatorname{Spec}A$.

**Lemma 8.6 (geometry of a quadratic transform).** The scheme $X$ is regular and integral, its
exceptional divisor is $E\simeq\mathbf P^1_k$, and

$$
\mathcal O_X(-E)=\mathcal O_X(1),\qquad
\mathcal O_E(E)=\mathcal O_{\mathbf P^1}(-1).
\tag{8.4}
$$

**Proof.** Choose regular parameters $u,v$. The Rees algebra is generated by $u,v$ in degree
one, so $X$ is the closed subscheme $uV=vU$ of $\mathbf P^1_A$. Its two charts are
$A[v/u]$ and $A[u/v]$. On the first, $u$ and $v/u$ are regular parameters at every closed point
above $\mathfrak m$; the second is identical. Tensoring the Rees algebra with $k$ gives
$\operatorname{gr}_{\mathfrak m}A=k[\bar u,\bar v]$, hence $E=\mathbf P^1_k$. The tautological
invertible ideal is $\mathfrak m\mathcal O_X=\mathcal O_X(1)=\mathcal O_X(-E)$, whose
restriction is $\mathcal O_E(1)$. $\square$

**Lemma 8.7 (cohomology of a quadratic transform).** For every quasi-coherent $\mathcal F$ on
$X$, $H^i(X,\mathcal F)=0$ for $i\ge2$. Moreover

$$
H^1(X,\mathcal O_X(n))=0\quad(n\ge-1),
\qquad
H^0(X,\mathcal O_X(n))=\mathfrak m^{\max(0,n)},
\tag{8.5}
$$

and for $n<0$,

$$
\operatorname{length}_A H^1(X,\mathcal O_X(n))=\frac{(-n)(-n-1)}2.
\tag{8.6}
$$

**Proof.** The two affine charts above have affine intersection, so their Cech complex has only
degrees zero and one. Relative ampleness gives $H^1(X,\mathcal O_X(N))=0$ for $N\gg0$.
Use successively

$$
0\to\mathcal O_X(n+1)\to\mathcal O_X(n)\to\mathcal O_E(n)\to0,
$$

with $H^1(\mathbf P^1,\mathcal O(d))=0$ for $d\ge-1$. Descending induction yields (8.5).
For negative $n$, the same sequences add the dimensions
$1+2+\cdots+(-n-1)$, proving (8.6). Global sections of $\mathcal O_X(n)$ for $n\ge0$ are the
degree-$n$ elements of the Rees algebra, namely $\mathfrak m^n$; for $n<0$, normality and the
codimension-two complement give $A$. $\square$

The next local theorem replaces every appeal to ``general members.'' It is valid over finite and
imperfect residue fields because all sums are weighted by the actual residue degrees.

**Lemma 8.8 (embedded principalization on a regular surface).** Let $T$ be an excellent regular
integral surface and let $I\subset\mathcal O_T$ be a nonzero coherent ideal. There is a finite
sequence of blowups at closed regular points

$$
T_r\longrightarrow\cdots\longrightarrow T_0=T
$$

such that the torsion-free pullback of $I$ to $T_r$ is invertible. The centers may be confined to
the locus where $I$ is not already invertible.

**Proof.** Remove the invertible height-one part of $I$. Its remaining cosupport is a finite set
of closed points, so it is enough to work over one regular local ring $(A,\mathfrak m,k)$ of
dimension two. Choose generators $f_0,\ldots,f_s$ and let $D$ be the reduced divisor cut out by
$f_0\cdots f_s$. Excellence makes the normalization of $D$ finite, by Theorem 3.2(2).

We first make the reduced total transform of $D$ a strict normal-crossings divisor. For a point
$x$ of the current strict transform of $D$ put

$$
\delta_x=\operatorname{length}_{\mathcal O_{D,x}}
 (\overline{\mathcal O}_{D,x}/\mathcal O_{D,x}).
$$

If $b:T'\to T$ is the blowup of $x$, $D'$ is the reduced strict transform, and $m_x(D)$ is the
order of a local equation, comparison of the two normalization exact sequences on the affine
charts $A[v/u]$ and $A[u/v]$ gives

$$
\delta_x=\binom{m_x(D)}2+
 \sum_{x'\mapsto x}[\kappa(x'):k]\cdot\delta_{x'}.            \tag{8.6a}
$$

Here is the local calculation behind the correction term. Filter the chart rings and their
normalizations by the exceptional parameter. In degrees $0,\ldots,m_x(D)-1$, the missing initial
monomials are respectively $0,1,\ldots,m_x(D)-1$ copies of the residue field; all later graded
pieces identify with those of the strict-transform normalization. Taking lengths gives
$1+\cdots+(m_x(D)-1)$, while restriction of scalars from a point $x'$ multiplies length by
$[\kappa(x'):k]$. This proves (8.6a) without an intersection pairing.

A reduced curve on a regular surface is regular at a point of multiplicity one. Thus at every
singular point the first term of (8.6a) is positive. Along every branch of successive singular
centers the nonnegative integer obtained by residue-weighting the remaining delta invariants
strictly decreases. Each stage has finitely many singular points, so the finitely branching tree
has no infinite branch and is finite.

After the branches are regular, two distinct branches with equations $g,h$ have contact

$$
i_x(g,h)=\operatorname{length}_A A/(g,h).
$$

The identical exceptional-parameter filtration gives

$$
i_x(g,h)=m_x(g)m_x(h)+
 \sum_{x'\mapsto x}[\kappa(x'):k]\cdot i_{x'}(g',h').        \tag{8.6b}
$$

For regular tangent branches the first term is one and the residual weighted contact is strictly
smaller. Repeatedly blow up tangencies. Once every pair is transverse, blowing up a point through
three or more branches places their distinct tangent directions at distinct closed points of the
exceptional line. Include every exceptional curve among the branches at the next stage; point
blowups preserve normal crossings away from the center. Hence finitely many further blowups make
the reduced total transform of $D$ strict normal crossings. Notice
that (8.6a) and (8.6b), including their residue factors, require no rational point or generic
linear combination.

On the resulting surface, at a point with parameters $u,v$ cutting out the at most two branches
of that total transform, every generator has the form
$\varepsilon_i u^{a_i}v^{b_i}$ with $\varepsilon_i$ a unit.
Thus the transformed ideal is monomial. A monomial ideal in a two-dimensional regular local ring
is principalized by finitely many blowups of the crossings of the coordinate divisors. For
completeness, attach to its exponent set the lower Newton polygon. A blowup replaces the cone
spanned by $(1,0),(0,1)$ by the two cones spanned by

$$
(1,0),(1,1)\quad\text{and}\quad(1,1),(0,1).
$$

After removing the common monomial on each chart, this is exactly the weak transform of the
ideal. Insert successively the primitive inward normals to the finitely many compact edges of the
polygon. If adjacent primitive rays have determinant $d>1$, the Euclidean algorithm inserts
their primitive sum and strictly lowers the determinant. A finite regular subdivision results.
On each regular cone one exponent is minimal for both coordinates, so its monomial divides all
the others and the ideal is principal. These toric subdivisions are precisely blowups of the
actual closed crossings and remain valid over $k$ without splitting any residue field.

All centers used above lie over the original noninvertible locus. Performing the constructions at
the finitely many points proves the global assertion. $\square$

**Corollary 8.8A (factorization through point blowups).** Let $T$ be an excellent regular
integral surface and let $Z\to T$ be a projective birational morphism. There is a sequence of
blowups at closed regular points $T_r\to\cdots\to T_0=T$ and a morphism $T_r\to Z$ over $T$.

**Proof.** Choose a relatively ample line bundle on $Z$ and replace it by a power which is
generated over $T$ and whose section algebra is generated in degree one. Trivialize it at the
generic point. Its direct image is then a coherent fractional ideal $I\subset K(T)$, and the
relative-Proj presentation identifies $Z$ with the blowup of $I$, after multiplying $I$ by one
denominator. Lemma 8.8 makes $I\mathcal O_{T_r}$ invertible. The universal property of the blowup
then gives $T_r\to Z$. $\square$

**Lemma 8.8B (finite graph domination).** Let $R$ be an excellent regular local domain of
dimension two with fraction field $K$, let $L/K$ be finite, and let $B$ be the integral closure of
$R$ in $L$. Every proper normal modification $W\to\operatorname{Spec}B$ is dominated by the
normalization in $L$ of an iterated closed-point blowup of $\operatorname{Spec}R$.

**Proof.** Chow's lemma followed by normalization supplies a projective normal modification
dominating $W$, so assume $W$ projective. We record the specialized flattening argument needed
here. If $P\to\operatorname{Spec}R$ is projective and its generic fiber is the finite scheme
$\operatorname{Spec}L$, choose a relatively very ample $\mathcal O_P(1)$. For $q$ beyond one
common regularity bound, the finite modules

$$
M_q=H^0(P,\mathcal O_P(q))
$$

and the multiplication and relation maps among the $M_q$ present $P$ as relative Proj; Book 8's
graded-presentation theorem shows that only finitely many consecutive $q$ are required. Over $K$
these modules all have rank $[L:K]$. For a finite module $M$ of generic rank $r$, blowing up the
ideal of its $r\times r$ minors makes the torsion-free pullback of $M$ locally free of rank $r$:
on the chart of one nonzero minor, divide every other maximal minor by it, and Cramer's rule gives
a free basis; the lower Fitting ideals exclude a rank drop. Apply this successively to the
finitely many modules, kernels, and cokernels in the chosen graded presentation. The product of
the resulting Fitting ideals is supported at the closed point, and on its blowup the strict
transform $P'$ has constant Hilbert polynomial $[L:K]$. It is therefore flat with
zero-dimensional fibers, hence finite flat, over that blowup. This is the projective
graph-flattening theorem in the only case used here, proved by the displayed minors rather than
invoked as an unspecified flattening step.

Apply this construction to $P=W$ viewed over $R$. By Lemma 8.8, an iterated point blowup
$X\to\operatorname{Spec}R$ principalizes the product of the Fitting ideals and hence dominates
the flattening blowup. The strict transform $W_X\to X$ is finite, has function field $L$, and maps
to $W$. Its normalization is the integral closure of $X$ in $L$. Finiteness follows from
Theorem 3.3, and the universal property of normalization gives

$$
\operatorname{Nor}_L(X)\longrightarrow W_X\longrightarrow W.
$$

Thus the normalization of the point-blowup sequence dominates the original modification.
$\square$

**Lemma 8.9 (normalized point-blowup domination).** Let $A$ be a two-dimensional normal Nagata
local domain. Every proper birational modification of $\operatorname{Spec}A$ is dominated by a
finite composite of normalized blowups at closed points.

**Proof.** Normalize the source. The morphism is an isomorphism outside the closed point, and it
has only finitely many exceptional curves. Induct on their number. Blow up the closed point of the
target and normalize; normalize also its fiber product with the source. Exceptional curves of the
new comparison inject into the old exceptional curves, because normalization is finite and the
comparison is an isomorphism at every old codimension-one point.

It remains to show that repeated normalized point blowups remove at least one old curve $C$.
At its generic point choose a rational function $u=a/b$ whose residue is transcendental over the
residue field of the closed point. Necessarily $a,b$ belong to the maximal ideal. Put

$$
N_C(a,b)=\min\{\operatorname{ord}_C(a),\operatorname{ord}_C(b)\}>0.
$$

If $C'$ above $C$ remains exceptional after the normalized blowup, then on the relevant chart
$a=a'd$ and $b=b'd$, where $d$ cuts out the exceptional Cartier divisor. Normalization is an
isomorphism at the generic point of $C$, so

$$
N_{C'}(a',b')=N_C(a,b)-\operatorname{ord}_C(d)<N_C(a,b).
$$

After finitely many steps $C$ can no longer occur. The number of exceptional curves then drops,
and induction ends. Finiteness of every normalization follows from the Nagata hypothesis.
$\square$

### 8.5 The remaining local resolution chain

The trace and quadratic-transformation results above are the first inputs to the resolution
proof. We next construct the duality and vanishing package, prove boundedness under finite
extensions, pass through rational singularities and rational double points, and lift normalized
blowups from completions. Only after those steps will Theorem 8.1 be discharged.

#### 8.5.1 Local duality in dimension two

From this subsection through Proposition 8.21, $A$ is complete. Book 1, Corollary 13.31 supplies
a surjection $Q\twoheadrightarrow A$ from a complete regular local ring: one may take
$Q=k[[X_1,\ldots,X_n]]$ if $A$ contains a field and $Q=C[[X_1,\ldots,X_n]]$ otherwise, with $C$
a Cohen ring for the residue field $k$ and $n$ the minimal number of generators of $\mathfrak m$;
these are complete regular local domains by Book 1, Lemma 13.29. Write $N=\dim Q$ and set

$$
D_A=R\operatorname{Hom}_Q(A,Q[N]).
$$

Proposition 4.1A gives finite global dimension for the regular ring $Q$ and depth two for the
normal surface ring $A$. The resulting depth calculation therefore concentrates this complex in one degree:
$D_A=\omega_A[2]$, where $\omega_A=\operatorname{Ext}^{N-2}_Q(A,Q)$ is a finite maximal
Cohen--Macaulay module. Applying the $\mathfrak m$-torsion functor to an injective resolution of
$D_A$ leaves the injective hull $E_A(k)$ in degree zero. Consequently, for every finite-length
module $M$,

$$
\operatorname{Ext}^i_A(M,\omega_A)=0\ (i\ne2),
\qquad
\operatorname{Ext}^2_A(M,\omega_A)=\operatorname{Hom}_A(M,E_A(k)).
\tag{8.7}
$$

The last functor, denoted $M^\vee$, is an exact length-preserving duality on finite-length
modules: induction on a composition series reduces this to
$\operatorname{Hom}_A(k,E_A(k))=k$. The same injective-resolution calculation, or equivalently
the Cech complex on generators of $\mathfrak m$, gives

$$
H^2_{\mathfrak m}(A)^\vee\simeq\omega_A.                 \tag{8.7a}
$$

The right side of (8.7a) is intrinsic. We henceforth use (8.7a) to identify $\omega_A$; in
particular the module and the complex $D_A=\omega_A[2]$ do not depend on the chosen regular
presentation $Q\twoheadrightarrow A$.

We need proper duality below only for **projective** modifications, and construct precisely that
case. If $f:X\to\operatorname{Spec}A$ is projective, choose
$X\hookrightarrow\mathbf P^n_A$ and compose with the closed immersion
$\mathbf P^n_A\hookrightarrow P=\mathbf P^n_Q$. The ambient scheme $P$ is regular of dimension
$N+n$. Hence $\mathcal O_X$, viewed on $P$, has a finite locally free resolution: resolve by
sums of twists, and after $N+n$ steps the local syzygies are projective because every local ring
of $P$ has global dimension at most $N+n$. Define

$$
D_X=R\mathcal Hom_P
   (\mathcal O_X,\omega_{P/Q}[N+n]).
$$

Proposition 4.1A makes the pure two-dimensional normal scheme $X$ Cohen--Macaulay. The same depth
and finite-resolution calculation as for $A$ therefore gives $D_X=\omega_X[2]$ for a maximal
Cohen--Macaulay sheaf $\omega_X$. Notice that the resolution is taken over the regular scheme
$P$, not over $\mathbf P^n_A$, whose local rings need not be regular and over which
$\mathcal O_X$ need not have finite projective dimension.

For a bounded coherent complex $F$ on $X$, projective-space duality over $Q$, followed by the
derived adjunction for $Q\twoheadrightarrow A$, gives

$$
R\operatorname{Hom}_A(Rf_*F,\omega_A[2])
\simeq Rf_*R\mathcal Hom_X(F,\omega_X[2]).
\tag{8.8}
$$

Here is the independence check that prevents the construction from depending on its ambient
space. A second embedding gives a second complex and a second instance of (8.8). Both represent,
functorially in every bounded coherent $F$, the same functor
$R\operatorname{Hom}_A(Rf_*F,D_A)$. Yoneda therefore gives a unique isomorphism between the two
complexes compatible with (8.8). For three embeddings uniqueness gives the cocycle identity.
Equivalently, on the product embedding this is the total finite resolution obtained by tensoring
the two ambient resolutions with the Koszul resolution of the diagonal; the two top Cech
coefficient maps agree. Thus (8.8), biduality, and $\omega_X$ are independent of $Q$, the
embedding, and the chosen resolutions. No projective factorization is asserted for an arbitrary
proper modification.

#### 8.5.2 Vanishing on a normal modification

**Lemma 8.10 (positive conormal).** Let $X$ be a normal modification of
$\operatorname{Spec}A$ and let $0\ne Z$ be an effective Cartier divisor supported on the closed
fiber. Some component $C$ of $Z$ has $\deg(\mathcal I_Z|_C)>0$.

**Proof.** Write the closed-fiber components as $C_i$. Choose
$x_i\in C_i\setminus\bigcup_{j\ne i}C_j$ and
$g_i\in\mathfrak m_{X,x_i}$ whose restriction to $C_i$ is nonzero. Since $X$ and
$\operatorname{Spec}A$ have the same function field, write $g_i=a_i/b_i$ with $a_i,b_i\in A$
and put $h=\prod_i a_i$. At the generic point of $C_i$, let $e_i>0$ be the valuation of $h$ and
let $d_i\ge0$ be the multiplicity of $Z$. Choose $i$ maximizing $d_i/e_i$; then $d_i>0$.
Replace $h$ by $h^{d_i}$ and $Z$ by $e_iZ$. For every $j$ the inequality
$d_ie_j\ge e_id_j$ says that $h$ lies in $\mathcal I_Z$ at the generic point of $C_j$, and at
$C_i$ its order is exactly that of $Z$. The Cartier divisor $Z$ on a normal surface is
Cohen--Macaulay, hence has no embedded associated points; generic membership therefore gives a
global section $h\in H^0(X,\mathcal I_Z)$. Its restriction to $C_i$ is nonzero and vanishes at
$x_i$ because $a_i=g_ib_i$ occurs as a factor. A nonzero section of a line bundle on a proper
integral curve has degree equal to the degree of its zero divisor, so
$\deg(\mathcal I_Z|_{C_i})>0$. Dividing by the positive scaling $e_i$ gives the assertion for the
original $Z$. $\square$

**Lemma 8.11 (punctured injection).** The restriction
$H^1(X,\mathcal O_X)\to H^1(X\setminus X_s,\mathcal O_X)$ is injective.

**Proof.** A nonzero class in the kernel gives an extension
$0\to\mathcal O_X\to\mathcal E\to\mathcal O_X\to0$ split on the punctured surface. The quotient
defines a section $\sigma:X\to P=\mathbf P(\mathcal E)$ with trivial conormal; the punctured
splitting defines a second section $\sigma'$ disjoint from $\sigma$. Let $Y$ be the
scheme-theoretic closure of $\sigma'$ in $P$. If $Y$ missed $\sigma(X)$, then it would lie in
$P\setminus\sigma(X)$, which is the affine bundle
$\operatorname{Spec}_X\operatorname{Sym}(\mathcal O_X)$ over $X$. Thus $Y\to X$ would be both
affine and proper, hence finite; being finite birational onto the normal $X$, it would be an
isomorphism and would extend the splitting, contrary to the chosen nonzero class.

Therefore $Y$ meets $\sigma(X)$. Normalize $Y$; finiteness follows from the Nagata property of
the complete ring $A$ and its finite-type algebras. The pullback $Z$ of $\sigma(X)$ is a nonempty
effective Cartier divisor supported over the closed point. Formation of a conormal under pullback
gives
$\mathcal I_Z/\mathcal I_Z^2\simeq\mathcal O_Z$, because the conormal of $\sigma(X)$ in $P$ is
trivial. This contradicts Lemma 8.10. Hence the restriction map is injective. $\square$

**Proposition 8.12 (surface vanishing).** For a projective normal modification as above,
$R^1f_*\omega_X=0$.

**Proof.** Put $U=\operatorname{Spec}A\setminus\{\mathfrak m\}$ and
$M=H^1(X,\mathcal O_X)$. The target is normal and $f$ is a modification, so
$f_*\mathcal O_X=A$; its fibers have dimension at most one, so there is a truncation triangle

$$
A\longrightarrow Rf_*\mathcal O_X\longrightarrow M[-1]
 \xrightarrow{\delta}A[1].                                  \tag{8.8a}
$$

The module $M$ has finite length. Under the identification
$X\setminus X_s\simeq U$, the map on cohomology induced by $\delta$ is the restriction map

$$
M=H^1(X,\mathcal O_X)\longrightarrow H^1(U,\mathcal O_U).
$$

Indeed both maps are the boundary obtained by comparing the Cech complex of an affine cover of
$X$ with its restriction away from the closed fiber. Since $A$ has depth two, the local
cohomology sequence identifies $H^1(U,\mathcal O_U)$ with $H^2_{\mathfrak m}(A)$. Lemma 8.11
therefore makes

$$
M\hookrightarrow H^2_{\mathfrak m}(A)          \tag{8.8b}
$$

injective. Matlis duality and (8.7a) turn (8.8b) into a surjection
$\omega_A\twoheadrightarrow M^\vee$.

Apply $R\operatorname{Hom}_A(-,\omega_A[2])$ to (8.8a). By (8.7),
$R\operatorname{Hom}_A(M,\omega_A[2])=M^\vee$ in degree zero. The cohomology row in degrees
$-2,-1$ is consequently

$$
0\longrightarrow H^0(X,\omega_X)\longrightarrow\omega_A
 \longrightarrow M^\vee\longrightarrow H^1(X,\omega_X)
 \longrightarrow0,                                          \tag{8.8c}
$$

where (8.8) identifies the middle derived complex with $Rf_*\omega_X[2]$. The middle arrow is
the Matlis dual of (8.8b), hence is surjective. Thus
$H^1(X,\omega_X)=0$. Since the base is affine this is exactly
$R^1f_*\omega_X=0$. $\square$

#### 8.5.3 Boundedness and reduction to rational singularities

For a normal modification put $g(X)=\operatorname{length}_A H^1(X,\mathcal O_X)$. If
$X'\to X$ is another normal modification, Leray gives

$$
0\to H^1(X,\mathcal O_X)\to H^1(X',\mathcal O_{X'})
\to H^0(X,R^1g_*\mathcal O_{X'})\to0.
\tag{8.9}
$$

The last sheaf has zero-dimensional support because a birational map of surfaces has only
finitely many positive-dimensional fibers.

For boundedness it is enough to range over projective normal modifications. Indeed Chow's lemma,
followed by normalization, gives a projective normal modification dominating any given normal
modification, and the first arrow of (8.9) injects the latter's $H^1$ into the former's. The same
observation shows that vanishing tested on projective normal modifications implies vanishing for
all normal modifications. Thus every use of (8.8) and Proposition 8.12 below may, and will, be
made on a projective comparison without changing either bound or the definition of a rational
singularity.

**Lemma 8.12A (uniform divisor-torsion bound).** Let $(A,\mathfrak m)$ be a complete normal local
domain of dimension two and let $0\ne a\in A$. There is a constant $N(a)$ such that, for every
projective normal modification $X\to\operatorname{Spec}A$,

$$
\operatorname{length}_A H^1(X,\mathcal O_X)[a]\le N(a).       \tag{8.9a0}
$$

**Proof.** We first prove the elementary principal-radical fact needed below. Given finitely many
height-one primes $\mathfrak p_i$ of a normal two-dimensional local domain, there is
$c\in\bigcap\mathfrak p_i$ such that $(c)$ is radical. Start with such an $f$, write
$\operatorname{div}(f)=\sum m_j\mathfrak q_j$, and choose $g$ with $(f,g)$ primary to
$\mathfrak m$. Restrict the permitted perturbations to

$$
I=g\mathfrak m^N\cap\bigcap_i\mathfrak p_i.
$$

For every $h\in I$ one has $(f+h,g)=(f,g)$; hence the number of height-one primes dividing $f+h$
is bounded by
$\operatorname{length}A/(f,g)$ (apply the one-dimensional inequality ``number of minimal primes
$\le$ length after a parameter'' to $A/(f+h)$). Among the integers obtained as $h$ ranges through
$I$, choose a maximal one and replace $f$ by the corresponding $f+h$. Adding any further element
of $I$ cannot now increase the number of prime divisors. For each $\mathfrak q_j$, prime avoidance
chooses $b_j\in\mathfrak q_j\setminus\mathfrak q_j^{(2)}$ avoiding the other $\mathfrak q_l$.
$g$ avoids every $\mathfrak q_j$. Hence $g$ times the product of $b_j^2$ for $m_j=1$ and $b_j$
for $m_j>1$, multiplied by a sufficiently high-order element avoiding all $\mathfrak q_j$, is a
permitted perturbation $h\in I$. Then every old prime occurs in
$\operatorname{div}(f+h)$ with coefficient one; maximality leaves no new prime. Thus $(f+h)$ is
radical. Applied to the primes in $\operatorname{div}(a)$ this gives $c$ with $A/cA$ reduced and
$a\mid c^n$ for $n$ at least their largest multiplicity, because the divisor criterion for a
normal domain gives $c^n/a\in A$.

It is therefore enough to prove the bound when $A/aA$ is reduced. Indeed
$H^1(\mathcal O_X)[a]\subset H^1(\mathcal O_X)[c^n]$, and the exact sequences

$$
0\longrightarrow M[c^j]\longrightarrow M[c^{j+1}]
 \xrightarrow{c^j}M[c]
$$

propagate a bound for $c$ to one for $c^n$.

Let $Z\subset X$ be cut out by $a$. From
$0\to\mathcal O_X\xrightarrow a\mathcal O_X\to\mathcal O_Z\to0$ and
$H^0(X,\mathcal O_X)=A$ we obtain

$$
H^1(X,\mathcal O_X)[a]=\operatorname{coker}(A/aA\to H^0(Z,\mathcal O_Z)). \tag{8.9a1}
$$

Let $Z'$ be the closure in $Z$ of its restriction over the punctured spectrum. It is proper and
quasi-finite over $\operatorname{Spec}(A/aA)$, hence finite, say $Z'=\operatorname{Spec}B'$.
By the last sentence of Theorem 3.2(2) the complete ring $A$ is Nagata. Thus the reduced ring $A/aA$ embeds in its finite
normalization $B$, and
$A/aA\subset B'\subset B$. The restriction $H^0(Z,\mathcal O_Z)\to B'$ is injective: a section
in its kernel has boundary class in $H^1(X,\mathcal O_X)$ restricting to zero off the closed
fiber, hence zero by Lemma 8.11; it comes from $A$, and its image in the total quotient ring of
the reduced ring $A/aA$ is zero. Thus (8.9a1) embeds in the fixed finite-length module
$B/(A/aA)$; this quotient has finite length because normalization is already equality at the
generic points of the one-dimensional reduced local ring. Its length is the required bound.
$\square$

Let $R$ be a complete regular local ring of dimension two, let $K$ be its fraction field, let
$L/K$ be finite, and let $B$ be the integral closure of $R$ in $L$. Fix a nonzero
$K$-linear map $T:L\to K$. Choose a generator identifying $\omega_R$ with $R$, and use its
canonical transforms as fractional ideals on every regular modification of $R$. Put

$$
C=\{z\in L:T(zB)\subseteq\omega_R\}.
$$

This is a finite rank-one reflexive $B$-module. Trace adjunction identifies it with
$\operatorname{Hom}_R(B,\omega_R)=\omega_B$.

**Lemma 8.13 (the canonical lattice measures $H^1$).** Let $X\to\operatorname{Spec}R$ be an
iterated blowup at closed points and let $\bar X$ be its normalization in $L$. Under the generic
identification above, set

$$
C_{\bar X}=H^0(\bar X,\omega_{\bar X})\subseteq C.
$$

Then $C/C_{\bar X}$ is Matlis dual to $H^1(\bar X,\mathcal O_{\bar X})$. Moreover every normal
modification of $\operatorname{Spec}B$ is dominated by some such $\bar X$.

**Proof.** Proposition 8.12 and (8.8), applied to $\bar X\to\operatorname{Spec}B$, turn the
triangle

$$
B\longrightarrow Rf_*\mathcal O_{\bar X}\longrightarrow
H^1(\bar X,\mathcal O_{\bar X})[-1]
$$

into the exact sequence

$$
0\longrightarrow C_{\bar X}\longrightarrow C\longrightarrow
H^1(\bar X,\mathcal O_{\bar X})^\vee\longrightarrow0.          \tag{8.9a}
$$

The domination assertion is exactly Lemma 8.8B. $\square$

**Lemma 8.14 (boundedness under the two elementary field steps).** The ring $B$ is bounded if
$L/K$ is separable. It is also bounded when $R=k[[u,v]]$ has characteristic $p$ and $L/K$ is
purely inseparable of degree $p$.

**Proof.** It suffices, by Lemma 8.13 and (8.9), to bound the normalizations $\bar X$ of iterated
point blowups of $R$.

Suppose first that $L/K$ is separable. Choose a $K$-basis $e_1,\ldots,e_n$ contained in $B$ and
put $d=\det(\operatorname{Tr}_{L/K}(e_ie_j))\ne0$. For the finite map
$\pi:\bar X\to X$, integrality of ordinary trace over the normal ring $\mathcal O_X$ gives an
injection

$$
\Phi:\pi_*\mathcal O_{\bar X}\longrightarrow\mathcal O_X^n,\qquad
s\longmapsto(\operatorname{Tr}(e_1s),\ldots,\operatorname{Tr}(e_ns)).
$$

The map $\mathcal O_X^n\to\pi_*\mathcal O_{\bar X}$ sending $(a_i)$ to $\sum a_ie_i$ composes
with $\Phi$ to the trace matrix. Its adjugate shows that $\operatorname{coker}\Phi$ is killed by
$d$. Since an iterated point blowup of the regular ring $R$ has zero $H^1$ by Lemma 8.7 and
Leray, the cohomology sequence shows that $H^1(\bar X,\mathcal O_{\bar X})$ is killed by $d$.
Lemma 8.12A, applied to the normal Nagata ring $B$ and the element $d$, bounds its length
uniformly.

Now suppose $L/K$ is purely inseparable of degree $p$. After multiplying a primitive element by
a denominator, choose $g\in B$ with $L=K(g)$ and $g^p=f\in R$. Lemma 8.3 permits a coefficient
subfield $k_0$ for which $df\ne0$ in $Q(K/k_0)$. Extend $df$ to a basis and clear one common
denominator to obtain $\eta\in Q^{r-1}(R/k_0)$ with
$0\ne\theta=\eta\wedge df\in Q^r(R/k_0)=\omega_R$. Put

$$
\alpha_i=\eta\wedge g^{p-1-i}dg\in Q^r(B/k_0),\qquad 0\le i<p.
$$

Formula (8.3a) gives

$$
\tau(g^j\alpha_i)=\delta_{ij}\,\theta\qquad(0\le i,j<p).       \tag{8.9b}
$$

Thus differential trace and finite duality define a generically surjective map

$$
c:Q^r(B/k_0)\longrightarrow
\operatorname{Hom}_R(B,\omega_R)=\omega_B.
$$

Its cokernel is a finite torsion $B$-module and is therefore killed by one nonzero $d\in B$;
(8.9b) proves generic surjectivity without using ordinary field trace, which is zero here.
For every $X$, Lemma 8.5 followed by Lemma 8.5A gives a trace
$\pi_*Q^r(\bar X/k_0)\to\omega_X$. Finite duality adjoints it to
$Q^r(\bar X/k_0)\to\omega_{\bar X}$, compatibly with $c$. The global forms pulled back from $B$
show that the image of $H^0(\bar X,\omega_{\bar X})\to\omega_B$ contains $\operatorname{im}c$.
Consequently its cokernel, and by (8.9a) the Matlis dual of
$H^1(\bar X,\mathcal O_{\bar X})$, is killed by $d$. Matlis duality preserves annihilators, and
Lemma 8.12A applied to $B,d$ supplies the uniform length bound. $\square$

Call a normal two-dimensional local ring **bounded** if its values $g(X)$ are bounded. Choose a
normal modification with maximal $g$. If $Y$ is any normal modification of the local ring at one
of its closed points, spread $Y$ to a modification of the surface and use (8.9). Maximality makes
the last term zero, so $H^1(Y,\mathcal O_Y)=0$. Such a ring is a **rational singularity**.
Conversely that vanishing is stable under normal birational localization by the same spreading
argument. Thus Lemma 8.14 supplies a normal modification all of whose singular local rings are
rational; Lemma 8.9 may then replace that modification by normalized point blowups without
losing rationality.

#### 8.5.4 Rational singularities and the Gorenstein reduction

**Lemma 8.15 (blowing up a rational singularity).** If $A$ is rational, the ordinary blowup
$X'=\operatorname{Proj}\bigoplus_{n\ge0}\mathfrak m^n$ is normal, and every local ring on it is
rational.

**Proof.** Normalize $X'$ to $\nu:X\to X'$ and put
$\mathcal I=\mathfrak m\mathcal O_X$. The fibers of this proper morphism have dimension at most
one, so the proper-curve cohomological-dimension argument of Book 9 gives
$H^2(X,\mathcal K)=0$ for every quasi-coherent $\mathcal K$. If $\mathcal F$ is a coherent
globally generated sheaf, choose an exact sequence
$0\to\mathcal K\to\mathcal O_X^r\to\mathcal F\to0$. Rationality says
$H^1(X,\mathcal O_X)=0$; the long exact sequence therefore gives
$H^1(X,\mathcal F)=0$.

Choose generators $x_0,\ldots,x_\mu$ of $\mathfrak m$. They generate
$\mathcal I=\mathfrak m\mathcal O_X$, so

$$
0\to\mathcal F\to\mathcal O_X^{\mu+1}\to\mathcal I\to0
$$

has locally free kernel of rank $\mu$. Tensoring the presentation by $\mathcal I^{n-1}$ remains
exact, since $\mathcal I$ is invertible. On the chart where $x_j$ generates $\mathcal I$, the
kernel has basis $e_i-(x_i/x_j)e_j$; after tensoring by $\mathcal I$, these are generated by the
global Koszul sections $x_je_i-x_ie_j$. Thus $\mathcal F\otimes\mathcal I$ is globally generated,
and so are $\mathcal I^n$ and $\mathcal F\otimes\mathcal I^n$ for $n\ge1$. The preceding
vanishing and the exact
sequence

$$
0\to\mathcal F\otimes\mathcal I^{n-1}
 \to(\mathcal I^{n-1})^{\mu+1}\to\mathcal I^n\to0
$$

show inductively that $H^1(X,\mathcal I^n)=0$ and that multiplication by the $x_i$ maps
$H^0(X,\mathcal I^{n-1})$ onto $H^0(X,\mathcal I^n)$. Since
$H^0(X,\mathcal I)=\mathfrak m$, this gives
$H^0(X,\mathcal I^n)=\mathfrak m^n$ for every $n$.

Here the asserted initial equality is not an assumption about normalized blowups.
Proposition 7.2A identifies $H^0(X,\mathcal I)$ with the integral closure
$\overline{\mathfrak m}$. A maximal ideal
is integrally closed: if a unit $z$ satisfied
$z^r+c_1z^{r-1}+\cdots+c_r=0$ with $c_i\in\mathfrak m^i$, reduction modulo
$\mathfrak m$ would say that the nonzero residue of $z^r$ is zero. Hence
$\overline{\mathfrak m}=\mathfrak m$.

Now $\nu$ is finite because $A$ is Nagata. If
$\mathcal O_{X'}\subsetneq\nu_*\mathcal O_X$, twisting by the very ample
$\mathcal O_{X'}(1)$ and using the associated-graded filtration produces an $n$ for which their
global sections differ. But projection formula gives

$$
H^0(X,\nu^*\mathcal O_{X'}(n))=H^0(X,\mathcal I^n)=\mathfrak m^n
 =H^0(X',\mathcal O_{X'}(n)),
$$

a contradiction. Thus $X'=X$ is normal.

It remains to check rationality locally rather than assert its locality. Let $x\in X$ and let
$V\to\operatorname{Spec}\mathcal O_{X,x}$ be a projective normal modification. Its finitely many
equations and denominators spread over an affine neighborhood $W$ of $x$. Take the closure of its
graph over $X$ and normalize; this gives a projective normal modification $g:Z\to X$ whose
localization at $x$ dominates $V$. Both $X$ and $Z$ are normal modifications of
$\operatorname{Spec}A$, so rationality of $A$ gives

$$
H^1(X,\mathcal O_X)=H^1(Z,\mathcal O_Z)=0.
$$

Their second cohomology vanishes by the preceding fiber-dimension argument. Leray therefore gives

$$
0\longrightarrow H^1(X,\mathcal O_X)\longrightarrow H^1(Z,\mathcal O_Z)
\longrightarrow H^0(X,R^1g_*\mathcal O_Z)\longrightarrow0.
$$

Thus $R^1g_*\mathcal O_Z=0$: it is supported at the finitely many closed points where $g$ is not
an isomorphism, and a nonzero coherent sheaf with zero-dimensional support has a nonzero global
section. After localization, (8.9) injects $H^1(V,\mathcal O_V)$ into the zero stalk of this
sheaf. Chow domination and the injection (8.9) reduce an arbitrary proper normal modification to
the projective case. Hence every local ring on $X$ is rational. $\square$

An ideal in a normal domain is **complete** if it is integrally closed.

**Proposition 8.15A (complete ideals on a rational surface).** Let $A$ be a rational normal
two-dimensional local domain. A product of complete $\mathfrak m$-primary ideals is complete.
Consequently the blowup of a complete $\mathfrak m$-primary ideal is normal and has rational
local rings.

**Proof.** We first isolate the cohomological multiplication argument. Let $f:X\to\operatorname{Spec}A$
be a normal modification with $H^1(X,\mathcal O_X)=0$, and let $L,M$ be invertible sheaves
generated by finite sets of global sections. Choose evaluation sequences

$$
0\longrightarrow K_L\longrightarrow\mathcal O_X^r\longrightarrow L\longrightarrow0,
\qquad
0\longrightarrow K_M\longrightarrow\mathcal O_X^s\longrightarrow M\longrightarrow0.
$$

The maps on global sections are surjective by the choice of generators, so
$H^1(X,K_L)=H^1(X,K_M)=0$. If $K$ is the kernel of
$\mathcal O_X^{rs}\to L\otimes M$, tensoring the two presentations shows that
$K_L^s\oplus K_M^r\to K$ is surjective. Its kernel has vanishing $H^2$, as does every
quasi-coherent sheaf on a proper surface over the affine local surface whose fibers have
dimension at most one. The two long exact sequences therefore give $H^1(X,K)=0$, and hence

$$
H^0(X,L)\otimes_AH^0(X,M)\longrightarrow H^0(X,L\otimes M)    \tag{8.9c}
$$

is surjective.

Now let $I,J$ be complete and put $H=\overline{IJ}$. Take the join of the blowups of
$I,J,H$, normalize it, and use Lemma 8.9 to dominate it by normalized point blowups. Starting
from the rational ring $A$, Lemma 8.15 says inductively that these are ordinary point blowups,
that every stage is normal and rational, and that the final surface $X$ has zero $H^1$. On $X$
the three extended ideals are invertible and globally generated. Proposition 7.2A, applied
because $X$ dominates all three blowups, gives

$$
I=H^0(X,I\mathcal O_X),\qquad J=H^0(X,J\mathcal O_X),\qquad
H=H^0(X,H\mathcal O_X).                                      \tag{8.9d}
$$

Because $H$ is integral over $IJ$, the ideal $H\mathcal O_X$ is integral over the invertible
ideal $IJ\mathcal O_X$. A principal ideal in a normal domain is integrally closed, so these two
invertible ideals are equal. Applying (8.9c) and then (8.9d) gives $H=IJ$. This proves that
products of complete ideals are complete.

All powers of a complete ideal $I$ are therefore complete. The integral closure of the Rees
algebra $A[It]$ in $A[t]$ has degree-$n$ part $\overline{I^n}=I^n$; hence the Rees algebra and
its Proj are normal. Rationality of its local rings follows by the spreading-and-Leray argument
in the last paragraph of Lemma 8.15, which applies to every normal modification of $A$.
$\square$

Return to the maximal-ideal blowup of Lemma 8.15, and let $E$ be its exceptional curve. The
preceding exact sequences give

$$
H^1(E,\mathcal O_E(n))=0,
\quad H^0(E,\mathcal O_E(n))=\mathfrak m^n/\mathfrak m^{n+1}\quad(n\ge0).
\tag{8.10}
$$

Thus $E$ is Cohen--Macaulay, $\mathcal O_E(1)$ is very ample, and
$\deg\mathcal O_E(1)=\dim_k\mathfrak m/\mathfrak m^2-1$, which is one only in the regular case.

**Lemma 8.16 (canonical module becomes invertible).** A rational normal surface singularity with
a dualizing module is dominated by a finite sequence of blowups at singular closed points on
which the final dualizing module is invertible.

**Proof.** Surface vanishing and (8.8) identify
$H^0(X,\omega_X)\to\omega_A$ with an isomorphism. Adjunction for the exceptional Cartier curve
gives $\omega_X|_E=\omega_E(1)$. We spell out the generation step. With
$\mathcal O_X(1)=\mathfrak m\mathcal O_X=\mathcal O_X(-E)$, adjunction gives exact sequences

$$
0\longrightarrow\omega_X(n+1)\longrightarrow\omega_X(n)
 \longrightarrow\omega_E(n+1)\longrightarrow0.              \tag{8.10a}
$$

Curve duality identifies
$H^1(E,\omega_E(n+1))$ with the dual of $H^0(E,\mathcal O_E(-n-1))$, which is zero for
$n\ge0$ because $\mathcal O_E(1)$ is ample. Relative Serre vanishing starts at $n\gg0$; descending
through (8.10a) gives

$$
H^1(X,\omega_X(n))=0\qquad(n\ge0).
$$

We also need the following base-point argument, which remains valid when $E$ is reducible or
nonreduced. Generation may be checked after a faithfully flat extension to an algebraic closure.
Fix a geometric point $z$ and choose a hyperplane section
$s:\mathcal O_E\to\mathcal O_E(1)$ which vanishes at $z$ but at no generic point. Its cokernel
$Q$ has length $\deg\mathcal O_E(1)\ge2$, because every center retained below is nonregular.
Tensor with $\omega_E$ and let $F'\subseteq\omega_E(1)$ be the sum of $\omega_E$ and the
submodule generated by all global sections. In the cohomology row

$$
H^0(\omega_E(1))\longrightarrow H^0(\omega_E\otimes Q)
 \longrightarrow H^1(\omega_E)\longrightarrow H^1(\omega_E(1)),
$$

the middle space has dimension at least two, the next has dimension one, and the final space is
zero by duality. Thus $F'/\omega_E\ne0$. Duality applied to
$0\to\omega_E\to F'\to F'/\omega_E\to0$ says either $H^1(F')=0$ or this sequence splits.
The second alternative would put a nonzero zero-dimensional submodule in the torsion-free sheaf
$\omega_E(1)$, so $H^1(F')=0$. If $F'\ne\omega_E(1)$, the nonzero zero-dimensional quotient has
a global section, while the cohomology sequence and the definition of $F'$ force its $H^0$ to be
zero. This contradiction proves that $\omega_E(1)$ is globally generated over the algebraic
closure, hence over $k$. The case $n=0$
of (8.10a), together with $H^1(X,\omega_X(1))=0$, lifts these generating sections to
$H^0(X,\omega_X)=\omega_A$. Therefore the evaluation map
$f^*\omega_A\to\omega_X$ is surjective along $E$, in particular at every singular point.

Choose a generator of the one-dimensional $K$-space $\omega_A\otimes_AK$. Torsion-freeness
embeds $\omega_A$ as a fractional ideal of $A$; after clearing one denominator it is an ordinary
ideal $I\subset A$. On $Y=\operatorname{Bl}_I A$ the image of the pullback of $\omega_A$ modulo
torsion is the tautological invertible ideal $I\mathcal O_Y$. Apply Lemma 8.9 to obtain a
sequence of normalized blowups at closed points dominating $Y$. At any rational stage the maximal
ideal of a closed point is complete; Proposition 8.15A says its ordinary blowup is already normal
and rational. Hence every normalized point blowup in this sequence is an ordinary point blowup.
Delete a blowup whose center is regular together with all of its descendants. Such a branch stays
regular, while it is disjoint from every branch ending at a singular point. The remaining
sequence therefore blows up only singular closed points.

Let $X$ be the final pruned surface. Along a chain ending at a singular point, the preceding
canonical surjections persist at every point blowup. A neighborhood of that chain is unchanged
from the unpruned surface dominating $Y$; hence there the torsion-free pullback of $\omega_A$ is
invertible and surjects onto the torsion-free rank-one module $\omega_X$.
After trivializing the source this is an ideal quotient of $\mathcal O_X$ which is generically a
unit; surjectivity forces the quotient ideal to be the whole local ring. Thus the two modules are
isomorphic. At regular points the dualizing module is already invertible. $\square$

A rational singularity with invertible dualizing module is called a **rational double point**.
The remaining tasks are now sharply delimited: prove that successive blowups resolve rational
double points, and lift the resulting normalized-blowup sequence from the completion.

#### 8.5.5 Formal arcs and termination at double points

A **nonsingular formal arc** through $x\in X$ is a local map
$\mathcal O_{X,x}\to R$ to a complete DVR with the same residue field and surjective cotangent
map. It lifts uniquely through the blowup of $x$.

**Lemma 8.17 (arc attached to an infinite quadratic sequence).** Suppose
$(X_i,x_i)_{i\ge0}$ is an infinite sequence of point blowups, residue fields are unchanged, and
one $t\in\mathfrak m_{x_0}$ cuts out every exceptional divisor at $x_i$. Then the sequence is
the sequence of centers of a nonsingular formal arc.

**Proof.** Put
$J_n=\ker(\mathcal O_{X_0,x_0}\to\mathcal O_{X_n,x_n}/\mathfrak m_{x_n}^{n+1})$.
We prove directly that

$$
\operatorname{length}(\mathcal O_{X_0,x_0}/J_n)=n+1,
\qquad
\mathcal O_{X_0,x_0}/((t)+J_n)=k.                            \tag{8.10b}
$$

Choose generators $y_{n,j}$ of $\mathfrak m_{x_n}$. Since
$\mathfrak m_{x_n}\mathcal O_{X_{n+1},x_{n+1}}=t\mathcal O_{X_{n+1},x_{n+1}}$, write
$y_{n,j}=a_{n,j}t$. Unchanged residue fields let us subtract a lift of the residue of
$a_{n,j}$; thus

$$
\mathfrak m_{x_n}=(t,z_{n,1},\ldots,z_{n,r_n}),\qquad
z_{n,j}\in\mathfrak m_{x_{n+1}}^2.                          \tag{8.10c}
$$

Also $t^q\notin\mathfrak m_{x_n}^{q+1}$ for every $q$: otherwise on the next blowup $t^q$ would
vanish to order at least $q+1$ along the divisor which, by hypothesis, it cuts out with order
one.

Assume (8.10b) at $n$. If $f\in J_n$, expand its image modulo
$\mathfrak m_{x_n}^{n+2}$ as

$$
f=a t^{n+1}+t^nA_1(z_{n,j})+\cdots+A_{n+1}(z_{n,j}),
$$

with $A_i$ homogeneous of degree $i$. Lift the residue of $a$ back to
$\mathcal O_{X_0,x_0}$. Formula (8.10c) shows on the next chart that $f$ and $at^{n+1}$ agree
modulo $\mathfrak m_{x_{n+1}}^{n+2}$. Since
$t^{n+1}\notin\mathfrak m_{x_{n+1}}^{n+2}$, the quotient $J_n/J_{n+1}$ has length one, and the
second assertion of (8.10b) persists. Induction proves both assertions.

The inverse limit
$R=\varprojlim\mathcal O_{X_0,x_0}/J_n$ is a quotient of the maximal-adic completion and hence
is complete noetherian local. It has infinite length by (8.10b), while its maximal ideal is
generated by $t$. Therefore it is a one-dimensional regular complete local domain, hence a DVR.
The map to $R$ is local and sends $t$ to a uniformizer, so its cotangent map is surjective. The
universal property on the affine $t$-chart gives compatible local maps
$\mathcal O_{X_i,x_i}\to R$ and identifies the prescribed $x_i$ as the successive centers.
$\square$

**Lemma 8.18 (a surjective arc eventually meets the regular locus).** Let $(A,\mathfrak m)$ be a
two-dimensional noetherian local domain and let $A\twoheadrightarrow R$ be a nonsingular formal
arc, with $R$ a complete DVR. If $A_{\mathfrak p}$ is regular for
$\mathfrak p=\ker(A\to R)$, then some center of the lifted arc is regular.

**Proof.** Choose $t\in\mathfrak m$ mapping to a uniformizer and minimally generate
$\mathfrak p$ by $z_2,\ldots,z_r$. Then $\mathfrak m=(t,z_2,\ldots,z_r)$. If $r=2$, this already
makes $A$ regular. Otherwise choose $z_2$ which generates the maximal ideal of the DVR
$A_{\mathfrak p}$. The torsion $(A/\mathfrak p)$-module
$\mathfrak p/(z_2,\mathfrak p^2)$ is killed by a power of $t$. Thus, for $j>2$, there are
$n_j\ge0$ and $a_j,b_{jhl}\in A$ such that

$$
t^{n_j}z_j-a_jz_2=\sum_{2\le h\le l\le r}b_{jhl}z_hz_l.     \tag{8.10d}
$$

An index with $n_j=0$ eliminates $z_j$ from a minimal generating set of $\mathfrak p$; an
$a_j$ which is a unit eliminates $z_2$. We may consequently suppose that every $n_j>0$ and no
$a_j$ is a unit. Since $A/\mathfrak p=R$, either $a_j\in\mathfrak p$, or
$a_j\equiv u_jt^{m_j}\pmod{\mathfrak p}$ for a unit $u_j$ and an integer $m_j>0$. Absorbing the
$\mathfrak p$-part into the right side, (8.10d) therefore has one of the two forms

$$
t^{n_j}z_j=\sum b_{jhl}z_hz_l,
\qquad
t^{n_j}z_j-u_jt^{m_j}z_2=\sum b_{jhl}z_hz_l.                \tag{8.10e}
$$

The center of the arc on the blowup lies on the $t$-chart. Put $w_i=z_i/t$. Its kernel there is
generated by the $w_i$, and division of (8.10e) by $t^2$ changes every positive $n_j$ and
$m_j$ to $n_j-1$ and $m_j-1$. When one reaches zero the preceding elimination reduces the number
of generators. Induction first on $r$ and then on the sum of the positive exponents terminates
with $r=2$. At that center the maximal ideal has two generators and the two-dimensional local
ring is regular. $\square$

**Lemma 8.18A (the quadratic tangent cone).** Let $A$ be a nonregular rational double point and
let $X$ be its maximal-ideal blowup. Then $X$ is normal, its singular local rings are again
rational double points with normal completions, and the exceptional curve is a plane conic
$E=V(q)\subset\mathbf P^2_k$ for a nonzero quadratic form $q$.

**Proof.** Lemma 8.15 gives normality and rationality. Since
$\omega_A\simeq A$, the trace isomorphism and the surjection in Lemma 8.16 give
$\omega_X\simeq\mathcal O_X$ at every singular point; regular points are already Gorenstein.
Completion preserves normality here: the blowup charts are essentially of finite type over the
excellent ring $A$, so by Theorem 3.2(1) and (3) their normal local rings remain normal after the
regular completion map. Adjunction gives $\omega_E=\mathcal O_E(-1)$. With
$k=H^0(E,\mathcal O_E)$ and $g=h^1(E,\mathcal O_E)$, curve duality and Riemann--Roch give

$$
1-g=-\tfrac12\deg\omega_E=\tfrac12\deg\mathcal O_E(1).
$$

The last degree is positive, so $g=0$ and it equals two. Equations (8.10) now give
$h^0(E,\mathcal O_E(n))=2n+1$. In particular
$\dim_k\mathfrak m/\mathfrak m^2=3$ and
$\dim_k\mathfrak m^2/\mathfrak m^3=5$. For lifts $x_1,x_2,x_3$ of a cotangent basis, the six
quadratic monomials consequently satisfy one nonzero relation modulo $\mathfrak m^3$:

$$
\sum_{i\le j}a_{ij}x_ix_j=\sum_{i\le j\le l}a_{ijl}x_ix_jx_l,
\qquad (\bar a_{ij})\ne0.                                  \tag{8.11}
$$

On the $x_1$-chart, with $y_i=x_i/x_1$, division by $x_1^2$ shows that the exceptional divisor is
cut out by $q(1,y_2,y_3)$, where $q=\sum\bar a_{ij}t_it_j$. The three charts therefore identify
$E$ with $V(q)\subset\mathbf P^2_k$. $\square$

**Lemma 8.18B (quadratics in squares of point ideals).** Let $I\subset k[x,y]$ have colength
greater than one. If a nonzero polynomial $Q$ of degree at most two belongs to $I^2$, then
$Q=c(\alpha+\beta x+\gamma y)^2$.

**Proof.** Both partial derivatives of $Q$ belong to $I$. If one is nonzero, an affine linear
change makes it $x$. Then $I=(x)$ or $(x,F(y))$ with $F$ monic of degree at least two. Writing
an element of $I^2$ as $Ax^2+B(y)xF+C(y)F^2$ and comparing degrees forces $B=C=0$ and $A$ to be
constant, giving the assertion. If both derivatives vanish, the characteristic is two and,
after interchanging variables and scaling, $Q=a+dx^2+y^2$. If $a,d$ are squares we are done.
Otherwise choose a derivation $\theta:k\to k$ nonzero on $a$ or $d$ (differentiate with respect
to a member of a $2$-basis), and extend it by $\theta(x)=\theta(y)=0$. Leibniz gives
$\theta(a)+\theta(d)x^2\in I$. The case $\theta(d)=0$ would put a unit in $I$; hence
$\alpha+x^2\in I$, and then $a+\alpha d+y^2\in I$. Put
$J=(\alpha+x^2,a+\alpha d+y^2)$. These two generators freely generate $J/J^2$, whereas $Q$ is
their linear combination and lies in $I^2$; consequently $J\subsetneq I$. Thus $I$ contains a
nonzero $g+hx+iy+jxy$. If $j=0$, it contains a linear form and the first argument applies. If
$j\ne0$, absence of a linear form forces $I/J$ to be one-dimensional and

$$
I=(\alpha+x^2,\beta+y^2,g+hx+iy+jxy).
$$

After faithfully extending to an algebraic closure and translating square roots, colength three
forces the last generator to be $jxy$, so $I=(x^2,y^2,xy)$. Direct multiplication shows that no
nonzero polynomial of degree two lies in $I^2$, a contradiction. Hence the nonsquare alternative
cannot occur. $\square$

**Lemma 8.18C (singular points on the conic).** In the notation of Lemma 8.18A, call the conic
type I if $q$ is not a scalar square of a linear form and type II otherwise. On every blowup chart:

1. a singular point with residue field strictly larger than $k$ can occur only in type II;
2. in type I there is at most one singular point, it is $k$-rational, and a parameter cutting out
   the exceptional divisor remains such a parameter after blowing it up;
3. in type II, either the next singular point is of type I, or there is at most one type-II
   singular point, it is $k$-rational, and the same exceptional parameter persists.

**Proof.** On the $x_1$-chart let $p$ correspond to a maximal ideal with residue field $k'$.
Its kernel in $k[y_2,y_3]$ is generated by two polynomials $f_2,f_3$, and the maximal ideal of
the surface local ring is generated by $x_1$ and lifts of them. If the point is singular, these
three classes are independent in the cotangent space; equivalently
$q(1,y_2,y_3)\in(f_2,f_3)^2$. If $[k':k]>1$, the latter ideal has colength greater than one, so
Lemma 8.18B makes $q$ a scalar square. This proves (1), including inseparable residue extensions.

In type I, translate a singular $k$-point to $(y_2,y_3)=(0,0)$. Then
$q(1,y_2,y_3)\in(y_2,y_3)^2$, so $q=q(t_2,t_3)$. A nonsquare binary conic is either two distinct
lines through their vertex or is the cone over a degree-two point of $\mathbf P^1$; the only point
at which its local equation can lie in the square of the point ideal is the vertex. Hence there is
at most one singular point. Singularity at the vertex also makes the residue of the coefficient
$a_{111}$ of $x_1^3$ vanish. Write
$a_{111}=b_{111}x_1+b_{112}x_2+b_{113}x_3$. After substitution in (8.11), the quadratic form in
the new parameters $x_1,y_2,y_3$ is

$$
b_{111}t_1^2+a_{112}t_1t_2+a_{113}t_1t_3+q(t_2,t_3),         \tag{8.12a}
$$

with harmless changes to the three displayed mixed coefficients. Its restriction to $t_1=0$ is
the same nonsquare binary form. Thus the new point is again type I, $x_1$ cuts out the exceptional
divisor there, and it remains a good coordinate. This proves (2).

For type II choose coordinates with $q=t_3^2$. The chart equation is

$$
y_3^2=x_1\sum a_{ijl}y_iy_jy_l.                            \tag{8.12}
$$

At the generic point of the reduced line $C=(x_1,y_3)$, normality makes the local ring a DVR;
$y_3$ is a uniformizer and $x_1$ is a unit times $y_3^2$. Therefore the cubic

$$
h(y_2)=\bar a_{111}+\bar a_{112}y_2+
       \bar a_{122}y_2^2+\bar a_{222}y_2^3
$$

is nonzero. A singular point must be a zero of $h$. A simple zero gives, in local parameters
$x_1,y_3,g$, a quadratic form
$y_3^2-x_1(ux_1+vy_3+wg)$ with $w$ a unit, which is not a square and hence is type I. Since a
cubic has at most one multiple root, at most one point remains in type II, and a multiple root
is $k$-rational: a multiple closed point of degree $d$ contributes at least $2d$ to a divisor of
degree three. Translate it to the origin. The type-II condition on its new quadratic form permits
changes of $y_3$ by a linear combination of $x_1,y_2$ and gives local parameters, denoted again by
$x_1,y_2,y_3$, for which

$$
y_3^2+x_1(ay_2^2+by_2y_3+cy_3^2)\in
(x_1,y_2,y_3)^4.                                             \tag{8.12b}
$$

Here the residue of $a$ is nonzero. Indeed, if $a$ belonged to the maximal ideal, write it as
$a_1x_1+a_2y_2+a_3y_3$. On the $x_1$-chart of the next blowup put
$Y_2=y_2/x_1$ and $Y_3=y_3/x_1$ and divide (8.12b) by $x_1^2$. At the generic point of
$(x_1,Y_3)$ every term of the resulting relation lies in $(x_1,Y_3)^2$. That height-one local
ring has dimension one and embedding dimension two, contradicting the normality of the blowup
from Lemma 8.15. Thus $a$ is a unit.

On the $y_2$-chart, the quadratic form at the only point with coordinates
$x_1/y_2=y_3/y_2=0$ is $t_3^2+\bar a\,t_1t_2$, so it is type I. The $y_3$-chart contains no
point of the reduced exceptional line. Hence a type-II successor can occur only on the
$x_1$-chart, at $Y_2=Y_3=0$. Direct substitution in (8.12b), followed by the linear change which
makes its square quadratic form $Y_3^2$, gives

$$
Y_3^2+x_1(a'Y_2^2+b'Y_2Y_3+c'Y_3^2)\in
(x_1,Y_2,Y_3)^4,
$$

where $a'$ is a unit. Terms of order two and three involving only $x_1,Y_3$ are precisely those
absorbed by the square-making change; the coefficient of $x_1Y_2^2$ is unchanged modulo the
maximal ideal. Thus the same normal form recurs and $x_1$ again cuts out the exceptional divisor.
This proves (3). $\square$

**Lemma 8.18D (termination for rational double points).** Repeatedly blowing up the singular
closed points of a rational double point terminates in a regular surface.

**Proof.** Lemmas 8.15 and 8.18A show after every blowup that the surface is normal and that its
finitely many singular local rings, and their completions, are rational double points. Suppose an
infinite branch of singular centers existed. If it ever enters type I, Lemma 8.18C gives a unique
rational successor and one fixed good coordinate cutting out every later exceptional divisor. If
it remains in type II, part (3) gives the same conclusion after discarding finitely many initial
terms. Thus the residue fields are constant and Lemma 8.17 constructs a nonsingular formal arc
whose centers are precisely this branch. The resulting map from the first local ring extends to a
surjection from its completion onto the complete DVR constructed in Lemma 8.17. Ordinary blowup
commutes with this flat base change, so the same centers define the lifted quadratic sequence over
the completion. That completion is normal by Lemma 8.18A; hence the localization at the height-one
kernel of the surjective arc is a DVR. Lemma 8.18 says that a later completed local ring is regular.
Completion preserves dimension and cotangent space (the standing completion fact in Section 8.2),
so the corresponding uncompleted center is regular, a contradiction.
The singular locus at every stage is finite, so the finitely branching tree of singular centers
has no infinite branch and is finite. Blowing up its terminal generation resolves the surface.
$\square$

#### 8.5.6 Completion and lifting

**Lemma 8.19 (completion comparison).** If $X$ is finite type over a noetherian local $A$, then
local rings at corresponding closed-fiber points of $X$ and $X_{\widehat A}$ have isomorphic
completions. Consequently a proper $X$ is regular exactly when $X_{\widehat A}$ is regular.

**Proof.** Modulo $\mathfrak m^n$, $A$ and $\widehat A$ agree. Localizing and then quotienting
by powers of the corresponding prime gives identical inverse systems. Regularity is equivalent
to regularity of the completion, and proper schemes have all closed points over the closed point.
$\square$

**Lemma 8.20 (normalization and lifting normalized blowups).** Let $(A,\mathfrak m)$ be an
excellent local ring and let $X$ be locally of finite type over $A$. Put
$Y=X\times_A\widehat A$. Then finite normalization commutes with this base change:

$$
(X^\nu)\times_A\widehat A\simeq Y^\nu.                     \tag{8.13}
$$

Consequently, if $A$ is a domain with normal completion, every finite sequence of normalized
blowups in ideals supported at closed-fiber points over $\widehat A$ is the base change of such a
sequence over $A$.

**Proof.** Excellence makes the normalization $X^\nu\to X$ finite, by Theorem 3.2(1) and (2). It
also says that $A\to\widehat A$ is regular: it is flat and its geometric fibers are regular, by
Theorem 3.2(3). Regularity is
preserved by base change, so

$$
(X^\nu)\times_A\widehat A\longrightarrow X^\nu
$$

is regular. The source of a regular morphism with normal target is normal. This follows directly
from Serre's criterion: flatness and the depth inequality preserve $(S_2)$, while a
codimension-one local ring of the source is regular from the dimension formula and regularity of
the corresponding base local ring and geometric fiber. Thus the left side of (8.13) is normal.
It is finite and birational over $Y$, because these properties survive flat base change.
The universal property of normalization gives (8.13), component by component.

We now descend a whole sequence, not merely its first center. Suppose a stage
$Y_i=X_i\times_A\widehat A$ has already been obtained by base change and let
$J_i\subset\mathcal O_{Y_i}$ be the next coherent center, supported at finitely many points of
the closed fiber. Affine-locally its quotient is killed by a power $\mathfrak m^r$, so
$J_i$ contains $\mathfrak m^r\mathcal O_{Y_i}$. Since

$$
\mathcal O_{X_i}/\mathfrak m^r\mathcal O_{X_i}
\simeq
\mathcal O_{Y_i}/\mathfrak m^r\mathcal O_{Y_i},
$$

$J_i/\mathfrak m^r\mathcal O_{Y_i}$ has a unique inverse-image ideal
$I_i\subset\mathcal O_{X_i}$. These affine inverse images agree on overlaps, so $I_i$ is coherent
and $J_i=I_i\mathcal O_{Y_i}$. Flat base change identifies the Rees algebras and hence the
ordinary blowups. Formula (8.13) identifies their normalizations. This constructs $X_{i+1}$ and
proves the induction. Every descended center is supported on the corresponding finite set of
closed-fiber points because that can be checked after faithful flat base change. $\square$

**Lemma 8.20A (realizing a resolution by normalized blowups).** Let $A$ be a complete
two-dimensional normal noetherian local domain and let
$X\to\operatorname{Spec}A$ be a resolution. There is a regular $X'$ and a factorization

$$
X'\longrightarrow X\longrightarrow\operatorname{Spec}A
$$

such that $X'\to\operatorname{Spec}A$ is a finite sequence of normalized blowups at closed
points.

**Proof.** We first record two rationality facts used in the conversion. A complete regular
two-dimensional local ring $R$ is rational. Indeed, given a normal modification $W\to
\operatorname{Spec}R$, Chow's lemma supplies a projective modification dominating it, and
Corollary 8.8A dominates that projective modification by a sequence
$T_r\to\cdots\to T_0$ of point
blowups of the regular surface. Lemma 8.7 and Leray give
$H^1(T_r,\mathcal O_{T_r})=0$, while (8.9) injects
$H^1(W,\mathcal O_W)$ into this group.

Rationality also passes to a normal two-dimensional local ring $B$ essentially of finite type and
birational over $R$. To see this without a locality assumption on rationality, choose a normal
projective modification $P\to\operatorname{Spec}R$ having a closed point $b$ with
$\mathcal O_{P,b}=B$: take a projective closure of the finite-type birational model containing
$\operatorname{Spec}B$, then normalize it. Let
$V\to\operatorname{Spec}B$ be a normal modification. After replacing $P$ by an open
neighborhood of $b$, finitely many affine equations and denominators defining $V$ spread it to a
modification of that neighborhood. Taking its graph closure over $P$ and normalizing gives
$g:P'\to P$ whose base change at $b$ dominates $V$. Both $P$ and $P'$ are normal modifications
of $R$, so the first paragraph gives

$$
H^1(P,\mathcal O_P)=H^1(P',\mathcal O_{P'})=0.
$$

The fibers of $P$ and $P'$ over the affine surface $\operatorname{Spec}R$ have dimension at most
one, so their second coherent cohomology vanishes. Leray for $g$ therefore gives the exact row

$$
0\longrightarrow H^1(P,\mathcal O_P)\longrightarrow
H^1(P',\mathcal O_{P'})\longrightarrow
H^0(P,R^1g_*\mathcal O_{P'})\longrightarrow0.
$$

Thus $R^1g_*\mathcal O_{P'}=0$: it is supported at the finitely many closed points where $g$ is
not an isomorphism, and a nonzero coherent module with zero-dimensional support has a nonzero
global section. Its stalk at $b$ is the $H^1$ of the localized modification; applying (8.9) to
the domination of $V$ injects $H^1(V,\mathcal O_V)$ into that zero stalk. Hence $B$ is rational.

Now let $X\to\operatorname{Spec}A$ be a regular resolution. Lemma 8.9 supplies a sequence of
normalized blowups

$$
Y_n\longrightarrow\cdots\longrightarrow Y_0=\operatorname{Spec}A
$$

and a morphism $Y_n\to X$. Chow's lemma gives a projective modification of $X$ dominating
$Y_n$, and Corollary 8.8A, applied over the regular $X$, gives a sequence of point blowups of $X$
dominating $Y_n$. (Equivalently, $Y_n\to X$ itself is projective: $Y_n$ is projective over
$A$, and its graph is closed because $X$ is separated over $A$.) Hence $Y_n$ has a resolution
and only finitely many singular closed points. If $y\in Y_n$ is one of them and
$x\in X$ is its image, the local map
$\mathcal O_{X,x}\to\mathcal O_{Y_n,y}$ is birational and essentially of finite type. The two
rationality facts show that $\mathcal O_{Y_n,y}$ is a rational singularity.

Apply Lemma 8.16 at the finitely many $y$. The local point-blowup sequences globalize because
their centers are disjoint closed points; Lemma 8.15 says every stage is normal and rational.
After finitely many stages all remaining singular local rings are Gorenstein, hence rational
double points. Lemma 8.18D resolves each of those by finitely many further singular-point
blowups. Again Lemma 8.15 makes every ordinary blowup normal, so each is already its normalized
blowup. Appending these stages to $Y_n\to\cdots\to Y_0$ produces a sequence of normalized
blowups whose final surface is regular. Every appended stage maps to $Y_n$, and the original
map $Y_n\to X$ therefore makes the final resolution dominate the prescribed $X$. $\square$

**Proposition 8.21 (complete local resolution).** A complete two-dimensional normal noetherian
local domain admits a resolution by normalized blowups.

**Proof.** We first construct the finite regular subring; this is Book 1, Theorem 13.34, in the
two-dimensional case. In equal characteristic $A$ contains a field, so Book 1, Theorem 13.15
supplies a coefficient field $K_A\subseteq A$ mapping isomorphically onto $k$. Choose a
parameter ideal $(x,y)$, so that $A/(x,y)$ has finite length. Book 1, Theorem 13.34(1) then makes
$A$ a finite module over $A_0=K_A[[x,y]]\cong k[[x,y]]$, and its closing clause makes
$A_0\to A$ injective, since $A$ is a domain and $\dim A_0=2=\dim A$ by Book 1, Lemma 13.29. In
mixed characteristic Book 1, Theorem 13.21 supplies a Cohen ring $C$ for $k$ and Book 1,
Theorem 13.25 a local homomorphism $C\to A$ inducing the identity on residue fields; choose $x$
so that $(p,x)$ is a parameter ideal and put $A_0=C[[x]]$. Book 1, Theorem 13.34(2) makes $A$ a
finite $A_0$-module, and again $\dim A_0=2=\dim A$ by Book 1, Lemma 13.29 forces injectivity.
Thus in both cases $A_0$ is a complete regular local domain of dimension two, by Book 1,
Lemma 13.29, and $K/K_0=\operatorname{Frac}(A)/\operatorname{Frac}(A_0)$ is finite.

The first paragraph of Lemma 8.20A proves more than regularity of $A_0$: every normal modification
of $A_0$ has zero $H^1$. Thus $A_0$ is rational. The finite extension
$A_0\subset A$ is exactly the setting of Lemma 8.14.

Induct on $[K:K_0]$ to construct some resolution. Degree one gives $A=A_0$. If
$K_0\subsetneq L\subsetneq K$, let $B$ be the integral closure of $A_0$ in $L$; it is finite and
local because $A_0$ is complete and hence henselian, and it is complete as a finite
$A_0$-module. By induction resolve it, obtaining
$Y\to\operatorname{Spec}B$. Normalize $Y\times_BA$ and examine its finitely many singular closed
points. Their completed local rings are complete normal surface rings, finite over the completed
regular local rings of $Y$. The remaining field degree is smaller, so induction resolves each;
Lemma 8.20 and the local-to-global construction lift and glue these resolutions. Lemma 8.20A
then converts the resulting resolution to normalized blowups. We may therefore assume there is no
intermediate field.

Such an extension is either separable, or has characteristic $p$ and is purely inseparable of
degree $p$. In mixed characteristic only the first case occurs. Lemma 8.14 gives boundedness in
both cases. Choose a normal modification on which $g$ is maximal. Equation (8.9) then makes
every singular local ring rational. Lemma 8.16 replaces it by a normal modification whose
singular local rings are rational double points, and Lemma 8.18D resolves those by finitely many
point blowups. This produces a resolution, and
Lemma 8.20A realizes it as a finite sequence of normalized blowups. $\square$

### 8.6 Why a three-entry local invariant is insufficient

The proof above avoids a tempting but invalid shortcut. For every
singular excellent normal two-dimensional local domain $(A,\mathfrak m)$, one must construct a
projective birational modification supported at $\mathfrak m$ whose local rings are all regular.
Doing this compatibly with the regular punctured spectrum, and then showing that the construction
terminates after finitely many stages, is the local core of Theorem 8.1.

Hilbert--Samuel multiplicity, the tangent cone and its directrix, coefficient ideals, and conductor
lengths of suitable curve sections are useful ingredients in proofs of this local theorem. They do
not yield a proof merely by being placed in a lexicographically ordered tuple. Such an argument must
establish all of the following points:

1. the coefficient ideal is intrinsically defined enough to transform under the chosen blowup;
2. a suitable hypersurface section exists over the actual residue field, including when that field
   is finite, and the invariant is independent of every auxiliary extension used to choose it;
3. equality of multiplicities forces the asserted directrix drop on every relevant chart;
4. in the remaining case, conductor length strictly decreases on every unresolved branch;
5. the inequalities hold simultaneously at every nonregular point of the normalized blowup; and
6. passage to completion and approximation back to $A$ preserve the center, its transform, and all
   strict inequalities.

None of these assertions is supplied by upper semicontinuity alone. In particular, independently
choosing a general section after passing to an unramified residue-field extension does not produce
a descended center, and decreasing the value semigroup on one branch does not control all points of
a normalized blowup. Accordingly the proof uses boundedness, rational singularities, formal arcs,
and completion lifting instead of the former unsupported ``surface decrease lemma.''

### 8.7 Termination

**Proof of Theorem 8.1.** Apply Lemma 8.2. At each of the finitely many singular points of the
normalization, excellence makes the completed local ring normal. Proposition 8.21 resolves that
completion by normalized blowups, and Lemma 8.20 lifts the finite sequence to the original local
ring. Lemma 8.19 reflects regularity. The local-to-global equivalence for modifications supported
at finitely many closed points glues these sequences with the identity on $U$. Each blowup is
projective and each normalization is finite, so their finite composite is projective and
birational. The resulting scheme is regular and unchanged over $U$. $\square$

### 8.8 Examples of the local procedure

The following calculations illustrate the general theorem in explicit equations.

Consider

$$
X_n=\operatorname{Spec}R[x,y]/(xy-\pi^n),\qquad n\geq2.
$$

Blow up the ideal $(x,\pi)$. Away from the singular point it is already invertible, so the modification is locally supported where needed. On the chart where $x$ generates the transformed ideal, write $\pi=xt$. Removing the common factor from $xy-\pi^n$ leaves

$$
y=x^{n-1}t^n,
$$

together with $\pi=xt$; this chart is regular. On the chart where $\pi$ generates, write $x=\pi s$. The strict transform has equation

$$
sy=\pi^{n-1}.
$$

Thus the only unresolved chart has the same form with exponent smaller by one. Induction ends at
$xy=\pi$, which is regular. Proposition 4.1A makes each member Cohen--Macaulay because it is a
hypersurface; its Jacobian singular locus is the closed point and therefore has codimension two,
so $(R_1)$ and Theorem 4.1 give normality. Normalization cannot simplify $X_n$, and blowing up is
the required repair. Globally the exceptional locus is a chain of rational curves. Its numerical
intersection data is not needed for termination of this local exponent reduction.

For the cone $xy=z^2$, blowing up $(x,y,z)$ gives on the $x$-chart

$$
x^2(y_1-z_1^2)=0.
$$

Removing the exceptional factor leaves $y_1=z_1^2$, a smooth chart. The other charts are similar. One blowup resolves the vertex.

A cusp requires more than branch separation. Normalizing $k[t^2,t^3]$ resolves the one-dimensional cusp immediately, but the arithmetic surface equation $y^2=x^3+\pi^m$ can remain a normal surface singularity. Blowups change both the plane-curve singularity and the vertical exponent. Proving that the alternating phenomena terminate in arbitrary excellent surface singularities is part of Theorem 8.1; the preceding examples do not supply that proof.

## 9. Regular proper models

### 9.1 Existence over excellent Dedekind bases

Combining the proved closure and normalization constructions with Theorem 8.1 gives the main
existence theorem.

**Theorem 9.1 (regular model theorem).** Let $S$ be an excellent Dedekind scheme with function field $K$, and let $C/K$ be a smooth projective geometrically connected curve. Then there exists a regular flat projective $S$-scheme $\mathcal X$ with generic fiber $C$. If a regular projective model is prescribed over a nonempty open $U\subset S$, $\mathcal X$ may be chosen to restrict to it.

**Proof.** If no model over $U$ is prescribed, embed $C$ in projective space and take its schematic closure. In the relative case, use the compatible embedding and closure constructed in Theorem 6.2. Normalize the closure to obtain a normal flat projective model $X_1$ which is unchanged over $U$. Its generic fiber, and its restriction to $U$ in the relative case, are regular. Apply Theorem 8.1 to $X_1$ with the regular open consisting of its generic fiber together with $X_{1,U}$. The result is regular and projective and has unchanged generic fiber and unchanged restriction over $U$. It remains flat because it is integral and dominates the Dedekind base. $\square$

If $C$ is merely proper, it is projective because every smooth proper curve over a field possesses a divisor of positive degree and a sufficiently large multiple is very ample. Thus no separate proper-only case is needed for smooth curves.

### 9.2 Keeping a prescribed good open

Arithmetic applications usually begin with a moduli construction that is already smooth over $S[1/N]$. The theorem must not replace that meaningful open part by an unrelated isomorphic model. The relative clause ensures exact preservation.

More explicitly, let $\mathcal U\to U$ be a smooth projective curve with generic fiber $C$. Choose a relatively very ample power of an ample bundle on $\mathcal U$ and embed it in $\mathbf P^N_U$. After multiplying finitely many transition functions by elements of $K^\times$, extend the equations to $S$. The closure restricts to $\mathcal U$ because schematic closure commutes with restriction to $U$. Normalization and resolution are isomorphisms there because $\mathcal U$ is regular and normal.

The bad set $S\setminus U$ is finite when $S$ is the spectrum of a Dedekind domain and $U$ is nonempty affine after harmless shrinking. Every modification is then vertical above those finitely many primes.

### 9.3 Dominating finitely many models

**Theorem 9.2.** Let $S$ be an excellent Dedekind scheme. Any finite collection of projective $S$-models of the same smooth curve is dominated by a regular projective model.

**Proof.** The fiber product of finitely many projective $S$-schemes is projective. Take in that product the schematic closure $Z$ of the diagonally embedded generic curve. It is integral, flat, and projective by Proposition 6.1, and every projection $Z\to X_i$ is proper and induces the identity on the generic fiber. Normalize $Z$ and apply Theorem 8.1 to the resulting normal surface. Both operations are projective and preserve the generic fiber. The final regular projective model maps to every $X_i$ and induces the identity on $C$. $\square$

This is the correct way to compare equations, moduli compactifications, and models adapted to correspondences. One does not identify them prematurely; one moves to a common regular domination.

### 9.4 Sections and closures of points

Let $P\in C(K)$. Properness extends the map $\eta\to\mathcal X$ uniquely to a section $S\to\mathcal X$ when $S$ is normal. Existence follows from the valuative criterion at each discrete valuation ring $\mathcal O_{S,s}$, and uniqueness from separatedness; the local extensions glue.

More generally, for a closed point $P$ of $C$ with residue field $L$, let $S_L$ be the normalization of $S$ in $L$. It is finite over $S$. Properness extends the $L$-point to a section over $S_L$, and its image in $\mathcal X$ is the horizontal closure of $P$. That closure need not be regular before normalization; its normalization is $S_L$.

A section of a regular arithmetic surface is a Cartier divisor. At a point of the section, the local ring has dimension two and the section is cut out by one parameter transverse to the base direction; that a single equation suffices is the factoriality of regular local rings, Theorem 14.43 combined with Theorem 14.38. This fact later makes marked points compatible with blowups and semistable models.

## 10. Finite extensions and base change

### 10.1 Integral closure of the base

Let $K'/K$ be a finite field extension and let $S'$ be the normalization of $S$ in $K'$. When $S$ is an excellent Dedekind scheme, $S'\to S$ is finite by Theorem 3.3, and $S'$ is again an excellent Dedekind scheme: it is finite over $S$, and Theorem 3.2(1) makes a finite algebra over an excellent ring excellent. More generally, normalizing in a finite reduced $K$-algebra gives the finite disjoint union belonging to its field factors. Locally at $s\in S$, the points of $S'$ correspond to extensions of the associated discrete valuation, exactly as in Book 1.

Given a model $X/S$, form $X_{S'}=X\times_SS'$. It is proper or projective when $X$ is, and flat when $X$ is flat because flatness survives base change. It may fail to be integral, reduced, normal, or regular. The generic fiber is $C\times_KK'$, which can itself split unless $C$ is geometrically integral.

### 10.2 Base change can destroy normality

Normality is not stable under arbitrary base change. Over an imperfect field $k$ of characteristic $p$, choose $a\notin k^p$. The field

$$
L=k[u]/(u^p-a)
$$

is normal as a zero-dimensional $k$-scheme. After base change to $k'=k(a^{1/p})$,

$$
L\otimes_kk'\simeq k'[u]/(u-a^{1/p})^p
$$

is nonreduced and therefore not normal. Even a finite purely inseparable extension can thus destroy normality.

Regularity also fails under arbitrary field extension for the same reason. **Geometric regularity** is the stable notion: a finite-type $k$-scheme is geometrically regular if every finite field extension produces a regular base change. Smoothness over $k$ is equivalent to geometric regularity for finite-type schemes.

By contrast, normalization commutes with smooth base change. Étale localization is the most frequently used case. On rings, a smooth algebra has geometrically regular fibers, and an integrally closed base remains integrally closed after smooth extension on each component. The universal property then identifies the pulled-back normalization with the new normalization.

### 10.3 The normalize-after-base-change rule

The safe operation after a finite extension is

$$
X'=\operatorname{Nor}\bigl((X\times_SS')_{\mathrm{red}}\bigr),
$$

taking the component or components with the desired generic fiber. Since $S'$ is excellent, Theorem 3.3 makes $X'\to X\times_SS'$ finite. If $X$ was proper or projective, so is $X'$. One then resolves $X'$ if a regular model is required.

There is a canonical comparison from the normalization after base change to the base change of the original normalization whenever the latter is interpreted componentwise and is dominated by the former. It is an isomorphism under smooth base change, and also under separable field extension when geometric normality supplies normality of the base-changed space. Without such a hypothesis, it need not be.

Say that a finite-type $K$-scheme $X$ is **geometrically normal** if $X_{K_1}$ is normal for
every finite extension $K_1/K$; by the argument below it is enough to test finite _purely
inseparable_ extensions, and in characteristic zero the condition is just normality of $X$. The
point of the definition is that this finite amount of testing already controls every extension,
however large.

**Proposition 10.1.** Let $X$ be a geometrically normal finite-type $K$-scheme and $K'/K$ a field extension. Then $X_{K'}$ is normal. If $X$ is a smooth curve, this applies automatically.

**Proof.** The question is local, so let $X=\operatorname{Spec}A$ with $A$ a finite-type
$K$-algebra; all the rings below are of finite type over a field and hence noetherian, so
Serre's criterion, Theorem 14.26, is available: normality means $(R_1)$ and $(S_2)$. We use
repeatedly the flat local dimension and depth formulas: for a flat local homomorphism
$(R,\mathfrak m)\to(T,\mathfrak n)$ of noetherian local rings with closed fiber
$\bar T=T/\mathfrak mT$,

$$
\dim T=\dim R+\dim\bar T,
\qquad
\operatorname{depth}T=\operatorname{depth}R+\operatorname{depth}\bar T.
\tag{10.1a}
$$

_Step 1: descending along a larger field._ Let $\Omega$ be an algebraically closed field
containing $K'$. We claim that normality of $D=A\otimes_K\Omega$ forces normality of
$C=A\otimes_KK'$. The map $C\to D$ is faithfully flat, being obtained from $K'\to\Omega$ by base
change. Let $\mathfrak q$ be a prime of $C$ and choose a prime $\mathfrak Q$ of $D$ minimal over
$\mathfrak qD$; such a prime lies over $\mathfrak q$ by faithful flatness. The induced map
$C_{\mathfrak q}\to D_{\mathfrak Q}$ is faithfully flat and local, and its closed fibre
$D_{\mathfrak Q}/\mathfrak qD_{\mathfrak Q}$ is a local ring whose maximal ideal is nilpotent, so
that fibre has dimension and depth zero. By (10.1a),

$$
\dim C_{\mathfrak q}=\dim D_{\mathfrak Q},
\qquad
\operatorname{depth}C_{\mathfrak q}=\operatorname{depth}D_{\mathfrak Q}.
$$

Hence $(S_2)$ for $D$ gives $(S_2)$ for $C$. For $(R_1)$, suppose $\dim C_{\mathfrak q}\le1$;
then $\dim D_{\mathfrak Q}\le1$, so $D_{\mathfrak Q}$ is regular. Take a minimal free resolution
$F_\bullet$ of the residue field $\kappa(\mathfrak q)$ over $C_{\mathfrak q}$. Flatness makes
$F_\bullet\otimes_{C_{\mathfrak q}}D_{\mathfrak Q}$ a free resolution of
$D_{\mathfrak Q}/\mathfrak qD_{\mathfrak Q}$, and its differentials still have entries in the
maximal ideal, so it is a minimal free resolution and therefore has length
$\operatorname{pd}_{D_{\mathfrak Q}}(D_{\mathfrak Q}/\mathfrak qD_{\mathfrak Q})$, which is
finite by Theorem 14.34. So $F_\bullet$ is finite, $\operatorname{pd}_{C_{\mathfrak q}}\kappa(\mathfrak q)<\infty$,
and $C_{\mathfrak q}$ is regular by Theorem 14.36. Thus we may assume $K'=\Omega$ is
algebraically closed.

_Step 2: the purely inseparable part._ Let $K^{\mathrm i}\subseteq\Omega$ be the purely
inseparable closure of $K$, that is, $K$ itself in characteristic zero and
$\{c\in\Omega:c^{p^n}\in K\text{ for some }n\}$ in characteristic $p$. It is a perfect field, it
is the union of its finite subextensions $K_1/K$, and each such $K_1$ is purely inseparable over
$K$. Put $B=A\otimes_KK^{\mathrm i}$ and $B_1=A\otimes_KK_1$, so that $B=\varinjlim B_1$ is a
filtered colimit with faithfully flat transition maps, each $B_1$ normal by hypothesis, and $B$
noetherian because it is of finite type over $K^{\mathrm i}$.

We check that $B$ is normal. It is reduced, since a nilpotent element of $B$ already lies in
some $B_1$. A reduced noetherian ring that is integrally closed in its total ring of fractions
is normal: the total ring of fractions is the product of the residue fields at the minimal
primes, its idempotents are integral over the ring, hence lie in it, and the ring is
correspondingly a finite product of domains integrally closed in their fraction fields. So let
$z$ lie in the total ring of fractions of $B$ and be integral over $B$, say $z=u/s$ with
$u,s\in B$ and $s$ a nonzerodivisor, and let an integral equation for $z$ have coefficients
$b_1,\ldots,b_n\in B$. Choose $K_1$ large enough that $u,s,b_1,\ldots,b_n$ all lie in $B_1$.
Multiplication by $s$ is injective on $B$, and $B_1\to B$ is faithfully flat, so multiplication
by $s$ is injective on $B_1$ as well; thus $z$ lies in the total ring of fractions of $B_1$ and
is integral over $B_1$, whence $z\in B_1\subseteq B$. So $B$ is normal.

_Step 3: extensions of a perfect field._ It remains to prove that
$B\otimes_{K^{\mathrm i}}\Omega=A\otimes_K\Omega$ is normal, where $B$ is a normal finite-type algebra over the perfect field
$F=K^{\mathrm i}$ and $\Omega\supseteq F$ is arbitrary. Write $C=B\otimes_F\Omega$, again
noetherian. First, every fibre of $B\to C$ is regular. Indeed, for a prime $\mathfrak q$ of $B$
the field $\kappa(\mathfrak q)$ is a finitely generated extension of the perfect field $F$,
hence separably generated: there are $t_1,\ldots,t_d\in\kappa(\mathfrak q)$, algebraically
independent over $F$, with $\kappa(\mathfrak q)$ finite separable over $F(t_1,\ldots,t_d)$. Now
$F(t_1,\ldots,t_d)\otimes_F\Omega$ is a localization of the polynomial ring
$\Omega[t_1,\ldots,t_d]$ and is therefore regular, and

$$
\kappa(\mathfrak q)\otimes_F\Omega
=\kappa(\mathfrak q)\otimes_{F(t_1,\ldots,t_d)}
 \bigl(F(t_1,\ldots,t_d)\otimes_F\Omega\bigr)
$$

is finite étale over it, hence regular as well.

Let $\mathfrak Q$ be a prime of $C$ lying over $\mathfrak q$. The map
$B_{\mathfrak q}\to C_{\mathfrak Q}$ is flat and local, and its closed fibre is a localization of
$\kappa(\mathfrak q)\otimes_F\Omega$, hence regular; in particular that fibre is
Cohen--Macaulay, so its depth equals its dimension $e$. If $\dim C_{\mathfrak Q}\le1$ then
$\dim B_{\mathfrak q}\le1$ by (10.1a), so $B_{\mathfrak q}$ is regular; a regular system of
parameters of $B_{\mathfrak q}$ together with elements of $C_{\mathfrak Q}$ inducing one of the
fibre then generates the maximal ideal of $C_{\mathfrak Q}$, whose dimension is
$\dim B_{\mathfrak q}+e$ by (10.1a), so $C_{\mathfrak Q}$ is regular. This is $(R_1)$. For
$(S_2)$, (10.1a) gives

$$
\operatorname{depth}C_{\mathfrak Q}=\operatorname{depth}B_{\mathfrak q}+e,
\qquad
\dim C_{\mathfrak Q}=\dim B_{\mathfrak q}+e .
$$

If $\dim B_{\mathfrak q}\ge2$ then $\operatorname{depth}B_{\mathfrak q}\ge2$ and hence
$\operatorname{depth}C_{\mathfrak Q}\ge2$; if $\dim B_{\mathfrak q}\le1$ then
$\operatorname{depth}B_{\mathfrak q}=\dim B_{\mathfrak q}$ and hence
$\operatorname{depth}C_{\mathfrak Q}=\dim C_{\mathfrak Q}$. Either way $C_{\mathfrak Q}$
satisfies the required inequality, so $C$ is $(S_2)$, and $C$ is normal.

Combining the three steps proves the proposition. Finally, if $X$ is smooth over $K$ then
$X_{K'}$ is smooth over $K'$ for every $K'$, hence regular, hence normal by Corollary 14.44; so
a smooth $K$-scheme, in particular a smooth curve, is geometrically normal and the conclusion is
automatic. $\square$

Thus the generic curve itself causes no trouble in our main setting. The trouble lies in the integral special fibers, where ramification and residue-field extension can create singularities.

### 10.4 Ramification and vertical multiplicities

Suppose $R\subset R'$ is an extension of discrete valuation rings with ramification index $e$, so

$$
\pi=u(\pi')^e
$$

for a unit $u\in R'$. Let $E$ be a prime component of the normalization of the base change lying over a vertical component $\Gamma$, and let $r(E/\Gamma)$ be the ramification index of their normalized divisorial valuations, so that

$$
v_E(f)=r(E/\Gamma)v_\Gamma(f)
\qquad(f\in K(X)^\times).
$$

If $\Gamma$ has multiplicity $m=v_\Gamma(\pi)$, then

$$
e\,v_E(\pi')=v_E(\pi)=r(E/\Gamma)m,
\qquad
v_E(\pi')=\frac{r(E/\Gamma)m}{e}.
$$

This integer is the multiplicity of $E$ in the normalized special fiber. The formula, rather than a blanket multiplication by $e$, accounts simultaneously for splitting and ramification of the divisorial valuation.

The local semistable equation illustrates both creation and repair:

$$
xy=\pi
\quad\leadsto\quad
xy=u(\pi')^e.
$$

For $e>1$ the base-changed total space is generally singular at the crossing, though the original total space was regular. Normalization alone may not resolve it; a chain of blowups does. After resolution, the reduced special fiber can again have normal crossings. Therefore “regular model commutes with ramified base change” is false.

Unramified étale base change behaves better. It preserves regularity and the equation $xy=\pi$ remains semistable. This contrast is one reason inertia and ramification enter the geometry of reduction.

### 10.5 Descent of models

Let $S'\to S$ be finite faithfully flat. A model over $S'$ with an isomorphism between its two pullbacks to $S'\times_SS'$ satisfying the cocycle condition descends effectively when it is quasi-projective; a compatible relatively ample line bundle provides the projective descent. These are the results of Book 10 together with the projective theory of Book 8.

Properties that are faithfully flat local on the base—flatness, finite presentation, properness, smoothness—descend. Regularity of the total space is not itself simply a property of the morphism, but it descends under faithfully flat maps with geometrically regular fibers, in particular under étale covers. Normality descends under faithfully flat morphisms satisfying the corresponding geometric reducedness conditions. Under a ramified cover, a regular model upstairs may descend to a singular quotient.

Hence descent is a two-part test: descend the object and its polarization, then verify the geometric property whose fibers or quotient singularities may have changed. A descent datum does not magically preserve regularity.

## 11. Minimal regular models

### 11.1 Exceptional curves and contraction

Existence leaves many choices: blowing up any closed point of a regular model gives another regular model. Minimality removes precisely this artificial freedom.

Let $R$ be a discrete valuation ring with residue field $k$, and let $X/R$ be a regular proper
model. A vertical integral curve $E$ is an **exceptional curve of the first kind** if, after
accounting for its field of constants, it is a projective line with normal bundle of degree
$-1$. Equivalently, if $k_E=H^0(E,\mathcal O_E)$, then
$E\simeq\mathbf P^1_{k_E}$ and $\mathcal O_E(E)\simeq\mathcal O_E(-1)$.

The following finite package contains all the intersection theory needed for minimal models. It
is proved here so that neither contraction nor factorization depends on Book 12.

**Proposition 11.0 (local intersection, blowup, and adjunction package).** Let $X$ be a regular
proper arithmetic surface over a discrete valuation ring $R$ with residue field $k$.

1. If $D$ is a Cartier divisor and $C$ is a vertical integral curve, set

   $$
   D\cdot C=\deg_k(\mathcal O_X(D)|_C)
   =[H^0(C,\mathcal O_C):k]\deg_{H^0(C,\mathcal O_C)}(\mathcal O_X(D)|_C).
   \tag{11.i}
   $$

   This is bilinear. If $D$ and $C$ have no common component, then

   $$
   D\cdot C=\sum_{x\in |D|\cap C}[\kappa(x):k]
   \operatorname{length}_{\mathcal O_{X,x}}\mathcal O_{X,x}/(f,g),       \tag{11.ii}
   $$

   where $f,g$ are local equations for $D,C$. In particular distinct effective integral curves
   have nonnegative intersection.
2. For a proper morphism $f:X\to Y$ of regular arithmetic surfaces, a Cartier divisor $D$ on
   $Y$, and a vertical integral curve $C$ on $X$,

   $$
   f^*D\cdot C=D\cdot f_*C,                                      \tag{11.iii}
   $$

   where $f_*C=0$ if $C$ is contracted and otherwise is the image curve multiplied by the degree
   of its function-field extension.
3. If $b:X'\to X$ is the blowup of a closed point $x$ and
   $e=[\kappa(x):k]$, its exceptional curve is
   $E=\mathbf P^1_{\kappa(x)}$ and

   $$
   E^2=-e,\qquad b^*D=D'+m_x(D)E,\qquad b^*D\cdot E=0,             \tag{11.iv}
   $$

   hence $D'\cdot E=m_x(D)e$ and $(D')^2=D^2-m_x(D)^2e$ whenever
   the displayed self-intersections are defined. Moreover

   $$
   K_{X'/R}=b^*K_{X/R}+E.                                        \tag{11.v}
   $$
4. If $C$ is a vertical integral curve, $k_C=H^0(C,\mathcal O_C)$, and arithmetic genus is taken
   over $k_C$, then

   $$
   [k_C:k](2p_a(C)-2)=C^2+K_{X/R}\cdot C.                         \tag{11.vi}
   $$
5. Write a connected closed fiber as $F=\sum m_iC_i$. Its intersection matrix is negative
   semidefinite and its kernel over $\mathbf Q$ is spanned by $F$. Consequently the form is
   negative definite on any collection of components which omits at least one component of the
   fiber.

**Proof.** A vertical integral curve on the regular surface is an effective Cartier divisor: its
generic point is a height-one prime of each local ring it meets, and such a prime is principal by
Theorems 14.43 and 14.38.
For a rational section of a line bundle on $C$, the degree of its divisor is the sum of the
orders multiplied by $[\kappa(x):k_C]$. Apply this to the restriction of a local equation $f$
of $D$. In the one-dimensional Cohen--Macaulay local ring $\mathcal O_{C,x}$, its order is
$\operatorname{length}\mathcal O_{C,x}/f$; writing
$\mathcal O_{C,x}=\mathcal O_{X,x}/(g)$ proves (11.ii), including its residue factor.
Bilinearity follows from tensor products of line bundles. The divisor of the norm of a rational
section has at a closed point the residue-weighted sum of the orders above it. Applied to the
restriction of an equation for $D$, this is (11.iii); the contracted case has degree zero because
a pullback from a point is trivial on $C$.

For the blowup, the two parameter charts of Section 8.4 identify
$E$ with $\mathbf P^1_{\kappa(x)}$ and its conormal bundle with $\mathcal O_E(1)$, so
$\mathcal O_E(E)=\mathcal O_E(-1)$ and $E^2=-e$. Dividing the pullback of a local equation of
$D$ by the largest exceptional power gives $b^*D=D'+m_x(D)E$. Formula (11.iii) gives
$b^*D\cdot E=0$; the remaining assertions of (11.iv) follow by expansion. On the same two
charts, if $(u,v)$ is a regular system of parameters, the Jacobians of
$(u,v)=(u,ut)$ and $(sv,v)$ are respectively $u$ and $v$. The transition quotient is the
canonical section of $\mathcal O(E)$, proving (11.v). Equivalently this is the codimension-one
case of the lci duality and transitivity theorem of Book 9.

The Cartier sequence for $C$, followed by the lci adjunction theorem of Book 9, gives

$$
(\omega_{X/R}\otimes\mathcal O_X(C))|_C\simeq\omega_{C/k}.
$$

Degree over $k$ of the right side is
$[k_C:k](2p_a(C)-2)$ by curve duality, proving (11.vi).

Finally the divisor $F$ is cut out by a uniformizer, hence
$F\cdot C_i=0$ for every $i$. For $V=\sum a_iC_i$, eliminate the diagonal terms from $V^2$ by
these equalities. One obtains

$$
V^2=-\sum_{i<j}m_im_j(C_i\cdot C_j)
       \left(\frac{a_i}{m_i}-\frac{a_j}{m_j}\right)^2.           \tag{11.vii}
$$

All coefficients are nonnegative by (11.ii). Equality says that $a_i/m_i$ is constant along
every edge of the component incidence graph. Connectedness of the fiber makes that graph
connected: otherwise the two unions of components would be disjoint open-and-closed subsets of
the fiber. Thus equality holds precisely for multiples of $F$. A vector supported on a proper
subset cannot be such a multiple, proving the last assertion. $\square$

**Theorem 11.1 (relative Castelnuovo contraction).** Let $S$ be an excellent Dedekind scheme, let $X/S$ be a regular proper arithmetic surface, and let $E$ be a vertical exceptional curve of the first kind. There is a regular proper $S$-scheme $Y$ and a proper birational morphism

$$
c:X\longrightarrow Y
$$

which is an isomorphism on $X\setminus E$, maps $E$ to a closed regular point $y\in Y$, and identifies $X$ with $\operatorname{Bl}_y(Y)$. The same assertion holds over the localization of $S$ at the image of $E$, and the local contraction glues with the identity away from that fiber.

**Proof.** Localize $S$ at the image of $E$, so the base is the spectrum of a DVR. We first
justify the polarization. On each irreducible component of the closed fiber choose a closed
regular point away from the other components. At such a point a parameter transverse to that
component cuts out a horizontal prime divisor. Its closure is finite over the DVR by properness
and is Cartier because $X$ is regular, hence factorial at every point by Theorem 14.43. The sum of these closures has positive degree on every
fiber component, so the fiberwise ampleness criterion for proper curves makes its associated
line bundle relatively ample. Choose such a relatively ample $H$.

Let $h=\deg(H|_E)$, with degree taken over
$k(E)=H^0(E,\mathcal O_E)$. Since
$\mathcal O_E(E)=\mathcal O_{\mathbf P^1_{k(E)}}(-1)$, the line bundle

$$
L=H\otimes\mathcal O_X(hE)
$$

restricts trivially to $E$ and has positive degree on every other component of the closed fiber.

We prove the required generation without assuming that this fiber is reduced or nodal. Write it
as $F=\sum m_iC_i$, with $E=C_0$. If $D$ is an effective subdivisor of $F$ and $C_i\leq D$, then

$$
0\longrightarrow\mathcal O_{D-C_i}(-C_i)
 \longrightarrow\mathcal O_D\longrightarrow\mathcal O_{C_i}\longrightarrow0. \tag{11.a}
$$

Starting with $D=F$, repeatedly use (11.a) to remove all copies of the components
$C_i\ne E$. Every quotient is a fixed coherent rank-one sheaf on such a component, tensored by
$L^n$; its degree tends to infinity with $n$. To see directly that its first cohomology then
vanishes, discard its zero-dimensional torsion, pull the remaining torsion-free rank-one sheaf to
the normalization of the reduced component, and use the conductor exact sequence. The only
cokernel is zero-dimensional, while on the normal proper curve Riemann--Roch gives vanishing once
the degree exceeds $2p_a-2$. After the other components have been removed, filter $m_0E$ by

$$
0\longrightarrow\mathcal O_E(j)\longrightarrow
 \mathcal O_{(j+1)E}\longrightarrow\mathcal O_{jE}\longrightarrow0
\qquad(0\leq j<m_0);
$$

these layers have zero first cohomology. The same filtration remains valid after tensoring by
the ideal of any subscheme of length at most two supported away from $E$: only fixed divisors of
degree at most two are added on the positive-degree components. It also remains valid for the
ideal of $E$ together with such a subscheme. Consequently one integer $n_0$ works simultaneously
for

$$
H^1(F,L^n\otimes\mathcal I_Z)=0\qquad(n\geq n_0),           \tag{11.b}
$$

where $Z$ is empty, is a length-one or length-two subscheme disjoint from $E$, or is the union of
$E$ with one such subscheme.

The evaluation exact sequences and (11.b) show that $L^n|_F$ is generated, that its sections
separate every length-two subscheme away from $E$, and that they separate every point away from
$E$ from the constant value on $E$. Every section restricts constantly to $E$ because
$L|_E\simeq\mathcal O_E$. The same filtration proves (11.b) on every thickening $rF$: since
$F$ is the divisor of a uniformizer, the successive quotients of $\mathcal O_{rF}$ are copies
of $\mathcal O_F$, and the same remains true after imposing any one of the listed evaluation
ideals. Apply the proper finiteness, theorem on formal functions, and evaluation criterion of
Book 9. The completed $R^1$ of each evaluation kernel is the inverse limit of these vanishing
$H^1$'s and is zero; faithful flatness of completion and Nakayama then make the evaluation map
surjective over the DVR. On the generic fiber $L=H$, so a further common multiple is very ample.
Thus some $L^N$ is generated, constant on $E$, and separates points and tangent vectors off $E$.
Let $V=H^0(X,L^N)$ and let $B$ be the image
of $\operatorname{Sym}_R(V)$ in $\bigoplus_qH^0(X,L^{qN})$. Then
$Y=\operatorname{Proj}_RB$ is algebraic and projective, and the induced $c:X\to Y$ contracts
exactly $E$ and is an isomorphism elsewhere by the separation criterion.

The common value of the sections on $E$ defines one point $y\in Y$. On $X\setminus E$ the
sections give a locally closed immersion into a standard projective open. The valuative criterion
shows that its inverse is defined at every specialization not meeting $E$; it is therefore both
open and proper over its image, hence an isomorphism. Replace $Y$ by the finite Stein factor
$\operatorname{Spec}_Y(c_*\mathcal O_X)$. It remains projective, is unchanged away from $y$, and
now satisfies $c_*\mathcal O_X=\mathcal O_Y$; its unique positive-dimensional fiber is $E$.

Put $I=\mathcal O_X(-E)$ and $J_q=c_*I^q$. The sheaf $I$ has positive degree on the only
positive-dimensional fiber of $c$, hence the componentwise argument above makes it $c$-ample.
The exact sequences

$$
0\to I^{q+1}\to I^q\to\mathcal O_E(q)\to0
$$

have $R^1c_*I^q=0$: relative Serre vanishing proves this for large $q$, and descending induction
uses $H^1(E,\mathcal O_E(q))=0$. Pushforward therefore gives, for every $q\ge0$, an exact row

$$
0\longrightarrow J_{q+1}\longrightarrow J_q
 \longrightarrow H^0(E,\mathcal O_E(q))\longrightarrow0.       \tag{11.0}
$$

For $q=0$, this identifies $J_1$ with the kernel of
$\mathcal O_Y\to k(y)$, hence with $\mathfrak m_y$. Products of the rows (11.0) form a
commutative diagram. Since
$H^0(\mathcal O_E(1))^{\otimes q}\to H^0(\mathcal O_E(q))$ is surjective, induction first gives
$J_1J_q+J_{q+2}=J_{q+1}$. Repeating the same equality inside its final summand gives

$$
J_{q+1}=J_1J_q+J_{q+n}\qquad(n\geq2).
$$

The theorem on formal functions from Book 9 identifies the completion of the coherent ideal
$J_{q+1}$ at $y$ with the inverse limit of its restrictions to the infinitesimal fibers. In
particular the induced filtration is separated, so the intersection over $n$ of the completed
$J_{q+n}$ is zero. Hence $J_{q+1}=J_1J_q$ after completion, and faithful flatness of completion
gives the equality in $\mathcal O_{Y,y}$; it already holds away from $y$. Consequently
$J_q=J_1^q=\mathfrak m_y^q$. Thus

$$
\mathfrak m_y^q/\mathfrak m_y^{q+1}\simeq H^0(E,\mathcal O_E(q)).
$$

We also need the corresponding equality before passing to associated graded rings. Pullback gives
a natural map

$$
c^{-1}\mathfrak m_y\,\mathcal O_X\longrightarrow I=\mathcal O_X(-E).
$$

It is an isomorphism off $E$. On $E$, row (11.0) for $q=0,1$ identifies its reduction with the
evaluation map

$$
H^0(E,\mathcal O_E(1))\otimes_{k(y)}\mathcal O_E
 \longrightarrow\mathcal O_E(1),
$$

which is surjective. The cokernel of the pullback map is coherent, supported on $E$, and is zero
modulo the ideal $I$; Nakayama at every point of $E$ makes it zero. Hence

$$
I=\mathfrak m_y\mathcal O_X.                               \tag{11.0a}
$$

Apply the theorem on formal functions of Book 9 to the proper morphism $c$ and the coherent
sheaves $I^q$. It identifies the completed stalks of $J_q=c_*I^q$ with the inverse limits of
$H^0(I^q/I^{q+n})$; the exact rows (11.0) make these systems Mittag--Leffler. Consequently it
identifies
$\operatorname{gr}_{\mathfrak m_y}\widehat{\mathcal O}_{Y,y}$ with
$\bigoplus_qH^0(E,\mathcal O_E(q))\simeq k(y)[u,v]$. Hence the completed local ring has dimension
and embedding dimension two and is regular; regularity descends from completion. The equality
(11.0a) and the universal property give
$\phi:X\to\operatorname{Bl}_yY$. Choose lifts $u,v$ of a basis of
$\mathfrak m_y/\mathfrak m_y^2$. The equality of associated graded rings says that the map on
exceptional curves induced by $[u:v]$ is
$E\simeq\mathbf P^1_{k(y)}\to\mathbf P(\mathfrak m_y/\mathfrak m_y^2)$ and is an isomorphism.
Thus $\phi$ is quasi-finite along $E$ and is already an isomorphism away from $E$. Proper and
quasi-finite makes it finite; the blowup of the regular local ring is normal, so finite
birationality makes $\phi$ an isomorphism.

The contraction has the factorization property used below. Let $h:X\to T$ be a morphism to a
separated scheme and suppose $h(E)$ is one point $t$. Choose an affine neighborhood $V$ of $t$.
The closed set $h^{-1}(T\setminus V)$ misses $E$; its proper image under $c$ therefore misses $y$.
After replacing $Y$ by the complementary neighborhood of $y$, the map $h$ lands in $V$. Since
$c_*\mathcal O_X=\mathcal O_Y$, its affine coordinate functions descend uniquely and define
$Y\to V$. This agrees with $h$ after pullback; away from $y$ it glues with the map transported
through $X\setminus E\simeq Y\setminus\{y\}$. Separatedness gives uniqueness. The construction
over $\mathcal O_{S,s}$ is of finite presentation: the graded algebra, its finitely many
generators and relations, the morphism, and the blowup isomorphism all descend to some affine
neighborhood $W$ of $s$. Shrink $W$ so that the descended morphism is an isomorphism away from
the fiber at $s$; this is possible because its non-isomorphism locus has closed image and its
base change to $\operatorname{Spec}\mathcal O_{S,s}$ is supported at the closed point. Regularity
of the descended target holds near the contracted point by the completed-local calculation and
elsewhere follows from its identification with $X$; after another shrinking it is regular.
Finally glue this target over $W$ to $X|_{S\setminus\{s\}}$ along
$W\setminus\{s\}$ using the established isomorphism. Finite-presentation descent also preserves
properness and the blowup identity. This proves the global assertion and the claimed compatibility
with localization. $\square$

A regular proper model is **relatively minimal** if none of its fibers contains an exceptional curve of the first kind. Every contraction lowers the number of irreducible components of the affected fiber, so repeatedly contracting must stop. This proves existence of a relatively minimal model once contractions remain in the chosen category.

### 11.2 Existence in positive genus

Contraction gives existence. We now prove the comparison needed for its universal property.

Proposition 11.0 supplies, before any use of factorization, the local-length pairing, its residue
weights and projection formula, the blowup and canonical-divisor formulas, adjunction, and the
negative-definite restriction of the fiber matrix. We now use that package.

**Factorization lemma.** Every proper birational morphism between regular arithmetic surfaces over
$R$ which is the identity on the generic fiber factors into blowups at closed regular points.

**Proof.** A proper birational morphism to a normal surface is an isomorphism over every
codimension-one point: after localization this is a proper birational morphism to the spectrum of
a DVR, and the valuative criterion supplies inverse sections which agree on the generic point.
Thus every nontrivial fiber of $f$ is a union of finitely many vertical curves over closed points.
If there are none, $f$ is proper and quasi-finite, hence finite, and finite birationality to the
normal $Y$ makes it an isomorphism.

Suppose exceptional curves exist. Since both surfaces are regular and of finite type over the
regular one-dimensional base, $f$ is a local complete-intersection morphism of virtual relative
dimension zero. Concretely, factor it locally as its graph in a smooth $Y$-scheme. The ambient
local rings are regular and the graph is regular of the expected codimension, so its ideal is
generated by a regular sequence. The two-term conormal presentation therefore has locally free
terms of the same rank. Taking its determinant gives the Jacobian map of line bundles

$$
f^*\omega_{Y/R}\longrightarrow\omega_{X/R}.
$$

Its zero divisor is an effective exceptional divisor
$D=\sum a_iE_i$. Every coefficient is positive. Indeed the determinant is a unit exactly where
the conormal presentation is acyclic, equivalently where the morphism is unramified. If it were a
unit at the generic point of an exceptional curve, the morphism would be unramified and hence
quasi-finite there, contradicting contraction of that curve. The determinant is an isomorphism
off the exceptional locus, so

$$
K_{X/R}=f^*K_{Y/R}+D.                                       \tag{11.1b}
$$

The intersection form is negative definite on the curves contracted by $f$. Indeed,
Proposition 11.0(5), applied one connected fiber at a time, says that the full fiber form is
negative semidefinite with kernel its multiplicity vector, whereas a divisor supported only on
contracted components omits the strict transform of at least one component of the target fiber.
It therefore cannot lie in the kernel. Since $D\ne0$, we have $D^2<0$, and hence
$D\cdot E<0$ for some exceptional component $E$.

The projection formula gives $f^*K_{Y/R}\cdot E=0$, so (11.1b) gives
$K_{X/R}\cdot E<0$. Put $d=[H^0(E,\mathcal O_E):k]$. Intersection degrees
over $k$ are multiples of $d$, so write

$$
E^2=-ad,\qquad K_{X/R}\cdot E=-bd
$$

with positive integers $a,b$. Proposition 11.0(4) gives
$2p_a(E)-2=-(a+b)$. Since $p_a(E)\ge0$, necessarily
$p_a(E)=0$ and $a=b=1$. Riemann--Roch on the integral Gorenstein curve $E$ says that the
degree-one line bundle $\mathcal O_E(-E)$ has two independent sections. Its complete linear
system is base-point free: subtracting any closed point leaves degree at most zero and at most one
section. A nonzero section has a degree-one zero, hence a rational point, and the
resulting degree-one map to $\mathbf P^1$ is an isomorphism. Thus $E$ is exceptional of the first
kind, even over an imperfect constant field.

Theorem 11.1 contracts $E$ to a regular point:
$c:X\to X_1$. Since $f$ is constant on $E$, the factorization property proved in Theorem 11.1
gives a unique $f_1:X_1\to Y$ with $f=f_1c$. The map $f_1$ is again proper and birational and
has one fewer exceptional curve. Induction ends with an isomorphism. Reversing the contractions,
$f$ is a finite composite of blowups at closed regular points. $\square$

**Theorem 11.2A (birational comparison for regular arithmetic surfaces).** Let $R$ be an excellent discrete valuation ring.

1. A birational map between regular proper arithmetic surfaces which is the identity on the generic fiber admits a common regular resolution obtained by finitely many blowups at closed points.
2. A proper birational morphism between regular arithmetic surfaces which is the identity on the generic fiber factors into finitely many blowups at closed points.
3. If the common generic fiber is a smooth projective geometrically connected curve of positive genus and $Y/R$ is relatively minimal, then the rational map $X\dashrightarrow Y$ induced by the generic-fiber identification extends uniquely to a morphism $X\to Y$. In particular two relatively minimal regular proper models with fixed generic-fiber identification are uniquely isomorphic.

**Proof.** Normalize the graph of the birational map and resolve it by Theorem 8.1. The graph
closure is integral and proper over $R$; its regular resolution is integral and dominates
$\operatorname{Spec}R$, hence is flat over the DVR. It is therefore itself a regular arithmetic
surface, not merely a regular scheme over the graph. Both projections are proper birational
morphisms between regular arithmetic surfaces and hence, by the factorization lemma, composites
of point blowups. This proves (1) unconditionally, and the factorization lemma itself proves (2).

For (3), write $X\xleftarrow pZ\xrightarrow qY$ in that form. We first prove the needed nefness
statement. Let $\Gamma$ be an integral component of the closed fiber of the relatively minimal
model $Y$, put $d_\Gamma=[H^0(\Gamma,\mathcal O_\Gamma):k]$, and take $p_a$ over that constant
field. Adjunction gives

$$
K_{Y/R}\cdot\Gamma=d_\Gamma(2p_a(\Gamma)-2)-\Gamma^2.       \tag{11.2}
$$

Proposition 11.0(5) gives $\Gamma^2\leq0$. If $p_a(\Gamma)\geq1$, (11.2) is nonnegative. If
$p_a(\Gamma)=0$ and $\Gamma^2=-d_\Gamma$, the line bundle
$\mathcal O_\Gamma(-\Gamma)$ has degree one, so $\Gamma$ is a projective line and is exceptional;
relative minimality excludes this. The next possible negative normal degree is at most
$-2d_\Gamma$, which again makes (11.2) nonnegative. It remains only the case
$\Gamma^2=0$. Equality in (11.vii), applied to a vector supported on $\Gamma$, says that the whole
connected fiber is $F=m\Gamma$. The filtration by powers of the ideal of $\Gamma$ has quotients

$$
\mathcal I_\Gamma^j/\mathcal I_\Gamma^{j+1}
 \simeq\mathcal O_\Gamma(-j\Gamma),\qquad 0\leq j<m.
$$

Each quotient has degree zero and is trivial: Riemann--Roch gives a nonzero section, whose
effective zero divisor has degree zero. Hence
$\chi(\mathcal O_F)=m[\kappa(\Gamma):k]>0$. Flatness gives
$\chi(\mathcal O_F)=\chi(\mathcal O_{Y_K})=1-g\leq0$, a contradiction. Thus
$K_{Y/R}\cdot\Gamma\geq0$ for every vertical integral curve.

Return to a common resolution $X\xleftarrow pZ\xrightarrow qY$. If a terminal
$p$-exceptional curve $E$ is also $q$-exceptional, then $E$ is a $(-1)$-line on $Z$ and both
maps are constant on it. Theorem 11.1 contracts it and both maps factor uniquely through the
contraction. Repeating this finite pruning, either $p$ becomes an isomorphism or there is a
terminal $p$-exceptional curve $E$ which is not $q$-exceptional. Assume the latter. For one point
blowup $b:W'\to W$, the determinant of differentials on the two affine charts gives
$K_{W'/R}=b^*K_{W/R}+E_b$. Induction through a factorization of $q$ therefore gives

$$
K_{Z/R}=q^*K_{Y/R}+\sum_i a_iE_i,                         \tag{11.3}
$$

where the $E_i$ are the $q$-exceptional prime curves and every $a_i$ is a positive integer: the
coefficient of a newly created exceptional curve is one plus the sum of the coefficients of the
old exceptional curves through its center, counted with their local multiplicities. Since $E$ is
not among the $E_i$, distinct integral curves on the regular surface have nonnegative local
intersection multiplicities. The projection formula and vertical nefness give

$$
q^*K_{Y/R}\cdot E=K_{Y/R}\cdot q_*E\geq0,
\qquad
E_i\cdot E\geq0.
$$

Thus (11.3) gives $K_{Z/R}\cdot E\geq0$. But adjunction for the $(-1)$-line, including its
residue degree in both terms, gives $K_{Z/R}\cdot E=-[\kappa(E):k]$, a contradiction. Hence
$p$ is an isomorphism. Separatedness gives uniqueness; applying the result both ways proves the
final assertion. $\square$

**Theorem 11.2 (minimal regular model).** Let $R$ be an excellent discrete valuation ring with fraction field $K$, and let $C/K$ be a smooth projective geometrically connected curve of positive genus. Then $C$ has a relatively minimal regular proper model $X_{\min}/R$. Every regular proper model of $C$ admits a unique morphism to $X_{\min}$ inducing the identity on $C$.

**Proof.** Theorem 9.1 supplies a regular proper model. Apply Theorem 11.1 repeatedly; each step
lowers the number of fiber components. Theorem 11.2A(3) gives the mapping property. $\square$

The same construction works over a global excellent Dedekind scheme. Only finitely many fibers of a fixed proper model are non-smooth. Theorem 11.1 glues each local contraction with the identity elsewhere, and the local Theorem 11.2A mapping properties glue uniquely because they agree on the generic fiber.

A genus-one curve with a rational point has the regular geometric model associated with a minimal Weierstrass equation after resolving its surface singularities. The Weierstrass model itself is often normal but singular; the minimal regular model is its resolution, while relative minimality prohibits superfluous point blowups.

### 11.3 Uniqueness and its limits

Positive genus is essential. For $\mathbf P^1_K$, both $\mathbf P^1_R$ and models obtained through elementary transformations of ruled surfaces can be relatively minimal in natural senses without a canonical map between them fixing the generic fiber. Marking three disjoint sections restores rigidity, but the unmarked genus-zero curve has too many automorphisms and too little canonical positivity.

Minimal regular does not mean smooth, semistable, or stable. Its special fiber may have multiplicities, cusps as curves inside a regular total space, or configurations that require a field extension before becoming nodal. Nor does minimality commute with arbitrary base change. A ramified extension can create exceptional curves after resolution; recovering relative minimality then requires new applications of Theorem 11.1.

Uniqueness is relative to the fixed identification of the generic fiber. If generic automorphisms are allowed, they act on the minimal model by the mapping property: an automorphism of $C$ gives a second identification and extends uniquely.

### 11.4 Marked and semistable variants

For a marked curve $(C;P_1,\ldots,P_n)$ one resolves the boundary as well as the surface.

**Embedded-resolution lemma.** On a regular excellent surface, a reduced curve together with
finitely many pairwise distinct regular marked branches becomes a normal-crossings divisor with
disjoint marked branches after finitely many closed-point blowups.

**Proof.** Apply the branch-resolution part of Lemma 8.8 to the union of the reduced curve and
the pairwise distinct labeled marked branches. We recall the two decreasing formulas because
their residue weights are essential over a nonclosed field. If
$\delta_x=\ell_{\mathcal O_{D,x}}(\overline{\mathcal O}_{D,x}/\mathcal O_{D,x})$ and $m_x$ is
the multiplicity, the two affine blowup charts and the normalization exact sequence give

$$
\delta_x=\binom{m_x}{2}+
 \sum_{y\mapsto x}[\kappa(y):\kappa(x)]\delta_y.             \tag{11.4a}
$$

Thus blowing up a point with a singular branch strictly lowers the residue-weighted sum of the
remaining branch delta invariants; finiteness of normalization makes the initial sum finite.
After every branch is regular, the same chart calculation gives

$$
I_x(D_1,D_2)=m_1m_2+
 \sum_{y\mapsto x}[\kappa(y):\kappa(x)]
 I_y(\widetilde D_1,\widetilde D_2).                         \tag{11.4b}
$$

Here $m_i$ is the branch multiplicity, hence one. Consequently blowing up a tangency strictly
lowers the residue-weighted sum of the excess contacts while preserving regularity of the
branches.
When every pair is transverse, blowing up a point through three or more branches lowers the number
of multiple incidences and creates only distinct transverse points on the exceptional line. Treat
marked branches as additional labeled branches and blow up any coincidence between two markings
or between a marking and an impermissible node. Lexicographic induction on total branch delta,
total excess intersection, and total multiple incidence terminates. All centers are actual closed
points, so finite residue fields cause no generic-choice problem. $\square$

A regular **semistable model** has reduced special fibers whose only singularities are ordinary double points and whose components meet transversely. Étale-locally at a node it has equation

$$
xy=\pi.
$$

Resolution alone does not guarantee semistability. Semistable reduction is the additional theorem that after a suitable finite separable extension of $K$, a smooth proper curve has a semistable model. Once that extension and a normal proper candidate are supplied, this book normalizes it and resolves away from the nodal open. Removing exceptional curves of the first kind uses Theorem 11.1, while contracting the unstable rational components of a stable model is a different stable-contraction problem. The stable model may have nodal total fibers; its total space need not be regular after ramified base change, so stable and minimal regular models serve different purposes.

## 12. Models for modular, Shimura, and semistable problems

### 12.1 The exact reusable model theorem

The preceding results can be collected in the form actually needed later.

**Theorem 12.1 (arithmetic curve model package).** Let $S$ be an excellent Dedekind scheme, $U\subset S$ a nonempty open, and $C/K(S)$ a smooth projective geometrically connected curve. Suppose a smooth projective model $\mathcal C_U/U$ is given. Then:

1. there is a normal flat projective model $X/S$ extending $\mathcal C_U$;
2. there is a regular flat projective model $\mathcal X/S$ and a projective birational map $\mathcal X\to X$, identical over $U$;
3. any finite collection of projective models, rational maps, and finite generic correspondences is dominated by such a regular model on which their graph closures are defined as proper correspondences;
4. after a finite extension $K'/K(S)$, with $S'$ the normalized base, normalization of the reduced base change followed by resolution gives a regular projective $S'$-model;
5. if the supplied model over an open of $S'$ is semistable, the resolution is an isomorphism over that open;
6. if $g(C)>0$, contracting vertical exceptional curves produces the unique minimal regular proper model.

Every adjective has a source. Excellence of $S$ gives finite normalization and supplies the ring-theoretic hypothesis in Theorem 8.1; termination and regularity of the resolution come from Theorem 8.1 itself. Smoothness of $C$ makes the generic fiber normal and regular. Projectivity of $C$ starts the closure and ensures the final model is projective. Flatness follows from integrality over a Dedekind base. Properness alone is preserved throughout but does not by itself choose an embedding. Geometric connectedness prevents an unintended product of generic components. The last assertion has two additional sources: Theorem 11.1 supplies algebraic contractions which stay in the regular proper category, and Theorem 11.2A supplies the positive-genus mapping property and uniqueness.

### 12.2 Modular curves

A modular curve is first presented over an open base where the level structure has good deformation theory. Its open moduli problem is generally not proper because elliptic curves can degenerate. Adding generalized degenerations supplies a proper compactification over that good open; the cusps form finite horizontal divisors.

To obtain the exact surface used in arithmetic arguments, proceed as follows.

1. Take the smooth projective generic modular curve, including its cusps.
2. Extend the chosen good integral compactification over $U$, typically the complement of primes dividing the level.
3. Close it projectively over $S$ and normalize. Normalization retains the moduli model over $U$ and repairs branch identifications at bad primes.
4. Resolve only the finitely many closed surface singularities above bad primes.
5. Apply the embedded-resolution lemma of Section 11.4 so cusp closures are disjoint regular horizontal divisors meeting the fiber transversely.

The resulting object is a regular proper, indeed projective, arithmetic surface carrying the same generic modular curve and the prescribed smooth model over $U$. It is enough for extending rational functions, maps to Jacobians, degeneracy maps after graph resolution, and special-fiber calculations. Normalization alone need not make it regular, and regularity does not make every bad fiber smooth.

Fine level structures may exist only after a faithfully flat extension of the base. Construct the polarized model there, retain the descent datum through normalization where geometric normality permits, and descend using Book 10. At primes where the group action has fixed points, the coarse quotient can be normal but singular. Resolve the quotient surface after descent; regularity upstairs does not eliminate quotient singularities downstairs.

### 12.3 Shimura curves

The distinction between a fine moduli cover and its coarse quotient is again essential. A finite group acting on a regular surface can have isolated fixed points; the quotient is finite and normal under the standard tame hypotheses but can fail to be regular. Its two-dimensional quotient singularities admit a projective resolution by Theorem 8.1.

For quaternionic or PEL constructions defined after a finite extension of the reflex field, use the normalized Dedekind base. A descent datum plus a polarization descends the projective model. If ramification has introduced singularities, normalize and resolve after the descent or on a common equivariant domination. The output required for curve-level arguments is a regular proper curve model, not a smooth integral moduli space at every bad prime.

### 12.4 Semistable reduction input

Suppose a finite separable extension $K'/K$ has been chosen and a projective semistable model has been supplied over an open $V\subseteq S'$, where $S'$ is the normalization of $S$ in $K'$. The model can be extended without changing its semistable locus as follows.

Apply Theorem 12.1 with the supplied model over $V$, and use Theorem 8.1 only outside $V$. At every node the completed local equation is

$$
\widehat{\mathcal O}_{\mathcal X,x}
\simeq \widehat R'[[x,y]]/(xy-\pi'),
$$

possibly after an étale extension. This ring is regular, so Theorem 8.1 leaves it unchanged. The embedded-resolution lemma of Section 11.4 separates marked sections from the nodes and makes the boundary transverse. Producing a stable rather than a regular semistable model requires a different contraction theorem for rational components meeting the remainder and markings in too few points; Theorem 11.1 concerns exceptional curves of the first kind.

This statement deliberately starts from an algebraic model over an open subscheme. A model known only over completed local rings does not automatically algebraize or glue: compatible algebraic descent data, or a separate approximation and algebraization theorem, must first supply the model over an open of $S'$. Common domination compares algebraic models once they exist; it is not a substitute for that algebraization step.

### 12.5 Finite correspondences

Hecke and degeneracy operations begin as finite maps or correspondences on generic curves. A finite generic map $f:C\to D$ produces a rational map between proper normal models. Its graph closure

$$
\Gamma_f\subset X\times_SY
$$

is proper over both factors. Normalize the graph and resolve it to obtain a regular surface $Z$ with morphisms to both models.

The universal property of normalization factors a morphism from a normal source through a normalization once that morphism already exists. It does not remove codimension-two indeterminacy of a rational map: for example, the rational map $\mathbf A^2\dashrightarrow\mathbf P^1$ given by $[x:y]$ is undefined at the origin although the source is normal. Thus the graph construction is essential. resolving the normalized graph makes the two projections honest proper morphisms. Without Theorem 8.1, normalization alone leaves this regular-domination claim unproved. Finiteness on the generic fiber still does not imply that either projection is finite, because it may contract vertical curves. Passing to the Stein factor—the spectrum of the direct image of the structure sheaf—separates a connected-fiber contraction from a finite map.

For a correspondence, keep both projections from the normalized graph. a common regular domination makes their compositions honest. Later intersection and cohomological theories may act with the correspondence even if neither projection is a morphism between preselected minimal models. This is why domination, rather than forced functoriality of minimal models, is the robust construction.

## 13. Synthesis

### 13.1 A hypothesis ledger

The main properties and their exact uses can now be read without ambiguity.

| Property                  | What it supplies                                                                                                                         | What it does not supply                                                             |
| ------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------- |
| reduced                   | a total ring of fractions componentwise                                                                                                  | separated branches or integral closure                                              |
| normal                    | integral extension across codimension one and the normalization mapping property                                                         | regular closed points on a surface                                                  |
| regular                   | regular local rings on the total space                                                                                                   | smooth or reduced fibers                                                            |
| smooth over $S$           | flatness and geometrically regular fibers                                                                                                | properness                                                                          |
| Japanese domain           | finite integral closure in finite field extensions                                                                                       | stability for all prime quotients                                                   |
| Nagata scheme             | finite normalization of the scheme itself                                                                                                | finite normalization for finite-type schemes over it                                |
| universally Japanese      | finite normalization for finite-type schemes                                                                                             | surface resolution by itself                                                        |
| excellent scheme          | Nagata finiteness, good formal fibers, open regular locus, and all three again on every chart, localization, finite cover and completion | a proof of Theorem 8.1, algebraization of a formal contraction, or smooth reduction |
| proper morphism           | valuative extension and universal closedness                                                                                             | a chosen projective embedding                                                       |
| projective morphism       | properness plus an ample polarization                                                                                                    | regularity or normality                                                             |
| flat over a Dedekind base | no vertical torsion and well-behaved fibers                                                                                              | reduced special fibers                                                              |

The surface inputs are independent entries in this ledger. Theorem 8.1 passes from a normal model to a regular one while preserving a chosen regular open. Theorem 11.1 contracts one specified exceptional curve inside the algebraic category. Theorem 11.2A resolves and factors birational comparisons and supplies the positive-genus minimal-target criterion. In particular, excellence is a hypothesis in all three settings but proves none of these theorems by itself.

Excellence, by contrast with the three surface inputs, is not a carried hypothesis: it is a theorem about the bases actually used. Theorem 3.2 imports from Book 10a the full permanence package — finite-type algebras, localizations, finite algebras and completions of an excellent ring are excellent; an excellent ring is universally Japanese; completion is a faithfully flat regular map at every point of an excellent scheme; and regular loci are open on every scheme locally of finite type over one — and Theorem 3.2(5) verifies excellence for every base occurring in this book. The one restriction is the residue-field convention fixed in Section 3.2: "excellent" here always means "excellent with $p$-finite residue fields", which excludes bases such as $\mathbf F_p(u_1,u_2,\ldots)$ and $k[[t]]$ over such a field, and which is satisfied by $\mathbf Z$, by rings of integers and their localizations, by discrete valuation rings with finite or perfect residue field, by fields finitely generated over their prime field, and by everything essentially of finite type over these. So the ledger entry "excellent scheme" is an established property of the bases, not an assumption about them.

Three counterexamples should remain in view:

$$
k[x,y,z]/(xy-z^2)
$$

is normal but not regular at the vertex;

$$
R[x,y]/(xy-\pi)
$$

is regular but not smooth at the node of its special fiber; and a purely inseparable scalar extension of a field can be nonreduced, so normality is not stable under arbitrary base change.

### 13.2 The construction pipeline

Starting with $C/K$, the reusable sequence, is

$$
\begin{array}{ccccc}
C&\subset&\mathbf P^N_K&&\\
&&\downarrow&&\\
&&X_0&\text{projective closure}&\\
&&\uparrow\ \text{finite}&&\\
&&X_1&\text{normalization}&\\
&&\uparrow\ \text{projective birational (Theorem 8.1)}&&\\
&&\mathcal X&\text{regular model}.&
\end{array}
$$

The arrows point from the improved model to the previous one. If a finite extension $K'/K$ is made, repeat normalization and resolution after base change. If positive genus calls for a canonical endpoint, Theorems 11.1 and 11.2A produce $\mathcal X_{\min}$ with its universal property. If semistability is desired, a separate semistable-reduction input supplies the field extension and nodal model; Theorem 8.1 then supplies its regular incarnation.

At every stage there is a simple diagnostic question.

1. Are unwanted vertical components present? Take schematic closure or remove base torsion.
2. Are integral functions missing or branches glued? Normalize.
3. Are closed surface points still singular? Invoke Theorem 8.1; normalized blowups alone do not prove termination.
4. Has ramified base change spoiled normality or regularity? Normalize and resolve again.
5. Are there superfluous exceptional curves? Contract them by Theorem 11.1 and identify the positive-genus endpoint by its mapping property.

Confusing these repairs is the source of many false shortcuts. Each answers a different defect.

### 13.3 Conclusion

An arithmetic curve has two lives. Generically it is a smooth projective one-dimensional variety; integrally it is a two-dimensional space whose vertical geometry records reduction. Projective closure connects the two lives but introduces defects. Normalization repairs the integral structure finitely because the bases of arithmetic geometry are excellent, hence universally Japanese: Theorem 3.2 records the permanence theory established in Book 10a, and Theorem 3.2(5) verifies it for $\mathbf Z$, for rings of integers and their localizations, for complete discrete valuation rings with perfect residue field, for fields of finite $p$-degree, and for everything essentially of finite type over these, so that the finiteness of normalization is available on every chart of every model built from them. Passing from the resulting normal surface to a regular one requires Theorem 8.1; the multiplicity, tangent-cone, and conductor ideas mentioned in Chapter 8 motivate proofs of that theorem but do not establish it here.

This volume supplies finite normalization and regular proper models preserving prescribed good loci and compatible regular dominations for maps and correspondences. It also gives the positive-genus model a relatively minimal endpoint with the stated universal property. Horizontal divisors retain generic points and markings; vertical components encode extensions of valuations and bad reduction. Regularity of the total surface and singularity of the fiber coexist without contradiction, while smoothness and semistability remain appropriately stronger relative conditions.

This separation of roles is the durable lesson. Normal, regular, smooth, excellent, Nagata, proper, and projective are not competing descriptions of one good object. They are distinct tools, and arithmetic curves become manageable only when each is invoked for exactly the work it performs.

## 14. Depth, Cohen–Macaulay rings, and Serre's criteria

Several pieces of local algebra were used on credit in the preceding chapters. Section 4.1 stated Serre's criterion and the condition $(S_2)$ with a proof strategy rather than a proof. Section 4.3 called a hypersurface Cohen–Macaulay in order to conclude that the quadratic cone is normal. Sections 8.5 and 10.4 produced the surfaces $xy=\pi^n$ without deciding which of them are normal, and Section 11.4 used the regularity of $xy=\pi$ without locating it in a general framework. Finally, the divisor calculus of Chapters 5, 9, and 11 rests on the assertion that a regular local ring is factorial, so that prime divisors on a regular model are locally principal, and Section 4.2 used the same assertion in dimension one. This chapter proves all of it.

The material is pure local algebra and depends on none of Chapters 5 to 13; a reader may insert it immediately after Chapter 4. It is placed last because it is also the form in which later books of the collection use these results: a freeness statement over two-dimensional regular local rings, and the two criteria of Serre.

The following standard facts about noetherian rings are used as proof sources and are not reproved here.

1. **Nakayama.** If $M$ is a finite module over a local ring $(A,\mathfrak m,k)$ and $M=\mathfrak mM$, then $M=0$. Consequently a family in $M$ whose residues span $M/\mathfrak mM$ generates $M$, and a finite projective module over a local ring is free.
2. **Associated primes.** For a finite nonzero module $M$ over a noetherian ring $A$, the set $\operatorname{Ass}M$ of primes of the form $\operatorname{Ann}(x)$, $x\in M$, is finite and nonempty; the zerodivisors on $M$ are exactly $\bigcup_{\mathfrak p\in\operatorname{Ass}M}\mathfrak p$; $\operatorname{Ass}M\subseteq\operatorname{Supp}M$ and every minimal element of $\operatorname{Supp}M$ lies in $\operatorname{Ass}M$; $\operatorname{Ass}$ of a submodule is contained in $\operatorname{Ass}M$; the annihilator of any nonzero $x\in M$ is contained in some member of $\operatorname{Ass}M$; and $\operatorname{Ass}$ commutes with localization, $\operatorname{Ass}_{A_\mathfrak p}M_\mathfrak p=\{\mathfrak qA_\mathfrak p:\mathfrak q\in\operatorname{Ass}M,\ \mathfrak q\subseteq\mathfrak p\}$.
3. **Prime avoidance**, in the version that permits two of the finitely many ideals to be arbitrary and requires the rest to be prime.
4. **Krull's height theorem.** A prime minimal over an ideal generated by $r$ elements has height at most $r$. In particular $\dim A\leq\dim_k\mathfrak m/\mathfrak m^2$ for a noetherian local ring, and $\dim M/xM\geq\dim M-1$ for $x\in\mathfrak m$ and $M$ finite, where $\dim M:=\dim A/\operatorname{Ann}M$.
5. **Ext.** Long exact sequences in both variables, the identification $\operatorname{Ext}^0=\operatorname{Hom}$, compatibility with finite direct sums, and the fact that $\operatorname{Ext}^i_A(N,M)$ is killed by $\operatorname{Ann}N$, so that the map induced by multiplication by $a\in\operatorname{Ann}N$ on $M$ is zero.
6. **Resolutions.** Schanuel's lemma, and the existence of minimal free resolutions of finite modules over a noetherian local ring.
7. **Completion.** For a noetherian local ring $A$ the completion $\widehat A$ is flat over $A$, $\widehat M\simeq M\otimes_A\widehat A$ for finite $M$, $\widehat A/\mathfrak m\widehat A=A/\mathfrak m$, $\dim\widehat A=\dim A$, and $\mathfrak m/\mathfrak m^2\simeq\widehat{\mathfrak m}/\widehat{\mathfrak m}^2$.
8. **Tor.** Long exact sequences in both variables, the identification $\operatorname{Tor}_0=\otimes$, computability of $\operatorname{Tor}^A_i(M,N)$ from a projective resolution of either argument, compatibility with finite direct sums, and compatibility with localization: $\operatorname{Tor}^A_i(M,N)_{\mathfrak p}\simeq\operatorname{Tor}^{A_{\mathfrak p}}_i(M_{\mathfrak p},N_{\mathfrak p})$, and likewise $\operatorname{Ext}^i_A(M,N)_{\mathfrak p}\simeq\operatorname{Ext}^i_{A_{\mathfrak p}}(M_{\mathfrak p},N_{\mathfrak p})$ when $M$ is finite and $A$ is noetherian.

Throughout, $(A,\mathfrak m,k)$ denotes a noetherian local ring and modules are finite. The zero module is given depth $+\infty$; this convention only serves to make the exact-sequence formulas uniform, and every substantive statement below concerns nonzero modules.

### 14.1 Regular sequences and the depth invariant

Let $M$ be an $A$-module and $x_1,\ldots,x_n$ elements of $A$. The sequence is **weakly $M$-regular** if $x_i$ is a nonzerodivisor on $M/(x_1,\ldots,x_{i-1})M$ for $1\leq i\leq n$, and **$M$-regular** if in addition
$$
M/(x_1,\ldots,x_n)M\neq0.
$$

When $M$ is finite, nonzero, and all $x_i$ lie in $\mathfrak m$, the second condition is automatic by Nakayama, so over a local ring the two notions agree for sequences in the maximal ideal.

The first observation is that failure to start a regular sequence is an associated-prime statement.

**Lemma 14.1.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$. The following are equivalent.

1. No element of $\mathfrak m$ is a nonzerodivisor on $M$.
2. $\mathfrak m\in\operatorname{Ass}M$.
3. $\operatorname{Hom}_A(k,M)\neq0$.

**Proof.** The zerodivisors on $M$ form the union of the finitely many associated primes. If every element of $\mathfrak m$ is a zerodivisor, then $\mathfrak m\subseteq\bigcup_{\mathfrak p\in\operatorname{Ass}M}\mathfrak p$, so prime avoidance places $\mathfrak m$ inside one associated prime, which must then equal $\mathfrak m$. Conversely $\mathfrak m\in\operatorname{Ass}M$ makes every element of $\mathfrak m$ a zerodivisor. Finally $\mathfrak m=\operatorname{Ann}(x)$ for some $x\neq0$ exactly when the map $k\to M$, $1\mapsto x$, is a nonzero homomorphism. $\square$

**Lemma 14.2.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$ and let $x\in\mathfrak m$ be a nonzerodivisor on $M$. Then
$$
\dim M/xM=\dim M-1 .
$$

Consequently every $M$-regular sequence in $\mathfrak m$ has length at most $\dim M$.

**Proof.** Since $x$ is a nonzerodivisor on $M$, it lies in no associated prime of $M$, hence in no minimal element of $\operatorname{Supp}M$, because those minimal elements are associated primes. Let
$$
\mathfrak q_0\subsetneq\mathfrak q_1\subsetneq\cdots\subsetneq\mathfrak q_s
$$

be a chain of primes in $\operatorname{Supp}M/xM=\operatorname{Supp}M\cap V(x)$. Then $\mathfrak q_0$ lies in the closed set $\operatorname{Supp}M=V(\operatorname{Ann}M)$ and contains $x$, so it is not minimal there; choosing a minimal prime of $\operatorname{Supp}M$ below it lengthens the chain inside $\operatorname{Supp}M$. Hence $s+1\leq\dim M$, that is $\dim M/xM\leq\dim M-1$. The reverse inequality is Krull's height theorem. Iterating the equality along a regular sequence lowers the dimension by one at each step, and dimensions are nonnegative for nonzero modules, so the length is at most $\dim M$. $\square$

Let $I\subseteq A$ be an ideal with $IM\neq M$. The **depth of $M$ along $I$**, written $\operatorname{depth}(I,M)$, is the supremum of the lengths of $M$-regular sequences contained in $I$. For a local ring the **depth of $M$** is
$$
\operatorname{depth}M:=\operatorname{depth}(\mathfrak m,M),
$$

and $\operatorname{depth}A$ means the depth of $A$ as a module over itself. Nothing so far says that this supremum is attained by every maximal sequence, and that is the content of Theorem 14.6. The bridge is the following criterion; its proof is the standard induction obtained by applying $\operatorname{Hom}(-,M)$ to the Koszul complex of a maximal regular subsequence and using prime avoidance at the first nonzero Koszul homology.

**Theorem 14.3 (Rees).** Let $A$ be noetherian, $I\subseteq A$ an ideal, $M$ a finite $A$-module with $IM\neq M$, and $n\geq0$ an integer. The following are equivalent.

1. There is an $M$-regular sequence of length $n$ contained in $I$.
2. $\operatorname{Ext}^i_A(A/I,M)=0$ for all $i<n$.
3. $\operatorname{Ext}^i_A(N,M)=0$ for all $i<n$ and every finite nonzero $N$ with $\operatorname{Supp}N\subseteq V(I)$.

Only the equivalence of the first two conditions is used below, and it is used in both directions.

**Corollary 14.4.** With the hypotheses of Theorem 14.3,
$$
\operatorname{depth}(I,M)=\min\{i:\operatorname{Ext}^i_A(A/I,M)\neq0\},
$$

with the convention that the minimum of the empty set is $+\infty$. If $A$ is local and $I=\mathfrak m$, then
$$
\operatorname{depth}M=\min\{i:\operatorname{Ext}^i_A(k,M)\neq0\}\leq\dim M<\infty .
$$

**Proof.** Write $e$ for the displayed minimum. If $e<\infty$, then condition (2) of Theorem 14.3 holds with $n=e$, so an $M$-regular sequence of length $e$ exists in $I$ and $\operatorname{depth}(I,M)\geq e$. If $\operatorname{depth}(I,M)\geq n$ for some $n$, condition (1) holds for that $n$, so $\operatorname{Ext}^i(A/I,M)=0$ for $i<n$ and hence $e\geq n$. Both inequalities together give $e=\operatorname{depth}(I,M)$, including the case $e=\infty$, in which regular sequences of every length exist. In the local case Lemma 14.2 bounds all lengths by $\dim M$, so the supremum is finite and the minimum is attained. $\square$

The corollary already resolves the well-definedness question in the weak sense: depth is a genuine invariant, computed by an Ext index, and it is finite. The next section upgrades this to the statement that no maximal regular sequence can be short.

### 14.2 The depth calculus

**Theorem 14.5.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$ and let $x\in\mathfrak m$ be a nonzerodivisor on $M$. Then
$$
\operatorname{depth}M/xM=\operatorname{depth}M-1 .
$$

**Proof.** Write $d=\operatorname{depth}M$, which is at least $1$ because $x$ is a regular element in $\mathfrak m$, and at most $\dim M$ by Corollary 14.4. The short exact sequence
$$
0\longrightarrow M\xrightarrow{\ x\ }M\longrightarrow M/xM\longrightarrow0
$$

gives a long exact sequence of $\operatorname{Ext}^\bullet_A(k,-)$. Multiplication by $x$ on $\operatorname{Ext}^i_A(k,M)$ induced by the first map coincides with the map induced by multiplication by $x$ on $k$, which is zero because $x\in\mathfrak m=\operatorname{Ann}k$. The long exact sequence therefore breaks into short exact sequences
$$
0\longrightarrow\operatorname{Ext}^i_A(k,M)\longrightarrow\operatorname{Ext}^i_A(k,M/xM)\longrightarrow\operatorname{Ext}^{i+1}_A(k,M)\longrightarrow0
$$

for every $i\geq0$. For $i<d-1$ both outer terms vanish, so $\operatorname{Ext}^i(k,M/xM)=0$. For $i=d-1$ the left term vanishes and the right term is $\operatorname{Ext}^d(k,M)\neq0$, so $\operatorname{Ext}^{d-1}(k,M/xM)\neq0$. By Corollary 14.4 the depth of $M/xM$ is $d-1$. $\square$

**Theorem 14.6.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$ and let $x_1,\ldots,x_n\in\mathfrak m$ be an $M$-regular sequence that cannot be extended to an $M$-regular sequence $x_1,\ldots,x_{n+1}$ in $\mathfrak m$. Then $n=\operatorname{depth}M$. In particular all maximal $M$-regular sequences in $\mathfrak m$ have the same length, namely $\operatorname{depth}M$.

**Proof.** Induction on $n$. If $n=0$, maximality says that no element of $\mathfrak m$ is a nonzerodivisor on $M$, so $\operatorname{Hom}(k,M)\neq0$ by Lemma 14.1 and $\operatorname{depth}M=0$ by Corollary 14.4. If $n\geq1$, then $x_1$ is a nonzerodivisor on $M$ and $x_2,\ldots,x_n$ is a maximal $M/x_1M$-regular sequence in $\mathfrak m$: an extension of the latter would extend the former. By induction $n-1=\operatorname{depth}M/x_1M$, and Theorem 14.5 gives $\operatorname{depth}M/x_1M=\operatorname{depth}M-1$. $\square$

Thus the depth may be computed by any greedy choice of regular elements, and the Ext description is only needed to know that greed cannot go wrong. The same description gives the behavior along short exact sequences.

**Lemma 14.7.** Let $0\to M'\to M\to M''\to0$ be exact with all three modules finite over $(A,\mathfrak m,k)$. Then
$$
\operatorname{depth}M\geq\min\{\operatorname{depth}M',\operatorname{depth}M''\},
$$

$$
\operatorname{depth}M'\geq\min\{\operatorname{depth}M,\operatorname{depth}M''+1\},
$$

$$
\operatorname{depth}M''\geq\min\{\operatorname{depth}M,\operatorname{depth}M'-1\}.
$$

Moreover, if $\operatorname{depth}M''<\operatorname{depth}M'$, then $\operatorname{depth}M=\operatorname{depth}M''$, and if $\operatorname{depth}M'>\operatorname{depth}M$, then $\operatorname{depth}M''=\operatorname{depth}M$.

**Proof.** All statements read off the long exact sequence
$$
\cdots\to\operatorname{Ext}^i(k,M')\to\operatorname{Ext}^i(k,M)\to\operatorname{Ext}^i(k,M'')\to\operatorname{Ext}^{i+1}(k,M')\to\cdots
$$

together with Corollary 14.4, which identifies the depth of a module with the first index at which $\operatorname{Ext}^\bullet(k,-)$ is nonzero. If $i<\min\{\operatorname{depth}M',\operatorname{depth}M''\}$, the two neighbors of $\operatorname{Ext}^i(k,M)$ vanish, so it vanishes; this is the first inequality. If $i<\min\{\operatorname{depth}M,\operatorname{depth}M''+1\}$, then $\operatorname{Ext}^i(k,M)=0$ and $\operatorname{Ext}^{i-1}(k,M'')=0$, and exactness of
$$
\operatorname{Ext}^{i-1}(k,M'')\to\operatorname{Ext}^i(k,M')\to\operatorname{Ext}^i(k,M)
$$

gives $\operatorname{Ext}^i(k,M')=0$; this is the second inequality. For the third, let $i<\min\{\operatorname{depth}M,\operatorname{depth}M'-1\}$; then $\operatorname{Ext}^i(k,M)=0$ and $\operatorname{Ext}^{i+1}(k,M')=0$, and exactness of
$$
\operatorname{Ext}^{i}(k,M)\to\operatorname{Ext}^i(k,M'')\to\operatorname{Ext}^{i+1}(k,M')
$$

gives $\operatorname{Ext}^i(k,M'')=0$. For the refinements, suppose $\operatorname{depth}M''<\operatorname{depth}M'$ and put $i=\operatorname{depth}M''$. Then $\operatorname{Ext}^j(k,M)=0$ for $j<i$ by the first inequality, while
$$
0=\operatorname{Ext}^i(k,M')\to\operatorname{Ext}^i(k,M)\to\operatorname{Ext}^i(k,M'')\to\operatorname{Ext}^{i+1}(k,M')=0
$$

shows $\operatorname{Ext}^i(k,M)\simeq\operatorname{Ext}^i(k,M'')\neq0$. Similarly, if $\operatorname{depth}M'>\operatorname{depth}M=:i$, then $\operatorname{Ext}^j(k,M'')=0$ for $j<i$ by the third inequality applied index by index, and
$$
0=\operatorname{Ext}^i(k,M')\to\operatorname{Ext}^i(k,M)\to\operatorname{Ext}^i(k,M'')
$$

is injective on a nonzero module, so $\operatorname{Ext}^i(k,M'')\neq0$. $\square$

One consequence will be used repeatedly: a nonzero submodule $M'\subseteq M$ satisfies $\operatorname{Ass}M'\subseteq\operatorname{Ass}M$, so if $\operatorname{depth}M'=0$ then $\mathfrak m\in\operatorname{Ass}M$ and $\operatorname{depth}M=0$. Contrapositively, submodules of modules of positive depth have positive depth.

Depth is insensitive to two changes of ring that occur constantly in the geometry of models: passing to a finite local algebra, and completing.

**Proposition 14.8.** Let $(A,\mathfrak m)\to(B,\mathfrak n)$ be a local homomorphism of noetherian local rings with $B$ finite as an $A$-module, and let $M\neq0$ be a finite $B$-module. Then
$$
\operatorname{depth}_AM=\operatorname{depth}_BM .
$$

**Proof.** First suppose $\operatorname{depth}_AM=0$, so some $0\neq y\in M$ is killed by $\mathfrak m$. Then $By$ is a nonzero finite module over $B/\mathfrak mB$, which is a local ring whose maximal ideal $\mathfrak n/\mathfrak mB$ is nilpotent, because $B/\mathfrak mB$ is a finite-dimensional algebra over $k=A/\mathfrak m$ and hence artinian local. Choose $r$ maximal with $\mathfrak n^rBy\neq0$; any nonzero element of $\mathfrak n^rBy$ is killed by $\mathfrak n$, so $\operatorname{depth}_BM=0$ by Lemma 14.1. Conversely, if $\operatorname{depth}_BM=0$, some nonzero element is killed by $\mathfrak n\supseteq\mathfrak m$, so $\operatorname{depth}_AM=0$.

Now induct on $\operatorname{depth}_AM$. If it is positive, then by the previous paragraph $\operatorname{depth}_BM$ is positive as well; choose $x\in\mathfrak m$ a nonzerodivisor on $M$, which is also an element of $\mathfrak n$ and a nonzerodivisor on $M$ over $B$. Theorem 14.5, applied over $A$ and over $B$, reduces the claim to $M/xM$, whose $A$-depth is smaller by one. $\square$

**Proposition 14.9.** Let $M\neq0$ be finite over the noetherian local ring $(A,\mathfrak m,k)$ and let $\widehat A$, $\widehat M$ denote the $\mathfrak m$-adic completions. Then
$$
\operatorname{depth}_{\widehat A}\widehat M=\operatorname{depth}_AM .
$$

**Proof.** Induct on $d=\operatorname{depth}_AM$. If $d=0$, Lemma 14.1 gives an injection $k\hookrightarrow M$; tensoring with the flat $A$-algebra $\widehat A$ gives an injection $\widehat A/\mathfrak m\widehat A\hookrightarrow\widehat M$, and $\widehat A/\mathfrak m\widehat A$ is the residue field of $\widehat A$, so $\operatorname{depth}_{\widehat A}\widehat M=0$. If $d\geq1$, choose $x\in\mathfrak m$ a nonzerodivisor on $M$. Flatness of $\widehat A$ preserves the injectivity of multiplication by $x$, so $x$ is a nonzerodivisor on $\widehat M$, and $\widehat A$-flatness identifies $\widehat{M/xM}$ with $\widehat M/x\widehat M$. By induction the latter has depth $d-1$, so Theorem 14.5 gives $\operatorname{depth}_{\widehat A}\widehat M=d$. $\square$

No comparison between $\operatorname{depth}A$ and $\operatorname{depth}A_{\mathfrak p}$ is asserted here, and none is used. The conditions $(S_r)$ below quantify over all primes precisely because depth at the closed point does not control depth after localization.

### 14.3 The Auslander–Buchsbaum formula

Recall that $\operatorname{pd}_AM$, the projective dimension, is the least length of a projective resolution of $M$, or $\infty$. Over a local ring the minimal free resolution computes it: $\operatorname{pd}_AM=0$ means exactly that $M$ is free.

**Lemma 14.10.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$ with $p=\operatorname{pd}_AM\geq1$ finite, and let $0\to N\to F\to M\to0$ be exact with $F$ finite free and $F\to M$ a minimal cover, that is, an isomorphism modulo $\mathfrak m$. Then $N\subseteq\mathfrak mF$, $N\neq0$, and $\operatorname{pd}_AN=p-1$.

**Proof.** Minimality of the cover means $F\otimes k\to M\otimes k$ is an isomorphism, so $N\subseteq\mathfrak mF$; and $N\neq0$ because $M$ is not free. Take any projective resolution of $M$ of length $p$ and let $N'$ be its first syzygy, so $\operatorname{pd}N'\leq p-1$. Schanuel's lemma gives $N\oplus P'\simeq N'\oplus P$ with $P,P'$ finite free, and adding free summands changes no projective dimension, so $\operatorname{pd}N=\operatorname{pd}N'\leq p-1$. Conversely, splicing a projective resolution of $N$ of length $\operatorname{pd}N$ with $F$ produces one of $M$ of length $\operatorname{pd}N+1$, whence $p\leq\operatorname{pd}N+1$. The two inequalities give $\operatorname{pd}N=p-1$. $\square$

**Lemma 14.11.** If $\operatorname{depth}A=0$ and $M\neq0$ is finite with $\operatorname{pd}_AM<\infty$, then $M$ is free.

**Proof.** Suppose $p=\operatorname{pd}_AM\geq1$ and take a minimal free resolution
$$
0\to F_p\xrightarrow{\ \varphi\ }F_{p-1}\to\cdots\to F_0\to M\to0 ,
$$

so that $\varphi$ is injective and $\varphi(F_p)\subseteq\mathfrak mF_{p-1}$, and $F_p\neq0$. Since $\operatorname{depth}A=0$, Lemma 14.1 supplies $a\neq0$ in $A$ with $a\mathfrak m=0$. Choose $0\neq u\in F_p$. Then $au\neq0$ because $F_p$ is free and $a\neq0$, while
$$
\varphi(au)=a\varphi(u)\in a\mathfrak mF_{p-1}=0,
$$

contradicting injectivity of $\varphi$. Hence $p=0$ and $M$ is free. $\square$

**Theorem 14.12 (the Auslander–Buchsbaum formula).** Let $M\neq0$ be a finite module of finite projective dimension over the noetherian local ring $(A,\mathfrak m,k)$. Then
$$
\operatorname{pd}_AM+\operatorname{depth}M=\operatorname{depth}A .
$$

**Proof.** Write $d=\operatorname{depth}A$ and induct on $p=\operatorname{pd}_AM$.

If $p=0$ then $M\simeq A^r$ with $r\geq1$, and $\operatorname{Ext}^i(k,A^r)=\operatorname{Ext}^i(k,A)^r$ shows $\operatorname{depth}M=d$ by Corollary 14.4.

Let $p\geq1$. By Lemma 14.11, $d\geq1$, since otherwise $M$ would be free. Choose a minimal cover and let
$$
0\to N\to F\to M\to0
$$

be as in Lemma 14.10, so $N\neq0$, $N\subseteq\mathfrak mF$, and $\operatorname{pd}N=p-1$. By induction
$$
n:=\operatorname{depth}N=d-p+1 .
$$

Since $N$ is a nonzero submodule of the free module $F$, and $\operatorname{depth}F=d\geq1$, the remark after Lemma 14.7 gives $n\geq1$.

Suppose first $p\geq2$, so $n=d-p+1<d$. In the long exact sequence
$$
\operatorname{Ext}^i(k,F)\to\operatorname{Ext}^i(k,M)\to\operatorname{Ext}^{i+1}(k,N)\to\operatorname{Ext}^{i+1}(k,F)
$$

take $i<n-1$: both flanking terms vanish, because $i<n\leq d$ and $i+1<n$, so $\operatorname{Ext}^i(k,M)=0$. Taking $i=n-1$: the term $\operatorname{Ext}^{n-1}(k,F)$ vanishes since $n-1<d$, and $\operatorname{Ext}^{n}(k,F)$ vanishes since $n<d$, so
$$
\operatorname{Ext}^{n-1}(k,M)\simeq\operatorname{Ext}^{n}(k,N)\neq0 .
$$

Hence $\operatorname{depth}M=n-1=d-p$, as required.

Now suppose $p=1$. Then $\operatorname{pd}N=0$, so $N$ is free of some rank $r\geq1$ and $\operatorname{depth}N=d$. For $i<d-1$ the same long exact sequence gives $\operatorname{Ext}^i(k,M)=0$, since $\operatorname{Ext}^i(k,F)=0$ and $\operatorname{Ext}^{i+1}(k,N)=0$. At $i=d-1$ the sequence reads
$$
0=\operatorname{Ext}^{d-1}(k,F)\to\operatorname{Ext}^{d-1}(k,M)\to\operatorname{Ext}^{d}(k,N)\xrightarrow{\ \alpha\ }\operatorname{Ext}^{d}(k,F),
$$

where $\alpha$ is induced by the inclusion $N\subseteq\mathfrak mF$. Writing $N\simeq A^r$ and $F\simeq A^s$, the inclusion is given by an $s\times r$ matrix with all entries in $\mathfrak m$, and by additivity of $\operatorname{Ext}$ the map $\alpha$ is given by the same matrix of scalars acting on $\operatorname{Ext}^{d}(k,A)^r\to\operatorname{Ext}^{d}(k,A)^s$. Every $\operatorname{Ext}^i(k,A)$ is killed by $\mathfrak m$, so $\alpha=0$. Since $\operatorname{Ext}^{d}(k,N)=\operatorname{Ext}^{d}(k,A)^r\neq0$, exactness gives $\operatorname{Ext}^{d-1}(k,M)\neq0$ and therefore $\operatorname{depth}M=d-1=d-p$. $\square$

**Corollary 14.13.** Let $M\neq0$ be finite of finite projective dimension over $(A,\mathfrak m,k)$. Then $\operatorname{pd}_AM\leq\operatorname{depth}A$, and $M$ is free if and only if $\operatorname{depth}M=\operatorname{depth}A$.

**Proof.** Both statements are immediate from Theorem 14.12, using that depth is nonnegative and that $\operatorname{pd}=0$ characterizes freeness over a local ring. $\square$

Two independent checks confirm the formula's shape. If $x\in\mathfrak m$ is a nonzerodivisor on $M$, then $\operatorname{depth}M/xM=\operatorname{depth}M-1$ by Theorem 14.5, while the projective dimension satisfies $\operatorname{pd}M/xM=\operatorname{pd}M+1$; the two shifts cancel, so the Auslander–Buchsbaum sum is unchanged by cutting with a regular element, exactly as the formula demands. Likewise, if $x_1,\ldots,x_c$ is an $A$-regular sequence in $\mathfrak m$, then $\operatorname{pd}_AA/(x_1,\ldots,x_c)=c$, and Theorem 14.12 recovers $\operatorname{depth}A/(x_1,\ldots,x_c)=\operatorname{depth}A-c$, which Theorem 14.5 also gives directly. Both projective-dimension identities follow by tensoring a free resolution with the two-term complex $[A\xrightarrow{x}A]$ and iterating.

### 14.4 Cohen–Macaulay local rings

A noetherian local ring $A$ is **Cohen–Macaulay** if
$$
\operatorname{depth}A=\dim A .
$$

By Corollary 14.4 the inequality $\operatorname{depth}A\leq\dim A$ always holds, so the condition asks that the algebraic count of independent regular parameters achieve the geometric dimension. A noetherian ring is Cohen–Macaulay if $A_{\mathfrak p}$ is Cohen–Macaulay for every prime $\mathfrak p$. No localization theorem is assumed: in every example below the Cohen–Macaulay property is verified at all primes directly.

The basic example is a regular local ring, but for that one first needs two structural facts.

**Lemma 14.14.** Let $A$ be regular local of dimension $n\geq1$ and let $x\in\mathfrak m\setminus\mathfrak m^2$. Then $A/(x)$ is regular local of dimension $n-1$.

**Proof.** Because $x\notin\mathfrak m^2$, its residue is part of a basis of $\mathfrak m/\mathfrak m^2$, so $x$ belongs to a minimal generating set $x,y_2,\ldots,y_n$ of $\mathfrak m$ by Nakayama. Hence the maximal ideal of $A/(x)$ is generated by $n-1$ elements, and Krull's height theorem gives $\dim A/(x)\leq n-1$. The same theorem gives $\dim A/(x)\geq n-1$. Thus $\dim A/(x)=n-1$ equals the number of generators of its maximal ideal, which is regularity. $\square$

**Proposition 14.15.** A regular local ring is a domain.

**Proof.** Induct on $n=\dim A$. If $n=0$, then $\mathfrak m$ is generated by the empty set, so $\mathfrak m=0$ and $A$ is a field. Let $n\geq1$ and let $\mathfrak p_1,\ldots,\mathfrak p_r$ be the minimal primes of $A$. Each is properly contained in $\mathfrak m$ because $\dim A\geq1$, and $\mathfrak m\neq\mathfrak m^2$ by Nakayama. Prime avoidance, in the version allowing one non-prime member, produces
$$
x\in\mathfrak m\setminus\bigl(\mathfrak m^2\cup\mathfrak p_1\cup\cdots\cup\mathfrak p_r\bigr).
$$

By Lemma 14.14 the ring $A/(x)$ is regular of dimension $n-1$, hence a domain by induction, so $(x)$ is a prime ideal. Since $x$ lies in no minimal prime, there is a minimal prime $\mathfrak q\subsetneq(x)$. For $a\in\mathfrak q$ write $a=bx$; as $x\notin\mathfrak q$ and $\mathfrak q$ is prime, $b\in\mathfrak q$. Hence $\mathfrak q=x\mathfrak q\subseteq\mathfrak m\mathfrak q$, and Nakayama gives $\mathfrak q=0$. So $A$ has a unique minimal prime, equal to $0$, and $A$ is a domain. $\square$

**Theorem 14.16.** Let $A$ be regular local of dimension $n$. Then every minimal generating sequence $x_1,\ldots,x_n$ of $\mathfrak m$ is $A$-regular, and
$$
\operatorname{depth}A=\dim A=n .
$$

In particular regular local rings are Cohen–Macaulay, and a regular ring is Cohen–Macaulay.

**Proof.** Induct on $n$. For $n=0$ there is nothing to prove. For $n\geq1$, the element $x_1$ lies outside $\mathfrak m^2$, so it is nonzero and hence a nonzerodivisor by Proposition 14.15, and $A/(x_1)$ is regular of dimension $n-1$ by Lemma 14.14 with minimal generating sequence the residues of $x_2,\ldots,x_n$. By induction those form a regular sequence, so $x_1,\ldots,x_n$ is $A$-regular and $\operatorname{depth}A\geq n$. Corollary 14.4 gives the reverse inequality. The last sentence follows because localizations of a regular ring at primes are regular local by definition. $\square$

**Proposition 14.17.** Let $A$ be Cohen–Macaulay local and let $x_1,\ldots,x_c\in\mathfrak m$ be an $A$-regular sequence. Then $A/(x_1,\ldots,x_c)$ is Cohen–Macaulay of dimension $\dim A-c$.

**Proof.** By induction it suffices to treat $c=1$. Theorem 14.5 gives $\operatorname{depth}A/(x)=\operatorname{depth}A-1$, where the depth of $A/(x)$ as an $A$-module equals its depth as a ring by Proposition 14.8 applied to $A\to A/(x)$. Lemma 14.2 gives $\dim A/(x)=\dim A-1$. Subtracting equal quantities from an equality preserves it. $\square$

**Corollary 14.18.** Let $P$ be a regular local ring of dimension $n$ and $0\neq f\in\mathfrak n=\mathfrak m_P$. Then $A=P/(f)$ is Cohen–Macaulay of dimension $n-1$, and $A$ is regular if and only if $f\notin\mathfrak n^2$. More generally, if $f_1,\ldots,f_c\in\mathfrak n$ is a $P$-regular sequence, then $P/(f_1,\ldots,f_c)$ is Cohen–Macaulay of dimension $n-c$.

**Proof.** $P$ is a domain by Proposition 14.15, so $f\neq0$ is a nonzerodivisor and Proposition 14.17 applies with Theorem 14.16. For the regularity criterion, $\dim A=n-1$ while the maximal ideal of $A$ needs $\dim_k\mathfrak n/(\mathfrak n^2+(f))$ generators, which is $n-1$ when $f\notin\mathfrak n^2$ and $n$ otherwise. The last sentence is Proposition 14.17 again. $\square$

Since depth and dimension are unchanged by completion — the first by Proposition 14.9, the second by the standing completion facts — and since $\mathfrak m/\mathfrak m^2$ is unchanged as well, a noetherian local ring is Cohen–Macaulay, respectively regular, if and only if its completion is. This is how the completed local equations of Section 12.4 will be read.

The examples that matter for this book are hypersurfaces, and for them the passage from a local statement to a statement at every prime is easy.

**Proposition 14.19.** Let $P$ be a regular noetherian ring, let $f\in P$ be a nonzerodivisor, and put $A=P/(f)$. Then $A_{\mathfrak q}$ is Cohen–Macaulay for every prime $\mathfrak q$ of $A$; in particular $A$ satisfies $(S_r)$ for every $r$. If moreover $A_{\mathfrak q}$ is regular for every prime $\mathfrak q$ of height at most one, then $A$ is normal.

**Proof.** A prime of $A$ is $\mathfrak q=\mathfrak p/(f)$ for a prime $\mathfrak p\supseteq(f)$ of $P$, and $A_{\mathfrak q}=P_{\mathfrak p}/fP_{\mathfrak p}$. Here $P_{\mathfrak p}$ is regular local because $P$ is a regular ring, and the image of $f$ lies in its maximal ideal and is nonzero, because a nonzerodivisor stays a nonzerodivisor after localization and $P_{\mathfrak p}\neq0$. Corollary 14.18 makes $A_{\mathfrak q}$ Cohen–Macaulay. Consequently
$$
\operatorname{depth}A_{\mathfrak q}=\dim A_{\mathfrak q}\geq\min\{r,\dim A_{\mathfrak q}\}
$$

for every $r$, which is $(S_r)$. The regularity hypothesis in the last sentence is $(R_1)$, so Theorem 14.26 below gives normality. $\square$

**Theorem 14.20 (the semistable local models).** Let $R$ be a discrete valuation ring with uniformizer $\pi$ and residue field $k$, let $n\geq1$, and set
$$
B_n=R[x,y]/(xy-\pi^n),\qquad
\mathfrak n=(\pi,x,y).
$$

Then:

1. $(B_n)_{\mathfrak q}$ is Cohen–Macaulay for every prime $\mathfrak q$, and $(B_n)_{\mathfrak n}$ has dimension two;
2. $(B_n)_{\mathfrak q}$ is regular for every prime $\mathfrak q\neq\mathfrak n$;
3. $(B_n)_{\mathfrak n}$ is regular if and only if $n=1$;
4. $B_n$ is normal for every $n\geq1$.

**Proof.** The ring $P=R[x,y]$ is regular. Indeed $R$ is a regular ring: its localizations are the field $\operatorname{Frac}R$, of dimension zero, and $R$ itself, whose maximal ideal is principal of height one. Polynomial algebras over regular noetherian rings are regular, which gives $P$. The element $f=xy-\pi^n$ is nonzero in the domain $P$, hence a nonzerodivisor, and $P/(f)=B_n$.

Statement (1) is now Proposition 14.19, apart from the dimension count at $\mathfrak n$, which is the following. In $P$ the ideal $\mathfrak N=(\pi,x,y)$ is maximal with $P/\mathfrak N=k$, and the chain
$$
0\subsetneq(\pi)\subsetneq(\pi,x)\subsetneq(\pi,x,y)
$$

consists of primes, since the successive quotients $k[x,y]$, $k[y]$, $k$ are domains. Hence $\operatorname{ht}\mathfrak N\geq3$, while Krull's height theorem gives $\operatorname{ht}\mathfrak N\leq3$ because $\mathfrak N$ has three generators. So $P_{\mathfrak N}$ is regular local of dimension three, and Corollary 14.18 makes $(B_n)_{\mathfrak n}=P_{\mathfrak N}/(f)$ Cohen–Macaulay of dimension two.

For (2), let $\mathfrak q$ be a prime of $B_n$ other than $\mathfrak n$. If $x,y\in\mathfrak q$ then $\pi^n=xy\in\mathfrak q$, so $\pi\in\mathfrak q$ and $\mathfrak q\supseteq\mathfrak n$, forcing $\mathfrak q=\mathfrak n$ because $\mathfrak n$ is maximal. Hence $x\notin\mathfrak q$ or $y\notin\mathfrak q$, and $(B_n)_{\mathfrak q}$ is a localization of $B_n[1/x]$ or of $B_n[1/y]$. Now
$$
B_n[1/x]=R[x,1/x][y]/(xy-\pi^n)\simeq R[x,1/x],
$$

because $xy-\pi^n=x\,(y-\pi^nx^{-1})$ and $x$ is a unit, so the quotient identifies $y$ with $\pi^nx^{-1}$. The right-hand side is a localization of the regular ring $R[x]$, hence a regular ring, and so are its localizations. The same computation applies with $x$ and $y$ exchanged. Thus $(B_n)_{\mathfrak q}$ is regular.

For (3), $f=xy-\pi^n$ lies in $\mathfrak N^2$ exactly when $n\geq2$, since $xy\in\mathfrak N^2$ always and $\pi^n\in\mathfrak N^2$ if and only if $n\geq2$; apply the criterion of Corollary 14.18.

For (4), by (2) the only prime at which $B_n$ can fail to be regular is $\mathfrak n$, whose height is two by the computation above. So $(R_1)$ holds, and (1) gives $(S_2)$; Proposition 14.19 concludes. $\square$

Part (3) is the local reason for the running example of Sections 4.3, 4.4, and 11.4: the semistable equation $xy=\pi$ has regular total space, while $xy=\pi^n$ with $n\geq2$ does not. Part (4) says that the singular members of the family are nevertheless normal, so normalization is powerless against them and only the blowups of Section 8.5 remove them. This is exactly the situation created by ramified base change in Section 10.4, where $xy=\pi$ becomes $xy=w(\pi')^e$ for a unit $w$: after absorbing $w$ into one of the coordinates, the base-changed surface is one of the $B_e$ above, normal and Cohen–Macaulay but no longer regular when $e\geq2$, and its repair is a resolution, not a normalization.

**Example.** The quadratic cone of Section 4.3, $A=k[x,y,z]/(xy-z^2)$ over a field of characteristic different from two, is handled by the same three steps. The ring $P=k[x,y,z]$ is regular, since a field is a regular ring and polynomial algebras over regular noetherian rings are regular, and $f=xy-z^2$ is a nonzerodivisor in the domain $P$; so all localizations of $A$ are Cohen–Macaulay by Proposition 14.19 and $(S_2)$ holds. A prime of $A$ containing $x$ and $y$ contains $z^2$, hence $z$, hence the maximal ideal $\mathfrak v=(x,y,z)$. As in Theorem 14.20, $P_{(x,y,z)}$ is regular local of dimension three, so $A_{\mathfrak v}$ has dimension two and $\mathfrak v$ has height two. Every other prime survives in $A[1/x]\simeq k[x,1/x,z]$ or in the symmetric localization $A[1/y]$, both of them localizations of polynomial algebras over $k$ and hence regular. Thus $(R_1)$ holds and $A$ is normal, while $f\in\mathfrak v^2$ shows by Corollary 14.18 that $A$ is not regular at the vertex. This completes the assertion made in Section 4.3.

### 14.5 Serre's conditions and the normality criterion

Let $A$ be a noetherian ring and $r\geq0$ an integer. Condition $(R_r)$ says that $A_{\mathfrak p}$ is regular for every prime with $\operatorname{ht}\mathfrak p\leq r$. Condition $(S_r)$ says that
$$
\operatorname{depth}A_{\mathfrak p}\geq\min\{r,\dim A_{\mathfrak p}\}
$$

for every prime $\mathfrak p$. Both conditions are inherited by localizations: the primes of $A_{\mathfrak p}$ are the $\mathfrak qA_{\mathfrak p}$ with $\mathfrak q\subseteq\mathfrak p$, their heights agree with the heights of $\mathfrak q$ in $A$, and $(A_{\mathfrak p})_{\mathfrak qA_{\mathfrak p}}=A_{\mathfrak q}$. Note also that $(R_1)$ implies $(R_0)$ and that $(S_2)$ implies $(S_1)$.

**Proposition 14.21.** A noetherian ring $A$ satisfies $(S_1)$ if and only if every associated prime of $A$ is a minimal prime.

**Proof.** For a prime $\mathfrak p$, the localization compatibility of associated primes gives $\mathfrak pA_{\mathfrak p}\in\operatorname{Ass}A_{\mathfrak p}$ precisely when $\mathfrak p\in\operatorname{Ass}A$, and by Lemma 14.1 this happens precisely when $\operatorname{depth}A_{\mathfrak p}=0$. Also $\dim A_{\mathfrak p}=0$ precisely when $\mathfrak p$ is minimal. So $(S_1)$, which asserts that $\operatorname{depth}A_{\mathfrak p}=0$ forces $\dim A_{\mathfrak p}=0$, says exactly that associated primes are minimal. $\square$

**Theorem 14.22.** A noetherian ring is reduced if and only if it satisfies $(R_0)$ and $(S_1)$.

**Proof.** Suppose $A$ is reduced. For a minimal prime $\mathfrak p$, the ring $A_{\mathfrak p}$ is reduced with a unique prime ideal, which is therefore its nilradical and hence zero; so $A_{\mathfrak p}$ is a field and $(R_0)$ holds. For $(S_1)$, let $\mathfrak p\in\operatorname{Ass}A$ and localize: $A_{\mathfrak p}$ is reduced and $\mathfrak pA_{\mathfrak p}=\operatorname{Ann}(a)$ for some $a\neq0$. If $a\in\mathfrak pA_{\mathfrak p}$, then $a^2=0$, contradicting reducedness; so $a$ is a unit in the local ring $A_{\mathfrak p}$ and $\mathfrak pA_{\mathfrak p}=\operatorname{Ann}(a)=0$. Thus $A_{\mathfrak p}$ is a field, $\mathfrak p$ is minimal, and Proposition 14.21 gives $(S_1)$.

Conversely assume $(R_0)$ and $(S_1)$. Consider the map
$$
A\longrightarrow\prod_{\mathfrak p\in\operatorname{Min}A}A_{\mathfrak p}.
$$

If $a\neq0$, its annihilator is contained in some associated prime $\mathfrak p$, which is minimal by Proposition 14.21; since no element outside $\mathfrak p$ annihilates $a$, the image of $a$ in $A_{\mathfrak p}$ is nonzero. Hence the map is injective. By $(R_0)$ each factor is a field, so the product is reduced, and therefore so is $A$. $\square$

The next theorem is the $(S_2)$ half of Serre's criterion, and it is the statement that Section 4.1 used without proof.

**Theorem 14.23.** Let $A$ be a noetherian local domain that is integrally closed in its fraction field. Then
$$
\operatorname{depth}A\geq\min\{2,\dim A\}.
$$

**Proof.** If $\dim A=0$ there is nothing to prove. If $\dim A\geq1$, then $\mathfrak m\neq0$ and any nonzero element of $\mathfrak m$ is a nonzerodivisor, so $\operatorname{depth}A\geq1$.

Assume $\dim A\geq2$ and suppose $\operatorname{depth}A=1$. Choose a nonzero $a\in\mathfrak m$. It is a nonzerodivisor, and it cannot be extended to an $A$-regular sequence of length two, since $\operatorname{depth}A=1$ is the supremum of the lengths. So every element of $\mathfrak m$ is a zerodivisor on $A/aA$, and Lemma 14.1 gives $\mathfrak m\in\operatorname{Ass}(A/aA)$. Thus there is $b\in A\setminus aA$ with $b\mathfrak m\subseteq aA$. Put
$$
u=\frac ba\in\operatorname{Frac}(A),\qquad u\notin A,\qquad u\mathfrak m\subseteq A .
$$

The set $u\mathfrak m$ is an ideal of $A$, so either $u\mathfrak m\subseteq\mathfrak m$ or $u\mathfrak m=A$.

In the first case multiplication by $u$ is an endomorphism of the finite faithful $A$-module $\mathfrak m$, and the determinant trick produces a monic equation for $u$ over $A$. Integral closedness forces $u\in A$, a contradiction.

In the second case $u\neq0$ and $\mathfrak m=u^{-1}A=(a/b)A$ is principal. Krull's height theorem then bounds $\dim A=\operatorname{ht}\mathfrak m$ by one, contradicting $\dim A\geq2$. $\square$

**Theorem 14.24.** Let $A$ be a noetherian domain satisfying $(S_2)$, with fraction field $K$. Then
$$
A=\bigcap_{\operatorname{ht}\mathfrak p=1}A_{\mathfrak p}\qquad\text{inside }K .
$$

**Proof.** The inclusion from left to right is clear. Let $x=b/a$ with $a\neq0$ lie in $A_{\mathfrak p}$ for every height-one prime $\mathfrak p$; we must show $b\in aA$.

First, every associated prime of $A/aA$ has height one. Indeed, let $\mathfrak q\in\operatorname{Ass}(A/aA)$. Since $A$ is a domain and $a\neq0$, every prime containing $a$ has height at least one, and $\operatorname{ht}\mathfrak q\geq1$. If $\operatorname{ht}\mathfrak q\geq2$, then $\dim A_{\mathfrak q}\geq2$ and $(S_2)$ gives $\operatorname{depth}A_{\mathfrak q}\geq2$; but $\mathfrak q\in\operatorname{Ass}(A/aA)$ localizes to $\mathfrak qA_{\mathfrak q}\in\operatorname{Ass}(A_{\mathfrak q}/aA_{\mathfrak q})$, so $\operatorname{depth}A_{\mathfrak q}/aA_{\mathfrak q}=0$ by Lemma 14.1, and Theorem 14.5 gives $\operatorname{depth}A_{\mathfrak q}=1$, a contradiction.

Now suppose the residue $\bar b\in A/aA$ is nonzero. Its annihilator $(aA:b)$ is contained in some associated prime $\mathfrak q$ of $A/aA$, which has height one by the previous paragraph. But $x\in A_{\mathfrak q}$ means $b/1\in aA_{\mathfrak q}$, that is, $sb\in aA$ for some $s\notin\mathfrak q$; then $s\in(aA:b)\subseteq\mathfrak q$, a contradiction. Hence $\bar b=0$ and $x\in A$. $\square$

**Lemma 14.25.** A noetherian local ring satisfying $(R_1)$ and $(S_2)$ is a domain.

**Proof.** By Theorem 14.22 the ring $A$ is reduced, since $(R_1)$ implies $(R_0)$ and $(S_2)$ implies $(S_1)$. Suppose $A$ has at least two minimal primes and let $\mathfrak p_1,\ldots,\mathfrak p_t$, $t\geq2$, be the complete list. Put
$$
I=\mathfrak p_1,\qquad J=\mathfrak p_2\cap\cdots\cap\mathfrak p_t .
$$

Then $I\cap J$ is the nilradical, hence zero, and $I+J\subseteq\mathfrak m$ is a proper ideal. The sequence
$$
0\to A\to A/I\oplus A/J\to A/(I+J)\to0,
\qquad a\mapsto(a,a),\quad(b,c)\mapsto b-c,
$$

is exact. Let $\mathfrak q$ be a prime minimal over $I+J$ and localize at $\mathfrak q$; localization is exact, and $(A/(I+J))_{\mathfrak q}$ is nonzero with support the single prime $\mathfrak qA_{\mathfrak q}$, because $\mathfrak q$ is minimal over $I+J$. Its associated primes are nonempty and contained in that support, so $\mathfrak qA_{\mathfrak q}$ is one of them and Lemma 14.1 gives depth zero.

Suppose $\operatorname{depth}A_{\mathfrak q}\geq2$. Then $\operatorname{Ext}^1(\kappa,A_{\mathfrak q})=0$ for the residue field $\kappa$ of $A_\mathfrak q$, and the long exact sequence
$$
\operatorname{Hom}(\kappa,(A/I\oplus A/J)_{\mathfrak q})\to\operatorname{Hom}(\kappa,(A/(I+J))_{\mathfrak q})\to\operatorname{Ext}^1(\kappa,A_{\mathfrak q})=0
$$

shows that $(A/I)_{\mathfrak q}$ or $(A/J)_{\mathfrak q}$ has depth zero. Both $A/I$ and $A/J$ are reduced, being intersections of primes, so by Theorem 14.22 and Proposition 14.21 depth zero at $\mathfrak q$ means that $\mathfrak q$ is a minimal prime of $A/I$, that is $\mathfrak q=\mathfrak p_1$, or a minimal prime of $A/J$, that is $\mathfrak q=\mathfrak p_i$ for some $i\geq2$. Either alternative is impossible: $\mathfrak q$ contains $I+J$, so $\mathfrak q=\mathfrak p_1$ would give $\mathfrak p_1\supseteq\mathfrak p_2$ and $\mathfrak q=\mathfrak p_i$ would give $\mathfrak p_i\supseteq\mathfrak p_1$, contradicting the incomparability of distinct minimal primes.

Therefore $\operatorname{depth}A_{\mathfrak q}\leq1$, and $(S_2)$ forces $\dim A_{\mathfrak q}\leq1$. If $\dim A_{\mathfrak q}=1$, then $(R_1)$ makes $A_{\mathfrak q}$ regular, hence a domain by Proposition 14.15, so $\mathfrak q$ contains exactly one minimal prime; but it contains $\mathfrak p_1$ and $\mathfrak p_2$. If $\dim A_{\mathfrak q}=0$, then $\mathfrak q$ is itself minimal and again contains the two distinct minimal primes $\mathfrak p_1,\mathfrak p_2$. Both cases are absurd, so $t=1$ and the reduced ring $A$ is a domain. $\square$

**Theorem 14.26 (Serre's normality criterion).** A noetherian ring $A$ is normal — that is, $A_{\mathfrak p}$ is an integrally closed domain for every prime $\mathfrak p$ — if and only if it satisfies $(R_1)$ and $(S_2)$. Such a ring is automatically reduced.

**Proof.** Suppose $A$ is normal. For $(R_1)$, let $\operatorname{ht}\mathfrak p\leq1$. If $\operatorname{ht}\mathfrak p=0$, then $A_{\mathfrak p}$ is a zero-dimensional domain, hence a field, hence regular. If $\operatorname{ht}\mathfrak p=1$, then $A_{\mathfrak p}$ is a one-dimensional noetherian local integrally closed domain, hence a discrete valuation ring by the characterizations of Book 1, Theorem 4.1, and a discrete valuation ring is regular by Proposition 4.2. For $(S_2)$, apply Theorem 14.23 to each $A_{\mathfrak p}$.

Conversely assume $(R_1)$ and $(S_2)$. Both conditions pass to localizations, so it suffices to prove that a noetherian local ring $A$ with $(R_1)$ and $(S_2)$ is an integrally closed domain. It is a domain by Lemma 14.25. Let $K$ be its fraction field and let $x\in K$ be integral over $A$. For every height-one prime $\mathfrak p$, the element $x$ is integral over $A_{\mathfrak p}$, which is a regular local ring of dimension one by $(R_1)$ and Proposition 14.15, hence a discrete valuation ring by Proposition 4.2 and therefore integrally closed in $K$; so $x\in A_{\mathfrak p}$. Theorem 14.24 now gives $x\in A$. Reducedness is Theorem 14.22. $\square$

This is the complete proof of Theorem 4.1, whose statement included reducedness explicitly; the criterion shows that reducedness is a consequence rather than an extra hypothesis. It is also the tool used in Theorem 14.20 and in the example of the quadratic cone, and it is what makes the phrase "normalization repairs codimension one" precise: by $(R_1)$ a normal ring has discrete valuation rings at all height-one primes, and by Theorem 14.24 its elements are detected there.

### 14.6 Freeness in dimension two

The purity arguments of later books need a converse to the intuition that a module of maximal depth is as good as free. Over a regular local ring it is exactly true, and no finiteness of projective dimension has to be assumed in advance.

**Theorem 14.27.** Let $A$ be a regular local ring of dimension $n$ and let $M\neq0$ be a finite $A$-module with $\operatorname{depth}M=n$. Then $M$ is free.

**Proof.** Induct on $n$. If $n=0$, then $A$ is a field and every module is free.

Let $n\geq1$. Since $\operatorname{depth}M=n\geq1$, Lemma 14.1 gives $\mathfrak m\notin\operatorname{Ass}M$, so every $\mathfrak p\in\operatorname{Ass}M$ is properly contained in $\mathfrak m$. Also $\mathfrak m\neq\mathfrak m^2$. Prime avoidance in the version allowing one non-prime member produces
$$
z\in\mathfrak m\setminus\Bigl(\mathfrak m^2\cup\bigcup_{\mathfrak p\in\operatorname{Ass}M}\mathfrak p\Bigr),
$$

so $z$ is a nonzerodivisor on $M$, and $z\neq0$ is a nonzerodivisor on the domain $A$. By Lemma 14.14 the ring $\bar A=A/(z)$ is regular local of dimension $n-1$, and by Theorem 14.5 together with Proposition 14.8 the module $\bar M=M/zM$ has
$$
\operatorname{depth}_{\bar A}\bar M=\operatorname{depth}_A\bar M=n-1=\dim\bar A .
$$

By induction $\bar M$ is free over $\bar A$, say of rank $r$.

Choose $m_1,\ldots,m_r\in M$ whose residues form a basis of $\bar M$. Their residues modulo $\mathfrak m$ form a basis of $M/\mathfrak mM=\bar M/\bar{\mathfrak m}\bar M$, so by Nakayama they generate $M$. Let
$$
0\to N\to A^r\xrightarrow{\ \varphi\ }M\to0
$$

be the resulting presentation. Tensoring the exact sequence $0\to A\xrightarrow{z}A\to\bar A\to0$ with $M$ computes $\operatorname{Tor}^A_1(M,\bar A)=\{m\in M:zm=0\}=0$, because $z$ is a nonzerodivisor on $M$. Hence tensoring the presentation with $\bar A$ leaves
$$
0\to N/zN\to\bar A^{\,r}\xrightarrow{\ \bar\varphi\ }\bar M\to0
$$

exact. Now $\bar\varphi$ is a surjection of free $\bar A$-modules of the same finite rank $r$, hence an isomorphism: a surjective endomorphism of a finite module over a commutative ring is injective. Therefore $N/zN=0$, so $N=zN$ with $z\in\mathfrak m$, and Nakayama gives $N=0$. Thus $\varphi$ is an isomorphism and $M\simeq A^r$. $\square$

Theorem 14.27 is the Auslander–Buchsbaum formula in the case where it is most often applied, but it does not presuppose $\operatorname{pd}M<\infty$; conversely, once $M$ is known to be free, Theorem 14.12 reads $0+n=n$, which is Theorem 14.16.

Modules of maximal depth arise in practice as duals.

**Proposition 14.28.** Let $A$ be a noetherian local ring and $N$ a finite $A$-module. Then
$$
\operatorname{depth}\operatorname{Hom}_A(N,A)\geq\min\{2,\operatorname{depth}A\}.
$$

**Proof.** If $\operatorname{Hom}_A(N,A)=0$ the claim is vacuous by the convention on the zero module. Choose a finite presentation $F_1\to F_0\to N\to0$ with $F_0,F_1$ finite free. Applying $\operatorname{Hom}_A(-,A)$ gives an exact sequence
$$
0\to N^{*}\to F_0^{*}\to F_1^{*},
$$

so $N^{*}$ fits into a short exact sequence $0\to N^{*}\to F_0^{*}\to C\to0$ where $C$ is the image of $F_0^{*}\to F_1^{*}$, a submodule of the free module $F_1^{*}$. If $C=0$ then $N^{*}$ is free and its depth is $\operatorname{depth}A$. Otherwise, $\operatorname{Ass}C\subseteq\operatorname{Ass}F_1^{*}=\operatorname{Ass}A$, so $\operatorname{depth}C=0$ would force $\operatorname{depth}A=0$; hence $\operatorname{depth}C\geq\min\{1,\operatorname{depth}A\}$. Lemma 14.7 gives
$$
\operatorname{depth}N^{*}\geq\min\{\operatorname{depth}F_0^{*},\operatorname{depth}C+1\}
\geq\min\{\operatorname{depth}A,\ \min\{1,\operatorname{depth}A\}+1\},
$$

which is $\min\{2,\operatorname{depth}A\}$. $\square$

**Corollary 14.29.** Let $A$ be a regular local ring of dimension two and let $M\neq0$ be a finite $A$-module isomorphic to the dual $N^{*}=\operatorname{Hom}_A(N,A)$ of some finite $A$-module $N$. In particular, let $M$ be reflexive, so that the natural map $M\to M^{**}$ is an isomorphism. Then $M$ is free.

**Proof.** By Theorem 14.16, $\operatorname{depth}A=2$, so Proposition 14.28 gives $\operatorname{depth}M\geq2$, and Corollary 14.4 gives $\operatorname{depth}M\leq\dim M\leq2$. Theorem 14.27 applies. $\square$

**Theorem 14.30.** Let $A$ be a regular local ring of dimension two and let $B$ be a local $A$-algebra, finite as an $A$-module, which is a normal domain of dimension two. Then $B$ is free as an $A$-module.

**Proof.** By Theorem 14.23, $\operatorname{depth}_BB\geq2$, and Proposition 14.8 gives $\operatorname{depth}_AB=\operatorname{depth}_BB\geq2$. On the other hand $\operatorname{depth}_AB\leq\dim_AB\leq\dim A=2$ by Corollary 14.4. Hence $\operatorname{depth}_AB=2=\dim A$, and Theorem 14.27 makes $B$ free over $A$. $\square$

The dimension hypothesis on $B$ is automatic when $A\to B$ is injective, by the incomparability and going-up theorems for finite extensions; it is stated separately so that no such theorem is needed for the proof itself. Applied to the local ring at a closed point of a regular arithmetic surface, Theorem 14.30 says that a finite normal cover is locally free there, which is the algebraic content of purity statements about branched covers of surfaces: the direct image of the structure sheaf of the cover is locally free, so its rank is constant and can be computed generically.

### 14.7 Finite free resolutions and the homological criterion for regularity

Every result so far has treated regularity as a numerical condition: the maximal ideal needs exactly $\dim A$ generators. That definition is easy to check on an explicit presentation, which is why Corollary 14.18 settles the family $xy=\pi^n$ at a stroke. It is, however, useless for two questions that the geometry of models keeps raising. First, if $A$ is regular local, is $A_{\mathfrak p}$ regular for every prime $\mathfrak p$? The definition compares two numbers attached to the closed point and says nothing at all about other points, and the standing convention that a _regular ring_ is one all of whose local rings are regular quietly presupposes an answer. Second, is a regular local ring factorial? Factoriality is a statement about height-one primes, that is, about localizations again.

Serre's discovery is that regularity has an equivalent formulation in which both questions become trivial or nearly so: a noetherian local ring is regular exactly when its residue field admits a _finite_ free resolution. The virtue of this reformulation is that it is manifestly stable under localization, because localizing a finite free resolution produces a finite free resolution. The cost is that one must prove the equivalence, and this is where the Auslander–Buchsbaum formula of Section 14.3 earns its place: it converts the finiteness of a projective dimension into an exact numerical identity, and the identity is rigid enough to force the ring to be regular.

This criterion is also proved in Book 10a, Section 2.2, where it is the foundation of the whole excellence package: the two consequences drawn from it there — that a localization of a regular local ring is regular, and that regularity descends along a faithfully flat map — are exactly what makes formal fibres a usable tool. The proof is repeated here in the form the divisor calculus of this book needs, so that Chapter 14 remains a self-contained account of the local algebra used in Chapters 4 to 12; nothing below depends on the version in Book 10a, and the two agree.

Throughout this section $\operatorname{pd}$ denotes projective dimension as in Section 14.3, and we use the standard properties of $\operatorname{Tor}$ listed at the head of the chapter. The first step is to make projective dimension computable over a local ring.

**Lemma 14.31.** Let $M\neq0$ be finite over $(A,\mathfrak m,k)$ and let
$$
\cdots\to F_2\to F_1\to F_0\to M\to0
$$

be a minimal free resolution: setting $N_0=M$ and $N_{i+1}=\ker(F_i\to N_i)$, each map $F_i\to N_i$ is a minimal cover by a finite free module. Then all differentials of $F_\bullet$ have image inside $\mathfrak mF_i$,
$$
\operatorname{Tor}^A_i(M,k)\simeq F_i\otimes_Ak\quad\text{for all }i\geq0,
$$

and
$$
\operatorname{pd}_AM=\sup\{i:\operatorname{Tor}^A_i(M,k)\neq0\}.
$$

**Proof.** Minimality of a cover $F\to N$ means that $F\otimes k\to N\otimes k$ is an isomorphism, so the kernel lies in $\mathfrak mF$; applied at each stage this is the first assertion. Computing $\operatorname{Tor}^A_\bullet(M,k)$ from $F_\bullet$, all differentials of $F_\bullet\otimes_Ak$ vanish, which gives the second assertion.

Write $\ell\in\{0,1,\ldots,\infty\}$ for the supremum of the $i$ with $F_i\neq0$; once some $F_i$ vanishes the remaining syzygy is zero and all later terms vanish too, so $F_\bullet$ is a free resolution of length $\ell$ and $\operatorname{pd}_AM\leq\ell$. By Nakayama $F_i\neq0$ if and only if $F_i\otimes k\neq0$, so $\ell$ is exactly the displayed supremum. It remains to see $\ell\leq\operatorname{pd}_AM$, and for this we may assume $p:=\operatorname{pd}_AM<\infty$. As long as $\operatorname{pd}N_i\geq1$, Lemma 14.10 gives $\operatorname{pd}N_{i+1}=\operatorname{pd}N_i-1$; hence $\operatorname{pd}N_p=0$ and $N_p$ is free, say of rank $r$. Then $F_p\to N_p$ is a minimal cover of a free module, so $F_p$ also has rank $r$, and a surjection between free modules of the same finite rank over a commutative ring is an isomorphism. Therefore $N_{p+1}=0$, $F_{p+1}=0$, and $\ell\leq p$. $\square$

**Corollary 14.32.** Let $(A,\mathfrak m,k)$ be noetherian local and let all modules be finite.

1. If $0\to M'\to M\to M''\to0$ is exact, then $\operatorname{pd}M''\leq\max\{\operatorname{pd}M,\operatorname{pd}M'+1\}$.
2. If $N$ is a direct summand of $M$, then $\operatorname{pd}N\leq\operatorname{pd}M$.
3. If $\operatorname{pd}_Ak=n<\infty$, then $\operatorname{pd}_AM\leq n$ for every finite $M$.

**Proof.** For (1), let $i>\max\{\operatorname{pd}M,\operatorname{pd}M'+1\}$. By Lemma 14.31 both $\operatorname{Tor}_i(M,k)$ and $\operatorname{Tor}_{i-1}(M',k)$ vanish, and the long exact sequence
$$
\operatorname{Tor}_i(M,k)\to\operatorname{Tor}_i(M'',k)\to\operatorname{Tor}_{i-1}(M',k)
$$

forces $\operatorname{Tor}_i(M'',k)=0$; Lemma 14.31 again gives the bound. For (2), $\operatorname{Tor}_i(N,k)$ is a direct summand of $\operatorname{Tor}_i(M,k)$. For (3), compute $\operatorname{Tor}^A_i(M,k)$ from a free resolution of the second argument $k$, which has length $n$: the groups vanish for $i>n$. $\square$

The next lemma is the transfer of projective dimension across the quotient by a single regular element. Both directions are used: one to build finite resolutions over $A$ out of finite resolutions over $A/xA$, the other to push a finite resolution down.

**Lemma 14.33.** Let $(A,\mathfrak m,k)$ be noetherian local, let $x\in\mathfrak m$ be a nonzerodivisor on $A$, and put $\bar A=A/xA$.

1. If $M$ is a finite $A$-module on which $x$ is a nonzerodivisor, then $\operatorname{pd}_{\bar A}(M/xM)\leq\operatorname{pd}_AM$.
2. If $M\neq0$ is a finite $\bar A$-module, then $\operatorname{pd}_AM\leq\operatorname{pd}_{\bar A}M+1$.

**Proof.** The sequence $0\to A\xrightarrow{\ x\ }A\to\bar A\to0$ is a free resolution of $\bar A$ of length one, so $\operatorname{Tor}^A_i(M,\bar A)=0$ for $i\geq2$ and $\operatorname{Tor}^A_1(M,\bar A)=\{m\in M:xm=0\}$.

For (1) we may assume $p=\operatorname{pd}_AM<\infty$ and take a free resolution $0\to F_p\to\cdots\to F_0\to M\to0$. Since $x$ is a nonzerodivisor on $M$, all $\operatorname{Tor}^A_i(M,\bar A)$ with $i\geq1$ vanish. Let $Z_0=M$ and $Z_{i+1}=\ker(F_i\to Z_i)$ be the syzygies, so that dimension shifting along the short exact sequences $0\to Z_{i+1}\to F_i\to Z_i\to0$ gives $\operatorname{Tor}^A_j(Z_i,\bar A)\simeq\operatorname{Tor}^A_{j+i}(M,\bar A)=0$ for all $j\geq1$. Consequently each of those short exact sequences remains exact after $-\otimes_A\bar A$, and splicing shows that $F_\bullet\otimes_A\bar A$ is a resolution of $M/xM$ by free $\bar A$-modules of length $p$.

For (2) we may assume $q=\operatorname{pd}_{\bar A}M<\infty$ and induct on $q$. If $q=0$ then $M$ is a finite free $\bar A$-module, so $\operatorname{pd}_AM=\operatorname{pd}_A\bar A$, which is $1$: the displayed resolution has length one, and $\bar A$ is not $A$-free because $x\neq0$ annihilates it while $x A^r\neq0$ for $r\geq1$. If $q\geq1$, choose $0\to N\to\bar F\to M\to0$ with $\bar F$ finite free over $\bar A$ and $\operatorname{pd}_{\bar A}N=q-1$, which is possible by Lemma 14.10 applied over $\bar A$. By induction $\operatorname{pd}_AN\leq q$, while $\operatorname{pd}_A\bar F=1$, and Corollary 14.32(1) gives $\operatorname{pd}_AM\leq\max\{1,q+1\}=q+1$. $\square$

**Theorem 14.34.** Let $A$ be a regular local ring of dimension $n$. Then $\operatorname{pd}_Ak\leq n$, and consequently every finite $A$-module has a free resolution of length at most $n$ by finite free modules.

**Proof.** Induct on $n$. If $n=0$ then $\mathfrak m=0$, $A=k$, and $\operatorname{pd}_Ak=0$. Let $n\geq1$ and choose $x\in\mathfrak m\setminus\mathfrak m^2$, which is possible because $\mathfrak m\neq\mathfrak m^2$ by Nakayama. By Proposition 14.15 the ring $A$ is a domain, so $x$ is a nonzerodivisor, and by Lemma 14.14 the ring $\bar A=A/(x)$ is regular local of dimension $n-1$ with the same residue field $k$. By induction $\operatorname{pd}_{\bar A}k\leq n-1$, so Lemma 14.33(2) gives $\operatorname{pd}_Ak\leq n$. The last assertion is Corollary 14.32(3) together with Lemma 14.31, which produces the resolution by finite free modules. $\square$

In fact the bound is an equality, and this is the first place where the Auslander–Buchsbaum formula is used for something other than bookkeeping: $k$ has depth $0$, since $\operatorname{Hom}_A(k,k)\neq0$, so Theorem 14.12 and Theorem 14.16 give
$$
\operatorname{pd}_Ak=\operatorname{depth}A-\operatorname{depth}k=n-0=n .
$$

The converse implication is the substantial half. Its engine is the following decomposition, which says that dividing the maximal ideal by a minimal generator splits off a copy of the residue field.

**Lemma 14.35.** Let $(A,\mathfrak m,k)$ be noetherian local and let $x\in\mathfrak m\setminus\mathfrak m^2$ be a nonzerodivisor. Put $\bar A=A/xA$ and $\bar{\mathfrak m}=\mathfrak m/xA$. Then there is an isomorphism of $\bar A$-modules
$$
\mathfrak m/x\mathfrak m\simeq\bar{\mathfrak m}\oplus k .
$$

**Proof.** Because $x\notin\mathfrak m^2$, its residue is part of a basis of $\mathfrak m/\mathfrak m^2$, so by Nakayama there is a minimal generating set $x,y_2,\ldots,y_t$ of $\mathfrak m$. All three modules in the statement are killed by $x$ and hence are $\bar A$-modules. Inside $\mathfrak m/x\mathfrak m$ consider
$$
N=xA/x\mathfrak m,\qquad M'=\bigl((y_2,\ldots,y_t)+x\mathfrak m\bigr)/x\mathfrak m .
$$

Since $x$ is a nonzerodivisor, $a\mapsto ax$ identifies $A/\mathfrak m$ with $N$, so $N\simeq k$. Clearly $N+M'=\mathfrak m/x\mathfrak m$. Suppose an element of $N\cap M'$ is represented by $ax=\sum_{i\geq2}a_iy_i+xm$ with $m\in\mathfrak m$. Then $(a-m)x\in(y_2,\ldots,y_t)$. If $a$ were a unit, so would be $a-m$, and then $x\in(y_2,\ldots,y_t)$, making $y_2,\ldots,y_t$ generate $\mathfrak m$ and contradicting the minimality of the chosen generating set. Hence $a\in\mathfrak m$, so $ax\in x\mathfrak m$ and the element is zero. Thus $\mathfrak m/x\mathfrak m=N\oplus M'$, and $M'\simeq(\mathfrak m/x\mathfrak m)/N=\mathfrak m/xA=\bar{\mathfrak m}$. $\square$

**Theorem 14.36 (Serre's homological characterization of regularity).** For a noetherian local ring $(A,\mathfrak m,k)$ of dimension $n$ the following are equivalent.

1. $A$ is regular.
2. $\operatorname{pd}_Ak<\infty$.
3. $\operatorname{pd}_AM<\infty$ for every finite $A$-module $M$.

When they hold, $\operatorname{pd}_Ak=n$ and every finite module has a resolution of length at most $n$ by finite free modules.

**Proof.** (1) implies (3) is Theorem 14.34, and (3) implies (2) is trivial. Assume (2) and write $t=\dim_k\mathfrak m/\mathfrak m^2$ for the embedding dimension; we induct on $t$.

Suppose first $\operatorname{depth}A=0$. Then Theorem 14.12, applied to $M=k$, which has finite projective dimension by hypothesis and depth $0$ because $\operatorname{Hom}_A(k,k)\neq0$ (Lemma 14.1 and Corollary 14.4), gives $\operatorname{pd}_Ak=\operatorname{depth}A-\operatorname{depth}k=0$. So $k$ is a finite free $A$-module, say $k\simeq A^r$ with $r\geq1$; but $\mathfrak m$ annihilates $k$, hence annihilates $A^r$, which forces $\mathfrak m=0$. Then $A=k$ is a field, regular of dimension zero. This case covers in particular $t=0$, since $t=0$ means $\mathfrak m=\mathfrak m^2$ and hence $\mathfrak m=0$ by Nakayama.

Now let $t\geq1$ and $\operatorname{depth}A\geq1$. Every $\mathfrak p\in\operatorname{Ass}A$ is then a proper subset of $\mathfrak m$ by Lemma 14.1, and $\mathfrak m\neq\mathfrak m^2$, so prime avoidance in the version allowing one non-prime member produces
$$
x\in\mathfrak m\setminus\Bigl(\mathfrak m^2\cup\bigcup_{\mathfrak p\in\operatorname{Ass}A}\mathfrak p\Bigr),
$$

a nonzerodivisor outside $\mathfrak m^2$. Put $\bar A=A/xA$. Since $t\geq1$ the field $k$ is not free over $A$, so $\operatorname{pd}_Ak\geq1$, and applying Lemma 14.10 to the minimal cover $A\to k$ with kernel $\mathfrak m$ gives $\operatorname{pd}_A\mathfrak m=\operatorname{pd}_Ak-1<\infty$. As $\mathfrak m\subseteq A$ and $x$ is a nonzerodivisor on $A$, it is a nonzerodivisor on $\mathfrak m$, so Lemma 14.33(1) gives $\operatorname{pd}_{\bar A}(\mathfrak m/x\mathfrak m)<\infty$. By Lemma 14.35 the residue field $k$ is a direct summand of $\mathfrak m/x\mathfrak m$ over $\bar A$, so $\operatorname{pd}_{\bar A}k<\infty$ by Corollary 14.32(2).

The embedding dimension of $\bar A$ is $\dim_k\mathfrak m/(\mathfrak m^2+xA)=t-1$, because $x\notin\mathfrak m^2$. By the inductive hypothesis $\bar A$ is regular, hence $\dim\bar A=t-1$. Lemma 14.2, applied to the module $A$ and the nonzerodivisor $x$, gives $\dim\bar A=\dim A-1$, so $\dim A=t=\dim_k\mathfrak m/\mathfrak m^2$ and $A$ is regular.

The final assertions are the computation after Theorem 14.34 and Theorem 14.34 itself. $\square$

**Corollary 14.37 (regularity localizes).** Let $A$ be a regular local ring of dimension $n$ and let $\mathfrak p$ be a prime of $A$. Then $A_{\mathfrak p}$ is a regular local ring of dimension $\operatorname{ht}\mathfrak p$, and $\operatorname{ht}\mathfrak p\leq n-1$ if $\mathfrak p\neq\mathfrak m$. In particular $\operatorname{Spec}A$ is a regular scheme, so a regular local ring is a regular ring in the sense of Section 1.2.

**Proof.** By Theorem 14.36 the module $A/\mathfrak p$ has a resolution
$$
0\to F_r\to\cdots\to F_0\to A/\mathfrak p\to0
$$

by finite free $A$-modules with $r\leq n$. Localization at $\mathfrak p$ is exact and carries finite free modules to finite free modules, so the localized complex is a finite free resolution of $(A/\mathfrak p)_{\mathfrak p}$, which is the residue field of $A_{\mathfrak p}$. Hence that residue field has finite projective dimension over $A_{\mathfrak p}$, and Theorem 14.36 makes $A_{\mathfrak p}$ regular. Its dimension is $\operatorname{ht}\mathfrak p$ by definition of height. If $\mathfrak p\neq\mathfrak m$, any chain of primes of length $\operatorname{ht}\mathfrak p$ ending at $\mathfrak p$ extends by $\mathfrak m$, so $\operatorname{ht}\mathfrak p+1\leq\dim A$. $\square$

This is the first genuinely new structural fact of the chapter: regularity, defined at one point, propagates to all points of the spectrum. It also removes a small circularity that the standing conventions of Section 1.2 would otherwise leave open, and it is the hypothesis-free version of the ad hoc verifications made in Theorem 14.20 and in the example of the quadratic cone, where regularity away from the singular point had to be checked by inverting a coordinate.

### 14.8 Regular local rings are factorial

A domain $A$ is **factorial**, or a **unique factorization domain**, if every nonzero nonunit is a product of irreducible elements and such a factorization is unique up to reordering and unit factors. Recall that $\pi\in A$ is _irreducible_ if it is a nonzero nonunit and $\pi=ab$ forces $a$ or $b$ to be a unit, and that $\pi$ is _prime_ if it is a nonzero nonunit and $(\pi)$ is a prime ideal. A prime element is irreducible; the content of factoriality is the converse.

Factoriality is what makes divisor theory work. On an integral scheme a prime divisor is the closure of a height-one point, and it is a Cartier divisor near a point $x$ exactly when the corresponding height-one prime of $\mathcal O_{X,x}$ becomes principal. So the statement that every Weil divisor on a regular scheme is Cartier — the statement that lets one intersect divisors, pull them back, and compute degrees on the models built in Chapters 6 to 11 — is precisely the assertion that regular local rings are factorial. That is the theorem of this section.

The proof has three movements. The first replaces factoriality by a statement about height-one primes, so that the problem becomes local and homological rather than combinatorial. The second is a descent principle: inverting a single prime element cannot destroy factoriality, so one is allowed to work on the complement of one hypersurface. The third is the homological input: a height-one prime of a regular local ring has a finite free resolution, and an ideal that has a finite free resolution and is principal at every localization must itself be principal. Only the last step uses Section 14.7.

**Theorem 14.38 (Kaplansky's criterion).** A noetherian domain $A$ is factorial if and only if every prime ideal of height one is principal.

**Proof.** Suppose $A$ is factorial and let $\mathfrak p$ have height one. Choose $0\neq a\in\mathfrak p$; it is a nonunit, so it factors into irreducibles, and since $\mathfrak p$ is prime one irreducible factor $\pi$ lies in $\mathfrak p$. In a factorial domain an irreducible element is prime: if $\pi\mid ab$, write $ab=\pi c$ and compare factorizations of both sides, so that $\pi$ agrees up to a unit with an irreducible factor of $a$ or of $b$. Hence $0\subsetneq(\pi)\subseteq\mathfrak p$ is a chain of primes, and $\operatorname{ht}\mathfrak p=1$ forces $(\pi)=\mathfrak p$.

Conversely, assume every height-one prime is principal. First, every nonzero nonunit $a$ is a product of irreducibles. Otherwise the set of principal ideals $(a)$ with $a$ a nonzero nonunit admitting no such factorization is nonempty, and since $A$ is noetherian it has a maximal member $(a)$. Then $a$ is not irreducible, so $a=bc$ with $b,c$ nonunits, and both are nonzero; the inclusions $(a)\subseteq(b)$ and $(a)\subseteq(c)$ are strict because $c$, respectively $b$, is not a unit. By maximality $b$ and $c$ factor into irreducibles, hence so does $a$, a contradiction.

Next, every irreducible $\pi$ is prime. Let $\mathfrak p$ be a prime minimal over $(\pi)$. Krull's height theorem gives $\operatorname{ht}\mathfrak p\leq1$, and $\operatorname{ht}\mathfrak p\geq1$ because $\pi\neq0$ and $A$ is a domain, so $\mathfrak p=(t)$ for some $t$ by hypothesis. Write $\pi=tu$. Since $\mathfrak p$ is a proper ideal, $t$ is not a unit, so irreducibility of $\pi$ makes $u$ a unit and $(\pi)=(t)=\mathfrak p$ prime.

Finally, existence of factorizations together with primality of irreducibles gives uniqueness by the usual induction on the number of factors: if $\pi_1\cdots\pi_r=\rho_1\cdots\rho_s$ with all factors irreducible, then $\pi_1$ is prime and divides the right-hand side, so it divides some $\rho_j$, which being irreducible equals $\pi_1$ times a unit; cancel and repeat. $\square$

The second movement is Nagata's descent principle. It is what allows an induction on dimension: in a regular local ring one can always find a prime element, and inverting it lands in rings of strictly smaller dimension.

**Theorem 14.39 (Nagata's lemma).** Let $A$ be a noetherian domain and let $S\subseteq A$ be the multiplicative set generated by a family of prime elements of $A$ together with $1$. If $S^{-1}A$ is factorial, then $A$ is factorial.

**Proof.** By Theorem 14.38 it suffices to prove that every height-one prime $\mathfrak q$ of $A$ is principal. Note first that $0\notin S$, since a product of nonzero elements of a domain is nonzero, so $S^{-1}A$ is again a noetherian domain with the same fraction field.

Suppose $\mathfrak q\cap S\neq\emptyset$. An element of $S$ is a product $\pi_1\cdots\pi_r$ of prime elements, and if it lies in the prime $\mathfrak q$ then some $\pi_i\in\mathfrak q$. Then $0\subsetneq(\pi_i)\subseteq\mathfrak q$ is a chain of primes and $\operatorname{ht}\mathfrak q=1$ gives $\mathfrak q=(\pi_i)$, which is principal.

Suppose instead $\mathfrak q\cap S=\emptyset$. Then $Q=S^{-1}\mathfrak q$ is a prime of $S^{-1}A$ with $(S^{-1}A)_Q=A_{\mathfrak q}$, so $\operatorname{ht}Q=\operatorname{ht}\mathfrak q=1$, and Theorem 14.38 applied to the factorial ring $S^{-1}A$ makes $Q$ principal. Clearing a denominator, $Q=\theta\,S^{-1}A$ for some $\theta\in\mathfrak q$: if $Q=\alpha S^{-1}A$ and $\alpha=\theta/s$ with $\theta\in A$ and $s\in S$, then $\theta=s\alpha$ still generates $Q$ because $s$ is a unit in $S^{-1}A$, and $\theta\in Q\cap A=\mathfrak q$, the last equality holding because $\mathfrak q$ is prime and disjoint from $S$. Among all such generators contained in $\mathfrak q$ choose one for which the ideal $\theta A$ is maximal, which is possible because $A$ is noetherian. We claim that no prime element $\pi$ occurring in the chosen family divides $\theta$. Indeed if $\theta=\pi\theta'$, then $\pi\notin\mathfrak q$ because $\mathfrak q\cap S=\emptyset$, so $\theta'\in\mathfrak q$ as $\mathfrak q$ is prime; moreover $\pi$ is a unit in $S^{-1}A$, so $\theta'$ still generates $Q$; and $\theta A\subsetneq\theta'A$ strictly, since $\pi$ is not a unit and $A$ is a domain. This contradicts maximality.

Now let $a\in\mathfrak q$. Then $a/1\in Q=\theta S^{-1}A$, so $sa=\theta b$ for some $s\in S$ and $b\in A$. Write $s$ as a product of prime elements from the family. Each such factor $\pi$ divides $\theta b$ but not $\theta$, hence divides $b$ because $(\pi)$ is prime; cancelling $\pi$ from both sides of $sa=\theta b$ is legitimate in the domain $A$ and reduces the number of factors of $s$. After finitely many steps $a=\theta b'$ with $b'\in A$. Therefore $\mathfrak q\subseteq\theta A\subseteq\mathfrak q$, and $\mathfrak q$ is principal. $\square$

The third movement supplies the local-to-global step. The situation to be handled is this: after inverting a prime element one is left with a noetherian ring $R$, no longer local, and a height-one prime $Q$ that is principal at every localization of $R$ and possesses a finite free resolution. Neither property alone makes $Q$ principal; together they do, and the mechanism is that a finite free resolution converts a locally free module first into a direct summand of a free module, then into a _stably_ free module, and finally a determinant computation removes the word "stably".

**Lemma 14.40.** Let $R$ be a noetherian ring and $M$ a finite $R$-module such that $M_P$ is a free $R_P$-module for every prime $P$. Then $M$ is a direct summand of a finite free $R$-module.

**Proof.** Choose a surjection $\varphi:F\to M$ with $F$ finite free and let $K=\ker\varphi$, a finite module since $R$ is noetherian. For every prime $P$ the module $M_P$ is free, hence projective, so $\operatorname{Ext}^1_{R_P}(M_P,K_P)=0$. Because $M$ is finite and $R$ noetherian, $\operatorname{Ext}^1_R(M,K)_P\simeq\operatorname{Ext}^1_{R_P}(M_P,K_P)$, so all localizations of $\operatorname{Ext}^1_R(M,K)$ vanish. A module with this property is zero: a nonzero element generates a nonzero submodule whose annihilator is proper, and localizing at a maximal ideal containing that annihilator keeps the element nonzero. The extension class of $0\to K\to F\to M\to0$ therefore vanishes, so the sequence splits. $\square$

**Lemma 14.41.** Let $R$ be a ring and $M$ a direct summand of a finite free module which admits a resolution
$$
0\to F_p\to\cdots\to F_1\to F_0\to M\to0
$$

by finite free $R$-modules. Then $M$ is **stably free**: there are integers $a,b\geq0$ with $M\oplus R^a\simeq R^b$.

**Proof.** Induct on $p$. If $p=0$ then $M\simeq F_0$ is free. If $p\geq1$, let $K=\ker(F_0\to M)$. Since $M$ is a direct summand of a free module, the surjection $F_0\to M$ splits, so $F_0\simeq M\oplus K$ and $K$ is itself a direct summand of a finite free module. Moreover $0\to F_p\to\cdots\to F_1\to K\to0$ is a resolution of $K$ by finite free modules of length $p-1$, so by induction $K\oplus R^a\simeq R^b$ for some $a,b$. Then
$$
M\oplus R^b\simeq M\oplus K\oplus R^a\simeq F_0\oplus R^a,
$$

and the right-hand side is finite free. $\square$

**Lemma 14.42.** Let $R$ be a domain with fraction field $K$ and let $I\subseteq R$ be a nonzero ideal with $I\oplus R^m\simeq R^{m'}$ for integers $m,m'\geq0$. Then $m'=m+1$ and $I$ is principal.

**Proof.** Localizing at the multiplicative set $R\setminus\{0\}$ turns the hypothesis into an isomorphism of $K$-vector spaces $K\oplus K^m\simeq K^{m'}$, because $I$ is a nonzero ideal of a domain and hence $I\otimes_RK=K$. Comparing dimensions gives $m'=m+1$.

Regard $M=I\oplus R^m$ as an $R$-submodule of $K^{m+1}$ by way of $I\subseteq R\subseteq K$, and write $e_1,\ldots,e_{m+1}$ for the standard basis of $K^{m+1}$, so that $M$ is generated by the elements $ae_1$ with $a\in I$ together with $e_2,\ldots,e_{m+1}$. For an $R$-submodule $N\subseteq K^{m+1}$ let
$$
\Delta(N)\subseteq K
$$

be the $R$-submodule generated by all determinants $\det(v_1|\cdots|v_{m+1})$ of matrices whose columns $v_i$ lie in $N$. Since the determinant is $R$-multilinear in its columns, $\Delta(N)$ is already generated by the determinants formed from any generating set of $N$.

Compute $\Delta(M)$ from the generators listed above. A tuple containing two elements of the form $ae_1,a'e_1$ has proportional columns and determinant zero; a tuple containing none of them repeats some $e_j$ and again has determinant zero; and a tuple consisting of one $ae_1$ and all of $e_2,\ldots,e_{m+1}$ has determinant $\pm a$. Hence $\Delta(M)=I$.

On the other hand, let $u:R^{m+1}\to K^{m+1}$ be the composite of an isomorphism $R^{m+1}\simeq M$ with the inclusion, and let $U\in K^{(m+1)\times(m+1)}$ be its matrix in the standard bases. Every $(m+1)$-tuple of elements of $M=u(R^{m+1})$ is of the form $u(w_1),\ldots,u(w_{m+1})$ with $w_i\in R^{m+1}$, and the multiplicativity of determinants gives
$$
\det\bigl(u(w_1)|\cdots|u(w_{m+1})\bigr)=\det(U)\cdot\det(w_1|\cdots|w_{m+1}).
$$

As the $w_i$ range over $R^{m+1}$, the determinants $\det(w_1|\cdots|w_{m+1})$ range over a set generating $R$, the identity matrix contributing $1$. Therefore $\Delta(M)=\det(U)\,R$.

Comparing the two computations gives $I=\det(U)R$. Since $I\subseteq R$ is nonzero, $\det(U)$ is a nonzero element of $R$ and $I=(\det U)$ is principal. $\square$

We can now prove the theorem. The induction is on dimension; the prime element needed to feed Nagata's lemma is any element of $\mathfrak m\setminus\mathfrak m^2$, which is prime precisely because the quotient by it is again regular and therefore a domain.

**Theorem 14.43 (the Auslander–Buchsbaum factoriality theorem).** Every regular local ring is a unique factorization domain.

**Proof.** Let $A$ be regular local of dimension $n$, with maximal ideal $\mathfrak m$. It is a domain by Proposition 14.15. We induct on $n$, the statement being that all regular local rings of dimension $n$ are factorial.

If $n=0$ then $A$ is a field and there is nothing to prove. If $n=1$ then $\mathfrak m$ is principal and is the only prime of height one, so Theorem 14.38 applies.

Let $n\geq2$ and choose $x\in\mathfrak m\setminus\mathfrak m^2$, possible because $\mathfrak m\neq\mathfrak m^2$. By Lemma 14.14 the ring $A/(x)$ is regular local of dimension $n-1$, hence a domain by Proposition 14.15, so $x$ is a prime element of $A$. Let $S=\{1,x,x^2,\ldots\}$ and $R=S^{-1}A=A_x$, a noetherian domain. By Theorem 14.39 it suffices to prove that $R$ is factorial, and by Theorem 14.38 it suffices to prove that every height-one prime $Q$ of $R$ is principal.

Such a $Q$ is $\mathfrak qR$ for a unique prime $\mathfrak q$ of $A$ with $x\notin\mathfrak q$ and $\operatorname{ht}\mathfrak q=\operatorname{ht}Q=1$. We verify the two hypotheses of the local-to-global step.

_The module $Q$ has a finite free resolution._ By Theorem 14.36 the ideal $\mathfrak q$, a finite $A$-module, has a resolution $0\to F_r\to\cdots\to F_0\to\mathfrak q\to0$ by finite free $A$-modules with $r\leq n$. Localizing at $S$ is exact and preserves finite freeness, so $Q=S^{-1}\mathfrak q$ has such a resolution over $R$.

_The module $Q$ is free at every localization._ A prime of $R$ is $P=\mathfrak pR$ with $\mathfrak p$ a prime of $A$ not containing $x$, and $R_P=A_{\mathfrak p}$, while $Q_P=\mathfrak qA_{\mathfrak p}$. Since $x\in\mathfrak m\setminus\mathfrak p$, we have $\mathfrak p\neq\mathfrak m$, so Corollary 14.37 makes $A_{\mathfrak p}$ a regular local ring of dimension $\operatorname{ht}\mathfrak p\leq n-1$. By the inductive hypothesis $A_{\mathfrak p}$ is factorial. If $\mathfrak q\not\subseteq\mathfrak p$ then $\mathfrak qA_{\mathfrak p}=A_{\mathfrak p}$ is free of rank one. If $\mathfrak q\subseteq\mathfrak p$ then $\mathfrak qA_{\mathfrak p}$ is a prime of $A_{\mathfrak p}$ of height one, hence principal by Theorem 14.38, say $\mathfrak qA_{\mathfrak p}=tA_{\mathfrak p}$ with $t\neq0$; multiplication by $t$ is injective on the domain $A_{\mathfrak p}$, so $\mathfrak qA_{\mathfrak p}$ is again free of rank one.

By Lemma 14.40 the module $Q$ is a direct summand of a finite free $R$-module, by Lemma 14.41 it is stably free, and by Lemma 14.42 — applied to the nonzero ideal $Q\subseteq R$ of the domain $R$ — it is principal. Hence $R$ is factorial by Theorem 14.38, and $A$ is factorial by Theorem 14.39. $\square$

Two remarks on the shape of the argument are worth recording. The induction is genuinely an induction on the dimension of _other_ rings: what is used about $A$ itself at dimension $n$ is only the existence of a prime element, whereas factoriality of the smaller-dimensional rings $A_{\mathfrak p}$ is what makes the height-one prime locally principal. This is why Corollary 14.37 is indispensable and why the homological characterization of regularity, rather than the numerical one, is the right tool. Second, the finite free resolution is used exactly once, to upgrade "locally principal" to "principal"; the local hypothesis alone would only say that the ideal is invertible, and invertible ideals need not be principal on a general noetherian domain.

**Corollary 14.44.** A factorial domain is integrally closed in its fraction field. Consequently every regular local ring is a normal domain, and a regular noetherian ring is normal.

**Proof.** Let $A$ be factorial with fraction field $K$ and let $z\in K$ be integral over $A$, satisfying
$$
z^d+c_{d-1}z^{d-1}+\cdots+c_0=0,\qquad c_i\in A .
$$

Write $z=a/b$ with $a,b\in A$, $b\neq0$, and cancel all common irreducible factors, which is possible by unique factorization; then no irreducible element divides both $a$ and $b$. Multiplying the equation by $b^d$ gives
$$
a^d=-b\,(c_{d-1}a^{d-1}+c_{d-2}a^{d-2}b+\cdots+c_0b^{d-1}).
$$

If $b$ were a nonunit, an irreducible factor $\pi$ of $b$ would be prime and would divide $a^d$, hence $a$, contradicting the choice of $a$ and $b$. So $b$ is a unit and $z\in A$.

For the consequences, a regular local ring is factorial by Theorem 14.43, hence integrally closed; and if $A$ is a regular noetherian ring, each $A_{\mathfrak p}$ is regular local, hence an integrally closed domain, which is normality. $\square$

Corollary 14.44 makes the two Serre conditions automatic for a regular ring in a way that does not pass through the depth calculus at all: such a ring is normal outright, and the conditions $(R_1)$ and $(S_2)$ then follow from Theorem 14.26. It also completes the picture of Section 4.2, where the equivalence of normality, regularity, and the discrete valuation property in dimension one was asserted with only a sketch: in dimension one, factoriality of a regular local ring gives integral closedness directly, and the reverse implication is the valuation-theoretic characterization of Book 1.

The divisor-theoretic consequence is the one that later chapters and later books consume. On an integral noetherian scheme $X$, a prime divisor $Z$ with generic point $\eta$ corresponds at each point $x\in Z$ to the height-one prime $\mathfrak p_x\subseteq\mathcal O_{X,x}$ of functions vanishing on $Z$. If $X$ is regular, Theorem 14.43 and Theorem 14.38 make every such $\mathfrak p_x$ principal, so $Z$ is cut out near $x$ by a single equation. Thus on a regular integral noetherian scheme every Weil divisor is Cartier, and the group of Weil divisors, the group of Cartier divisors, and the group of invertible fractional ideal sheaves coincide. For a regular arithmetic surface this is the statement that both the horizontal divisors of Section 5.3 and the components of the special fibers are locally principal, which is what allows the intersection numbers of Section 11.1 to be defined by pulling back local equations.

### 14.9 What the criteria return to the models

The chapter closes by recording where each result is used.

Section 4.1 proved Serre's criterion in the codimension-two form needed by the intervening
chapters. Theorem 14.26 rederives the general ring statement from the expanded depth calculus:
Theorem 14.23 supplies the forward implication, while Theorem 14.24 and Lemma 14.25 supply the
converse. In this respect the chapter is an expansion of Section 4.1 rather than a prerequisite for it.

Sections 14.7 and 14.8 are the exception, and deliberately so: Proposition 4.2 and the divisor
calculus of Chapters 5, 9, and 11 use the factoriality of regular local rings, and Theorem 14.43 is
where that is proved. No circularity arises, because the proof of Theorem 14.43 draws only on
Sections 14.1 to 14.4 — depth, the Auslander–Buchsbaum formula, and the elementary properties of
regular local rings — and never on Serre's normality criterion or on Proposition 4.2.

Section 4.2 identified normal, regular, and discrete valuation rings in dimension one. Its
valuation-theoretic half is Book 1, Theorem 4.1; the implication from regularity to normality is
Theorem 14.43 together with Corollary 14.44, and the resulting statement is used inside Theorem
14.26.

Section 4.3 asserted that the quadratic cone is normal because it is a Cohen–Macaulay hypersurface with a codimension-two singularity. The example after Theorem 14.20 proves it, and the same three steps prove Theorem 14.20 itself for the arithmetic family $xy=\pi^n$.

Section 4.4 gave the hypersurface regularity test $f\notin\mathfrak n^2$; that is Corollary 14.18, and it identifies $n=1$ as the only regular member of the family $xy=\pi^n$.

Sections 8.5 and 10.4 blow up the singular members of that family. Theorem 14.20 shows what the blowups are for: the surfaces $xy=\pi^n$ with $n\geq2$ are normal, so normalization is powerless against them and only a resolution helps. This is the precise sense in which normalization and resolution repair different defects.

Section 11.4 and Section 12.4 use the semistable local equation $xy=\pi$ and its completion. Theorem 14.20(3) proves regularity of the algebraic local ring at the node, and regularity is unchanged by completion, because dimension and the cotangent space are both preserved; the same holds for the Cohen–Macaulay property by Proposition 14.9. Under the standard identification of the completion of $R[x,y]_{(\pi,x,y)}$ with $\widehat R[[x,y]]$, the completed ring is the one displayed in Section 12.4, so that ring is regular and no resolution acts on it.

Theorems 14.27 and 14.30 and Corollary 14.29 are stated in the form that later books require: over a two-dimensional regular local ring, a finite module of depth two is free, and this applies to reflexive modules and to finite normal local domains. The hypothesis that cannot be dropped is depth, not torsion-freeness: a torsion-free module has depth at least one, which in dimension two is not enough, and the freeness statement genuinely uses the second regular parameter.

Sections 14.7 and 14.8 close the last two gaps in the treatment of regularity itself. Corollary 14.37 proves that regularity passes to localizations, which the standing terminology of Section 1.2 and the fiberwise arguments of Section 4.4 both presuppose, and which Theorem 14.20 and the quadratic-cone example verified by hand in their particular cases. Theorem 14.43 proves that a regular local ring is factorial, so that Proposition 4.2 is complete as stated, so that the normality of regular schemes recorded in Corollary 14.44 needs no separate verification, and above all so that on a regular arithmetic surface every prime divisor is locally cut out by one equation. That last statement is the standing hypothesis behind the divisor calculus of Chapters 5, 9, and 11: it is what identifies Weil divisors with Cartier divisors, hence what makes the intersection pairing of Section 11.1 well defined and computable from local equations. The chain of implications is worth naming once more, because each link was proved here: regular implies finite global dimension (Theorem 14.36), finite global dimension localizes (Corollary 14.37), locally free plus finite free resolution implies free (Lemmas 14.40 to 14.42), and factoriality follows by descent along one prime element (Theorem 14.39).
