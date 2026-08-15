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
   - [The differential trace in inseparable degree p](#83-the-differential-trace-in-inseparable-degree-p)
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
    - [What the criteria return to the models](#147-what-the-criteria-return-to-the-models)

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

A domain $A$ is **Japanese** if the integral closure of $A$ in every finite extension of its fraction field is a finite $A$-module. A noetherian ring is **Nagata** if each quotient by a prime is Japanese. This is the finiteness condition for normalization of finite-type schemes. An excellent ring is, in particular, universally catenary, has geometrically regular formal fibers, and satisfies a uniform openness condition for regular loci; every excellent ring is Nagata. Excellence supplies more than normalization finiteness: it permits completion and localization to reflect the regularity information used in surface resolution.

A morphism is **proper** if it is separated, of finite type, and universally closed. It is **projective** if it factors as a closed immersion into a projective space over the base. Projective implies proper. The converse holds in many curve situations after extra arguments, but it is not a definition and is not assumed silently.

The logical implications needed later are

$$
\text{smooth over a regular base}\Longrightarrow\text{regular},
$$

$$
\text{regular}\Longrightarrow\text{normal},
\qquad
\text{excellent}\Longrightarrow\text{Nagata}.
$$

None of the reverse implications is valid in this generality.

### 1.3 Standing conventions

Unless otherwise specified, rings are commutative and schemes are noetherian. A **curve over a field** is a separated finite-type scheme of pure dimension one. A **smooth proper curve** is also assumed geometrically connected when a single function field is used. If $S$ is integral, its generic point is $\eta$ and its function field is $K=\kappa(\eta)$. For an $S$-scheme $X$, write $X_K=X\times_S\operatorname{Spec}K$.

A **model** of a $K$-scheme $C$ is a flat finite-type $S$-scheme $X$ together with an identification $X_K\simeq C$. A proper, projective, normal, or regular model has the indicated additional property. Flatness is part of the word “model”: without it, vertical embedded components can be added without changing the generic fiber.

The valuation and Dedekind facts developed in Book 1 will be used freely. Relative projective constructions and their base-change behavior come from Book 8. Effective faithfully flat descent, when invoked, is the descent theory of Book 10. All local algebra specific to normalization and two-dimensional regularity is proved here.

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

To apply the criterion to a finite-type scheme over a base, one still needs a permanence theorem for the base condition. That permanence is supplied below in the excellent case actually used here: finite-type algebras over an excellent ring are excellent, and excellent rings are Nagata. Merely assuming that the base is Nagata would require the separate theorem that finite-type algebras over a Nagata ring remain Nagata.

### 3.2 Excellent rings

Excellence is a package designed to make local algebra survive completion and finite-type passage. A noetherian ring $A$ is excellent when:

1. $A$ is universally catenary;
2. for each prime $\mathfrak p$, the formal fibers of $A_{\mathfrak p}\to\widehat{A_{\mathfrak p}}$ are geometrically regular;
3. for every finite-type $A$-algebra, the regular locus is open.

The third condition is often called the $J_2$ property. The first controls dimensions in chains of specializations; the second controls completion; the third lets singular points be isolated in a closed set. These are exactly the three roles excellence plays in resolving arithmetic surfaces.

**Theorem 3.2.** Excellent rings are Nagata. Localizations and finite-type algebras over excellent rings are excellent. Complete noetherian local rings, fields, and Dedekind domains arising by localization from rings of integers of number fields are excellent.

**Proof of the finiteness assertion.** We record the criterion that makes the argument effective. Let $A$ be a noetherian domain whose formal fibers are geometrically regular and whose finite-type algebras have open regular locus. For a finite extension $L/K(A)$, choose a finite $A$-subalgebra $C\subset L$ with fraction field $L$. Apply openness of the regular locus to $C$ and to each reduced fiber over $A$. There is a nonzero $a\in A$ such that $C_a$ is regular over the normal locus of $A_a$; hence $C_a$ is integrally closed and equals the integral closure there.

It remains to cross $V(a)$. Localize at a generic point $\mathfrak p$ of this closed set and complete. Geometric regularity of the formal fiber implies that normalization after completion is finite and descends from a finite neighborhood: a monic relation in the completion has only finitely many coefficients, and faithful flatness contracts the resulting finite module to $A_{\mathfrak p}$. Thus the normalization is finite on an open neighborhood of every generic point of $V(a)$. Remove those neighborhoods. The remaining closed subset has smaller dimension. Noetherian induction proves finiteness everywhere. Applying this to every quotient $A/\mathfrak p$ gives the Nagata property.

Universal catenarity and stability of geometrically regular formal fibers under localization and finite-type extension prove the two permanence assertions. Fields are immediate. For a complete noetherian local ring, the coefficient-ring structure and the lifting criterion for regularity give geometrically regular formal fibers and openness of the regular locus. Rings of integers are finite over $\mathbf Z$, and their localizations inherit excellence. $\square$

The proof displays the three functions of excellence: regular formal fibers cross from a local ring to its completion, openness spreads a finite calculation to a neighborhood, and noetherian induction crosses the remaining closed set. Thus excellence turns a generic finite field extension into a finite geometric normalization.

### 3.3 The one-dimensional proof

The relevant one-dimensional finiteness can be seen more concretely. Let $A$ be an excellent one-dimensional noetherian domain and $L/K$ finite. Choose a $K$-basis of $L$ and clear denominators so that an $A$-subalgebra $B_0\subset L$, finite over $A$, has fraction field $L$. Its normalization $B$ is finite by the Nagata property. Localizing at a nonzero prime $\mathfrak p$ of $A$ gives a finite semilocal normal one-dimensional algebra.

Every local factor $B_{\mathfrak q}$ is a noetherian normal local domain of dimension one, hence a discrete valuation ring. Therefore the integral closure of an excellent Dedekind domain in a finite separable extension is again Dedekind and finite over the original ring. This recovers, in the global form needed here, the local valuation picture of Book 1.

There is also a useful trace argument when $L/K$ is separable. Choose a $K$-basis $e_1,\ldots,e_n$ of $L$ and multiply its elements by nonzero scalars of $A$ so that every $e_i$ is integral over $A$. If $e_1^*,\ldots,e_n^*$ is the trace-dual basis and $x$ is integral over $A$, then every product $xe_i$ is integral. Its field trace, being a coefficient of the characteristic polynomial of multiplication by $xe_i$, is integral over $A$ and lies in $K$; because $A$ is integrally closed, $\operatorname{Tr}_{L/K}(xe_i)\in A$. Hence

$$
x=\sum_i\operatorname{Tr}_{L/K}(xe_i)e_i^*
$$

lies in the finite free fractional $A$-module $\sum_iAe_i^*$. The integral closure, as an $A$-submodule of that module, is finite because $A$ is noetherian. Thus every Dedekind domain is Japanese for finite separable extensions. The trace form degenerates for inseparable extensions, which is why the Japanese formulation is the correct general hypothesis.

### 3.4 The two-dimensional cases used here

Let $R$ be an excellent Dedekind domain and $A$ a finite-type $R$-domain whose generic fiber has dimension one. Then $A$ has dimension at most two, and it has dimension two when $\operatorname{Spec}A$ dominates $\operatorname{Spec}R$. By stability of excellence under finite type, $A$ is excellent and hence Nagata. Its normalization in any finite extension of its fraction field is finite.

This proves the central finiteness statement for arithmetic surfaces:

**Theorem 3.3.** If $X$ is a reduced finite-type scheme over an excellent Dedekind scheme $S$, then $X^{\mathrm{nor}}\to X$ is finite. If $X\to S$ is proper, respectively projective, then its normalization is proper, respectively projective, over $S$.

**Proof.** Every affine coordinate ring of $X$ is a finite-type algebra over an excellent ring, hence is excellent and therefore Nagata by Theorem 3.2. Finiteness is now Theorem 3.1. A finite morphism is projective and proper. Composing it with a proper morphism gives a proper morphism. If $X\hookrightarrow\mathbf P^n_S$, a finite morphism $Y\to X$ is projective; composing projective morphisms proves projectivity of $Y/S$. $\square$

The theorem remains valid for two-dimensional schemes of finite type over a field or over a complete noetherian local ring. These cases cover local surface charts and completed local calculations.

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

The complete proof, together with the depth calculus that makes $(S_2)$ well defined, is Chapter 14; Theorem 14.26 is the criterion itself and shows that reducedness is a consequence rather than an extra hypothesis. The following strategy explains the mechanism.

**Proof strategy.** An integrally closed domain is the intersection of its height-one valuation rings inside its fraction field. Condition $(R_1)$ identifies those local rings as discrete valuation rings, while $(S_2)$ ensures that functions regular away from codimension at least two extend.

For the forward implication, a noetherian normal local domain has depth at least two when its dimension is at least two: if a nonzero $a\in\mathfrak m$ were such that every element of $\mathfrak m$ were a zero divisor modulo $a$, prime avoidance would force an associated height-one prime incompatible with integral closedness. Height-one localizations are one-dimensional noetherian normal local domains and hence discrete valuation rings. Conversely, assume $(R_1)$ and $(S_2)$. If $x$ in the fraction field is integral over $A$, it belongs to every height-one localization. The intersection theorem supplied by $(S_2)$ gives

$$
A=\bigcap_{\operatorname{ht}\mathfrak p=1}A_{\mathfrak p}
\quad\text{inside }K(A),
$$

so $x\in A$. $\square$

This criterion explains a major feature of normal surfaces: their nonregular locus has codimension at least two and therefore consists of closed points locally. If the surface is of finite type over a Dedekind scheme, the singular locus is closed by excellence; on a quasi-compact surface it is a finite set whenever it contains no curve.

### 4.2 The dimension-one coincidence

**Proposition 4.2.** For a noetherian local domain $A$ of dimension one, the following are equivalent:

1. $A$ is normal;
2. $A$ is a discrete valuation ring;
3. $A$ is regular.

**Proof.** Normality implies that every nonzero ideal has a factor of least valuation, giving a principal maximal ideal; this is the discrete valuation characterization. A one-dimensional local ring with principal maximal ideal has embedding dimension one and is regular. Conversely, a regular local ring is a unique factorization domain in codimension one and is integrally closed. $\square$

Consequently a normal curve over a perfect field is regular, and because its residue extensions are separable, it is smooth. Over an imperfect field, regular need not imply smooth: geometric regularity can fail after a purely inseparable field extension. This is the first reason to keep “regular” and “smooth” separate.

### 4.3 Normal surfaces need not be regular

Let $k$ have characteristic different from $2$ and consider

$$
A=k[x,y,z]/(xy-z^2).
$$

This two-dimensional domain is singular at the origin because its maximal ideal needs three generators. Yet it is normal. Indeed, it is a hypersurface and hence Cohen–Macaulay, so it satisfies $(S_2)$; its only singular point has codimension two, so $(R_1)$ holds. Serre's criterion applies. Every step of this verification, including the Cohen–Macaulay property of a hypersurface and the location of the singular locus, is carried out in Section 14.4.

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

Let $S$ be an excellent Dedekind scheme: a connected, normal, noetherian scheme of dimension one whose local rings at closed points are excellent discrete valuation rings. An **arithmetic surface over $S$** is an integral, normal, flat, finite-type $S$-scheme $X$ of relative dimension one. When $X$ is proper, it is a proper arithmetic surface.

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

* $R[x]$ is smooth and regular; the special fiber is a smooth affine line.
* $R[x,y]/(xy-\pi)$ is regular and flat; the special fiber has an ordinary node. It is the basic semistable equation.
* $R[x,y]/(xy-\pi^n)$ for $n>1$ is normal but singular at the origin. Its resolution produces a chain between the two branches.
* $R[x,y]/(y^2-x^3-\pi)$ can be regular even though the special fiber is cuspidal; regular total space does not make the fiber nodal.
* $R[x]/(\pi x)$ has vertical torsion and is not flat.

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

Let $X_0$ be the integral projective closure. Normalize it in $K(C)$. Since $S$ is excellent and $X_0$ is finite type over $S$, Theorem 3.3 makes

$$
\nu:X_1\longrightarrow X_0
$$

finite. Therefore $X_1$ is projective over $S$. It is integral and normal by construction, and it remains flat because it dominates $S$. Its generic fiber is $C$: a smooth curve is normal, so normalization is an isomorphism there.

**Theorem 6.2 (normal model theorem).** Every smooth projective geometrically connected curve over the function field of an excellent Dedekind scheme has a normal flat projective model. Given a smooth projective model over a nonempty open $U\subset S$, the normal model may be chosen to restrict to it.

For the relative clause, choose a relatively very ample bundle on the given projective $U$-model, embed it in $\mathbf P^N_U$, and extend its finitely many equations after shrinking the ambient trivializations only outside $U$. The schematic closure in $\mathbf P^N_S$ then restricts exactly to the given model. Since that model is normal, normalization changes nothing there. The word projective is necessary: the restriction of a projective $S$-model is projective, so an arbitrary nonprojective regular model over $U$ cannot be prescribed in this statement.

### 6.5 Existence and uniqueness up to modification

A **modification** is a proper birational morphism. Normal models are not unique, but any two proper models of $C$ admit a common proper model dominating both.

**Proposition 6.3.** Let $X$ and $Y$ be proper $S$-models of $C$. The closure $Z_0$ of the diagonal copy of $C$ in $X\times_SY$ is proper over $S$, and its two projections are modifications. If $S$ is excellent, the normalization $Z$ of $Z_0$ is finite and gives a normal proper common domination.

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

If $X$ is normal and $\operatorname{Bl}_{\mathcal I}X$ is not normal, define the **normalized blowup** as its normalization. Over an excellent scheme of finite type, this normalization is finite. Hence the normalized blowup remains projective and birational over $X$.

The construction combines two corrections. Blowup changes the birational geometry so that an ideal becomes invertible; normalization then restores integrally closed local rings. For a surface, normalized blowups centered at closed singular points keep all codimension-one local rings under valuation control.

There is a valuation interpretation. Let $A$ be a normal domain and $I$ a nonzero ideal. The normalization of the Rees algebra $A[It]$ in $A[t]$ is graded; its degree-$n$ part is the integral closure $\overline{I^n}$. The normalized blowup is therefore

$$
\operatorname{Proj}\bigoplus_{n\geq0}\overline{I^n}.
$$

It depends only on the integral-closure class of the ideal. Divisorial valuations appearing on the exceptional locus measure the asymptotic orders of the powers $I^n$.

### 7.4 Locality and projectivity

Blowing up is local on the target and projective over it. If an ideal is supported in a closed subset $Z$, the blowup is an isomorphism over $X\setminus Z$. Thus resolutions may be performed one singular point at a time and glued with the unchanged regular open.

For arithmetic surfaces, every chosen center will be vertical and disjoint from the generic fiber. The resulting morphism is then an isomorphism on the generic curve. A composite of finitely many blowups and finite normalizations is projective. Consequently resolving a projective model keeps it projective, not merely proper.

## 8. Resolving surface singularities

### 8.1 The resolution theorem in the required setting

The central low-dimensional theorem is not a formal consequence of normalization, excellence, or
the elementary blowup calculations above. We therefore isolate exactly the additional result used
from this point onward.

**Prerequisite 8.1 (surface resolution, SR2).** Let $X$ be a reduced excellent noetherian scheme of
dimension at most two, and let $U\subseteq X$ be a regular open subscheme. There exists a projective
birational morphism

$$
r:X'\longrightarrow X
$$

such that $X'$ is regular and $r$ is an isomorphism over $U$.

This is the precise relative form needed in this book: projectivity keeps projective models
projective, and the clause involving $U$ preserves the generic fiber and every prescribed good
open. SR2 is a substantial theorem on excellent surfaces. It is not proved in Books 1--10, and it
is not proved in this volume. Thus the phrase **assuming SR2** is a genuine mathematical
hypothesis, not an abbreviation for the paragraphs below.

For an arithmetic surface normalized as in Chapter 6, the singular locus is a finite set of
closed points. In that special situation SR2 says that the exceptional locus may be kept above
those points. It still contains the hard local assertion that every singularity lying above them
is eliminated by one projective modification.

### 8.2 Preparing the singular locus

We first record the elementary reduction that any proof of SR2 must use.

**Lemma 8.2 (surface preparation).** Let $X$ be a reduced excellent noetherian scheme of dimension at most two, let $U=X_{\mathrm{reg}}$, and let $\nu:X^{\nu}\to X$ be its componentwise normalization. Then $\nu$ is finite and is an isomorphism over $U$. The singular locus of $X^{\nu}$ is a closed subset of codimension at least two, and hence is finite.

**Proof.** Reduce $X$, separate its irreducible components by normalization, and use finiteness from the Nagata property. A normal noetherian surface satisfies $(R_1)$, so every codimension-zero or codimension-one point is regular. Excellence makes the regular locus open. Hence the singular locus is closed and consists of dimension-zero points. A noetherian zero-dimensional closed space has finitely many points. $\square$

Thus the new input needed for SR2 is local at the finitely many singular points: one must resolve $\operatorname{Spec}A$ for a two-dimensional excellent normal local domain $(A,\mathfrak m)$. A modification supported at $\mathfrak m$ glues to the identity away from that point. If the required local modifications exist and terminate, those over the finitely many prepared points can be composed without disturbing the regular open.

Completion is a powerful diagnostic but must be used with care. Excellence gives that
$A\to\widehat A$ is a regular faithfully flat map, so $A$ is regular if and only if $\widehat A$
is. It does not follow merely from excellence that a center constructed in $\widehat A$ descends to
$A$, nor that numerical inequalities proved after completion survive an approximation. Those are
parts of a proof of SR2, not consequences of the preparation lemma.

### 8.3 The differential trace in inseparable degree $p$

The boundedness argument used below must survive a finite purely inseparable extension. Ordinary
field trace vanishes in that case, so we first construct the replacement on differential forms.

Let $R$ be an $\mathbf F_p$-algebra, let $a\in R$, and put
$T=R[x]/(x^p-a)$. As an $R$-module, $\Omega_{T/R}$ is free on
$dx,x,dx,\ldots,x^{p-1}dx$. Define

$$
\tau_x:\Omega_{T/R}\longrightarrow\Omega_R,
\qquad
\tau_x(x^i dx)=
\begin{cases}
0,&i<p-1,\\
da,&i=p-1.
\end{cases}
\tag{8.1}
$$

**Lemma 8.3 (coordinate independence).** If
$R[x]/(x^p-a)\to R[y]/(y^p-b)$ is an $R$-algebra map, then
$\tau_x=\tau_y\circ d$.

**Proof.** Write the image of $x$ as
$u=\lambda_0+\lambda_1y+\cdots+\lambda_{p-1}y^{p-1}$. The relation $u^p=a$ says

$$
a=\lambda_0^p+\lambda_1^pb+\cdots+\lambda_{p-1}^pb^{p-1}.
\tag{8.2}
$$

For $i<p-1$, the coefficient of every $y^{mp-1}$ in $u^i(du/dy)$ is zero, since this
polynomial is $(i+1)^{-1}d(u^{i+1})/dy$. Reduction by $y^p=b$ therefore gives
$\tau_y(u^i,du)=0$. For $i=p-1$, perform the calculation over
$\mathbf Z[b,\lambda_0,\ldots,\lambda_{p-1}]$ before reducing modulo $p$. The coefficients of
$y^{mp-1}$ in $u^{p-1}du/dy=p^{-1}d(u^p)/dy$ reduce to

$$
\lambda_1^p+2\lambda_2^pb+\cdots+(p-1)\lambda_{p-1}^pb^{p-2}.
$$

Multiplying by $db$ gives $da$ by differentiating (8.2). These values agree with (8.1) on its
$R$-basis. $\square$

**Lemma 8.4 (trace on exterior powers).** If
$\mathbf F_p\subseteq\Lambda\subseteq R\subseteq T$ and $T=R[x]/(x^p-a)$, there are canonical
$R$-linear maps, for $q\ge1$,

$$
\tau:\Omega^q_{T/\Lambda}\longrightarrow\Omega^q_{R/\Lambda}
$$

which kill the image of $T\otimes_R\Omega^q_{R/\Lambda}$ and satisfy

$$
\tau(\eta_1\wedge\cdots\wedge\eta_{q-1}\wedge x^i dx)
=\eta_1\wedge\cdots\wedge\eta_{q-1}\wedge\tau_x(x^i dx).
$$

**Proof.** The cotangent sequence has the presentation

$$
T\,d(x^p-a)\longrightarrow T\otimes_R\Omega_{R/\Lambda}
\longrightarrow\Omega_{T/\Lambda}\longrightarrow T,dx\longrightarrow0.
$$

Its first arrow sends the displayed generator to $-da$. Quotient
$\Omega_{R/\Lambda}$ by $R,da$, take the $(q-1)$-st exterior power, and tensor with
$\Omega_{T/R}$. Wedging the resulting class with $\tau_x$ is independent of the chosen lifts,
because every ambiguity is a multiple of $da$ and $da\wedge da=0$. Lemma 8.3 proves
functoriality and hence canonicity. $\square$

**Proposition 8.5 (trace on normal surfaces).** Let $Y\to X$ be finite between noetherian normal
integral schemes of characteristic $p$, with purely inseparable function-field extension of
degree $p$. If $X$ is of finite type over a base $S$, the generic trace extends uniquely to

$$
f_*\Omega^q_{Y/S}\longrightarrow(\Omega^q_{X/S})^{**},\qquad q\ge1.
\tag{8.3}
$$

**Proof.** Both sides are coherent, and the target is reflexive. A map into a reflexive module on
a normal scheme extends uniquely once it extends at every height-one point. At such a point the
local ring of $X$ is a DVR. Its integral closure in the degree-$p$ extension is again a DVR and
is either totally ramified or has residue degree $p$; in both cases it has the form
$A[t]/(t^p-c)$, with $c$ respectively a uniformizer or a unit. Lemma 8.4 supplies the integral
map there. Intersecting the height-one extensions inside the generic reflexive module gives
(8.3). $\square$

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

**Lemma 8.8 (factorization through point blowups).** Let $T$ be a regular integral surface and
$Z\to T$ a projective birational morphism. There is a sequence of blowups at closed regular
points $T_r\to\cdots\to T_0=T$ and a morphism $T_r\to Z$ over $T$.

**Proof.** Write $Z$ as the blowup of a coherent fractional ideal after replacing a relatively
ample bundle by a generated power. Remove its invertible height-one part. Locally the remaining
ideal is primary to a closed point. Blow up that point and divide by the largest exceptional
power. If the transform is not invertible, repeat at its finitely many base points. Termination is
measured by two general members $a,b$ of a reduction of the ideal: on a point blowup,

$$
\operatorname{length}A/(a,b)
=\operatorname{ord}(a)\operatorname{ord}(b)[k(x):k]
+\sum_{x'\mapsto x}\operatorname{length}\mathcal O_{T',x'}/(a',b').
$$

This follows by filtering the two blowup charts by the exceptional parameter. Every unresolved
base point leaves a positive first term, so the sum of residual lengths strictly decreases.
Over a finite residue field, use the product of all closed base points; the residue degrees in the
formula give the same decrease. Eventually the ideal is invertible, and the universal property of
the blowup supplies $T_r\to Z$. $\square$

**Lemma 8.9 (normalized-blowup domination).** Let $A$ be a two-dimensional normal noetherian
local domain with finite normalization after every finite-type modification. Every proper
birational modification of $\operatorname{Spec}A$ is dominated by a finite composite of
normalized blowups in ideals supported at the closed point.

**Proof.** Chow's lemma gives a projective modification dominating the given one. A projective
birational morphism is the blowup of a fractional ideal after taking a generated relatively ample
power. Replace its Rees algebra by its finite graded normalization. The resulting normalized
blowup dominates the projective modification. Repeating on the finitely many affine charts where
the comparison is not yet a morphism decreases the base-ideal colength exactly as in Lemma 8.8;
no new codimension-one center occurs because both schemes are normal and already agree there.
$\square$

### 8.5 The remaining local resolution chain

The trace and quadratic-transformation results above are the first inputs to the resolution
proof. We next construct the duality and vanishing package, prove boundedness under finite
extensions, pass through rational singularities and rational double points, and lift normalized
blowups from completions. Only after those steps will Theorem 8.1 be discharged.

#### 8.5.1 Local duality in dimension two

Let $(A,\mathfrak m,k)$ be a two-dimensional normal local ring possessing a normalized dualizing
complex. Normality gives depth two, so the complex is $\omega_A[2]$ for a finite maximal
Cohen--Macaulay module $\omega_A$. Choose an injective resolution of this complex and apply the
$\mathfrak m$-torsion functor. The only surviving indecomposable injective at the closed point is
the injective hull $E_A(k)$ in degree zero. Consequently, for every finite-length module $M$,

$$
\operatorname{Ext}^i_A(M,\omega_A)=0\ (i\ne2),
\qquad
\operatorname{Ext}^2_A(M,\omega_A)=\operatorname{Hom}_A(M,E_A(k)).
\tag{8.7}
$$

The last functor is an exact length-preserving duality on finite-length modules: induction on a
composition series reduces this to $\operatorname{Hom}_A(k,E_A(k))=k$.

For a proper modification $f:X\to\operatorname{Spec}A$, define
$\omega_X[2]=f^!(\omega_A[2])$. The functor $f^!$ is constructed on a projective factorization
$X\hookrightarrow\mathbf P^n_A$ by a finite locally free resolution and the formula

$$
f^!K=R\mathcal Hom_{\mathbf P^n_A}
(\mathcal O_X,K\otimes\omega_{\mathbf P^n_A/A}[n])[-n].
$$

Changing the embedding gives the same object: tensor the two resolutions, use the Koszul
resolution of the diagonal, and cancel the two projective-space canonical bundles. The same
calculation gives the adjunction identity

$$
R\operatorname{Hom}_A(Rf_*F,\omega_A[2])
\simeq Rf_*R\mathcal Hom_X(F,\omega_X[2]).
\tag{8.8}
$$

Thus no duality statement beyond finite locally free resolutions, Cech cohomology on projective
space, and the displayed diagonal calculation is being assumed here.

#### 8.5.2 Vanishing on a normal modification

**Lemma 8.10 (positive conormal).** Let $X$ be a normal modification of
$\operatorname{Spec}A$ and let $0\ne Z$ be an effective Cartier divisor supported on the closed
fiber. Some component $C$ of $Z$ has $\deg(\mathcal I_Z|_C)>0$.

**Proof.** Choose a function $h\in\mathfrak m$ whose divisor contains every closed-fiber
component and, on each component, has a point away from all the others where its residual factor
vanishes. If $d_C$ and $e_C$ are the orders of $Z$ and $h$ at the generic point of $C$, choose
$C$ maximizing $d_C/e_C$ and replace $Z,h$ by multiples making the two orders equal. Then $h$
is a section of $\mathcal I_Z$ which is generically nonzero on $C$ and has a zero at the chosen
point. Its divisor on the proper curve $C$ has positive degree. $\square$

**Lemma 8.11 (punctured injection).** The restriction
$H^1(X,\mathcal O_X)\to H^1(X\setminus X_s,\mathcal O_X)$ is injective.

**Proof.** A class in the kernel gives an extension
$0\to\mathcal O_X\to\mathcal E\to\mathcal O_X\to0$ split off the closed fiber. The two sections
of $\mathbf P(\mathcal E)$ are disjoint there. Normalize the closure of the second section. If it
missed the first, its proper affine map to $X$ would be finite and hence an isomorphism, splitting
the extension. Otherwise their pullback intersection is a nonempty vertical Cartier divisor with
trivial conormal, contradicting Lemma 8.10. $\square$

**Proposition 8.12 (surface vanishing).** For a normal modification as above,
$R^1f_*\omega_X=0$.

**Proof.** Adjunction turns a map $k[-1]\to Rf_*\mathcal O_X$ into an extension of the closed
fiber by $\mathcal O_X$. Pulling back along $\mathcal O_X\to\mathcal O_{X_s}$ gives a class
which is split off the fiber and hence zero by Lemma 8.11. A lifted section shows the original
extension is multiplication by an element of $A$ and is therefore split. Thus
$\operatorname{Hom}_{D(A)}(k[-1],Rf_*\mathcal O_X)=0$.

If $R^1f_*\omega_X\ne0$, quotient it onto $k$. Applying the duality (8.8) produces a nonzero map
$k[-1]\to Rf_*\mathcal O_X$, contradiction. $\square$

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

**Lemma 8.13 (annihilator bound).** Fix $0\ne a\in A$. The lengths of
$H^1(X,\mathcal O_X)[a]$ are bounded independently of the normal modification $X$.

**Proof.** The exact sequence cut out by $a$ identifies this torsion module with the cokernel of
$A\to H^0(Z,\mathcal O_Z)$. After replacing $a$ by a power, $A/(a)$ is reduced. The closure of
the punctured part of $Z$ is finite over $A/(a)$ and embeds in its finite normalization; its
global sections therefore differ from $A/(a)$ by a subquotient of the fixed finite module
$(A/(a))^\nu/(A/(a))$. Embedded vertical points contribute no global section on the normal
surface. Its length is the required bound. $\square$

Call $A$ **bounded** if the integers $g(X)$ are bounded. Choosing a modification with maximal
$g(X)$ and using (8.9) shows that every local ring on it has
$H^1(Y,\mathcal O_Y)=0$ for every further normal modification $Y$; such a local ring is called a
**rational singularity**. Lemma 8.9 replaces the chosen modification by a finite sequence of
normalized blowups without losing this property.

**Lemma 8.14 (finite extensions preserve boundedness).** Let $A\subset B$ be finite between
normal two-dimensional local domains.

1. If the fraction-field extension is separable and $A$ is bounded, then $B$ is bounded.
2. If $A=k[[u,v]]$ has characteristic $p$ and the fraction-field extension is purely inseparable
   of degree $p$, then $B$ is bounded.

**Proof.** In the separable case choose a field basis in $B$. The determinant $d\ne0$ of its
trace pairing makes $\pi_*\mathcal O_Y$ sit between two free modules with cokernel killed by $d$
on every finite comparison $Y\to X$. Cohomology, (8.9), and Lemma 8.13 give a uniform bound.

For the inseparable case write $L=K(t)$, $t^p=q$. Choose a finite subfield
$k^p\subset k_0\subset k$ such that $dq\ne0$ over
$A_0=k_0[[u^p,v^p]]$. Put $r=\operatorname{rank}\Omega_{A/A_0}$ and
$\omega_A=\Omega^r_{A/A_0}$. Proposition 8.5 and the blowup calculation in Lemma 8.6 give, on
every finite comparison $Y\to X$,

$$
\pi_*(\Omega^r_{Y/A_0})^{**}\longrightarrow
(\Omega^r_{X/A_0})^{**}\longrightarrow\omega_X.
$$

Choose $\eta$ with $\theta=\eta\wedge dq\ne0$. The forms
$\eta\wedge t^{p-1-i}dt$ map to the $A$-linear functionals sending $t^j$ to
$\delta_{ij}\theta$. Hence a fixed nonzero element kills the cokernel of
$H^0(Y,\omega_Y)\to\omega_B$. By (8.8), (8.7), and Proposition 8.12 this cokernel is the Matlis
dual of $H^1(Y,\mathcal O_Y)$; Lemma 8.13 supplies the uniform bound. $\square$

#### 8.5.4 Rational singularities and the Gorenstein reduction

**Lemma 8.15 (blowing up a rational singularity).** If $A$ is rational, the ordinary blowup
$X'=\operatorname{Proj}\bigoplus_{n\ge0}\mathfrak m^n$ is normal, and every local ring on it is
rational.

**Proof.** Normalize $X'$ to $\nu:X\to X'$ and put
$\mathcal I=\mathfrak m\mathcal O_X$. Rationality makes $H^1(X,\mathcal F)=0$ for every globally
generated $\mathcal F$: resolve it by a direct sum of $\mathcal O_X$ and use that coherent
cohomology above degree one vanishes on a surface modification. From

$$
0\to\mathcal F\to\mathcal O_X^{\mu+1}\to\mathcal I\to0
$$

and its twists one obtains inductively
$H^1(X,\mathcal I^n)=0$ and $H^0(X,\mathcal I^n)=\mathfrak m^n$ for all $n$. The projection
formula therefore identifies every graded piece of
$\bigoplus H^0(X,\nu^*\mathcal O_{X'}(n))$ with the Rees algebra. A finite morphism over Proj is
recovered from these twists, so $\nu$ is an isomorphism. Rationality of its local rings follows
by spreading any local modification to a modification of $X$ and applying (8.9). $\square$

Let $E$ be its exceptional curve. The preceding exact sequences give

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
gives $\omega_X|_E=\omega_E(1)$. The curve duality calculation and (8.10) show
$H^1(X,\omega_X(n))=0$ for $n\ge0$ and that $\omega_E(1)$ is generated. Hence
$f^*\omega_A\to\omega_X$ is surjective at every singular point.

Blow up the Fitting ideal of the rank-one module $\omega_A$; its torsion-free transform is
invertible. Dominate this blowup by point blowups using Lemma 8.9. Lemma 8.15 says each stage is
normal and rational. Along a chain ending at a singular point the preceding surjections persist;
there the invertible torsion-free transform surjects onto the torsion-free rank-one module
$\omega_X$, hence is an isomorphism. At regular points the dualizing module is already invertible.
$\square$

A rational singularity with invertible dualizing module is called a **rational double point**.
The remaining tasks are now sharply delimited: prove that successive blowups resolve rational
double points, and lift the resulting normalized-blowup sequence from the completion.

### 8.6 Why a three-entry local invariant is insufficient

After Lemma 8.2, the missing local assertion can be stated without global language. For every
singular excellent normal two-dimensional local domain $(A,\mathfrak m)$, one must construct a
projective birational modification supported at $\mathfrak m$ whose local rings are all regular.
Doing this compatibly with the regular punctured spectrum, and then showing that the construction
terminates after finitely many stages, is the local core of SR2.

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
a normalized blowup. Accordingly this volume does not assert the former ``surface decrease lemma'':
that lemma was the unresolved theorem rather than a proof of it. SR2 is the exact replacement.

### 8.7 Termination

Assume SR2, and let $X$ be a normal arithmetic surface produced by Chapter 6. Lemma 8.2 shows that
its singular locus is a finite set of closed points, but does not construct a modification. Apply
SR2 directly, taking for $U$ the regular locus or any smaller regular open that contains the generic
fiber and every prescribed good fiber. It gives a projective birational morphism $X'\to X$ with
$X'$ regular and with no change over $U$. Projectivity is part of the prerequisite because it is
required to preserve projective models downstream.

This is a deduction *from* SR2, not a proof of SR2. In particular, no termination argument remains
to be supplied by well-ordering a proposed invariant: termination is part of the prerequisite.
Every later instruction to ``resolve'' a surface means precisely this conditional application of
SR2.

### 8.8 Examples of the local procedure

The following calculations verify particular resolutions directly. They illustrate why blowups are
the right modifications, but they do not prove SR2 for an arbitrary excellent surface singularity.

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

Thus the only unresolved chart has the same form with exponent smaller by one. Induction ends at $xy=\pi$, which is regular. Theorem 14.20 shows that every member of this family is normal and Cohen–Macaulay, so normalization cannot simplify $X_n$ and blowing up is the only available repair. Globally the exceptional locus is a chain of rational curves. The exact number and self-intersections belong to the intersection theory of the next book; here the important point is finite reduction of the exponent.

For the cone $xy=z^2$, blowing up $(x,y,z)$ gives on the $x$-chart

$$
x^2(y_1-z_1^2)=0.
$$

Removing the exceptional factor leaves $y_1=z_1^2$, a smooth chart. The other charts are similar. One blowup resolves the vertex.

A cusp requires more than branch separation. Normalizing $k[t^2,t^3]$ resolves the one-dimensional cusp immediately, but the arithmetic surface equation $y^2=x^3+\pi^m$ can remain a normal surface singularity. Blowups change both the plane-curve singularity and the vertical exponent. Proving that the alternating phenomena terminate in arbitrary excellent surface singularities is part of SR2; the preceding examples do not supply that proof.

## 9. Regular proper models

### 9.1 Existence over excellent Dedekind bases

Combining the proved closure and normalization constructions with SR2 gives the main conditional
existence theorem.

**Theorem 9.1 (regular model theorem, conditional on SR2).** Assume SR2. Let $S$ be an excellent Dedekind scheme with function field $K$, and let $C/K$ be a smooth projective geometrically connected curve. Then there exists a regular flat projective $S$-scheme $\mathcal X$ with generic fiber $C$. If a regular projective model is prescribed over a nonempty open $U\subset S$, $\mathcal X$ may be chosen to restrict to it.

**Proof.** If no model over $U$ is prescribed, embed $C$ in projective space and take its schematic closure. In the relative case, use the compatible embedding and closure constructed in Theorem 6.2. Normalize the closure to obtain a normal flat projective model $X_1$ which is unchanged over $U$. Its generic fiber, and its restriction to $U$ in the relative case, are regular. Apply SR2 to $X_1$ with the regular open consisting of its generic fiber together with $X_{1,U}$. The result is regular and projective and has unchanged generic fiber and unchanged restriction over $U$. It remains flat because it is integral and dominates the Dedekind base. $\square$

If $C$ is merely proper, it is projective because every smooth proper curve over a field possesses a divisor of positive degree and a sufficiently large multiple is very ample. Thus no separate proper-only case is needed for smooth curves.

### 9.2 Keeping a prescribed good open

Arithmetic applications usually begin with a moduli construction that is already smooth over $S[1/N]$. The theorem must not replace that meaningful open part by an unrelated isomorphic model. The relative clause ensures exact preservation.

More explicitly, let $\mathcal U\to U$ be a smooth projective curve with generic fiber $C$. Choose a relatively very ample power of an ample bundle on $\mathcal U$ and embed it in $\mathbf P^N_U$. After multiplying finitely many transition functions by elements of $K^\times$, extend the equations to $S$. The closure restricts to $\mathcal U$ because schematic closure commutes with restriction to $U$. Normalization and resolution are isomorphisms there because $\mathcal U$ is regular and normal.

The bad set $S\setminus U$ is finite when $S$ is the spectrum of a Dedekind domain and $U$ is nonempty affine after harmless shrinking. Every modification is then vertical above those finitely many primes.

### 9.3 Dominating finitely many models

**Theorem 9.2 (conditional on SR2).** Assume SR2. Any finite collection of projective $S$-models of the same smooth curve is dominated by a regular projective model, provided $S$ is excellent.

**Proof.** The fiber product of finitely many projective $S$-schemes is projective. Take in that product the schematic closure $Z$ of the diagonally embedded generic curve. It is integral, flat, and projective by Proposition 6.1, and every projection $Z\to X_i$ is proper and induces the identity on the generic fiber. Normalize $Z$ and apply SR2 to the resulting normal surface. Both operations are projective and preserve the generic fiber. The final regular projective model maps to every $X_i$ and induces the identity on $C$. $\square$

This is the correct way to compare equations, moduli compactifications, and models adapted to correspondences. One does not identify them prematurely; one moves to a common regular domination.

### 9.4 Sections and closures of points

Let $P\in C(K)$. Properness extends the map $\eta\to\mathcal X$ uniquely to a section $S\to\mathcal X$ when $S$ is normal. Existence follows from the valuative criterion at each discrete valuation ring $\mathcal O_{S,s}$, and uniqueness from separatedness; the local extensions glue.

More generally, for a closed point $P$ of $C$ with residue field $L$, let $S_L$ be the normalization of $S$ in $L$. It is finite over $S$. Properness extends the $L$-point to a section over $S_L$, and its image in $\mathcal X$ is the horizontal closure of $P$. That closure need not be regular before normalization; its normalization is $S_L$.

A section of a regular arithmetic surface is a Cartier divisor. At a point of the section, the local ring has dimension two and the section is cut out by one parameter transverse to the base direction. This fact later makes marked points compatible with blowups and semistable models.

## 10. Finite extensions and base change

### 10.1 Integral closure of the base

Let $K'/K$ be a finite field extension and let $S'$ be the normalization of $S$ in $K'$. When $S$ is excellent Dedekind, $S'\to S$ is finite and $S'$ is an excellent Dedekind scheme. More generally, normalizing in a finite reduced $K$-algebra gives the finite disjoint union belonging to its field factors. Locally at $s\in S$, the points of $S'$ correspond to extensions of the associated discrete valuation, exactly as in Book 1.

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

taking the component or components with the desired generic fiber. Since $S'$ is excellent, $X'\to X\times_SS'$ is finite. If $X$ was proper or projective, so is $X'$. Assuming SR2, resolve $X'$ if a regular model is required.

There is a canonical comparison from the normalization after base change to the base change of the original normalization whenever the latter is interpreted componentwise and is dominated by the former. It is an isomorphism under smooth base change, and also under separable field extension when geometric normality supplies normality of the base-changed space. Without such a hypothesis, it need not be.

**Proposition 10.1.** Let $X$ be a geometrically normal finite-type $K$-scheme and $K'/K$ a field extension. Then $X_{K'}$ is normal. If $X$ is a smooth curve, this applies automatically.

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

Let $R$ be a discrete valuation ring and $X/R$ a regular proper model. A vertical integral curve $E$ is an **exceptional curve of the first kind** if, after accounting for its residue field, it is a projective line with normal bundle of degree $-1$. Equivalently over an algebraically closed residue field, $E\simeq\mathbf P^1$ and $E^2=-1$. The intersection notation is used here only for this contraction criterion; systematic component pairings are developed in Book 12.

**Prerequisite 11.1 (relative Castelnuovo contraction, RC).** Let $S$ be an excellent Dedekind scheme, let $X/S$ be a regular proper arithmetic surface, and let $E$ be a vertical exceptional curve of the first kind. There is a regular proper $S$-scheme $Y$ and a proper birational morphism

$$
c:X\longrightarrow Y
$$

which is an isomorphism on $X\setminus E$, maps $E$ to a closed regular point $y\in Y$, and identifies $X$ with $\operatorname{Bl}_y(Y)$. The same assertion holds over the localization of $S$ at the image of $E$, and the local contraction glues with the identity away from that fiber.

RC is a genuine algebraic contraction theorem. It is not a consequence of excellence alone and is not proved in Books 1--10 or earlier in this volume. The normal-bundle calculation does explain why RC has the stated form: after choosing a parameter transverse to $E$, the successive exact sequences

$$
0\to\mathcal O_E(n)\to
\mathcal O_{(n+1)E}\to\mathcal O_{nE}\to0
$$

and the vanishing $H^1(\mathbf P^1,\mathcal O(n))=0$ for $n\geq-1$ identify the expected complete local target and the expected inverse blowup. These formal calculations do not by themselves produce an algebraic scheme $Y$. Passing from the formal target to $Y$, proving properness, and verifying that the blowup recovers $X$ are precisely the content of RC; excellence supplies favorable approximation and finiteness properties, not an automatic formal algebraization theorem.

**Theorem 11.1 (relative contraction, conditional on RC).** Assume RC. An exceptional curve of the first kind on a regular arithmetic surface can be contracted to a regular point. The contraction is proper and birational, is an isomorphism away from $E$, and is inverse to blowing up that point.

**Proof.** This is the assertion of RC applied to $E$. $\square$

A regular proper model is **relatively minimal** if none of its fibers contains an exceptional curve of the first kind. Every contraction lowers the number of irreducible components of the affected fiber, so repeatedly contracting must stop. This proves existence of a relatively minimal model once contractions remain in the chosen category.

### 11.2 Existence in positive genus

Contraction gives existence, but the universal property of the endpoint requires another surface theorem. Resolving a graph gives a regular common domination only after SR2; it does not show that a rational map to a minimal model is already a morphism. Nor does Theorem 11.1 prove that every proper birational morphism of regular surfaces factors into point blowups.

**Prerequisite 11.2 (birational comparison for regular arithmetic surfaces, BC2).** Let $R$ be an excellent discrete valuation ring.

1. A birational map between regular proper arithmetic surfaces which is the identity on the generic fiber admits a common regular resolution obtained by finitely many blowups at closed points.
2. A proper birational morphism between regular arithmetic surfaces which is the identity on the generic fiber factors into finitely many blowups at closed points.
3. If the common generic fiber is a smooth projective geometrically connected curve of positive genus and $Y/R$ is relatively minimal, then the rational map $X\dashrightarrow Y$ induced by the generic-fiber identification extends uniquely to a morphism $X\to Y$. In particular two relatively minimal regular proper models with fixed generic-fiber identification are uniquely isomorphic.

The third clause is the minimal-target consequence of the first two clauses together with the exceptional-curve and intersection arguments needed to compare the two blowup factorizations. Those cancellation arguments are substantial: merely choosing a "last exceptional curve" does not prove that its image on the other side is again an exceptional curve of the first kind. BC2 records the exact comparison input used below and is not proved in this volume.

**Theorem 11.2 (minimal regular model, conditional on SR2, RC, and BC2).** Assume SR2, RC, and BC2. Let $R$ be an excellent discrete valuation ring with fraction field $K$, and let $C/K$ be a smooth projective geometrically connected curve of positive genus. Then $C$ has a relatively minimal regular proper model $X_{\min}/R$. Every regular proper model of $C$ admits a unique morphism to $X_{\min}$ inducing the identity on $C$.

**Proof.** Theorem 9.1, using SR2, supplies a regular proper model. Apply RC repeatedly to its vertical exceptional curves. Each contraction remains a regular proper model and strictly lowers the number of irreducible components of the affected fiber, so the process terminates at a relatively minimal model $X_{\min}$. For any other regular proper model $Y$, BC2(3) extends the generic-fiber identification to a unique morphism $Y\to X_{\min}$. $\square$

Assuming RC and BC2 over the corresponding localizations, the same construction works over a global excellent Dedekind scheme. Only finitely many fibers of a fixed proper model are non-smooth. RC includes the algebraic gluing of each local contraction with the identity elsewhere, and the local BC2 mapping properties glue uniquely because they agree on the generic fiber. Thus the global conclusion is conditional on the same contraction and comparison inputs; it does not follow from excellence alone.

Under the same three prerequisites, a genus-one curve with a rational point has the regular geometric model associated with a minimal Weierstrass equation after resolving its surface singularities. The Weierstrass model itself is often normal but singular; the minimal regular model is its resolution, while relative minimality prohibits superfluous point blowups.

### 11.3 Uniqueness and its limits

Positive genus is essential. For $\mathbf P^1_K$, both $\mathbf P^1_R$ and models obtained through elementary transformations of ruled surfaces can be relatively minimal in natural senses without a canonical map between them fixing the generic fiber. Marking three disjoint sections restores rigidity, but the unmarked genus-zero curve has too many automorphisms and too little canonical positivity.

Minimal regular does not mean smooth, semistable, or stable. Its special fiber may have multiplicities, cusps as curves inside a regular total space, or configurations that require a field extension before becoming nodal. Nor does minimality commute with arbitrary base change. A ramified extension can create exceptional curves after resolution; recovering relative minimality then requires new applications of RC.

Uniqueness is relative to the fixed identification of the generic fiber. If generic automorphisms are allowed, they act on the minimal model by the mapping property: an automorphism of $C$ gives a second identification and extends uniquely.

### 11.4 Marked and semistable variants

For a marked curve $(C;P_1,\ldots,P_n)$, one would like to resolve not only the surface but also the boundary formed by the special fiber and the closures of the marked points. SR2 supplies the regular total space, but its statement alone does not prove embedded resolution of that boundary. Thus the further assertion that finitely many point blowups make the marked sections disjoint and transverse to a normal-crossings boundary is a separate embedded-resolution input; no termination claim for it is made here.

A regular **semistable model** has reduced special fibers whose only singularities are ordinary double points and whose components meet transversely. Étale-locally at a node it has equation

$$
xy=\pi.
$$

Resolution alone does not guarantee semistability. Semistable reduction is the additional theorem that after a suitable finite separable extension of $K$, a smooth proper curve has a semistable model. Once that extension and a normal proper candidate are supplied, this book normalizes it and, assuming SR2, resolves away from the nodal open. Removing exceptional curves of the first kind requires RC, while contracting the unstable rational components of a stable model requires the corresponding stable-contraction input. The stable model may have nodal total fibers; its total space need not be regular after ramified base change, so stable and minimal regular models serve different purposes.

## 12. Models for modular, Shimura, and semistable problems

### 12.1 The exact reusable model theorem

The preceding results can be collected in the form actually needed later, with the unresolved
surface input displayed rather than hidden.

**Theorem 12.1 (arithmetic curve model package).** Assume SR2. Let $S$ be an excellent Dedekind scheme, $U\subset S$ a nonempty open, and $C/K(S)$ a smooth projective geometrically connected curve. Suppose a smooth projective model $\mathcal C_U/U$ is given. Then:

1. there is a normal flat projective model $X/S$ extending $\mathcal C_U$;
2. there is a regular flat projective model $\mathcal X/S$ and a projective birational map $\mathcal X\to X$, identical over $U$;
3. any finite collection of projective models, rational maps, and finite generic correspondences is dominated by such a regular model on which their graph closures are defined as proper correspondences;
4. after a finite extension $K'/K(S)$, with $S'$ the normalized base, normalization of the reduced base change followed by resolution gives a regular projective $S'$-model;
5. if the supplied model over an open of $S'$ is semistable, the resolution is an isomorphism over that open;
6. if $g(C)>0$ and RC and BC2 are also assumed, contracting vertical exceptional curves produces the unique minimal regular proper model.

Every adjective has a source. Excellence of $S$ gives finite normalization and supplies the ring-theoretic hypothesis in SR2; termination and regularity of the resolution come from SR2 itself. Smoothness of $C$ makes the generic fiber normal and regular. Projectivity of $C$ starts the closure and ensures the final model is projective. Flatness follows from integrality over a Dedekind base. Properness alone is preserved throughout but does not by itself choose an embedding. Geometric connectedness prevents an unintended product of generic components. The last assertion has two additional sources: RC supplies algebraic contractions which stay in the regular proper category, and BC2 supplies the positive-genus mapping property and uniqueness.

### 12.2 Modular curves

A modular curve is first presented over an open base where the level structure has good deformation theory. Its open moduli problem is generally not proper because elliptic curves can degenerate. Adding generalized degenerations supplies a proper compactification over that good open; the cusps form finite horizontal divisors.

To obtain the exact surface used in arithmetic arguments, proceed as follows.

1. Take the smooth projective generic modular curve, including its cusps.
2. Extend the chosen good integral compactification over $U$, typically the complement of primes dividing the level.
3. Close it projectively over $S$ and normalize. Normalization retains the moduli model over $U$ and repairs branch identifications at bad primes.
4. Assuming SR2, resolve only the finitely many closed surface singularities above bad primes.
5. If the separate embedded-resolution input of Section 11.4 is also assumed, blow up so cusp closures are disjoint regular horizontal divisors meeting the fiber transversely.

Assuming SR2, the resulting object is a regular proper, indeed projective, arithmetic surface carrying the same generic modular curve and the prescribed smooth model over $U$. It is enough for extending rational functions, maps to Jacobians, degeneracy maps after graph resolution, and special-fiber calculations. Without SR2 the construction stops at the normal projective model. One must not claim that normalization alone makes it regular, or that regularity makes every bad fiber smooth.

Fine level structures may exist only after a faithfully flat extension of the base. Construct the polarized model there, retain the descent datum through normalization where geometric normality permits, and descend using Book 10. At primes where the group action has fixed points, the coarse quotient can be normal but singular. Assuming SR2, resolve the quotient surface after descent; regularity upstairs does not eliminate quotient singularities downstairs.

### 12.3 Shimura curves

Compact Shimura curves have no cusps, so no boundary divisor must be added. Their integral models nevertheless acquire bad fibers at primes connected with the discriminant or level. Over the good open, the moduli construction is smooth and proper. Conditional Theorem 12.1 extends it to a regular projective arithmetic surface without changing that open.

The distinction between a fine moduli cover and its coarse quotient is again essential. A finite group acting on a regular surface can have isolated fixed points; the quotient is finite and normal under the standard tame hypotheses but can fail to be regular. Assuming SR2, its two-dimensional quotient singularities admit a projective resolution. The elementary normalized-blowup discussion alone does not prove that the procedure terminates.

For quaternionic or PEL constructions defined after a finite extension of the reflex field, use the normalized Dedekind base. A descent datum plus a polarization descends the projective model. If ramification has introduced singularities, normalize and, assuming SR2, resolve after the descent or on a common equivariant domination. The output required for curve-level arguments is a regular proper curve model, not a smooth integral moduli space at every bad prime.

### 12.4 Semistable reduction input

Suppose a finite separable extension $K'/K$ has been chosen and a projective semistable model has been supplied over an open $V\subseteq S'$, where $S'$ is the normalization of $S$ in $K'$. Assuming SR2, the model can be extended without changing its semistable locus as follows.

Apply the conditional Theorem 12.1 with the supplied model over $V$, and use SR2 only outside $V$. At every node the completed local equation is

$$
\widehat{\mathcal O}_{\mathcal X,x}
\simeq \widehat R'[[x,y]]/(xy-\pi'),
$$

possibly after an étale extension. This ring is regular, so SR2 leaves it unchanged. Separating marked sections from the nodes and making the boundary transverse requires the embedded-resolution input isolated in Section 11.4. Producing a stable rather than a regular semistable model requires a further stable-contraction theorem for rational components meeting the remainder and markings in too few points. RC concerns exceptional curves of the first kind and does not by itself supply these contractions.

This statement deliberately starts from an algebraic model over an open subscheme. A model known only over completed local rings does not automatically algebraize or glue: compatible algebraic descent data, or a separate approximation and algebraization theorem, must first supply the model over an open of $S'$. Common domination compares algebraic models once they exist; it is not a substitute for that algebraization step.

### 12.5 Finite correspondences

Hecke and degeneracy operations begin as finite maps or correspondences on generic curves. A finite generic map $f:C\to D$ produces a rational map between proper normal models. Its graph closure

$$
\Gamma_f\subset X\times_SY
$$

is proper over both factors. Normalize the graph and, assuming SR2, resolve it to obtain a regular surface $Z$ with morphisms to both models.

The universal property of normalization factors a morphism from a normal source through a normalization once that morphism already exists. It does not remove codimension-two indeterminacy of a rational map: for example, the rational map $\mathbf A^2\dashrightarrow\mathbf P^1$ given by $[x:y]$ is undefined at the origin although the source is normal. Thus the graph construction is essential. Assuming SR2, resolving the normalized graph makes the two projections honest proper morphisms. Without SR2, normalization alone leaves this regular-domination claim unproved. Finiteness on the generic fiber still does not imply that either projection is finite, because it may contract vertical curves. Passing to the Stein factor—the spectrum of the direct image of the structure sheaf—separates a connected-fiber contraction from a finite map.

For a correspondence, keep both projections from the normalized graph. Conditional on SR2, a common regular domination makes their compositions honest. Later intersection and cohomological theories may act with the correspondence even if neither projection is a morphism between preselected minimal models. This is why domination, rather than forced functoriality of minimal models, is the robust construction.

## 13. Synthesis

### 13.1 A hypothesis ledger

The main properties and their exact uses can now be read without ambiguity.

| Property | What it supplies | What it does not supply |
|---|---|---|
| reduced | a total ring of fractions componentwise | separated branches or integral closure |
| normal | integral extension across codimension one and the normalization mapping property | regular closed points on a surface |
| regular | regular local rings on the total space | smooth or reduced fibers |
| smooth over $S$ | flatness and geometrically regular fibers | properness |
| Japanese domain | finite integral closure in finite field extensions | stability for all prime quotients |
| Nagata scheme | finite normalization for finite-type schemes | surface resolution by itself |
| excellent scheme | Nagata finiteness, good formal fibers, open regular locus, the hypotheses required by SR2 | a proof of SR2, algebraization of a formal contraction, or smooth reduction |
| proper morphism | valuative extension and universal closedness | a chosen projective embedding |
| projective morphism | properness plus an ample polarization | regularity or normality |
| flat over a Dedekind base | no vertical torsion and well-behaved fibers | reduced special fibers |

The surface inputs are independent entries in this ledger. SR2 passes from a normal model to a regular one while preserving a chosen regular open. RC contracts one specified exceptional curve inside the algebraic category. BC2 resolves and factors birational comparisons and supplies the positive-genus minimal-target criterion. In particular, excellence is a hypothesis in all three settings but proves none of these theorems by itself.

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

Starting with $C/K$, the reusable sequence, conditional at its final arrow, is

$$
\begin{array}{ccccc}
C&\subset&\mathbf P^N_K&&\\
&&\downarrow&&\\
&&X_0&\text{projective closure}&\\
&&\uparrow\ \text{finite}&&\\
&&X_1&\text{normalization}&\\
&&\uparrow\ \text{projective birational (SR2)}&&\\
&&\mathcal X&\text{regular model, conditional on SR2}.&
\end{array}
$$

The arrows point from the improved model to the previous one. If a finite extension $K'/K$ is made, repeat normalization and, assuming SR2, resolution after base change. If positive genus calls for a canonical endpoint, the conditional regular model is the starting point for contracting vertical exceptional curves; RC and BC2 are then additionally required to obtain $\mathcal X_{\min}$ with its universal property. If semistability is desired, a separate semistable-reduction input supplies the field extension and nodal model; SR2 then supplies its regular incarnation.

At every stage there is a simple diagnostic question.

1. Are unwanted vertical components present? Take schematic closure or remove base torsion.
2. Are integral functions missing or branches glued? Normalize.
3. Are closed surface points still singular? Invoke SR2; normalized blowups alone do not prove termination.
4. Has ramified base change spoiled normality or regularity? Normalize and, conditional on SR2, resolve again.
5. Are there superfluous exceptional curves? Assuming RC, contract them; assuming BC2 as well, identify the positive-genus endpoint by its mapping property.

Confusing these repairs is the source of many false shortcuts. Each answers a different defect.

### 13.3 Conclusion

An arithmetic curve has two lives. Generically it is a smooth projective one-dimensional variety; integrally it is a two-dimensional space whose vertical geometry records reduction. Projective closure connects the two lives but introduces defects. Normalization repairs the integral structure finitely because the bases in arithmetic geometry are excellent. Passing from the resulting normal surface to a regular one requires SR2; the multiplicity, tangent-cone, and conductor ideas mentioned in Chapter 8 motivate proofs of that theorem but do not establish it here.

Unconditionally, this volume supplies finite normalization and normal projective models with controlled behavior under finite extension. Conditional on SR2, it also supplies regular proper models preserving prescribed good loci and compatible regular dominations for maps and correspondences. Conditional further on RC and BC2, the positive-genus model has a relatively minimal endpoint with the stated universal property. Horizontal divisors retain generic points and markings; vertical components encode extensions of valuations and bad reduction. Regularity of the total surface and singularity of the fiber coexist without contradiction, while smoothness and semistability remain appropriately stronger relative conditions.

This separation of roles is the durable lesson. Normal, regular, smooth, excellent, Nagata, proper, and projective are not competing descriptions of one good object. They are distinct tools, and arithmetic curves become manageable only when each is invoked for exactly the work it performs.

## 14. Depth, Cohen–Macaulay rings, and Serre's criteria

Three pieces of local algebra were used on credit in the preceding chapters. Section 4.1 stated Serre's criterion and the condition $(S_2)$ with a proof strategy rather than a proof. Section 4.3 called a hypersurface Cohen–Macaulay in order to conclude that the quadratic cone is normal. Sections 8.5 and 10.4 produced the surfaces $xy=\pi^n$ without deciding which of them are normal, and Section 11.4 used the regularity of $xy=\pi$ without locating it in a general framework. This chapter proves all of it.

The material is pure local algebra and depends on none of Chapters 5 to 13; a reader may insert it immediately after Chapter 4. It is placed last because it is also the form in which later books of the collection use these results: a freeness statement over two-dimensional regular local rings, and the two criteria of Serre.

The following standard facts about noetherian rings are used as proof sources and are not reproved here.

1. **Nakayama.** If $M$ is a finite module over a local ring $(A,\mathfrak m,k)$ and $M=\mathfrak mM$, then $M=0$. Consequently a family in $M$ whose residues span $M/\mathfrak mM$ generates $M$, and a finite projective module over a local ring is free.
2. **Associated primes.** For a finite nonzero module $M$ over a noetherian ring $A$, the set $\operatorname{Ass}M$ of primes of the form $\operatorname{Ann}(x)$, $x\in M$, is finite and nonempty; the zerodivisors on $M$ are exactly $\bigcup_{\mathfrak p\in\operatorname{Ass}M}\mathfrak p$; $\operatorname{Ass}M\subseteq\operatorname{Supp}M$ and every minimal element of $\operatorname{Supp}M$ lies in $\operatorname{Ass}M$; $\operatorname{Ass}$ of a submodule is contained in $\operatorname{Ass}M$; the annihilator of any nonzero $x\in M$ is contained in some member of $\operatorname{Ass}M$; and $\operatorname{Ass}$ commutes with localization, $\operatorname{Ass}_{A_\mathfrak p}M_\mathfrak p=\{\mathfrak qA_\mathfrak p:\mathfrak q\in\operatorname{Ass}M,\ \mathfrak q\subseteq\mathfrak p\}$.
3. **Prime avoidance**, in the version that permits two of the finitely many ideals to be arbitrary and requires the rest to be prime.
4. **Krull's height theorem.** A prime minimal over an ideal generated by $r$ elements has height at most $r$. In particular $\dim A\leq\dim_k\mathfrak m/\mathfrak m^2$ for a noetherian local ring, and $\dim M/xM\geq\dim M-1$ for $x\in\mathfrak m$ and $M$ finite, where $\dim M:=\dim A/\operatorname{Ann}M$.
5. **Ext.** Long exact sequences in both variables, the identification $\operatorname{Ext}^0=\operatorname{Hom}$, compatibility with finite direct sums, and the fact that $\operatorname{Ext}^i_A(N,M)$ is killed by $\operatorname{Ann}N$, so that the map induced by multiplication by $a\in\operatorname{Ann}N$ on $M$ is zero.
6. **Resolutions.** Schanuel's lemma, and the existence of minimal free resolutions of finite modules over a noetherian local ring.
7. **Completion.** For a noetherian local ring $A$ the completion $\widehat A$ is flat over $A$, $\widehat M\simeq M\otimes_A\widehat A$ for finite $M$, $\widehat A/\mathfrak m\widehat A=A/\mathfrak m$, $\dim\widehat A=\dim A$, and $\mathfrak m/\mathfrak m^2\simeq\widehat{\mathfrak m}/\widehat{\mathfrak m}^2$.

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
and $\operatorname{depth}A$ means the depth of $A$ as a module over itself. Nothing so far says that this supremum is attained by every maximal sequence, and that is the content of Theorem 14.6. The bridge is the following criterion, which is the one substantial homological input of the chapter; it is quoted from the ambient library rather than reproved.

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

**Theorem 14.12 (Auslander–Buchsbaum).** Let $M\neq0$ be a finite module of finite projective dimension over the noetherian local ring $(A,\mathfrak m,k)$. Then
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

Two independent checks confirm the formula's shape. If $x\in\mathfrak m$ is a nonzerodivisor on $M$, then $\operatorname{depth}M/xM=\operatorname{depth}M-1$ by Theorem 14.5, while the projective dimension satisfies $\operatorname{pd}M/xM=\operatorname{pd}M+1$; the two shifts cancel, so the Auslander–Buchsbaum sum is unchanged by cutting with a regular element, exactly as the formula demands. Likewise, if $x_1,\ldots,x_c$ is an $A$-regular sequence in $\mathfrak m$, then $\operatorname{pd}_AA/(x_1,\ldots,x_c)=c$, and Theorem 14.12 recovers $\operatorname{depth}A/(x_1,\ldots,x_c)=\operatorname{depth}A-c$, which Theorem 14.5 also gives directly. These two projective-dimension identities are available from the ambient library and are recorded here because they shorten the calculations of the next section.

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

### 14.7 What the criteria return to the models

The chapter closes by recording where each result is used.

Section 4.1 stated Serre's criterion. Its proof is Theorem 14.26, together with Theorem 14.23 for the forward implication and Theorem 14.24 and Lemma 14.25 for the converse. The definition of $(S_2)$ used there is the definition adopted in Section 14.5, and Theorem 14.6 makes it independent of which maximal regular sequence is chosen to compute depth.

Section 4.2 identified normal, regular, and discrete valuation rings in dimension one. That identification is used inside Theorem 14.26 and is not reproved here; Book 1, Theorem 4.1 is the source for the valuation-theoretic half.

Section 4.3 asserted that the quadratic cone is normal because it is a Cohen–Macaulay hypersurface with a codimension-two singularity. The example after Theorem 14.20 proves it, and the same three steps prove Theorem 14.20 itself for the arithmetic family $xy=\pi^n$.

Section 4.4 gave the hypersurface regularity test $f\notin\mathfrak n^2$; that is Corollary 14.18, and it identifies $n=1$ as the only regular member of the family $xy=\pi^n$.

Sections 8.5 and 10.4 blow up the singular members of that family. Theorem 14.20 shows what the blowups are for: the surfaces $xy=\pi^n$ with $n\geq2$ are normal, so normalization is powerless against them and only a resolution helps. This is the precise sense in which normalization and resolution repair different defects.

Section 11.4 and Section 12.4 use the semistable local equation $xy=\pi$ and its completion. Theorem 14.20(3) proves regularity of the algebraic local ring at the node, and regularity is unchanged by completion, because dimension and the cotangent space are both preserved; the same holds for the Cohen–Macaulay property by Proposition 14.9. Under the standard identification of the completion of $R[x,y]_{(\pi,x,y)}$ with $\widehat R[[x,y]]$, the completed ring is the one displayed in Section 12.4, so that ring is regular and no resolution acts on it.

Finally, Theorems 14.27 and 14.30 and Corollary 14.29 are stated in the form that later books require: over a two-dimensional regular local ring, a finite module of depth two is free, and this applies to reflexive modules and to finite normal local domains. The hypothesis that cannot be dropped is depth, not torsion-freeness: a torsion-free module has depth at least one, which in dimension two is not enough, and the freeness statement genuinely uses the second regular parameter.
