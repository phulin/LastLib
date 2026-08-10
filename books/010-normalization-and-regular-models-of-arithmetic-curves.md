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
   - [A decreasing local invariant](#83-a-decreasing-local-invariant)
   - [Termination](#84-termination)
   - [Examples of the local procedure](#85-examples-of-the-local-procedure)
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

The valuation and Dedekind facts developed in Book 1 will be used freely. Relative projective constructions and their base-change behavior come from Book 8. Effective faithfully flat descent, when invoked, is the descent theory of Book 13. All local algebra specific to normalization and two-dimensional regularity is proved here.

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

**Theorem 2.3 (universal property).** Let $X$ be integral with function field $F$, let $L/F$ be finite, and let $\nu:X'\to X$ be the normalization in $L$. Suppose $Y$ is normal and integral, $f:Y\to X$ is dominant, and the induced embedding $F\hookrightarrow K(Y)$ factors through $L$. If the resulting rational map $Y\dashrightarrow X'$ sends each point into an affine chart on which it is defined—for example if $f$ is a morphism and $K(Y)=L$—then there is a unique $X$-morphism $Y\to X'$ inducing the chosen field embedding.

**Proof strategy.** A map to an affine normalization amounts contravariantly to showing that every integral element is regular on the normal source. This can be checked in its local rings.

Take $U=\operatorname{Spec}A\subset X$ and a point $y\in f^{-1}(U)$. Every $b\in A_L$ is integral over $A$, hence its image in $K(Y)$ is integral over $\mathcal O_{Y,y}$. Since this local ring is integrally closed, the image lies in $\mathcal O_{Y,y}$. Thus $b$ is regular near every point of $f^{-1}(U)$ and defines a map to $\operatorname{Spec}A_L$. These maps agree on overlaps by Proposition 2.2. Uniqueness follows because $X'\to X$ is separated and two $X$-maps from an integral scheme that agree at its generic point agree everywhere. $\square$

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

**Theorem 3.1 (finite normalization criterion).** Let $X$ be a reduced finite-type scheme over a Nagata scheme $S$. Then the normalization $X^{\mathrm{nor}}\to X$ is finite. More generally, the normalization of each irreducible component of $X$ in a finite extension of its function field is finite.

**Proof.** The assertion is affine-local on $X$. Write $X=\operatorname{Spec}B$ over $\operatorname{Spec}A\subset S$. A finite-type algebra over a Nagata ring is Nagata. After quotienting $B$ by each minimal prime, the Japanese condition says exactly that its integral closure in the relevant finite field extension is module-finite. A finite product of these closures is finite over the reduced ring $B_{\mathrm{red}}$, and $B_{\mathrm{red}}$ is finite over $B$ because $B$ is noetherian. Hence the normalization is finite. $\square$

The one nontrivial permanence assertion used here—that finite-type algebras over a Nagata ring remain Nagata—can be reduced to the domain case. Noether normalization makes a finite-type domain finite over a polynomial ring after inverting one element; the Japanese condition for the polynomial ring and a conductor argument handle that open, while noetherian induction handles its closed complement. This proof also explains why the condition must be imposed on every prime quotient.

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

There is also a useful trace argument when $L/K$ is separable and $A$ is a Dedekind domain with suitable finiteness. Choose a $K$-basis $e_i$ of $L$ and the trace-dual basis $e_i^*$. Any integral $x$ has $\operatorname{Tr}(xe_i)$ integral after denominators are cleared, so the integral closure lies in a fixed finitely generated fractional $A$-module spanned by the $e_i^*$. Since $A$ is noetherian, it is finite. The trace form degenerates for inseparable extensions, which is why the Japanese formulation is the correct general hypothesis.

### 3.4 The two-dimensional cases used here

Let $R$ be an excellent Dedekind domain and $A$ a finite-type $R$-domain whose generic fiber has dimension one. Then $A$ has dimension at most two, and it has dimension two when $\operatorname{Spec}A$ dominates $\operatorname{Spec}R$. By stability of excellence under finite type, $A$ is excellent and hence Nagata. Its normalization in any finite extension of its fraction field is finite.

This proves the central finiteness statement for arithmetic surfaces:

**Theorem 3.3.** If $X$ is a reduced finite-type scheme over an excellent Dedekind scheme $S$, then $X^{\mathrm{nor}}\to X$ is finite. If $X\to S$ is proper, respectively projective, then its normalization is proper, respectively projective, over $S$.

**Proof.** Finiteness is Theorem 3.1. A finite morphism is projective and proper. Composing it with a proper morphism gives a proper morphism. If $X\hookrightarrow\mathbf P^n_S$, a finite morphism $Y\to X$ is projective; composing projective morphisms proves projectivity of $Y/S$. $\square$

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

This two-dimensional domain is singular at the origin because its maximal ideal needs three generators. Yet it is normal. Indeed, it is a hypersurface and hence Cohen–Macaulay, so it satisfies $(S_2)$; its only singular point has codimension two, so $(R_1)$ holds. Serre's criterion applies.

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

**Theorem 6.2 (normal model theorem).** Every smooth projective geometrically connected curve over the function field of an excellent Dedekind scheme has a normal flat projective model. Given a smooth model over a nonempty open $U\subset S$, the normal model may be chosen to restrict to it.

For the relative clause, embed and close compatibly with the given projective $U$-model. Since the model over $U$ is normal, normalization changes nothing there. If the given smooth model is only proper, a relatively ample line bundle after shrinking $U$ produces the required embedding; alternatively one first chooses any generic embedding and uses the closure of its graph to compare the two models.

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

Blowup commutes with arbitrary base change because its Rees algebra does. Strict transform does not always commute so innocently: one must remove components created inside the exceptional divisor, and flatness hypotheses prevent anomalies.

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

The central low-dimensional theorem is the following.

**Theorem 8.1 (resolution of excellent surfaces).** Let $X$ be a reduced excellent noetherian scheme of dimension at most two. There is a proper birational morphism

$$
r:X'\longrightarrow X
$$

with $X'$ regular. It may be chosen as a finite composite of blowups at nowhere-dense closed centers followed at intermediate stages by normalization. If $X$ is quasi-projective over a noetherian base, $r$ may be chosen projective. If $U\subset X$ is regular, every center can be chosen in $X\setminus U$, so $r$ is an isomorphism over $U$.

For an arithmetic surface, $X$ is already normal after Chapter 6. Its singular locus is then a locally finite set of closed points. On a quasi-compact model it is finite, and the centers can be taken successively above those points.

The proof occupies the next three sections. Its scope matters. It proves resolution in dimension two using excellence; it does not assert resolution in arbitrary dimension or over arbitrary nonexcellent schemes.

### 8.2 Preparing the singular locus

We first reduce the theorem to a local statement.

**Lemma 8.2 (surface preparation).** Let $X$ be as in Theorem 8.1 and let $U$ be its regular locus. After one finite normalization, the complement of $U$ is a closed subset of codimension two. On every quasi-compact open it is finite.

**Proof.** Reduce $X$, separate its irreducible components by normalization, and use finiteness from the Nagata property. A normal noetherian surface satisfies $(R_1)$, so every codimension-zero or codimension-one point is regular. Excellence makes the regular locus open. Hence the singular locus is closed and consists of dimension-zero points. A noetherian zero-dimensional closed space has finitely many points. $\square$

It therefore suffices to resolve $\operatorname{Spec}A$ for a two-dimensional excellent normal local domain $(A,\mathfrak m)$. A modification supported at $\mathfrak m$ glues to the identity away from that point. Resolutions of the finitely many prepared points can be composed: resolving one point does not disturb the regular open, and any new singularities lie above its center.

Completion is a powerful diagnostic but must be used with care. Excellence gives that $A\to\widehat A$ is regular and faithfully flat. Thus $A$ is regular if and only if $\widehat A$ is, and the singular points on normalized blowups can be detected after completion. Coherent ideals in a completion that arise from a sufficiently high finite neighborhood can be approximated by ideals in $A$; openness of regularity then descends the achieved regularity. This is where arbitrary noetherian local rings are inadequate.

### 8.3 A decreasing local invariant

For a two-dimensional noetherian local ring $(A,\mathfrak m)$, the Hilbert–Samuel function is eventually a quadratic polynomial:

$$
\ell_A(A/\mathfrak m^{n+1})
=\frac{e(A)}2n^2+O(n).
$$

The positive integer $e(A)$ is the multiplicity. A regular local ring has $e(A)=1$; for an unmixed local ring, the converse holds. Multiplicity alone may remain constant under a blowup, so it is refined by the directrix of the tangent cone.

Let

$$
\operatorname{gr}_{\mathfrak m}A
=\bigoplus_{n\geq0}\mathfrak m^n/\mathfrak m^{n+1}.
$$

After passing to a residue-field extension when necessary, the **directrix dimension** $d(A)$ is the largest dimension of a vector subspace of the Zariski tangent space whose translations preserve the tangent cone. Define

$$
\iota(A)=\bigl(e(A),2-d(A),c(A)\bigr)
$$

with lexicographic order, where $c(A)$ is the conductor colength on a generic one-dimensional hypersurface section. More intrinsically, choose a sufficiently general parameter $h$ avoiding the finitely many tangent directions; normalize $A/(h)$, and let

$$
c(A)=\ell_A\left(\widetilde{A/(h)}/(A/(h))\right).
$$

The value is independent of a general choice for purposes of comparison; over a finite residue field one first uses a finite unramified extension to find a direction and descends the resulting center. The ordered triple lies in $\mathbf N^3$.

The hard local calculation is the following surface decrease lemma.

**Lemma 8.3 (surface decrease).** Let $A$ be an excellent normal two-dimensional local domain that is not regular. There is an $\mathfrak m$-primary ideal $I$, generated by elements of maximal order, such that every nonregular local ring $B$ on the normalized blowup of $I$ satisfies

$$
\iota(B)<\iota(A).
$$

The ideal may be chosen compatibly with a prescribed regular punctured spectrum.

**Proof.** We give the decisive local argument. Complete $A$; regularity and multiplicity are unchanged. A coefficient ring and two parameters give a finite presentation of the completion over a regular two-dimensional complete local ring. Choose elements whose initial forms cut the largest translation-invariant subspace of the tangent cone, and let $I$ be the coefficient ideal obtained by collecting, with their orders, the coefficients of the finite equations.

On a blowup chart one divides each equation by the largest exceptional power common to its terms. The initial form then transforms by dehomogenizing the tangent cone. Upper semicontinuity of Hilbert–Samuel multiplicity gives $e(B)\leq e(A)$. If strict inequality occurs, the first coordinate drops. If equality occurs, equality in the multiplicity comparison forces the center to lie in the directrix and the transformed tangent cone loses a transverse direction; the second coordinate drops unless the tangent cone is already a cylinder in that direction.

In the remaining cylindrical case, take a general hypersurface section transverse to the directrix. Its transform is the blowup of a one-dimensional reduced local ring at its maximal ideal. Write its normalization as a finite product of discrete valuation rings $V_j$. If $J$ is its conductor, then

$$
\ell(\widetilde B/B)
=\sum_j\ell_{V_j}(V_j/JV_j)-\ell_B(B/J).
$$

The transform removes at least one lowest nonintegral value from the value semigroup of every unresolved branch. Therefore the conductor colength strictly decreases. Equality would say that the one-dimensional section was already normal, hence regular, contradicting persistence of the cylindrical singularity. Finiteness of the normalization makes all lengths finite. Approximation carries the coefficient ideal back from the completion, and openness of the regular locus shows that the same inequalities hold before completion. $\square$

The lemma packages the classical quadratic-transform proof in a form suited to arithmetic surfaces. The first coordinate detects coarse multiplicity, the second prevents an endless equimultiple tangent cone, and the conductor resolves the final one-dimensional branch obstruction. All three pieces are necessary: a node and a cusp can have the same multiplicity but behave differently after blowup.

### 8.4 Termination

Start with a prepared normal surface $X_0$. At each singular point choose the ideal from Lemma 8.3, blow it up, and normalize. Let $X_{n+1}\to X_n$ be the composite modifications over all points where the maximal value of $\iota$ occurs.

**Proof of Theorem 8.1.** Each stage is finite over a projective blowup and hence projective. It is an isomorphism over the regular locus. On every nonregular point above a chosen center, the lexicographic invariant strictly decreases. There is no infinite strictly decreasing sequence in $\mathbf N^3$.

One further finiteness point is required: a stage cannot produce infinitely many points having the same positive invariant. Its singular locus is a zero-dimensional closed subset of a noetherian quasi-compact scheme, hence finite. We can therefore clear the maximal invariant at finitely many points. Induction on the well-ordered set of possible triples terminates with a regular scheme. The componentwise reduction and gluing of Section 8.2 finish the proof. $\square$

This argument also proves the relative assertion. If $U$ is regular, all coefficient ideals are supported in the closed singular locus, so each modification is the identity over $U$. For an arithmetic surface, take $U$ to contain the generic fiber and every chosen good fiber.

### 8.5 Examples of the local procedure

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

Thus the only unresolved chart has the same form with exponent smaller by one. Induction ends at $xy=\pi$, which is regular. Globally the exceptional locus is a chain of rational curves. The exact number and self-intersections belong to the intersection theory of the next book; here the important point is finite reduction of the exponent.

For the cone $xy=z^2$, blowing up $(x,y,z)$ gives on the $x$-chart

$$
x^2(y_1-z_1^2)=0.
$$

Removing the exceptional factor leaves $y_1=z_1^2$, a smooth chart. The other charts are similar. One blowup resolves the vertex.

A cusp requires more than branch separation. Normalizing $k[t^2,t^3]$ resolves the one-dimensional cusp immediately, but the arithmetic surface equation $y^2=x^3+\pi^m$ can remain a normal surface singularity. Blowups change both the plane-curve singularity and the vertical exponent. The decreasing triple, rather than multiplicity alone, guarantees that alternating phenomena cannot continue indefinitely.

## 9. Regular proper models

### 9.1 Existence over excellent Dedekind bases

Combining closure, normalization, and resolution gives the main existence theorem.

**Theorem 9.1 (regular model theorem).** Let $S$ be an excellent Dedekind scheme with function field $K$, and let $C/K$ be a smooth projective geometrically connected curve. Then there exists a regular flat projective $S$-scheme $\mathcal X$ with generic fiber $C$. If a regular model is prescribed over a nonempty open $U\subset S$, $\mathcal X$ may be chosen to restrict to it.

**Proof.** Embed $C$ in projective space, take its schematic closure $X_0$, and normalize to obtain the normal flat projective model $X_1$. Its generic fiber is smooth and hence regular. Resolve $X_1$ with centers contained in the finite union of singular closed points outside $U$. The result is regular and projective and has unchanged generic fiber. It remains flat because it is integral and dominates the Dedekind base. $\square$

If $C$ is merely proper, it is projective because every smooth proper curve over a field possesses a divisor of positive degree and a sufficiently large multiple is very ample. Thus no separate proper-only case is needed for smooth curves.

### 9.2 Keeping a prescribed good open

Arithmetic applications usually begin with a moduli construction that is already smooth over $S[1/N]$. The theorem must not replace that meaningful open part by an unrelated isomorphic model. The relative clause ensures exact preservation.

More explicitly, let $\mathcal U\to U$ be a smooth projective curve with generic fiber $C$. Choose a relatively very ample power of an ample bundle on $\mathcal U$ and embed it in $\mathbf P^N_U$. After multiplying finitely many transition functions by elements of $K^\times$, extend the equations to $S$. The closure restricts to $\mathcal U$ because schematic closure commutes with restriction to $U$. Normalization and resolution are isomorphisms there because $\mathcal U$ is regular and normal.

The bad set $S\setminus U$ is finite when $S$ is the spectrum of a Dedekind domain and $U$ is nonempty affine after harmless shrinking. Every modification is then vertical above those finitely many primes.

### 9.3 Dominating finitely many models

**Theorem 9.2.** Any finite collection of proper $S$-models of the same smooth curve is dominated by a regular projective model, provided $S$ is excellent.

**Proof.** Repeatedly take the closure of the diagonal generic curve in the fiber product, as in Proposition 6.3, and call the result $Z$. The curve $C$ is a dense quasi-projective open of $Z$. The relative form of Chow's lemma gives a projective modification $Z'\to Z$: to see the needed case, cover $Z$ by finitely many affine opens, choose generators for their boundary ideals, and use the closure of the graph of the resulting maps to projective spaces; the graph projections glue after taking the product of those projective spaces. Over the dense open where all chosen ideals are invertible this is an isomorphism. Normalize $Z'$ and resolve the resulting normal surface. The final regular projective scheme maps to $Z$, hence to every original model, and is the identity on the generic fiber. $\square$

This is the correct way to compare equations, moduli compactifications, and models adapted to correspondences. One does not identify them prematurely; one moves to a common regular domination.

### 9.4 Sections and closures of points

Let $P\in C(K)$. Properness extends the map $\eta\to\mathcal X$ uniquely to a section $S\to\mathcal X$ when $S$ is normal. Existence follows from the valuative criterion at each discrete valuation ring $\mathcal O_{S,s}$, and uniqueness from separatedness; the local extensions glue.

More generally, for a closed point $P$ of $C$ with residue field $L$, let $S_L$ be the normalization of $S$ in $L$. It is finite over $S$. Properness extends the $L$-point to a section over $S_L$, and its image in $\mathcal X$ is the horizontal closure of $P$. That closure need not be regular before normalization; its normalization is $S_L$.

A section of a regular arithmetic surface is a Cartier divisor. At a point of the section, the local ring has dimension two and the section is cut out by one parameter transverse to the base direction. This fact later makes marked points compatible with blowups and semistable models.

## 10. Finite extensions and base change

### 10.1 Integral closure of the base

Let $K'/K$ be finite and let $S'$ be the normalization of $S$ in $K'$. When $S$ is excellent Dedekind, $S'\to S$ is finite, and $S'$ is a finite disjoint union of excellent Dedekind schemes after separating field factors. Locally at $s\in S$, its points correspond to extensions of the associated discrete valuation, exactly as in Book 1.

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
X'=operatorname{Nor}\bigl((X\times_SS')_{\mathrm{red}}\bigr),
$$

taking the component or components with the desired generic fiber. Since $S'$ is excellent, $X'\to X\times_SS'$ is finite. If $X$ was proper or projective, so is $X'$. Resolve $X'$ if a regular model is required.

There is a canonical comparison from the normalization after base change to the base change of the original normalization whenever the latter is interpreted componentwise and is dominated by the former. It is an isomorphism under smooth base change, and also under separable field extension when geometric normality supplies normality of the base-changed space. Without such a hypothesis, it need not be.

**Proposition 10.1.** Let $X$ be a geometrically normal finite-type $K$-scheme and $K'/K$ a field extension. Then $X_{K'}$ is normal. If $X$ is a smooth curve, this applies automatically.

Thus the generic curve itself causes no trouble in our main setting. The trouble lies in the integral special fibers, where ramification and residue-field extension can create singularities.

### 10.4 Ramification and vertical multiplicities

Suppose $R\subset R'$ is an extension of discrete valuation rings with ramification index $e$, so

$$
\pi=u(\pi')^e
$$

for a unit $u\in R'$. If a vertical component $\Gamma$ of $X_s$ has multiplicity $m$, its pullback before reduction carries generic multiplicity divisible according to $em$. Normalization can then split the component and divide multiplicities by ramification indices of the induced divisorial valuations.

The local semistable equation illustrates both creation and repair:

$$
xy=\pi
\quad\leadsto\quad
xy=u(\pi')^e.
$$

For $e>1$ the base-changed total space is generally singular at the crossing, though the original total space was regular. Normalization alone may not resolve it; a chain of blowups does. After resolution, the reduced special fiber can again have normal crossings. Therefore “regular model commutes with ramified base change” is false.

Unramified étale base change behaves better. It preserves regularity and the equation $xy=\pi$ remains semistable. This contrast is one reason inertia and ramification enter the geometry of reduction.

### 10.5 Descent of models

Let $S'\to S$ be finite faithfully flat. A model over $S'$ with an isomorphism between its two pullbacks to $S'\times_SS'$ satisfying the cocycle condition descends effectively when it is quasi-projective; a compatible relatively ample line bundle provides the projective descent. These are the results of Book 13 together with the projective theory of Book 8.

Properties that are faithfully flat local on the base—flatness, finite presentation, properness, smoothness—descend. Regularity of the total space is not itself simply a property of the morphism, but it descends under faithfully flat maps with geometrically regular fibers, in particular under étale covers. Normality descends under faithfully flat morphisms satisfying the corresponding geometric reducedness conditions. Under a ramified cover, a regular model upstairs may descend to a singular quotient.

Hence descent is a two-part test: descend the object and its polarization, then verify the geometric property whose fibers or quotient singularities may have changed. A descent datum does not magically preserve regularity.

## 11. Minimal regular models

### 11.1 Exceptional curves and contraction

Existence leaves many choices: blowing up any closed point of a regular model gives another regular model. Minimality removes precisely this artificial freedom.

Let $R$ be a discrete valuation ring and $X/R$ a regular proper model. A vertical integral curve $E$ is an **exceptional curve of the first kind** if, after accounting for its residue field, it is a projective line with normal bundle of degree $-1$. Equivalently over an algebraically closed residue field, $E\simeq\mathbf P^1$ and $E^2=-1$. The intersection notation is used here only for this contraction criterion; systematic component pairings are developed in Book 11.

**Theorem 11.1 (relative contraction).** An exceptional curve of the first kind on a regular arithmetic surface can be contracted to a regular point. The contraction is proper and birational, is an isomorphism away from $E$, and is inverse to blowing up that point.

**Proof strategy.** The normal bundle condition reproduces the exceptional divisor of a point blowup. Choose a parameter transverse to $E$. Successive exact sequences

$$
0\to\mathcal O_E(n)\to
\mathcal O_{(n+1)E}\to\mathcal O_{nE}\to0
$$

and the vanishing $H^1(\mathbf P^1,\mathcal O(n))=0$ for $n\geq-1$ show that functions on infinitesimal neighborhoods descend with no obstruction. Their inverse limit is a two-dimensional regular complete local ring. Excellence algebraizes the formal contraction. The resulting point has maximal ideal whose blowup pulls back to $\mathcal O_X(-E)$, so blowing it up recovers $X$. $\square$

A regular proper model is **relatively minimal** if none of its fibers contains an exceptional curve of the first kind. Every contraction lowers the number of irreducible components of the affected fiber, so repeatedly contracting must stop. This proves existence of a relatively minimal model once contractions remain in the chosen category.

### 11.2 Existence in positive genus

**Theorem 11.2 (minimal regular model).** Let $R$ be an excellent discrete valuation ring with fraction field $K$, and let $C/K$ be a smooth projective geometrically connected curve of positive genus. Then $C$ has a relatively minimal regular proper model $X_{\min}/R$. Every regular proper model of $C$ admits a unique morphism to $X_{\min}$ inducing the identity on $C$.

**Proof.** Begin with Theorem 9.1 and contract vertical exceptional curves until none remains. Termination follows from the strictly decreasing number of fiber components. To compare a second regular model $Y$, resolve the indeterminacy of the birational map $Y\dashrightarrow X_{\min}$ by point blowups, obtaining $Z$ with morphisms to both.

Factor a birational morphism between regular surfaces into point blowups by choosing the first exceptional component and applying Theorem 11.1 inductively. In the two factorizations from $Z$, take the last exceptional curve created. If it were contracted on only one side, its image on the other would be a vertical rational curve with normal degree $-1$, unless it survived to the generic fiber. The latter is impossible because every modification is the identity generically; the former contradicts relative minimality of $X_{\min}$. Cancelling common last blowups inductively shows that the birational map from $Y$ has no indeterminacy and gives a morphism $Y\to X_{\min}$. This argument works in genus one as well as in larger genus; positive genus rules out the ruled-surface elementary transformations responsible for genus-zero nonuniqueness. Separatedness gives uniqueness. $\square$

Over a global excellent Dedekind scheme, perform these contractions fiber by fiber. Only finitely many fibers of a fixed proper model are non-smooth, and each contraction is supported over one closed point. The local contractions glue with the identity elsewhere, producing a global minimal regular model for a positive-genus curve.

For genus one with a rational point, this is the regular geometric model associated with a minimal Weierstrass equation after resolving its surface singularities. The Weierstrass model itself is often normal but singular; the minimal regular model is its resolution, while its relatively minimality prohibits superfluous point blowups.

### 11.3 Uniqueness and its limits

Positive genus is essential. For $\mathbf P^1_K$, both $\mathbf P^1_R$ and models obtained through elementary transformations of ruled surfaces can be relatively minimal in natural senses without a canonical map between them fixing the generic fiber. Marking three disjoint sections restores rigidity, but the unmarked genus-zero curve has too many automorphisms and too little canonical positivity.

Minimal regular does not mean smooth, semistable, or stable. Its special fiber may have multiplicities, cusps as curves inside a regular total space, or configurations that require a field extension before becoming nodal. Nor does minimality commute with arbitrary base change. A ramified extension can create exceptional curves after resolution; they must then be contracted again.

Uniqueness is relative to the fixed identification of the generic fiber. If generic automorphisms are allowed, they act on the minimal model by the mapping property: an automorphism of $C$ gives a second identification and extends uniquely.

### 11.4 Marked and semistable variants

For a marked curve $(C;P_1,\ldots,P_n)$, resolve not only the surface but also the boundary formed by the special fiber and the closures of the marked points. Blow up until the marked sections lie in the smooth locus, are disjoint, and meet the reduced special fiber transversely. Each defect is supported at a closed point, and the same surface invariant with the number of boundary tangencies as a final coordinate proves termination.

A regular **semistable model** has reduced special fibers whose only singularities are ordinary double points and whose components meet transversely. Étale-locally at a node it has equation

$$
xy=\pi.
$$

Resolution alone does not guarantee semistability. Semistable reduction is the additional theorem that after a suitable finite separable extension of $K$, a smooth proper curve has a semistable model. Once that extension and a normal proper candidate are supplied, the constructions of this book normalize, resolve, and remove exceptional components while preserving the nodal open. The stable model may have nodal total fibers and contracts unstable rational components; its total space need not be regular after ramified base change, so stable and minimal regular models serve different purposes.

## 12. Models for modular, Shimura, and semistable problems

### 12.1 The exact reusable model theorem

The preceding results can be collected in the form actually needed later.

**Theorem 12.1 (arithmetic curve model package).** Let $S$ be an excellent Dedekind scheme, $U\subset S$ a nonempty open, and $C/K(S)$ a smooth projective geometrically connected curve. Suppose a smooth projective model $\mathcal C_U/U$ is given. Then:

1. there is a normal flat projective model $X/S$ extending $\mathcal C_U$;
2. there is a regular flat projective model $\mathcal X/S$ and a projective birational map $\mathcal X\to X$, identical over $U$;
3. any finite collection of proper models, rational maps, and finite generic correspondences is dominated by such a regular model on which their graph closures are defined as proper correspondences;
4. after a finite extension $K'/K(S)$, with $S'$ the normalized base, normalization of the reduced base change followed by resolution gives a regular projective $S'$-model;
5. if the supplied model over an open of $S'$ is semistable, all centers can be kept outside that open;
6. if $g(C)>0$, contracting vertical exceptional curves produces the unique minimal regular proper model.

Every adjective has a source. Excellence of $S$ gives finite normalization and terminating surface resolution. Smoothness of $C$ makes the generic fiber normal and regular. Projectivity of $C$ starts the closure and ensures the final model is projective. Flatness follows from integrality over a Dedekind base. Properness alone is preserved throughout but does not by itself choose an embedding. Geometric connectedness prevents an unintended product of generic components.

### 12.2 Modular curves

A modular curve is first presented over an open base where the level structure has good deformation theory. Its open moduli problem is generally not proper because elliptic curves can degenerate. Adding generalized degenerations supplies a proper compactification over that good open; the cusps form finite horizontal divisors.

To obtain the exact surface used in arithmetic arguments, proceed as follows.

1. Take the smooth projective generic modular curve, including its cusps.
2. Extend the chosen good integral compactification over $U$, typically the complement of primes dividing the level.
3. Close it projectively over $S$ and normalize. Normalization retains the moduli model over $U$ and repairs branch identifications at bad primes.
4. Resolve only the finitely many closed surface singularities above bad primes.
5. Blow up, if necessary, so cusp closures are disjoint regular horizontal divisors meeting the fiber transversely.

The resulting object is a regular proper, indeed projective, arithmetic surface carrying the same generic modular curve and the prescribed smooth model over $U$. It is enough for extending rational functions, maps to Jacobians, degeneracy maps after graph resolution, and special-fiber calculations. One must not claim that normalization alone makes it regular, or that regularity makes every bad fiber smooth.

Fine level structures may exist only after a faithfully flat extension of the base. Construct the polarized model there, retain the descent datum through normalization where geometric normality permits, and descend using Book 13. At primes where the group action has fixed points, the coarse quotient can be normal but singular. Resolve the quotient surface after descent; regularity upstairs does not eliminate quotient singularities downstairs.

### 12.3 Shimura curves

Compact Shimura curves have no cusps, so no boundary divisor must be added. Their integral models nevertheless acquire bad fibers at primes connected with the discriminant or level. Over the good open, the moduli construction is smooth and proper. Theorem 12.1 extends it to a regular projective arithmetic surface without changing that open.

The distinction between a fine moduli cover and its coarse quotient is again essential. A finite group acting on a regular surface can have isolated fixed points; the quotient is finite and normal under the standard tame hypotheses but can fail to be regular. Its singularities are two-dimensional quotient singularities and are resolved by the normalized blowup procedure.

For quaternionic or PEL constructions defined after a finite extension of the reflex field, use the normalized Dedekind base. A descent datum plus a polarization descends the projective model. If ramification has introduced singularities, normalize and resolve after the descent or on a common equivariant domination. The output required for curve-level arguments is a regular proper curve model, not a smooth integral moduli space at every bad prime.

### 12.4 Semistable reduction input

Suppose a finite separable extension $K'/K$ has been chosen so that $C_{K'}$ has semistable reduction. Let $S'$ be the normalization of $S$ in $K'$. A semistable model on an open or locally at each completed discrete valuation ring can be globalized as follows.

Take a projective normal $S'$-model dominating the local candidates by closing their generic graphs. Resolve away from the semistable loci. At every node the completed local equation is

$$
\widehat{\mathcal O}_{\mathcal X,x}
\simeq \widehat R'[[x,y]]/(xy-\pi'),
$$

possibly after an étale extension. This ring is regular, so resolution does not alter it. Marked sections can be separated from the nodes by point blowups. Contract rational components that meet the remainder and markings in too few points if a stable rather than a regular semistable model is desired.

The local-to-global assertion uses properness and uniqueness of the generic identifications. Two models over overlapping localizations have a common regular domination; minimality then identifies their relatively minimal regular forms in positive genus. Thus local models patch without choosing equations uniformly at all primes.

### 12.5 Finite correspondences

Hecke and degeneracy operations begin as finite maps or correspondences on generic curves. A finite generic map $f:C\to D$ produces a rational map between proper normal models. Its graph closure

$$
\Gamma_f\subset X\times_SY
$$

is proper over both factors. Normalize the graph and resolve it to obtain a regular surface $Z$ with morphisms to both models.

If the target model is normal, the universal property of normalization often extends $f$ directly once the map is defined in codimension one. Properness supplies extension at valuation rings; normality then extends across codimension two when the associated rational functions have no poles. But finiteness on the generic fiber does not automatically imply that the extended map is finite: vertical curves may be contracted. Passing to the Stein factor—the spectrum of the direct image of the structure sheaf—separates a connected-fiber contraction from a finite map.

For a correspondence, keep both projections from the normalized graph. A common regular domination makes their compositions honest. Later intersection and cohomological theories may act with the correspondence even if neither projection is a morphism between preselected minimal models. This is why domination, rather than forced functoriality of minimal models, is the robust construction.

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
| excellent scheme | Nagata finiteness, good formal fibers, open regular locus, surface resolution | smooth reduction |
| proper morphism | valuative extension and universal closedness | a chosen projective embedding |
| projective morphism | properness plus an ample polarization | regularity or normality |
| flat over a Dedekind base | no vertical torsion and well-behaved fibers | reduced special fibers |

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

Starting with $C/K$, the reusable sequence is

$$
\begin{array}{ccccc}
C&\subset&\mathbf P^N_K&&\\
&&\downarrow&&\\
&&X_0&\text{projective closure}&\\
&&\uparrow\ \text{finite}&&\\
&&X_1&\text{normalization}&\\
&&\uparrow\ \text{projective birational}&&\\
&&\mathcal X&\text{regular model}.&
\end{array}
$$

The arrows point from the improved model to the previous one. If a finite extension $K'/K$ is made, repeat normalization and resolution after base change. If positive genus calls for a canonical endpoint, contract all vertical exceptional curves to obtain $\mathcal X_{\min}$. If semistability is desired, a separate semistable-reduction input supplies the field extension and nodal model; the present machinery then gives its regular and minimal incarnations.

At every stage there is a simple diagnostic question.

1. Are unwanted vertical components present? Take schematic closure or remove base torsion.
2. Are integral functions missing or branches glued? Normalize.
3. Are closed surface points still singular? Resolve by normalized blowups.
4. Has ramified base change spoiled normality or regularity? Normalize and resolve again.
5. Are there superfluous exceptional curves? Contract them when positive-genus minimality warrants it.

Confusing these repairs is the source of many false shortcuts. Each answers a different defect.

### 13.3 Conclusion

An arithmetic curve has two lives. Generically it is a smooth projective one-dimensional variety; integrally it is a two-dimensional space whose vertical geometry records reduction. Projective closure connects the two lives but introduces defects. Normalization repairs the integral structure finitely because the bases in arithmetic geometry are excellent. Surface resolution replaces isolated normal singularities by controlled vertical curves and terminates because multiplicity, tangent data, and conductor complexity cannot decrease forever.

The result is the precise geometric platform used later: regular proper models preserving prescribed good loci, compatible common dominations for maps and correspondences, controlled behavior under finite extension, and minimal regular models in positive genus. Horizontal divisors retain generic points and markings; vertical components encode extensions of valuations and bad reduction. Regularity of the total surface and singularity of the fiber coexist without contradiction, while smoothness and semistability remain appropriately stronger relative conditions.

This separation of roles is the durable lesson. Normal, regular, smooth, excellent, Nagata, proper, and projective are not competing descriptions of one good object. They are distinct tools, and arithmetic curves become manageable only when each is invoked for exactly the work it performs.
