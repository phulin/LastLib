# Finite Locally Free Schemes and Algebras

## Contents

1. [Why finite geometry is linear algebra](#1-why-finite-geometry-is-linear-algebra)
   - [The governing idea](#11-the-governing-idea)
   - [Rings and affine schemes run in opposite directions](#12-rings-and-affine-schemes-run-in-opposite-directions)
   - [Three meanings of “finite” that must not be confused](#13-three-meanings-of-finite-that-must-not-be-confused)
   - [The affine-local principle](#14-the-affine-local-principle)
2. [Finite modules and finite algebras](#2-finite-modules-and-finite-algebras)
   - [Generators, relations, and localization](#21-generators-relations-and-localization)
   - [The determinant trick and integrality](#22-the-determinant-trick-and-integrality)
   - [Transitivity and base change](#23-transitivity-and-base-change)
   - [Quotients, monogenic algebras, and counterexamples](#24-quotients-monogenic-algebras-and-counterexamples)
3. [Projective and locally free modules](#3-projective-and-locally-free-modules)
   - [Why projectivity is the global form of freeness](#31-why-projectivity-is-the-global-form-of-freeness)
   - [Dual bases](#32-dual-bases)
   - [Rank and its local constancy](#33-rank-and-its-local-constancy)
   - [Fitting ideals and rank detection](#34-fitting-ideals-and-rank-detection)
   - [Exact sequences and projective summands](#35-exact-sequences-and-projective-summands)
4. [Duals, tensors, and determinants](#4-duals-tensors-and-determinants)
   - [Why finite projective modules have a complete linear algebra](#41-why-finite-projective-modules-have-a-complete-linear-algebra)
   - [Base change for tensors, Hom, and duals](#42-base-change-for-tensors-hom-and-duals)
   - [Symmetric and exterior powers](#43-symmetric-and-exterior-powers)
   - [Trace and characteristic polynomial of an endomorphism](#44-trace-and-characteristic-polynomial-of-an-endomorphism)
5. [Finite morphisms](#5-finite-morphisms)
   - [From finite algebras to finite maps](#51-from-finite-algebras-to-finite-maps)
   - [Integral morphisms and the affine-local characterization](#52-integral-morphisms-and-the-affine-local-characterization)
   - [Closedness and prime ideals](#53-closedness-and-prime-ideals)
   - [Fibers of finite morphisms](#54-fibers-of-finite-morphisms)
6. [Finite locally free morphisms and degree](#6-finite-locally-free-morphisms-and-degree)
   - [Definition and algebraic equivalence](#61-definition-and-algebraic-equivalence)
   - [Rank and degree](#62-rank-and-degree)
   - [Worked families](#63-worked-families)
   - [Positive rank and faithful flatness](#64-positive-rank-and-faithful-flatness)
7. [Stability under the standard operations](#7-stability-under-the-standard-operations)
   - [Arbitrary base change](#71-arbitrary-base-change)
   - [Composition and multiplication of degree](#72-composition-and-multiplication-of-degree)
   - [Fiber products and products of rank](#73-fiber-products-and-products-of-rank)
   - [Disjoint unions and addition of degree](#74-disjoint-unions-and-addition-of-degree)
   - [Closed subschemes and quotients](#75-closed-subschemes-and-quotients)
8. [Finite flatness and finite presentation](#8-finite-flatness-and-finite-presentation)
   - [The exact equivalences](#81-the-exact-equivalences)
   - [Why finite flat alone is not enough](#82-why-finite-flat-alone-is-not-enough)
   - [Scheme-theoretic formulations](#83-scheme-theoretic-formulations)
   - [Noetherian and coherent shortcuts](#84-noetherian-and-coherent-shortcuts)
   - [Fiber criteria and their limitations](#85-fiber-criteria-and-their-limitations)
9. [Local rings and discrete valuation rings](#9-local-rings-and-discrete-valuation-rings)
   - [Finite projective modules over local rings](#91-finite-projective-modules-over-local-rings)
   - [Flat quotients and idempotents in local rings](#92-flat-quotients-and-idempotents-in-local-rings)
   - [Finite modules over a DVR](#93-finite-modules-over-a-dvr)
   - [Finite algebras over a DVR](#94-finite-algebras-over-a-dvr)
   - [Lattices in generic fibers](#95-lattices-in-generic-fibers)
10. [Trace, norm, and characteristic polynomials of algebras](#10-trace-norm-and-characteristic-polynomials-of-algebras)
    - [Multiplication as the regular representation](#101-multiplication-as-the-regular-representation)
    - [Base-change compatibility](#102-base-change-compatibility)
    - [Examples](#103-examples)
    - [Units and the norm](#104-units-and-the-norm)
    - [Transitivity in towers](#105-transitivity-in-towers)
    - [The trace pairing and the discriminant](#106-the-trace-pairing-and-the-discriminant)
    - [Perfect trace pairing and finite étale examples](#107-perfect-trace-pairing-and-finite-étale-examples)
    - [The norm as a polynomial law](#108-the-norm-as-a-polynomial-law)
11. [Descent of finite projective structure](#11-descent-of-finite-projective-structure)
    - [Why descent is needed](#111-why-descent-is-needed)
    - [Faithfully flat detection of exactness](#112-faithfully-flat-detection-of-exactness)
    - [Descent of finite generation](#113-descent-of-finite-generation)
    - [Descent of finite presentation](#114-descent-of-finite-presentation)
    - [Descent of flatness](#115-descent-of-flatness)
    - [Descent theorem for finite projective modules](#116-descent-theorem-for-finite-projective-modules)
    - [Descent for algebras and schemes](#117-descent-for-algebras-and-schemes)
    - [Zariski and finite families of localizations](#118-zariski-and-finite-families-of-localizations)
12. [Finite algebras as sheaves](#12-finite-algebras-as-sheaves)
    - [Relative spectra without a general scheme-theory detour](#121-relative-spectra-without-a-general-scheme-theory-detour)
    - [Pullback and pushforward under base change](#122-pullback-and-pushforward-under-base-change)
    - [Internal Hom for finite locally free modules](#123-internal-hom-for-finite-locally-free-modules)
    - [The relative dual of a finite locally free morphism](#124-the-relative-dual-of-a-finite-locally-free-morphism)
    - [Projection formula in the finite setting](#125-projection-formula-in-the-finite-setting)
13. [Idempotents, components, and sections](#13-idempotents-components-and-sections)
    - [Idempotents are finite decompositions](#131-idempotents-are-finite-decompositions)
    - [Idempotents and base change](#132-idempotents-and-base-change)
    - [Sections in algebraic form](#133-sections-in-algebraic-form)
    - [A section of a finite map is closed](#134-a-section-of-a-finite-map-is-closed)
    - [Retractions and rank accounting](#135-retractions-and-rank-accounting)
14. [Anatomy of fibers](#14-anatomy-of-fibers)
    - [Artinian algebras over a field](#141-artinian-algebras-over-a-field)
    - [Geometric points versus length](#142-geometric-points-versus-length)
    - [Variation in a flat family](#143-variation-in-a-flat-family)
    - [Reduced and étale boundary cases](#144-reduced-and-étale-boundary-cases)
    - [Support and the image of a finite locally free scheme](#145-support-and-the-image-of-a-finite-locally-free-scheme)
15. [Worked structural patterns](#15-worked-structural-patterns)
    - [A monic equation over an arbitrary base](#151-a-monic-equation-over-an-arbitrary-base)
    - [Splitting a base and varying rank](#152-splitting-a-base-and-varying-rank)
    - [Two integral models with the same generic rank](#153-two-integral-models-with-the-same-generic-rank)
    - [A closed subscheme that ceases to be flat](#154-a-closed-subscheme-that-ceases-to-be-flat)
    - [Recognizing a family after a faithfully flat cover](#155-recognizing-a-family-after-a-faithfully-flat-cover)
16. [Constant rank repairs finite flatness](#16-constant-rank-repairs-finite-flatness)
   - [Why rank is the missing hypothesis](#161-why-rank-is-the-missing-hypothesis)
   - [The constant-rank theorem](#162-the-constant-rank-theorem)
   - [Locally constant rank and nonconnected bases](#163-locally-constant-rank-and-nonconnected-bases)
   - [Criteria over local rings and valuation bases](#164-criteria-over-local-rings-and-valuation-bases)
17. [The unramified and étale boundary](#17-the-unramified-and-étale-boundary)
   - [Differentials measure infinitesimal motion](#171-differentials-measure-infinitesimal-motion)
   - [Finite unramified and finite étale algebras](#172-finite-unramified-and-finite-étale-algebras)
   - [Geometric fibers and separability](#173-geometric-fibers-and-separability)
   - [The trace-pairing criterion](#174-the-trace-pairing-criterion)
   - [Ramified boundary examples](#175-ramified-boundary-examples)
18. [Quotients, kernels, and exactness](#18-quotients-kernels-and-exactness)
   - [Why finite locally free objects do not form an abelian category](#181-why-finite-locally-free-objects-do-not-form-an-abelian-category)
   - [Split exact sequences and rank bookkeeping](#182-split-exact-sequences-and-rank-bookkeeping)
   - [Quotients of finite locally free algebras](#183-quotients-of-finite-locally-free-algebras)
   - [Images, equalizers, and base change](#184-images-equalizers-and-base-change)
   - [Fiberwise criteria for maps](#185-fiberwise-criteria-for-maps)
19. [Schematic closure and saturation](#19-schematic-closure-and-saturation)
   - [Closing a generic subscheme](#191-closing-a-generic-subscheme)
   - [Saturation in modules and ideals](#192-saturation-in-modules-and-ideals)
   - [The DVR closure theorem](#193-the-dvr-closure-theorem)
   - [Dedekind bases and the limits of the theorem](#194-dedekind-bases-and-the-limits-of-the-theorem)
   - [Closure of algebraic structure](#195-closure-of-algebraic-structure)
20. [Weil restriction along a finite locally free map](#20-weil-restriction-along-a-finite-locally-free-map)
   - [The functor and its variance](#201-the-functor-and-its-variance)
   - [Restriction of affine space](#202-restriction-of-affine-space)
   - [Equations and affine representability](#203-equations-and-affine-representability)
   - [Base change, products, and open subfunctors](#204-base-change-products-and-open-subfunctors)
   - [Quasi-projective gluing and its boundary](#205-quasi-projective-gluing-and-its-boundary)
   - [Units, sections, and a norm example](#206-units-sections-and-a-norm-example)
21. [Descent interfaces for group schemes and moduli](#21-descent-interfaces-for-group-schemes-and-moduli)
   - [Finite locally free algebras form a descent category](#211-finite-locally-free-algebras-form-a-descent-category)
   - [Descending morphisms, subobjects, and identities](#212-descending-morphisms-subobjects-and-identities)
   - [Exactness after a faithfully flat cover](#213-exactness-after-a-faithfully-flat-cover)
   - [Norms, determinants, and duals under descent](#214-norms-determinants-and-duals-under-descent)
   - [A moduli-oriented descent protocol](#215-a-moduli-oriented-descent-protocol)
22. [The stability theorem](#22-the-stability-theorem)
   - [Statement with exact hypotheses](#221-statement-with-exact-hypotheses)
   - [Proof by reduction to finite projective algebra](#222-proof-by-reduction-to-finite-projective-algebra)
   - [Operations that require an extra hypothesis](#223-operations-that-require-an-extra-hypothesis)
   - [Consequences for finite-flat families](#224-consequences-for-finite-flat-families)
23. [The finite locally free dictionary](#23-the-finite-locally-free-dictionary)
    - [The four affine translations](#231-the-four-affine-translations)
    - [What rank $n$ guarantees](#232-what-rank-n-guarantees)
    - [The arithmetic of degrees](#233-the-arithmetic-of-degrees)
    - [The base-change checklist](#234-the-base-change-checklist)
    - [The locality and descent checklist](#235-the-locality-and-descent-checklist)
    - [Local and DVR diagnostics](#236-local-and-dvr-diagnostics)
    - [Trace and norm in reusable form](#237-trace-and-norm-in-reusable-form)
    - [Common invalid shortcuts](#238-common-invalid-shortcuts)
    - [Final synthesis](#239-final-synthesis)

## 1. Why finite geometry is linear algebra

### 1.1 The governing idea

A scheme finite over an affine base is itself affine, and its geometry is encoded by an algebra that is finite as a module. This simple observation is unusually powerful. It turns fibers into tensor products, degrees into ranks, disjoint unions into products of rings, and many geometric constructions into familiar operations on finite modules. The especially well-behaved objects are the **finite locally free** morphisms. Their coordinate algebras are finite projective modules, so they possess duals, determinants, characteristic polynomials, traces, and norms, all compatible with passage to a new base.

The phrase “finite flat of rank $n$” occurs constantly in arithmetic geometry. Each word matters. Finiteness controls algebraic size and forces affine fibers. Flatness prevents relations from appearing suddenly after specialization. Rank records the length of every fiber. When the base is not connected, rank need not be a single integer: it is a locally constant function. One purpose of this book is to make these qualifications automatic rather than burdensome.

We develop only the scheme theory demanded by this circle of ideas. All rings are commutative with identity, all ring homomorphisms preserve identity, and all schemes are ordinary schemes. If $A$ is a ring and $M$ an $A$-module, write

$$
M_{\mathfrak p}=A_{\mathfrak p}\otimes_A M,
\qquad
M_f=A_f\otimes_A M.
$$

For a field-valued point $s\colon \operatorname{Spec} k\to S$, the fiber of $X\to S$ at $s$ is $X_s=X\times_S\operatorname{Spec}k$. At a prime $\mathfrak p\in\operatorname{Spec}A$, its residue field is

$$
\kappa(\mathfrak p)=\operatorname{Frac}(A/\mathfrak p)
=A_{\mathfrak p}/\mathfrak pA_{\mathfrak p}.
$$

### 1.2 Rings and affine schemes run in opposite directions

A homomorphism $A\to B$ gives a morphism

$$
\operatorname{Spec}B\longrightarrow\operatorname{Spec}A.
$$

This reversal is the source of nearly every variance issue below. Extension of scalars $A\to A'$ changes $B$ to $B\otimes_AA'$, and geometrically changes $\operatorname{Spec}B$ to its base change over $\operatorname{Spec}A'$. A composite $A\to B\to C$ corresponds to the composite

$$
\operatorname{Spec}C\longrightarrow\operatorname{Spec}B
\longrightarrow\operatorname{Spec}A.
$$

Products behave differently on the two sides. The fiber product of affine schemes corresponds to a tensor product:

$$
\operatorname{Spec}B\times_{\operatorname{Spec}A}\operatorname{Spec}C
\simeq \operatorname{Spec}(B\otimes_AC).
$$

By contrast, a finite disjoint union corresponds to a direct product:

$$
\operatorname{Spec}(B_1\times\cdots\times B_r)
\simeq \coprod_{i=1}^r\operatorname{Spec}B_i.
$$

These formulas are not merely notation. They explain why base change preserves finite locally free morphisms and why ranks add under disjoint union but multiply under fiber product and composition.

### 1.3 Three meanings of “finite” that must not be confused

Let $A\to B$ be a ring map.

* It is **finite** if $B$ is a finitely generated $A$-module.
* It is **of finite type** if $B$ is generated by finitely many elements as an $A$-algebra.
* It is **of finite presentation** if $B\cong A[x_1,\ldots,x_r]/(g_1,\ldots,g_m)$ for finite $r,m$.

A finite map is of finite type: module generators together with $1$ certainly generate the algebra. More strongly, every finite ring map is integral, because multiplication by any $b\in B$ acts on a finite module and the determinant trick supplies a monic equation for $b$. But a finite module need not be finitely presented, and therefore a finite ring map need not be an algebra of finite presentation over an arbitrary nonnoetherian base.

The simplest warning is a quotient. For any ideal $I\subseteq A$, the map $A\to A/I$ is finite, generated by $1$ as an $A$-module. It is finitely presented as an $A$-module, or as an $A$-algebra, exactly when $I$ is finitely generated. Thus finite does not imply finitely presented without an additional hypothesis. Over a noetherian ring it does, because submodules of finite modules are finite.

Flatness introduces a different distinction. The quotient $A/I$ is flat over $A$ only in special circumstances; over a local ring, a nonzero proper quotient is never flat. Thus finite says that the object has bounded algebraic size, while flat says that scalar extension preserves exact relations. Neither word contains the other.

### 1.4 The affine-local principle

Many properties in this book are checked over affine open subsets of the target. Suppose $f\colon X\to S$ is a morphism and $S=\bigcup U_i$ is an affine open cover. To say that $f$ is finite means that each $f^{-1}(U_i)$ is affine and its coordinate ring is finite over the coordinate ring of $U_i$. It is enough that this hold for one affine open cover, because localization preserves finite generation and affineness glues over refinements.

Similarly, finite local freeness of rank $n$ means that, after an open cover of $S$, the inverse image is affine with coordinate algebra free of rank $n$. The word “locally” refers to the base. There is no demand that $X$ itself be covered by opens on which an unrelated module is free.

The main work will therefore be algebraic. We shall repeatedly prove a statement for $A\to B$ and then obtain its scheme form by applying it on affine opens and checking compatibility on overlaps.

## 2. Finite modules and finite algebras

### 2.1 Generators, relations, and localization

A finite module has finitely many global generators, but their relations can be large. Concretely, $M$ is finite if there is a surjection $A^r\twoheadrightarrow M$ for some $r$. It is finitely presented if the kernel is also finite, equivalently if there is an exact sequence

$$
A^s\longrightarrow A^r\longrightarrow M\longrightarrow0
$$

with $r,s$ finite. Finite presentation is the hypothesis that makes maps out of $M$ commute with arbitrary filtered colimits and that lets local information be spread to an actual neighborhood.

Localization preserves both properties. Indeed, localizing a finite presentation gives

$$
A_f^s\longrightarrow A_f^r\longrightarrow M_f\longrightarrow0.
$$

The converse for finiteness is quasi-compact. If $D(f_1),\ldots,D(f_r)$ cover $\operatorname{Spec}A$ and every $M_{f_i}$ is finite over $A_{f_i}$, then $M$ is finite. Choose local generators and clear their denominators to obtain a finite submodule $N\subseteq M$ with $N_{f_i}=M_{f_i}$. Then $(M/N)_{f_i}=0$. For any $x\in M/N$, some power of each $f_i$ kills $x$; because the $f_i$ generate the unit ideal up to suitable powers, $x=0$. Hence $M=N$.

The same argument, applied also to the relation module of a fixed finite generating set, proves:

**Local finite-presentation criterion.** An $A$-module $M$ is finitely presented if and only if some finite principal-open cover $D(f_i)$ has every $M_{f_i}$ finitely presented.

The finiteness of the cover cannot simply be discarded. Quasi-compactness of $\operatorname{Spec}A$ is what extracts finitely many neighborhoods from an arbitrary open cover.

### 2.2 The determinant trick and integrality

The bridge from finite modules to integral elements is the determinant trick.

**Theorem 2.1 (determinant trick).** Let $M$ be a finite $A$-module and let $u\colon M\to M$ be $A$-linear. Then $u$ satisfies a monic polynomial with coefficients in $A$.

**Proof.** Choose generators $m_1,\ldots,m_r$. Write

$$
u(m_i)=\sum_j a_{ij}m_j.
$$

Regard $M$ as an $A[T]$-module by letting $T$ act as $u$. Then the matrix $TI-(a_{ij})$ annihilates the column $(m_i)$. Multiplication by its adjugate shows that

$$
p(T)(m_i)=0,
\qquad
p(T)=\det(TI-(a_{ij})).
$$

Since the $m_i$ generate $M$, this gives $p(u)=0$ as an endomorphism. The polynomial $p$ is monic of degree $r$. $\square$

For a finite ring map $A\to B$, apply the argument to the module $B$ and multiplication by $b\in B$. The identity $p(m_b)=0$, evaluated at $1\in B$, gives $p(b)=0$. We conclude that every $b$ is integral over $A$, even when $A\to B$ has a kernel.

Conversely, if $B=A[b_1,\ldots,b_r]$ and every $b_i$ is integral over $A$, then $B$ is finite over $A$. If $b_i$ satisfies a monic equation of degree $d_i$, every monomial can be reduced to an $A$-linear combination of

$$
b_1^{e_1}\cdots b_r^{e_r},
\qquad 0\le e_i<d_i.
$$

Therefore:

**Theorem 2.2.** A ring map is finite if and only if it is of finite type and integral.

This equivalence explains the geometric rigidity of finite morphisms. Integrality controls prime ideals; finite type makes that control uniform.

### 2.3 Transitivity and base change

If $A\to B$ and $B\to C$ are finite, then $A\to C$ is finite. Choose $A$-module generators $b_i$ of $B$ and $B$-module generators $c_j$ of $C$. The finitely many products $b_ic_j$ generate $C$ over $A$.

If $A\to B$ is finite and $A\to A'$ is arbitrary, then

$$
B'=B\otimes_AA'
$$

is finite over $A'$: the tensors of a finite set of $A$-module generators of $B$ generate $B'$. No flatness assumption on $A'$ is needed. The same is true for finite presentation.

Products also preserve finiteness. If $B_1,\ldots,B_r$ are finite $A$-algebras, then $\prod_iB_i$ is finite as an $A$-module. The restriction to finite products matters: an infinite product of nonzero $A$-modules is almost never finitely generated.

### 2.4 Quotients, monogenic algebras, and counterexamples

Several model algebras will recur.

1. A quotient $A/I$ is finite for every ideal $I$. It is flat precisely when the inclusion $I\hookrightarrow A$ remains injective after every scalar extension. If $I=Ae$ for an idempotent $e$, then $A/I\cong A(1-e)$ is projective and hence flat. Conversely, a finitely presented flat quotient arises this way.

2. If $f(T)\in A[T]$ is monic of degree $n$, then

$$
B=A[T]/(f)
$$

is free with basis $1,T,\ldots,T^{n-1}$. This is the basic finite locally free algebra of rank $n$.

3. The dual numbers $A[\epsilon]/(\epsilon^2)$ are free of rank $2$. They are finite flat over every base even though every fiber is nonreduced. Thus finite flatness is not a reducedness condition.

4. The algebra $A[T]/(aT,T^2)$ is finite, generated by $1,T$, but when $a$ is neither zero nor a unit its fibers can jump: over points where $a$ is invertible, $T=0$ and the fiber has dimension $1$; where $a=0$, it has dimension $2$. This is the behavior flatness rules out.

5. A field extension $L/K$ is a finite $K$-algebra exactly when $[L:K]<\infty$. Every finite-dimensional vector space is free, so every finite field extension defines a finite locally free morphism of degree $[L:K]$, with no separability required.

## 3. Projective and locally free modules

### 3.1 Why projectivity is the global form of freeness

A module that is free on small pieces need not admit a single global basis. Projectivity captures precisely the possibility of making compatible local choices without insisting on global triviality. An $A$-module $P$ is **projective** if every map $P\to N$ lifts across every surjection $M\twoheadrightarrow N$. Equivalently, the functor $\operatorname{Hom}_A(P,-)$ is exact. Equivalently, $P$ is a direct summand of a free module.

For finite modules the relevant theorem is:

**Theorem 3.1.** For an $A$-module $P$, the following are equivalent.

1. $P$ is finite projective.
2. $P$ is finitely presented and flat.
3. For every prime $\mathfrak p$, $P_{\mathfrak p}$ is a finite free $A_{\mathfrak p}$-module.
4. There is a finite principal-open cover $\operatorname{Spec}A=\bigcup D(f_i)$ such that every $P_{f_i}$ is finite free.

The equivalence deserves a proof because it is the algebraic engine of the subject.

**Proof.** If $P$ is a direct summand of $A^r$, it is finitely presented and flat. Suppose conversely that $P$ is finitely presented and flat. Over a local ring $(R,\mathfrak m)$, choose elements of $P$ lifting a basis of $P/\mathfrak mP$. They give a surjection $R^r\to P$ by Nakayama's lemma. Since $P$ is flat, the kernel $K$ satisfies $K/\mathfrak mK=0$; because $K$ is finite, Nakayama gives $K=0$. Thus a finite flat module over a local ring is free.

Localizing at $\mathfrak p$ proves (2)$\Rightarrow$(3). If $P_{\mathfrak p}$ has a basis, finite presentation lets both spanning and linear independence spread to some $D(f)$ containing $\mathfrak p$: lift the basis elements, express a finite set of generators in terms of them after clearing denominators, and clear denominators in the finitely many relations. Quasi-compactness then gives (4).

If (4) holds, $P$ is finitely presented by the local criterion and flat because flatness can be checked after localization: an injection $N'\hookrightarrow N$ remains injective after tensoring with every $P_{f_i}$, hence after tensoring with $P$ since vanishing is detected on the cover. Thus (4)$\Rightarrow$(2), completing the circle. $\square$

The proof also explains why “finite flat” alone is delicate: the local freeness argument used finite generation of a kernel, supplied by finite presentation. Over a general ring, a finitely generated flat module need not be finitely presented or projective. Chapter 8 isolates the exact additional hypotheses.

### 3.2 Dual bases

For $P$ an $A$-module, put $P^\vee=\operatorname{Hom}_A(P,A)$. A finite family $p_i\in P$ and $\lambda_i\in P^\vee$ is a **dual basis** if

$$
p=\sum_i\lambda_i(p)p_i
\quad\text{for every }p\in P.
$$

The terminology does not mean that $P$ is free: the $p_i$ can be redundant.

**Dual-basis criterion.** An $A$-module $P$ is finite projective if and only if it admits a finite dual basis.

**Proof.** Given a dual basis, define $i\colon P\to A^r$ by $i(p)=(\lambda_i(p))$ and $q\colon A^r\to P$ by $q(e_i)=p_i$. The displayed identity says $q i=\operatorname{id}_P$, so $P$ is a direct summand of $A^r$. Conversely, if $P$ is a direct summand of $A^r$, restrict the coordinate functionals and project the standard basis vectors to obtain a dual basis. $\square$

The tensor

$$
\operatorname{coev}_P(1)=\sum_i p_i\otimes\lambda_i\in P\otimes_AP^\vee
$$

is independent of the chosen dual basis. Under the natural map

$$
P\otimes_AP^\vee\longrightarrow\operatorname{End}_A(P),
\qquad p\otimes\lambda\longmapsto(x\mapsto\lambda(x)p),
$$

it corresponds to the identity. This basis-free element is the source of traces and of the good base-change behavior of duals.

### 3.3 Rank and its local constancy

If $P$ is finite projective and $\mathfrak p\in\operatorname{Spec}A$, then $P_{\mathfrak p}$ is free of a uniquely determined finite rank. Define

$$
\operatorname{rk}_P(\mathfrak p)=
\dim_{\kappa(\mathfrak p)}(P\otimes_A\kappa(\mathfrak p)).
$$

Local triviality shows that this function is locally constant. Consequently each set

$$
S_n(P)=\{\mathfrak p:\operatorname{rk}_P(\mathfrak p)=n\}
$$

is both open and closed, and only finitely many are nonempty. If $\operatorname{Spec}A$ is connected, the rank is constant. Without connectedness there need not be one rank: for $A=A_1\times A_2$ and $P=A_1^r\times A_2^s$, the ranks on the two components are $r$ and $s$.

The clopen decomposition is algebraic. A decomposition $\operatorname{Spec}A=U\amalg V$ into open-and-closed subsets corresponds to an idempotent $e\in A$ with $U=D(e)$ and $V=D(1-e)$. Thus a finite projective module has a canonical finite product decomposition of the base on which its rank is separately constant.

For general finite modules, fiber dimension need not be locally constant. It is upper semicontinuous under finite-presentation hypotheses: the locus where at least $r$ generators are needed is closed, described by Fitting ideals. The jumping module in §2.4 illustrates the distinction.

### 3.4 Fitting ideals and rank detection

Let $M$ be finitely presented, with a presentation $A^m\xrightarrow{R}A^n\to M\to0$. The $i$-th Fitting ideal $\operatorname{Fitt}_i(M)$ is generated by the $(n-i)\times(n-i)$ minors of $R$, with the conventions that minors of size at most zero generate $A$ and impossible minors generate $0$. Row and column operations and stabilization show that this ideal is independent of the presentation.

Here is the mechanism behind independence. Replacing bases multiplies $R$ on the left or right by an invertible matrix, and the Cauchy–Binet formula shows that the ideal of minors of each size is unchanged. Adding a redundant generator and relation replaces $R$ by a block matrix with an identity block; expanding minors along that block shifts the indexing exactly as in the definition. Any two finite presentations become equivalent after such stabilizations and basis changes, because both present the same cokernel. Thus the ideals depend only on $M$.

At a prime $\mathfrak p$, the fiber $M\otimes\kappa(\mathfrak p)$ has dimension at most $i$ exactly when $\operatorname{Fitt}_i(M)\not\subseteq\mathfrak p$. Hence Fitting ideals locate rank strata. If $P$ is finite projective of constant rank $n$, then

$$
\operatorname{Fitt}_{n-1}(P)=0,
\qquad
\operatorname{Fitt}_n(P)=A.
$$

Conversely, a finitely presented flat module satisfying these identities is locally free of rank $n$. Fitting ideals are particularly useful when a family is given by generators and relations rather than by an evident basis.

To verify the fiber criterion, reduce the presentation modulo $\mathfrak p$. Over the field $\kappa(\mathfrak p)$, the cokernel dimension is $n-\operatorname{rank}(R(\mathfrak p))$. It is at most $i$ exactly when some $(n-i)$-minor is nonzero, exactly when the corresponding Fitting ideal is not contained in $\mathfrak p$. This also proves that the locus where fiber dimension is at most $i$ is open. For projective $P$, local freeness makes the complementary inequalities open as well, producing the clopen rank strata of §3.3.

### 3.5 Exact sequences and projective summands

If

$$
0\longrightarrow P'\longrightarrow P\longrightarrow P''\longrightarrow0
$$

is exact and $P''$ is projective, the sequence splits. Thus $P\cong P'\oplus P''$. If two of the three modules are finite projective in the combinations forced by such a splitting, so is the third, and ranks add pointwise:

$$
\operatorname{rk}P=\operatorname{rk}P'+\operatorname{rk}P''.
$$

Kernels require care. A map between finite projective modules need not have projective kernel: multiplication by a zero divisor $a$ on $A$ has kernel $\operatorname{Ann}(a)$, which can be badly behaved. If the cokernel is projective, however, splitting makes the kernel a finite projective summand.

Tensor products and finite direct sums of finite projective modules are finite projective. Their ranks satisfy

$$
\operatorname{rk}(P\oplus Q)=\operatorname{rk}P+\operatorname{rk}Q,
\qquad
\operatorname{rk}(P\otimes Q)=\operatorname{rk}P\,\operatorname{rk}Q.
$$

These local identities will become the addition and multiplication laws for degrees of finite locally free schemes.

## 4. Duals, tensors, and determinants

### 4.1 Why finite projective modules have a complete linear algebra

Vector-space constructions often fail for arbitrary modules. The canonical map from a module to its double dual may not be injective or surjective; tensoring may destroy exact sequences; and a linear map need not possess a useful determinant. Finite projective modules are exactly large enough to retain the basis-free part of finite-dimensional linear algebra while still allowing nontrivial variation over the base.

If $P$ is finite projective, then $P^\vee$ is finite projective and the evaluation map

$$
P\longrightarrow P^{\vee\vee}
$$

is an isomorphism. Both assertions may be checked on a cover where $P$ is free. More intrinsically, a dual basis $(p_i,\lambda_i)$ gives a dual basis $(\lambda_i,\operatorname{ev}_{p_i})$ of $P^\vee$, and the identity $p=\sum_i\lambda_i(p)p_i$ proves reflexivity.

For any $A$-module $M$, the natural map

$$
P^\vee\otimes_AM\longrightarrow\operatorname{Hom}_A(P,M),
\qquad
\lambda\otimes m\longmapsto(p\mapsto\lambda(p)m)
$$

is an isomorphism. Its inverse sends $u\colon P\to M$ to $\sum_i\lambda_i\otimes u(p_i)$. Consequently

$$
\operatorname{Hom}_A(P,Q)\cong P^\vee\otimes_AQ
$$

is finite projective whenever $P$ and $Q$ are.

### 4.2 Base change for tensors, Hom, and duals

Let $A\to A'$ be any ring map. Tensor products associate without a flatness hypothesis:

$$
(M\otimes_AN)\otimes_AA'
\cong
(M\otimes_AA')\otimes_{A'}(N\otimes_AA').
$$

Hom is subtler. There is always a natural map

$$
\operatorname{Hom}_A(M,N)\otimes_AA'
\longrightarrow
\operatorname{Hom}_{A'}(M\otimes_AA',N\otimes_AA'),
$$

but it need not be an isomorphism. It is an isomorphism when $M$ is finitely presented and $A'$ is flat, and, more importantly here, whenever $M$ is finite projective with no condition on $A'$. In the latter case both sides identify with

$$
(M^\vee\otimes_AN)\otimes_AA'.
$$

Taking $N=A$ yields the fundamental dual-base-change isomorphism

$$
M^\vee\otimes_AA'
\xrightarrow{\sim}
(M\otimes_AA')^\vee
$$

for finite projective $M$. Arbitrary base change is essential: fibers use the generally nonflat map $A\to\kappa(\mathfrak p)$.

### 4.3 Symmetric and exterior powers

The tensor power $P^{\otimes r}$ carries an action of the symmetric group. Its symmetric quotient is $\operatorname{Sym}^r_A(P)$, and its alternating quotient is $\bigwedge^r_AP$. These constructions commute with arbitrary base change because they are defined by cokernels of maps between tensor powers. If $P$ is finite projective of rank $n$, then both are finite projective, and locally

$$
\operatorname{rk}\operatorname{Sym}^r(P)=\binom{n+r-1}{r},
\qquad
\operatorname{rk}\bigwedge^rP=\binom nr.
$$

Indeed, on a basis $e_1,\ldots,e_n$, the symmetric monomials

$$
e_1^{a_1}\cdots e_n^{a_n},
\qquad a_1+\cdots+a_n=r,
$$

form a basis of the symmetric power, while the wedges

$$
e_{i_1}\wedge\cdots\wedge e_{i_r},
\qquad i_1<\cdots<i_r,
$$

form a basis of the exterior power. Counting these bases gives the binomial ranks. Because their transition maps are induced functorially from those of $P$, the local modules glue. In particular no assumption that $r!$ be invertible is required; symmetric power is being defined as the symmetric quotient, not as the image of an averaging idempotent.

The top exterior power

$$
\det(P)=\bigwedge^nP
$$

is an invertible module when $P$ has constant rank $n$. If rank varies, define the determinant separately on the clopen rank strata; equivalently one obtains an invertible module by the usual alternating convention on that decomposition.

An endomorphism $u$ of a constant-rank-$n$ projective module induces multiplication by a unique scalar on the invertible module $\det(P)$. This scalar is $\det(u)$. Local bases show the familiar identities

$$
\det(uv)=\det(u)\det(v),
\qquad
\det(u\otimes_AA')=\det(u)\otimes1.
$$

If $0\to P'\to P\to P''\to0$ is exact with all three modules finite projective of constant ranks $r,r+s,s$, then the sequence splits locally and wedge products give a canonical isomorphism

$$
\det(P)\cong\det(P')\otimes_A\det(P'').
$$

Although a local splitting was used to see the formula, the isomorphism itself is independent of that splitting: it sends

$$
(p'_1\wedge\cdots\wedge p'_r)\otimes
(\bar p_1\wedge\cdots\wedge\bar p_s)
$$

to $p'_1\wedge\cdots\wedge p'_r\wedge p_1\wedge\cdots\wedge p_s$, and changing lifts $p_i$ alters the wedge only by terms containing too many vectors from $P'$. This exact-sequence formula is the determinant analogue of additivity of rank.

### 4.4 Trace and characteristic polynomial of an endomorphism

The trace of $u\in\operatorname{End}_A(P)$ is defined through

$$
\operatorname{End}_A(P)\cong P^\vee\otimes_AP
\xrightarrow{\operatorname{ev}}A.
$$

For a dual basis it is

$$
\operatorname{tr}(u)=\sum_i\lambda_i(u(p_i)).
$$

This definition gives $\operatorname{tr}(uv)=\operatorname{tr}(vu)$, additivity in $u$, and compatibility with arbitrary base change. Localizing reduces each identity to matrices.

For constant rank $n$, define the characteristic polynomial

$$
\chi_u(T)=\det(T\operatorname{id}_P-u)\in A[T].
$$

It is monic of degree $n$, its $T^{n-1}$ coefficient is $-\operatorname{tr}(u)$, and its constant term is $(-1)^n\det(u)$. The Cayley–Hamilton identity $\chi_u(u)=0$ holds because it holds after localization wherever $P$ is free, and an endomorphism vanishing at every prime is zero. All coefficients commute with arbitrary base change.

If rank is only locally constant, there is no single global degree unless the rank strata are separated. On each clopen piece $S_n(P)$ one has a degree-$n$ polynomial. It is often cleaner to state characteristic-polynomial results after decomposing the base by rank.

## 5. Finite morphisms

### 5.1 From finite algebras to finite maps

A morphism $f\colon X\to S$ is **finite** if every affine open $U=\operatorname{Spec}A\subseteq S$ has affine inverse image

$$
f^{-1}(U)=\operatorname{Spec}B
$$

with $B$ finite over $A$. It is enough to require this for one affine open cover. Indeed, if $V=D(g)\subseteq U$, then

$$
f^{-1}(V)=D(g)\subseteq\operatorname{Spec}B
=\operatorname{Spec}B_g,
$$

and $B_g$ is finite over $A_g$. General affine opens are covered by finitely many principal opens, and affineness descends through this finite cover.

Thus finite morphisms over $\operatorname{Spec}A$ are precisely spectra of finite $A$-algebras. In particular every finite morphism is affine. The converse “affine and of finite type” is false: the affine line $\mathbb A^1_A=\operatorname{Spec}A[T]$ is not finite over a nonzero base.

Finite morphisms are stable under arbitrary base change and composition by §2.3. They are also separated: for $B$ an $A$-algebra, the diagonal corresponds to the multiplication map

$$
B\otimes_AB\longrightarrow B,
$$

which is surjective, so the diagonal is a closed immersion.

### 5.2 Integral morphisms and the affine-local characterization

A morphism is **integral** if it is affine and, on affine opens of the target, its coordinate-ring map is integral. By Theorem 2.2,

$$
\text{finite}=\text{integral}+\text{finite type}.
$$

This equality is meant as an equivalence of properties, not as a decomposition of a morphism. It has two useful consequences. First, an integral morphism of finite type is automatically finite. Second, many topological properties can be proved at the integral level.

The affine-local definition also admits a useful strengthening.

**Theorem 5.1.** Let $f\colon X\to S$ be a morphism. If $S$ has an affine open cover $U_i$ such that every $f^{-1}(U_i)$ is affine and finite over $U_i$, then $f$ is finite. Conversely, the inverse image of every affine open under a finite morphism is affine with finite coordinate algebra.

**Proof strategy.** The forward direction is built into locality. For the converse, cover an affine $V\subseteq S$ by principal opens lying inside the $U_i$. Their inverse images are affine and arise from localizations of finite algebras. The relative spectrum of the finite quasi-coherent algebra $f_*\mathcal O_X|_V$ glues these pieces and is affine over $V$; it agrees with $X|_V$ on a cover and therefore globally. Its global algebra is finite by the local criterion of §2.1. $\square$

This theorem is why one can freely switch affine charts without rebuilding finiteness.

### 5.3 Closedness and prime ideals

Integral ring extensions satisfy lying over: if $A\to B$ is integral and $\mathfrak p$ contains the kernel of $A\to B$, then some prime $\mathfrak q$ of $B$ contracts to $\mathfrak p$. One proof localizes at $\mathfrak p$, passes to $B/\mathfrak pB$, and chooses a maximal ideal; integrality forces its contraction to be the maximal ideal of $A_{\mathfrak p}$.

To make the last step explicit, use this elementary fact: if $D\subseteq L$ is an integral extension of domains and $L$ is a field, then $D$ is a field. For $0\ne d\in D$, the element $d^{-1}\in L$ is integral over $D$, so it satisfies

$$
(d^{-1})^r+a_{r-1}(d^{-1})^{r-1}+\cdots+a_0=0.
$$

Multiplying by $d^{r-1}$ expresses $d^{-1}$ as an element of $D$. Applied to the quotient by a maximal ideal upstairs, this shows that the contraction is maximal downstairs. Localization then gives lying over for $\mathfrak p$.

This proves that an integral morphism $f\colon X\to S$ has image

$$
f(X)=V(\ker(\mathcal O_S\to f_*\mathcal O_X))
$$

on each affine chart. More generally, if $Z=V(J)\subseteq\operatorname{Spec}B$, then $B/J$ is integral over $A/(J\cap A)$, so

$$
f(Z)=V(J\cap A).
$$

Hence integral, and in particular finite, morphisms are closed. A finite morphism is therefore universally closed, because every base change remains finite. Combined with separatedness and finite type, this says finite morphisms are proper, although no general theory of proper morphisms is needed here.

Closedness has a useful specialization consequence. If $x\in X$ lies over $s\in S$ and $s'$ is a specialization of $s$, then the closure of $\{x\}$ maps onto the closure of $\{s\}$ under an integral morphism, so some specialization of $x$ lies above $s'$. Finite geometry cannot lose every point while moving toward a more special base point. Flatness strengthens this topological statement to conservation of scheme-theoretic length.

### 5.4 Fibers of finite morphisms

For $X=\operatorname{Spec}B\to\operatorname{Spec}A=S$ and $\mathfrak p\in S$,

$$
X_{\mathfrak p}
=\operatorname{Spec}(B\otimes_A\kappa(\mathfrak p)).
$$

The fiber algebra is finite-dimensional over $\kappa(\mathfrak p)$, so the fiber has finitely many points and is an Artinian scheme. Its scheme-theoretic length is

$$
\dim_{\kappa(\mathfrak p)}(B\otimes_A\kappa(\mathfrak p)).
$$

Finiteness of the point set follows algebraically: a finite-dimensional algebra over a field is Artinian, its nilradical is nilpotent, and its reduced quotient is a finite product of finite field extensions. The maximal ideals of the factors are the points. This description also shows why residue-field degrees enter the length.

This length counts nilpotent thickness and residue-field degrees, not merely geometric points. For example, $K[T]/(T^n)$ has one point but length $n$. If $L/K$ is a finite field extension, $\operatorname{Spec}L$ has one point and length $[L:K]$.

A **geometric fiber** uses an algebraic closure $\overline{\kappa(\mathfrak p)}$:

$$
X_{\overline{\mathfrak p}}
=\operatorname{Spec}(B\otimes_A\overline{\kappa(\mathfrak p)}).
$$

Its length is unchanged by field extension. Its number of points can increase: a separable field extension splits into a product after algebraic closure, while a purely inseparable extension remains nonreduced at one geometric point. Length is the invariant robust enough for finite flat families.

## 6. Finite locally free morphisms and degree

### 6.1 Definition and algebraic equivalence

A morphism $f\colon X\to S$ is **finite locally free** if it is finite and the $\mathcal O_S$-module $f_*\mathcal O_X$ is locally free of finite rank. Equivalently, every point of $S$ has an affine neighborhood $U=\operatorname{Spec}A$ for which

$$
f^{-1}(U)=\operatorname{Spec}B
$$

and $B$ is a finite free $A$-module. Equivalently again, on every affine open, $B$ is a finite projective $A$-module.

The last equivalence follows from Theorem 3.1. It is the central dictionary entry:

$$
\boxed{
\begin{array}{c}
\text{finite locally free schemes over }\operatorname{Spec}A
\\
\text{correspond contravariantly to finite }A\text{-algebras}\\
\text{whose underlying }A\text{-modules are finite projective.}
\end{array}}
$$

No condition is imposed on multiplication beyond being an $A$-algebra structure. In particular nilpotents are allowed.

### 6.2 Rank and degree

For a finite locally free morphism $f\colon X\to S$, define

$$
\deg_f(s)=\operatorname{rk}_{(f_*\mathcal O_X)_s}
=\dim_{\kappa(s)}H^0(X_s,\mathcal O_{X_s}).
$$

This is a locally constant function $S\to\mathbb Z_{\ge0}$. We say that $f$ has **constant rank**, or **degree**, $n$ if this function is everywhere $n$. On a connected nonempty base every finite locally free morphism has a unique degree. On a disconnected base, writing “degree $n$” is an additional assertion, not a harmless abbreviation.

Rank zero is possible: the empty scheme $\varnothing\to S$ corresponds to the zero algebra, whose identity agrees with zero. Some conventions exclude the zero ring; when they do, rank zero must be treated separately. For positive-rank algebras, the structure map $A\to B$ is injective whenever $B$ is faithfully flat, as it will be below.

At every $s\in S$, the fiber $X_s$ has length $\deg_f(s)$. Thus flatness converts rank into a conservation law: points may collide, split, or acquire nilpotents, but total fiber length cannot jump.

### 6.3 Worked families

Let $f(T)$ be monic of degree $n$. Then

$$
X=\operatorname{Spec}A[T]/(f)\longrightarrow\operatorname{Spec}A
$$

is finite locally free of degree $n$. Specialization may radically change its geometry. For $A=k[t]$ and $f(T)=T^2-t$, fibers over $t=a\ne0$ have two geometric points if $\operatorname{char}k\ne2$, while the fiber over $0$ is $k[T]/(T^2)$, one doubled point. Degree remains $2$.

The disjoint union of $n$ copies of $S$ corresponds to $A^n$ and has degree $n$. This is the **constant finite scheme** with $n$ elements. It is very different from $\operatorname{Spec}A[T]/(T^n)$, although both have degree $n$.

For a finite extension $L/K$, $\operatorname{Spec}L\to\operatorname{Spec}K$ has degree $[L:K]$. If the extension is separable, the geometric fiber is a disjoint union of $[L:K]$ reduced points. If it is inseparable, the geometric fiber has fewer points and nilpotent structure.

### 6.4 Positive rank and faithful flatness

A finite locally free module of positive rank at every point is faithfully flat. Flatness is clear. To prove faithfulness, suppose $M$ is an $A$-module with $M\otimes_AP=0$. Localizing at any prime gives

$$
M_{\mathfrak p}\otimes_{A_{\mathfrak p}}A_{\mathfrak p}^{r(\mathfrak p)}=0.
$$

Since $r(\mathfrak p)>0$, this forces $M_{\mathfrak p}=0$ for all $\mathfrak p$, hence $M=0$.

Therefore a positive-rank finite locally free morphism is faithfully flat and surjective. The positivity qualification is indispensable: the empty morphism is finite locally free of rank zero but not surjective. If rank is positive only on a clopen subset $U\subseteq S$, the image is exactly $U$.

## 7. Stability under the standard operations

### 7.1 Arbitrary base change

Base change is the most important operation because fibers, residue extensions, and later group constructions are all instances of it.

**Theorem 7.1.** If $f\colon X\to S$ is finite locally free and $S'\to S$ is arbitrary, then

$$
f'\colon X\times_SS'\longrightarrow S'
$$

is finite locally free. Its rank at $s'\in S'$ equals the rank of $f$ at the image $s$.

**Proof.** Work over $S=\operatorname{Spec}A$ and $S'=\operatorname{Spec}A'$. Write $X=\operatorname{Spec}B$. Then

$$
X\times_SS'=\operatorname{Spec}(B\otimes_AA').
$$

If $B$ is a direct summand of $A^r$, tensoring the splitting with $A'$ shows that $B\otimes_AA'$ is a direct summand of $(A')^r$. Thus it is finite projective. At $s'$, tensoring further with $\kappa(s')$ identifies the fiber with the scalar extension of the fiber at $s$, and vector-space dimension is unchanged by field extension. $\square$

Notice that $S'\to S$ need not be flat. This strength comes from projectivity rather than from exactness of the base-change functor.

### 7.2 Composition and multiplication of degree

Suppose

$$
X\xrightarrow{f}Y\xrightarrow{g}S
$$

are finite locally free. Then $g\circ f$ is finite locally free. Algebraically, take $A\to B\to C$, with $B$ finite projective over $A$ and $C$ finite projective over $B$. A $B$-linear splitting $C\oplus C'\cong B^m$ exhibits $C$ as an $A$-module summand of $B^m$, which is finite projective over $A$. Thus $C$ is finite projective over $A$.

If $g$ has constant degree $m$ and $f$ constant degree $n$, then $g\circ f$ has degree $mn$. More generally, for $x$ over $s$, rank is computed componentwise on the finite scheme $Y_s$. If $f$ has rank function $n(y)$ and $Y_s$ has components selected by idempotents, the $A$-rank of $C$ is the sum of the $B$-ranks weighted by the ranks of the corresponding pieces of $B$. The clean product formula needs constant $n$ on all of $Y$ lying over the relevant component of $S$.

This caveat is real. Let $S$ be connected, $Y=S\amalg S$, so $Y\to S$ has degree $2$. Let $X$ be one copy of $S$ over the first component and two copies over the second. Then $X\to Y$ is finite locally free with ranks $1$ and $2$, not constant, while $X\to S$ has degree $3$, not $2n$ for any single $n$.

### 7.3 Fiber products and products of rank

If $X\to S$ and $Y\to S$ are finite locally free, then $X\times_SY\to S$ is finite locally free. Over $A$, its algebra is $B\otimes_AC$. Since tensor products of finite projective modules are finite projective,

$$
\operatorname{rk}(B\otimes_AC)
=\operatorname{rk}(B)\operatorname{rk}(C)
$$

pointwise. Thus constant degrees multiply. This should not be confused with composition, even though the same numerical law appears; here it is the tensor-product rank formula.

The geometric fiber obeys

$$
(X\times_SY)_{\bar s}\cong X_{\bar s}\times_{\bar s}Y_{\bar s}.
$$

Lengths multiply because dimensions of tensor products of finite-dimensional vector spaces multiply.

### 7.4 Disjoint unions and addition of degree

A finite disjoint union $X=\coprod_iX_i$ over $S$ corresponds on affine charts to $\prod_iB_i$. As an $A$-module a finite product equals a finite direct sum. Hence $X\to S$ is finite locally free exactly when every $X_i\to S$ is, and

$$
\deg(X/S)=\sum_i\deg(X_i/S)
$$

whenever constant degrees are defined.

An infinite disjoint union of nonempty finite schemes is not finite over $S$. Again, “finite” in the number of components is part of the statement.

### 7.5 Closed subschemes and quotients

A closed subscheme $Z\hookrightarrow X=\operatorname{Spec}B$ is given by a quotient $B\to B/I$. If $X$ is finite over $S=\operatorname{Spec}A$, then $Z$ is finite over $S$, since $B/I$ is a quotient of a finite $A$-module. But finite local freeness does not automatically descend to closed subschemes. For example, inside $\operatorname{Spec}A[T]/(T^2)$ the closed subscheme defined by $(aT)$ has algebra $A[T]/(T^2,aT)$, whose fiber rank jumps as in §2.4.

A useful sufficient condition is that $B/I$ be flat and finitely presented over $A$; the latter is automatic if $A$ is noetherian or if $I$ is finitely generated in the situations at hand. Chapter 8 then shows that $Z$ is finite locally free. If, still more strongly, the exact sequence

$$
0\to I\to B\to B/I\to0
$$

splits as $A$-modules, both $I$ and $B/I$ are finite projective whenever $B$ is.

## 8. Finite flatness and finite presentation

### 8.1 The exact equivalences

The terms “finite flat,” “finite locally free,” and “finite projective” are often used almost interchangeably. They are interchangeable over noetherian bases, but not over arbitrary rings. The precise theorem is the following.

**Theorem 8.1.** For an $A$-module $M$, the following are equivalent:

1. $M$ is finitely presented and flat;
2. $M$ is finite projective;
3. $M$ is finite locally free: a finite open cover trivializes it in finite rank.

Equivalently, a module is finite locally free if and only if it is finite, flat, **and finitely presented**. The finite-presentation clause is not redundant over an arbitrary base.

Theorem 3.1 already proved these equivalences. What remains is to understand exactly how the frequently used phrase “finite flat” fits around them.

### 8.2 Why finite flat alone is not enough

Let $k$ be a field and take

$$
A=\prod_{n\ge1}k,
\qquad
I=\bigoplus_{n\ge1}k\subset A,
\qquad
M=A/I.
$$

The ideal $I$ consists of sequences with finite support. The ring $A$ is absolutely flat: for $a=(a_n)$, choose $b_n=a_n^{-1}$ when $a_n\ne0$ and $b_n=0$ otherwise; then $a=a^2b$. Over an absolutely flat ring every module is flat. Hence the cyclic module $M$ is finite and flat.

It is not finitely presented. If it were, the kernel $I$ of the surjection $A\to M$ would be finitely generated. But any finite collection of finite-support sequences is supported in one finite set, so it cannot generate all of $I$. Nor is $M$ projective: a projective cyclic quotient would split $A\to A/I$, making $I$ a direct summand $Ae$ generated by an idempotent. An idempotent of $A$ is the characteristic function of a subset $E\subseteq\mathbb N$; the ideal $Ae$ contains every sequence supported on $E$, not just finite-support sequences. No such $Ae$ equals $I$.

This example pinpoints the failure. At every local ring the localization of $M$ is free of rank zero or one, but those ranks do not spread to a finite open trivializing cover. Finite presentation is precisely the condition that allows local bases and their relations to spread to neighborhoods.

### 8.3 Scheme-theoretic formulations

For a morphism $f\colon X\to S$, the following conditions are equivalent:

1. $f$ is finite locally free;
2. $f$ is finite, flat, and locally of finite presentation;
3. on affine opens $S=\operatorname{Spec}A$, the algebra $B=\Gamma(X,\mathcal O_X)$ is a finitely presented flat $A$-module.

Indeed a finite projective $A$-algebra $B$ is finitely presented as an $A$-algebra. To see this, choose algebra generators and a surjection $A[x_1,\ldots,x_r]\to B$. Since $B$ is finitely presented as an $A$-module, a finite set of module relations, together with finitely many multiplication-table relations for a finite module generating set, yields a finite algebra presentation. Conversely, for a finite flat algebra, local finite presentation supplies the missing finite relations and Theorem 8.1 applies to the underlying module.

One can see the first implication concretely from a finite dual basis $b_i,\lambda_i$ of $B$. Introduce variables $X_i$ corresponding to the $b_i$. The finitely many relations

$$
1=\sum_i\lambda_i(1)X_i,
\qquad
X_iX_j=\sum_k\lambda_k(b_ib_j)X_k
$$

give the correct unit and multiplication table. The dual-basis identity reduces every polynomial to an $A$-linear combination of the $X_i$, while the remaining finitely many linear relations among the $b_i$ identify precisely the desired projective module. Thus finitely many algebra relations suffice even when $B$ has no basis.

Thus “finite flat” by itself can be weaker than “finite locally free” on a nonnoetherian base. Many authors build finite presentation into the situations where they use the phrase; one must check the convention rather than infer the implication.

Without the word finite, flat and finitely presented means **finite locally free only in relative dimension zero when the morphism is also affine and quasi-finite in an appropriate global form**. The affine line is flat and finitely presented but not finite. Without flatness, finite presentation does not prevent rank jumps. Without finite presentation in the general module theorem, a flat module need not be locally free or projective.

### 8.4 Noetherian and coherent shortcuts

Over a noetherian ring, every finite module is finitely presented. Therefore for finite modules the implications simplify:

$$
\text{flat}\Longleftrightarrow\text{projective}
\Longleftrightarrow\text{locally free of finite rank}.
$$

The noetherian hypothesis is a convenience, not part of Theorem 8.1 because finite presentation is stated explicitly there. It becomes decisive when one wishes to omit finite presentation: a finite ring map over a noetherian base is automatically finitely presented even without flatness, whereas the quotient $A/I$ for a non-finitely generated ideal shows failure over arbitrary rings.

A coherent ring, where finitely generated ideals are finitely presented, supports many intermediate finiteness arguments; in particular finite modules presented by controlled kernels behave better. Keeping these facts separate prevents both accidental insertion of noetherian hypotheses and accidental deletion of finite-presentation hypotheses.

### 8.5 Fiber criteria and their limitations

For a finite projective module, constant fiber dimension is equivalent to constant rank. The converse is false for a merely finite module: constant fiber dimension by itself need not imply flatness over a nonreduced base.

For example, let $A=k[\epsilon]/(\epsilon^2)$ and $M=A/(\epsilon)$. The spectrum of $A$ has one point, and the unique fiber $M\otimes_Ak$ has dimension $1$, so fiber dimension is “constant.” Yet $M$ is not flat: tensoring

$$
0\to(\epsilon)\to A
$$

with $M$ kills the inclusion. Thus fiber ranks see variation between points, but not infinitesimal torsion inside the base.

There is a valid local criterion: if $M$ is finitely presented, flatness can be tested after localization, or by vanishing of suitable $\operatorname{Tor}_1$ groups together with flatness of fibers over a quotient. Such criteria are powerful, but finite local freeness should not be inferred from numerical fiber data alone.

## 9. Local rings and discrete valuation rings

### 9.1 Finite projective modules over local rings

Local rings have no nontrivial open-and-closed decomposition, and Nakayama's lemma turns a basis modulo the maximal ideal into a basis upstairs.

**Theorem 9.1.** If $(A,\mathfrak m)$ is local, every finite projective $A$-module $P$ is free. Its rank is

$$
\dim_{A/\mathfrak m}(P/\mathfrak mP).
$$

**Proof.** Choose $p_1,\ldots,p_n$ lifting a residue-field basis. Nakayama gives a surjection $q\colon A^n\twoheadrightarrow P$. Projectivity splits it, so $A^n\cong P\oplus K$ with $K$ finite projective. Reducing modulo $\mathfrak m$, the map $(A/\mathfrak m)^n\to P/\mathfrak mP$ is an isomorphism, hence $K/\mathfrak mK=0$. Nakayama gives $K=0$. $\square$

The same conclusion holds for every finite flat module over a local ring even when finite presentation has not been assumed.

**Theorem 9.2.** A finitely generated flat module $M$ over a local ring $(A,\mathfrak m)$ is finite free.

**Proof.** Choose a minimal generating family $x_1,\ldots,x_n$; its residue classes form a basis of $M/\mathfrak mM$. We show it is linearly independent. Suppose $\sum_i a_ix_i=0$. The equational criterion for flatness factors this relation: there are elements $y_j\in M$ and coefficients $b_{ij}\in A$ such that

$$
x_i=\sum_jb_{ij}y_j,
\qquad
\sum_i a_ib_{ij}=0\quad\text{for every }j.
$$

Write $y_j=\sum_kc_{jk}x_k$ and put $D=(d_{ik})$ with $d_{ik}=\sum_jb_{ij}c_{jk}$. Then $x_i=\sum_kd_{ik}x_k$. Hence every row of $I-D$ is a relation among the minimal generators, so all its entries lie in $\mathfrak m$. Thus $D$ is congruent to $I$ modulo $\mathfrak m$ and is invertible over the local ring. In row-vector notation the original coefficients satisfy $aB=0$, hence $aD=aBC=0$. Invertibility of $D$ gives $a=0$. Therefore the $x_i$ form a basis. $\square$

The equational criterion used in the proof is equivalent to flatness: it says that every finite linear relation among elements of $M$ is induced from finitely many relations among coefficients. It follows directly by tensoring the kernel of the row map $A^n\to A$ determined by $(a_i)$ with $M$.

Thus a finite flat algebra over a local ring is actually finite free. This does not contradict §8.2: over a general ring these local bases need not spread to neighborhoods without finite presentation. The chosen local basis is seldom canonical, but its size is canonical and equals the fiber length.

### 9.2 Flat quotients and idempotents in local rings

If $A/I$ is finite flat over a local ring $A$, then it is free. Since it is cyclic, its rank is at most one. If its rank is zero, $A/I=0$ and $I=A$; if its rank is one, the image of $1$ is a basis and the structure map $A\to A/I$ is an isomorphism, so $I=0$. Therefore a local ring has no nontrivial flat quotient.

Globally, a finitely presented flat quotient $A/I$ corresponds to an idempotent. Localizing shows that at each prime $I$ is either $0$ or the whole local ring. The locus where it is zero is clopen; its idempotent $e$ gives $I=Ae$. This is the module-theoretic shadow of decomposing a scheme into open-and-closed pieces.

### 9.3 Finite modules over a DVR

Let $R$ be a DVR with uniformizer $\pi$ and fraction field $K$. The structure theorem for finite modules over the PID $R$ gives

$$
M\cong R^r\oplus\bigoplus_{i=1}^tR/(\pi^{a_i}),
\qquad a_i\ge1.
$$

Consequently the following are equivalent for a finite $R$-module $M$:

1. $M$ is torsion-free;
2. multiplication by $\pi$ is injective;
3. the natural map $M\to M\otimes_RK$ is injective;
4. $M$ is flat;
5. $M$ is free.

The equivalence between torsion-free and flat actually holds over every valuation domain, though finite freeness uses finite generation. Over a general domain, a finite torsion-free module need not be free or even projective; ideals in a non-PID Dedekind domain provide projective but nonfree examples, and singular domains provide nonprojective ones.

### 9.4 Finite algebras over a DVR

For a finite $R$-algebra $B$, finite flatness is therefore equivalent to $R$-torsion-freeness. Since every nonzero element of $R$ is a unit times a power of $\pi$, it is enough that multiplication by $\pi$ on $B$ be injective. Equivalently, the generic-fiber map

$$
B\longrightarrow B_K=B\otimes_RK
$$

is injective.

When these hold, $B$ is free of rank

$$
n=\dim_KB_K=dim_k(B/\pi B),
$$

where $k=R/(\pi)$. This equality links generic and special fibers: their lengths agree even when their point sets and nilpotent structures do not.

An instructive failure is $B=R[T]/(\pi T,T^2)$. Its generic fiber is $K$, of dimension $1$, but its special fiber is $k[T]/(T^2)$, of dimension $2$. The element $T$ is killed by $\pi$, precisely recording nonflatness.

By contrast, $R[T]/(T^2-\pi)$ is free of rank $2$. Its generic fiber is a field when $T^2-\pi$ is irreducible, while its special fiber is $k[T]/(T^2)$, nonreduced. Flatness preserves length, not reducedness.

### 9.5 Lattices in generic fibers

A finite free $R$-module $M$ inside a finite-dimensional $K$-vector space $V$ with $M\otimes_RK=V$ is an $R$-**lattice**. A finite flat $R$-algebra $B$ is therefore an algebra lattice inside $B_K$. This viewpoint is useful for extending generic-fiber constructions integrally: the issue is whether the chosen lattice is closed under multiplication and whether quotients remain torsion-free.

If $M\subseteq N$ are two lattices in the same $V$, then $N/M$ is finite torsion, killed by a power of $\pi$. Thus lattices differ only at finite valuation depth. But a subalgebra of a finite-dimensional $K$-algebra need not be finite over $R$ unless it is contained in a lattice; valuation bounds are the missing finiteness input.

## 10. Trace, norm, and characteristic polynomials of algebras

### 10.1 Multiplication as the regular representation

Let $B$ be a finite projective $A$-algebra. Each $b\in B$ defines an $A$-linear endomorphism

$$
m_b\colon B\to B,
\qquad x\longmapsto bx.
$$

The map $b\mapsto m_b$ always embeds $B$ into its endomorphism algebra, because $m_b(1)=b$. This remains true even when the structure map $A\to B$ has a kernel. Applying the linear algebra of Chapter 4 gives the **algebra trace** and **algebra norm**

$$
\operatorname{Tr}_{B/A}(b)=\operatorname{tr}(m_b),
\qquad
\operatorname{Nm}_{B/A}(b)=\det(m_b).
$$

If $B$ has constant rank $n$, its characteristic polynomial at $b$ is

$$
\chi_{b,B/A}(T)=\det(T-m_b).
$$

It is monic of degree $n$ and satisfies $\chi_{b,B/A}(b)=0$ in $B$ by Cayley–Hamilton. This gives a canonical integral equation, usually sharper than the determinant-trick equation obtained from arbitrary generators.

Trace is $A$-linear:

$$
\operatorname{Tr}(b+b')=\operatorname{Tr}(b)+\operatorname{Tr}(b'),
\qquad
\operatorname{Tr}(ab)=a\operatorname{Tr}(b).
$$

Norm is multiplicative:

$$
\operatorname{Nm}(bb')=\operatorname{Nm}(b)\operatorname{Nm}(b'),
\qquad
\operatorname{Nm}(1)=1.
$$

Norm is generally not additive. For $a\in A$, multiplication by its image is scalar multiplication, so on a rank-$n$ piece

$$
\operatorname{Tr}_{B/A}(a)=na,
\qquad
\operatorname{Nm}_{B/A}(a)=a^n.
$$

### 10.2 Base-change compatibility

Let $A\to A'$ be arbitrary and put $B'=B\otimes_AA'$. Under the canonical identification

$$
\operatorname{End}_A(B)\otimes_AA'
\cong\operatorname{End}_{A'}(B'),
$$

$m_b\otimes1$ corresponds to $m_{b\otimes1}$. Trace, determinant, and exterior powers commute with arbitrary scalar extension. Therefore

$$
\operatorname{Tr}_{B'/A'}(b\otimes1)
=\operatorname{Tr}_{B/A}(b)\otimes1,
$$

$$
\operatorname{Nm}_{B'/A'}(b\otimes1)
=\operatorname{Nm}_{B/A}(b)\otimes1,
$$

and

$$
\chi_{b\otimes1,B'/A'}(T)
=\chi_{b,B/A}(T)\otimes_AA'.
$$

More generally, for $b'\in B'$ the trace and norm are obtained from the same universal polynomial laws in local coordinates. The displayed formulas on pure base-changed elements are often the needed form.

This compatibility includes localization, ordinary fibers, and geometric fibers. In particular the trace and norm of a specialized element are the specializations of the global trace and norm. No flatness of $A'$ is required.

### 10.3 Examples

For $B=A^n$, an element $b=(b_1,\ldots,b_n)$ acts diagonally. Hence

$$
\chi_b(T)=\prod_{i=1}^n(T-b_i),
\quad
\operatorname{Tr}(b)=\sum_i b_i,
\quad
\operatorname{Nm}(b)=\prod_i b_i.
$$

For $B=A[T]/(T^2-c)$ with basis $1,t$, multiplication by $x+yt$ has matrix

$$
\begin{pmatrix}
x&cy\\
y&x
\end{pmatrix}.
$$

Thus

$$
\operatorname{Tr}(x+yt)=2x,
\qquad
\operatorname{Nm}(x+yt)=x^2-cy^2.
$$

For the dual numbers $B=A[\epsilon]/(\epsilon^2)$,

$$
m_{x+y\epsilon}=
\begin{pmatrix}x&0\\y&x\end{pmatrix},
$$

so trace is $2x$ and norm is $x^2$. Nilpotent directions can disappear from both invariants without disappearing from the algebra.

If $B=A[T]/(f)$ with $f$ monic of degree $n$ and $t$ the class of $T$, the companion matrix shows

$$
\chi_{t,B/A}(T)=f(T).
$$

In particular $\operatorname{Nm}(t)=(-1)^nf(0)$ and $\operatorname{Tr}(t)$ is the negative coefficient of $T^{n-1}$ in $f$.

### 10.4 Units and the norm

An element $b\in B$ is a unit if and only if the endomorphism $m_b$ is invertible. For an endomorphism of a finite projective module, invertibility is equivalent to invertibility of its determinant: locally this is the adjugate formula, and local inverses glue uniquely. Hence

$$
b\in B^\times
\quad\Longleftrightarrow\quad
\operatorname{Nm}_{B/A}(b)\in A^\times.
$$

The reverse implication uses that if $m_b$ is an automorphism then its inverse sends $1$ to an element $c$ with $bc=1$. This criterion makes norm a morphism from the multiplicative units of $B$ to those of $A$ and will later support multiplicative group constructions.

### 10.5 Transitivity in towers

Let $A\to B\to C$ be finite locally free, and assume for clarity that $B$ has constant rank $m$ over $A$ and $C$ constant rank $n$ over $B$. Then

$$
\operatorname{Tr}_{C/A}
=\operatorname{Tr}_{B/A}\circ\operatorname{Tr}_{C/B},
$$

$$
\operatorname{Nm}_{C/A}
=\operatorname{Nm}_{B/A}\circ\operatorname{Nm}_{C/B}.
$$

For trace, choose locally an $A$-basis $(b_i)$ of $B$ and a $B$-basis $(c_j)$ of $C$. The products $b_ic_j$ form an $A$-basis of $C$. View an endomorphism of $C$ as an $n\times n$ matrix over $B$, each entry itself acting on the rank-$m$ module $B$. The ordinary block-matrix trace is the trace over $A$ of the matrix trace over $B$. Applying this to multiplication by $c$ proves the formula.

For norm, use the determinant-of-restriction lemma:

$$
\det_A(u)=\operatorname{Nm}_{B/A}(\det_Bu)
$$

for a $B$-linear endomorphism $u$ of a finite free $B$-module. Here the right side means the determinant over $A$ of multiplication by the element $\det_Bu$ on $B$. A direct proof chooses bases, writes $u$ as a matrix over $B$, replaces each entry by its $m\times m$ multiplication matrix over $A$, and expands the resulting block determinant. Regrouping the Leibniz expansion first by the induced permutation of the $B$-basis gives exactly the determinant of multiplication by the ordinary $B$-determinant of $u$. Since the assertion is invariant under both basis changes, localization proves it for projective modules. Taking $u=m_c$ yields norm transitivity.

When ranks vary, these identities hold on every clopen rank stratum. The formulas themselves remain global because trace and norm glue across that decomposition.

### 10.6 The trace pairing and the discriminant

The **trace pairing** is the symmetric $A$-bilinear form

$$
\tau_{B/A}\colon B\times B\to A,
\qquad
(x,y)\longmapsto\operatorname{Tr}_{B/A}(xy).
$$

It corresponds to an $A$-linear map

$$
\theta_{B/A}\colon B\longrightarrow B^\vee,
\qquad
x\longmapsto(y\mapsto\operatorname{Tr}(xy)).
$$

For constant rank $n$, its determinant is a section of

$$
(\det B^\vee)\otimes(\det B)^{-1}
\cong(\det B^\vee)^{\otimes2}.
$$

If a basis $e_1,\ldots,e_n$ is chosen, it is represented by

$$
\operatorname{disc}(e_1,\ldots,e_n)
=\det\big(\operatorname{Tr}(e_ie_j)\big).
$$

Changing basis by a matrix $U$ multiplies this scalar by $(\det U)^2$. Therefore the discriminant is intrinsically a quadratic element attached to the determinant line; it becomes an ordinary element or ideal after choosing a trivialization. The **discriminant ideal** is locally generated by these determinants and is globally well defined.

Because trace and duals commute with base change, the trace-pairing map and its determinant do too. Thus discriminants specialize correctly:

$$
\operatorname{disc}(B\otimes_AA'/A')
=\operatorname{disc}(B/A)A'
$$

as ideals, with the corresponding statement for determinant-line sections.

### 10.7 Perfect trace pairing and finite étale examples

The trace pairing is **perfect** when $\theta_{B/A}$ is an isomorphism. This can be checked after localization or arbitrary faithfully flat base change. For a finite separable field extension $L/K$, the pairing $(x,y)\mapsto\operatorname{Tr}_{L/K}(xy)$ is perfect. For a purely inseparable field extension it is degenerate; often the trace is identically zero.

The split algebra $A^n$ has perfect trace pairing, represented in its idempotent basis by the identity matrix. Any algebra that becomes $A'^n$ after a faithfully flat base change therefore has perfect trace pairing. Such algebras are basic finite étale examples.

Conversely, for a finite locally free commutative algebra, perfectness of the trace pairing is closely tied to being étale, but a systematic development of unramifiedness, étaleness, and coverings belongs later. Here the examples serve only to contrast two phenomena:

* $A^n$ is finite flat and has reduced, separated geometric points;
* $A[\epsilon]/(\epsilon^2)$ is finite flat but its trace pairing is degenerate and every fiber has a nilpotent.

Finite flatness controls length and base change. It does not control infinitesimal structure.

### 10.8 The norm as a polynomial law

Although $b\mapsto\operatorname{Nm}(b)$ is usually nonlinear, it is homogeneous of degree $n$ on a constant-rank-$n$ algebra:

$$
\operatorname{Nm}(ab)=a^n\operatorname{Nm}(b).
$$

After choosing a local basis, the multiplication matrix entries are linear functions of the coordinates of $b$, so its determinant is a degree-$n$ polynomial. These local polynomials agree on overlaps and under every base change. Thus norm can be evaluated functorially on

$$
b\in B\otimes_AC
$$

for any $A$-algebra $C$, producing an element of $C$. This functorial viewpoint is stronger than treating norm as a set map on $B$ and explains why it defines geometric morphisms in later applications.

The characteristic polynomial similarly supplies coefficient functions $s_i(b)$ homogeneous of degree $i$:

$$
\chi_b(T)=T^n-s_1(b)T^{n-1}+\cdots+(-1)^ns_n(b),
$$

with $s_1=\operatorname{Tr}$ and $s_n=\operatorname{Nm}$. All of them commute with base change.

## 11. Descent of finite projective structure

### 11.1 Why descent is needed

Local freeness is meant to be recognized after passing to a cover. Ordinary open covers are built into the definition, but arithmetic constructions often use a faithfully flat ring map $A\to A'$ instead. If an $A$-module becomes finite free or finite projective over $A'$, when may one conclude that it was finite projective over $A$?

Faithfulness is essential. The localization $A\to A_f$ may erase all behavior on $V(f)$, so projectivity after that single nonfaithful base change says nothing there. Flatness is also essential for descending relations. The correct basic statement is that finite presentation and flatness descend through faithfully flat maps.

### 11.2 Faithfully flat detection of exactness

Let $A\to A'$ be faithfully flat. A sequence of $A$-modules

$$
M'\xrightarrow{u}M\xrightarrow{v}M''
$$

is exact at $M$ if and only if its scalar extension to $A'$ is exact at $M\otimes_AA'$.

Indeed, flatness preserves kernels and images in the required direction. Conversely, let $H=\ker(v)/\operatorname{im}(u)$. Flatness identifies $H\otimes_AA'$ with the homology after base change. If this vanishes, faithful flatness forces $H=0$. Similarly, a map is zero, injective, or surjective if its base change has that property, using its image, kernel, or cokernel.

Faithful flatness also detects equality of submodules and isomorphisms. These elementary observations replace most gluing computations in what follows.

### 11.3 Descent of finite generation

**Lemma 11.1.** If $A\to A'$ is faithfully flat and $M\otimes_AA'$ is finite over $A'$, then $M$ is finite over $A$.

**Proof.** Choose finitely many elements of $M\otimes_AA'$ generating it. Each is a finite sum of pure tensors, so finitely many elements $m_1,\ldots,m_r\in M$ occur in all of them. Let $N=\sum Am_i$. Then the image of $N\otimes_AA'$ contains the chosen generators and hence equals $M\otimes_AA'$. Therefore $(M/N)\otimes_AA'=0$. Faithfulness gives $M/N=0$. $\square$

This proof is pleasantly direct. Descent of finite presentation requires control of relations as well.

### 11.4 Descent of finite presentation

**Lemma 11.2.** If $A\to A'$ is faithfully flat and $M\otimes_AA'$ is finitely presented over $A'$, then $M$ is finitely presented over $A$.

**Proof.** By Lemma 11.1 choose a surjection $A^r\twoheadrightarrow M$ with kernel $K$. Flatness gives an exact sequence

$$
0\to K\otimes_AA'\to(A')^r\to M\otimes_AA'\to0.
$$

Since the last module is finitely presented, the kernel $K\otimes_AA'$ is finite. Lemma 11.1 applied to $K$ makes $K$ finite. Hence $M$ has a finite presentation. $\square$

The argument shows exactly where faithful flatness enters: it prevents generators and relations from disappearing after scalar extension.

### 11.5 Descent of flatness

**Lemma 11.3.** If $A\to A'$ is faithfully flat and $M\otimes_AA'$ is flat over $A'$, then $M$ is flat over $A$.

**Proof.** For every injection $N_1\hookrightarrow N_2$, consider

$$
N_1\otimes_AM\longrightarrow N_2\otimes_AM.
$$

After tensoring with $A'$, associativity identifies it with

$$
(N_1\otimes_AA')\otimes_{A'}(M\otimes_AA')
\longrightarrow
(N_2\otimes_AA')\otimes_{A'}(M\otimes_AA').
$$

The first map $N_1\otimes_AA'\to N_2\otimes_AA'$ is injective because $A'$ is flat; the displayed map is injective because $M\otimes_AA'$ is flat. Faithful flatness detects injectivity before base change. Thus $M$ is flat. $\square$

### 11.6 Descent theorem for finite projective modules

Combining the preceding lemmas gives:

**Theorem 11.4.** Let $A\to A'$ be faithfully flat. An $A$-module $P$ is finite projective if and only if $P\otimes_AA'$ is finite projective over $A'$.

The forward implication is ordinary base change. For the reverse, finite projectivity upstairs implies finite presentation and flatness upstairs; Lemmas 11.2 and 11.3 descend both properties, and Theorem 3.1 gives finite projectivity downstairs.

Ranks are also detected. For each prime $\mathfrak p$ of $A$, faithful flatness supplies a prime $\mathfrak q$ of $A'$ above it. The rank of $P$ at $\mathfrak p$ equals the rank of $P\otimes_AA'$ at $\mathfrak q$, since the corresponding fibers differ by extension of residue fields. Hence constant rank $n$ descends.

### 11.7 Descent for algebras and schemes

Suppose $A\to A'$ is faithfully flat and $B$ is an $A$-algebra. If $B\otimes_AA'$ is finite projective over $A'$, then $B$ is finite projective over $A$, by Theorem 11.4 applied to its underlying module. Therefore

$$
\operatorname{Spec}(B\otimes_AA')\to\operatorname{Spec}A'
$$

being finite locally free implies

$$
\operatorname{Spec}B\to\operatorname{Spec}A
$$

is finite locally free. Constant degree descends as well.

More generally, if a given morphism $X\to S$ becomes finite locally free after a faithfully flat and quasi-compact base change $S'\to S$, then it is finite locally free. Affineness and finiteness descend under such covers, while flatness and finite presentation descend by the affine arguments above. The quasi-compact qualification guarantees that the cover controls global finiteness; it is automatic for a single affine faithfully flat map.

In the common affine recognition case there is no hidden geometric step. If $S=\operatorname{Spec}A$, $X=\operatorname{Spec}B$, and $S'=\operatorname{Spec}A'$, then the pullback is $\operatorname{Spec}(B\otimes_AA')$ and Theorem 11.4 applies verbatim. For a general given $X$, affineness descent can be reduced to this case as follows. The finite locally free pullback is affine, so its coordinate algebra has two pullbacks to $S'\times_SS'$ identified by the fact that both come from $X$. The equalizer of these two algebra maps is a quasi-coherent algebra $\mathcal A$ on $S$. Faithful flatness makes the natural map

$$
X\longrightarrow\underline{\operatorname{Spec}}_S(\mathcal A)
$$

an isomorphism after pullback to $S'$. Isomorphisms are detected by a faithfully flat cover, so it was already an isomorphism. Hence $X\to S$ is affine. Lemmas 11.1–11.3 then descend finiteness, finite presentation, and flatness of $\mathcal A$, giving finite local freeness. This is the elementary equalizer form of affine descent.

This theorem descends a property of an object already defined downstairs. Constructing a downstairs object from an upstairs object requires **descent data**: an isomorphism between its two pullbacks to $S'\times_SS'$ satisfying a cocycle condition over the triple product. That broader construction is not needed for recognizing finite locally free structure, but the distinction prevents a common logical error: existence after a cover does not by itself identify what should be descended.

### 11.8 Zariski and finite families of localizations

Let $f_1,\ldots,f_r$ generate the unit ideal. Then

$$
A\longrightarrow\prod_{i=1}^rA_{f_i}
$$

is faithfully flat. Theorem 11.4 therefore recovers the familiar statement that a module is finite projective if it becomes finite projective on a finite principal-open cover. If each localization is free of rank $n$, the module has constant rank $n$.

For an infinite open cover, quasi-compactness of $\operatorname{Spec}A$ extracts a finite subcover. For covers of a general scheme, the same argument is applied affine-locally. Thus Zariski-local and faithfully-flat descent are manifestations of the same principle: sufficiently rich scalar extensions detect finite generators, finite relations, and exactness.

## 12. Finite algebras as sheaves

### 12.1 Relative spectra without a general scheme-theory detour

The affine calculations globalize through quasi-coherent algebras. Let $S$ be a scheme and $\mathcal A$ a quasi-coherent $\mathcal O_S$-algebra. Its relative spectrum

$$
\underline{\operatorname{Spec}}_S(\mathcal A)\longrightarrow S
$$

is characterized by the rule that over every affine $U=\operatorname{Spec}A$ with $\mathcal A|_U$ associated to an $A$-algebra $B$, its inverse image is $\operatorname{Spec}B$. Localization compatibility glues these affine pieces.

Conversely, for an affine morphism $f\colon X\to S$, the sheaf $f_*\mathcal O_X$ is a quasi-coherent $\mathcal O_S$-algebra and the natural map

$$
X\longrightarrow\underline{\operatorname{Spec}}_S(f_*\mathcal O_X)
$$

is an isomorphism. Therefore finite morphisms over $S$ correspond contravariantly to quasi-coherent $\mathcal O_S$-algebras that are finite as modules. Finite locally free morphisms correspond to those whose underlying modules are locally free of finite rank.

This language is useful because $S$ need not be affine, while all proofs remain affine-local.

### 12.2 Pullback and pushforward under base change

Consider a cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
S'&\xrightarrow{g}&S.
\end{array}
$$

When $f$ is affine, there is a canonical isomorphism of algebras

$$
g^*(f_*\mathcal O_X)\xrightarrow{\sim}f'_*\mathcal O_{X'}.
$$

On affine charts this is simply

$$
B\otimes_AA'\cong B\otimes_AA'.
$$

For finite locally free $f$, dualizing and base change give

$$
g^*((f_*\mathcal O_X)^\vee)
\xrightarrow{\sim}
(f'_*\mathcal O_{X'})^\vee.
$$

Trace, norm, characteristic coefficients, and the trace-pairing map commute with these identifications. This sheaf form is what permits the invariants to be defined over a nonaffine base.

### 12.3 Internal Hom for finite locally free modules

If $\mathcal P$ is finite locally free on $S$, put

$$
\mathcal P^\vee=\mathcal Hom_{\mathcal O_S}(\mathcal P,\mathcal O_S).
$$

For any quasi-coherent $\mathcal M$, the evaluation construction gives

$$
\mathcal P^\vee\otimes\mathcal M
\xrightarrow{\sim}
\mathcal Hom(\mathcal P,\mathcal M).
$$

In particular, Hom from a finite locally free module remains quasi-coherent and commutes with every pullback. If both $\mathcal P$ and $\mathcal Q$ are finite locally free, so are $\mathcal P^\vee$, $\mathcal P\otimes\mathcal Q$, and $\mathcal Hom(\mathcal P,\mathcal Q)$.

The corresponding ranks are pointwise

$$
\operatorname{rk}(\mathcal P^\vee)=\operatorname{rk}(\mathcal P),
\qquad
\operatorname{rk}\mathcal Hom(\mathcal P,\mathcal Q)
=\operatorname{rk}(\mathcal P)\operatorname{rk}(\mathcal Q).
$$

These formulas support dual algebraic constructions later: all evaluation and coevaluation maps survive specialization exactly.

### 12.4 The relative dual of a finite locally free morphism

For $f\colon X\to S$ finite locally free, the module

$$
\mathcal D_{X/S}=(f_*\mathcal O_X)^\vee
$$

is finite locally free of the same rank. It is naturally an $f_*\mathcal O_X$-module by

$$
(b\cdot\lambda)(x)=\lambda(bx).
$$

Equivalently it may be regarded as a quasi-coherent module on $X$. The trace defines a distinguished $f_*\mathcal O_X$-linear map

$$
f_*\mathcal O_X\longrightarrow\mathcal D_{X/S},
\qquad
b\longmapsto(x\mapsto\operatorname{Tr}(bx)).
$$

This is the trace-pairing map of §10.6. It is not generally an isomorphism: dual numbers already give a degenerate example. Nevertheless $\mathcal D_{X/S}$ itself always has good base-change behavior, because it comes from the module dual rather than from an assertion of trace-perfectness.

### 12.5 Projection formula in the finite setting

Let $f\colon X\to S$ be finite, let $\mathcal F$ be a quasi-coherent module on $X$, and let $\mathcal M$ be a quasi-coherent module on $S$. There is an isomorphism

$$
f_*\mathcal F\otimes_{\mathcal O_S}\mathcal M
\xrightarrow{\sim}
f_*(\mathcal F\otimes_{\mathcal O_X}f^*\mathcal M).
$$

On $S=\operatorname{Spec}A$, with $X=\operatorname{Spec}B$ and $\mathcal F$ represented by a $B$-module $N$, both sides are the $A$-module $N\otimes_AM$. The formula is therefore just associativity of tensor products. Unlike more general pushforwards, no higher or properness machinery is hidden here.

When $f$ is finite locally free, applying the formula to dual modules gives a clean way to transport pairings between $X$ and $S$. The trace map then contracts a $B$-valued pairing to an $A$-valued one.

## 13. Idempotents, components, and sections

### 13.1 Idempotents are finite decompositions

An idempotent $e\in B$ gives a product decomposition

$$
B\xrightarrow{\sim}Be\times B(1-e),
\qquad
b\longmapsto(be,b(1-e)).
$$

Geometrically,

$$
\operatorname{Spec}B
=D(e)\amalg D(1-e)
$$

is a decomposition into open-and-closed subschemes. Conversely every such decomposition produces an idempotent. A finite family of pairwise orthogonal idempotents $e_i$ summing to $1$ gives a finite disjoint-union decomposition.

If $B$ is finite projective over $A$, each factor $Be$ is an $A$-module direct summand and hence finite projective. Its rank can vanish on some components of $\operatorname{Spec}A$ and be positive on others. This is the algebraic reason that a component of a finite locally free scheme can fail to surject onto the entire base.

### 13.2 Idempotents and base change

Every idempotent of $B$ remains idempotent in $B\otimes_AA'$, so decompositions persist under base change. New idempotents can appear after base change. For example, a finite separable field extension $L/K$ may be connected over $K$ while

$$
L\otimes_K\overline K\cong\overline K^{[L:K]}
$$

has many idempotents. Thus connectedness of a finite scheme is not preserved by arbitrary extension of the ground field.

Nilpotent thickenings do not alter idempotents. If $I\subseteq B$ is nilpotent, every idempotent of $B/I$ lifts uniquely to an idempotent of $B$. Existence may be seen by correcting an arbitrary lift through a finite polynomial iteration, while uniqueness follows because if $e-e'\in I$, the identity

$$
(e-e')(e+e'-1)=0
$$

and the fact that $e+e'-1$ is a unit modulo the nilpotent ideal force $e=e'$. Consequently a finite scheme and its reduction have the same open-and-closed components.

### 13.3 Sections in algebraic form

Let $f\colon X=\operatorname{Spec}B\to S=\operatorname{Spec}A$. A section $s\colon S\to X$ corresponds contravariantly to an $A$-algebra homomorphism

$$
s^*\colon B\longrightarrow A
$$

whose composite $A\to B\to A$ is the identity. Thus sections are augmentations of the algebra. The kernel $I=\ker(s^*)$ gives an $A$-module decomposition

$$
B\cong A\oplus I,
$$

but generally not a product decomposition of algebras: $I$ need not be generated by an idempotent.

For the dual numbers, the quotient $A[\epsilon]/(\epsilon^2)\to A$ supplies a section, and $B=A\oplus A\epsilon$ as a module. Yet the image of the section is not open unless the base is empty, because $(\epsilon)$ is nilpotent and defines the entire underlying topological space. This example separates sections from components.

### 13.4 A section of a finite map is closed

Every finite morphism is separated. A general separated morphism has closed sections: the section is the pullback of the diagonal along the map $(s,\operatorname{id}_S)$. In affine terms the claim is immediate: the map $B\to A$ corresponding to the section is surjective because it retracts $A\to B$, so $\operatorname{Spec}A\to\operatorname{Spec}B$ is a closed immersion.

For the section to be open as well requires extra structure. Algebraically, its kernel must be generated by an idempotent, so that $B\cong A\times B'$. This holds for sections of suitable finite étale morphisms but not for arbitrary finite flat morphisms. Therefore one must never remove a section as a disjoint component merely from finite flatness.

### 13.5 Retractions and rank accounting

Suppose $B$ is finite projective of constant rank $n$ over $A$ and admits an augmentation $B\to A$. Its kernel $I$ is an $A$-module direct summand, hence finite projective of rank $n-1$. This rank statement concerns modules even when the section is not a component.

If the section is open and closed, then $B\cong A\times B'$ as algebras, and $B'$ is finite projective of rank $n-1$. Geometrically,

$$
X\cong S\amalg X'.
$$

Without an idempotent, one still has the conormal module $I/I^2$, which measures the first-order thickness of $X$ along the section. For dual numbers it is free of rank one. This indicates why nonreduced finite flat schemes possess infinitesimal directions even though their fibers have dimension zero.

## 14. Anatomy of fibers

### 14.1 Artinian algebras over a field

Every finite-dimensional algebra $C$ over a field $k$ is Artinian. It has finitely many maximal ideals $\mathfrak m_1,\ldots,\mathfrak m_r$, and powers of these ideals are pairwise comaximal. The Chinese remainder theorem yields a canonical product decomposition

$$
C\cong\prod_{i=1}^r C_i
$$

into Artinian local $k$-algebras. Therefore

$$
\operatorname{Spec}C=\coprod_{i=1}^r\operatorname{Spec}C_i.
$$

Each $C_i$ has one point, residue field $k_i=C_i/\mathfrak m_i$, and nilpotent maximal ideal. Its contribution to the $k$-dimension is

$$
\dim_kC_i=[k_i:k]\,\operatorname{length}_{C_i}(C_i).
$$

Thus the length of a finite fiber records both residue-field extension and local nilpotent multiplicity.

### 14.2 Geometric points versus length

After extension to an algebraic closure $\bar k$, every residue field factor separates according to its separable embeddings, while purely inseparable residue extensions thicken. If $C$ is reduced and separable over $k$, then

$$
C\otimes_k\bar k\cong\bar k^n,
\qquad n=\dim_kC.
$$

If $C=k[T]/(T^p-a)$ in characteristic $p$ with $a$ not a $p$th power, then $C$ is a field of degree $p$, but over $\bar k$ it becomes

$$
\bar k[T]/((T-\alpha)^p),
$$

one geometric point of length $p$. If $C=k[T]/(T^n)$, it already has one point of length $n$ over $k$.

These examples explain why degree of a finite locally free morphism is defined through vector-space dimension, not through cardinality of a fiber. Cardinality is unstable even under extension of the residue field; length is stable.

### 14.3 Variation in a flat family

In the family $A=k[t]$, $B=A[T]/(T^2-t)$, every fiber has length $2$. Away from $t=0$ and in characteristic not $2$, the geometric fiber has two reduced points. At $t=0$ they coalesce into a doubled point. The underlying topological cardinality drops, while module rank remains constant.

In contrast, $B=A[T]/(tT,T^2)$ has generic fiber of length $1$ and special fiber of length $2$. The class of $T$ is $t$-torsion. Thus the slogan is exact:

$$
\text{flatness forbids creation of fiber length from base torsion.}
$$

It does not forbid collision, splitting after field extension, or nilpotence.

### 14.4 Reduced and étale boundary cases

A finite locally free morphism whose geometric fibers are reduced is finite étale. This criterion is useful as orientation, but its proof and systematic consequences require the theory of differentials and étale morphisms and are not developed here. We use only transparent examples: constant finite schemes and spectra of finite separable field extensions are finite étale; dual numbers and purely inseparable field extensions are not.

The boundary clarifies terminology. “Finite flat” is an integral linear-algebra condition. “Finite étale” adds the absence of infinitesimal ramification. A later theory of finite étale covers will organize monodromy and fundamental groups. Nothing in the present book depends on that theory.

### 14.5 Support and the image of a finite locally free scheme

For a finite $A$-module $M$, its support

$$
\operatorname{Supp}(M)=\{\mathfrak p:M_{\mathfrak p}\ne0\}
$$

is closed when $M$ is finite, equal to $V(\operatorname{Ann}_A(M))$. If $M$ is finite projective, its support is also open because it is the union of positive-rank strata. Hence it is clopen.

For a finite locally free algebra $B$, the image of $\operatorname{Spec}B\to\operatorname{Spec}A$ equals $\operatorname{Supp}(B)$. Indeed a fiber is nonempty exactly when $B\otimes_A\kappa(\mathfrak p)\ne0$. Thus the image is the clopen locus where rank is positive. On that locus the morphism is faithfully flat and surjective; on its complement it is empty.

If one assumes the usual convention that an algebra structure map preserves a nonzero identity on every connected component, rank is positive there. Retaining the support formulation handles the zero algebra and disconnected bases without concealed conventions.

## 15. Worked structural patterns

### 15.1 A monic equation over an arbitrary base

Let

$$
B=A[T]/(T^n+a_1T^{n-1}+\cdots+a_n),
$$

and write $t$ for the image of $T$. Division by a monic polynomial works over any commutative ring, so every element has a unique expression

$$
b=b_0+b_1t+\cdots+b_{n-1}t^{n-1}.
$$

Thus $B$ is free of rank $n$, independently of zero divisors or nilpotents in $A$. The multiplication matrix of $t$ in this basis is the companion matrix, giving

$$
\chi_t(U)=U^n+a_1U^{n-1}+\cdots+a_n,
$$

$$
\operatorname{Tr}_{B/A}(t)=-a_1,
\qquad
\operatorname{Nm}_{B/A}(t)=(-1)^na_n.
$$

After any base change $A\to A'$, the same basis and formulas persist with the coefficients mapped to $A'$. At a prime $\mathfrak p$, the factorization of the specialized polynomial describes the points of the fiber, but multiplicities and residue degrees always sum to $n$.

For $n=2$ and polynomial $T^2-sT+p$, multiplication by $x+yt$ has matrix

$$
\begin{pmatrix}
x&-py\\
y&x+sy
\end{pmatrix}.
$$

Hence

$$
\operatorname{Tr}(x+yt)=2x+sy,
\qquad
\operatorname{Nm}(x+yt)=x^2+sxy+py^2.
$$

The trace matrix in the basis $(1,t)$ is

$$
\begin{pmatrix}
2&s\\
s&s^2-2p
\end{pmatrix},
$$

whose determinant is $s^2-4p$. The familiar quadratic discriminant is therefore exactly the discriminant of the trace pairing, with the formula valid in every characteristic. In characteristic $2$ its behavior warns that reducedness and separability cannot be read using characteristic-zero intuition.

### 15.2 Splitting a base and varying rank

Let $A=A_1\times A_2$. Every $A$-module splits canonically as

$$
M=e_1M\times e_2M,
\qquad e_1=(1,0),\ e_2=(0,1).
$$

Take finite free algebras $B_1$ and $B_2$ of ranks $r$ and $s$ over $A_1$ and $A_2$, and view $B=B_1\times B_2$ as an $A$-algebra. Then $B$ is finite projective, but its rank function is $r$ on $\operatorname{Spec}A_1$ and $s$ on $\operatorname{Spec}A_2$. If $r\ne s$, there is no global degree.

All invariants split componentwise:

$$
\operatorname{Tr}_{B/A}(b_1,b_2)
=(\operatorname{Tr}_{B_1/A_1}(b_1),
\operatorname{Tr}_{B_2/A_2}(b_2)),
$$

and similarly for norm. Characteristic polynomials have different degrees on the two components, which is why they must be interpreted on clopen rank strata.

This example also explains composition subtleties. If $Y=S\amalg S$ and a finite locally free $X\to Y$ has degrees $r$ and $s$ on the two components, then $X\to S$ has degree $r+s$. There is no legitimate expression $2n$ unless $r=s=n$.

### 15.3 Two integral models with the same generic rank

Let $R$ be a DVR with uniformizer $\pi$ and fraction field $K$. Compare

$$
B_1=R[T]/(T^2-\pi),
\qquad
B_2=R[T]/(\pi T,T^2).
$$

The first is free with basis $(1,t)$, hence finite locally free of degree $2$. Its generic fiber has dimension $2$ and its special fiber is $k[T]/(T^2)$, also of length $2$. The special fiber is nonreduced, but no rank is lost.

The second is generated by $(1,t)$ but satisfies $\pi t=0$. Its generic fiber kills $t$ and is just $K$, while its special fiber is again $k[T]/(T^2)$. The generic and special lengths are $1$ and $2$. The visible $\pi$-torsion proves nonflatness.

Thus two schemes can have isomorphic special fibers while only one is flat, and two finite $R$-algebras can look equally small in presentations while having different generic ranks. The reliable diagnostic is torsion-freeness of the whole coordinate algebra.

The traces also expose the difference. In $B_1$, multiplication acts on a rank-$2$ free module and gives a genuine degree-$2$ characteristic polynomial. In $B_2$, there is no globally valid rank-$2$ determinant package: the module is not projective, and specializing an arbitrarily chosen two-generator presentation would create spurious invariants.

### 15.4 A closed subscheme that ceases to be flat

Let $X=\operatorname{Spec}R[T]/(T^2)$, finite locally free of degree $2$ over a DVR $R$. Inside $X$, impose the additional equation $\pi T=0$. The resulting closed subscheme

$$
Z=\operatorname{Spec}R[T]/(T^2,\pi T)
$$

is finite but not flat. Its generic fiber is the reduced section defined by $T=0$, while its special fiber is the entire doubled point.

This example captures a recurring issue. Closedness is preserved automatically inside a finite scheme because quotients of finite modules remain finite. Flatness is not preserved because a quotient can introduce base torsion. To show that a closed subscheme of a finite locally free scheme is finite locally free, one must prove the quotient algebra flat and finitely presented, or over a DVR simply prove it torsion-free.

There is a useful exact-sequence test. Given

$$
0\to I\to B\to C\to0
$$

with $B$ finite projective, if $C$ is finite projective then the sequence splits as $A$-modules and $I$ is finite projective. Conversely, if $I$ and $C$ are both flat and one has sufficient finite presentation, all three are finite projective. Merely knowing that $I$ is an ideal does not supply these properties.

### 15.5 Recognizing a family after a faithfully flat cover

Suppose $A\to A'$ is faithfully flat and an $A$-algebra $B$ is given. Assume a calculation upstairs produces an explicit $A'$-basis

$$
u_1,\ldots,u_n
\quad\text{of}\quad B\otimes_AA'.
$$

One should not expect the $u_i$ themselves to descend to a basis of $B$; they may transform nontrivially over $A'\otimes_AA'$. Nevertheless they prove that $B\otimes_AA'$ is finite projective of rank $n$. The descent theorem then proves that $B$ is finite projective of rank $n$. Local bases downstairs exist even when no preferred global basis does.

Trace and norm may be computed upstairs and descended. If $b\in B$, calculate the matrix of $m_{b\otimes1}$ in the chosen basis. Its trace and determinant lie initially in $A'$. Base-change compatibility says they equal the images of $\operatorname{Tr}_{B/A}(b)$ and $\operatorname{Nm}_{B/A}(b)$. The two pullbacks of these values to $A'\otimes_AA'$ agree, and faithful flatness makes their downstairs origin unique.

This pattern separates two roles of a cover. A cover may simplify coordinates enough to prove and calculate; faithful descent then guarantees that the coordinate-independent result belongs to the original base.

## 16. Constant rank repairs finite flatness

### 16.1 Why rank is the missing hypothesis

The distinction between finite flat and finite locally free is not pedantry. A finite flat module over an arbitrary ring can fail to be finitely presented, and without finite presentation there need not be any neighborhood on which a finite set of generators becomes a basis. Chapter 8 exhibited this failure. Yet the finite-flat objects used in arithmetic geometry usually carry a degree. That numerical datum is precisely what rules out the pathology.

Let $M$ be a finite flat $A$-module. For $\mathfrak p\in\operatorname{Spec}A$, set

$$
r_M(\mathfrak p)=\dim_{\kappa(\mathfrak p)}
   (M\otimes_A\kappa(\mathfrak p)).
$$

This dimension is finite because $M$ is finite. For a finite projective module it is locally constant. For a merely finite flat module it need not be locally constant, and its discontinuity records exactly where finite presentation fails. Thus there are three statements, not two:

* finite locally free implies finite flat and has locally constant finite rank;
* finite flat need not be finite locally free;
* finite flat with locally constant rank is finite locally free.

On a connected base, “locally constant finite rank” is the same as “constant rank $n$” for one integer $n$. On a nonconnected base, a single integer is an additional condition and cannot be silently built into the phrase finite locally free.

### 16.2 The constant-rank theorem

**Theorem 16.1 (finite flat constant-rank criterion).** Let $M$ be a finitely generated flat $A$-module. If $r_M$ is locally constant on $\operatorname{Spec}A$, then $M$ is finite projective. More precisely, near every prime $\mathfrak p$ at which the rank is $n$, the module is free of rank $n$.

The difficulty is that the kernel of a surjection from a finite free module onto $M$ need not initially be finite. The proof therefore uses constant rank to prove injectivity directly, rather than trying to apply the finite form of Nakayama's lemma to that kernel.

**Proof.** Fix $\mathfrak p$. After replacing $A$ by a principal localization around $\mathfrak p$, local constancy lets us assume that every maximal fiber has dimension $n=r_M(\mathfrak p)$. Choose elements of $M$ whose images form a basis after localization at $\mathfrak p$. Clearing denominators and shrinking once more, they define a surjection

$$
q:A^n\twoheadrightarrow M.
$$

We show that $q$ is injective. Localize at a maximal ideal $\mathfrak m$. Flatness of $M_{\mathfrak m}$ and finiteness of $M$ imply that it is free over the local ring $A_{\mathfrak m}$; this local freeness theorem for finite flat modules over a local ring does not require a globally finite presentation. Its rank is the dimension of its residue fiber, hence is $n$. The localized map

$$
q_{\mathfrak m}:A_{\mathfrak m}^n\twoheadrightarrow M_{\mathfrak m}
$$

is consequently a surjection between free modules of the same finite rank. Its reduction modulo $\mathfrak m$ is a surjection between $n$-dimensional vector spaces and hence an isomorphism. Its determinant is therefore a unit, so $q_{\mathfrak m}$ is an isomorphism. A module map is injective when it is injective at every maximal localization. Hence $q$ is an isomorphism on the chosen neighborhood. These neighborhoods cover the spectrum, proving that $M$ is finite locally free, and therefore finite projective. $\square$

The local input in this proof can itself be understood through equational flatness. Over a local ring $(A,\mathfrak m)$, lift a basis of $M/\mathfrak mM$ to a minimal finite generating family. Every relation among those generators becomes, by flatness, an $A$-linear combination of relations whose coefficients vanish appropriately. Minimality forces all coefficients to vanish, so the generators are independent. This is the finite-flat analogue of the familiar proof that a finitely generated projective module over a local ring is free.

**Corollary 16.2.** A finite morphism $f:X\to S$ that is flat and whose fiber-length function is locally constant is finite locally free. If every fiber has length $n$, then it has constant degree $n$.

Indeed, on an affine open $S=\operatorname{Spec}A$, write $X=\operatorname{Spec}B$. The fiber length is $r_B(\mathfrak p)$, so Theorem 16.1 applies.

This is the formulation behind the common phrase “finite flat of degree $n$.” It is safe when degree $n$ is part of the data or has been proved. It is unsafe to infer local freeness from the two words finite and flat over an unrestricted base.

### 16.3 Locally constant rank and nonconnected bases

Suppose

$$
S=S_1\amalg S_2,
\qquad
X=X_1\amalg X_2,
$$

where $X_i\to S_i$ has constant degree $n_i$. Then $X\to S$ is finite locally free, with rank function equal to $n_i$ on $S_i$. There is no reason for $n_1=n_2$. For example, with $A=k\times k$ and

$$
B=k^2\times k^3,
$$

viewed as an $A$-algebra componentwise, $\operatorname{Spec}B\to\operatorname{Spec}A$ has degrees $2$ and $3$ on the two connected components.

Every locally constant map from a quasi-compact space to the discrete set $\mathbb N$ has finite image. Hence a finite locally free morphism over a quasi-compact base has only finitely many occurring degrees, and the base decomposes into finitely many clopen rank strata

$$
S=\coprod_n S_n.
$$

All constant-rank constructions may be performed on these strata and then reassembled. Determinant lines, trace, and characteristic-polynomial coefficients are already global; only formulas that mention a single degree require this decomposition. For instance, the scalar formula

$$
\operatorname{Nm}_{B/A}(a)=a^n
$$

holds on the degree-$n$ stratum. Globally it is a family of such formulas, not an identity with an unspecified integer exponent.

Faithful flatness has a similarly componentwise form. A finite locally free morphism is faithfully flat exactly when its rank is positive at every point of the base. If it has rank zero on a clopen union of components, its source is empty there. Thus nonempty source does not imply faithful flatness when the base is disconnected.

### 16.4 Criteria over local rings and valuation bases

Over a local ring, every finite flat module is free. Its rank is determined by its closed fiber, so no separate constancy check is needed after the base has been localized at one point. This statement is local in the ring-theoretic sense; it does not imply that a finite flat module on an arbitrary spectrum is locally free without controlling how the local ranks vary on neighborhoods.

Over a DVR $R$, the criterion becomes especially concrete. For a finite $R$-module $M$, the following are equivalent:

1. $M$ is flat;
2. $M$ is torsion-free;
3. multiplication by a uniformizer $\pi$ is injective on $M$;
4. $M$ is finite free.

If $K$ is the fraction field and $k$ the residue field, then in this case

$$
\operatorname{rank}_R M
=\dim_K(M\otimes_RK)
=\dim_k(M/\pi M).
$$

This equality is the most efficient degree test in one-parameter integral families. A proposed finite model whose special fiber has larger length than its generic fiber contains torsion and is not flat. If the lengths agree and the module is known finite, torsion-freeness still needs proof; equality of two selected fibers alone is not a general flatness criterion over higher-dimensional or nonreduced bases.

Over a Dedekind domain, every finite torsion-free module is projective, though it need not be free. Consequently a finite algebra over a Dedekind domain is finite locally free exactly when it is torsion-free as a module. The possible failure of global freeness is measured by ideal classes, another reminder that locally free does not mean equipped with a global basis.

## 17. The unramified and étale boundary

### 17.1 Differentials measure infinitesimal motion

Finite local freeness keeps fiber length constant but allows points to collide and thicken. To separate those behaviors one needs a test for infinitesimal motion. For a ring map $A\to B$, the module of relative differentials $\Omega_{B/A}$ is generated by symbols $db$ subject to

$$
d(b+b')=db+db',\qquad d(bb')=b\,db'+b'\,db,
\qquad da=0\quad(a\in A).
$$

It represents $A$-derivations:

$$
\operatorname{Hom}_B(\Omega_{B/A},N)
\cong\operatorname{Der}_A(B,N).
$$

Thus $\Omega_{B/A}=0$ means that $B$ admits no first-order motion relative to $A$. If

$$
B=A[x_1,\ldots,x_r]/(f_1,\ldots,f_m),
$$

then $\Omega_{B/A}$ is generated by $dx_j$ with relations

$$
df_i=\sum_j\frac{\partial f_i}{\partial x_j}dx_j.
$$

For a monogenic algebra $B=A[T]/(f)$, this reduces to

$$
\Omega_{B/A}\cong B\,dT/(f'(t)dT).
$$

Hence the differential vanishes exactly when $f'(t)$ is a unit in $B$. This calculation is the source of the derivative criterion for unramified points.

Differentials commute with arbitrary base change when the evident tensor comparison is made:

$$
\Omega_{(B\otimes_AA')/A'}
\cong\Omega_{B/A}\otimes_B(B\otimes_AA').
$$

Vanishing therefore ascends under every base change and descends under faithfully flat base change.

### 17.2 Finite unramified and finite étale algebras

A ring map $A\to B$ of finite type is **unramified** when $\Omega_{B/A}=0$. Geometrically, a morphism is unramified when it is locally of finite type and its diagonal is an open immersion; the differential criterion is equivalent to this statement on affine charts. No flatness is included. A finite morphism has a closed diagonal, so for a finite unramified morphism the diagonal is both open and closed.

An algebra is **étale** over $A$ when it is finitely presented, flat, and unramified. Consequently:

**Theorem 17.1.** For a finite locally free $A$-algebra $B$, the following are equivalent:

1. $B$ is étale over $A$;
2. $B$ is unramified over $A$;
3. $\Omega_{B/A}=0$.

Finite local freeness already supplies finite presentation and flatness, so only the infinitesimal condition remains. The theorem cleanly identifies the boundary: finite locally free geometry governs constant length, while finite étale geometry is the locus where that length consists geometrically of distinct reduced points.

For $B=A[T]/(f)$ with $f$ monic, the algebra is finite free. It is finite étale precisely when the images of $f$ and $f'$ generate the unit ideal in $A[T]$, equivalently when $f'(t)$ is a unit in $B$. If $f=T^n-a$, the condition is that $nt^{n-1}$ be a unit in $B$. When $a$ is a unit this says that $n$ is a unit. Thus adjoining an $n$th root of a unit is finite étale away from residue characteristics dividing $n$, but may remain finite locally free and become ramified in those characteristics.

### 17.3 Geometric fibers and separability

Let $k$ be a field and $C$ a finite-dimensional commutative $k$-algebra. The following are equivalent:

* $C$ is étale over $k$;
* $C$ is a finite product of finite separable field extensions of $k$;
* $C\otimes_k\bar k$ is a product of copies of $\bar k$;
* $C\otimes_k\bar k$ is reduced.

The last condition must use a geometric fiber. If $k$ is imperfect, a finite purely inseparable field extension is reduced as a $k$-algebra but becomes nonreduced after extending scalars to an algebraic closure. Over a perfect field, ordinary reducedness is enough because every finite field extension is separable.

**Theorem 17.2 (fiber criterion).** A finite locally free morphism $X\to S$ is finite étale if and only if every geometric fiber is reduced.

One direction follows from base change and the field classification. Conversely, geometric reducedness makes every fiber algebra separable, so the fiber of $\Omega_{X/S}$ vanishes at every point. The differential module is finite because the morphism is finitely presented. Nakayama's lemma then gives $\Omega_{X/S}=0$, and Theorem 17.1 applies.

This criterion has no analogue with “every fiber has the right number of topological points” unless geometric residue fields and multiplicities are handled carefully. Purely inseparable extensions and nilpotent thickenings show the two distinct failures.

### 17.4 The trace-pairing criterion

The trace pairing from Chapter 10 detects exactly the same boundary.

**Theorem 17.3 (trace criterion).** Let $B$ be a finite locally free commutative $A$-algebra. Then $B$ is finite étale over $A$ if and only if

$$
B\longrightarrow B^\vee,
\qquad b\longmapsto(x\mapsto\operatorname{Tr}_{B/A}(bx))
$$

is an isomorphism. On a constant-rank stratum, this is equivalent to the discriminant being a unit.

**Proof strategy.** Both the trace map and being an isomorphism commute with base change. The assertion may therefore be checked on geometric fibers. Over an algebraically closed field, a finite étale algebra is $k^n$, whose trace pairing is the standard dot product. Conversely, if a finite-dimensional commutative algebra has a nonzero nilpotent $z$, then every $zx$ is nilpotent and multiplication by it is nilpotent, so $\operatorname{Tr}(zx)=0$ for every $x$. The nilradical lies in the radical of the trace pairing. Perfectness forces the algebra to be reduced, and over an algebraically closed field it is then a product of copies of the field. The fiber criterion finishes the proof. $\square$

This theorem justifies the qualification left open in §10.7. It also turns the étale locus into an explicit open subset: it is the complement of the vanishing locus of the discriminant section. For a finite locally free family, ramification is therefore a closed condition, although its detailed multiplicities require a theory of the different beyond the present scope.

### 17.5 Ramified boundary examples

The dual numbers $A[\epsilon]/(\epsilon^2)$ are free of rank $2$, but

$$
d(\epsilon^2)=2\epsilon\,d\epsilon
$$

does not kill $d\epsilon$ in general. Every geometric fiber is nonreduced, and the trace pairing is degenerate. This is the universal small example of finite locally free but non-étale behavior.

For $B=A[T]/(T^2-a)$, the trace matrix in the basis $(1,t)$ is

$$
\begin{pmatrix}
2&0\\
0&2a
\end{pmatrix},
$$

so its discriminant is $4a$. The étale locus is where $2a$ is invertible. If $a$ vanishes, two geometric points collide; if $2$ vanishes, separability can fail even when $a$ is a unit.

Finally, $k\to k^{1/p}$ in characteristic $p$ is finite locally free as a field extension, but not étale when it is nontrivial and purely inseparable. Its source is reduced, demonstrating why reducedness before geometric base change is insufficient.

## 18. Quotients, kernels, and exactness

### 18.1 Why finite locally free objects do not form an abelian category

Later constructions repeatedly take kernels, images, and quotients. The ambient category of modules has all of them, but finite projective modules are not closed under them. Over $A=\mathbb Z$, multiplication by $2$ gives

$$
\mathbb Z\xrightarrow{2}\mathbb Z
$$

between finite free modules, while its cokernel $\mathbb Z/2\mathbb Z$ is not flat. Over a ring with a nonprojective finitely generated ideal $I$, the inclusion $I\hookrightarrow A$ may have finite target and finite quotient without $I$ being projective. Exactness must therefore be accompanied by a flatness, projectivity, or splitting argument.

The reliable principle is simple: kernels and cokernels exist in all modules; they remain finite locally free only when an additional hypothesis makes the relevant short exact sequence locally split.

### 18.2 Split exact sequences and rank bookkeeping

Consider an exact sequence

$$
0\longrightarrow P'\longrightarrow P\longrightarrow P''\longrightarrow0.
$$

If $P''$ is projective, the surjection splits and $P\cong P'\oplus P''$. It follows that if $P$ and $P''$ are finite projective, then $P'$ is finite projective. If $P'$ and $P''$ are finite projective, then $P$ is finite projective. By contrast, knowing $P'$ and $P$ are finite projective does not force $P''$ to be flat, as multiplication by $2$ shows.

Whenever all three are finite locally free,

$$
\operatorname{rk}P
=\operatorname{rk}P'+\operatorname{rk}P''
$$

pointwise, and the determinant-line isomorphism of §4.3 applies. These facts are stable under arbitrary base change because a split sequence remains split.

A useful quotient criterion follows. If $P$ is finite projective and $Q$ is a finitely presented quotient, then $Q$ is finite projective exactly when it is flat. In that event the sequence splits and the kernel is finite projective. Over a DVR, “$Q$ is flat” can be replaced by “$Q$ is torsion-free.”

### 18.3 Quotients of finite locally free algebras

Let $B$ be a finite locally free $A$-algebra and $I\subseteq B$ an ideal. The quotient $C=B/I$ is always finite over $A$, but it is finite locally free precisely when its underlying $A$-module satisfies one of the equivalent projectivity criteria. Sufficient conditions include:

* $C$ is finitely presented and flat over $A$;
* $C$ is finite flat with locally constant fiber rank;
* $A$ is a DVR and $C$ is torsion-free;
* the $A$-module surjection $B\to C$ admits a splitting.

If $C$ is finite projective, then

$$
0\longrightarrow I\longrightarrow B\longrightarrow C\longrightarrow0
$$

splits as $A$-modules, so $I$ is finite projective. The splitting need not respect multiplication, and $I$ generally has no identity; it should not be mistaken for a product decomposition of algebras. Such a decomposition occurs exactly when the ideal is generated by an idempotent and the quotient is an open-and-closed component.

Geometrically, a closed subscheme of a finite locally free $S$-scheme is finite over $S$ but need not be flat. It is finite locally free if its quotient algebra passes one of the tests above. If it does, its fiber length is locally constant, and the complementary rank

$$
\operatorname{rk}_A I=\operatorname{rk}_A B-\operatorname{rk}_A C
$$

measures equations as an $A$-module, not a geometric complementary component.

### 18.4 Images, equalizers, and base change

For an $A$-algebra map $B\to C$ with $C$ finite over $A$, the scheme-theoretic image of

$$
\operatorname{Spec}C\longrightarrow\operatorname{Spec}B
$$

is $\operatorname{Spec}(B/\ker(B\to C))$. If $B$ is finite over $A$, this image is finite over $A$. It need not be finite locally free, because taking an image is taking a quotient module.

Flat base change behaves well: for a flat $A$-algebra $A'$,

$$
\ker(B\to C)\otimes_AA'
\cong
\ker(B\otimes_AA'\to C\otimes_AA').
$$

Thus scheme-theoretic images of finite morphisms commute with flat base change. Without flatness, kernels can grow after tensoring and the assertion fails.

Equalizers are governed by the same issue. The equalizer of two maps $u,v:P\to Q$ is $\ker(u-v)$. If $Q$ is flat and the cokernel of $u-v$ is finite projective, then the kernel is finite projective; without such a hypothesis it may not be. Algebra equalizers commute with flat base change because flat tensor products preserve kernels. These qualifications are essential when invariant subalgebras or fixed-point conditions are introduced later.

### 18.5 Fiberwise criteria for maps

Let $u:P\to Q$ be a map of finite projective $A$-modules. If every residue-field map

$$
u_{\mathfrak p}:P\otimes_A\kappa(\mathfrak p)
\longrightarrow Q\otimes_A\kappa(\mathfrak p)
$$

is surjective, then $u$ is surjective: its finite cokernel has zero fiber at every prime and hence vanishes. Since $Q$ is projective, the map splits and the kernel is finite projective.

If every fiber map is injective, injectivity of $u$ follows after localizing and choosing bases only when the ranks and cokernel behavior exclude hidden torsion. A clean sufficient condition is that the cokernel be flat; then tensoring the exact sequence with every residue field preserves the kernel. Equal-rank maps admit a determinant test. On a constant-rank-$n$ stratum,

$$
u\text{ is an isomorphism near }\mathfrak p
\quad\Longleftrightarrow\quad
\det(u)\notin\mathfrak p.
$$

The isomorphism locus is therefore open. If every fiber map is an isomorphism, the determinant is a unit and $u$ is an isomorphism globally. This last criterion is among the safest ways to descend identities and compare two proposed finite locally free models.

## 19. Schematic closure and saturation

### 19.1 Closing a generic subscheme

Integral models are often specified first on a generic fiber and then extended across the base. Topological closure remembers which points specialize, but it does not determine nilpotents or equations. The correct construction is schematic closure.

Let $j:U\hookrightarrow S$ be a schematically dense open immersion, let $X\to S$ be a scheme, and let $Z_U\hookrightarrow X_U$ be a closed subscheme. If $k:Z_U\to X$ is the composite, the **schematic closure** $\overline Z\hookrightarrow X$ is defined by the kernel

$$
\mathcal O_X\longrightarrow k_*\mathcal O_{Z_U}.
$$

It is the smallest closed subscheme through which $k$ factors. The same scheme-theoretic-image construction applies after a localization that is not literally an open immersion, notably passage from a domain to its fraction field. Concretely, let $S=\operatorname{Spec}A$, let $S_0\subseteq A$ be multiplicative, let $X=\operatorname{Spec}B$, and suppose the localized closed subscheme is

$$
Z_U=\operatorname{Spec}(S_0^{-1}B/J_U),
$$

the closure is $\operatorname{Spec}(B/J)$ with

$$
J=\ker(B\longrightarrow S_0^{-1}B/J_U)
=B\cap J_U.
$$

The intersection is taken inside $S_0^{-1}B$. This formula immediately proves minimality: an ideal $I\subseteq B$ has localized closed subscheme containing $Z_U$ exactly when $S_0^{-1}I\subseteq J_U$, hence $I\subseteq J$.

If $X\to S$ is finite, then $\overline Z\to S$ is finite because $B/J$ is a quotient of a finite module. Flatness is a separate question. Schematic closure preserves equations by contraction; it does not magically preserve projectivity.

### 19.2 Saturation in modules and ideals

Given a submodule $N\subseteq M$ and a multiplicative set $S_0$, its **$S_0$-saturation** is

$$
N^{\mathrm{sat}}
=\{m\in M:\text{ some }s\in S_0\text{ satisfies }sm\in N\}.
$$

Equivalently,

$$
N^{\mathrm{sat}}
=\ker(M\longrightarrow S_0^{-1}(M/N)).
$$

Thus $M/N^{\mathrm{sat}}$ is the image of $M/N$ in its localization and has no element killed by an element of $S_0$. Saturation is idempotent, contains $N$, and has the same localization as $N$. It is the unique largest submodule of $M$ with that localization.

When $M=B$ and $N=I$ is an ideal, $I^{\mathrm{sat}}$ is again an ideal: if $si\in I$, then $s(bi)=b(si)\in I$. The affine schematic closure of the subscheme defined by $S_0^{-1}I$ is therefore defined by $I^{\mathrm{sat}}$. If one begins directly with an ideal $J_U\subseteq S_0^{-1}B$, its contraction is already saturated.

For a domain $A$ with fraction field $K$, take $S_0=A\setminus\{0\}$. Then saturation removes precisely the $A$-torsion from the quotient:

$$
B/I^{\mathrm{sat}}
\hookrightarrow (B/I)\otimes_AK.
$$

This injection is the basic flatness mechanism over a valuation base. Over a general domain, torsion-free need not mean flat, so it is only the beginning of the argument.

### 19.3 The DVR closure theorem

**Theorem 19.1.** Let $R$ be a DVR with fraction field $K$, let $B$ be a finite locally free $R$-algebra, and let $Z_K\hookrightarrow\operatorname{Spec}(B_K)$ be a closed subscheme. Its schematic closure $Z\hookrightarrow\operatorname{Spec}B$ is finite locally free over $R$. Its degree equals the $K$-dimension of the coordinate algebra of $Z_K$.

**Proof.** Write $Z_K=\operatorname{Spec}(B_K/J_K)$ and let $J=B\cap J_K$. The contraction formula identifies $Z$ with $\operatorname{Spec}(B/J)$. By construction,

$$
B/J\hookrightarrow B_K/J_K,
$$

so $B/J$ is torsion-free over $R$. It is finite because it is a quotient of the finite $R$-module $B$. A finite torsion-free module over a DVR is free. Localization gives

$$
(B/J)\otimes_RK\cong B_K/J_K,
$$

so its rank is the displayed generic dimension. $\square$

The same proof gives a frequently used module statement. If $P$ is finite free over a DVR and $N_K\subseteq P_K$, then

$$
N=P\cap N_K
$$

and $P/N$ are finite free; moreover $N\otimes_RK=N_K$. Indeed, $P/N$ injects into $P_K/N_K$, hence is torsion-free, and then $N$ is a submodule of a finite free module. This provides exact integral lattices from exact generic data.

The saturation clause is essential. In $R^2$, the submodule generated by $(\pi,0)$ has the same generic span as the submodule generated by $(1,0)$, but the first quotient contains $\pi$-torsion. The schematic closure of the generic line uses the saturated second submodule, not the chosen nonsaturated lattice.

### 19.4 Dedekind bases and the limits of the theorem

Over a Dedekind domain, the proof remains valid with “finite free” replaced by “finite projective.” A finite torsion-free module is projective, so the schematic closure of a generic closed subscheme inside a finite locally free ambient scheme is finite locally free. Its rank is constant on each connected component and agrees with generic degree.

Over an arbitrary domain, the conclusion can fail. Saturation guarantees only torsion-freeness of the quotient, and finite torsion-free modules need not be flat or projective. Over a nonnormal base, even a rank-one torsion-free module can fail to be invertible. Over a higher-dimensional normal domain, reflexive modules need not be locally free at codimension at least two. Therefore the closure theorem must always name the property of the base that turns finite torsion-free modules into projective ones; a DVR or Dedekind domain is sufficient, while “integral” by itself is not.

Closure also need not commute with arbitrary base change. A nonflat base change can create new torsion and enlarge kernels. If the saturated quotient is finite flat and the pulled-back open remains schematically dense, then flat base change does preserve the closure: flatness preserves the defining kernel, and the pulled-back quotient remains torsion-free. By contrast, starting from a nonsaturated presentation and merely tensoring its equations can give something smaller than the closure; saturation must occur before this comparison.

### 19.5 Closure of algebraic structure

Suppose a generic closed subscheme $Z_K$ carries operations expressed by morphisms between finite schemes: a multiplication, identity, inverse, action, or endomorphism. To extend an operation to its closure, one first checks that the generic map sends the chosen integral coordinate lattice into the appropriate lattice. Density then gives uniqueness: two morphisms from a flat $R$-scheme to a separated $R$-scheme that agree on the generic fiber agree everywhere, because their equalizer is closed and contains a schematically dense open.

Existence is not automatic from uniqueness. For a multiplication $Z_K\times_KZ_K\to Z_K$, one must show that the corresponding algebra map preserves the contracted ideals, or equivalently that the ambient multiplication carries the closure product into the closure. When $Z_K$ is a closed subgroup of a finite locally free group over a DVR, the contracted Hopf ideal is stable under the structural maps because the relevant containments hold after localization and the target quotients are torsion-free. The closure is then again finite locally free by Theorem 19.1. This is the algebraic mechanism that later permits generic finite subgroup data to acquire integral finite-flat models.

The argument also explains its boundary. If a quotient introduced torsion, equality on the generic fiber would not detect maps into that torsion. Flatness of the closure is what makes the generic fiber schematically dense and turns generic identities into integral identities.

## 20. Weil restriction along a finite locally free map

### 20.1 The functor and its variance

Changing the base of a scheme is easy: one forms a fiber product. Going in the opposite direction is subtler. Let $p:S'\to S$ be finite locally free and let $X'$ be an $S'$-scheme. The **Weil restriction**, when representable, is the $S$-functor

$$
\operatorname{Res}_{S'/S}(X')(T)
=\operatorname{Hom}_{S'}(T\times_SS',X')
$$

for $S$-schemes $T$. It packages an $S'$-valued family as an object over $S$ by remembering all of its coordinates along the finite fibers of $S'/S$.

The finite locally free hypothesis is exactly what makes those coordinates behave like a finite vector bundle. If $S'$ has degree $d$ over $S$, an affine line over $S'$ should restrict to an affine bundle of rank $d$ over $S$. Without finite projectivity, duals need not commute with base change and there is no uniform coordinate object.

Variance deserves attention. A map $X'\to Y'$ induces

$$
\operatorname{Res}_{S'/S}(X')
\longrightarrow\operatorname{Res}_{S'/S}(Y').
$$

A base change $S_1\to S$ changes both $S'$ and $X'$, and restriction is expected to commute with it. These properties follow directly from the defining Hom functor once representability is established.

### 20.2 Restriction of affine space

Work first with $S=\operatorname{Spec}A$, $S'=\operatorname{Spec}B$, where $B$ is finite projective over $A$. Let $P$ be a finite projective $B$-module and let

$$
\mathbf V_{S'}(P)=\underline{\operatorname{Spec}}_{S'}
  (\operatorname{Sym}_B P^\vee)
$$

be its associated affine space. For an $A$-algebra $R$, an $R$-point of its restriction is an element of

$$
P\otimes_A R,
$$

where $P$ is regarded as an $A$-module. Since $P$ is finite projective over $B$ and $B$ finite projective over $A$, it is finite projective over $A$. Therefore this functor is represented by

$$
\mathbf V_S(P_A)
=\operatorname{Spec}\big(\operatorname{Sym}_A(P_A^\vee)\big).
$$

In particular,

$$
\operatorname{Res}_{S'/S}(\mathbf A^1_{S'})
\cong\mathbf V_S(B),
$$

an affine bundle of rank $d$. If $B$ is free with basis $e_1,\ldots,e_d$, a point of $R\otimes_AB$ has coordinates $x_1,\ldots,x_d$, and the restriction is ordinary $d$-dimensional affine space. A different basis acts by a linear change of coordinates; the vector-bundle formulation is what glues when $B$ is only locally free.

### 20.3 Equations and affine representability

Let $X'=\operatorname{Spec}_{S'}C$ be affine. Choose a presentation of the $B$-algebra $C$ by generators $x_i$ and relations $f_j$. An $S'$-map

$$
\operatorname{Spec}(R\otimes_AB)\longrightarrow X'
$$

is a choice of elements $c_i\in R\otimes_AB$ satisfying $f_j(c_i)=0$. Each $c_i$ is represented by a point of the vector bundle associated with $B$. Each value $f_j(c_i)$ lies in $R\otimes_AB$. It vanishes if and only if all its coordinates against the dual module $B^\vee$ vanish. Hence every $B$-valued relation becomes finitely many $A$-valued relations locally on $S$.

This proves:

**Theorem 20.1 (affine Weil restriction).** If $p:S'\to S$ is finite locally free and $X'\to S'$ is affine, then $\operatorname{Res}_{S'/S}(X')$ is represented by an affine $S$-scheme. If $X'$ is of finite type or finite presentation over $S'$, the representing scheme has the same respective finiteness property over $S$.

The construction does not depend on the chosen generators. Two resulting affine schemes represent the same functor, so the Yoneda principle gives a unique isomorphism between them. On overlaps where $B$ becomes free, these unique isomorphisms satisfy the cocycle condition and glue. This is an instance where a functorial characterization removes all basis dependence.

Closed immersions are preserved. If $Z'\hookrightarrow X'$ is cut out by equations, its restriction is cut out by all coordinate equations obtained through $B^\vee$. The result is a closed immersion

$$
\operatorname{Res}_{S'/S}(Z')
\hookrightarrow\operatorname{Res}_{S'/S}(X').
$$

### 20.4 Base change, products, and open subfunctors

For every $S_1\to S$, there is a canonical isomorphism

$$
\operatorname{Res}_{S'/S}(X')\times_SS_1
\cong
\operatorname{Res}_{S'\times_SS_1/S_1}
   (X'\times_SS_1).
$$

It is proved by evaluating both sides on an $S_1$-scheme $T$: the two Hom sets are literally the same. This compatibility is one of the principal reasons for using finite locally free maps rather than a coordinate-dependent restriction construction.

Weil restriction also preserves finite products and fiber products whenever the displayed functors are representable:

$$
\operatorname{Res}(X'\times_{Z'}Y')
\cong\operatorname{Res}(X')
\times_{\operatorname{Res}(Z')}\operatorname{Res}(Y').
$$

This follows because Hom into a fiber product is a fiber product of Hom sets. It will allow identities expressed by product diagrams to survive restriction.

Open immersions require more geometry than closed equations. If $U'\hookrightarrow X'$ is an open immersion and $X'$ is affine, then $\operatorname{Res}(U')$ is an open subfunctor of $\operatorname{Res}(X')$. Its complement consists of maps for which the inverse image of the closed complement meets at least one point of the finite fiber. That incidence condition is closed because a finite morphism has closed image; its complement is open. In the principal case $U'=D(g)$, the condition is that $g(c)$ be a unit in $R\otimes_AB$, equivalently that

$$
\operatorname{Nm}_{(R\otimes_AB)/R}(g(c))
$$

be a unit. Thus the restricted open is the principal open defined by this norm.

### 20.5 Quasi-projective gluing and its boundary

Suppose $X'\to S'$ is quasi-projective and of finite presentation. Choose an immersion into a projective space over $S'$. Sections of the pulled-back projective bundle whose graphs satisfy the defining equations form an open subfunctor inside a suitable affine or projective parameter space, and the incidence argument above controls the domain on which a section lands in $X'$. This constructs a scheme representing $\operatorname{Res}_{S'/S}(X')$, and the representing scheme is quasi-projective over $S$. The finite-presentation condition keeps the parameter spaces and their equations finite.

The quasi-projectivity hypothesis supplies enough common affine neighborhoods for several points in one finite fiber. Without such a hypothesis, the functor can fail to be a scheme even when it exists naturally as a more general geometric object. The affine theorem is unconditional within its stated scope; the nonaffine theorem must not be replaced by the claim that restriction along a finite locally free map always produces a scheme.

Separatedness also matters in gluing local restrictions. Two maps that agree after pullback to a cover glue uniquely, but finding a single affine neighborhood containing the image of an entire finite fiber is a genuine geometric condition. Quasi-projective schemes have this property because finitely many points lie in a common affine open after working locally on the base.

### 20.6 Units, sections, and a norm example

Apply affine restriction to the multiplicative group over $S'$. For an $A$-algebra $R$,

$$
\operatorname{Res}_{B/A}(\mathbf G_m)(R)
=(R\otimes_AB)^\times.
$$

Inside the vector bundle representing $R\otimes_AB$, this is the open locus where the norm is invertible. It is therefore represented by a principal open affine scheme. The norm itself defines a morphism

$$
\operatorname{Res}_{B/A}(\mathbf G_m)
\longrightarrow\mathbf G_m,
$$

and its compatibility with arbitrary base change is exactly the base-change compatibility of determinants.

At the other extreme, $\operatorname{Res}_{S'/S}(X')$ records sections of $X'$ after every base change. Its $S$-points are simply sections $S'\to X'$. Thus restriction converts a relative section problem over a finite base into an ordinary point problem over the original base. This is the interface used in moduli constructions: endomorphisms, trivializations, embeddings, and finite collections of marked data can often be realized as points of an affine or quasi-projective restriction.

If $S'=\coprod_{i=1}^dS$ is split, then

$$
\operatorname{Res}_{S'/S}(X')
\cong\prod_{i=1}^dX'_i.
$$

This formula gives the correct intuition for all preceding results. General finite locally free restriction is the twisted, base-independent version of taking one copy for each point of a finite fiber.

## 21. Descent interfaces for group schemes and moduli

### 21.1 Finite locally free algebras form a descent category

Book 13 established effective faithfully flat descent for modules, algebras, affine schemes, and finite locally free objects. Here is the specialized package needed in finite geometry. Let $S'\to S$ be an fpqc cover. A finite locally free $\mathcal O_{S'}$-algebra $\mathcal B'$ equipped with an isomorphism between its two pullbacks to $S'\times_SS'$ satisfying the cocycle condition descends uniquely to a finite locally free $\mathcal O_S$-algebra $\mathcal B$.

Effectivity occurs in stages. First the underlying module descends. Multiplication and the unit are morphisms between tensor constructions of that module, so full faithfulness descends them. Associativity, commutativity, and the unit laws are equalities of maps; faithful flatness detects those equalities. Finite projectivity descends because finite presentation and flatness descend. Taking relative spectra then gives effective descent for finite locally free schemes.

Rank descends pointwise. If $S'$ has constant rank $n$ after pullback and the cover meets every component, the descended algebra has constant rank $n$. More generally a locally constant rank function upstairs descends exactly when it is compatible on the double overlap, in which case it determines a locally constant function downstairs.

### 21.2 Descending morphisms, subobjects, and identities

A compatible morphism of descended algebras descends uniquely. Its properties of being an isomorphism, injection, or surjection can be checked after faithfully flat base change because kernels and cokernels are detected there. On the geometric side, morphisms, closed immersions, and finite locally free morphisms descend.

A closed subobject needs both equations and flatness. Compatible ideals descend as submodules when their inclusion maps and quotient data descend. If the quotient is finite locally free upstairs, that property descends, so the resulting closed subscheme is finite locally free downstairs. Merely descending an ideal inside a finite locally free algebra guarantees a finite closed subscheme, not a flat one.

Algebraic structures specified by diagrams descend economically. A multiplication, inverse, pairing, action, or involution consists of morphisms among finite products and base changes. Descend the morphisms; then check each required identity after pulling back to the cover. This is the interface needed before the systematic theory of group objects: the finite locally free carrier and all of its structural arrows may be descended without changing category.

### 21.3 Exactness after a faithfully flat cover

For modules, a sequence is exact if and only if its pullback along a faithfully flat map is exact. For finite locally free modules, one must add that the descended kernel or quotient remains finite locally free when the later construction requires it. This is automatic if the corresponding module upstairs is finite locally free and is equipped with compatible descent data.

For finite group objects, exactness is eventually interpreted in a sheaf topology: the first object is the kernel and the last map is locally surjective in the chosen topology. The present algebraic input is that kernels are fiber products, fiber products commute with base change, and faithful flatness descends the relevant finite locally free property. A pointwise exact sequence of abstract groups on geometric fibers is not a substitute; it can miss infinitesimal kernels and failure of flatness.

An especially safe procedure for a proposed quotient is:

1. construct the algebra quotient and verify compatibility of its descent datum;
2. prove finite presentation and flatness, or prove constant fiber rank together with finite flatness;
3. descend the quotient as a finite locally free object;
4. verify the universal property after the cover, where maps are detected faithfully.

This order prevents a set-theoretic orbit space from being mistaken for a scheme-theoretic quotient.

### 21.4 Norms, determinants, and duals under descent

Duals and tensor products of finite locally free modules commute with pullback. Therefore evaluation, coevaluation, exterior powers, determinant lines, trace maps, norm laws, characteristic polynomials, and trace pairings all inherit descent data. Their descended versions agree with those constructed directly downstairs because each is characterized by a universal map or by a basis-independent determinant.

This compatibility is stronger than numerical invariance. For example, if a trivialization of a determinant line upstairs is compatible on overlaps, it descends to a trivialization downstairs. If a pairing is perfect upstairs, its determinant is a unit upstairs and hence downstairs; the descended pairing is perfect. If a finite locally free algebra becomes étale over a faithfully flat cover, the vanishing of its differential module descends, so it was already étale.

Norm constructions and Weil restriction fit together particularly well. After pulling back to a cover that trivializes a rank-$d$ algebra as a module, norm is an ordinary determinant polynomial in $d$ coordinates. The change-of-basis invariance of determinant is precisely the overlap compatibility needed to descend that polynomial.

### 21.5 A moduli-oriented descent protocol

Finite-flat data in a moduli problem often become elementary only after an fpqc cover. The following protocol isolates what must be shown.

First identify the carrier: a finite locally free algebra or scheme, with its rank function. Next list every structural map and express every axiom as an equality of morphisms. Then record any closed conditions as ideals or zero loci and any open conditions as invertibility loci, often detected by a determinant or norm. Verify the cocycle on the double and triple overlaps. Apply effective descent to the carrier and full faithfulness to the maps. Finally descend the properties—finite local freeness, constant degree, closedness, perfectness, or étaleness—rather than assuming that the descended object inherits them by notation.

Representability questions can then be separated from descent. Homomorphisms between finite locally free modules form an affine bundle; algebra homomorphisms are a closed subscheme cut out by preservation of multiplication and unit. When source and target have the same rank, isomorphisms form the open locus where the determinant is invertible; unequal rank strata contribute nothing. Weil restriction converts the corresponding conditions over a finite locally free cover into conditions over the original base. These constructions provide the finite-dimensional parameter spaces that later moduli arguments repeatedly use.

## 22. The stability theorem

### 22.1 Statement with exact hypotheses

We can now collect the principal structural result.

**Theorem 22.1 (stability of finite flat morphisms of constant rank).** Let $f:X\to S$ be finite and flat, and suppose its fiber-length function is locally constant. Then $f$ is finite locally free. In particular, if every fiber has length $n$, it is finite locally free of constant degree $n$. The following operations preserve finite local freeness, with the indicated rank laws:

1. arbitrary base change preserves rank by pullback;
2. composition preserves finite local freeness, and multiplies degrees when the first morphism has constant degree over the relevant part of the intermediate scheme;
3. fiber product over $S$ multiplies ranks pointwise;
4. finite disjoint union adds ranks pointwise;
5. restriction to an open or clopen subscheme of the base restricts the rank function;
6. dual, tensor, internal Hom, symmetric power, exterior power, and determinant preserve finite local freeness with their usual rank formulas;
7. faithfully flat descent recovers finite local freeness and constant degree;
8. a quotient or closed subscheme does so when its quotient module is flat with locally constant finite rank, equivalently finite projective;
9. over a DVR or Dedekind domain, schematic closure of a generic closed subscheme in a finite locally free ambient scheme is finite locally free;
10. Weil restriction along a finite locally free map preserves affine representability and commutes with arbitrary base change.

Items 8 and 9 state their extra hypotheses explicitly. Quotients and closures are not unconditional operations in the finite locally free category over arbitrary bases.

### 22.2 Proof by reduction to finite projective algebra

The proof is the accumulated dictionary. On $S=\operatorname{Spec}A$, finiteness writes $X=\operatorname{Spec}B$ with $B$ a finite $A$-module. Flatness and local constancy of fiber rank make $B$ finite projective by Theorem 16.1. This proves the first assertion.

Base change sends $B$ to $B\otimes_AA'$. Composition regards a finite projective $C$ over $B$ as a finite projective $A$-module, locally with the product basis. Fiber product sends $(B,C)$ to $B\otimes_AC$. Disjoint union sends them to $B\times C$, which is $B\oplus C$ as a module. Every assertion follows locally from the corresponding operation on finite free modules and then glues because projectivity and rank are local.

Tensor constructions use dual bases. Descent uses faithful exactness together with descent of finite presentation and flatness. Quotients use the projectivity criteria of Chapter 18. Closure over a one-dimensional regular base uses saturation to eliminate torsion. Weil restriction uses the finite dual $B^\vee$ to turn $B$-valued coordinates into finitely many scalar equations. The same finite-projective mechanism is therefore responsible for every item.

### 22.3 Operations that require an extra hypothesis

Several tempting extensions are false.

* An arbitrary closed subscheme of a finite locally free scheme is finite but may not be flat.
* The image of a morphism between finite locally free schemes is finite but may not be locally free.
* The kernel or cokernel of a map of finite projective modules need not be projective.
* A finite flat morphism over an arbitrary ring need not be finitely presented unless its rank is locally constant or another finiteness hypothesis is supplied.
* Schematic closure in a finite locally free ambient scheme need not be flat over an arbitrary integral base.
* Weil restriction of an arbitrary nonaffine scheme need not be representable by a scheme without a hypothesis such as quasi-projectivity.
* Constancy of the number of geometric points does not imply flatness or constant length.

These are not peripheral exceptions. Each marks a place where an exactness, finite-presentation, or affine-neighborhood argument is needed. The stability theorem is powerful because its hypotheses are stable and checkable, not because every finite construction automatically stays flat.

### 22.4 Consequences for finite-flat families

Once a family is known finite locally free, every fiber has a well-defined length equal to the rank at its base point, and this length survives arbitrary scalar extension. Trace, norm, determinant, characteristic polynomial, and duality specialize exactly. Positive rank gives a faithfully flat cover. Étaleness is detected by the vanishing of differentials, reduced geometric fibers, or perfectness of the trace pairing. Over a DVR, generic closed data acquire finite locally free closures after saturation.

These consequences give a robust workflow for later finite-flat group schemes. One first proves that the coordinate algebra is finite and flat and that its rank is constant. All products needed for laws remain finite locally free; all identities may be checked after a faithfully flat cover; duals and determinants commute with base change; closed subgroup candidates require a flat quotient; and generic subgroup schemes over a DVR may be closed schematically without losing finite local freeness. The underlying geometry may develop nilpotents or collide in special fibers, but its degree and linear-algebraic invariants remain controlled.

## 23. The finite locally free dictionary

### 23.1 The four affine translations

We now collect the theory into a form that can be used without reopening every definition. Let $A\to B$ be a ring map and let

$$
f\colon X=\operatorname{Spec}B\longrightarrow S=\operatorname{Spec}A.
$$

There are four progressively stronger levels.

1. The map $f$ is affine exactly because it is presented as the spectrum of an algebra.
2. It is finite exactly when $B$ is finite as an $A$-module. Equivalently, $A\to B$ is integral and of finite type.
3. It is finite and flat exactly when $B$ is finite and flat. Over arbitrary $A$, this need not yet mean finite locally free.
4. It is finite locally free exactly when $B$ is finite projective, equivalently finitely presented and flat, as an $A$-module.

If $A$ is noetherian, level 3 equals level 4 because every finite module is finitely presented. If $A$ is local, a finite flat $A$-module is free by Theorem 9.2, so level 3 again equals level 4. If $A$ is a DVR, level 3 is also equivalent to $B$ being torsion-free as an $A$-module. Without such hypotheses, the finite-presentation clause must remain visible.

### 23.2 What rank $n$ guarantees

Suppose $B$ is finite projective of constant rank $n$. Then all of the following hold.

* Every localization $B_{\mathfrak p}$ is free of rank $n$ over $A_{\mathfrak p}$.
* Every fiber $B\otimes_A\kappa(\mathfrak p)$ and every geometric fiber has vector-space dimension, hence scheme length, $n$.
* Every base change $B\otimes_AA'$ is finite projective of rank $n$ over $A'$.
* The dual $B^\vee$, tensor powers, symmetric powers, exterior powers, and endomorphism module have the expected finite projective ranks.
* Multiplication by $b$ has a monic characteristic polynomial of degree $n$, with trace and norm as its first and last coefficients.
* Trace, norm, characteristic polynomial, trace pairing, and discriminant commute with arbitrary base change.

What rank $n$ does **not** guarantee is equally important. It does not say that fibers are reduced, that they contain $n$ points, that residue extensions are separable, that the trace pairing is perfect, or that a section is an open-and-closed component. Dual numbers supply a counterexample to all of these unwarranted conclusions.

### 23.3 The arithmetic of degrees

Whenever the relevant rank functions are constant, degree obeys a compact arithmetic.

$$
\begin{array}{c|c}
\text{geometric operation}&\text{degree}\\
\hline
X\amalg Y&\deg X+\deg Y\\
X\times_SY&\deg X\,\deg Y\\
X\to Y\to S&\deg(X/Y)\deg(Y/S)\\
X\times_SS'\to S'&\deg(X/S)
\end{array}
$$

The composition formula assumes that $X\to Y$ has the stated constant degree on all components relevant over $S$. On disconnected bases, replace every integer by a locally constant rank function and perform the calculation on clopen strata. Addition under disjoint union and multiplication under fiber product remain pointwise valid without connectedness.

A positive rank function makes the morphism faithfully flat and surjective. Rank zero records the empty piece. Hence the image of an arbitrary finite locally free morphism is precisely its positive-rank clopen locus.

### 23.4 The base-change checklist

Given $A\to A'$, no flatness of $A'$ is required for the following statements when the modules shown on the left are finite projective where needed:

$$
\begin{aligned}
(M\otimes_AN)\otimes_AA'&\cong
(M\otimes_AA')\otimes_{A'}(N\otimes_AA'),\\
B^\vee\otimes_AA'&\cong(B\otimes_AA')^\vee,\\
\operatorname{End}_A(B)\otimes_AA'&\cong
\operatorname{End}_{A'}(B\otimes_AA'),\\
\bigwedge^rB\otimes_AA'&\cong
\bigwedge^r(B\otimes_AA').
\end{aligned}
$$

The first line holds for arbitrary modules $M,N$; the other lines use finite projectivity of $B$. These identifications carry multiplication endomorphisms to multiplication endomorphisms. Consequently all determinant-based invariants specialize correctly.

For a general finitely presented module $M$, Hom commutes with **flat** base change, but not necessarily arbitrary base change. For finite projective $M$, arbitrary base change is allowed because $\operatorname{Hom}(M,-)=M^\vee\otimes-$. Remembering which reason applies prevents an invalid exchange of Hom and fibers.

### 23.5 The locality and descent checklist

Finite projectivity may be verified in any of the following ways.

* Exhibit $B$ as a direct summand of a finite free $A$-module.
* Produce a finite dual basis.
* Prove $B$ finitely presented and flat.
* Find a finite principal-open cover on which $B$ is finite free.
* Make a faithfully flat base change $A\to A'$ and prove $B\otimes_AA'$ finite projective.

The last method is recognition, not construction. If only an algebra $B'$ over $A'$ is given, descending it requires an isomorphism between its two pullbacks to $A'\otimes_AA'$ satisfying the cocycle identity over $A'\otimes_AA'\otimes_AA'$. If $B$ is already given downstairs, no such extra datum is needed to descend the property.

Finite generation, finite presentation, and flatness each descend faithfully flatly, as proved in Chapter 11. Constant rank descends because residue-field extension preserves dimension. Conversely, all of these properties are preserved by arbitrary base change once finite projectivity is known.

### 23.6 Local and DVR diagnostics

Over a local ring $(A,\mathfrak m)$, a finite projective or finite flat module is free. To determine its rank, compute

$$
\dim_{A/\mathfrak m}M/\mathfrak mM.
$$

Minimal lifts of a residue basis form a basis. This turns questions about finite locally free algebras near a point into ordinary finite free linear algebra.

Over a DVR $R$ with fraction field $K$, residue field $k$, and uniformizer $\pi$, a finite $R$-module $M$ is flat exactly when it has no $R$-torsion, exactly when multiplication by $\pi$ is injective. In that case it is free and

$$
\operatorname{rk}_RM
=\dim_K(M\otimes_RK)
=\dim_k(M/\pi M).
$$

For a finite $R$-algebra, one can therefore diagnose flatness by checking injection into the generic fiber. Equality of generic and special fiber lengths follows. If these lengths differ, the difference is witnessed by torsion; if the special fiber is nonreduced but the lengths agree, flatness may still hold.

### 23.7 Trace and norm in reusable form

For a finite projective $A$-algebra $B$ of constant rank $n$, multiplication supplies

$$
B\longrightarrow\operatorname{End}_A(B),
\qquad b\longmapsto m_b.
$$

Then

$$
\operatorname{Tr}_{B/A}(b)=\operatorname{tr}(m_b),
\qquad
\operatorname{Nm}_{B/A}(b)=\det(m_b),
\qquad
\chi_b(T)=\det(T-m_b).
$$

Trace is linear, norm is multiplicative, and $b$ is a unit precisely when its norm is. In a tower $A\to B\to C$, both trace and norm are transitive under the finite locally free hypotheses. On scalar elements, trace multiplies by $n$ and norm raises to the $n$th power.

The trace pairing $B\to B^\vee$ is always defined and base-change compatible, but need not be perfect. Its determinant is the discriminant, naturally valued in a square of the determinant line. A chosen basis turns it into the familiar determinant $\det(\operatorname{Tr}(e_ie_j))$, with change of basis multiplying by a square.

### 23.8 Common invalid shortcuts

The theory is robust largely because it identifies the shortcuts that are unsafe.

**Finite is not finitely presented over every ring.** The quotient $A/I$ is finite for every ideal $I$, but is finitely presented only when $I$ is finitely generated.

**Finite flat is not automatically finite locally free over every ring.** Add finite presentation, or assume a condition such as noetherianity that supplies it. The product-ring example of §8.2 is a concrete obstruction.

**Constant rank changes the preceding conclusion.** A finite flat module whose fiber rank is locally constant is finite projective by Theorem 16.1. On a connected base, a specified constant degree therefore supplies the missing finite-presentation consequence.

**Fiber dimension does not detect infinitesimal nonflatness.** Over a one-point nonreduced base, the dimensions are vacuously constant while torsion can remain. Use flatness, projectivity, or a valid local criterion.

**Torsion-free is not projective over every domain.** The equivalence with finite freeness is special to PIDs and hence to DVRs in the local setting.

**Degree is not globally one integer on a disconnected base.** Use the locally constant rank function or decompose the base into clopen rank strata.

**A section is not necessarily a component.** It is closed for a finite morphism, but it is open only when the corresponding augmentation ideal is generated by an idempotent.

**Finite flat does not mean reduced or separable.** It preserves fiber length; it allows nilpotent fibers and inseparable residue phenomena.

### 23.9 Final synthesis

Finite locally free geometry is finite-dimensional linear algebra allowed to vary over a scheme. Its apparent complexity comes from three kinds of variation: bases need not be connected, specialization need not preserve point sets, and rings need not be noetherian. Rank functions, scheme-theoretic fiber length, and explicit finite-presentation hypotheses resolve these three difficulties.

Once the coordinate algebra is finite projective, the whole structure becomes predictable. Localization produces genuine bases. Arbitrary base change preserves the object and all of its linear invariants. Composition preserves the class and multiplies degrees under the stated constant-rank hypothesis; fiber products multiply ranks and disjoint unions add them. Local rings turn finite flat modules into free modules, and DVRs turn flatness into torsion-freeness. Faithfully flat extensions detect the structure. Duals, traces, norms, characteristic polynomials, and discriminants then follow from one regular representation and remain compatible with every fiber.

The unramified boundary is now equally precise: differentials, reduced geometric fibers, and the trace pairing all detect when a finite locally free family is étale. Quotients remain in the category exactly when the requisite projectivity survives. Saturation produces the correct schematic closure and, over DVRs and Dedekind domains, preserves finite local freeness. Weil restriction converts objects and section problems over a finite locally free cover into finite-dimensional geometry over the original base, while effective descent carries their compatible structures back down.

The result is more than a collection of equivalences. It is a stable language for zero-dimensional families: geometry can change from separated points to collided or nonreduced fibers, while rank and determinant data continue to make exact sense. That stability is precisely what makes finite locally free schemes suitable as the underlying spaces of finite group schemes, as integral closures of generic subgroup data, and as finite parameter objects in moduli theory.
