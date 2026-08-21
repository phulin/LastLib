# Formal Schemes, GAGA, and Algebraization

## Contents

1. [Geometry seen through infinitesimal neighborhoods](#1-geometry-seen-through-infinitesimal-neighborhoods)
   - [The completion problem](#11-the-completion-problem)
   - [Three geometries that must remain distinct](#12-three-geometries-that-must-remain-distinct)
   - [Standing conventions](#13-standing-conventions)
2. [Adic rings and restricted power series](#2-adic-rings-and-restricted-power-series)
   - [Linear and adic topologies](#21-linear-and-adic-topologies)
   - [Completion and change of ideal](#22-completion-and-change-of-ideal)
   - [Restricted power series](#23-restricted-power-series)
   - [Continuous substitution and examples](#24-continuous-substitution-and-examples)
3. [Affine formal spectra](#3-affine-formal-spectra)
   - [The points of a formal spectrum](#31-the-points-of-a-formal-spectrum)
   - [Completed localization and the structure sheaf](#32-completed-localization-and-the-structure-sheaf)
   - [Affine sheaves from complete modules](#33-affine-sheaves-from-complete-modules)
   - [Continuous maps and affine morphisms](#34-continuous-maps-and-affine-morphisms)
4. [Formal schemes and their morphisms](#4-formal-schemes-and-their-morphisms)
   - [Gluing affine formal spectra](#41-gluing-affine-formal-spectra)
   - [Ideals of definition and thickenings](#42-ideals-of-definition-and-thickenings)
   - [Adic, finite-type, separated, and proper morphisms](#43-adic-finite-type-separated-and-proper-morphisms)
   - [Fiber products and base change](#44-fiber-products-and-base-change)
5. [Completion along a closed subscheme](#5-completion-along-a-closed-subscheme)
   - [From a pair to a formal scheme](#51-from-a-pair-to-a-formal-scheme)
   - [The universal property](#52-the-universal-property)
   - [Exactness, closed immersions, and base change](#53-exactness-closed-immersions-and-base-change)
   - [Examples and boundaries](#54-examples-and-boundaries)
6. [Formal fibers and what they measure](#6-formal-fibers-and-what-they-measure)
   - [Two related meanings](#61-two-related-meanings)
   - [Fibers of completion maps](#62-fibers-of-completion-maps)
   - [Geometric information and counterexamples](#63-geometric-information-and-counterexamples)
7. [Coherent modules on noetherian formal schemes](#7-coherent-modules-on-noetherian-formal-schemes)
   - [Finite modules with complete topology](#71-finite-modules-with-complete-topology)
   - [The finite-level equivalence](#72-the-finite-level-equivalence)
   - [Exactness, tensor products, and internal Hom](#73-exactness-tensor-products-and-internal-hom)
   - [Support, flatness, and locally free objects](#74-support-flatness-and-locally-free-objects)
8. [Proper formal geometry and formal functions](#8-proper-formal-geometry-and-formal-functions)
   - [Properness through all thickenings](#81-properness-through-all-thickenings)
   - [Cohomology as an inverse limit](#82-cohomology-as-an-inverse-limit)
   - [The formal-functions interface](#83-the-formal-functions-interface)
   - [Consequences and failure without properness](#84-consequences-and-failure-without-properness)
9. [Grothendieck existence for coherent sheaves](#9-grothendieck-existence-for-coherent-sheaves)
   - [The effectivity question](#91-the-effectivity-question)
   - [Full faithfulness](#92-full-faithfulness)
   - [Difference sheaves, uniform vanishing, and formal Serre vanishing](#93-difference-sheaves-uniform-vanishing-and-formal-serre-vanishing)
   - [Finiteness of formal sections and essential surjectivity](#94-finiteness-of-formal-sections-and-essential-surjectivity)
   - [Passage from projective to proper](#95-passage-from-projective-to-proper)
   - [What the theorem does and does not say](#96-what-the-theorem-does-and-does-not-say)
10. [Algebraizing proper formal schemes](#10-algebraizing-proper-formal-schemes)
    - [Why coherent existence is not enough](#101-why-coherent-existence-is-not-enough)
    - [The ample-line criterion](#102-the-ample-line-criterion)
    - [Construction by sections and Proj](#103-construction-by-sections-and-proj)
    - [Uniqueness and algebraization of morphisms](#104-uniqueness-and-algebraization-of-morphisms)
    - [Properties recovered after algebraization](#105-properties-recovered-after-algebraization)
11. [Complex analytification](#11-complex-analytification)
    - [From algebraic varieties to analytic spaces](#111-from-algebraic-varieties-to-analytic-spaces)
    - [Analytification of coherent sheaves](#112-analytification-of-coherent-sheaves)
    - [Properness and comparison maps](#113-properness-and-comparison-maps)
12. [GAGA for cohomology and coherent sheaves](#12-gaga-for-cohomology-and-coherent-sheaves)
    - [The projective comparison](#121-the-projective-comparison)
    - [The proper comparison theorem](#122-the-proper-comparison-theorem)
    - [Full faithfulness and essential surjectivity](#123-full-faithfulness-and-essential-surjectivity)
    - [Closed subspaces and morphisms](#124-closed-subspaces-and-morphisms)
    - [Sharp boundaries](#125-sharp-boundaries)
13. [Completion and analytification compared](#13-completion-and-analytification-compared)
    - [Two comparison squares](#131-two-comparison-squares)
    - [Formal neighborhoods versus analytic neighborhoods](#132-formal-neighborhoods-versus-analytic-neighborhoods)
    - [Why no generic fiber appears here](#133-why-no-generic-fiber-appears-here)
14. [Algebraizing formal curves](#14-algebraizing-formal-curves)
    - [The curve criterion](#141-the-curve-criterion)
    - [Lifting an ample line bundle](#142-lifting-an-ample-line-bundle)
    - [Flat, smooth, and stable curves](#143-flat-smooth-and-stable-curves)
    - [Uniqueness and marked structures](#144-uniqueness-and-marked-structures)
15. [Algebraizing formal abelian varieties](#15-algebraizing-formal-abelian-varieties)
    - [Polarization supplies effectivity](#151-polarization-supplies-effectivity)
    - [Recovering the group law](#152-recovering-the-group-law)
    - [Smoothness, duality, and uniqueness](#153-smoothness-duality-and-uniqueness)
    - [The unpolarized boundary](#154-the-unpolarized-boundary)
16. [Synthesis](#16-synthesis)
    - [The four passage principles](#161-the-four-passage-principles)
    - [A hypothesis ledger](#162-a-hypothesis-ledger)
    - [Conclusion](#163-conclusion)

## 1. Geometry seen through infinitesimal neighborhoods

### 1.1 The completion problem

Let $X$ be a scheme and $Y\hookrightarrow X$ a closed subscheme with ideal sheaf $\mathcal I$. The successive closed subschemes

$$
X_n=(Y,\mathcal O_X/\mathcal I^{n+1}),\qquad n\geq 0,
$$

retain more than the reduced locus $|Y|$. The first layer records normal directions, the second records quadratic contact, and the entire tower records every finite order of contact with $Y$. Completion asks whether the compatible tower itself can be treated as a geometric object. Algebraization asks the reverse question: when did such an infinitesimal object come from an ordinary scheme?

These questions arise whenever a construction is performed one nilpotent order at a time. A line bundle may be lifted from $X_n$ to $X_{n+1}$; a morphism may be determined modulo every power of an ideal; a proper family over a complete local base may be visible only through its reductions. Merely writing an inverse limit is not enough. One needs a topology on rings, local models whose functions are completed localizations, a coherent sheaf theory compatible with limits, and an effectivity theorem strong enough to reconstruct algebraic objects.

The decisive tension is this. Completeness gives uniqueness because two finite objects agreeing at every infinitesimal order must agree. Existence is harder: compatible finite-order data can fail to arise from a finite algebraic object. Properness controls cohomology, while ampleness supplies enough sections to build a global projective model. Those two ideas govern the book.

### 1.2 Three geometries that must remain distinct

Three constructions are often placed side by side, but they answer different questions.

The formal completion $\widehat X_Y$ has underlying topological space $|Y|$ and remembers nilpotent neighborhoods inside $X$. It has no new points away from $Y$. Complex analytification $X^{\mathrm{an}}$ has complex points with their Euclidean analytic topology and holomorphic functions. A nonarchimedean generic fiber, when defined from a formal model over a valued base, discards the special fiber as a set and produces an analytic space over the fraction field. It is not the formal scheme itself.

For example, with a complete discrete valuation ring $R$, uniformizer $\pi$, and $X=\operatorname{Spec}R[t]$, the $\pi$-adic completion has affine ring $R\langle t\rangle$, not $R[[t]]$. It remembers the entire special affine line and its infinitesimal thickening. By contrast, completion along the closed point $(\pi,t)$ has ring $R[[t]]$ and underlying space one point. A later nonarchimedean generic-fiber construction would turn the first object into a closed unit disc, but no such operation is part of the definition of either completion.

This separation prevents two tempting mistakes. Formal functions are not convergent analytic functions. Conversely, holomorphic functions near a complex subspace need not be determined by arbitrary formal coefficients unless a comparison or convergence theorem is proved.

### 1.3 Standing conventions

All rings are commutative with identity. A noetherian adic ring will mean a noetherian ring $A$, complete and separated for the powers of an ideal $I$. Such an $I$ is called an ideal of definition. Replacing $I$ by another ideal with cofinal powers does not change the topology or the associated formal spectrum.

Most structural theorems are stated in the noetherian setting. This is not cosmetic. It makes ideals of definition finitely generated, invokes Artin--Rees, makes finite modules complete, and ensures that coherent objects can be reconstructed from their quotients. When a definition makes sense more generally, that will be said without silently extending the theorems.

For an ideal $I\subset A$, set

$$
A_n=A/I^{n+1}.
$$

Indexing from $n=0$ makes the special fiber $A_0=A/I$. For a formal scheme $\mathfrak X$ with ideal of definition $\mathcal J$, write

$$
X_n=(|\mathfrak X|,\mathcal O_{\mathfrak X}/\mathcal J^{n+1}).
$$

Book 8 supplies relative Proj, ampleness, and projective embeddings. Book 15 supplies proper coherent cohomology and the theorem on formal functions. Book 57 supplies the algebra of separated complete rings and finite modules. We recall the interfaces precisely when they are used.

## 2. Adic rings and restricted power series

### 2.1 Linear and adic topologies

A topology on a ring is useful for infinitesimal geometry only when addition and multiplication respect a basis of ideals. A **linearly topologized ring** is a topological ring for which open ideals form a neighborhood basis of zero. It is **adic** if there is a finitely generated ideal $I$ whose powers $I^n$ form such a basis. In a noetherian ring finite generation is automatic, so the essential assertion is that the topology is the $I$-adic topology.

Separatedness means

$$
\bigcap_{n\geq 0}I^n=0,
$$

and completeness means that the canonical map

$$
A\longrightarrow\varprojlim_n A/I^{n+1}
$$

is an isomorphism. The kernel measures failure of separatedness; the cokernel measures compatible residue classes with no limit in $A$. Thus the familiar sequence of finite shadows determines the ring exactly only under both conditions.

An open ideal $J$ is an **ideal of definition** if its powers form a neighborhood basis of zero. If $I$ is one ideal of definition, then $J$ is another precisely when the two power filtrations are cofinal: for some $r,s>0$,

$$
I^r\subseteq J,\qquad J^s\subseteq I.
$$

Consequently the radical $\sqrt I$ is a topological invariant, while $I$ itself is not. The rings $k[[x,y]]$ with the $(x,y)$-adic topology, the $(x^2,xy,y^3)$-adic topology, and the $(x,y)^5$-adic topology define the same adic geometry.

An arbitrary ideal in a complete ring need not define the given topology. In $k[[x,y]]$ with its $(x,y)$-adic topology, the ideal $(x)$ is not open: no power of $(x,y)$ lies in $(x)$. Completing again along $(x)$ is a new operation, not a harmless change of notation.

### 2.2 Completion and change of ideal

For an $A$-module $M$, its $I$-adic completion is

$$
\widehat M=\varprojlim_n M/I^{n+1}M.
$$

If $A$ is noetherian and $M$ is finite, Artin--Rees proves three indispensable facts: submodules of $M$ are closed, completion is exact on short exact sequences of finite modules, and

$$
\widehat M\simeq M\otimes_A\widehat A.
$$

In particular, if $A$ is already complete, every finite $A$-module is complete and separated. This conclusion fails for infinitely generated modules. Completion can cease to be exact, and the natural map from a submodule completion to the ambient completion can acquire a kernel.

If $A\to B$ is continuous between adic rings, continuity says that the inverse image of every open ideal of $B$ is open in $A$. For ideals of definition $I\subset A$ and $J\subset B$, this is equivalent to the existence, for every $n$, of an $m$ with

$$
I^mB\subseteq J^n.
$$

The map is **adic** when $IB$ itself is an ideal of definition of $B$. Adic implies continuous, but the converse need not hold. For instance, the inclusion

$$
k[[t]]\longrightarrow k[[t,u]],
$$

with the $(t)$-adic topology on the source and the $(t,u)$-adic topology on the target, is continuous: $t^n$ lands in $(t,u)^n$. It is not adic, because $(t)$ is not an ideal of definition of the target; no power of $(t,u)$ lies inside $(t)$. Since $(t^n)\subsetneq(t,u)^n$, the $(t)$-adic topology induced on the target ring is strictly finer than its chosen $(t,u)$-adic topology.

Completed tensor products express base change. If $A\to B$ and $A\to C$ are compatible continuous maps and the indicated adic topologies are noetherian, then

$$
B\widehat\otimes_A C
=\varprojlim_n (B\otimes_A C)/K_n,
$$

where one may take a cofinal family generated by suitable powers of the defining ideals. The topology must be specified: without it, the notation does not determine a ring.

### 2.3 Restricted power series

Polynomial coordinates are not complete, while unrestricted formal power series are often too large. Let $A$ be complete and separated for $I$. The restricted power-series ring in $r$ variables is

$$
A\langle T_1,\ldots,T_r\rangle
=\varprojlim_n (A/I^{n+1})[T_1,\ldots,T_r].
$$

An element has a unique expansion

$$
f=\sum_{\nu\in\mathbf N^r}a_\nu T^\nu
$$

such that, for every $n$, all but finitely many coefficients lie in $I^n$. Equivalently, $a_\nu\to0$ in the cofinite sense. Modulo $I^{n+1}$ only finitely many terms remain, so multiplication is defined by the ordinary finite convolution at every level and then by passage to the limit.

This coefficient condition explains the word restricted. The series

$$
\sum_{m\geq0}\pi^mT^m
$$

belongs to $R\langle T\rangle$ for a $\pi$-adically complete ring $R$, whereas $\sum_{m\geq0}T^m$ does not. The latter belongs to $R[[T]]$. Thus

$$
R[T]\subset R\langle T\rangle\subset R[[T]],
$$

and both inclusions are usually strict.

There is another instructive limiting case. If $A$ is discrete, so that zero is an ideal of definition, convergence of coefficients to zero means that only finitely many coefficients are nonzero. Hence $A\langle T_1,\ldots,T_r\rangle=A[T_1,\ldots,T_r]$. Restricted series interpolate between polynomial and formal series according to the topology on the coefficients.

If $A$ is noetherian and $I$-adically complete, then $A\langle\mathbf T\rangle$ is again noetherian, $I$-adically complete, and separated. Completeness is built into the inverse limit. For noetherianity, the $I$-adic associated graded ring is

$$
\operatorname{gr}_I(A\langle\mathbf T\rangle)
\simeq (\operatorname{gr}_I A)[\mathbf T].
$$

The ring $\operatorname{gr}_I A$ is a finite-type algebra over $A/I$, because $I$ is finitely generated, and is noetherian. The polynomial ring on the right is therefore noetherian. Given an ideal of $A\langle\mathbf T\rangle$, choose finitely many elements whose initial forms generate its graded initial ideal. Successively subtract their multiples to raise the $I$-adic order of any element of the ideal; completeness takes the corrections to a convergent finite-generator expression. Hence the original ideal is finitely generated. This is the topological Hilbert-basis argument used below.

### 2.4 Continuous substitution and examples

The defining inverse limit gives the correct universal property. Let $B$ be a complete separated adic $A$-algebra, with continuous structure map. Given $b_1,\ldots,b_r\in B$, the rule

$$
\sum a_\nu T^\nu\longmapsto\sum a_\nu b^\nu
$$

defines a continuous $A$-homomorphism $A\langle T_1,\ldots,T_r\rangle\to B$. Modulo each open ideal of $B$, only finitely many coefficients contribute. Conversely, a continuous $A$-homomorphism is determined by the images of the variables. This is the topological analogue of the universal property of a polynomial ring.

For $A=R$ complete along $(\pi)$,

$$
R\langle x_1,\ldots,x_r\rangle/(f_1,\ldots,f_s)
$$

is the typical affine algebra topologically of finite presentation over $R$. The quotient is already complete because ideals in a noetherian complete ring are closed. If noetherianity is removed, one must complete the quotient and cannot assume the algebraic quotient is separated.

By contrast, $R[[x]]$ is naturally complete for $(\pi,x)$, not topologically of finite type for the $\pi$-adic topology in the restricted sense. Geometrically, $R\langle x\rangle$ retains a whole affine line on the special fiber, while $R[[x]]$ has a one-point special fiber when $(\pi,x)$ is the chosen ideal of definition.

## 3. Affine formal spectra

### 3.1 The points of a formal spectrum

Let $A$ be an adic ring with ideal of definition $I$. Its affine formal spectrum is denoted

$$
\operatorname{Spf}A.
$$

As a topological space it is the set of open prime ideals of $A$. A prime $\mathfrak p$ is open exactly when it contains $I$, so

$$
|\operatorname{Spf}A|=V(I)=|\operatorname{Spec}(A/I)|.
$$

Changing the ideal of definition does not change this set because it does not change $\sqrt I$. The formal spectrum therefore exposes only the special locus, but its sheaf remembers every quotient $A/I^{n+1}$.

The distinction from ordinary spectrum is immediate. For $A=R$ a complete discrete valuation ring, $\operatorname{Spec}R$ has a generic and a closed point, while $\operatorname{Spf}R$ has only the closed point. The missing generic point has not been replaced by an analytic point; it is simply absent.

For $A=R\langle t\rangle$ with the $\pi$-adic topology, $\operatorname{Spf}A$ has underlying space $\operatorname{Spec}k[t]$. For $A=R[[t]]$ with ideal $(\pi,t)$, the underlying space is $\operatorname{Spec}k$, although the completed local ring contains the entire transverse parameter $t$.

### 3.2 Completed localization and the structure sheaf

Ordinary localization is not complete in general, so it cannot directly provide functions on formal open subsets. If $f\in A$ and $D(\bar f)\subseteq\operatorname{Spec}(A/I)$ is the corresponding principal open, define

$$
A_{\{f\}}=\varprojlim_n (A/I^{n+1})_{\bar f}.
$$

Equivalently, this is the completion of $A_f$ for the ideal $IA_f$ in the noetherian case. Set

$$
\mathcal O_{\operatorname{Spf}A}(D(\bar f))=A_{\{f\}}.
$$

The usual localization identities hold level by level. They therefore hold after inverse limits, and the resulting presheaf on principal opens is a sheaf. Its stalk at an open prime $\mathfrak p$ is the filtered colimit of these completed localizations; it is a local ring. Thus $(\operatorname{Spf}A,\mathcal O)$ is a locally ringed space.

There is a useful limit description:

$$
\operatorname{Spf}A=\varinjlim_n\operatorname{Spec}(A/I^{n+1})
$$

in the sense of locally ringed spaces with a fixed underlying topological space and inverse-limit structure sheaf. The arrow is mnemonic: the closed immersions of schemes go from level $n$ to $n+1$, while functions form an inverse system.

If $A$ is noetherian and complete, global sections recover $A$. Without appropriate hypotheses, sheafification and inverse limit can behave poorly; this is one reason the noetherian theory is the reliable setting for coherent geometry.

### 3.3 Affine sheaves from complete modules

Let $M$ be a finite $A$-module. On a principal open define

$$
M_{\{f\}}=\varprojlim_n(M/I^{n+1}M)_f.
$$

These modules form a sheaf $M^\triangle$ on $\operatorname{Spf}A$. Exactness of completion for finite modules shows that $M\mapsto M^\triangle$ is exact. Moreover

$$
\Gamma(\operatorname{Spf}A,M^\triangle)=M,
$$

and finite submodules, quotients, tensor products followed by completion, and finite presentations sheafify as expected.

The completion clause matters for tensor products. If $M$ and $N$ are finite over noetherian complete $A$, then $M\otimes_AN$ is finite and already complete, so

$$
M^\triangle\otimes_{\mathcal O}N^\triangle\simeq(M\otimes_AN)^\triangle.
$$

For nonfinite modules the ordinary tensor product can be incomplete; the correct topological object is then a completed tensor product.

An affine formal scheme is not recovered merely from the ordinary scheme $\operatorname{Spec}(A/I)$. The rings $k[[t]]/(t^2)$ and $k[[t]]$ have the same underlying one-point reduced space, but different infinitesimal sheaves. The tower, not just the special fiber, is the object.

### 3.4 Continuous maps and affine morphisms

A continuous homomorphism $\varphi:A\to B$ of adic rings induces

$$
\operatorname{Spf}B\longrightarrow\operatorname{Spf}A.
$$

On points it sends an open prime $\mathfrak q$ to $\varphi^{-1}(\mathfrak q)$; continuity ensures this prime is open. On principal opens the sheaf map comes from completed localization. Conversely, every morphism of affine formal spectra arises uniquely from a continuous homomorphism in the opposite direction.

One must retain the word continuous. An abstract ring map can fail to respect infinitesimal convergence and hence fail to induce a formal morphism. If both rings are noetherian adic and the map is adic and topologically of finite type, it is locally presented as a quotient of a restricted power-series ring.

At finite level an adic map $A\to B$ with $I\subset A$ produces compatible maps

$$
\operatorname{Spec}(B/I^{n+1}B)\longrightarrow\operatorname{Spec}(A/I^{n+1}).
$$

A merely continuous map may require replacing the same index $n$ on the source by a larger index on the target. This difference is why adic morphisms have especially direct reduction theory.

## 4. Formal schemes and their morphisms

### 4.1 Gluing affine formal spectra

A **formal scheme** is a locally ringed space locally isomorphic to $\operatorname{Spf}A$ for adic rings $A$. In this book, a **locally noetherian formal scheme** is locally modeled on noetherian adic rings, and a **noetherian formal scheme** is additionally quasi-compact.

Gluing works because intersections of affine opens can be covered by principal formal opens and completed localization satisfies the cocycle identities. As with schemes, the local rings encode infinitesimal functions and the underlying topological space encodes points. Unlike schemes, even an affine chart comes with a chosen topology, though the particular ideal presenting that topology is not part of the final object.

Examples include an ordinary scheme viewed with the discrete topology; $\operatorname{Spf}A$ for a complete local ring; and the completion of a noetherian scheme along a closed subscheme. A scheme with discrete topology is a formal scheme because zero is an ideal of definition. Thus formal schemes enlarge ordinary schemes rather than forming a disjoint category.

### 4.2 Ideals of definition and thickenings

An ideal of definition on $\mathfrak X$ is a coherent open ideal sheaf $\mathcal J\subset\mathcal O_{\mathfrak X}$ whose powers form a neighborhood basis of zero locally. It gives ordinary schemes

$$
X_n=(|\mathfrak X|,\mathcal O_{\mathfrak X}/\mathcal J^{n+1}).
$$

The maps $X_n\hookrightarrow X_{n+1}$ are nilpotent closed immersions and all $X_n$ have the same underlying topological space. Locally, they are $\operatorname{Spec}(A/I^{n+1})$.

Different ideals of definition yield cofinal systems and hence the same formal scheme. Statements formulated at a single index can depend on the choice, whereas statements stable under passage to a cofinal subsystem do not. For instance, “$X_0$ is reduced” depends on $\mathcal J$, but the reduced closed subscheme supported on $|\mathfrak X|$ does not.

The structure sheaf satisfies

$$
\mathcal O_{\mathfrak X}\simeq\varprojlim_n\mathcal O_{X_n}.
$$

This identity is local and exact enough for coherent calculations because of noetherianity. It should not be read as saying every inverse system of schemes with the same support is a formal scheme; the transition ideals must reproduce powers of an ideal of definition locally.

### 4.3 Adic, finite-type, separated, and proper morphisms

Let $f:\mathfrak X\to\mathfrak S$ be a morphism of locally noetherian formal schemes. It is **adic** if, for an ideal of definition $\mathcal K$ on $\mathfrak S$, the ideal $\mathcal K\mathcal O_{\mathfrak X}$ is an ideal of definition on $\mathfrak X$. This is independent of the chosen $\mathcal K$.

An adic morphism is **of finite type** if locally it comes from a continuous map $A\to B$ for which $B/J$ is a finite-type $A/I$-algebra, equivalently in the noetherian setting $B$ is a quotient of some $A\langle T_1,\ldots,T_r\rangle$. It is **of finite presentation** when the kernel can be taken finitely generated. Here the restricted power-series ring is noetherian, so its kernel is finitely generated and the two notions coincide for these noetherian adic morphisms.

Separatedness is defined by requiring the diagonal

$$
\Delta_f:\mathfrak X\longrightarrow\mathfrak X\times_{\mathfrak S}\mathfrak X
$$

to be a closed immersion. For an adic finite-type morphism, this is equivalent to separatedness of every sufficiently compatible reduction $X_n\to S_n$, and it is enough to test the special reduction.

A morphism is **proper** here when it is adic, separated, of finite type, and its reductions $X_n\to S_n$ are proper. For noetherian adic morphisms, properness of $X_0\to S_0$ already implies properness of every thickening, because nilpotent closed thickenings do not change universal closedness and preserve finite type and separatedness. Thus properness is visible at level zero once adicity and finite type have been established.

The adjectives cannot be detached from their hypotheses. A continuous nonadic morphism need not admit reductions indexed by the same powers, so “proper special fiber” alone does not define a proper formal morphism.

### 4.4 Fiber products and base change

Fiber products of locally noetherian formal schemes are constructed affinely by completed tensor products. Given continuous maps $A\to B$ and $A\to C$ with compatible ideals, the affine chart is

$$
\operatorname{Spf}(B\widehat\otimes_A C).
$$

In the adic situation its level-$n$ reduction agrees with the ordinary fiber product of corresponding thickenings after choosing compatible ideals. This finite-level description proves associativity and the universal property.

Adic finite type, separatedness, and properness are stable under base change. Properness follows level by level from the corresponding scheme theorem. This is a recurring proof method: formulate a formal property so that it is stable under cofinal change of ideals, prove it for each nilpotent thickening, then pass back to the formal object.

The product $\operatorname{Spf}R[[x]]\times_{\operatorname{Spf}R}\operatorname{Spf}R[[y]]$ illustrates the topology. With all rings $\pi$-adic, the result uses the $\pi$-adically completed tensor product and resembles $R[[x,y]]$ only after the topologies and presentations are checked. If the source rings carry $(\pi,x)$- and $(\pi,y)$-adic topologies, the resulting ideal of definition contains both variables. An unqualified tensor product would erase this distinction.

## 5. Completion along a closed subscheme

### 5.1 From a pair to a formal scheme

Let $X$ be a locally noetherian scheme and $Y\hookrightarrow X$ a closed subscheme defined by a coherent ideal $\mathcal I$. The **formal completion of $X$ along $Y$** is

$$
\widehat X_Y=(|Y|,\varprojlim_n\mathcal O_X/\mathcal I^{n+1}).
$$

On an affine open $U=\operatorname{Spec}A$ with $I=\Gamma(U,\mathcal I)$, its restriction is

$$
\operatorname{Spf}\widehat A^I,
\qquad
\widehat A^I=\varprojlim_nA/I^{n+1}.
$$

The underlying space depends only on $\sqrt{\mathcal I}$, but the embedding data are carried by every power. Replacing $Y$ by another closed subscheme with an ideal having cofinal powers gives the same completion.

If $X$ is already proper over a base $S$, then $\widehat X_Y$ is proper over the completion of $S$ along any closed locus whose inverse image supports $Y$, provided the ideals are compatible. Properness is inherited from the reductions, not from the bare fact that $|Y|$ is proper.

### 5.2 The universal property

Completion is characterized by the condition that functions vanishing on $Y$ become topologically nilpotent. Let $\mathfrak T$ be a locally noetherian formal scheme and $g:\mathfrak T\to X$ a morphism of locally ringed spaces such that $g^{-1}\mathcal I\cdot\mathcal O_{\mathfrak T}$ is contained in an ideal of definition. Equivalently, every section of $\mathcal I$ pulls back to something tending to zero through the topology of $\mathfrak T$. Then $g$ factors uniquely as

$$
\mathfrak T\longrightarrow\widehat X_Y\longrightarrow X.
$$

Affinely, a map $A\to B$ to a complete adic ring factors through $\widehat A^I$ exactly when the images of $I^n$ tend to zero. Existence follows by sending a compatible sequence modulo $I^{n+1}$ to its limit in $B$; uniqueness follows from separatedness.

Merely asking the underlying map of spaces to land in $|Y|$ is insufficient without continuity. The point condition says each element of $I$ belongs to every relevant prime, while the universal property needs its powers to become small in the target topology.

### 5.3 Exactness, closed immersions, and base change

For a coherent sheaf $\mathcal F$ on $X$, its completion is

$$
\widehat{\mathcal F}=\varprojlim_n\mathcal F/\mathcal I^{n+1}\mathcal F.
$$

On noetherian affine charts this is the sheaf associated with the completed finite module. Artin--Rees makes the operation exact on coherent sheaves. In particular, if $Z\hookrightarrow X$ is a closed subscheme with ideal $\mathcal K$, then its completion along $Z\cap Y$ is a closed formal subscheme of $\widehat X_Y$, defined by the closure of $\mathcal K\mathcal O_{\widehat X_Y}$.

Completion commutes with base change when the fiber product on the formal side is completed. Precisely, let $X'\to X$ be a morphism of locally noetherian schemes, assume $Y'=X'\times_XY$ is defined by the extended ideal, and form the fiber product in locally noetherian formal schemes. Then the natural map

$$
\widehat {X'}_{Y'}\longrightarrow X'\times_X\widehat X_Y.
$$

is an isomorphism. Affinely, for $A\to B$ and $I\subset A$, both sides are

$$
\operatorname{Spf}\!\left(\varprojlim_nB/I^{n+1}B\right),
$$

because the completed tensor product is defined by these quotients. No flatness is needed for this identity. Flatness enters a different assertion, namely comparison of an uncompleted tensor product with completion. Ordinary scheme fiber products must not be substituted for completed formal ones.

### 5.4 Examples and boundaries

Completing $\mathbf A^1_k=\operatorname{Spec}k[t]$ at the origin gives $\operatorname{Spf}k[[t]]$. Completing $\mathbf P^1_k$ at the same point gives the same formal scheme: completion sees only an arbitrarily small algebraic neighborhood. Thus completion is local around the center and cannot remember the distant point at infinity.

Completing $\operatorname{Spec}R[t]$ along the whole special fiber $(\pi)$ gives $\operatorname{Spf}R\langle t\rangle$. Completing it along the origin $(\pi,t)$ gives $\operatorname{Spf}R[[t]]$. These centers have different supports, so their completions should differ.

Finally, completion is not faithful on arbitrary nonproper global geometry. The open curve $\mathbf A^1_k$ and the projective curve $\mathbf P^1_k$ have isomorphic completions at the origin. Proper existence theorems recover coherent objects on a fixed proper scheme; they do not reconstruct an unspecified ambient scheme from one local formal neighborhood.

## 6. Formal fibers and what they measure

### 6.1 Two related meanings

The phrase **formal fiber** is used for two constructions, and clarity requires naming the map. Let $A$ be noetherian and $I\subset A$, and put $\widehat A=\widehat A^I$. The completion map of ordinary schemes

$$
\operatorname{Spec}\widehat A\longrightarrow\operatorname{Spec}A
$$

has, over $\mathfrak p\in\operatorname{Spec}A$, the scheme-theoretic fiber

$$
\operatorname{Spec}(\widehat A\otimes_A\kappa(\mathfrak p)).
$$

This is the **formal fiber of $A$ at $\mathfrak p$**. Despite the name, it is an ordinary affine scheme. It measures the primes and residue extensions created when the ring is completed.

A second usage concerns an adic morphism $f:\mathfrak X\to\mathfrak S$. For $s\in|\mathfrak S|$, one can base change to the complete local formal neighborhood of $s$ and then take either its special fiber or its completion along a chosen fiber. This produces a formal neighborhood of the geometric fiber. It remembers nilpotent normal directions in the family, whereas the ordinary fiber $X_0\times_{S_0}\operatorname{Spec}\kappa(s)$ remembers only level zero.

The two usages are related through affine completion maps, but they are not interchangeable. In what follows, “ring-theoretic formal fiber” means the first and “formal neighborhood of a fiber” means the second.

### 6.2 Fibers of completion maps

Suppose first that $A$ is local with maximal ideal $\mathfrak m$ and is completed $\mathfrak m$-adically. At the closed point,

$$
\widehat A\otimes_A\kappa(\mathfrak m)\simeq\kappa(\mathfrak m),
$$

so the closed formal fiber is one reduced point. At a nonmaximal prime $\mathfrak p$, the fiber may have positive dimension or several points. Completion is faithfully flat for noetherian local $A$, so the fiber is never empty, but flatness does not force it to be geometrically regular or irreducible.

For $A=k[x]_{(x)}$, completion gives $k[[x]]$. There are only two primes. The closed fiber is $k$, while over the generic point

$$
k[[x]]\otimes_{k[x]_{(x)}}k(x)
$$

is the fraction field $k((x))$. The corresponding formal fiber is a point with a larger residue field. In higher dimension, the generic formal fiber can have positive dimension because many primes of $\widehat A$ may contract to zero.

If $I$ is not contained in $\mathfrak p$, then $I$ becomes the unit ideal in $\kappa(\mathfrak p)$. This does not imply that the fiber vanishes: tensor product and inverse limit need not commute in that naive way. The map $A\to\widehat A$ must be studied as an ordinary ring map. This is a useful warning against trying to read all formal fibers directly from the point set of $\operatorname{Spf}\widehat A$, which contains only primes containing $I$.

For a proper morphism $X\to\operatorname{Spec}A$, the formal neighborhood of the closed fiber is the completion $\widehat X$. Its levels are

$$
X_n=X\times_A\operatorname{Spec}(A/I^{n+1}).
$$

Here no mysterious new points appear: every level has the closed-fiber support. What grows is the sheaf of functions and modules normal to that support.

### 6.3 Geometric information and counterexamples

Formal fibers diagnose how local properties behave under completion. If all formal fibers of a noetherian local ring are geometrically regular, the completion map is regular; excellent rings are designed so that this and related finiteness properties behave well. No such regularity is automatic for an arbitrary noetherian ring. A regular-looking completed neighborhood therefore cannot always be descended without an excellence or finite-presentation hypothesis.

Completion can also split branches. A prime of $A$ can have several primes above it in $\widehat A$, and the corresponding formal fiber is disconnected. Conversely, a nonreduced formal fiber can reveal inseparable or nilpotent behavior invisible in the set of points. These phenomena explain why arguments about irreducibility, normality, or smoothness cannot rely on topological spaces alone.

None of these fibers is a nonarchimedean analytic generic fiber. The scheme $\operatorname{Spec}(\widehat A\otimes_A\kappa(\mathfrak p))$ is obtained by ordinary base change along a residue field. A nonarchimedean generic fiber requires a valued base and an analytic construction, has a different point set, and is reserved for the separate theory of rigid analytic spaces.

## 7. Coherent modules on noetherian formal schemes

### 7.1 Finite modules with complete topology

Coherent sheaves are the finite objects for which infinitesimal reconstruction works. On $\mathfrak X=\operatorname{Spf}A$, with $A$ noetherian adic, a coherent $\mathcal O_{\mathfrak X}$-module is locally of the form $M^\triangle$ for a finite $A$-module $M$. The topology on $M$ is the $I$-adic topology, and Artin--Rees makes it independent of the chosen finite presentation.

The canonical map

$$
M\longrightarrow\varprojlim_nM/I^{n+1}M
$$

is an isomorphism. If $N\subseteq M$ is finite, the induced topology on $N$ is equivalent to its own $I$-adic topology, because for some $c$ and all large $n$,

$$
I^nM\cap N\subseteq I^{n-c}N.
$$

This is the exact point at which noetherianity enters the abelian theory: kernels and images remain complete finite modules. Hence coherent sheaves on a noetherian formal scheme form an abelian category.

One should not define coherence merely by requiring each quotient to be coherent. Without compatibility or uniform finite generation, an inverse system can acquire infinitely many generators as $n$ grows. The limit is then a topological module, but not a coherent one.

### 7.2 The finite-level equivalence

Fix an ideal of definition $\mathcal J$ on a noetherian formal scheme $\mathfrak X$, and let $X_n$ be its thickenings. If $\mathcal F$ is coherent, then

$$
\mathcal F_n=\mathcal F/\mathcal J^{n+1}\mathcal F
$$

is coherent on $X_n$ and satisfies

$$
\mathcal F_{n+1}\otimes_{\mathcal O_{X_{n+1}}}\mathcal O_{X_n}
\simeq\mathcal F_n.
$$

Conversely, suppose coherent $\mathcal F_n$ are supplied with these transition isomorphisms and the cocycle compatibility. Then

$$
\mathcal F=\varprojlim_n\mathcal F_n
$$

is coherent on $\mathfrak X$, and reduction recovers every $\mathcal F_n$. Thus

$$
\operatorname{Coh}(\mathfrak X)
\simeq
\varprojlim_n\operatorname{Coh}(X_n),
$$

where the right side means the category of compatible systems, not merely an inverse limit of isomorphism classes.

The affine proof contains the decisive details. Choose generators of $M_0$ and lift them compatibly through the surjections $M_{n+1}\to M_n$. Topological Nakayama makes the induced map $A^r\to\varprojlim M_n$ surjective. Relations modulo $I$ lift to a finite relation module because $A$ is noetherian. Completeness then identifies the cokernel and all reductions. On overlaps, uniqueness of limits glues the modules.

This result is reconstruction on a formal scheme already given. Grothendieck existence later asks whether such a formal coherent sheaf comes from a coherent sheaf on an ordinary proper scheme. The two statements have different content.

### 7.3 Exactness, tensor products, and internal Hom

Let

$$
0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0
$$

be a sequence of coherent formal sheaves. Exactness is tested on affine charts by exactness of the corresponding sequence of finite complete modules. Because completion is exact on finite modules, an exact algebraic sequence remains exact after completion.

Naive reduction is not left exact and must not be used as an exactness test. If the displayed sequence is short exact and $\mathcal F_n'=\mathcal F'/\mathcal J^{n+1}\mathcal F'$, then reduction gives the exact segment

$$
\operatorname{Tor}_1^{\mathcal O_{\mathfrak X}}
(\mathcal F'',\mathcal O_{X_n})
\longrightarrow\mathcal F'_n\longrightarrow\mathcal F_n
\longrightarrow\mathcal F''_n\longrightarrow0,
$$

so $\mathcal F'_n\to\mathcal F_n$ can fail to be injective. What can be tested infinitesimally is the coherent homology formed first in the formal category: a coherent kernel, cokernel, or homology sheaf is zero exactly when its reduction modulo an ideal of definition is zero, by Nakayama. Equivalently, one may use the full compatible pro-system including the displayed Tor terms. This distinction prevents a false passage from exact formal data to termwise exact reductions.

Tensor products are completed implicitly in the formal category. For coherent sheaves this causes no ambiguity:

$$
\mathcal F\widehat\otimes\mathcal G
\simeq\varprojlim_n(\mathcal F_n\otimes_{\mathcal O_{X_n}}\mathcal G_n).
$$

On a noetherian affine chart, the ordinary tensor product of the corresponding finite modules is already complete, so the hat records topology rather than altering the underlying finite module.

If $\mathcal F$ is finitely presented, internal Hom satisfies

$$
\mathcal H om(\mathcal F,\mathcal G)/\mathcal J^{n+1}
\longrightarrow
\mathcal H om(\mathcal F_n,\mathcal G_n).
$$

This map need not be an isomorphism at each $n$ unless flatness or projectivity removes Tor terms. At the level of compatible systems the correct object is recovered, and when $\mathcal F$ is locally free the displayed map is an isomorphism for every $n$.

### 7.4 Support, flatness, and locally free objects

The support of a coherent formal sheaf is the set of points where its stalk is nonzero. Since every point lies on $X_0$, Nakayama gives

$$
\operatorname{Supp}(\mathcal F)=\operatorname{Supp}(\mathcal F_0).
$$

Thus support is visible on the special fiber, although annihilators and multiplicities are not.

A coherent $\mathcal F$ is locally free of rank $r$ exactly when its reductions are locally free of rank $r$ and their trivializations can be chosen compatibly. In the noetherian complete local affine case it is enough that $M/I M$ be free and $M$ be flat over $A$: lift a basis, use Nakayama for surjectivity, and use flatness to kill the kernel. Freeness of the special fiber alone is not enough; $A/I$ itself is free over itself, while as an $A$-module it usually has torsion.

For an adic morphism $f:\mathfrak X\to\operatorname{Spf}A$, flatness over $A$ can be tested by the local criterion for flatness: each $\mathcal F_n$ must be flat over $A_n$, together with compatibility and separatedness. Smoothness requires more than flatness; in finite presentation it can be checked by formal lifting or, equivalently, by smoothness of the reductions. Nilpotent thickenings are precisely the tests in the infinitesimal criterion.

## 8. Proper formal geometry and formal functions

### 8.1 Properness through all thickenings

Let $f:\mathfrak X\to\mathfrak S$ be an adic finite-type morphism of noetherian formal schemes, and choose compatible ideals of definition. Then $f$ gives morphisms

$$
f_n:X_n\longrightarrow S_n.
$$

If $f_0$ is proper, every $f_n$ is proper. Indeed, $X_0\hookrightarrow X_n$ and $S_0\hookrightarrow S_n$ are nilpotent thickenings; underlying topological maps are unchanged, finite type persists, and the diagonal remains closed. Conversely, formal properness plainly implies properness at level zero.

This criterion makes formal proper geometry manageable, but it does not eliminate the adic and finite-type assumptions. A formal space with proper underlying special fiber can have infinitely many formal coordinates normal to that fiber and fail finite type. Its coherent cohomology need not be finite.

Projective formal morphisms are those admitting a closed immersion into a formal projective space $\widehat{\mathbf P}^r_{\mathfrak S}$. A compatible invertible sheaf $\mathcal L$ is relatively ample when $\mathcal L_0$ is relatively ample on $X_0$; ampleness is unchanged by nilpotent thickening. Projective implies proper, just as at finite level.

### 8.2 Cohomology as an inverse limit

For a coherent sheaf $\mathcal F$ on a proper noetherian formal scheme $\mathfrak X$ over $\operatorname{Spf}A$, define formal cohomology by the sheaf cohomology of $\mathcal F$. There are natural maps

$$
H^q(\mathfrak X,\mathcal F)\longrightarrow H^q(X_n,\mathcal F_n).
$$

The proper formal-functions theorem states

$$
H^q(\mathfrak X,\mathcal F)
\simeq\varprojlim_nH^q(X_n,\mathcal F_n),
$$

and these groups are finite $A$-modules when the base is affine noetherian adic. More generally, for $f:\mathfrak X\to\mathfrak S$ proper,

$$
R^qf_*\mathcal F\simeq\varprojlim_nR^qf_{n*}\mathcal F_n
$$

is coherent.

The proof is local on the base. In the projective case, the uniform levelwise vanishing and generation of Section 9.3 (Lemma 9.3.3 and Proposition 9.3.4) provide finite resolutions by sufficiently positive twists, with bounds independent of the level, and finite cochain complexes. Artin--Rees makes completion exact on their cycles and boundaries. For proper morphisms, a projective modification and noetherian induction reduce the assertion to the projective calculation. The transition systems satisfy the Mittag--Leffler condition because their relevant images stabilize modulo each fixed power.

### 8.3 The formal-functions interface

Suppose now that $X\to\operatorname{Spec}A$ is an ordinary proper morphism, $A$ is noetherian, $I\subset A$, and $\mathcal F$ is coherent. Let $\widehat X$ and $\widehat{\mathcal F}$ denote completion along $I$. Book 15 proves the comparison

$$
H^q(X,\mathcal F)^\wedge_I
\xrightarrow{\sim}
\varprojlim_nH^q(X_n,\mathcal F_n).
$$

The right side is precisely $H^q(\widehat X,\widehat{\mathcal F})$. Hence

$$
H^q(X,\mathcal F)^\wedge_I
\simeq H^q(\widehat X,\widehat{\mathcal F}).
$$

If $A$ itself is $I$-adically complete, proper finiteness makes $H^q(X,\mathcal F)$ finite and therefore complete. The left side may then be written without a hat.

No flatness of $X$ or $\mathcal F$ over $A$ is required. This is important: formal functions is a completion theorem, not the assertion that cohomology commutes with each individual quotient. The map

$$
H^q(X,\mathcal F)/I^{n+1}H^q(X,\mathcal F)
\longrightarrow H^q(X_n,\mathcal F_n)
$$

can fail to be an isomorphism at a fixed level because neighboring cohomology contributes Tor. The inverse limit absorbs the bounded discrepancy through Artin--Rees.

### 8.4 Consequences and failure without properness

For coherent $\mathcal F,\mathcal G$ on proper $X/A$, apply formal functions to $\mathcal H om(\mathcal F,\mathcal G)$ when $\mathcal F$ is locally free, or use a finite presentation and the corresponding Ext sequence in general. One obtains

$$
\operatorname{Hom}_X(\mathcal F,\mathcal G)
\simeq
\varprojlim_n\operatorname{Hom}_{X_n}(\mathcal F_n,\mathcal G_n)
$$

when $A$ is complete. Thus a morphism of coherent sheaves is determined by all its infinitesimal restrictions, and every compatible system of such morphisms is effective once the two sheaves are algebraic.

For a line bundle $\mathcal L$, compatible sections $s_n\in H^0(X_n,\mathcal L_n)$ come from a unique section of $\mathcal L$. Vanishing at every order forces the section to vanish. These elementary-looking consequences are the uniqueness engine in later algebraization arguments.

Without properness, inverse limits can contain functions with unbounded behavior at a missing boundary. For example, formal sections on infinitesimal neighborhoods of a closed fiber in an affine or punctured family may be represented by successively worse denominators. There need be no finite module of global sections whose completion contains them. Completeness controls limits inside a finite module; properness is what supplies that finite module.

## 9. Grothendieck existence for coherent sheaves

### 9.1 The effectivity question

Let $A$ be a noetherian ring complete and separated for $I$, and let $X$ be proper over $A$. Write

$$
X_n=X\times_A\operatorname{Spec}(A/I^{n+1}),
\qquad \widehat X=\varinjlim X_n.
$$

Completion sends a coherent sheaf $\mathcal F$ on $X$ to the compatible system $(\mathcal F_n)_n$, or equivalently to a coherent sheaf $\widehat{\mathcal F}$ on $\widehat X$. The **Grothendieck existence theorem** says that

$$
\operatorname{Coh}(X)\longrightarrow\operatorname{Coh}(\widehat X)
$$

is an equivalence of categories.

Every word carries weight. The base is noetherian and complete, the space is proper, and the objects are coherent. The theorem includes uniqueness of algebraization, existence of an algebraic coherent sheaf, and effectivity of morphisms. It does not assert that arbitrary quasi-coherent sheaves, arbitrary nonproper spaces, or arbitrary inverse systems are effective.

### 9.2 Full faithfulness

For coherent $\mathcal F$ and $\mathcal G$, the desired statement is

$$
\operatorname{Hom}_X(\mathcal F,\mathcal G)
\xrightarrow{\sim}
\operatorname{Hom}_{\widehat X}(\widehat{\mathcal F},\widehat{\mathcal G}).
$$

If $\mathcal F$ is locally free, the right side is the inverse limit of

$$
H^0(X_n,\mathcal F_n^\vee\otimes\mathcal G_n),
$$

and formal functions identifies it with the completion of $H^0(X,\mathcal F^\vee\otimes\mathcal G)$. This module is finite and $A$ is complete, so completion changes nothing.

For general $\mathcal F$, finite presentation gives an affine-local isomorphism

$$
\widehat{\mathcal H om_X(\mathcal F,\mathcal G)}
\simeq
\mathcal H om_{\widehat X}
(\widehat{\mathcal F},\widehat{\mathcal G}).
$$

Indeed, both sides are the same kernel after completing a finite presentation of $\mathcal F$; exactness of completion identifies those kernels. Apply formal functions in degree zero to the coherent sheaf $\mathcal H om_X(\mathcal F,\mathcal G)$. Its global sections are finite over $A$ and hence complete, which gives the desired Hom isomorphism without requiring a global vector-bundle resolution.

This proof yields more than injectivity. A compatible family of maps $\mathcal F_n\to\mathcal G_n$ is not merely approximated by algebraic maps; it comes from one unique algebraic map. Consequently, equations between maps may be checked after completion. If two composites agree at every finite level, they agree on $X$.

### 9.3 Difference sheaves, uniform vanishing, and formal Serre vanishing

Before effectivity can be attempted, three auxiliary results are needed. They are proved here once and are used both in Section 8.2, whose sketch they justify, and in the constructions of Sections 9.4 and 10.3. Throughout this section $A$ is noetherian and complete for $I$, $X=\mathbf P^r_A$ with its standard relatively ample twisting sheaf $\mathcal O(1)$, and $\mathfrak F$ is a coherent sheaf on $\widehat X$. Write $A_n=A/I^{n+1}$, $X_n=X\times_A\operatorname{Spec}A_n$, and $\mathfrak F_n$ for the restriction of $\mathfrak F$ to $X_n$. Set $R=A/I$ and let $X_0=\mathbf P^r_R$ be the closed fiber.

The first lemma controls the failure of two consecutive levels to agree.

**Lemma 9.3.1 (difference sheaves).** For each $n\geq0$ let
$\mathcal K_n=\ker(\mathfrak F_{n+1}\to\mathfrak F_n)$,
viewed as a sheaf on $X_{n+1}$. Then $\mathcal K_n$ is annihilated by
$I^{n+1}$, hence is the pullback of a uniquely determined coherent sheaf
$\overline{\mathcal K}_n$ on $X_0$, and there is a natural surjection

$$
\mathfrak F_0\otimes_R\bigl(I^{n+1}/I^{n+2}\bigr)\longrightarrow\overline{\mathcal K}_n .
$$

_Proof._ On an affine open of $X_{n+1}$ over which $\mathfrak F_{n+1}$ is the
tilde of a module $M$, restriction to $X_n$ is the map induced by
$A_{n+1}\to A_n$, whose kernel is the image of
$M\otimes_{A_{n+1}}(I^{n+1}/I^{n+2})$: indeed
$\ker\bigl(M\to M\otimes_{A_{n+1}}A_n\bigr)$ is generated by the action of
$I^{n+1}$, because the quotient by that image is exactly
$M\otimes_{A_{n+1}}A_n$. Hence $\mathcal K_n$ is locally the image of
$\mathfrak F_{n+1}\otimes(I^{n+1}/I^{n+2})$ and is killed by $I^{n+1}$.
Sheaves killed by the defining ideal of the nilpotent closed immersion
$X_0\hookrightarrow X_{n+1}$ correspond to sheaves on $X_0$ (the finite-level
equivalence of Section 7.2, applied to the thickenings of $X_0$), which gives
$\overline{\mathcal K}_n$. Reducing the displayed local description modulo
$I$ identifies the source with $\mathfrak F_0\otimes_R(I^{n+1}/I^{n+2})$
because $\mathfrak F_{n+1}\otimes_{A_{n+1}}A/I\simeq\mathfrak F_0$, and the
resulting map to $\overline{\mathcal K}_n$ remains surjective since reduction
of a surjective map of sheaves killed by $I^{n+1}$ stays surjective.
$\square$

The second lemma is the engine of uniformity. Call a coherent sheaf
$\mathcal G$ on $\mathbf P^r_S$ _eventually good_ if there is an integer
$e(\mathcal G)$ such that $\mathcal G(t)$ is generated by finitely many
global sections and $H^q(\mathbf P^r_S,\mathcal G(t))=0$ for all $q>0$ and
all $t\geq e(\mathcal G)$.

**Lemma 9.3.2 (propagation of eventual goodness).** Work over the artinian
special-fiber ring $R$.

1. Every coherent sheaf on $\mathbf P^r_R$ is eventually good.
2. Eventual goodness passes over short exact sequences: if
   $0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0$ is exact and two of the
   three sheaves are eventually good, so is the third.
3. If $\mathcal G$ is eventually good, then for every finite $R$-module $M$
   and every coherent quotient $\mathcal Q$ of
   $\mathcal G\otimes_RM$, the sheaf $\mathcal Q$ is eventually good.

_Proof._ (1) Generation and vanishing in high twists hold on
$\mathbf P^r_R$ by the Serre vanishing and generation theorem (Book 008,
Section 6.2).

(2) Generation is immediate: a surjection from a generated sheaf is
generated, and generated sheaves are closed under extensions once the
boundary map can be lifted, which the vanishing clause supplies. For
vanishing, fix $q\geq1$ and let $e'$ and $e''$ work for $\mathcal G'$ and
$\mathcal G''$. For $t\geq\max(e',e'',e'+1)$ the long exact sequence segment
$$
H^q(\mathcal G'(t))\longrightarrow H^q(\mathcal G(t))
\longrightarrow H^q(\mathcal G''(t))
\longrightarrow H^{q+1}(\mathcal G'(t))
$$

has both outer terms zero, so the middle group is caught between two zeros
and vanishes; the same segment read one degree lower handles the boundary
case. The third case is identical chasing.

(3) By hypothesis there is a surjection $\mathcal G\otimes_RM\twoheadrightarrow\mathcal Q$.
Every finite module over the artinian ring $R$ has a finite filtration whose
successive quotients are residue fields of $R$ (take a maximal proper
submodule repeatedly; noetherianity terminates the process). We argue by
induction on the length of such a filtration that every coherent quotient of
$\mathcal G$ twisted against any subquotient of $M$ is eventually good; the
statement for $M$ itself is the top case.

The base case is a residue field $k=S/\mathfrak m$. Then
$\mathcal G\otimes_Sk$ is the pullback of a coherent sheaf on
$\mathbf P^r_k$, and because the closed immersion
$\mathbf P^r_k\hookrightarrow\mathbf P^r_S$ is affine it has the same
cohomology on either space (Book 007b, Corollary 3.11). On $\mathbf P^r_k$
the module of homogeneous sections
$\Gamma_*=\bigoplus_tH^0(\mathcal G\otimes k(t))$ is a finite graded
$k[S]$-module: each piece is finite-dimensional (Book 008, Section 6.3),
and finite generation as a graded module follows because high pieces are
quotients of the finite free modules attached to a finite generating set of
twists, while low pieces are finite in number and each finite-dimensional.
By Hilbert's syzygy theorem over the field $k$ (Book 007b, Chapter 7)
$\Gamma_*$ admits a finite graded free resolution
$\bigoplus_jk[S](-a_j)\to\dots\to\bigoplus_jk[S](-a_j)\to\Gamma_*\to0$.
Applying the sheafification functor, which is exact, resolves
$\mathcal G\otimes k$ by finite sums of twists; every quotient of
$\mathcal G\otimes k$ therefore also admits such a resolution, obtained by
resolving the quotient module, which is again a finite graded module as a
submodule quotient in the noetherian graded ring. The long exact cohomology
sequence together with the projective-space calculation (Book 008, Section
6.1: $H^q(\mathbf P^r,\mathcal O(n))=0$ for $q>0$, $n\geq0$, and vanishing
above degree $r$) shows that any sheaf resolved by sums of
$\mathcal O(a)$ with $\max a_j$ bounded is eventually good, the bound being
read off from the largest shift appearing. This proves the base case,
including all its quotients.

For the induction step, let $0\to M'\to M\to k\to0$ exhibit a filtration
step. Tensoring with $\mathcal G$, which is right exact, gives an exact
sequence
$$
\mathcal G\otimes_RM'\longrightarrow\mathcal G\otimes_RM
\longrightarrow\mathcal G\otimes_Rk\longrightarrow0 ,
$$

so the image $\mathcal R$ of the first map, which is a quotient of
$\mathcal G\otimes_RM'$, fits into
$0\to\mathcal R\to\mathcal G\otimes_RM\to\mathcal G\otimes_Rk\to0$.
Given a quotient $\mathcal Q$ of $\mathcal G\otimes_RM$, let
$\mathcal Q_1$ be the image of $\mathcal R$ in $\mathcal Q$ and
$\mathcal Q_2=\mathcal Q/\mathcal Q_1$ its quotient in
$\mathcal G\otimes_Rk$. Then $\mathcal Q_1$ is a quotient of a quotient of
$\mathcal G\otimes_RM'$, hence eventually good by induction; $\mathcal Q_2$
is a quotient of $\mathcal G\otimes_Rk$, hence eventually good by the base
case; and part (2) makes the extension $\mathcal Q$ eventually good.
Quotients of quotients being quotients, the induction closes.
$\square$

The third lemma transports this along the infinitesimal tower.

**Lemma 9.3.3 (uniform control along the tower).** Choose $m_0$ such that
$\mathfrak F_0$ is $m_0$-regular in the sense of Book 008, Section 6.4; then
for all $m\geq m_0$ the sheaf $\mathfrak F_0(m)$ is globally generated and
$H^q(\mathbf P^r_R,\mathfrak F_0(m))=0$ for $q>0$: generation is part of the
Castelnuovo--Mumford package, and vanishing follows from persistence of
regularity, because $\mathfrak F_0$ is then $j$-regular for every $j\geq m_0$
and applying the definition at $j=m+q$ kills $H^q(\mathfrak F_0(m))$. Such
an $m_0$ exists by Serre vanishing on the closed fiber (Book 008, Section
6.2). Assume henceforth that $R$ is artinian, so that Lemma 9.3.2 applies.
Then for every $n\geq0$ and every $m\geq m_0$:

1. $H^q\bigl(X_0,\overline{\mathcal K}_n(m)\bigr)=0$ for all $q>0$, and
   $\overline{\mathcal K}_n(m)$ is globally generated;
2. the restriction map
   $H^0(X_{n+1},\mathfrak F_{n+1}(m))\to H^0(X_n,\mathfrak F_n(m))$ is
   surjective;
3. $H^q(X_n,\mathfrak F_n(m))=0$ for all $q>0$, and $\mathfrak F_n(m)$ is
   globally generated.

_Proof._ (1) By Lemma 9.3.1, $\overline{\mathcal K}_n$ is a coherent
quotient of $\mathfrak F_0\otimes_R(I^{n+1}/I^{n+2})$, and the module
$I^{n+1}/I^{n+2}$ is finite over the artinian ring $R$; Lemma 9.3.2(3)
applies with $\mathcal G=\mathfrak F_0$, which is eventually good by the
$m_0$-regularity discussion, and yields both clauses.

(2) The short exact sequence of Lemma 9.3.1 gives a long exact sequence
whose relevant segment reads
$$
H^0(X_{n+1},\mathfrak F_{n+1}(m))\longrightarrow H^0(X_n,\mathfrak F_n(m))
\longrightarrow H^1\bigl(X_{n+1},\mathcal K_n(m)\bigr),
$$

and the right-hand group vanishes by (1), the cohomology of a sheaf pulled
back from $X_0$ along the nilpotent thickening being unchanged (affine
morphisms are cohomologically invisible, Book 007b, Corollary 3.11).

(3) Induction on $n$. The case $n=0$ was arranged in choosing $m_0$. Given
vanishing at level $n$, the segment
$$
H^q\bigl(X_0,\overline{\mathcal K}_n(m)\bigr)
\longrightarrow H^q(X_{n+1},\mathfrak F_{n+1}(m))
\longrightarrow H^q(X_n,\mathfrak F_n(m))
$$

shows both neighbors of the middle term vanish, first for $q$ and then,
applying (1) one degree down, for the connecting term; so level $n+1$
vanishes. Generation propagates because $\mathfrak F_{n+1}(m)$ sits in an
extension of $\overline{\mathcal K}_n(m)$ and $\mathfrak F_n(m)$, both
globally generated, and generated sheaves are closed under extensions once
their $H^0$ restriction maps are surjective, which is (2).
$\square$

**Proposition 9.3.4 (formal Serre vanishing).** Let $A$ be noetherian and
complete for $I$, let $X$ be projective over $A$ with $\mathcal O_X(1)$
relatively ample, and let $\mathfrak F$ be coherent on $\widehat X$. If the
closed fiber $X_0$ is projective over an artinian ring — in particular
whenever $A$ is a complete local ring or a complete discrete valuation ring,
so that every consumer in later books sits in this case — then there is an
integer $m_0$ depending only on $\mathfrak F$ and $\mathcal O_X(1)$ such
that for all $m\geq m_0$:

1. $H^q(\widehat X,\mathfrak F(m))=0$ for all $q>0$;
2. the same vanishing holds simultaneously at every finite level,
   $H^q(X_n,\mathfrak F_n(m))=0$;
3. $\mathfrak F_n(m)$ is generated by finitely many global sections for
   every $n$, the number being bounded in terms of $m_0$ alone.

Moreover formal cohomology agrees with the inverse limit of level
cohomologies,
$$
H^q(\widehat X,\mathfrak F(m))
\simeq\varprojlim_nH^q\bigl(X_n,\mathfrak F_n(m)\bigr),
$$

the transition maps satisfying Mittag--Leffler automatically.

_Proof._ A closed immersion $X\hookrightarrow\mathbf P^r_A$ identifies
$\widehat X$ with a closed formal subscheme of $\widehat{\mathbf P}^r_A$,
and pushing forward along it changes neither cohomology nor the levelwise
statements, because a closed immersion is affine and the finite-level
equivalence commutes with pushforward (Section 7.3). So assume
$X=\mathbf P^r_A$. Choose $m_0$ by Lemma 9.3.3.

The comparison with the inverse limit is the formal Čech mechanism. The
standard charts $D_+(T_i)$ and their intersections are affine formal
schemes, on which coherent sheaves are tilde of finite modules over the
completed localizations (Sections 3.3 and 7.2); Serre's criterion in its
formal form — proved exactly as in Book 007b, Theorem 3.9, the alternating
Čech complexes of principal-open covers carrying the same explicit
contracting homotopies, whose coefficients are integral and hence continuous
for the adic topology — shows that sheaf cohomology on $\widehat X$ is
computed by the alternating Čech complex of the standard cover, and that the
terms of that complex are the inversely limited levelwise Čech terms. Each
levelwise term is a finite $A_n$-module (Book 008, Section 6.3), so the
term-wise inverse systems have Mittag--Leffler zero transition images past
each fixed stage, being descending chains in finite modules. Inverse limits
commute with taking cohomology of a complex whose terms satisfy
Mittag--Leffler, which proves the displayed comparison.

Claims (2) and (3) are Lemma 9.3.3(3). For claim (1), the comparison
identifies $H^q(\widehat X,\mathfrak F(m))$ with the inverse limit of the
zero groups of Lemma 9.3.3(3), and the limit of a system of zeros with
surjective-or-zero transitions is zero.
$\square$

Two consequences are recorded for immediate use. First, the discussion of
Section 8.2 is now unconditional in the projective case: the finite
resolutions by sufficiently positive twists exist levelwise uniformly, and
the finiteness of formal cohomology follows from the comparison, each
$H^q(X_n,\mathfrak F_n)$ being finite over $A_n$ and the limit being taken
along a Mittag--Leffler system with eventually surjective structure maps in
degree zero. Second, the appeal to formal Serre vanishing in Section 10.3 is
covered by Proposition 9.3.4 with the same hypotheses.

What Proposition 9.3.4 deliberately does not assert is effectivity: that
$\mathfrak F$ itself is the completion of a coherent sheaf on $X$. Global
generation of $\mathfrak F(m)$ by _formal_ sections, with a finite module of
generators independent of the level, is a strictly stronger statement whose
proof requires the finiteness of the module of formal sections as an
$A$-module, and that is the content of the next section.

### 9.4 Finiteness of formal sections and essential surjectivity

Proposition 9.3.4 stops deliberately short of effectivity, and the distance between the two statements is larger than it looks. Levelwise generation says that each $\mathfrak F_n(m)$ has enough sections defined over $A_n$; it does not say that $\mathfrak F(m)$ has enough sections defined over $A$, because a section of $\mathfrak F(m)$ must be a compatible family of levelwise sections across the whole tower. Surjectivity of the transition maps on global sections, which Lemma 9.3.3(2) supplies, does not close this gap by itself. An inverse system of finite $A/I^{n+1}$-modules with surjective transitions can have an inverse limit that is not finite over $A$: take $M_n=(A/I)^{\oplus n}$ with projections that forget the last summand; every transition is surjective, every $M_n$ is finite over $A/I^{n+1}$, and the limit is a product of countably many copies of $A/I$. The kernels of the transitions, here one new copy of $A/I$ per stage, accumulate without bound. Finiteness of the module of formal sections is therefore a theorem requiring proof, not a formal consequence of the machinery of Section 9.3.

The proof rests on the completed analogue of the homogeneous coordinate ring. Assume first that $X=\mathbf P^r_A$ with its standard twisting sheaf, and set

$$
\widehat S=\bigoplus_{d\geq0}H^0\bigl(\widehat X,\mathcal O(d)\bigr).
$$

Each piece is unchanged by completion. Indeed $H^0(\mathbf P^r_A,\mathcal O(d))=\operatorname{Sym}^d(A^{r+1})$ is a finite free $A$-module (Book 008, Section 6.3), the theorem on formal functions (Book 015, Section 7.2, applied with $i=0$) identifies $H^0(\widehat X,\mathcal O(d))$ with the $I$-adic completion of that module, and finite modules over a complete noetherian ring are already complete (Chapter 2). Hence

$$
H^0\bigl(\widehat X,\mathcal O(d)\bigr)\simeq\operatorname{Sym}^d\bigl(A^{r+1}\bigr),
$$

a finite free $A$-module for every $d$. Multiplication is induced by the tensor product of sections followed by the trivialization $\mathcal O(a)\otimes\mathcal O(b)\simeq\mathcal O(a+b)$, and the resulting graded ring $\widehat S$ is the completed homogeneous coordinate ring of the pair $(\mathbf P^r_A,I)$, the completed Rees algebra of the polarization. Its action on sections is the usual one: multiplying a section of $\mathfrak F(m)$ by an element of degree $e$ yields a section of $\mathfrak F(m+e)$, and a global section of $\mathfrak F(m)$ is the same datum as a morphism $\widehat{\mathcal O}(-m)\to\mathfrak F$. Write $V(m)=H^0(\widehat X,\mathfrak F(m))$.

The first lemma produces generators. It is here that the lifting mechanism converts levelwise data into formal data.

**Lemma 9.4.1 (formal global generation).** Let $m_0$ be an integer working for $\mathfrak F$ in Lemma 9.3.3. Then for every $m\geq m_0$:

1. the restriction map $V(m)\to H^0(X_0,\mathfrak F_0(m))$ is surjective;
2. if $v_1,\dots,v_N$ generate $\mathfrak F_0(m)$ and $v_i'$ are lifts to $V(m)$, then $v_1',\dots,v_N'$ generate $\mathfrak F(m)$;
3. $\mathfrak F$ is a quotient of $\widehat{\mathcal O}(-m)^{\oplus N}$.

_Proof._ (1) By Lemma 9.3.3(2) every transition $H^0(X_{n+1},\mathfrak F_{n+1}(m))\to H^0(X_n,\mathfrak F_n(m))$ is surjective, so any section of $\mathfrak F_0(m)$ lifts recursively through the tower to a compatible system. Proposition 9.3.4 identifies the limit of that system with $V(m)$.

(2) Let $\alpha:\widehat{\mathcal O}^{\oplus N}\to\mathfrak F(m)$ be the map defined by the lifted sections and let $\mathcal G$ be its image, a coherent subsheaf because the category of coherent sheaves is abelian (Section 7). Reducing modulo $I$ sends $\alpha$ to the original surjection $\mathcal O_{X_0}^{\oplus N}\to\mathfrak F_0(m)$, and reduction is right exact, so the composite $\mathcal G_0\to\mathfrak F_0(m)$ remains surjective. The quotient $\mathfrak F(m)/\mathcal G$ is coherent, and right exactness of reduction computes its reduction as $\mathfrak F_0(m)$ divided by the image of $\mathcal G_0$, which is zero. A coherent sheaf whose reduction modulo an ideal of definition vanishes is itself zero (Section 7.3, Nakayama), so $\mathcal G=\mathfrak F(m)$.

(3) Untwisting clause (2), a generating set of $\mathfrak F(m)$ is a set of morphisms $\widehat{\mathcal O}(-m)\to\mathfrak F$ whose images jointly cover; their sum is the desired surjection.
$\square$

The second lemma upgrades one surjection to a presentation. Nothing new is needed beyond applying the first lemma twice, once to $\mathfrak F$ and once to the kernel.

**Lemma 9.4.2 (presentation by completed twists).** There exist integers $m_1\geq m_0\geq0$ and a two-term complex

$$
\widehat{\mathcal O}(-m_1)^{\oplus s}
\xrightarrow{\;\varphi\;}
\widehat{\mathcal O}(-m_0)^{\oplus r}
\longrightarrow\mathfrak F\longrightarrow0
$$

that is exact, in the sense that the image of $\varphi$ equals the kernel of the surjection.

_Proof._ By Lemma 9.4.1(3) there is a surjection $\psi:\widehat{\mathcal O}(-m_0)^{\oplus r}\twoheadrightarrow\mathfrak F$. Its kernel $\mathcal K$ is coherent. Enlarge the initial bound so that it also works for $\mathcal K$ in Lemma 9.3.3, choose $m_1$ beyond that bound, and apply Lemma 9.4.1(2) to $\mathcal K(m_1)$: lifted generators give a surjection $\widehat{\mathcal O}^{\oplus s}\twoheadrightarrow\mathcal K(m_1)$, equivalently a map $\varphi':\widehat{\mathcal O}(-m_1)^{\oplus s}\to\mathcal K$ with image all of $\mathcal K$. Composing with the inclusion $\mathcal K\hookrightarrow\widehat{\mathcal O}(-m_0)^{\oplus r}$ gives $\varphi$ with image equal to $\ker\psi$.
$\square$

Now comes the point where the naive limit argument fails and the noetherian trapping succeeds. Consider what the presentation gives after taking global sections. For each $m$ there is an exact sequence of sheaves

$$
0\longrightarrow\mathcal K(m)\longrightarrow\widehat{\mathcal O}(m-m_0)^{\oplus r}
\longrightarrow\mathfrak F(m)\longrightarrow0 ,
$$

and applying $H^0$ is left exact but not right exact. However, Proposition 9.3.4 applied to $\mathcal K$ produces an integer $m_2$ such that $H^1(\widehat X,\mathcal K(m))=0$ for all $m\geq m_2$. For such $m$ the long exact sequence shows that $H^0$ is exact here:

$$
0\longrightarrow V(\mathcal K,m)\longrightarrow
H^0\bigl(\widehat X,\mathcal O(m-m_0)\bigr)^{\oplus r}
\longrightarrow V(m)\longrightarrow0,
$$

where $V(\mathcal K,m)=H^0(\widehat X,\mathcal K(m))$. The middle term is the finite free module $\operatorname{Sym}^{m-m_0}(A^{r+1})^{\oplus r}$, and $V(\mathcal K,m)$ sits inside it as a submodule. Over the noetherian ring $A$ a submodule of a finite module is finite, and a quotient of a finite module is finite. This trapping of a section module between two finite objects — using injectivity of $H^0$ on the left of a sequence and vanishing of $H^1$ to secure exactness on the right — is precisely the step that the bare surjectivity of transitions could never deliver, because surjectivity controls only quotients of limits, while finiteness needs the kernels to be trapped as well.

**Proposition 9.4.3 (finiteness and finite presentation of formal sections).** Let $\mathfrak F$ be coherent on $\widehat{\mathbf P}^r_A$ with closed fiber projective over the artinian ring $R=A/I$, and let the presentation of Lemma 9.4.2 be fixed, with second kernel $\mathcal K'=\ker(\widehat{\mathcal O}(-m_1)^{\oplus s}\to\mathcal K)$. Then there is an integer $M\geq\max(m_0,m_1)$ such that for all $m\geq M$:

1. $V(m)$ is a finite $A$-module, hence $I$-adically complete;
2. the map $\varphi$ induces, in degree $m$, a map
   $$
   \varphi_m:\operatorname{Sym}^{m-m_1}\bigl(A^{r+1}\bigr)^{\oplus s}
   \longrightarrow
   \operatorname{Sym}^{m-m_0}\bigl(A^{r+1}\bigr)^{\oplus r},
   $$
   and the natural map exhibits $V(m)$ as its cokernel. In particular $V(m)$ carries an explicit finite presentation by finite free $A$-modules.

_Proof._ Choose $m_2$ with $H^1(\widehat X,\mathcal K(m))=0$ for $m\geq m_2$ and $m_3$ with $H^1(\widehat X,\mathcal K'(m))=0$ for $m\geq m_3$, both by Proposition 9.3.4; let $M=\max(m_0,m_1,m_2,m_3)$ and fix $m\geq M$.

The trapping sequence above proves clause (1): $V(m)$ is a quotient of a finite module by a submodule of a finite module.

For clause (2), apply the same argument one step earlier in the presentation. The exact sequence
$$
0\longrightarrow\mathcal K'(m)\longrightarrow
\widehat{\mathcal O}(m-m_1)^{\oplus s}\longrightarrow\mathcal K(m)
\longrightarrow0
$$

has vanishing $H^1$ on the left term, so its $H^0$ sequence is exact and identifies $V(\mathcal K,m)$ with the image of the map induced by the inclusion-composite, namely the image of $\varphi_m$ inside $\operatorname{Sym}^{m-m_0}(A^{r+1})^{\oplus r}$. Chasing the two identifications: the image of $\varphi_m$ equals $V(\mathcal K,m)$ viewed as a submodule of the middle term, and the quotient of the middle term by that submodule is $V(m)$ by the trapping sequence. Hence $V(m)\simeq\operatorname{coker}\varphi_m$ naturally, the maps being the obvious ones induced by $\psi$ and the inclusions.
$\square$

Two remarks record what Proposition 9.4.3 does and does not compare. The proposition describes the formal section modules $V(m)$ absolutely, without reference to levels. It deliberately does not assert that the reduction map $V(m)/I^{k+1}V(m)\to H^0(X_k,\mathfrak F_k(m))$ is an isomorphism at any fixed level $k>0$: as explained in Section 8.3, neighboring cohomology contributes Tor terms, and the fixed-level base-change map may fail to be bijective even when the sheaf involved is algebraic. What holds is exactly the limit statement of Proposition 9.3.4, of which the finitely presented modules $V(m)$ are now known to be the source. Any consumer that needs levelwise information must argue with compatible systems and limits, not with equality at a single level; this discipline will be respected in Section 10.3.

With presentations and finiteness in place, essential surjectivity is short.

**Theorem 9.4.4 (essential surjectivity in the projective case).** Let $A$ be noetherian and complete for $I$, let $X$ be projective over $A$ with relatively ample $\mathcal O_X(1)$, and suppose the closed fiber $X_0$ is projective over an artinian ring. Every coherent sheaf $\mathfrak F$ on $\widehat X$ is the completion of a coherent sheaf $\mathcal F$ on $X$, and $\mathcal F$ is unique up to canonical isomorphism.

_Proof._ First let $X=\mathbf P^r_A$ and fix the presentation of Lemma 9.4.2. Full faithfulness (Section 9.2) algebraizes $\varphi$ uniquely to a map $\varphi_{\mathrm{alg}}:\mathcal O_X(-m_1)^{\oplus s}\to\mathcal O_X(-m_0)^{\oplus r}$ whose completion is $\varphi$ under the Hom identification of Section 9.2. Define $\mathcal F=\operatorname{coker}\varphi_{\mathrm{alg}}$. Completion is exact on coherent sheaves (Artin--Rees, Chapter 2), so the completion of the cokernel is the cokernel of the completion, and therefore $\widehat{\mathcal F}\simeq\operatorname{coker}\varphi\simeq\mathfrak F$.

For uniqueness, given two algebraizations with completions isomorphic to $\mathfrak F$, full faithfulness lifts the isomorphism and its inverse to algebraic maps whose composites complete to the respective identities; faithfulness forces those composites to be the identities.

Now let $X\hookrightarrow\mathbf P^r_A$ be a closed immersion realizing $\mathcal O_X(1)$, and let $\mathfrak G$ be the pushforward of $\mathfrak F$, coherent because the immersion is affine (Sections 7.2 and 7.3). The projective case provides a coherent $G$ on $\mathbf P^r_A$ completing $\mathfrak G$. Support cannot distinguish $G$ from its reduction: for a finite module over a noetherian ring, Nakayama detects vanishing modulo $I$, so $\operatorname{Supp}(G)=\operatorname{Supp}(G_0)\subseteq X_0\subseteq X$, the equality of supports with the formal side being the special-fiber statement of Section 7.4. Hence some power of the ideal sheaf of $X$ annihilates $G$, and $G$ descends to a coherent sheaf $\mathcal F$ on $X$. Completion along $I$ commutes with restriction to the closed subscheme, so $\widehat{\mathcal F}\simeq\mathfrak F|_{\widehat X}=\mathfrak F$, finishing the reduction.
$\square$

Finally, the propositions assemble into the completed-Rees form of Serre's correspondence, which packages the same mathematics without choosing coordinates twice.

**Proposition 9.4.5 (graded reconstruction).** With the hypotheses of Proposition 9.4.3, let $\widehat T=\bigoplus_{m\geq M}\widehat S_m$.

1. The modules $N_m=V(m)$ for $m\geq M$, equipped with the multiplication maps $\widehat S_e\otimes V(m)\to V(m+e)$, form a finitely generated graded $\widehat T$-module $N$; explicitly $N$ is the truncation of the cokernel of the graded map $\widehat S(-m_1)^{\oplus s}\to\widehat S(-m_0)^{\oplus r}$, hence is generated by its pieces in finitely many consecutive degrees starting at $M$.
2. The sheaf attached to $N$ on the formal projective space by the standard chart construction (Section 3.3) is canonically isomorphic to $\mathfrak F$.
3. Conversely, if $P$ is a finitely generated graded $\widehat T$-module, then the sheaf $\widetilde P$ is coherent on $\widehat X$, and $H^0(\widehat X,\widetilde P(m))\simeq P_m$ canonically for all sufficiently large $m$. The kernel of $P\mapsto\widetilde P$ consists of the modules eventually killed under multiplication by high powers of the irrelevant ideal; modules killed by a power of $I$, by contrast, sheafify to pullbacks from the closed fiber rather than to zero, which distinguishes the formal Proj theory from the affine theory of Chapter 7.

_Proof._ (1) The degree-$m$ part of the displayed cokernel is $\operatorname{coker}\varphi_m$, which is $V(m)$ by Proposition 9.4.3(2); the grading is compatible because $\varphi$ is homogeneous of degree $m_1-m_0$. Finite generation follows since the truncation of a finitely generated graded module over $\widehat T$ is finitely generated, being generated by its pieces up to the degrees in which the shifted free modules start.

(2) Sheafification is right exact and commutes with the shift functor, so the sheaf attached to $N$ is presented by the same two-term complex of twists as $\mathfrak F$ in Lemma 9.4.2; comparing the two presentations gives the isomorphism.

(3) Resolve $P$ in high degrees by a finite complex of shifts $\widehat T(-a_j)$; sheafifying resolves $\widetilde P(m)$ by direct sums of twists of $\mathcal O$. Each twist of $\mathcal O$ satisfies the vanishing clauses of Proposition 9.3.4 in large degree, and the two-out-of-three principle for eventual goodness (Lemma 9.3.2(2)) transports vanishing and generation through the resolution, giving $H^q(\widehat X,\widetilde P(m))=0$ for $q>0$ and $m$ large. Exactness of $H^0$ on the truncated resolution then identifies $H^0(\widetilde P(m))$ with $P_m$ plus acyclic corrections that vanish. The description of the kernel is Serre's criterion read formally: a module sheafifies to zero precisely when its high-degree multiplication maps vanish eventually; the remark on $I$-torsion rephrases Lemma 9.3.1, since a module killed by $I^{n+1}$ presents a sheaf pulled back from $X_n$ and ultimately from $X_0$.
$\square$

The decisive point throughout is uniformity. It would not suffice to generate each $\mathfrak F_n$ by a number or twist depending on $n$: the accumulating-kernel example above shows that such data can converge to something infinitely generated. One bound and one finitely presented module of sections serve the entire tower, and that is what makes the algebraization of Theorem 9.4.4 possible.

### 9.5 Passage from projective to proper

The existence theorem remains true when $X$ is proper but not assumed projective. The proof is not obtained by pretending proper means projective. One uses a projective modification $p:X'\to X$ that is an isomorphism over a dense open, algebraizes the pullback data on $X'$, and descends across the exceptional locus by noetherian induction on its support.

Here is the dévissage that makes the descent effective. Choose a coherent ideal $\mathcal J$ supported on $X\setminus U$, where $p$ is an isomorphism over $U$, and replace it by a power so that the natural map from $\mathcal J\mathfrak F$ to its transform under $p$ is injective. This is possible because the kernel is supported outside $U$ and Artin--Rees kills it after multiplication by a high power of $\mathcal J$. The proper-reduction argument of Book 15 gives the same construction algebraically and shows that the cokernel and every positive higher direct image are coherent and supported on $V(\mathcal J)$.

On $X'$ the transformed formal sheaf is effective by the projective case. Its direct image, the cokernel of the injection, and the quotient $\mathfrak F/\mathcal J\mathfrak F$ are therefore reduced to coherent data on $V(\mathcal J)$. Noetherian induction on the support algebraizes those terms. The two exact sequences

$$
0\to\mathcal J\mathfrak F\to\mathfrak F
\to\mathfrak F/\mathcal J\mathfrak F\to0
$$

and the corresponding transform sequence then reconstruct an algebraic extension. Full faithfulness algebraizes the boundary and extension maps and says that the two possible composites agree. Exactness may be checked after forming their coherent homology and completing it; Nakayama kills that homology. Thus the resulting algebraic sheaf completes to $\mathfrak F$. The induction terminates because $V(\mathcal J)$ contains no generic point of the support.

This reduction is why the final theorem requires properness, not a hidden global polarization. Projectivity is a proof device for coherent effectivity. It will reappear as a genuine hypothesis when the object to algebraize is the formal space itself.

### 9.6 What the theorem does and does not say

The theorem algebraizes finite modules, ideals, closed formal subschemes of $\widehat X$, vector bundles, and invertible sheaves. A coherent ideal $\mathfrak a\subset\mathcal O_{\widehat X}$ comes from a unique coherent ideal $\mathcal a\subset\mathcal O_X$, because the inclusion map and the condition of being an ideal are effective. Hence every closed formal subscheme of $\widehat X$ is the completion of a unique closed subscheme of $X$.

It does not say that an abstract proper formal scheme $\mathfrak X$ is the completion of some $X$. There is no ambient $X$ on which to apply the equivalence. Nor does it say an algebraization, when it exists, is determined by a small local completion without properness. The passage from formal sheaves on a known $X$ to an algebraic sheaf is categorically different from constructing $X$ itself.

A useful counterboundary is the affine formal disc $\operatorname{Spf}k[[t]]$. It is the completion of many different curves at smooth points. Coherent existence relative to any chosen proper curve says nothing that selects one of them. Global positivity is the missing datum.

## 10. Algebraizing proper formal schemes

### 10.1 Why coherent existence is not enough

Suppose $A$ is noetherian and $I$-adically complete, and $\mathfrak X$ is proper over $\operatorname{Spf}A$. Its compatible schemes $X_n$ are each proper over $A_n$. We seek a proper $A$-scheme $X$ with

$$
\widehat X\simeq\mathfrak X.
$$

The structure sheaf of $\mathfrak X$ cannot simply be fed into Grothendieck existence, because that theorem begins with an already existing proper scheme $X$. Effectivity of the space requires a way to place every $X_n$ into one fixed finite-dimensional ambient space, with compatible equations.

An ample line bundle provides exactly that. High powers have enough sections to embed every infinitesimal level, and formal cohomology turns compatible sections into a finite complete $A$-module. The equations then become a coherent homogeneous ideal that can be interpreted algebraically.

### 10.2 The ample-line criterion

**Algebraization theorem.** Let $A$ be a noetherian ring complete and separated for an ideal $I$. Let $\mathfrak X$ be a proper adic formal scheme over $\operatorname{Spf}A$. Suppose there is an invertible sheaf $\mathfrak L$ on $\mathfrak X$ whose restriction $L_0$ to $X_0$ is ample over $A/I$. Then there exist a projective $A$-scheme $X$, an invertible sheaf $L$ on $X$, and an isomorphism

$$
(\widehat X,\widehat L)\simeq(\mathfrak X,\mathfrak L).
$$

After replacing $\mathfrak L$ by a sufficiently high power, $L$ may be chosen relatively very ample. The polarized algebraization is unique up to a unique isomorphism compatible with the displayed formal identification.

No separate flatness hypothesis is needed for existence of the scheme. If the formal family is flat, smooth, or has another finite-presentation property detectable on completions or infinitesimal fibers, that property can often be transferred afterward. Properness alone does not provide the ample line bundle; the theorem is a criterion, not a claim that every proper formal scheme is automatically algebraizable.

Ampleness need only be checked on $X_0$. Nilpotent thickenings do not change the underlying topological space, and the affine-open criterion for ampleness shows that an invertible sheaf is ample on $X_n$ exactly when its restriction is ample on $X_0$.

### 10.3 Construction by sections and Proj

Choose $d$ large enough that $\mathfrak L^d$ is generated by formal sections and gives a closed immersion at every level. Formal Serre vanishing (Section 9.3) makes

$$
E=H^0(\mathfrak X,\mathfrak L^d)
$$

a finite $A$-module. Formal global generation (Section 9.4) says that its evaluation map is surjective, and reducing that one map supplies a common finite linear system on every $X_n$. This does not assert that $E/I^{n+1}E$ equals all of $H^0(X_n,L_n^d)$ at each fixed level. A finite set of generators of $E$ gives a morphism

$$
\mathfrak X\longrightarrow\widehat{\mathbf P}^N_A.
$$

Its level-zero map is a closed immersion. The conormal criterion and Nakayama then show that the formal map itself is a closed immersion: the ideal sheaf is coherent and surjectivity can be checked modulo the ideal of definition.

Let $\mathfrak a$ be its coherent homogeneous ideal in the completed projective space. Grothendieck existence for the proper scheme $\mathbf P^N_A$ algebraizes $\mathfrak a$ to a coherent ideal $\mathcal a\subset\mathcal O_{\mathbf P^N_A}$. Set

$$
X=V(\mathcal a)\subseteq\mathbf P^N_A.
$$

Exactness of completion identifies $\widehat X$ with $\mathfrak X$. The tautological bundle restricts to an algebraization of a suitable power of $\mathfrak L$; the original $\mathfrak L$ itself then algebraizes by coherent existence on $X$. The algebraized coherent sheaf is invertible: its non-locally-free locus is closed and proper over $A$, while its completion is empty; the closed-support argument of Section 10.4 forces that locus to be empty.

This proof displays the distinct jobs of the hypotheses. Noetherian completeness makes formal sections finite and effective. Properness gives formal finiteness and vanishing. Ampleness creates the embedding. Omitting any one breaks a specific step.

### 10.4 Uniqueness and algebraization of morphisms

**Proper formal full faithfulness.** Let $X$ and $Y$ be proper $A$-schemes. Completion induces a bijection

$$
\operatorname{Hom}_A(X,Y)
\xrightarrow{\sim}
\operatorname{Hom}_{\operatorname{Spf}A}(\widehat X,\widehat Y).
$$

Indeed, the graph of a formal morphism is a closed formal subscheme of the completion of the proper scheme $X\times_AY$. Grothendieck existence algebraizes its coherent ideal to a closed subscheme $\Gamma\subset X\times_AY$. The first projection $p:\Gamma\to X$ is proper and is an isomorphism after completion. Its non-quasi-finite locus is closed, and its image in $\operatorname{Spec}A$ is closed. If nonempty, that image contains a closed point. The ideal $I$ lies in the Jacobson radical of $A$: for $a\in I$, the partial sums of $1+a+a^2+\cdots$ converge to $(1-a)^{-1}$. Hence every closed point contains $I$, contradicting the formal isomorphism. Thus $p$ is proper and quasi-finite, so it is finite.

Now $\mathcal O_X\to p_*\mathcal O_\Gamma$ is a map of coherent algebras whose completed kernel and cokernel vanish. If either support were nonempty, its proper image in $\operatorname{Spec}A$ would again contain a closed point over $V(I)$, contradicting that vanishing. Thus the algebra map is an isomorphism, $p$ is an isomorphism, and the second projection gives the desired morphism. The same support argument proves uniqueness.

Taking a formal isomorphism and applying the theorem in both directions shows that two proper algebraizations are uniquely isomorphic. The theorem also algebraizes sections, products, and every structure map in this book, because all their sources and targets are proper over $A$. If a separated finite-type target is supplied with an open immersion into a proper $A$-scheme, the same graph proof works: the algebraized graph cannot meet the boundary, since such an intersection would be proper over $A$ and would meet the completed closed locus. No compactification theorem is being assumed for a completely arbitrary target.

Separatedness of the target is essential for a graph to be closed and for uniqueness. Properness of the source supplies coherent effectivity. Without it, distinct maps may have identical restrictions to a chosen formal neighborhood.

### 10.5 Properties recovered after algebraization

Let $X$ algebraize $\mathfrak X$. Flatness over $A$ can be checked after $I$-adic completion for finite modules when $I$ lies in the Jacobson radical, as it does for a complete local base. Locally, the completion is faithfully flat and the local criterion for flatness transfers flatness from all $X_n$ to $X$ near the closed fiber. If every point of the base specializes to the closed locus, properness extends this neighborhood statement globally.

Smoothness is open and can be detected by flatness together with smooth geometric fibers, or by the infinitesimal lifting criterion. Hence a formally smooth, topologically finitely presented algebraization is smooth near the completed fiber; over a complete local base that is the whole proper family. Relative dimension and geometric connectedness can likewise be checked on fibers.

Normality and regularity demand more care. Completion is faithfully flat, but descent of these properties may require excellence. A complete noetherian local ring is excellent in many arithmetic situations of interest, but excellence should be stated rather than smuggled into the word complete. Algebraization guarantees the scheme; transfer of a finer singularity property uses its own criterion.

## 11. Complex analytification

### 11.1 From algebraic varieties to analytic spaces

Completion compares a space with its nilpotent neighborhoods. Over $\mathbf C$ there is another passage: polynomial equations define holomorphic equations on complex points. If $X$ is a scheme locally of finite type over $\mathbf C$, its analytification $X^{\mathrm{an}}$ is a complex analytic space, functorial in $X$ and characterized on affine space by

$$
(\mathbf A^n_{\mathbf C})^{\mathrm{an}}=\mathbf C^n
$$

with its usual topology and sheaf of holomorphic functions. Closed algebraic subschemes are sent to closed analytic subspaces by using the same equations inside the holomorphic structure sheaf. General $X$ is obtained by gluing affine charts.

Analytification preserves finite products and fiber products:

$$
(X\times_SY)^{\mathrm{an}}
\simeq X^{\mathrm{an}}\times_{S^{\mathrm{an}}}Y^{\mathrm{an}}.
$$

It also preserves open and closed immersions, smooth and étale morphisms, and proper morphisms. For a proper algebraic variety, $X^{\mathrm{an}}$ is compact; for a separated one, it is Hausdorff. The converses need not hold without algebraicity data.

The topology changes drastically. The algebraic affine line has closed points and one generic point; its analytification is the ordinary complex plane. The analytic structure sheaf contains $e^z$, while $\Gamma(\mathbf A^1_{\mathbf C},\mathcal O)=\mathbf C[z]$. Thus algebraic and analytic functions cannot agree on nonproper spaces.

### 11.2 Analytification of coherent sheaves

There is a natural morphism of locally ringed spaces

$$
\alpha:X^{\mathrm{an}}\longrightarrow X.
$$

For a coherent algebraic sheaf $\mathcal F$, define

$$
\mathcal F^{\mathrm{an}}
=\alpha^{-1}\mathcal F\otimes_{\alpha^{-1}\mathcal O_X}\mathcal O_{X^{\mathrm{an}}}.
$$

Analytic local rings are flat over the corresponding algebraic local rings. Consequently analytification is exact on coherent sheaves, respects tensor products and finite presentations, and sends locally free sheaves and invertible sheaves to their analytic counterparts.

For a closed subscheme $Z\subset X$ defined by $\mathcal I$, the exact sequence

$$
0\to\mathcal I\to\mathcal O_X\to\mathcal O_Z\to0
$$

remains exact after analytification, so $Z^{\mathrm{an}}$ is the closed analytic subspace defined by $\mathcal I^{\mathrm{an}}$. Nilpotents are retained. Analytification is not merely a functor on sets of complex points.

Stalkwise flatness can be understood through convergent power series. Near a smooth point, the algebraic local ring is localized from polynomials, while the analytic local ring consists of convergent germs. Relations among finitely many algebraic functions that hold analytically already obey the flatness criterion. This local statement is the algebraic foundation for global comparison.

### 11.3 Properness and comparison maps

Every coherent $\mathcal F$ has natural cohomology maps

$$
H^q(X,\mathcal F)\longrightarrow
H^q(X^{\mathrm{an}},\mathcal F^{\mathrm{an}}).
$$

They arise by analytifying sections and their cocycles. On a nonproper space these maps can be far from surjective even in degree zero. Properness removes escape to infinity, just as it did for formal completion, though the analytic mechanism is compactness rather than adic completeness.

For $X=\mathbf P^1_{\mathbf C}$, holomorphic functions on $X^{\mathrm{an}}$ are constant by the maximum principle, matching algebraic global functions. The contrast with $\mathbf A^1$ is exact and memorable. For the line bundles $\mathcal O(n)$, the algebraic and analytic spaces of sections have the same homogeneous-polynomial description for $n\geq0$, and both higher-cohomology calculations agree. This projective-space calculation is the seed of GAGA.

Properness also turns analytic closed subspaces into compact objects. When placed in projective space, Chow's theorem says a closed analytic subspace is algebraic. Coherent GAGA extends that result from ideals to arbitrary coherent sheaves and from projective to proper spaces.

## 12. GAGA for cohomology and coherent sheaves

### 12.1 The projective comparison

Let $X$ be projective over $\mathbf C$. Choose a closed immersion $X\hookrightarrow\mathbf P^N_{\mathbf C}$. The comparison begins with $\mathcal O(n)$ on projective space. A standard affine cover computes algebraic cohomology by rational Cech cocycles. The corresponding analytic cover can be refined by compact polycircular regions. Laurent expansion and the Cauchy integral formula show that its cohomology has the same surviving homogeneous terms. Hence

$$
H^q(\mathbf P^N,\mathcal O(n))
\xrightarrow{\sim}
H^q((\mathbf P^N)^{\mathrm{an}},\mathcal O(n)^{\mathrm{an}})
$$

for every $q$ and $n$.

A coherent sheaf on projective space admits, through repeated use of sufficiently positive twists, a finite resolution long enough for any fixed cohomological degree by sums of $\mathcal O(-m)$. Exactness of analytification and the long exact cohomology sequences transfer the comparison from twists to the sheaf. Pushing a coherent sheaf on $X$ forward along the closed immersion reduces to this case.

The proof strategy mirrors formal existence in a revealing way. Positivity produces finite presentations, finiteness prevents infinite analytic behavior, and exact sequences transport a calculation from standard generators to all coherent objects.

### 12.2 The proper comparison theorem

**GAGA cohomology theorem.** Let $X$ be a proper scheme of finite type over $\mathbf C$ and $\mathcal F$ a coherent algebraic sheaf. Then for every $q\geq0$ the canonical map

$$
H^q(X,\mathcal F)
\xrightarrow{\sim}
H^q(X^{\mathrm{an}},\mathcal F^{\mathrm{an}})
$$

is an isomorphism of finite-dimensional complex vector spaces.

Projectivity gives the preceding proof directly. Two analytic facts extend it to a proper $X$. First, a proper holomorphic map sends a coherent analytic sheaf to coherent higher direct images. Locally on the target, place the inverse image of a relatively compact polydisc in finitely many Weierstrass charts. Division replaces its Čech complex by a bounded complex of finite modules over the polydisc algebra, whose kernels and cokernels remain finite. Second, for a projective morphism this direct-image construction agrees with analytification, by the projective calculation already made.

Now take a projective modification $p:X'\to X$ that is an isomorphism over a dense open. Comparison holds on $X'$. Apply the algebraic and analytic Leray sequences to $p$ and $p^{\mathrm{an}}$. The kernel and cokernel of $\mathcal F\to p_*p^*\mathcal F$, and the sheaves $R^jp_*p^*\mathcal F$ for $j>0$, are coherent and supported on the smaller closed subset where $p$ is not an isomorphism; the analytic direct-image fact supplies the corresponding analytic coherent sheaves. Noetherian induction on that support and the two long exact sequences prove comparison for $\mathcal F$. This includes the higher-direct-image terms omitted by a bare kernel--cokernel argument.

The theorem is functorial in $\mathcal F$ and compatible with connecting homomorphisms, cup products, pullback, and proper pushforward wherever those operations are defined. It is stronger than equality of dimensions: it identifies the naturally corresponding classes.

For $q=0$, every holomorphic section of an algebraic coherent sheaf on a proper algebraic space is algebraic. Applied to $\mathcal O_X$, this says every global holomorphic function is algebraic. If $X$ is connected and proper, both are constant when $X$ is reduced; with nilpotents, both retain the same finite nilpotent algebra.

### 12.3 Full faithfulness and essential surjectivity

For coherent algebraic sheaves $\mathcal F$ and $\mathcal G$ on proper $X$, analytification induces

$$
\operatorname{Hom}_X(\mathcal F,\mathcal G)
\xrightarrow{\sim}
\operatorname{Hom}_{X^{\mathrm{an}}}
(\mathcal F^{\mathrm{an}},\mathcal G^{\mathrm{an}}).
$$

Finite presentation and flatness of analytic local rings give

$$
\mathcal H om_X(\mathcal F,\mathcal G)^{\mathrm{an}}
\simeq
\mathcal H om_{X^{\mathrm{an}}}
(\mathcal F^{\mathrm{an}},\mathcal G^{\mathrm{an}}):
$$

affine-locally both are the same kernel obtained from a finite presentation of $\mathcal F$. The $q=0$ cohomology comparison for this coherent internal Hom gives the displayed global Hom isomorphism. Thus analytification on coherent sheaves is fully faithful without assuming a global vector-bundle resolution of $\mathcal F$.

Essential surjectivity is the deeper direction. Let $\mathfrak F$ be a coherent analytic sheaf on $X^{\mathrm{an}}$. In the projective case, compactness gives a finite Stein cover subordinate to the standard projective charts. Repeated Cauchy division on this cover proves analytic Serre vanishing and global generation for $\mathfrak F(m)$ when $m$ is sufficiently large. Choose finitely many generators, take their coherent kernel, and repeat once. This gives a presentation

$$
\mathcal O_{X^{\mathrm{an}}}(-m_1)^{\oplus a}
\longrightarrow
\mathcal O_{X^{\mathrm{an}}}(-m_0)^{\oplus b}
\longrightarrow\mathfrak F\longrightarrow0.
$$

Full faithfulness algebraizes the first arrow; the algebraic cokernel analytifies to $\mathfrak F$. For proper $X$, use a projective modification. The analytic coherent direct-image theorem keeps the transform, its positive higher direct images, and the exceptional-locus quotients coherent. The same $\mathcal J$-adic dévissage as in Section 9.5 algebraizes the transform upstairs and the smaller-support terms downstairs; full faithfulness algebraizes the gluing maps. Noetherian induction therefore descends the analytic sheaf to $X$.

Therefore analytification gives an equivalence

$$
\operatorname{Coh}(X)
\simeq\operatorname{Coh}(X^{\mathrm{an}})
$$

for proper $X/\mathbf C$. In particular,

$$
\operatorname{Pic}(X)\xrightarrow{\sim}\operatorname{Pic}(X^{\mathrm{an}}),
$$

because invertibility can be tested stalkwise and is preserved in both directions. An analytic vector bundle on $X^{\mathrm{an}}$ has a unique algebraic vector bundle behind it.

### 12.4 Closed subspaces and morphisms

A coherent analytic ideal $\mathfrak a\subset\mathcal O_{X^{\mathrm{an}}}$ algebraizes uniquely to a coherent algebraic ideal $\mathcal a\subset\mathcal O_X$. Full faithfulness algebraizes its inclusion, and exactness shows that multiplication closes its image under products. Hence every closed analytic subspace of a proper algebraic $X$ is the analytification of a unique closed algebraic subscheme.

Morphisms follow from graphs. Let $X$ be proper over $\mathbf C$ and let $Y$ be a separated finite-type scheme supplied with an open immersion into a proper complex scheme $\overline Y$; in particular, $Y$ may be proper or quasi-projective. An analytic morphism

$$
u:X^{\mathrm{an}}\longrightarrow Y^{\mathrm{an}}
$$

has a closed analytic graph in $(X\times Y)^{\mathrm{an}}$. Viewed inside $(X\times\overline Y)^{\mathrm{an}}$, the graph is compact and hence closed; no boundary points are added. Coherent GAGA algebraizes its ideal to a closed algebraic subscheme $\Gamma\subset X\times\overline Y$. The first projection is an isomorphism because its analytification is. The intersection of $\Gamma$ with $X\times(\overline Y\setminus Y)$ has empty analytification and is therefore empty. The second projection consequently lands in $Y$ and yields a unique algebraic morphism $X\to Y$ whose analytification is $u$.

Thus analytification is fully faithful on proper complex schemes. The extension to the displayed nonproper targets is recorded only when a proper compactification is part of the available geometry; no general compactification theorem is hidden in the proof. Separatedness of $Y$ ensures the graph is closed. Properness of $X$ is the source of compactness and effectivity.

As an application, every holomorphic automorphism of a proper complex algebraic variety is algebraic, and every holomorphic homomorphism between complex abelian varieties is algebraic. The assertion includes uniqueness, not merely existence.

### 12.5 Sharp boundaries

GAGA does not say every compact complex manifold is algebraic. A complex torus is algebraic exactly when it admits a positive integral polarization; many complex tori do not. The input to GAGA is a proper algebraic $X$, and the equivalence concerns coherent objects on its analytification.

Properness cannot be weakened to quasi-projectivity. On $\mathbf A^1_{\mathbf C}$, the holomorphic function $e^z$ is not polynomial. Its multiplication map on the analytic structure sheaf is not the analytification of an algebraic endomorphism. Even when global functions happen to agree, coherent essential surjectivity can fail at infinity.

Analytic isomorphism of open varieties need not force algebraic isomorphism by this theorem. Nor does a holomorphic germ automatically come from an algebraic germ. Those are local algebraization or approximation questions requiring separate hypotheses.

Finally, comparison is over $\mathbf C$ and uses complex analytic spaces. It should not be transferred by analogy to a complete nonarchimedean field. There the analytic category, convergence radii, and proper comparison theorem require their own foundations.

## 13. Completion and analytification compared

### 13.1 Two comparison squares

Let $X$ be a finite-type complex scheme and $Y\hookrightarrow X$ a closed subscheme. There are two ways to retain information near $Y$:

$$
X\longmapsto X^{\mathrm{an}},
\qquad
X\longmapsto\widehat X_Y.
$$

Analytifying first gives the analytic space $X^{\mathrm{an}}$ and its closed analytic subspace $Y^{\mathrm{an}}$. Completing its analytic structure sheaf along the analytic ideal gives an analytic formal neighborhood. Completing algebraically first and then extending the finite-level sheaves to the analytic topology gives the same compatible tower:

$$
(\mathcal O_X/\mathcal I^{n+1})^{\mathrm{an}}
\simeq
\mathcal O_{X^{\mathrm{an}}}/(\mathcal I^{\mathrm{an}})^{n+1}.
$$

Thus algebraic and analytic completion commute level by level for coherent data. This is a comparison of infinitesimal systems, not an identification of $\widehat X_Y$ with an open analytic neighborhood.

If $X$ is proper, the two effectivity theorems reinforce one another. A coherent algebraic sheaf determines both a formal sheaf on $\widehat X_Y$ and an analytic sheaf on $X^{\mathrm{an}}$. Formal existence reconstructs it from all infinitesimal levels when the base is complete; GAGA reconstructs it from the entire analytic space. These are different reconstructions with a common coherent source.

### 13.2 Formal neighborhoods versus analytic neighborhoods

A formal neighborhood forgets convergence transverse to $Y$. At a point of the complex affine line, its functions are $\mathbf C[[t]]$, whereas germs of holomorphic functions form the ring $\mathbf C\{t\}$ of convergent power series. The inclusion

$$
\mathbf C\{t\}\subsetneq\mathbf C[[t]]
$$

is strict. A series such as $\sum_{n\geq0}n!t^n$ is a valid formal function but has zero radius of convergence.

Consequently, an isomorphism of formal completions need not itself converge to an analytic isomorphism of neighborhoods. The formal principle is a separate theorem in situations where positivity or negativity of a normal bundle forces convergence. It is not part of formal GAGA or complex GAGA as stated here.

Conversely, an analytic neighborhood contains points away from $Y$, while $\widehat X_Y$ has exactly the points of $Y$. Even when every holomorphic germ has a Taylor series, the passage to Taylor series forgets its radius of convergence and the size of its domain.

### 13.3 Why no generic fiber appears here

For a formal scheme over a complete valuation ring, one may later associate a nonarchimedean analytic generic fiber. That construction inverts a topologically nilpotent parameter and equips the result with analytic convergence conditions. Nothing in

$$
\mathfrak X=\varinjlim X_n
$$

alone performs this inversion or creates analytic points.

The special fiber $X_0$, the formal scheme $\mathfrak X$, and a future analytic generic fiber therefore form three different layers:

$$
\text{special algebraic fiber}
\quad\longleftarrow\quad
\text{formal model}
\quad\dashrightarrow\quad
\text{analytic generic fiber}.
$$

The left relation is reduction modulo an ideal of definition. The dashed arrow requires an additional construction and hypotheses. This book uses only the left relation and algebraization back to ordinary schemes.

## 14. Algebraizing formal curves

### 14.1 The curve criterion

Let $(A,\mathfrak m)$ be a complete noetherian local ring, and let

$$
\mathfrak C\longrightarrow\operatorname{Spf}A
$$

be a proper, flat, finitely presented formal scheme whose fibers have pure dimension one. Assume the special fiber $C_0$ is projective. Then $\mathfrak C$ is algebraizable once it carries a formal invertible sheaf restricting to an ample line bundle on $C_0$. In fact, for curves such a formal lift can be constructed from any ample $L_0$.

The resulting algebraization is a projective flat finitely presented $A$-scheme $C$ with completion $\mathfrak C$. If the formal morphism is smooth, then $C$ is smooth. If the special fiber has only ordinary double points, then $C\to\operatorname{Spec}A$ is a nodal curve. Properness ensures that these open finite-presentation properties, once valid along the closed fiber, hold over the whole local base.

Why dimension one matters is cohomological. The obstruction to lifting a line bundle across a square-zero thickening lies in degree two of the structure sheaf. Coherent cohomology above degree one vanishes on a proper curve. Thus polarization data can be created, not merely assumed.

### 14.2 Lifting an ample line bundle

Write $C_n=\mathfrak C\times_AA/\mathfrak m^{n+1}$. Suppose $L_n$ is an invertible sheaf on $C_n$. The extension $C_n\hookrightarrow C_{n+1}$ has square-zero ideal

$$
\mathcal K_n=\mathfrak m^{n+1}\mathcal O_{C_{n+1}}/
\mathfrak m^{n+2}\mathcal O_{C_{n+1}}.
$$

The multiplicative exact sequence

$$
1\longrightarrow1+\mathcal K_n
\longrightarrow\mathcal O_{C_{n+1}}^\times
\longrightarrow\mathcal O_{C_n}^\times
\longrightarrow1
$$

identifies $1+\mathcal K_n$ with the additive sheaf $\mathcal K_n$, because $\mathcal K_n^2=0$. The obstruction to lifting $L_n$ lies in

$$
H^2(C_0,\mathcal K_n),
$$

which vanishes since the support has dimension one. Hence $L_n$ lifts to $L_{n+1}$. The possible lifts form a torsor under $H^1(C_0,\mathcal K_n)$, while automorphisms of a chosen lift reducing to the identity are $H^0(C_0,\mathcal K_n)$.

Starting with an ample $L_0$, choose lifts successively. Their transition identifications make a formal invertible sheaf $\mathfrak L$. Ampleness of $L_0$ implies ampleness on every nilpotent thickening. The ample-line algebraization theorem now produces $(C,L)$.

Choices need not be unique: $H^1(C_0,\mathcal K_n)$ is usually nonzero. What is unique is the algebraization of the chosen compatible formal pair $(\mathfrak C,\mathfrak L)$. The underlying formal curve may still have a unique algebraization in the proper category by graph effectivity, but no claim should identify different formal line-bundle lifts.

### 14.3 Flat, smooth, and stable curves

Flatness of $C$ follows from formal flatness. Locally, a finite $A$-module $M$ is flat if all $M/\mathfrak m^{n+1}M$ are flat over $A/\mathfrak m^{n+1}$ and $M$ is separated; the local criterion supplies the implication. Since completion is faithfully flat along the closed fiber, no hidden torsion remains.

If every $C_n\to\operatorname{Spec}A_n$ is smooth, the infinitesimal lifting criterion makes the completed morphism formally smooth. The algebraized morphism is of finite presentation, so formal smoothness implies smoothness in a neighborhood of $C_0$. The nonsmooth locus is closed; its image under the proper map is closed in $\operatorname{Spec}A$. Every nonempty closed subset of the spectrum of a local ring meets the closed point, so the nonsmooth locus must be empty.

For nodal curves, use the finite-presentation fiber criterion rather than descending a completed equation. In a flat finitely presented family of curves, the locus where the geometric fiber is either smooth or an ordinary double point is open. Its complement is closed in $C$. If the special fiber is nodal, this complement misses the closed fiber. Its proper image in the local base is closed; if nonempty it would meet the closed point, a contradiction. Thus every geometric fiber of the algebraization is nodal. Étale-locally at a node the completed equation then has the familiar form $A'[[x,y]]/(xy-a)$, with $a$ in the maximal ideal of the étale-local base, as a consequence rather than an unproved descent step. Marked sections avoiding the nodes algebraize as morphisms, and disjointness can be checked on the closed fiber.

Stability is then finite-level. Properness and nodality are already known, while ampleness of

$$
\omega_{C/A}\Bigl(\sum_i s_i\Bigr)
$$

can be checked on the special fiber. Hence a compatible formal stable marked curve over $A$ algebraizes to a stable marked curve. Automorphisms algebraize uniquely, so no new formal symmetries appear.

### 14.4 Uniqueness and marked structures

A formal section $\operatorname{Spf}A\to\mathfrak C$ is a compatible system of sections $s_n:\operatorname{Spec}A_n\to C_n$. Both $\operatorname{Spec}A$ and the algebraization $C$ are proper over $A$, so proper formal full faithfulness gives a unique algebraic section $s:\operatorname{Spec}A\to C$ directly. Its completion is the prescribed compatible system.

The same graph argument algebraizes morphisms between proper formal curves, finite maps, involutions, and group actions by a fixed finite group. Relations such as $u^2=1$ hold algebraically because they hold at every finite level and morphisms are unique. Effective Cartier divisors algebraize through their invertible ideals; their flatness over $A$ must still be checked, usually from the finite levels.

Thus the reusable curve statement is precise: over a complete noetherian local base, a proper flat formal curve is effective because dimension-one obstruction theory lifts an ample bundle; compatible markings and morphisms are effective by proper full faithfulness; smoothness or nodality passes under the stated finite-presentation criteria.

## 15. Algebraizing formal abelian varieties

### 15.1 Polarization supplies effectivity

Let $A$ be a complete noetherian local ring. A **polarized formal abelian scheme** consists here of a proper smooth formal group

$$
\mathfrak A\longrightarrow\operatorname{Spf}A
$$

with geometrically connected fibers, together with a compatible relatively ample invertible sheaf $\mathfrak L$; symmetry and rigidification at the identity may also be included. The ample-line criterion algebraizes $(\mathfrak A,\mathfrak L)$ to a projective $A$-scheme $(A^{\mathrm{alg}},L)$.

To avoid confusing the base ring with the resulting scheme, denote the latter by $G$. Thus

$$
\widehat G\simeq\mathfrak A.
$$

Formal smoothness and finite presentation imply that $p:G\to\operatorname{Spec}A$ is smooth, while properness is built into the projective construction. Geometric connectedness requires no separate component theorem. On the geometrically connected smooth special fiber, $H^0(\mathcal O)=k$. The class of $1$ makes degree-zero base change surjective, so Book 15's exact base-change criterion makes $p_*\mathcal O_G$ a line bundle commuting with every base change near the closed point. An open neighborhood of the closed point of a local spectrum is the whole spectrum, and the unit map $\mathcal O_A\to p_*\mathcal O_G$ is therefore an isomorphism. Every geometric fiber is smooth, hence reduced, and has one-dimensional global functions; properness then forces it to be connected. The remaining task is to recover the group structure.

The polarization is not decoration. It creates the projective embedding that makes the formal space effective. A polarization on the special fiber alone is not the same as a compatible formal polarization: lifting a line bundle on a higher-dimensional variety can be obstructed in $H^2(\mathcal O)$.

### 15.2 Recovering the group law

The formal multiplication, inverse, and identity are morphisms

$$
\mathfrak m:\mathfrak A\times\mathfrak A\to\mathfrak A,
\qquad
\mathfrak i:\mathfrak A\to\mathfrak A,
\qquad
\mathfrak e:\operatorname{Spf}A\to\mathfrak A.
$$

The product $G\times_AG$ is proper, and its completion is $\mathfrak A\times\mathfrak A$. Graph effectivity algebraizes $\mathfrak m$ uniquely to

$$
m:G\times_AG\to G.
$$

Similarly, $\mathfrak i$ and $\mathfrak e$ algebraize to $i$ and $e$. Associativity compares two morphisms $G^3\to G$; they have the same completion because formal multiplication is associative, so full faithfulness makes them equal. The identity and inverse axioms follow identically. Commutativity, if part of the formal data, also descends.

Thus $G$ is a proper smooth group scheme with geometrically connected fibers: an abelian scheme. This argument exemplifies a general principle. Once objects are algebraized and the source of each structure map is proper, operations algebraize by their graphs and axioms descend by uniqueness.

Rigidifications and symmetry of $\mathfrak L$ algebraize as well. For example, an isomorphism

$$
[-1]^*\mathfrak L\simeq\mathfrak L
$$

comes from a unique algebraic isomorphism. Compatibility diagrams hold algebraically because they hold formally.

### 15.3 Smoothness, duality, and uniqueness

Smoothness of $G$ can be checked at the closed fiber. The formal scheme supplies flat infinitesimal neighborhoods and a smooth special fiber. The completed module of relative differentials is locally free of the expected rank, and the infinitesimal lifting criterion holds. Finite presentation turns formal smoothness into ordinary smoothness near the closed fiber; properness over the local base rules out a remote nonsmooth locus.

The dual abelian scheme and a polarization morphism can be recovered after algebraization. A rigidified line bundle determines the usual homomorphism

$$
\lambda_L:G\longrightarrow G^\vee,
\qquad
x\longmapsto t_x^*L\otimes L^{-1}.
$$

Its completion is the formal polarization. Book 15 proves that a relatively ample rigidified line bundle on an abelian scheme makes $\lambda_L$ an isogeny with finite locally free kernel, compatibly with base change. Since the base is local, the kernel rank is the rank on the special fiber. Thus degree and polarization type are preserved, and rank one makes $\lambda_L$ an isomorphism. A principal formal polarization therefore algebraizes to a principal polarization.

Suppose two polarized abelian schemes over $A$ have isomorphic formal completions. Proper full faithfulness algebraizes the formal isomorphism uniquely. Compatibility with multiplication and polarization is an equality of algebraic maps or line-bundle morphisms and can be checked after completion. Hence the polarized algebraization is unique, including all group data.

Over $\mathbf C$, the analytic counterpart says that a holomorphic homomorphism between complex abelian varieties is algebraic. A polarized compact complex torus is projective and hence an abelian variety; the polarization is exactly the positivity that crosses the boundary from general compact complex tori to algebraic ones.

### 15.4 The unpolarized boundary

It is unsafe to argue that an ample line bundle on the special fiber automatically lifts through a formal abelian family. For a square-zero thickening, the obstruction lies in

$$
H^2(A_0,\mathcal K),
$$

which need not vanish when the relative dimension is at least two. A polarization homomorphism need not by itself choose a globally inducing line bundle, and a chosen inducing bundle can be obstructed. Therefore the theorem proved here assumes a compatible formal relatively ample line bundle, with its rigidification and symmetry when those are required. No weaker polarization datum is silently treated as equivalent.

There are broader algebraization theorems for formal group objects under additional hypotheses, but they require arguments beyond the ample-line criterion. No such theorem is silently invoked. In applications where a polarization is intrinsic—principally polarized Jacobians, PEL structures, or abelian schemes equipped with a fixed polarization type—the stated criterion is exactly the needed one.

Level structure and endomorphisms behave more simply once the polarized object exists. A finite collection of formal endomorphisms algebraizes uniquely, and their ring relations persist. If $n$ is invertible on the base, $G[n]$ is finite étale; a full formal level-$n$ structure is a finite list of compatible sections and equalities in this proper finite scheme. Proper formal full faithfulness algebraizes the sections, and equality after completion preserves the group-law and basis relations. These additions do not replace polarization; they are extra structures carried through full faithfulness.

## 16. Synthesis

### 16.1 The four passage principles

The theory is organized by four passages, each with a different source of control.

First, an adic ring is reconstructed from its quotients:

$$
A\simeq\varprojlim_nA/I^{n+1}.
$$

Separatedness gives uniqueness and completeness gives existence of limits. Noetherianity makes the same statement exact for finite modules.

Second, a noetherian formal scheme and its coherent sheaves are reconstructed locally from compatible nilpotent thickenings. This is formal geometry itself. It requires no ambient ordinary scheme.

Third, for a proper scheme over a complete noetherian base, Grothendieck existence identifies coherent algebraic sheaves with coherent formal sheaves on its completion. Properness supplies finite cohomology; completeness turns compatible approximations into actual maps and sections.

Fourth, an abstract proper formal scheme becomes algebraic when a compatible ample line bundle supplies a projective embedding. The output is projective, and graph effectivity supplies uniqueness and algebraizes structure maps. Over $\mathbf C$, GAGA makes the parallel passage between coherent algebraic and coherent analytic objects on a proper space.

These implications should not be collapsed into one slogan:

$$
\begin{array}{ccccc}
\text{algebraic proper space}
&\xrightarrow{\text{completion}}&
\text{formal space}
&\xrightarrow{\text{ample effectivity}}&
\text{algebraic projective space},\\
\downarrow\text{analytification}&&&&\\
\text{proper complex analytic space}.&&&&
\end{array}
$$

The horizontal return arrow needs positivity. The vertical comparison needs the algebraic source to be proper. Neither arrow is a generic-fiber construction.

### 16.2 A hypothesis ledger

For safe later use, the main results can be read through the following ledger.

**Adic algebra.** Reconstruction of $A$ requires separatedness and completeness. Exact reconstruction of finite modules and closedness of submodules use noetherianity, through Artin--Rees. Restricted power series encode topologically finite-type coordinates; unrestricted power series encode a different topology.

**Formal spectra and sheaves.** The points of $\operatorname{Spf}A$ are primes containing an ideal of definition. Functions on a principal open are completed localizations. Coherent formal sheaves correspond to compatible coherent sheaves on all thickenings in the noetherian setting.

**Formal functions.** For a proper morphism of locally noetherian schemes and a coherent sheaf, completed higher direct images equal inverse limits over infinitesimal thickenings. Flatness is not required. A fixed finite-level base-change isomorphism is not asserted.

**Grothendieck existence.** If $A$ is noetherian and $I$-adically complete and $X$ is proper over $A$, completion is an equivalence on coherent sheaves. This gives existence and uniqueness for coherent modules, ideals, closed subschemes, and morphisms between them. It presupposes $X$.

**Algebraization of a formal space.** If $\mathfrak X$ is proper over $\operatorname{Spf}A$ and has an invertible sheaf ample on the special fiber, it has a projective algebraization. The polarized algebraization and its compatible morphisms are unique. Properness without ampleness is not being asserted sufficient here.

**Complex GAGA.** If $X$ is proper of finite type over $\mathbf C$, algebraic and analytic coherent sheaves are equivalent and their cohomology agrees. Analytification is fully faithful on proper complex schemes. The graph argument also algebraizes a morphism to a separated finite-type target when a proper compactification of that target is supplied, as for a quasi-projective target. These conclusions fail in general for nonproper sources.

**Curves and abelian schemes.** On a proper curve, $H^2$ vanishes, so an ample line bundle on the special fiber lifts successively and the formal curve algebraizes. For abelian varieties in dimension at least two, that vanishing argument is unavailable; a compatible formal relatively ample line bundle is retained as a hypothesis. Group operations then algebraize by proper full faithfulness.

### 16.3 Conclusion

Infinitesimal neighborhoods are simultaneously local and global. Their points remain on a closed locus, yet their compatible functions can encode an entire proper family. Adic topology makes this compatibility precise; coherent finiteness makes inverse limits exact; properness turns cohomology into finite data; and ampleness turns finite data into equations in projective space.

The resulting discipline is one of controlled reversibility. Completion forgets points away from a center, so it cannot generally be reversed. On a fixed proper scheme it nevertheless loses no coherent sheaf. On an abstract proper formal scheme, a polarization restores enough global geometry to reverse it. Over the complex numbers, compactness plays the corresponding role: analytic coherent objects and morphisms on a proper algebraic space return uniquely to algebraic geometry.

For curves, vanishing in degree two manufactures the needed positivity and makes formal families effective. For abelian varieties, polarization must be carried as genuine data, after which the scheme, group law, endomorphisms, and polarization all algebraize uniquely. These are not instances of a vague principle that limits converge. They are exact theorems whose hypotheses identify the separate mechanisms of existence, uniqueness, and preservation of structure.
