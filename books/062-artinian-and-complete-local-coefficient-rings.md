# Artinian and Complete Local Coefficient Rings

## Contents

1. [The coefficient problem](#1-the-coefficient-problem)
   - [Why local coefficients](#11-why-local-coefficients)
   - [Local rings and their closed point](#12-local-rings-and-their-closed-point)
   - [Local homomorphisms](#13-local-homomorphisms)
   - [Fixing the residue field](#14-fixing-the-residue-field)
   - [The two scales](#15-the-two-scales)
2. [The anatomy of an Artinian local ring](#2-the-anatomy-of-an-artinian-local-ring)
   - [Why Artinian rings are finite infinitesimal neighborhoods](#21-why-artinian-rings-are-finite-infinitesimal-neighborhoods)
   - [Nilpotence of the maximal ideal](#22-nilpotence-of-the-maximal-ideal)
   - [Finite length and the maximal-ideal filtration](#23-finite-length-and-the-maximal-ideal-filtration)
   - [Tangent and cotangent spaces](#24-tangent-and-cotangent-spaces)
   - [Artinian modules and Nakayama](#25-artinian-modules-and-nakayama)
   - [Morphisms and graded layers](#26-morphisms-and-graded-layers)
3. [The Artinian coefficient category](#3-the-artinian-coefficient-category)
   - [Why a category, not merely a class of rings](#31-why-a-category-not-merely-a-class-of-rings)
   - [Variance of coefficient change](#32-variance-of-coefficient-change)
   - [Fiber products over a common quotient](#33-fiber-products-over-a-common-quotient)
   - [A calculated fiber product](#34-a-calculated-fiber-product)
   - [Quotients as finite stages](#35-quotients-as-finite-stages)
4. [Small extensions and induction on thickness](#4-small-extensions-and-induction-on-thickness)
   - [Why arbitrary surjections are too large](#41-why-arbitrary-surjections-are-too-large)
   - [The socle and principal kernels](#42-the-socle-and-principal-kernels)
   - [Factoring every Artinian surjection](#43-factoring-every-artinian-surjection)
   - [Factoring by powers](#44-factoring-by-powers)
   - [What a small extension linearizes](#45-what-a-small-extension-linearizes)
   - [Small versus square-zero: a counterexample](#46-small-versus-square-zero-a-counterexample)
5. [Square-zero extensions and differentials](#5-square-zero-extensions-and-differentials)
   - [Why first-order change is measured by derivations](#51-why-first-order-change-is-measured-by-derivations)
   - [The split square-zero algebra](#52-the-split-square-zero-algebra)
   - [Kähler differentials](#53-kähler-differentials)
   - [Cotangent space from differentials](#54-cotangent-space-from-differentials)
   - [Conormal modules of square-zero quotients](#55-conormal-modules-of-square-zero-quotients)
   - [Existence, ambiguity, and automorphisms](#56-existence-ambiguity-and-automorphisms)
   - [A basic obstruction calculation](#57-a-basic-obstruction-calculation)
6. [Adic topologies and complete local rings](#6-adic-topologies-and-complete-local-rings)
   - [Why topology enters](#61-why-topology-enters)
   - [Cauchy sequences and compatible residues](#62-cauchy-sequences-and-compatible-residues)
   - [Constructing the completion](#63-constructing-the-completion)
   - [Equivalent adic topologies](#64-equivalent-adic-topologies)
   - [Continuity of homomorphisms](#65-continuity-of-homomorphisms)
   - [Abstract maps can be misleading](#66-abstract-maps-can-be-misleading)
7. [Reconstruction from Artinian quotients](#7-reconstruction-from-artinian-quotients)
   - [Why the finite shadows are Artinian](#71-why-the-finite-shadows-are-artinian)
   - [Separation by Krull intersection](#72-separation-by-krull-intersection)
   - [Completeness and reconstruction](#73-completeness-and-reconstruction)
   - [Reconstructing modules and quotients](#74-reconstructing-modules-and-quotients)
   - [Compatible maps and their limit](#75-compatible-maps-and-their-limit)
8. [Continuous mapping properties](#8-continuous-mapping-properties)
   - [The universal property of completion](#81-the-universal-property-of-completion)
   - [Maps are determined at finite level](#82-maps-are-determined-at-finite-level)
   - [Maps to finite rings](#83-maps-to-finite-rings)
   - [Dense subrings and a caution](#84-dense-subrings-and-a-caution)
   - [Abstract versus continuous Hom](#85-abstract-versus-continuous-hom)
9. [Formal power-series rings](#9-formal-power-series-rings)
   - [Why polynomial coordinates are insufficient](#91-why-polynomial-coordinates-are-insufficient)
   - [Substitution and convergence](#92-substitution-and-convergence)
   - [Universal mapping property](#93-universal-mapping-property)
   - [Quotients and closed ideals](#94-quotients-and-closed-ideals)
   - [Presentations and embedding dimension](#95-presentations-and-embedding-dimension)
   - [Minimal presentations](#96-minimal-presentations)
   - [A mixed-coefficient example](#97-a-mixed-coefficient-example)
10. [Finite modules and topological Nakayama](#10-finite-modules-and-topological-nakayama)
    - [Why algebraic finiteness controls topology](#101-why-algebraic-finiteness-controls-topology)
    - [Topological Nakayama](#102-topological-nakayama)
    - [Artin--Rees and induced topology](#103-artin--rees-and-induced-topology)
    - [Closed submodules and ideals](#104-closed-submodules-and-ideals)
    - [Exactness of completion](#105-exactness-of-completion)
    - [Surjectivity and finite generation modulo the ideal](#106-surjectivity-and-finite-generation-modulo-the-ideal)
    - [Completion and quotients](#107-completion-and-quotients)
11. [Completed tensor products](#11-completed-tensor-products)
    - [Why the ordinary tensor product is not enough](#111-why-the-ordinary-tensor-product-is-not-enough)
    - [Construction over a complete base](#112-construction-over-a-complete-base)
    - [Topology and residue field](#113-topology-and-residue-field)
    - [Universal property](#114-universal-property)
    - [Associativity and symmetry](#115-associativity-and-symmetry)
    - [Base change and quotients](#116-base-change-and-quotients)
    - [Finite-level construction](#117-finite-level-construction)
    - [Three examples](#118-three-examples)
12. [Coefficient bases in equal and mixed characteristic](#12-coefficient-bases-in-equal-and-mixed-characteristic)
    - [Why a residue field need not be a subring](#121-why-a-residue-field-need-not-be-a-subring)
    - [Coefficient fields](#122-coefficient-fields)
    - [Cohen rings as mixed-characteristic bases](#123-cohen-rings-as-mixed-characteristic-bases)
    - [What structure is needed here](#124-what-structure-is-needed-here)
    - [Ramified coefficient rings](#125-ramified-coefficient-rings)
    - [Teichmüller representatives and their limitation](#126-teichmüller-representatives-and-their-limitation)
13. [Lifting and detecting homomorphisms](#13-lifting-and-detecting-homomorphisms)
    - [Why maps should be built one order at a time](#131-why-maps-should-be-built-one-order-at-a-time)
    - [Lifting maps out of power-series rings](#132-lifting-maps-out-of-power-series-rings)
    - [Compatible lifting along a tower](#133-compatible-lifting-along-a-tower)
    - [Surjectivity from cotangent spaces](#134-surjectivity-from-cotangent-spaces)
    - [Relative cotangent criterion](#135-relative-cotangent-criterion)
    - [Detecting isomorphisms](#136-detecting-isomorphisms)
    - [Associated graded tests](#137-associated-graded-tests)
14. [Pro-objects at the concrete inverse-limit level](#14-pro-objects-at-the-concrete-inverse-limit-level)
    - [Why an infinite ring can act on finite tests](#141-why-an-infinite-ring-can-act-on-finite-tests)
    - [Morphisms of inverse systems](#142-morphisms-of-inverse-systems)
    - [The functor attached to a complete ring](#143-the-functor-attached-to-a-complete-ring)
    - [What pro-representation means](#144-what-pro-representation-means)
    - [Uniqueness of the pro-representing ring](#145-uniqueness-of-the-pro-representing-ring)
    - [Tangent space of a represented functor](#146-tangent-space-of-a-represented-functor)
    - [Fiber products and functorial gluing](#147-fiber-products-and-functorial-gluing)
    - [Products of coefficient problems](#148-products-of-coefficient-problems)
    - [Presentations as generators and relations for functors](#149-presentations-as-generators-and-relations-for-functors)
    - [The boundary with later theory](#1410-the-boundary-with-later-theory)
15. [The reusable coefficient-ring dictionary](#15-the-reusable-coefficient-ring-dictionary)
    - [Residue and locality](#151-residue-and-locality)
    - [Artinian diagnostics](#152-artinian-diagnostics)
    - [Tangent and differential translations](#153-tangent-and-differential-translations)
    - [Small-extension protocol](#154-small-extension-protocol)
    - [Fiber products and variance](#155-fiber-products-and-variance)
    - [Completeness checklist](#156-completeness-checklist)
    - [Continuity checklist](#157-continuity-checklist)
    - [Presentation checklist](#158-presentation-checklist)
    - [Finite-module topology checklist](#159-finite-module-topology-checklist)
    - [Completed tensor checklist](#1510-completed-tensor-checklist)
    - [Map-detection checklist](#1511-map-detection-checklist)
    - [Pro-representation checklist](#1512-pro-representation-checklist)
    - [Conclusion](#1513-conclusion)

## 1. The coefficient problem

### 1.1 Why local coefficients

Deformation theory studies an object known over a field by asking how it can vary over rings containing nilpotent elements. The smallest variation is governed by the dual numbers $k[\epsilon]/(\epsilon^2)$; longer variations require thicker rings; and a compatible system of variations often has a limiting ring with infinitely many infinitesimal layers. The coefficient rings must therefore support two opposite requirements. At every finite stage they should be small enough for induction on nilpotence, while at the limit they should be large enough to encode all stages simultaneously.

Local rings meet the first requirement because they single out one closed point. Complete local rings meet the second because they can be reconstructed from all infinitesimal neighborhoods of that point. The passage

$$
R\longmapsto (R/\mathfrak m_R^n)_{n\geq 1}
$$

is the bridge between them. This book builds that bridge carefully, with particular attention to the hypotheses under which it is actually an isomorphism rather than suggestive notation.

All rings are commutative with identity, and homomorphisms preserve identity. Standard commutative algebra concerning ideals, tensor products, localization, finite modules, Noetherian rings, and length is assumed. Topologies, continuity, and completeness will always be specified; no topology on a ring is understood merely from the adjective “local.”

### 1.2 Local rings and their closed point

The problem solved by locality is uniqueness of the point about which one is deforming. A ring $A$ is **local** if it has a unique maximal ideal, denoted $\mathfrak m_A$. Its **residue field** is

$$
k_A=A/\mathfrak m_A.
$$

The quotient map $A\to k_A$ is the algebraic closed point. The following elementary criterion is the source of much of the rigidity of local algebra.

**Proposition (unit criterion).** For a ring $A$, the following are equivalent.

1. $A$ is local.
2. The nonunits of $A$ form an ideal.
3. There is a proper ideal $\mathfrak m$ such that every element of $A\setminus\mathfrak m$ is a unit.

In that case the ideal in (2) and (3) is $\mathfrak m_A$.

**Proof.** If $A$ has unique maximal ideal $\mathfrak m_A$, every nonunit belongs to some maximal ideal and hence to $\mathfrak m_A$; elements outside it are units. Conversely, if all elements outside a proper ideal $\mathfrak m$ are units, every maximal ideal is contained in $\mathfrak m$, so maximality forces it to equal $\mathfrak m$. $\square$

Thus an element $a\in A$ is a unit exactly when its residue $\bar a\in k_A$ is nonzero. In particular $1+x$ is a unit for every $x\in\mathfrak m_A$. If $x$ is nilpotent, its inverse is the finite geometric sum

$$
(1-x)^{-1}=1+x+\cdots+x^{N-1}\qquad(x^N=0).
$$

The ring $k[[t]]$ is local with maximal ideal $(t)$, as is $k[t]_{(t)}$. They have the same residue field and many of the same finite quotients, but only the first is complete for its maximal-ideal-adic topology. Locality and completeness are distinct pieces of structure.

### 1.3 Local homomorphisms

A homomorphism $f:A\to B$ between local rings is **local** if

$$
f(\mathfrak m_A)\subseteq\mathfrak m_B.
$$

Equivalently, $f^{-1}(\mathfrak m_B)=\mathfrak m_A$: the inclusion from left to right is the definition, while an element outside $\mathfrak m_A$ is a unit and its image cannot lie in $\mathfrak m_B$. A local map therefore induces a field homomorphism $k_A\to k_B$.

Not every unital map between local rings is local. The inclusion $k[t]_{(t)}\to k(t)$ into its fraction field is not local: the target maximal ideal is zero, whereas $t$ maps to a nonzero element. This warning matters because maps in the coefficient category must preserve the distinguished closed point.

Surjections behave better. If $f:A\twoheadrightarrow B$ is surjective and $A$ is local, then $B$ is local, $\mathfrak m_B=f(\mathfrak m_A)$, and $f$ is local. Indeed maximal ideals of $B$ correspond to maximal ideals of $A$ containing the kernel. Conversely, if $B$ is local and $f:A\twoheadrightarrow B$ is local, no additional condition is hidden in the terminology.

### 1.4 Fixing the residue field

Deformations of one residual object must all reduce to the same field. Fix henceforth a field $k$. A **local $k$-residue algebra** is a local ring $A$ equipped with a specified identification

$$
\iota_A:A/\mathfrak m_A\xrightarrow{\sim}k.
$$

A morphism $f:A\to B$ is a local homomorphism compatible with these identifications: its induced residue-field map is the identity on $k$. This formulation does not require a section $k\to A$. That omission is essential in mixed characteristic, where a ring of characteristic $p^n$ cannot contain its residue field of characteristic $p$ as a unital subring when $n>1$.

When all rings are $k$-algebras and the structural map $k\to A$ splits the residue map, one often works in the narrower category of **augmented local $k$-algebras**. Then morphisms are $k$-algebra maps. In equal characteristic this is convenient, but the residue-identification category is the stable convention that covers both equal and mixed characteristic.

Two pieces of notation will recur:

$$
\operatorname{Art}_k
$$

denotes local Artinian rings with specified residue field $k$, and

$$
\operatorname{CNL}_k
$$

denotes complete Noetherian local rings with specified residue field $k$, with continuous local residue-compatible maps. A coefficient base, introduced later, may impose an additional algebra structure on every object.

### 1.5 The two scales

The finite and complete scales should be kept visible from the beginning. Typical objects of $\operatorname{Art}_k$ are

$$
k,\qquad k[\epsilon]/(\epsilon^2),\qquad
k[x,y]/(x^2,xy,y^3),\qquad W_n(k)
$$

when the last expression is available. Typical complete objects are

$$
k[[x_1,\ldots,x_r]],\qquad
\mathcal O[[x_1,\ldots,x_r]]/I,\qquad
\mathbf Z_p.
$$

Their Artinian shadows are their quotients by powers of the maximal ideal. The central theme is that a map from a complete ring into an Artinian test ring sees only a finite shadow, while the complete ring itself remembers the compatible totality of those shadows.

## 2. The anatomy of an Artinian local ring

### 2.1 Why Artinian rings are finite infinitesimal neighborhoods

An arbitrary local ring may have infinitely deep powers of its maximal ideal. Inductive deformation arguments need the depth to terminate. The descending chain condition on ideals supplies precisely this termination and, in a local ring, forces the maximal ideal to be nilpotent. Consequently an Artinian local ring is a closed point together with finitely many nilpotent layers.

A ring is **Artinian** if every descending chain of ideals stabilizes. For modules, the same word means the descending chain condition on submodules. We shall repeatedly use the standard theorem that a commutative Artinian ring is Noetherian and has finite length as a module over itself.

### 2.2 Nilpotence of the maximal ideal

**Theorem.** If $(A,\mathfrak m)$ is an Artinian local ring, then $\mathfrak m^N=0$ for some $N$.

**Proof strategy.** The powers stabilize. One must then rule out a nonzero stable ideal by applying Nakayama in a form whose finite generation is guaranteed by Artinianness.

**Proof.** Choose $N$ with $\mathfrak m^N=\mathfrak m^{N+1}$. The ideal $M=\mathfrak m^N$ is a finite $A$-module because an Artinian ring is Noetherian. Thus $M=\mathfrak mM$, and Nakayama's lemma gives $M=0$. $\square$

The least $N$ with $\mathfrak m^N=0$ is the **Loewy length** in one common convention; some authors shift the count, so we will always state the equation defining the convention.

Nilpotence gives an explicit unit theory. Every $a\in A$ has a unique decomposition only after choosing representatives of $k$, but without any choice one still has

$$
A^\times=A\setminus\mathfrak m,
\qquad
1+\mathfrak m\subseteq A^\times,
$$

and $1+\mathfrak m$ has a finite filtration by $1+\mathfrak m^i$. Multiplication on successive quotients is additive:

$$
(1+\mathfrak m^i)/(1+\mathfrak m^{i+1})
\simeq \mathfrak m^i/\mathfrak m^{i+1},
$$

because $(1+x)(1+y)\equiv1+x+y\pmod{\mathfrak m^{i+1}}$ for $x,y\in\mathfrak m^i$ and $2i\geq i+1$.

### 2.3 Finite length and the maximal-ideal filtration

The filtration

$$
A\supset\mathfrak m\supset\mathfrak m^2\supset\cdots\supset
\mathfrak m^N=0
$$

turns nonlinear multiplication into linear algebra. Each quotient $\mathfrak m^i/\mathfrak m^{i+1}$ is annihilated by $\mathfrak m$, hence is naturally a vector space over $k=A/\mathfrak m$. It is finite-dimensional because it has finite length. Additivity of length gives

$$
\ell_A(A)=\sum_{i=0}^{N-1}
\dim_k(\mathfrak m^i/\mathfrak m^{i+1}).
$$

This formula is more informative than the mere finiteness of $A$. It describes the size of every infinitesimal layer and permits induction one layer at a time. The exact finiteness alternatives are worth recording, because nilpotence by itself is not enough.

**Proposition (Artinian local criteria).** For a local ring $(A,\mathfrak m,k)$, the following are equivalent.

1. The ring $A$ is Artinian.
2. The $A$-module $A$ has finite length.
3. The ring $A$ is Noetherian and $\mathfrak m$ is nilpotent.
4. The ideal $\mathfrak m$ is nilpotent and every layer $\mathfrak m^i/\mathfrak m^{i+1}$ is finite-dimensional over $k$.

Indeed, an Artinian commutative ring is Noetherian, and Section 2.2 gives nilpotence. Under (3), each layer is a finitely generated $A$-module annihilated by $\mathfrak m$, hence is finite-dimensional over $k$. Condition (4) directly gives a finite filtration with finite-dimensional factors, so $A$ has finite length. Conversely, a finite-length module is both Artinian and Noetherian. Under any of these conditions the length is the displayed sum of the dimensions of the layers.

The finite-dimensional qualification in (4) cannot be dropped. The local ring

$$
k[x_1,x_2,\ldots]/(x_ix_j:i,j\geq1)
$$

has maximal ideal spanned by all $x_i$ and satisfying $\mathfrak m^2=0$, but it is not Artinian: the descending chain $(x_1,x_2,\ldots)\supset(x_2,x_3,\ldots)\supset\cdots$ never stabilizes.

If $A$ is a local $k$-algebra in the stronger sense and is finite-dimensional as a $k$-vector space, then it is Artinian. Conversely, an object of $\operatorname{Art}_k$ need not be finite-dimensional over $k$ unless it actually carries a compatible $k$-algebra structure. Nevertheless every layer above is a finite-dimensional $k$-space through the residue action, and therefore $A$ has finite length.

**Example.** Let

$$
A=k[x,y]/(x^2,xy,y^3).
$$

It is local with $\mathfrak m=(x,y)$, $\mathfrak m^2=(y^2)$, and $\mathfrak m^3=0$. Its graded layers have dimensions $1,2,1$, so $\ell_A(A)=4$. The relation $xy=0$ is invisible in the first-order tangent layer but affects multiplication between directions. Mixed characteristic gives a complementary example. For $A=\mathbf Z/p^n\mathbf Z$, the maximal ideal is $(p)$, every nonzero layer $(p^i)/(p^{i+1})$ is one-dimensional over $\mathbf F_p$, and $\ell_A(A)=n$. There is no unital embedding $\mathbf F_p\hookrightarrow A$ when $n>1$, despite the simple shape of the layers.

### 2.4 Tangent and cotangent spaces

The first nilpotent layer measures independent first-order parameters. The **cotangent space** of $(A,\mathfrak m,k)$ is

$$
t_A^*=\mathfrak m/\mathfrak m^2,
$$

and its dual

$$
t_A=\operatorname{Hom}_k(\mathfrak m/\mathfrak m^2,k)
$$

is the **Zariski tangent space** of the closed point. The terminology distinguishes parameters from tangent vectors: elements of $\mathfrak m/\mathfrak m^2$ are first-order functions, while a tangent vector evaluates them.

The dimension $\dim_k\mathfrak m/\mathfrak m^2$ is the **embedding dimension**. Nakayama's lemma says it is the minimal number of generators of $\mathfrak m$ when $\mathfrak m$ is finite. Higher layers are not determined by the first: $k[x]/(x^2)$ and $k[x]/(x^3)$ both have embedding dimension one but different lengths and multiplication.

There is a useful functorial interpretation in the augmented equal-characteristic setting. A $k$-algebra map

$$
A\longrightarrow k[\epsilon]/(\epsilon^2)
$$

reducing to the residue map has the form $a\mapsto\bar a+d(a)\epsilon$, where $d:A\to k$ is a $k$-derivation. Such derivations vanish on $\mathfrak m^2$ and identify with $t_A$. This statement will be placed in its natural generality in Chapter 5.

### 2.5 Artinian modules and Nakayama

For later use we record the precise finite-generation engine.

**Nakayama's lemma.** Let $(A,\mathfrak m)$ be local and $M$ a finitely generated $A$-module.

1. If $M=\mathfrak mM$, then $M=0$.
2. If elements $x_1,\ldots,x_r$ map to generators of $M/\mathfrak mM$ over $k$, then they generate $M$.
3. If $N\subseteq M$ and $M=N+\mathfrak mM$, then $M=N$.

**Proof strategy.** Choose a minimal generating family. If its first element is an $\mathfrak m$-linear combination of all generators, move its coefficient to the left; the coefficient of that generator becomes a unit, contradicting minimality. The other forms follow by applying the first to a quotient. $\square$

Finite generation cannot be omitted. For $A=k[[t]]$, the module $M=k((t))/k[[t]]$ satisfies $tM=M$ but is nonzero. This counterexample will matter when topological Nakayama is discussed: completeness is not a substitute for finite generation unless the topology and a limiting argument provide additional control.

### 2.6 Morphisms and graded layers

A morphism $f:A\to B$ in $\operatorname{Art}_k$ carries $\mathfrak m_A^i$ into $\mathfrak m_B^i$ and induces $k$-linear maps

$$
\mathfrak m_A^i/\mathfrak m_A^{i+1}
\longrightarrow
\mathfrak m_B^i/\mathfrak m_B^{i+1}.
$$

The first is the cotangent map $t_A^*\to t_B^*$. A surjection $A\twoheadrightarrow B$ induces a surjection on cotangent spaces, but the converse is false without completeness and finite-generation hypotheses. For example, the local inclusion $k[t]_{(t)}\hookrightarrow k[[t]]$ induces an isomorphism on cotangent spaces and all quotients by powers, yet is not surjective as an abstract ring map.

For a surjection with kernel $I$, one has

$$
\mathfrak m_B=\mathfrak m_A/I,
\qquad
\mathfrak m_B^n=(\mathfrak m_A^n+I)/I,
$$

and the exact cotangent sequence

$$
I/(I\cap\mathfrak m_A^2)
\longrightarrow \mathfrak m_A/\mathfrak m_A^2
\longrightarrow \mathfrak m_B/\mathfrak m_B^2\longrightarrow0.
$$

It displays exactly which first-order parameters are killed by the quotient.

## 3. The Artinian coefficient category

### 3.1 Why a category, not merely a class of rings

A deformation over $A$ must be transportable along a coefficient map $A\to B$. Consequently the test rings need their morphisms, products, and quotient factorizations, not just a list of objects. Fix a residue field $k$ and use $\operatorname{Art}_k$ as defined in Section 1.4. Its terminal object is $k$: every $A$ has exactly its specified residue map $A\to k$. Unless coefficient fields are chosen, $k$ need not be initial.

If a complete local base ring $(\mathcal O,\mathfrak m_{\mathcal O},k)$ is fixed, the category $\operatorname{Art}_{\mathcal O}$ consists of Artinian local $\mathcal O$-algebras $A$ for which $\mathcal O\to A$ is local and induces the fixed residue identification. Morphisms are local $\mathcal O$-algebra maps. The corresponding complete category is $\operatorname{CNL}_{\mathcal O}$. Taking $\mathcal O=k$ recovers augmented equal-characteristic algebras.

### 3.2 Variance of coefficient change

Given a coefficient map $A\to B$, scalar extension carries an object over $A$ to one over $B$. Thus a deformation assignment is normally a **covariant** functor

$$
D:\operatorname{Art}_k\longrightarrow\mathbf{Sets}.
$$

This sometimes looks contrary to the geometric convention because affine spectra reverse arrows. A ring map $A\to B$ corresponds to $\operatorname{Spec}B\to\operatorname{Spec}A$, and pulling a family back along this geometric arrow is the same forward operation $D(A)\to D(B)$ on rings.

A complete local ring $R$ gives the model functor

$$
h_R(A)=\operatorname{Hom}_{\mathrm{loc},k}(R,A).
$$

It is covariant in $A$ and contravariant in $R$. For Artinian $A$, every local map from an adic complete Noetherian $R$ is automatically continuous; we retain the continuity label later to expose why.

### 3.3 Fiber products over a common quotient

Gluing two coefficient changes that agree after reduction leads to a fiber product. Suppose $A'\to A$ and $A''\to A$ are morphisms in $\operatorname{Art}_k$, and assume at least one is surjective. Define

$$
B=A'\times_AA''=\{(a',a''):f'(a')=f''(a'')\}.
$$

The unit is $(1,1)$ and operations are componentwise. The surjectivity hypothesis ensures that $B$ is again local with

$$
\mathfrak m_B=\mathfrak m_{A'}\times_{\mathfrak m_A}\mathfrak m_{A''}.
$$

Indeed, suppose $A'\to A$ is surjective. Projection $B\to A''$ is then surjective, and its kernel identifies with $I=\ker(A'\to A)$. A pair outside the displayed maximal ideal has two unit components, and their compatible inverses again form a pair. Hence $B$ is local and its residue field is $k$. Filter $I$ by powers of $\mathfrak m_{A'}$. Every layer is a finite-dimensional $k$-space, and the $B$-action on it factors through the common residue map, so $I$ has finite length as a $B$-module. The quotient $A''$ also has finite length as a $B$-module because its $B$-submodules are its ideals. The exact sequence $0\to I\to B\to A''\to0$ gives finite length for $B$, hence Artinianness.

The projections satisfy the universal property: maps $C\to B$ are the same as pairs $C\to A'$, $C\to A''$ with equal composites to $A$. The construction is therefore the categorical pullback in $\operatorname{Art}_k$ under the stated hypothesis.

Surjectivity is not cosmetic in this formulation. Without it, the ordinary ring fiber product is not guaranteed by the preceding argument to be an object of the fixed-residue Artinian category: even the prescribed residue identification can fail to descend with the required surjectivity. We therefore assert closure only for diagrams with a surjective leg. In the applications, one leg is a quotient precisely because the diagram compares two lifts of the same lower-order object.

### 3.4 A calculated fiber product

Let $A=k$, $A'=k[\epsilon]/(\epsilon^2)$, and $A''=k[\eta]/(\eta^2)$, with both maps the residue maps. Then

$$
A'\times_kA''\cong
k[\epsilon,\eta]/(\epsilon^2,\epsilon\eta,\eta^2).
$$

The vanishing of $\epsilon\eta$ records that the two infinitesimal directions live on separate branches over the common closed point. Its cotangent space is two-dimensional. More generally, when $A'\to A$ is surjective, the additive exact sequence $0\to B\to A'\oplus A''\to A\to0$ gives

$$
\ell(B)=\ell(A')+\ell(A'')-\ell(A),
$$

where length may be read as the number of common residue-field composition factors. By contrast, the tensor product

$$
A'\otimes_kA''\cong k[\epsilon,\eta]/(\epsilon^2,\eta^2)
$$

retains the mixed term $\epsilon\eta$ and has length four rather than three. Fiber product and tensor product answer different universal problems and must not be interchanged.

### 3.5 Quotients as finite stages

If $A\in\operatorname{Art}_k$, each $A/\mathfrak m_A^n$ lies in $\operatorname{Art}_k$, and the tower stabilizes at $A$. If $R$ is complete Noetherian local, the same quotients are its finite stages. A local map $R\to A$ kills $\mathfrak m_R^n$ once $\mathfrak m_A^n=0$, hence factors through $R/\mathfrak m_R^n$. Therefore

$$
\operatorname{Hom}_{\mathrm{loc},k}(R,A)
=\varinjlim_n
\operatorname{Hom}_{\mathrm{loc},k}(R/\mathfrak m_R^n,A).
$$

The transition direction is worth checking: a map from a later, thicker quotient that kills enough powers descends to a map from the appropriate finite stage. This finite-factorization principle is the elementary reason complete rings can govern functors on Artinian rings.

## 4. Small extensions and induction on thickness

### 4.1 Why arbitrary surjections are too large

Suppose one wants to lift data from $A$ across a surjection $A'\twoheadrightarrow A$. If the kernel has many interacting layers, existence and uniqueness are entangled. The remedy is to factor the surjection into steps whose kernels are one residue-vector-space layer and are killed by the maximal ideal. At such a step, nonlinear error terms disappear and the lifting problem becomes linear.

A surjection $\pi:A'\twoheadrightarrow A$ in $\operatorname{Art}_k$, with kernel $I$, is a **small extension** if

$$
\mathfrak m_{A'}I=0.
$$

Then automatically $I^2=0$, since $I\subseteq\mathfrak m_{A'}$ unless $A=0$, which never occurs in our unital local category. The action of $A'$ on $I$ factors through $k$, so $I$ is a finite-dimensional $k$-vector space.

Some authors reserve “small extension” for $\dim_k I=1$. We will call that a **principal small extension**. Equivalently, it has a nonzero generator $t\in I$ with

$$
I=(t),\qquad \mathfrak m_{A'}t=0.
$$

The qualifier prevents ambiguity in arguments where a multi-dimensional square-zero kernel is split into one-dimensional steps.

### 4.2 The socle and principal kernels

The **socle** of an Artinian local ring $A$ is

$$
\operatorname{Soc}(A)=0:_A\mathfrak m_A.
$$

It is a nonzero $k$-vector space unless $A=0$: if $N$ is maximal with $\mathfrak m^N\neq0$, then $\mathfrak m^N\subseteq\operatorname{Soc}(A)$. A quotient $A\twoheadrightarrow A/(t)$ by a nonzero socle element $t$ is a principal small extension when $(t)$ is one-dimensional over $k$. Every nonzero element of the socle spans such an ideal because $at=\bar a\,t$ under the residue-field action on the socle.

**Example.** The map $k[x]/(x^{n+1})\twoheadrightarrow k[x]/(x^n)$ has kernel $k x^n$, killed by $(x)$, and is principal small. The map

$$
k[x,y]/(x,y)^2\twoheadrightarrow k
$$

is small with two-dimensional kernel but is not principal.

### 4.3 Factoring every Artinian surjection

**Theorem (small-extension factorization).** Let $A'\twoheadrightarrow A$ be a surjection in $\operatorname{Art}_k$. It factors as a finite composite of principal small extensions.

**Proof strategy.** Work inside the kernel and repeatedly remove a one-dimensional subspace lying in its intersection with the socle. Length decreases at every step, so the process terminates.

**Proof.** Let $I$ be the kernel. If $I=0$ there is nothing to prove. Choose the largest $r$ such that $\mathfrak m_{A'}^rI\neq0$. Then

$$
0\neq\mathfrak m_{A'}^rI\subseteq I\cap\operatorname{Soc}(A').
$$

Choose $0\neq t$ in this vector space and put $J=kt=(t)$. The quotient map $A'\to A'/J$ is principal small. Since $J\subseteq I$, the original map factors through a surjection $A'/J\twoheadrightarrow A$ whose kernel $I/J$ has smaller length. Induction on $\ell_{A'}(I)$ completes the proof. $\square$

The assumptions are exact. Artinianness supplies finite length and a nonzero socle layer. For a general complete local surjection the kernel may have infinite length, so a finite factorization need not exist. Also, a general square-zero extension need not be small: $I^2=0$ does not imply $\mathfrak m_{A'}I=0$.

### 4.4 Factoring by powers

There is a coarser but canonical factorization. If $I=\ker(A'\to A)$, the filtration

$$
I\supseteq \mathfrak m_{A'}I\supseteq\mathfrak m_{A'}^2I\supseteq\cdots\supseteq0
$$

has $k$-vector-space quotients. It gives successive surjections whose kernels are killed by the maximal ideal of the relevant source. Refining each finite-dimensional quotient by a flag yields the principal factorization above. The flag is noncanonical; the existence is what induction requires.

### 4.5 What a small extension linearizes

Let $A'\twoheadrightarrow A$ be small with kernel $I$. If $x',y'$ are two lifts of the same $x\in A$, then $x'-y'\in I$. Products of correction terms vanish, and multiplying a correction by $a'\in A'$ depends only on $\bar a'\in k$. Thus polynomial equations can be expanded to first order.

For example, if $F\in A'[X_1,\ldots,X_r]$ and $\mathbf x$ is a solution modulo $I$, choose a lift $\widetilde{\mathbf x}$. Replacing it by $\widetilde{\mathbf x}+\mathbf u$ with $\mathbf u\in I^r$ changes the value by

$$
F(\widetilde{\mathbf x}+\mathbf u)
=F(\widetilde{\mathbf x})+
\sum_i \overline{\frac{\partial F}{\partial X_i}(\widetilde{\mathbf x})}\,u_i,
$$

because all quadratic terms in the $u_i$ vanish and coefficients act on $I$ through $k$. Existence becomes a linear equation in $I$; the ambiguity among solutions is a kernel. This is the elementary algebra behind later obstruction calculations, but no deformation functor is needed to see it.

### 4.6 Small versus square-zero: a counterexample

Set

$$
A'=k[x,e]/(x^2,e^2),\qquad A=k[x]/(x^2),
$$

and quotient by $(e)$. The kernel $I=(e)$ satisfies $I^2=0$, but $xe\neq0$, so $\mathfrak m_{A'}I\neq0$. It is a square-zero extension, not a small extension. The kernel is an $A$-module on which the nilpotent element $x$ acts nontrivially. Smallness is precisely the stronger assertion that only the residue field acts.

## 5. Square-zero extensions and differentials

### 5.1 Why first-order change is measured by derivations

When an ideal $I$ has $I^2=0$, multiplication in a ring extension remembers at most one occurrence of an element of $I$. Any change of a lift is therefore additive and obeys the product rule. Derivations are not an analogy imposed on the problem; they are forced by comparing multiplicative sections of a square-zero quotient.

Let $B$ be an $A$-algebra and $M$ a $B$-module. An **$A$-derivation** is an additive map $d:B\to M$ satisfying

$$
d(ab)=a\,d(b)+b\,d(a),\qquad d(a_0)=0\quad(a_0\in A).
$$

The group is denoted $\operatorname{Der}_A(B,M)$. The formula gives $d(1)=0$. In general a derivation is not $B$-linear; the failure of linearity is exactly the information it records.

### 5.2 The split square-zero algebra

The universal elementary model is $B\oplus M$ with multiplication

$$
(b,m)(b',m')=(bb',bm'+b'm).
$$

Its ideal $0\oplus M$ has square zero, and projection to $B$ is a ring map. It is often denoted $B\ltimes M$. A section $s:B\to B\ltimes M$ has the form $s(b)=(b,d(b))$, and it is a ring homomorphism exactly when $d$ is a derivation.

More generally, if two $A$-algebra maps $f,g:C\to B'$ have the same composite to $B=B'/I$, where $I^2=0$, then $f-g:C\to I$ is an $A$-derivation when $I$ is regarded as a $C$-module through their common reduction. This follows by expanding

$$
f(xy)-g(xy)=f(x)(f(y)-g(y))+(f(x)-g(x))g(y).
$$

Either map gives the same action on $I$, since their difference lies in $I$ and $I^2=0$.

### 5.3 Kähler differentials

It is inefficient to study every target module separately. The module of **Kähler differentials** $\Omega_{B/A}$ represents derivations:

$$
\operatorname{Hom}_B(\Omega_{B/A},M)
\xrightarrow{\sim}\operatorname{Der}_A(B,M).
$$

It is generated by symbols $db$ subject to

$$
d(b+b')=db+db',\qquad d(bb')=b\,db'+b'\,db,
\qquad da=0\quad(a\in A).
$$

The map $d_{B/A}:B\to\Omega_{B/A}$ is universal. This definition imposes exactly, and only, the identities shared by all derivations. For a polynomial ring,

$$
\Omega_{A[x_1,\ldots,x_r]/A}
\cong\bigoplus_{i=1}^r A[x_1,\ldots,x_r]\,dx_i.
$$

If $B=P/J$, there is a right-exact **conormal sequence**

$$
J/J^2\xrightarrow{d}\Omega_{P/A}\otimes_PB
\longrightarrow\Omega_{B/A}\longrightarrow0.
$$

Thus differentials of defining equations are precisely the linear relations among coordinate differentials.

### 5.4 Cotangent space from differentials

If $B$ is a local $A$-algebra with residue field $k$, then $\Omega_{B/A}\otimes_Bk$ is the relative cotangent space. If $A=k$ and $B\to k$ is augmented, there is a canonical isomorphism

$$
\Omega_{B/k}\otimes_Bk\cong\mathfrak m_B/\mathfrak m_B^2.
$$

Both spaces represent $k$-derivations $B\to V$ for every $k$-vector space $V$, where $B$ acts through its residue field.

For $B=k[x,y]/(x^2,xy,y^3)$, the conormal sequence gives generators $dx,dy$ and relations

$$
2x\,dx,\qquad x\,dy+y\,dx,\qquad 3y^2\,dy.
$$

After tensoring with $k=B/(x,y)$ all coefficients vanish, so the cotangent space has basis $dx,dy$ in every characteristic. Higher relations govern more than the tangent space and reappear when lifting beyond first order.

### 5.5 Conormal modules of square-zero quotients

For a surjection $B'\twoheadrightarrow B$ with kernel $I$, the relative conormal sequence begins

$$
I/I^2\longrightarrow\Omega_{B'/A}\otimes_{B'}B
\longrightarrow\Omega_{B/A}\longrightarrow0.
$$

If $I^2=0$, the first term is simply $I$. The map need not be injective. If $B'=k[x]$ and $B=k[x]/(x^p)$ in characteristic $p$, the class of $x^p$ maps to $d(x^p)=0$. Thus right exactness is general; injectivity requires further hypotheses.

For a small extension in $\operatorname{Art}_k$, $I$ is a $k$-vector space. This is why obstruction terms naturally take values in tensor products with $I$: every nonlinear coefficient action has collapsed to the residue action.

### 5.6 Existence, ambiguity, and automorphisms

For a square-zero extension $B'\twoheadrightarrow B$ with kernel $I$, if a lift of an $A$-algebra map $C\to B$ exists, the set of lifts is a torsor under

$$
\operatorname{Der}_A(C,I).
$$

After choosing a lift $f$, the action is $f\mapsto f+d$. The derivation rule makes $f+d$ multiplicative. Existence of a lift, ambiguity among lifts, and automorphisms identifying choices are distinct questions. Square-zero algebra answers the second and prepares the first; it does not automatically solve existence or quotient by automorphisms.

### 5.7 A basic obstruction calculation

Let $C=A[X_1,\ldots,X_r]/(F_1,\ldots,F_s)$ and let $B'\twoheadrightarrow B$ be small with kernel $I$. A map $C\to B$ gives a solution $\mathbf x\in B^r$. Choose lifts $\widetilde{\mathbf x}\in(B')^r$. Each error $F_j(\widetilde{\mathbf x})$ lies in $I$. A correction $\mathbf u\in I^r$ gives a solution precisely when

$$
F_j(\widetilde{\mathbf x})+
\sum_i \overline{\frac{\partial F_j}{\partial X_i}(\mathbf x)}\,u_i=0.
$$

Thus the error vector must lie in the image of a Jacobian linear map $I^r\to I^s$. Changing the initial lifts changes the error by an element of that image, so its cokernel class is intrinsic. This is obstruction theory in elementary form: a nonlinear lifting problem produces a well-defined linear class.

## 6. Adic topologies and complete local rings

### 6.1 Why topology enters

A formal power series is meaningful because its tails become arbitrarily divisible by the variables. An infinite sum requires a topology making those tails tend to zero. For local coefficient rings the natural neighborhoods are powers of an ideal, usually the maximal ideal, but this topology must be declared and its separation and completeness proved.

Let $R$ be a ring and $I\subseteq R$. The **$I$-adic topology** has $I^n$ as a neighborhood basis of $0$. It is Hausdorff exactly when

$$
\bigcap_{n\geq1}I^n=0.
$$

We then say $R$ is **$I$-adically separated**.

### 6.2 Cauchy sequences and compatible residues

A sequence $(x_j)$ is $I$-adically Cauchy if for every $n$ there is $N$ such that $x_i-x_j\in I^n$ for $i,j\geq N$. It converges to $x$ if eventually $x_j-x\in I^n$ for every $n$. Separation gives uniqueness.

Compatible residues give the canonical map

$$
\eta_R:R\longrightarrow\varprojlim_n R/I^n,
\qquad r\longmapsto(r\bmod I^n)_n.
$$

Its kernel is $\bigcap_nI^n$. Surjectivity says every compatible family of finite-precision residues is represented. We call $R$ **$I$-adically complete and separated** if $\eta_R$ is an isomorphism. Our use of “complete” in an adic context includes separatedness.

### 6.3 Constructing the completion

The **$I$-adic completion** is

$$
\widehat R^{\,I}=\varprojlim_nR/I^n.
$$

If $R$ is Noetherian, the kernel of $\widehat R^{\,I}\to R/I^n$ is $I^n\widehat R^{\,I}$, and

$$
\widehat R^{\,I}/I^n\widehat R^{\,I}\cong R/I^n.
$$

These identities can fail in nonnoetherian situations: the inverse-limit topology need not coincide with powers of the extended ideal. We invoke them only under Noetherian or explicit finite-generation hypotheses. For $R=k[t]$ and $I=(t)$, the completion is $k[[t]]$; compatible residues are truncations of a series.

### 6.4 Equivalent adic topologies

Ideals $I,J$ define the same topology if their powers are cofinal. If $I^r\subseteq J\subseteq I$, their topologies agree. In a Noetherian local ring any ideal with radical $\mathfrak m$ defines the same topology as $\mathfrak m$, since finite generation turns radical containment into containment of a power.

This does not make every topology on a local ring maximal-adic. In $\operatorname{CNL}_k$, “complete” means complete and separated for the maximal-ideal-adic topology.

### 6.5 Continuity of homomorphisms

Let $f:R\to S$, with $I$-adic topology on $R$ and $J$-adic topology on $S$. It is continuous exactly when for every $n$ there exists $m$ with

$$
f(I^m)\subseteq J^n.
$$

If $f$ is local between local rings carrying maximal-adic topologies, then $f(\mathfrak m_R^n)\subseteq\mathfrak m_S^n$, so it is automatically continuous. A map into an Artinian local ring is continuous for the discrete topology: if $\mathfrak m_A^N=0$, a local map kills $\mathfrak m_R^N$.

### 6.6 Abstract maps can be misleading

Continuity belongs to a map together with chosen topologies. Give $k[[x,y]]$ the $(x)$-adic topology as both source and target. The abstract automorphism interchanging $x$ and $y$ is not continuous: no power of the source ideal $(x)$ maps into the target ideal $(x)$. For maximal-adic local maps continuity is automatic, but it records the topological category in which universal properties are asserted.

## 7. Reconstruction from Artinian quotients

### 7.1 Why the finite shadows are Artinian

Let $(R,\mathfrak m,k)$ be Noetherian local. Each quotient $R/\mathfrak m^n$ is local Artinian. Indeed, its maximal ideal is nilpotent, and the filtration factors

$$
\mathfrak m^i/\mathfrak m^{i+1}
$$

are finite-dimensional over $k$: $\mathfrak m^i$ is finitely generated. Thus $R$ produces a tower

$$
\cdots\twoheadrightarrow R/\mathfrak m^3
\twoheadrightarrow R/\mathfrak m^2
\twoheadrightarrow R/\mathfrak m=k.
$$

These quotients are the infinitesimal neighborhoods of the closed point. Surjective transition maps make compatible lifting possible one order at a time.

### 7.2 Separation by Krull intersection

Noetherian locality supplies separation.

**Theorem (Krull intersection, local form).** If $(R,\mathfrak m)$ is Noetherian local and $M$ is a finitely generated $R$-module, then

$$
\bigcap_{n\geq0}\mathfrak m^nM=0.
$$

**Proof strategy.** Artin--Rees makes the intersection into a finite module equal to its product with $\mathfrak m$; Nakayama then annihilates it.

**Proof.** Put $N=\bigcap_n\mathfrak m^nM$. Artin--Rees applied to $N\subseteq M$ gives a $c$ such that

$$
N\cap\mathfrak m^nM=\mathfrak m^{n-c}(N\cap\mathfrak m^cM)
\quad(n\geq c).
$$

Since $N\subseteq\mathfrak m^nM$, taking $n=c+1$ yields $N=\mathfrak mN$. The module $N$ is finite because $R$ is Noetherian. Nakayama gives $N=0$. $\square$

Without Noetherianity or finite generation, maximal-adic separation is not automatic.

### 7.3 Completeness and reconstruction

A **complete Noetherian local ring** is a Noetherian local ring $R$ for which

$$
R\xrightarrow{\sim}\varprojlim_nR/\mathfrak m^n.
$$

Injectivity follows from Krull intersection; completeness is the surjectivity assertion. Its elements are exactly compatible finite-order approximations.

Two basic reconstructions should be kept in mind:

$$
\mathbf Z_p\cong\varprojlim_n\mathbf Z/p^n\mathbf Z,
\qquad
k[[t]]\cong\varprojlim_n k[t]/(t^n).
$$

The first reads a $p$-adic integer as compatible base-$p$ precision; the second reads a series as compatible truncations. By contrast, $k[t]_{(t)}$ maps injectively but not surjectively to the second limit. Its missing elements are genuine infinite series, even though it has the same quotient $k[t]/(t^n)$ at every finite order. This is the clearest example of why knowing all finite quotients up to individual isomorphism does not prove a ring complete: the canonical reconstruction map must be surjective.

Not every inverse limit of Artinian local rings is Noetherian. For example, set

$$
A_n=k[x_1,\ldots,x_n]/(x_1,\ldots,x_n)^n
$$

and map $A_{n+1}\twoheadrightarrow A_n$ by sending $x_{n+1}$ to zero and truncating at degree $n$. Every $A_n$ is Artinian local, but the limit has independent cotangent classes represented by $x_1,x_2,\ldots$, so its maximal ideal is not finitely generated. An inverse-limit platform needs a finiteness condition before it belongs to $\operatorname{CNL}_k$.

### 7.4 Reconstructing modules and quotients

If $R$ is complete Noetherian local and $M$ is finite, then

$$
M\xrightarrow{\sim}\varprojlim_nM/\mathfrak m^nM.
$$

A proof uses a finite presentation and exactness of completion on finite modules, established in Chapter 10. For an ideal $J\subseteq R$,

$$
J\cong\varprojlim_n J/(J\cap\mathfrak m^n),
$$

so $J$ is closed. Moreover $R/J$ is complete and

$$
R/J\cong\varprojlim_nR/(J+\mathfrak m^n).
$$

Noetherianity ensures $J$ is finite. Without it a submodule of a complete module need not be closed.

### 7.5 Compatible maps and their limit

Suppose $R,S$ are complete Noetherian local rings and compatible local maps

$$
f_n:R/\mathfrak m_R^n\longrightarrow S/\mathfrak m_S^n
$$

are given. Taking inverse limits gives a continuous local $f:R\to S$. More generally, the indices need not match: a continuous map is encoded by maps to every $S/\mathfrak m_S^n$, each factoring through some $R/\mathfrak m_R^{a(n)}$.

Compatibility is essential. Independently choosing a map at every order does not define a limit. The inverse-limit viewpoint turns convergence into algebraic coherence.

## 8. Continuous mapping properties

### 8.1 The universal property of completion

Let $R$ carry its $I$-adic topology and let $S$ be complete and separated for its $J$-adic topology. If $f:R\to S$ is continuous, meaning that for every $n$ some $m$ satisfies $f(I^m)\subseteq J^n$, then $f$ extends uniquely to

$$
\widehat f:\widehat R^{\,I}\longrightarrow S.
$$

**Proof strategy.** A compatible $I$-adic approximation gives compatible images in $S/J^n$; completeness supplies an element of $S$, and separation gives uniqueness because $R$ is dense in its completion. Ring operations hold at every finite level and hence in the limit. $\square$

This property explains why a polynomial map extends to formal series only when the images of variables are topologically nilpotent.

### 8.2 Maps are determined at finite level

For complete separated local rings $R,S$,

$$
\operatorname{Hom}_{\mathrm{cts,loc}}(R,S)
\xrightarrow{\sim}
\varprojlim_n\operatorname{Hom}_{\mathrm{loc}}(R,S/\mathfrak m_S^n),
$$

where the right side means compatible maps. Injectivity follows from separation. For surjectivity, evaluate a compatible family on each $r\in R$ and use $S\cong\varprojlim S/\mathfrak m_S^n$.

Every map on the right factors through some Artinian quotient of $R$, but the exponent may depend on $n$. Suppressing this dependence can accidentally impose a stronger filtration-preserving condition than continuity. In the maximal-adic local case one can take the same exponent because $f(\mathfrak m_R^n)\subseteq\mathfrak m_S^n$; the flexible formulation is retained for other ideals of definition.

### 8.3 Maps to finite rings

Let $A\in\operatorname{Art}_k$ and $\mathfrak m_A^N=0$. Every local map $R\to A$ kills $\mathfrak m_R^N$, and hence

$$
\operatorname{Hom}_{\mathrm{cts,loc},k}(R,A)
\cong\operatorname{Hom}_{\mathrm{loc},k}(R/\mathfrak m_R^N,A).
$$

One Artinian target never probes a complete source at infinite precision. Infinite structure appears through coherent behavior over all targets.

### 8.4 Dense subrings and a caution

If $R_0\to R$ has dense image and $S$ is Hausdorff, continuous maps $R\to S$ agreeing on $R_0$ agree everywhere. Existence of an extension requires images of Cauchy sequences to converge. The inclusion $k[t]\subset k[[t]]$ is dense. Evaluation $t\mapsto s\in S$ extends to all series when $s$ is topologically nilpotent in a sufficiently strong adic sense. The polynomial universal property permits arbitrary $s$; the series universal property does not.

### 8.5 Abstract versus continuous Hom

The set $\operatorname{Hom}_{\mathrm{Ring}}(R,S)$ forgets chosen ideals of definition and may include maps irrelevant to formal neighborhoods. The set $\operatorname{Hom}_{\mathrm{cts}}(R,S)$ encodes convergence, while $\operatorname{Hom}_{\mathrm{cts,loc},k}(R,S)$ additionally preserves the distinguished point and residue field. In the maximal-adic local setting the continuity condition follows from locality, but retaining it makes composition with more general topological constructions unambiguous.

## 9. Formal power-series rings

### 9.1 Why polynomial coordinates are insufficient

A complete local ring may contain elements defined by infinite recursive approximation. Polynomial rings cannot evaluate an infinite series, while formal power-series rings are designed so that terms of increasing degree tend to zero. They are the coordinate rings of formal neighborhoods and the free complete local algebras on finitely many infinitesimal parameters.

Let $(\mathcal O,\mathfrak m_{\mathcal O})$ be a complete Noetherian local ring. The ring

$$
\mathcal O[[x_1,\ldots,x_r]]
$$

consists of formal sums $\sum_\alpha a_\alpha x^\alpha$. It is local with maximal ideal

$$
\mathfrak n=(\mathfrak m_{\mathcal O},x_1,\ldots,x_r).
$$

The power-series ring is Noetherian and is complete and separated for the $\mathfrak n$-adic topology. Its residue field equals that of $\mathcal O$. The Noetherian hypothesis also ensures that the formal-series topology agrees with the topology defined by powers of the displayed maximal ideal.

### 9.2 Substitution and convergence

Suppose $S$ is complete separated for an ideal $J$, $f:\mathcal O\to S$ is continuous, and $s_1,\ldots,s_r\in J$. Then

$$
\sum_\alpha a_\alpha x^\alpha
\longmapsto
\sum_\alpha f(a_\alpha)s^\alpha
$$

defines a continuous homomorphism $\mathcal O[[\mathbf x]]\to S$. Modulo $J^n$, only finitely many monomials of total degree below $n$ contribute, so the sum is defined level by level. Completeness joins the levels; separation makes the value unique.

If the target is a complete local $\mathcal O$-algebra and each $s_i\in\mathfrak m_S$, the hypotheses hold. Sending a variable to a unit generally fails: the series $1+x+x^2+\cdots$ would demand a convergent geometric sum even when its terms do not tend to zero.

### 9.3 Universal mapping property

**Theorem.** For a complete separated local $\mathcal O$-algebra $S$,

$$
\operatorname{Hom}_{\mathrm{cts},\mathcal O}
(\mathcal O[[x_1,\ldots,x_r]],S)
\xrightarrow{\sim}\mathfrak m_S^r,
$$

where morphisms are local and the bijection sends a map to the images of the variables.

**Proof strategy.** Uniqueness follows from density of $\mathcal O[x_1,\ldots,x_r]$. Existence is substitution, whose convergence was checked modulo every power of $\mathfrak m_S$. $\square$

For an Artinian target the sum is literally finite because every sufficiently high-degree monomial in the $s_i$ vanishes. For example, a map $k[[x,y]]\to k[\epsilon]/(\epsilon^3)$ is determined by

$$
x\longmapsto a\epsilon+b\epsilon^2,
\qquad
y\longmapsto c\epsilon+d\epsilon^2.
$$

Substitution discards every monomial of total degree at least three. The four scalars $a,b,c,d$ encode first- and second-order data, while the target's nilpotence guarantees that no analytic convergence issue remains.

### 9.4 Quotients and closed ideals

If $I\subseteq\mathcal O[[\mathbf x]]$ is an ideal and the ring is Noetherian, then $I$ is closed and

$$
R=\mathcal O[[\mathbf x]]/I
$$

is complete Noetherian local exactly when $I$ is proper and contained in $(\mathfrak m_{\mathcal O},\mathbf x)$. A continuous $\mathcal O$-map $R\to S$ is the same as a tuple $\mathbf s\in\mathfrak m_S^r$ on which every series in $I$ vanishes.

The closedness qualification is essential outside Noetherian settings. Quotienting a complete topological ring by a nonclosed ideal produces a non-Hausdorff quotient; its separated completion is the quotient by the closure.

### 9.5 Presentations and embedding dimension

Let $R$ be a complete Noetherian local $k$-algebra with residue field $k$ and finite embedding dimension $r$. Choose elements $y_1,\ldots,y_r\in\mathfrak m_R$ lifting a basis of $\mathfrak m_R/\mathfrak m_R^2$. The universal property gives

$$
\phi:k[[x_1,\ldots,x_r]]\longrightarrow R,
\qquad x_i\mapsto y_i.
$$

This map is surjective. One proof first applies Nakayama to see $y_i$ generate $\mathfrak m_R$ as an ideal. Successive approximation then writes any $r\in R$ as a constant plus homogeneous polynomials in the $y_i$ to arbitrary order; completeness produces a power series and separation proves equality.

Thus

$$
R\cong k[[x_1,\ldots,x_r]]/I.
$$

When the coefficient ring is $\mathcal O$ rather than a field, the relative number of variables is

$$
\dim_k\frac{\mathfrak m_R}{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R},
$$

and lifts of a basis yield an $\mathcal O$-algebra surjection $\mathcal O[[\mathbf x]]\twoheadrightarrow R$, assuming the structural map is fixed and $R$ is topologically generated over $\mathcal O$.

### 9.6 Minimal presentations

A presentation from $k[[x_1,\ldots,x_r]]$ is **minimal** when the induced cotangent map is an isomorphism. This is equivalent to $I\subseteq(x_1,\ldots,x_r)^2$. A linear term in a relation eliminates a variable at first order; conversely, the absence of linear relations makes the variables a cotangent basis.

Embedding dimension measures the minimal number of formal coordinates, not the Krull dimension. For $k[[x]]/(x^n)$ the embedding dimension is one and the Krull dimension is zero. For $k[[x,y]]/(xy)$ both embedding and Krull dimensions are two and one respectively. The gap reflects equations, not a failure of the definition.

### 9.7 A mixed-coefficient example

Let $\mathcal O$ be a complete discrete valuation ring with uniformizer $\pi$. Then

$$
R=\mathcal O[[x,y]]/(xy-\pi)
$$

is complete Noetherian local with maximal ideal generated by $x,y$ because $\pi=xy$. Its special fiber is $k[[x,y]]/(xy)$, a nodal formal curve, while inverting $\pi$ makes both $x$ and $y$ nonzero. The example shows how a coefficient parameter can enter a relation rather than contribute an independent relative tangent direction.

## 10. Finite modules and topological Nakayama

### 10.1 Why algebraic finiteness controls topology

Completion is an inverse limit, and inverse limits are not exact in unrestricted settings. Noetherianity and finite generation force submodules to carry the expected induced topology, close images, and permit finite-stage data to reconstruct exact sequences. These are the hypotheses that make complete local algebra reliable.

### 10.2 Topological Nakayama

Let $R$ be complete and separated for an ideal $I$ contained in its Jacobson radical, and let $M$ be an $I$-adically complete and separated $R$-module. If finitely many elements $m_1,\ldots,m_r$ have images generating $M/IM$, then they generate $M$. In particular this applies to finite modules over a complete Noetherian ring.

**Proof strategy.** Approximate an element modulo $IM$, then correct the error modulo $I^2M$, and continue. The coefficients form Cauchy sequences in $R^r$, whose limits give an exact expression.

**Proof.** Let $\phi:R^r\to M$ send the standard basis to the $m_i$. Surjectivity modulo $I$ implies inductively that $\phi(R^r)+I^nM=M$ for all $n$. Choose compatible coefficient vectors approximating a given $m$ modulo $I^nM$, correcting at stage $n$ by an element of $I^nR^r$. Completeness of $R^r$ gives $a\in R^r$ and separatedness of $M$ gives $\phi(a)=m$. $\square$

The hypotheses prevent the earlier counterexample $k((t))/k[[t]]=t(k((t))/k[[t]])$: that module is neither finite nor separated complete in the required topology.

### 10.3 Artin--Rees and induced topology

Let $R$ be Noetherian, $I\subseteq R$, $M$ finite, and $N\subseteq M$. Artin--Rees supplies $c$ such that

$$
I^nM\cap N=I^{n-c}(I^cM\cap N)
\quad(n\geq c).
$$

Consequently the filtration $N\cap I^nM$ is cofinal with $I^nN$. Thus the topology induced on $N$ from $M$ agrees with its intrinsic $I$-adic topology. This is the decisive bridge from algebraic submodule to topological subspace.

### 10.4 Closed submodules and ideals

If $R$ is complete Noetherian $I$-adic and $M$ is finite, every submodule $N\subseteq M$ is closed, and $N$ and $M/N$ are complete for their intrinsic adic topologies. Indeed Artin--Rees identifies the induced topology, and exactness of completion preserves

$$
0\longrightarrow N\longrightarrow M\longrightarrow M/N\longrightarrow0.
$$

In particular every ideal of a complete Noetherian ring is closed. Infinite generation is the dangerous boundary: dense proper ideals can occur in nonnoetherian complete rings.

### 10.5 Exactness of completion

**Theorem.** Let $R$ be Noetherian, $I\subseteq R$, and

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

an exact sequence of finitely generated $R$-modules. Then

$$
0\longrightarrow\widehat{M'}\longrightarrow\widehat M
\longrightarrow\widehat{M''}\longrightarrow0
$$

is exact. Moreover $\widehat M\cong M\otimes_R\widehat R$.

**Proof strategy.** Right exactness follows from tensor products and inverse limits of surjective finite-level systems. The subtle point is injectivity; Artin--Rees makes the filtration on $M'$ cofinal with the induced filtration, so no element disappears unexpectedly. The tensor description is first checked for finite free modules and then passed through a finite presentation. $\square$

Completion need not be exact for arbitrary modules or over arbitrary rings. Thus later uses will always retain the Noetherian and finite-module assumptions.

### 10.6 Surjectivity and finite generation modulo the ideal

Let $f:M\to N$ be a map of finite modules over a complete Noetherian local ring. If $f\bmod\mathfrak m$ is surjective, then $f$ is surjective: apply Nakayama to $\operatorname{coker}f$. More generally, a compatible system of maps $M/\mathfrak m^nM\to N/\mathfrak m^nN$ defines a map $M\to N$ by completeness. If its first-stage map is surjective, then the limit map is surjective by the same Nakayama argument. This conclusion uses finite modules over one complete local ring; surjectivity of inverse limits is not automatic for arbitrary inverse systems.

### 10.7 Completion and quotients

For a finite module $M$ and submodule $N$ as above,

$$
\widehat{M/N}\cong\widehat M/\widehat N.
$$

For an ideal $J\subseteq R$,

$$
\widehat{R/J}^{\,I}
\cong \widehat R^{\,I}/J\widehat R^{\,I}.
$$

The right side is already separated because the extended ideal is closed. These formulas are the legitimate form of the slogan that completion commutes with finite algebraic constructions.

## 11. Completed tensor products

### 11.1 Why the ordinary tensor product is not enough

Tensor products combine two algebra structures over a common base. In the complete local category, however, $R\otimes_AS$ generally contains only finite sums of pure tensors and need not be complete for the topology dictated by the two maximal ideals. Formal families require infinite sums whose bidegrees tend to infinity. The **completed tensor product** adds precisely those limits.

The simplest example is

$$
k[[x]]\otimes_k k[[y]].
$$

It maps into $k[[x,y]]$, but it is not all of $k[[x,y]]$. An element of the tensor product is a finite sum $\sum_{i=1}^r f_i(x)g_i(y)$, so its infinite coefficient matrix has finite rank. The series

$$
\sum_{n\geq0}x^ny^{n^2}
$$

has coefficient matrix of infinite rank and cannot have this form. Completion supplies it, and in fact

$$
k[[x]]\widehat\otimes_k k[[y]]\cong k[[x,y]].
$$

### 11.2 Construction over a complete base

Let $(A,\mathfrak a)$ be complete Noetherian local, and let $R,S$ be complete Noetherian local $A$-algebras with local continuous structure maps. Write $\mathfrak m,\mathfrak n$ for their maximal ideals. A robust definition is

$$
R\widehat\otimes_A S
=\varprojlim_{p,q}
(R/\mathfrak m^p)\otimes_A(S/\mathfrak n^q),
$$

where the tensor products use the induced $A$-module structures. Equivalently one may complete $R\otimes_AS$ for

$$
K=\mathfrak m(R\otimes_AS)+\mathfrak n(R\otimes_AS)
$$

when standard Noetherian and finite-type hypotheses ensure these descriptions agree. If the $A$-maps are local, the image of $\mathfrak a$ is already contained in both summands.

The inverse limit in the definition always produces a complete separated topological $A$-algebra for the displayed finite-level topology, but it is not being asserted here that it is Noetherian or local in complete generality. Those conclusions require the residue and finite-generation hypotheses below. This distinction prevents properties of a power-series presentation from being silently transferred to an arbitrary completed tensor product.

In the commonly used topologically finite-type setting

$$
R=A[[\mathbf x]]/I,\qquad S=A[[\mathbf y]]/J,
$$

with closed finitely generated ideals, there is a concrete formula

$$
R\widehat\otimes_AS
\cong A[[\mathbf x,\mathbf y]]/(I,J).
$$

It proves at once that the result is complete Noetherian local.

### 11.3 Topology and residue field

Let $T=R\widehat\otimes_AS$ in the topologically finite-type setting, and assume the residue maps $R\to k$, $S\to k$ agree with $A\to k$. Then

$$
\mathfrak m_T=\overline{\mathfrak m_R T+\mathfrak m_S T}
$$

and $T/\mathfrak m_T\cong k$. In the Noetherian situation the sum ideal is finitely generated and hence closed, so the bar may be omitted. The topology on $T$ is its maximal-ideal-adic topology, which agrees with the completion topology used in the construction.

If the two residue fields differ over that of $A$, the tensor product of residue fields need not be a field, and the completed tensor product need not be local. Fixed residue-field compatibility is therefore structural, not decorative.

### 11.4 Universal property

Under the residue-compatible topologically finite-type hypotheses of Section 11.3, let $U$ be a complete separated local $A$-algebra. Continuous local $A$-maps

$$
R\widehat\otimes_AS\longrightarrow U
$$

correspond to pairs of continuous $A$-maps $R\to U$ and $S\to U$ whose images commute. Commutativity is automatic for our commutative rings. The forward direction restricts along $r\mapsto r\widehat\otimes1$ and $s\mapsto1\widehat\otimes s$. Conversely, multiplication gives $R\otimes_AS\to U$, and continuity plus completeness extends it uniquely.

The word continuous is decisive. The ordinary tensor product represents pairs of abstract maps into any ring. Its completion represents pairs whose induced map respects the chosen adic topology.

### 11.5 Associativity and symmetry

Under the preceding complete Noetherian, residue-compatible, topologically finite-type hypotheses, canonical continuous isomorphisms give

$$
R\widehat\otimes_AS\cong S\widehat\otimes_AR
$$

and

$$
(R\widehat\otimes_AS)\widehat\otimes_AT
\cong R\widehat\otimes_A(S\widehat\otimes_AT).
$$

The cleanest proof uses the universal property: both sides represent triples of compatible continuous $A$-maps into a complete target. Alternatively, power-series presentations reduce both sides to one quotient of $A[[\mathbf x,\mathbf y,\mathbf z]]$.

Without hypotheses guaranteeing that all completions and tensor products carry the asserted topologies, an unqualified associativity formula is unsafe. One should define the topology or use the universal property in a fixed category.

### 11.6 Base change and quotients

Let $A\to A'$ be a continuous local map of complete Noetherian rings and keep topological finite presentation assumptions. Completed base change is

$$
R_{A'}=R\widehat\otimes_AA'.
$$

It is characterized by the corresponding universal property over $A'$. If $R=A[[\mathbf x]]/I$, then

$$
R_{A'}\cong A'[[\mathbf x]]/\overline{IA'[[\mathbf x]]}.
$$

The closure is redundant when the extended ideal is finitely generated in a Noetherian target, but displaying it records the topological operation.

For a closed ideal $I\subseteq R$,

$$
(R/I)\widehat\otimes_AS
\cong(R\widehat\otimes_AS)/\overline{I(R\widehat\otimes_AS)}.
$$

Flatness is not automatic: completed base change preserves exact sequences under appropriate flatness and finite-module hypotheses, not merely because a completion symbol is present.

### 11.7 Finite-level construction

When $R,S$ are $k$-algebras with residue field $k$, one useful formula is

$$
R\widehat\otimes_kS
\cong\varprojlim_n
\bigl(R/\mathfrak m_R^n\bigr)\otimes_k
\bigl(S/\mathfrak m_S^n\bigr),
$$

where using separate indices gives the same limit by cofinality. The finite tensor product is Artinian local: its maximal ideal is generated by the two maximal ideals, is nilpotent, and its residue field is $k$. This exhibits the completed tensor product as a compatible totality of finite coefficient rings.

### 11.8 Three examples

First,

$$
k[[x_1,\ldots,x_r]]\widehat\otimes_k
k[[y_1,\ldots,y_s]]
\cong k[[x_1,\ldots,x_r,y_1,\ldots,y_s]].
$$

Second, if $R=k[[x]]/(x^a)$ and $S=k[[y]]/(y^b)$, then

$$
R\widehat\otimes_kS\cong k[[x,y]]/(x^a,y^b).
$$

This ring is already finite-dimensional, so completion changes nothing.

Third, over a complete discrete valuation ring $\mathcal O$,

$$
\mathcal O[[x]]\widehat\otimes_{\mathcal O}\mathcal O[[y]]/(y^2-\pi)
\cong\mathcal O[[x,y]]/(y^2-\pi).
$$

The coefficient uniformizer is shared, not duplicated. Tensoring over the residue field instead would describe a different problem and generally change characteristic.

## 12. Coefficient bases in equal and mixed characteristic

### 12.1 Why a residue field need not be a subring

Fixing $A/\mathfrak m_A\cong k$ identifies the closed fiber but does not choose representatives of elements of $k$ inside $A$. In equal characteristic a coefficient field may provide such representatives. In mixed characteristic it cannot: a characteristic-zero ring cannot contain a field of characteristic $p$ as a unital subring. A separate complete local coefficient base is the right replacement.

The **equal-characteristic** case means $\operatorname{char}R=\operatorname{char}k$. The **mixed-characteristic** case means $\operatorname{char}R=0$ and $\operatorname{char}k=p>0$, or at finite Artinian level that the characteristic is a positive power of $p$ while the residue characteristic is $p$.

### 12.2 Coefficient fields

A **coefficient field** of a complete local ring $(R,\mathfrak m,k)$ is a subfield $k_0\subseteq R$ whose composite to $R/\mathfrak m$ is an isomorphism. Choosing its inverse identifies $k$ with a subring of $R$ and makes $R$ a local $k$-algebra.

Examples $k[[\mathbf x]]/I$ come with a visible coefficient field. Existence for arbitrary complete equicharacteristic Noetherian local rings is a substantial structure theorem. It holds in the standard equicharacteristic complete Noetherian setting, but the choice need not be canonical. We use a coefficient field only when it is part of the data or when an existence theorem has explicitly been invoked.

Even when coefficient fields exist, morphisms need not preserve arbitrary choices. The residue-identification category avoids making noncanonical splittings functorial.

### 12.3 Cohen rings as mixed-characteristic bases

For a field $k$ of characteristic $p$, a **Cohen ring** for $k$ is, in a standard unramified form, a complete discrete valuation ring $\mathcal O$ of characteristic zero with maximal ideal $(p)$ and residue field $k$. When $k$ is perfect, the ring of Witt vectors $W(k)$ is the canonical example. For $k=\mathbf F_q$, it is the ring of integers in the unramified extension of $\mathbf Q_p$ with residue field $\mathbf F_q$.

For imperfect $k$, existence and uniqueness require additional choices and a more delicate formulation. We will not claim canonicity there. The safe platform is: fix a complete Noetherian local ring $\mathcal O$ and a specified residue isomorphism $\mathcal O/\mathfrak m_{\mathcal O}\cong k$, then work with local $\mathcal O$-algebras.

### 12.4 What structure is needed here

This book does not require the full Cohen structure theorem. The later coefficient formalism needs only the following input when mixed characteristic is intended:

1. a fixed complete Noetherian local base $\mathcal O$;
2. a chosen identification of its residue field with $k$;
3. local, continuous $\mathcal O$-algebra maps as morphisms;
4. power-series presentations over $\mathcal O$ for those rings known to be topologically generated by finitely many elements.

If $R$ is a complete Noetherian local $\mathcal O$-algebra with the same residue field and lifts $x_i$ span

$$
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R),
$$

then the induced map $\mathcal O[[X_1,\ldots,X_r]]\to R$ is surjective. The maximal ideal of the source is generated by $\mathfrak m_{\mathcal O}$ and the variables, so its map to the absolute cotangent space of $R$ is surjective. The complete cotangent criterion of Section 13.4 applies. This relative presentation statement is what coefficient-ring arguments actually use.

### 12.5 Ramified coefficient rings

A complete discrete valuation ring $\mathcal O$ may have uniformizer $\varpi$ with $p=u\varpi^e$. It still serves as a coefficient base with residue field $k$, although it is not an unramified Cohen ring when $e>1$. Deformation problems often fix such an $\mathcal O$ because it contains values of characters or matrix entries.

One should not replace $\mathcal O$ by $k$ without changing the category. The quotient $\mathcal O/\varpi^n$ remembers mixed-characteristic arithmetic that no augmented $k$-algebra can reproduce.

### 12.6 Teichmüller representatives and their limitation

For perfect $k$, $W(k)$ has multiplicative Teichmüller representatives $[a]$ satisfying $[ab]=[a][b]$ and reducing to $a$. They are not additive in general, so the set of representatives is not a coefficient field inside a characteristic-zero ring. Every Witt vector has a convergent expansion

$$
\sum_{n\geq0}p^n[a_n],
$$

but this is a digit expansion, not an embedding of $k$ as a ring. This distinction prevents a common but serious mixed-characteristic error.

## 13. Lifting and detecting homomorphisms

### 13.1 Why maps should be built one order at a time

A continuous map between complete rings is equivalent to compatible maps at all finite orders. This suggests constructing it inductively through the Artinian quotients. The method succeeds when each finite lifting problem is soluble and choices can be made compatibly; power-series sources are especially flexible because their maps are determined by freely chosen variable images.

### 13.2 Lifting maps out of power-series rings

Let $P=\mathcal O[[x_1,\ldots,x_r]]$ and let $A'\twoheadrightarrow A$ be a surjection of complete or Artinian local $\mathcal O$-algebras. Every continuous local $\mathcal O$-map $P\to A$ lifts to $P\to A'$: lift each image of $x_i\in\mathfrak m_A$ to an element of $\mathfrak m_{A'}$ and apply the universal property.

For a quotient $R=P/I$, a lift exists exactly when the chosen lifts of the variable images can be adjusted so that every element of $I$ vanishes. Across a small extension this becomes the Jacobian calculation of Section 5.7. Power-series rings are thus formally free; relations are the sole source of obstruction.

### 13.3 Compatible lifting along a tower

Let $S\cong\varprojlim S_n$ with surjective transition maps, where each $S_n$ is Artinian local. Suppose maps $f_n:R\to S_n$ can be chosen so that $f_{n+1}$ reduces to $f_n$. Then they define a unique continuous $R\to S$. Merely knowing that the set of maps to every $S_n$ is nonempty does not produce compatibility. A sufficient mechanism is that every transition map

$$
\operatorname{Hom}(R,S_{n+1})\longrightarrow\operatorname{Hom}(R,S_n)
$$

is surjective. This holds for a power-series source and can fail for a quotient with obstructing relations.

### 13.4 Surjectivity from cotangent spaces

**Theorem.** Let $f:R\to S$ be a continuous local homomorphism of complete Noetherian local rings inducing an isomorphism on residue fields. If the induced cotangent map

$$
\mathfrak m_R/\mathfrak m_R^2
\longrightarrow\mathfrak m_S/\mathfrak m_S^2
$$

is surjective, then $f$ is surjective.

**Proof strategy.** Cotangent surjectivity says $f(\mathfrak m_R)+\mathfrak m_S^2=\mathfrak m_S$. Nakayama makes $f(\mathfrak m_R)$ generate $\mathfrak m_S$ in the appropriate finite sense. Repeated approximation then expresses every target element as limits of source elements.

**Proof.** Cotangent surjectivity implies that the map on every graded layer is surjective: $\mathfrak m_S^n/\mathfrak m_S^{n+1}$ is generated by products of $n$ elements from $\mathfrak m_S/\mathfrak m_S^2$, and each factor lifts from $R$. Given $s\in S$, lift its residue to $r_0\in R$. Having chosen $r_0+\cdots+r_{n-1}$ whose image agrees with $s$ modulo $\mathfrak m_S^n$, use graded surjectivity to choose $r_n\in\mathfrak m_R^n$ correcting the error modulo $\mathfrak m_S^{n+1}$. The series $\sum_nr_n$ converges in $R$, and its image is $s$ by completeness and separation of $S$. $\square$

The completeness is indispensable: $k[t]_{(t)}\to k[[t]]$ is an isomorphism on cotangent spaces but not surjective.

### 13.5 Relative cotangent criterion

For a local map $\mathcal O\to R$, the correct relative cotangent space is

$$
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R).
$$

**Relative cotangent criterion.** Let $R\to S$ be a continuous local map of complete Noetherian local $\mathcal O$-algebras, and suppose that $R$ and $S$ have the same specified residue field and that the induced residue map is the identity. If

$$
\frac{\mathfrak m_R}{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R}
\longrightarrow
\frac{\mathfrak m_S}{\mathfrak m_S^2+\mathfrak m_{\mathcal O}S}
$$

is surjective, then $R\to S$ is surjective.

To reduce this to Section 13.4, observe that every element of $\mathfrak m_{\mathcal O}S$ is, modulo $\mathfrak m_S^2$, in the image of $\mathfrak m_R$. Indeed, for a term $as$ with $a\in\mathfrak m_{\mathcal O}$, choose $r\in R$ having the same residue as $s$. Then $a(s-f(r))\in\mathfrak m_S^2$, while $af(r)=f(ar)$ comes from $\mathfrak m_R$. Relative cotangent surjectivity therefore implies absolute cotangent surjectivity, and the complete criterion applies. Omitting $\mathfrak m_{\mathcal O}R$ in the relative space would incorrectly count coefficient directions as variables.

### 13.6 Detecting isomorphisms

Surjectivity on cotangent spaces does not imply injectivity. The quotient

$$
k[[x]]\twoheadrightarrow k[[x]]/(x^2)
$$

induces an isomorphism on cotangent spaces but has nonzero kernel. Even isomorphisms $R/\mathfrak m_R^2\cong S/\mathfrak m_S^2$ do not determine higher relations.

A reliable criterion is finite-level.

**Proposition.** A continuous local map $f:R\to S$ of complete separated local rings is an isomorphism if it induces isomorphisms

$$
R/\mathfrak m_R^n\xrightarrow{\sim}S/\mathfrak m_S^n
$$

for every $n$, compatibly with the transition maps.

**Proof.** Take inverse limits and use completeness and separation. $\square$

Another common criterion starts with a known surjection $R\twoheadrightarrow S$: it is an isomorphism exactly when its closed kernel is zero, and Krull intersection can detect zero if the kernel maps to zero at every finite level. Cotangent information alone detects generators, not all relations.

### 13.7 Associated graded tests

A local map gives

$$
\operatorname{gr}_{\mathfrak m_R}R
\longrightarrow\operatorname{gr}_{\mathfrak m_S}S.
$$

If this graded map is surjective and both rings are complete and separated, then $f$ is surjective by successive approximation. If it is an isomorphism and the maximal-ideal filtrations are separated and complete, then $f$ is an isomorphism. This criterion uses every infinitesimal layer, not merely degree one.

The proof lifts a target element degree by degree. Injectivity follows because a nonzero kernel element would have a first nonzero initial form, contradicting graded injectivity. Exhaustiveness and separation are what make “first nonzero order” and convergence legitimate.

## 14. Pro-objects at the concrete inverse-limit level

### 14.1 Why an infinite ring can act on finite tests

The test category contains only Artinian rings, yet a universal coefficient ring is usually not Artinian. There is no contradiction: a complete ring acts through its entire tower of Artinian quotients. The prefix “pro” packages the idea of an object known through all finite approximations.

We need only a concrete version. An **inverse system of Artinian coefficient rings** is a family $(R_i)$ indexed by a directed ordered set, with compatible transition maps $R_j\to R_i$ for $j\geq i$. In the principal example,

$$
R_n=R/\mathfrak m_R^n.
$$

The formal pro-object is the system itself. Its inverse limit is an actual topological ring when the limit exists in rings, but the pro-object and the underlying abstract limit ring are conceptually different: the system remembers which quotients define the topology.

### 14.2 Morphisms of inverse systems

The correct morphism from $(R_i)$ to $(S_j)$ allows each finite target stage $S_j$ to be reached from some sufficiently fine source stage $R_i$. Concretely,

$$
\operatorname{Hom}_{\mathrm{Pro}}((R_i),(S_j))
=\varprojlim_j\varinjlim_i
\operatorname{Hom}_{\operatorname{Art}_k}(R_i,S_j).
$$

The order of limit and colimit expresses two requirements. For each $j$ one may choose a sufficiently large $i$, and the resulting maps must be compatible as $j$ varies. Reversing the order would impose one source stage that works simultaneously for every target precision, which is generally too strong.

For towers arising from complete Noetherian local rings $R,S$, this pro-morphism set is naturally the set of continuous local residue-compatible maps $R\to S$. A map to $S/\mathfrak m_S^j$ factors through some $R/\mathfrak m_R^i$, and compatibility reconstructs the complete map.

### 14.3 The functor attached to a complete ring

For $R\in\operatorname{CNL}_k$, define

$$
h_R(A)=\operatorname{Hom}_{\mathrm{cts,loc},k}(R,A),
\qquad A\in\operatorname{Art}_k.
$$

Because $A$ is Artinian, this is equivalently

$$
h_R(A)=\varinjlim_n
\operatorname{Hom}_{\operatorname{Art}_k}(R/\mathfrak m_R^n,A).
$$

A coefficient map $A\to B$ sends $f:R\to A$ to its composite $R\to B$, so $h_R$ is covariant in the test ring. A continuous map $R\to S$ induces a natural transformation

$$
h_S\longrightarrow h_R
$$

by precomposition. Thus representing rings vary contravariantly.

### 14.4 What pro-representation means

A set-valued functor $F$ on $\operatorname{Art}_k$ is **pro-represented** by $R\in\operatorname{CNL}_k$ if there is a natural isomorphism

$$
F(A)\cong h_R(A)
$$

for every $A$. This is a definition of the categorical platform, not a criterion ensuring that a given functor has such an $R$. The existence criteria and the deformation functors to which they apply belong to later developments.

If $R$ pro-represents $F$, an element over $A$ corresponds to a continuous coefficient map $R\to A$. Base change is composition. The universal compatible element is visible through the identity maps of the finite quotients $R/\mathfrak m_R^n$; no single Artinian ring contains it at every order.

### 14.5 Uniqueness of the pro-representing ring

If $h_R\cong h_S$ naturally, then $R\cong S$ as complete local topological rings. One may see this by applying the natural maps to the compatible identity classes on all finite quotients. They produce continuous maps $R\to S$ and $S\to R$, and naturality forces their composites to induce the identity at every finite level. Completeness and separation then make the composites identities.

This is the complete-local form of the Yoneda principle. Topology cannot be discarded: the functor sees the inverse systems of Artinian quotients and therefore determines the adic topological ring.

### 14.6 Tangent space of a represented functor

Without introducing any deformation problem, one can calculate the first test value of $h_R$. In the augmented equal-characteristic setting,

$$
h_R(k[\epsilon]/(\epsilon^2))
\cong\operatorname{Hom}_k(\mathfrak m_R/\mathfrak m_R^2,k).
$$

A map must send $r$ to $\bar r+d(r)\epsilon$, and multiplicativity makes $d$ a derivation. Thus the tangent space of the functor represented by $R$ is dual to the cotangent space of $R$. Over a coefficient base $\mathcal O$, the relative cotangent quotient

$$
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R)
$$

appears instead, with the appropriate square-zero test algebra.

Finite tangent dimension is therefore necessary for representation by a complete Noetherian local ring. It is far from sufficient: tangent information controls generators, while compatibility across small extensions controls relations and obstructions.

### 14.7 Fiber products and functorial gluing

Let $A'\to A\leftarrow A''$ be a diagram in $\operatorname{Art}_k$ with one arrow surjective. For any complete $R$,

$$
h_R(A'\times_AA'')
\cong h_R(A')\times_{h_R(A)}h_R(A'').
$$

This follows directly from the universal property of the ring fiber product: a map $R\to A'\times_AA''$ is a compatible pair. Thus every represented functor preserves these pullbacks. The assertion is a necessary structural property of representability, but analyzing when a general functor has it belongs beyond this coefficient-ring book.

### 14.8 Products of coefficient problems

If $R$ and $S$ are complete local $k$-algebras satisfying the hypotheses of Chapter 11, then

$$
h_{R\widehat\otimes_kS}(A)
\cong h_R(A)\times h_S(A).
$$

The completed tensor product represents the product of the two mapping functors because a map out of it is a pair of maps from its factors. This formula is the formal analogue of combining independent sets of parameters. Over a coefficient base $\mathcal O$, replace $k$ by $\mathcal O$ and use relative completed tensor products.

### 14.9 Presentations as generators and relations for functors

Suppose

$$
R=\mathcal O[[x_1,\ldots,x_r]]/(f_1,\ldots,f_s).
$$

Then $h_R(A)$ is the set of tuples $(a_1,\ldots,a_r)\in\mathfrak m_A^r$ satisfying

$$
f_j(a_1,\ldots,a_r)=0\quad(1\leq j\leq s).
$$

The variables give possible infinitesimal choices and the equations give compatibility conditions. Across a small extension, linearizing these equations produces the Jacobian map of Chapter 5. This does not assert that every naturally occurring functor admits such a presentation; it explains exactly what a presentation means once a representing ring is known.

### 14.10 The boundary with later theory

The coefficient platform now provides:

- finite local test objects and their fiber products;
- principal small extensions for induction;
- square-zero linearization and cotangent spaces;
- complete rings reconstructed from finite quotients;
- continuous maps and topological presentations;
- completed tensor products for combining coefficient systems;
- concrete pro-representing functors.

What it deliberately does not provide is a particular deformation assignment, a cohomological formula for its tangent or obstruction spaces, criteria guaranteeing a hull or universal ring, or a treatment of automorphisms of deformed objects. Those questions require additional structure. The present book ensures they can be asked without rebuilding the coefficient algebra each time.

## 15. The reusable coefficient-ring dictionary

### 15.1 Residue and locality

The distinguished point of $(A,\mathfrak m_A)$ is $A\to k_A=A/\mathfrak m_A$. A map $A\to B$ is local exactly when the inverse image of $\mathfrak m_B$ is $\mathfrak m_A$. It then induces $k_A\to k_B$. In a fixed-residue category this induced map must agree with the chosen identity on $k$.

Units are detected at the closed point:

$$
A^\times=A\setminus\mathfrak m_A.
$$

A residue-field identification is not a coefficient-field embedding. The former is always part of the category; the latter is extra equal-characteristic structure.

### 15.2 Artinian diagnostics

For an Artinian local ring,

$$
\mathfrak m_A^N=0
$$

for some $N$, and

$$
\ell_A(A)=\sum_i\dim_k\mathfrak m_A^i/\mathfrak m_A^{i+1}.
$$

Every finite $A$-module has a terminating maximal-ideal filtration. Morphisms respect all layers. The cotangent space $\mathfrak m_A/\mathfrak m_A^2$ detects the minimal number of generators of $\mathfrak m_A$, but not higher relations or length.

### 15.3 Tangent and differential translations

For an augmented local $k$-algebra,

$$
\Omega_{A/k}\otimes_Ak\cong\mathfrak m_A/\mathfrak m_A^2,
$$

and

$$
\operatorname{Hom}_{k\text{-alg},k}
(A,k[\epsilon]/(\epsilon^2))
\cong\operatorname{Hom}_k(\mathfrak m_A/\mathfrak m_A^2,k).
$$

For a presentation $P/J$, the conormal sequence

$$
J/J^2\to\Omega_{P/k}\otimes_P(P/J)\to\Omega_{(P/J)/k}\to0
$$

turns equations into linear differential relations. It is right exact; the left arrow is not generally injective.

### 15.4 Small-extension protocol

A small extension $A'\twoheadrightarrow A$ has kernel $I$ with

$$
\mathfrak m_{A'}I=0,
$$

so $I$ is a finite-dimensional $k$-space and $I^2=0$. It is principal when $\dim_kI=1$. Every surjection in $\operatorname{Art}_k$ factors into finitely many principal small extensions, by choosing one-dimensional socle ideals successively.

Square-zero alone is weaker than smallness. Across a square-zero extension, differences of lifts are derivations. Across a small extension, polynomial errors linearize over $k$. These are the two facts used in induction on Artinian thickness.

### 15.5 Fiber products and variance

If $A'\to A\leftarrow A''$ has one surjective leg, then $A'\times_AA''$ is again an Artinian local $k$-ring, with

$$
\mathfrak m_{A'\times_AA''}
=\mathfrak m_{A'}\times_{\mathfrak m_A}\mathfrak m_{A''}.
$$

Coefficient change $A\to B$ acts forward on objects over coefficients, so test-ring functors are covariant. A representing ring $R$ gives $h_R(A)=\operatorname{Hom}(R,A)$, covariant in $A$ and contravariant in $R$.

### 15.6 Completeness checklist

For an ideal $I$, the statements

$$
\bigcap_nI^n=0,
\qquad
R\xrightarrow{\sim}\varprojlim_nR/I^n
$$

mean separatedness and complete separatedness respectively. They concern the $I$-adic topology, not an arbitrary topology on the same ring. In a Noetherian local ring, Krull intersection gives maximal-adic separation; completeness still asserts surjectivity onto the inverse limit.

A complete Noetherian local ring satisfies

$$
R\cong\varprojlim_nR/\mathfrak m_R^n,
$$

and each quotient is Artinian local. A finite module $M$ similarly satisfies

$$
M\cong\varprojlim_nM/\mathfrak m_R^nM.
$$

Noetherianity and finite generation are the standard safeguards behind these reconstructions.

### 15.7 Continuity checklist

For $I$-adic $R$ and $J$-adic $S$, a map $f:R\to S$ is continuous exactly when for every $n$ some $m$ satisfies $f(I^m)\subseteq J^n$. A local map between maximal-adic local rings satisfies the stronger relation

$$
f(\mathfrak m_R^n)\subseteq\mathfrak m_S^n.
$$

A local map to an Artinian target is automatically continuous and factors through a finite quotient of the source. Maps between complete rings are determined by compatible maps to all finite quotients of the target.

### 15.8 Presentation checklist

If $R$ is a complete Noetherian local $k$-algebra with coefficient field $k$ and embedding dimension $r$, then

$$
k[[x_1,\ldots,x_r]]\twoheadrightarrow R.
$$

The presentation is minimal when its kernel lies in $(x_1,\ldots,x_r)^2$. Relative to a coefficient base $\mathcal O$, use

$$
\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R)
$$

to count variables. A tuple in a target maximal ideal defines a unique map out of a power-series ring; it factors through a quotient precisely when the defining relations vanish.

### 15.9 Finite-module topology checklist

Over a Noetherian ring, Artin--Rees identifies the topology induced on a finite submodule with its intrinsic adic topology. Completion is exact on finite modules, finite submodules of complete modules are closed, and finite quotients remain complete. None of these conclusions should be transferred without hypotheses to arbitrary modules or nonnoetherian rings.

Topological Nakayama lifts a finite list of generators from $M/IM$ by successive approximation when $R$ and $M$ are complete and separated in their $I$-adic topologies. Finite generation of $M$ is a standard sufficient setting, but the stated topological form requires only the finite list modulo $I$ and the completeness hypotheses.

### 15.10 Completed tensor checklist

The ordinary tensor product solves an algebraic universal problem; the completed tensor product solves its continuous analogue. In the complete Noetherian topologically finite-type setting,

$$
(A[[\mathbf x]]/I)\widehat\otimes_A
(A[[\mathbf y]]/J)
\cong A[[\mathbf x,\mathbf y]]/(I,J).
$$

Residue compatibility keeps the result local with residue field $k$. Associativity, symmetry, base change, and quotient formulas hold in the fixed complete category under the stated Noetherian and finite-type hypotheses. Closures must be retained when finite generation is absent.

### 15.11 Map-detection checklist

For maps of complete Noetherian local rings with the same residue field:

- surjectivity on cotangent spaces implies surjectivity, by complete successive approximation;
- cotangent isomorphism alone does not imply ring isomorphism;
- an isomorphism on every Artinian quotient implies an isomorphism of complete rings;
- an isomorphism on associated graded rings implies an isomorphism when the filtrations are complete and separated.

The first layer detects generators. Every layer together detects the filtered ring.

### 15.12 Pro-representation checklist

The tower $(R/\mathfrak m_R^n)_n$ gives

$$
h_R(A)=\varinjlim_n
\operatorname{Hom}(R/\mathfrak m_R^n,A).
$$

Natural transformations $h_S\to h_R$ correspond contravariantly to continuous maps $R\to S$. Fiber products of Artinian targets are carried to fiber products of sets, while completed tensor products of representing rings correspond to products of represented functors. This is the exact categorical infrastructure needed before any specific deformation problem is introduced.

### 15.13 Conclusion

Local algebra organizes infinitesimal information around one closed point. Artinian rings reveal that point in finitely many nilpotent layers, small extensions isolate one linear step, and derivations explain how choices vary across that step. Complete Noetherian local rings gather every finite layer into a single separated object; continuity guarantees that maps respect this gathering rather than merely the underlying abstract rings.

Formal power-series presentations then turn parameters into coordinates and ideals into relations. Topological Nakayama and Artin--Rees make the passage between finite algebra and infinite limits dependable. Completed tensor products combine compatible formal coefficient systems without discarding convergent infinite expressions. Equal and mixed characteristic fit the same architecture once residue identifications are distinguished from coefficient fields and a coefficient base is fixed where necessary.

The result is a coherent two-scale language. At finite scale, one can induct through principal small extensions and calculate first-order change. At complete scale, one can reconstruct rings and maps from compatible Artinian quotients. The two scales meet in the functor $A\mapsto\operatorname{Hom}_{\mathrm{cts,loc}}(R,A)$: each test is finite, while the representing ring remembers all tests at once. That is the coefficient-ring foundation on which deformation theory can build.
