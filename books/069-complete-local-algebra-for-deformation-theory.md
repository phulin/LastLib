# Complete Local Algebra for Deformation Theory

## Contents

1. [The local algebra behind a universal object](#1-the-local-algebra-behind-a-universal-object)
   - [From representability to equations](#11-from-representability-to-equations)
   - [The coefficient conventions](#12-the-coefficient-conventions)
   - [Continuity and finite shadows](#13-continuity-and-finite-shadows)
   - [The three numerical questions](#14-the-three-numerical-questions)
2. [Cotangent spaces and infinitesimal directions](#2-cotangent-spaces-and-infinitesimal-directions)
   - [Why first-order neighborhoods are linear](#21-why-first-order-neighborhoods-are-linear)
   - [Absolute cotangent and Zariski tangent spaces](#22-absolute-cotangent-and-zariski-tangent-spaces)
   - [Relative cotangent spaces](#23-relative-cotangent-spaces)
   - [The coefficient direction in mixed characteristic](#24-the-coefficient-direction-in-mixed-characteristic)
   - [Functoriality and exact sequences](#25-functoriality-and-exact-sequences)
   - [The conormal sequence at the closed point](#26-the-conormal-sequence-at-the-closed-point)
   - [Examples and first warnings](#27-examples-and-first-warnings)
3. [Topological Nakayama and minimal generation](#3-topological-nakayama-and-minimal-generation)
   - [Why ordinary generation is not visibly enough](#31-why-ordinary-generation-is-not-visibly-enough)
   - [Topological Nakayama with exact hypotheses](#32-topological-nakayama-with-exact-hypotheses)
   - [Finite modules over complete local rings](#33-finite-modules-over-complete-local-rings)
   - [Minimal generators of modules and ideals](#34-minimal-generators-of-modules-and-ideals)
   - [Topological generators of algebras](#35-topological-generators-of-algebras)
   - [What fails without completeness or finiteness](#36-what-fails-without-completeness-or-finiteness)
4. [Cohen structure, formal coordinates, and minimal presentations](#4-cohen-structure-formal-coordinates-and-minimal-presentations)
   - [Why formal power series are the correct source](#41-why-formal-power-series-are-the-correct-source)
   - [The coefficient-ring theorem](#42-the-coefficient-ring-theorem)
   - [The Cohen presentation theorem](#43-the-cohen-presentation-theorem)
   - [Cohen presentations are not canonical](#44-cohen-presentations-are-not-canonical)
   - [Building a presentation from tangent lifts](#45-building-a-presentation-from-tangent-lifts)
   - [Minimality over a field](#46-minimality-over-a-field)
   - [Minimality over a coefficient ring](#47-minimality-over-a-coefficient-ring)
   - [Changes of coordinates and uniqueness information](#48-changes-of-coordinates-and-uniqueness-information)
   - [Worked presentations](#49-worked-presentations)
5. [Relation modules and the number of equations](#5-relation-modules-and-the-number-of-equations)
   - [Why an ideal is not yet a count of relations](#51-why-an-ideal-is-not-yet-a-count-of-relations)
   - [The minimal relation module](#52-the-minimal-relation-module)
   - [Relations in the conormal sequence](#53-relations-in-the-conormal-sequence)
   - [Relative and special-fiber relation counts](#54-relative-and-special-fiber-relation-counts)
   - [Changing a presentation](#55-changing-a-presentation)
   - [Examples and counterexamples](#56-examples-and-counterexamples)
   - [Relation modules, syzygies, and redundancy](#57-relation-modules-syzygies-and-redundancy)
   - [Relative relation modules for a map](#58-relative-relation-modules-for-a-map)
   - [The universal small extension attached to a relation](#59-the-universal-small-extension-attached-to-a-relation)
6. [Krull dimension in the complete local setting](#6-krull-dimension-in-the-complete-local-setting)
   - [Dimension as chains of irreducible constraints](#61-dimension-as-chains-of-irreducible-constraints)
   - [Prime chains and quotients](#62-prime-chains-and-quotients)
   - [Power-series dimensions](#63-power-series-dimensions)
   - [Generator--relation inequalities](#64-generator--relation-inequalities)
   - [Height, minimal primes, and equality](#65-height-minimal-primes-and-equality)
   - [Dimension is not embedding dimension](#66-dimension-is-not-embedding-dimension)
7. [Regular local rings](#7-regular-local-rings)
   - [The smallest possible cotangent space](#71-the-smallest-possible-cotangent-space)
   - [Equivalent characterizations](#72-equivalent-characterizations)
   - [The associated graded criterion](#73-the-associated-graded-criterion)
   - [Complete regular rings and coefficient bases](#74-complete-regular-rings-and-coefficient-bases)
   - [Detecting singularity in examples](#75-detecting-singularity-in-examples)
   - [From regularity to regular sequences](#76-from-regularity-to-regular-sequences)
8. [Parameters, depth, and complete intersections](#8-parameters-depth-and-complete-intersections)
   - [Why dimension needs concrete witnesses](#81-why-dimension-needs-concrete-witnesses)
   - [Systems of parameters](#82-systems-of-parameters)
   - [Existence and dimension cutting](#83-existence-and-dimension-cutting)
   - [Parameter ideals and finite quotients](#84-parameter-ideals-and-finite-quotients)
   - [Examples and limitations](#85-examples-and-limitations)
   - [Non-zero-divisors and regular sequences](#86-non-zero-divisors-and-regular-sequences)
   - [Depth and Cohen--Macaulay rings](#87-depth-and-cohen--macaulay-rings)
   - [Regular local rings are Cohen--Macaulay](#88-regular-local-rings-are-cohen--macaulay)
   - [Quotients by regular sequences](#89-quotients-by-regular-sequences)
   - [Complete intersections](#810-complete-intersections)
   - [Regular sequences under flat base change](#811-regular-sequences-under-flat-base-change)
9. [Finite local homomorphisms](#9-finite-local-homomorphisms)
   - [Why finite maps matter](#91-why-finite-maps-matter)
   - [Integrality, lying over, and going up](#92-integrality-lying-over-and-going-up)
   - [The exact dimension formula](#93-the-exact-dimension-formula)
   - [Faithfully finite maps](#94-faithfully-finite-maps)
   - [Residue fields and maximal ideals](#95-residue-fields-and-maximal-ideals)
   - [Finite maps and completion](#96-finite-maps-and-completion)
   - [Finite does not mean quotient](#97-finite-does-not-mean-quotient)
10. [Finite modules as geometric detectors](#10-finite-modules-as-geometric-detectors)
    - [Support and annihilators](#101-support-and-annihilators)
   - [Faithful modules](#102-faithful-modules)
   - [What reduction modulo the maximal ideal detects](#103-what-reduction-modulo-the-maximal-ideal-detects)
   - [Closed submodules and exact limits](#104-closed-submodules-and-exact-limits)
   - [Examples of support and failure of detection](#105-examples-of-support-and-failure-of-detection)
   - [Why coefficient flatness is torsion control](#106-why-coefficient-flatness-is-torsion-control)
   - [Finite flat modules are free](#107-finite-flat-modules-are-free)
   - [The torsion exact sequence and specialization](#108-the-torsion-exact-sequence-and-specialization)
   - [Flatness of a presented algebra](#109-flatness-of-a-presented-algebra)
   - [Dimension of special and generic fibers](#1010-dimension-of-special-and-generic-fibers)
   - [Exactness under completed scalar extension](#1011-exactness-under-completed-scalar-extension)
11. [Completed tensor products](#11-completed-tensor-products)
   - [Combining two formal local problems](#111-combining-two-formal-local-problems)
   - [Construction and universal property](#112-construction-and-universal-property)
   - [Noetherianity and locality](#113-noetherianity-and-locality)
    - [Relative tangent spaces add](#114-relative-tangent-spaces-add)
   - [Dimension over a field](#115-dimension-over-a-field)
   - [Dimension over a discrete valuation ring](#116-dimension-over-a-discrete-valuation-ring)
   - [Examples and topology warnings](#117-examples-and-topology-warnings)
   - [Fiber products solve a different problem](#118-fiber-products-solve-a-different-problem)
   - [Locality, completeness, and the exact sequence](#119-locality-completeness-and-the-exact-sequence)
   - [Prime spectra and dimension of a fiber product](#1110-prime-spectra-and-dimension-of-a-fiber-product)
   - [Cotangent spaces of fiber products](#1111-cotangent-spaces-of-fiber-products)
   - [Fiber products in lifting arguments](#1112-fiber-products-in-lifting-arguments)
12. [Base change and formal smoothness](#12-base-change-and-formal-smoothness)
    - [Base-changing a presentation](#121-base-changing-a-presentation)
    - [Cotangent spaces after coefficient extension](#122-cotangent-spaces-after-coefficient-extension)
    - [When relation counts survive base change](#123-when-relation-counts-survive-base-change)
    - [Formal smoothness as a lifting property](#124-formal-smoothness-as-a-lifting-property)
    - [The power-series characterization](#125-the-power-series-characterization)
    - [The functorial interpretation](#126-the-functorial-interpretation)
13. [From tangent and obstruction spaces to equations](#13-from-tangent-and-obstruction-spaces-to-equations)
    - [Tangent dimension counts variables](#131-tangent-dimension-counts-variables)
    - [When obstruction dimension bounds relations](#132-when-obstruction-dimension-bounds-relations)
    - [The basic dimension bound](#133-the-basic-dimension-bound)
   - [What cohomology does not determine](#134-what-cohomology-does-not-determine)
   - [Unobstructed problems](#135-unobstructed-problems)
   - [Framed and fixed-determinant bookkeeping](#136-framed-and-fixed-determinant-bookkeeping)
   - [Relative tangent and obstruction theory](#137-relative-tangent-and-obstruction-theory)
   - [Local products and the global presentation](#138-local-products-and-the-global-presentation)
   - [Balanced presentations](#139-balanced-presentations)
14. [A gallery of deformation-shaped local rings](#14-a-gallery-of-deformation-shaped-local-rings)
    - [A smooth universal ring](#141-a-smooth-universal-ring)
    - [A fat infinitesimal direction](#142-a-fat-infinitesimal-direction)
    - [A nodal relation](#143-a-nodal-relation)
    - [A mixed-characteristic smoothing](#144-a-mixed-characteristic-smoothing)
    - [A finite normalization-shaped map](#145-a-finite-normalization-shaped-map)
    - [A completed product of constrained problems](#146-a-completed-product-of-constrained-problems)
15. [The patching dictionary](#15-the-patching-dictionary)
    - [Reading cohomology as a presentation](#151-reading-cohomology-as-a-presentation)
   - [Reading a ring map](#152-reading-a-ring-map)
   - [Reading completed products](#153-reading-completed-products)
   - [A disciplined numerical workflow](#154-a-disciplined-numerical-workflow)
   - [Balance plus finiteness over a regular base](#155-balance-plus-finiteness-over-a-regular-base)
   - [The local-to-global numerical package](#156-the-local-to-global-numerical-package)
   - [A faithful patched module controls its ring](#157-a-faithful-patched-module-controls-its-ring)
   - [Augmentation and descent to finite level](#158-augmentation-and-descent-to-finite-level)
   - [Conclusion](#159-conclusion)

## 1. The local algebra behind a universal object

### 1.1 From representability to equations

Book 62 established the coefficient rings on which deformation theory lives: local Artinian rings record finite infinitesimal thickness, and complete Noetherian local rings assemble all thicknesses at once. We now study what can be deduced whenever a deformation problem is represented by such a complete ring. Existence and the calculation of particular tangent and obstruction spaces are separate inputs; the question here is what their algebra says once they are available.

Three transitions drive the subject. A tangent calculation should become a count of formal coordinates. A complete, functorial linear obstruction theory should become a bound on equations. A map between deformation problems should become a local homomorphism whose finiteness, dimension, or surjectivity can be checked. None of these transitions is automatic. They require a careful distinction between absolute and coefficient-relative directions, between a chosen presentation and a minimal one, and between a finite map and a faithfully finite map.

The purpose of this book is to make those transitions reliable. The guiding picture is a presentation

$$
R\simeq \mathcal O[[X_1,\ldots,X_r]]/(f_1,\ldots,f_s),
$$

but this picture is useful only after every symbol has been justified. Why are there $r$ variables? In what sense are the $f_j$ minimal? Does $s$ give a dimension drop of exactly $s$, or only at most $s$? What happens to the presentation after changing coefficients or combining two local problems? These are the questions that follow.

The narrative moves from Cohen coefficient rings and minimal presentations to relation modules and dimension, then to regular sequences, complete intersections, and coefficient flatness. Completed tensor products combine independent local conditions, while fiber products glue compatible reductions. The final chapters place a global ring over the completed product of its local rings and prove the exact balanced-presentation and faithful-module criteria used to force complete-intersection and freeness conclusions in patching.

### 1.2 The coefficient conventions

Fix either a field $k$, or a complete discrete valuation ring $(\mathcal O,(\varpi),k)$ with residue field $k$. More generally, several purely algebraic statements hold for a complete Noetherian local base $(\mathcal O,\mathfrak m_{\mathcal O},k)$, and we state them at that level when no discrete valuation is needed. Every ring is commutative with identity.

An **admissible complete local $\mathcal O$-algebra** is a complete Noetherian local ring $(R,\mathfrak m_R)$ equipped with a continuous local map $\mathcal O\to R$ inducing the specified identity on residue fields. Morphisms are continuous local $\mathcal O$-homomorphisms inducing the identity on $k$. Completeness includes separatedness:

$$
R\xrightarrow{\sim}\varprojlim_n R/\mathfrak m_R^n,
\qquad
\bigcap_n\mathfrak m_R^n=0.
$$

When $\mathcal O=k$, the structural map is a coefficient field and the relative and absolute theories coincide. When $\mathcal O$ is a discrete valuation ring, $\varpi$ is a coefficient parameter. It may remain a genuine tangent direction in $R$, fall into $\mathfrak m_R^2$, or vanish. Relative invariants deliberately ignore it; absolute invariants do not.

Book 62 supplied the fixed-base coefficient formalism. Chapter 4 proves the coefficient-ring existence theorem needed to place an arbitrary complete Noetherian local ring into that formalism. In equal characteristic a chosen coefficient field permits presentations over $k$; in mixed characteristic a chosen complete coefficient ring supplies the base. Neither choice is generally canonical, and all relative power-series presentations remember the displayed structural map.

### 1.3 Continuity and finite shadows

The maximal-ideal topology is not decoration. A local map $R\to S$ between the rings under consideration is automatically continuous because

$$
f(\mathfrak m_R^n)\subseteq\mathfrak m_S^n.
$$

It is nevertheless useful to retain the word *continuous*: formal power series are evaluated by convergence, completed tensor products satisfy a topological universal property, and inverse limits classify compatible finite-order maps.

Every admissible $R$ is recovered from its Artinian shadows. Every finite $R$-module $M$ is recovered in the same way:

$$
R\simeq\varprojlim_nR/\mathfrak m_R^n,
\qquad
M\simeq\varprojlim_nM/\mathfrak m_R^nM.
$$

Noetherianity makes ideals and finite submodules closed, while finite generation makes completion exact on the modules we use. These facts will repeatedly turn a construction modulo $\mathfrak m_R^n$ for all $n$ into an actual construction over $R$.

The hypotheses must not be suppressed. An inverse limit of Artinian local rings can have infinitely generated cotangent space and fail to be Noetherian. A complete module can contain a nonclosed submodule if finiteness is absent. A quotient by a nonclosed ideal is not separated. Our category excludes these pathologies because later numerical arguments require ideals, modules, and their topologies to agree.

### 1.4 The three numerical questions

For a universal ring $R$, three numbers arise naturally:

$$
\operatorname{edim}R,
\qquad
\dim R,
\qquad
\text{a minimal number of defining relations}.
$$

The first is linear: it is the dimension of a cotangent space. The second is prime-theoretic: it is the maximum length of a chain of prime ideals. The third is presentation-theoretic: it is the dimension of a relation module for a minimal power-series source. They interact, but they are not interchangeable.

For example,

$$
k[[X]]/(X^n)
$$

has embedding dimension $1$, Krull dimension $0$, and one minimal relation for every $n\geq2$. The tangent space does not see the exponent $n$. By contrast, $k[[X,Y]]/(XY)$ has embedding dimension $2$, dimension $1$, and one minimal relation. Its two tangent directions are both present, but they cannot vary freely beyond first order. This gap between first-order freedom and actual dimension is exactly where relations enter.

## 2. Cotangent spaces and infinitesimal directions

### 2.1 Why first-order neighborhoods are linear

Multiplication is nonlinear, but modulo the square of a maximal ideal it becomes linear. If $x,y\in\mathfrak m_R$, then $xy$ vanishes in $\mathfrak m_R/\mathfrak m_R^2$. Thus the first infinitesimal neighborhood of the closed point is a vector space over the residue field. This is the smallest quotient that remembers directions while forgetting products among them.

Deformation theory usually computes the dual space: maps to dual numbers, cocycles, or Selmer classes are tangent vectors. Ring presentations are built from the primal space: classes of elements of the maximal ideal are cotangent coordinates. Keeping this duality explicit prevents a common reversal. Cohomology classes are not themselves generators of the universal ring; a basis dual to them determines generators after choices of lifts.

### 2.2 Absolute cotangent and Zariski tangent spaces

Let $(R,\mathfrak m,k)$ be Noetherian local. Its **absolute cotangent space** is

$$
C_R=\mathfrak m/\mathfrak m^2.
$$

It is finite-dimensional over $k$ because $\mathfrak m$ is finitely generated. The **Zariski tangent space** is its dual

$$
T_R=\operatorname{Hom}_k(C_R,k).
$$

The **embedding dimension** is

$$
\operatorname{edim}R=\dim_k C_R=\dim_kT_R.
$$

The name is explained in Chapter 4: it is the least number of variables in a power-series ring over a coefficient field that can surject onto $R$.

If $R$ is an augmented local $k$-algebra, then a local $k$-map

$$
R\longrightarrow k[\epsilon]/(\epsilon^2)
$$

has the form $r\mapsto\bar r+d(r)\epsilon$. Multiplicativity says that $d$ is a $k$-derivation, and every such derivation factors through $C_R$. Hence

$$
T_R\simeq\operatorname{Der}_k(R,k).
$$

This is the ring-theoretic source of tangent spaces of represented functors.

### 2.3 Relative cotangent spaces

Over a nontrivial coefficient ring, absolute embedding dimension counts coefficient directions as well as deformation directions. The problem solved by the relative cotangent space is to remove changes already forced by the base.

For a local map $\mathcal O\to R$ with common residue field $k$, define

$$
C_{R/\mathcal O}
=\frac{\mathfrak m_R}
{\mathfrak m_R^2+\mathfrak m_{\mathcal O}R},
\qquad
T_{R/\mathcal O}=\operatorname{Hom}_k(C_{R/\mathcal O},k).
$$

The **relative embedding dimension** is $\operatorname{edim}_{\mathcal O}R=\dim_kC_{R/\mathcal O}$. Equivalently,

$$
T_{R/\mathcal O}\simeq\operatorname{Der}_{\mathcal O}(R,k),
$$

where $R$ acts on $k$ through the residue map. For a functor represented over $\mathcal O$, this is the tangent space computed with $\mathcal O$ held fixed.

More generally, if the residue fields are $k_{\mathcal O}\to k_R$, there is a natural right-exact sequence

$$
\frac{\mathfrak m_{\mathcal O}}{\mathfrak m_{\mathcal O}^2}
\otimes_{k_{\mathcal O}}k_R
\longrightarrow C_R
\longrightarrow C_{R/\mathcal O}
\longrightarrow0.
$$

In our fixed-residue category the tensor factor is just $k$. The first arrow need not be injective. A coefficient parameter can die or become decomposable in $R$.

### 2.4 The coefficient direction in mixed characteristic

Let $\mathcal O$ be a complete discrete valuation ring with uniformizer $\varpi$. Then

$$
C_{R/\mathcal O}
=\mathfrak m_R/(\mathfrak m_R^2+\varpi R).
$$

For the free power-series ring $P=\mathcal O[[X_1,\ldots,X_r]]$, the absolute cotangent space has basis

$$
\bar\varpi,\bar X_1,\ldots,\bar X_r,
$$

while the relative cotangent space has basis only $\bar X_1,\ldots,\bar X_r$. Thus

$$
\operatorname{edim}P=r+1,
\qquad
\operatorname{edim}_{\mathcal O}P=r.
$$

The distinction can collapse after quotienting. In

$$
R=\mathcal O[[X,Y]]/(XY-\varpi),
$$

the equation puts $\varpi=XY\in\mathfrak m_R^2$. Hence the coefficient class maps to zero in $C_R$, and both absolute and relative cotangent spaces have basis $\bar X,\bar Y$. By contrast, in $\mathcal O[[X]]$ the class of $\varpi$ is independent of $X$ absolutely.

Another extreme is $R=\mathcal O/(\varpi)=k$. Its absolute and relative cotangent spaces are both zero, even though its presentation over $\mathcal O$ has the coefficient-killing relation $\varpi$. Tangent directions count variables, not every equation in a chosen coefficient presentation.

### 2.5 Functoriality and exact sequences

A local homomorphism $f:R\to S$ induces covariantly a map on cotangent spaces and contravariantly a map on tangent spaces:

$$
C_R\longrightarrow C_S,
\qquad
T_S\longrightarrow T_R.
$$

Over $\mathcal O$ the same holds relatively. Surjectivity of $f$ implies surjectivity of $C_R\to C_S$, but the converse needs completeness and a common residue field.

**Cotangent surjectivity criterion.** Let $f:R\to S$ be a continuous local homomorphism of complete Noetherian local rings inducing an isomorphism on residue fields. If $C_R\to C_S$ is surjective, then $f$ is surjective. The same conclusion follows from surjectivity of $C_{R/\mathcal O}\to C_{S/\mathcal O}$ for a map of admissible $\mathcal O$-algebras.

**Proof strategy.** Degree one generates every graded layer multiplicatively. Lift a target element one order at a time, then use completeness to sum the corrections.

**Proof.** Cotangent surjectivity gives

$$
f(\mathfrak m_R)+\mathfrak m_S^2=\mathfrak m_S.
$$

Products show that $\mathfrak m_R^n/\mathfrak m_R^{n+1}\to\mathfrak m_S^n/\mathfrak m_S^{n+1}$ is surjective for every $n$. After lifting the residue of $s\in S$, successively choose $r_n\in\mathfrak m_R^n$ so that the image of $\sum_{i\leq n}r_i$ agrees with $s$ modulo $\mathfrak m_S^{n+1}$. The sum converges in $R$ and maps to $s$ by separatedness of $S$. In the relative case, every coefficient contribution modulo $\mathfrak m_S^2$ already comes from $R$, so relative surjectivity implies absolute surjectivity. $\square$

Completeness is decisive: $k[t]_{(t)}\to k[[t]]$ is an isomorphism on cotangent spaces but is not onto. Cotangent information also cannot detect injectivity. The quotient $k[[X]]\to k[[X]]/(X^2)$ induces an isomorphism on cotangent spaces and has nonzero kernel.

### 2.6 The conormal sequence at the closed point

Suppose $P\twoheadrightarrow R=P/I$ is a surjection of local $\mathcal O$-algebras, with maximal ideal $\mathfrak n$ in $P$. Kähler differentials give the conormal sequence

$$
I/I^2\longrightarrow
\Omega_{P/\mathcal O}\otimes_PR
\longrightarrow\Omega_{R/\mathcal O}\longrightarrow0.
$$

Tensoring with $k$ produces the right-exact sequence

$$
\frac{I}{\mathfrak nI+I^2}
\longrightarrow C_{P/\mathcal O}
\longrightarrow C_{R/\mathcal O}
\longrightarrow0.
$$

Because $I\subseteq\mathfrak n$ for a proper local quotient, $I^2\subseteq\mathfrak nI$; we retain $I^2$ in the notation to display its conormal origin. The first arrow sends a relation to its linear differential at the closed point. It need not be injective. In characteristic $p$, the relation $X^p$ has zero differential; so does every relation with no linear term after passage to $k$.

The sequence answers one question exactly: the image of the relation space consists of linear dependencies among the chosen cotangent coordinates. It does not say that all minimal algebraic relations remain linearly visible. Indeed, a minimal presentation is characterized by the opposite phenomenon: all its relations have zero image in the relative cotangent space.

### 2.7 Examples and first warnings

For

$$
R=k[[X,Y]]/(X^2,XY,Y^3),
$$

both $X$ and $Y$ survive in $C_R$, so $\operatorname{edim}R=2$. The three displayed equations impose no linear cotangent relation, even though they drastically shorten the ring. This example shows why tangent dimension cannot count higher equations.

For

$$
R=k[[X,Y]]/(X-Y^2),
$$

the relation has linear term $X$. The cotangent space is one-dimensional, generated by $Y$, and eliminating $X$ gives $R\simeq k[[Y]]$. The original two-variable presentation is therefore nonminimal.

Finally, consider the map

$$
k[[U,V]]/(V^2-U^3)\longrightarrow k[[T]],
\qquad U\mapsto T^2,\quad V\mapsto T^3.
$$

It is finite and injective, but its cotangent map is zero because $T^2,T^3\in(T)^2$. Finiteness alone says nothing about surjectivity on tangent coordinates.

## 3. Topological Nakayama and minimal generation

### 3.1 Why ordinary generation is not visibly enough

In a finite Artinian ring, lifting generators from the residue field is ordinary Nakayama. In a complete ring, one naturally obtains approximations modulo every power of an ideal. To turn them into one exact expression, their coefficients must converge. Topological Nakayama isolates the exact hypotheses that make this passage legitimate.

The theorem is useful in two forms. For finite modules, ordinary Nakayama already proves generation because the cokernel is finite. For modules presented only as complete topological objects, successive approximation proves the result without first assuming the module finite. The latter form still requires a finite list of proposed generators and completeness on both coefficients and target.

### 3.2 Topological Nakayama with exact hypotheses

**Theorem (topological Nakayama).** Let $R$ be complete and separated for the $J$-adic topology, where $J$ lies in the Jacobson radical. Let $M$ be a $J$-adically complete and separated $R$-module. If elements $m_1,\ldots,m_r$ have images spanning $M/JM$ over $R/J$, then they generate $M$ as an $R$-module.

No finite generation of $M$ is assumed in the statement; instead, the existence of a finite spanning list modulo $J$ and completeness of $M$ are explicit.

**Proof strategy.** Correct an approximate expression at one higher $J$-adic order at each step. Arrange the coefficient corrections to lie in matching powers of $J$, so they converge in $R^r$.

**Proof.** Let $\phi:R^r\to M$ send the standard basis to the $m_i$. The hypothesis says $M=\phi(R^r)+JM$. Multiplying and iterating gives

$$
M=\phi(R^r)+J^nM
$$

for every $n$. Given $m\in M$, choose $a_0\in R^r$ with $m-\phi(a_0)\in JM$. Suppose $a_0+\cdots+a_{n-1}$ has error $e\in J^nM$. Write $e=\sum_jc_ju_j$ with $c_j\in J^n$, and write each $u_j=\phi(b_j)+v_j$ with $v_j\in JM$. Then

$$
a_n=\sum_jc_jb_j\in J^nR^r
$$

moves the error into $J^{n+1}M$. The partial sums form a Cauchy sequence in $R^r$ and converge to $a$. Continuity gives $m-\phi(a)\in\bigcap_nJ^nM=0$. Thus $\phi$ is onto. $\square$

If only $M=JM$ is known, the theorem with an empty list gives $M=0$. The completeness and separatedness clauses cannot simply be replaced by suggestive limiting notation.

### 3.3 Finite modules over complete local rings

Let $(R,\mathfrak m)$ be complete Noetherian local and $M$ finite. Then $M$ is complete and separated, every submodule is closed, and

$$
M\simeq\varprojlim_nM/\mathfrak m^nM.
$$

These facts follow from Artin--Rees and exactness of completion on finite modules. Consequently the topological theorem applies automatically.

For finite modules, the familiar form is enough:

**Nakayama lemma.** If $N\subseteq M$ and $M=N+\mathfrak mM$, then $M=N$. In particular, if $M/\mathfrak mM=0$, then $M=0$.

Applying this to a cokernel gives a frequently used test. A map $f:M\to N$ of finite $R$-modules is surjective if and only if

$$
M/\mathfrak mM\longrightarrow N/\mathfrak mN
$$

is surjective. The analogous statement for injectivity is false; Chapter 10 will explain the asymmetry.

### 3.4 Minimal generators of modules and ideals

For a finite $R$-module $M$, define $\mu_R(M)$ to be its minimal number of generators. Nakayama gives the exact formula

$$
\mu_R(M)=\dim_kM/\mathfrak mM.
$$

Indeed, any generating set spans the quotient. Conversely, lift a basis of the quotient and apply Nakayama. A generating set is minimal exactly when its residue classes form a basis.

For $M=\mathfrak m$, this yields

$$
\mu_R(\mathfrak m)=\dim_k\mathfrak m/\mathfrak m^2
=\operatorname{edim}R.
$$

For an ideal $I\subseteq R$,

$$
\mu_R(I)=\dim_k I/\mathfrak mI.
$$

This formula is the foundation of relation counting. It counts ideal generators, not their images under differentiation and not their heights.

### 3.5 Topological generators of algebras

Suppose $R$ is an admissible complete local $\mathcal O$-algebra. Elements $y_1,\ldots,y_r\in\mathfrak m_R$ **topologically generate $R$ over $\mathcal O$** if the continuous map

$$
\mathcal O[[X_1,\ldots,X_r]]\longrightarrow R,
\qquad X_i\mapsto y_i,
$$

is surjective. This is stronger than saying that the abstract $\mathcal O$-subalgebra generated by the $y_i$ is all of $R$; infinite convergent sums are allowed in the source.

The correct finite test is relative cotangent generation.

**Proposition.** The elements $y_i$ topologically generate $R$ over $\mathcal O$ if their classes span

$$
C_{R/\mathcal O}
=\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R).
$$

**Proof.** The induced map from $P=\mathcal O[[\mathbf X]]$ to $R$ is local and is surjective on relative cotangent spaces. The relative cotangent surjectivity criterion of Section 2.5 makes it surjective. $\square$

Thus $\operatorname{edim}_{\mathcal O}R$ is the least number of topological algebra generators over the fixed base.

### 3.6 What fails without completeness or finiteness

The inclusion $k[t]_{(t)}\subset k[[t]]$ shows that matching residues and cotangent generators need not give surjectivity without completeness of the source. Every truncation of a series can be approximated by a polynomial, but one element of the localization need not encode all truncations simultaneously.

Finiteness also matters for algebraic Nakayama. Let $R=k[[t]]$ and $M=k((t))/k[[t]]$. Multiplication by $t$ is surjective on $M$, so $M=tM$, yet $M\neq0$. This does not contradict Nakayama because $M$ is not finite and is not separated complete in the required topology.

Finally, merely being complete as an abstract metric object is insufficient if the topology is not the $J$-adic one used in the approximation. The correction terms must tend to zero in the topology under which both $R^r$ and $M$ are complete.

## 4. Cohen structure, formal coordinates, and minimal presentations

### 4.1 Why formal power series are the correct source

A polynomial ring is free on finitely many algebraic generators. A formal power-series ring is free on finitely many *topologically nilpotent* generators in a complete local category. If $S$ is complete separated and $s_i\in\mathfrak m_S$, substitution defines a unique continuous local map

$$
\mathcal O[[X_1,\ldots,X_r]]\longrightarrow S,
\qquad X_i\mapsto s_i.
$$

Modulo $\mathfrak m_S^n$, only finitely many terms matter. Compatibility over all $n$ defines the value of a series. This universal property is exactly adapted to universal deformations, whose parameters live in maximal ideals of Artinian targets and are recovered at the limit.

The source

$$
P=\mathcal O[[X_1,\ldots,X_r]]
$$

is complete Noetherian local, with maximal ideal $(\mathfrak m_{\mathcal O},X_1,\ldots,X_r)$. If $\mathcal O$ is a field, $\dim P=r$; if $\mathcal O$ is a discrete valuation ring, $\dim P=r+1$. Every ideal is closed, so every local quotient is again complete and separated.

### 4.2 The coefficient-ring theorem

A presentation over a field or a complete discrete valuation ring begins with a less visible question: why may the residue field be lifted into the ring at all? In equal characteristic one wants an actual field of representatives. In mixed characteristic that is impossible, and one instead wants a characteristic-zero discrete valuation ring whose residue map is the prescribed one. These are the two forms of the coefficient-ring theorem.

**Theorem (coefficient rings).** Let $(R,\mathfrak m,k)$ be a complete Noetherian local ring.

1. If $R$ and $k$ have the same characteristic, there is a subfield $k_0\subseteq R$ mapping isomorphically onto $k$.
2. Suppose $R$ has characteristic zero and $k$ has characteristic $p>0$. There is a complete discrete valuation ring $C$ of characteristic zero, with maximal ideal $(p)$ and residue field $k$, together with a local homomorphism $C\to R$ inducing the identity on $k$. The map is injective.
3. If $k$ is perfect, the mixed-characteristic ring $C$ is unique up to the unique isomorphism compatible with multiplicative representatives of $k$. In particular it may be fixed once and for all. For imperfect $k$, existence remains true, but choices of representatives of a $p$-basis enter and uniqueness is not asserted without those choices.

Here and below a chosen copy of $k_0$ or a chosen map from $C$ is part of the presentation data. The theorem does not make arbitrary morphisms preserve independently chosen coefficient rings.

**Proof strategy.** One first chooses representatives in successively thicker quotients $R/\mathfrak m^n$. At each stage the failure of addition and multiplication lies one order deeper. Completeness turns a compatible tower of increasingly accurate representatives into exact representatives. In equal characteristic the correction equations are linear over $k$. In mixed characteristic the multiplicative representatives and their $p$-adic digits are lifted instead; for an imperfect residue field, a chosen $p$-basis supplies the missing independent digits.

**Proof.** We give the decisive construction. In equal characteristic, choose a transcendence basis $S$ of $k$ over its prime field and lift its elements to $R$. Every nonzero polynomial in finitely many elements of $S$ has nonzero residue and is therefore a unit in $R$. The resulting map from the rational function field on $S$ embeds into $R$. The residue extension $k/k_{\mathrm{prime}}(S)$ is algebraic. For a finite separable subextension, a primitive element has separable minimal polynomial; a lift of a simple residue root is corrected uniquely modulo $\mathfrak m^n$ at each stage because the derivative is a unit. Completeness supplies a root in $R$. Purely inseparable generators are handled by choosing a $p$-basis before the induction: at each finite stage the needed representatives are chosen freely on the basis and extended by the unique finite $p$-polynomial expansion. Taking the directed union of the lifted finitely generated subfields and closing under the compatible construction gives a subfield mapping onto $k$. Its intersection with $\mathfrak m$ is zero, so the residue map restricts to an isomorphism.

In mixed characteristic, begin with multiplicative representatives of a $p$-basis of $k$. Construct rings $C_n$ of characteristic $p^n$ recursively so that $C_{n+1}/p^nC_{n+1}\simeq C_n$, $p$ generates the maximal ideal, and the residue field is $k$. The lift from level $n$ to $n+1$ is determined on the chosen $p$-basis; every residue element has a unique finite expression in $p$-basis monomials with coefficients in $k^p$, so induction extends the lift to addition and multiplication. The inverse limit

$$
C=\varprojlim_n C_n
$$

is complete, has maximal ideal $(p)$, and every nonzero element is uniquely $p^au$ with $u$ a unit. Hence $C$ is a discrete valuation ring. The same recursive corrections, now performed inside $R/\mathfrak m^n$ and made compatible with the $p$-adic quotients, give $C\to R$. Its kernel is an ideal $(p^a)$ if nonzero, but $p^a$ cannot vanish in a characteristic-zero ring; therefore the map is injective. When $k$ is perfect there is no $p$-basis choice beyond the empty one, and the multiplicative representatives determine all digits, giving the stated uniqueness. $\square$

For a finite field $k$, the perfect case is the one used most often. Each $a\in k$ has a unique multiplicative lift $[a]\in C$, and every element of $C$ has a unique convergent expansion

$$
[a_0]+p[a_1]+p^2[a_2]+\cdots.
$$

The representatives are multiplicative, not additive. Treating $a\mapsto[a]$ as a field embedding would contradict the characteristic difference.

### 4.3 The Cohen presentation theorem

The coefficient-ring theorem supplies constants. Cotangent lifts supply variables. Together they give the structural presentation on which all later numerical arguments rest.

**Theorem (Cohen presentation).** Let $(R,\mathfrak m,k)$ be complete Noetherian local.

- In equal characteristic, after choosing a coefficient field $k\hookrightarrow R$, there is a surjection

  $$
  k[[X_1,\ldots,X_e]]\twoheadrightarrow R,
  $$

  where $e=\dim_k\mathfrak m/\mathfrak m^2$. It may be chosen minimal, and then its kernel lies in $(X_1,\ldots,X_e)^2$.
- In mixed characteristic, choose a coefficient ring $C\to R$. Put

  $$
  r=\dim_k\frac{\mathfrak m}{\mathfrak m^2+pR}.
  $$

  There is a surjection

  $$
  C[[X_1,\ldots,X_r]]\twoheadrightarrow R
  $$

  inducing the given coefficient map, and it is minimal relative to $C$.

**Proof strategy.** Lift a basis of the appropriate cotangent space, map the formal variables to those lifts, and prove surjectivity one order at a time. The coefficient ring supplies the constant term at every order; products of the chosen lifts supply every graded correction.

**Proof.** In equal characteristic choose $y_i\in\mathfrak m$ lifting a basis of $\mathfrak m/\mathfrak m^2$. In mixed characteristic choose lifts of a basis of $\mathfrak m/(\mathfrak m^2+pR)$. Substitution gives the displayed continuous map $\phi$. In the equal-characteristic case its cotangent map is onto. In the mixed-characteristic case its relative cotangent map is onto; the image of $pR$ already comes from $C$, so its absolute cotangent map is also onto. The complete cotangent criterion proves that $\phi$ is surjective. The chosen bases make the relative cotangent maps isomorphisms. The conormal sequence then says precisely that the kernel has no unit-coefficient linear part. $\square$

In mixed characteristic the absolute embedding dimension $e$ and the relative number $r$ differ according to the position of $p$:

$$
r=
\begin{cases}
e-1,&p\notin\mathfrak m^2,\\
e,&p\in\mathfrak m^2.
\end{cases}
$$

Indeed the image of $pR$ in $\mathfrak m/\mathfrak m^2$ is respectively one-dimensional or zero. In the second case the coefficient parameter is already decomposable; a typical ramified presentation has a relation

$$
p-F(X_1,\ldots,X_e),\qquad F\in(X_1,\ldots,X_e)^2.
$$

This is why a ramified regular local ring can require as many relative variables as its absolute embedding dimension.

### 4.4 Cohen presentations are not canonical

The structure theorem gives existence, not preferred coordinates. A different coefficient field, a different coefficient-ring map, a different cotangent basis, or different lifts of that basis can alter the kernel inside the source. Even in $k[[T]]$, the parameters $T$ and $T+T^2$ give different written coordinates.

What is intrinsic is more modest and more useful: the minimal number of variables, the isomorphism class of the quotient, the minimal number of generators of the kernel after the coefficient map is fixed, and properties invariant under source automorphisms. Dimension, regularity, flatness, and the complete-intersection property belong to this stable package. Individual equations generally do not.

The coefficient-ring map also matters. A ring can admit two coefficient structures over the same residue field that are not carried into one another by an automorphism fixed in advance. Every relative statement in this book therefore names its base. Absolute invariants such as $\dim R$ and $\operatorname{edim}R$ do not depend on that choice; relative embedding dimension and a relative relation module do.

### 4.5 Building a presentation from tangent lifts

Let $R$ be an admissible complete local $\mathcal O$-algebra, and put

$$
r=\dim_kC_{R/\mathcal O}.
$$

Choose a basis $\bar y_1,\ldots,\bar y_r$ and lifts $y_i\in\mathfrak m_R$. Substitution gives

$$
\phi:P=\mathcal O[[X_1,\ldots,X_r]]\longrightarrow R.
$$

The induced relative cotangent map is an isomorphism, in particular surjective, so $\phi$ is surjective. Therefore

$$
R\simeq P/I
$$

for the closed ideal $I=\ker\phi$.

This construction separates intrinsic data from choices. The number $r$ is intrinsic. The basis, its lifts, the variables, and the kernel as a named subideal of a named power-series ring are not. What survives changes of coordinates is the isomorphism class of $R$ and the numerical data attached to a minimal presentation.

### 4.6 Minimality over a field

Assume first that $\mathcal O=k$ and write $\mathfrak n=(X_1,\ldots,X_r)$. A surjection

$$
k[[X_1,\ldots,X_r]]\twoheadrightarrow R
$$

is **minimal** if the induced map on cotangent spaces is an isomorphism. The conormal sequence shows that this is equivalent to

$$
I\subseteq\mathfrak n^2.
$$

Equivalently, no relation has a nonzero linear term. If a relation has linear part with a nonzero coefficient, an invertible linear coordinate change makes that part $X_r$; formal elimination then removes $X_r$. Repeating yields a minimal presentation.

Thus the least number of variables is exactly $\operatorname{edim}R$. A presentation can always be enlarged artificially, for example

$$
k[[X]]/(X^2)
\simeq k[[X,Y]]/(X^2,Y),
$$

but the second presentation has a linear relation and is not minimal.

### 4.7 Minimality over a coefficient ring

Let $P=\mathcal O[[X_1,\ldots,X_r]]$ with maximal ideal $\mathfrak n$. The presentation $P\twoheadrightarrow R$ is **minimal relative to $\mathcal O$** when

$$
C_{P/\mathcal O}\xrightarrow{\sim}C_{R/\mathcal O}.
$$

Equivalently,

$$
I\subseteq\mathfrak n^2+\mathfrak m_{\mathcal O}P.
$$

This criterion allows a relation whose apparent linear term is a coefficient multiple. For a discrete valuation base, a term $\varpi X$ vanishes in the relative cotangent space, whereas a unit multiple of $X$ does not. The variables count freedom beyond $\mathcal O$; relations internal to the base are not counted as coordinate dependencies.

Absolute minimality is a different question. In $R=\mathcal O[[X,Y]]/(XY-\varpi)$, the relative presentation has two variables and one equation. Absolutely, $\varpi$ becomes decomposable, so the maximal ideal of $R$ is generated by $X,Y$ rather than by $\varpi,X,Y$. A relative presentation need not display an absolute minimal generating set term by term.

### 4.8 Changes of coordinates and uniqueness information

Two choices of bases of $C_{R/\mathcal O}$ differ by an element of $\operatorname{GL}_r(k)$. More strongly, let $\phi,\psi:P=\mathcal O[[\mathbf X]]\twoheadrightarrow R$ be two minimal presentations. Choose $z_i\in\mathfrak n_P$ with $\phi(z_i)=\psi(X_i)$. Substitution $X_i\mapsto z_i$ defines a continuous $\mathcal O$-endomorphism $\alpha$ of $P$ satisfying $\phi\circ\alpha=\psi$. Its relative linear part is invertible because both presentations identify $C_{P/\mathcal O}$ with $C_{R/\mathcal O}$. The relative cotangent surjectivity criterion makes $\alpha$ surjective, and a surjective endomorphism of the Noetherian ring $P$ is injective. Thus $\alpha$ is an automorphism carrying $\ker\psi$ to $\ker\phi$.

The resulting principle is:

**Minimal presentation uniqueness.** Any two minimal power-series presentations of $R$ over the same fixed coefficient ring use the same number of variables. After choosing compatible tangent bases, they are related by continuous coordinate changes of their sources and an isomorphism of quotients. There is generally no canonical coordinate change and no canonical list of equations.

This is exactly the uniqueness one should expect. A universal deformation ring may be canonical relative to its universal property, but coordinates on its formal neighborhood never are.

### 4.9 Worked presentations

The ring $R=k[[T]]/(T^3)$ has $C_R=k\bar T$, so its displayed one-variable presentation is minimal. The kernel is generated by one cubic relation. Replacing $T$ by $T+T^2$ gives another minimal coordinate and changes the written equation by a unit multiple plus higher terms.

For

$$
R=k[[X,Y,Z]]/(Z-X^2-Y^3),
$$

the displayed presentation is not minimal because the relation has linear term $Z$. Eliminating $Z$ gives $R\simeq k[[X,Y]]$, revealing formal smoothness that the three-variable presentation obscured.

Over a discrete valuation ring,

$$
R=\mathcal O[[X]]/(\varpi X,X^2)
$$

has one relative tangent direction, so the one-variable presentation is minimal relative to $\mathcal O$. The ring is not flat over $\mathcal O$, since $\varpi$ kills the nonzero class of $X$. Minimality records the absence of a removable variable; it says nothing about flatness or regularity.

## 5. Relation modules and the number of equations

### 5.1 Why an ideal is not yet a count of relations

Once $R=P/I$ is presented, it is tempting to count whatever equations happen to be written down. That count is coordinate-dependent and can contain redundancies. Even the ideal $I$ itself is too large to be a linear count: multiplying one relation by arbitrary elements produces infinitely many relations that carry no new generating information.

Nakayama supplies the correct linearization. One kills multiples by the maximal ideal of the source. The resulting vector space records precisely which equations are needed to generate the ideal. This is a different linearization from taking differentials: minimal relations can begin in degree two or higher and hence have zero differential at the closed point.

### 5.2 The minimal relation module

Let $(P,\mathfrak n,k)$ be complete Noetherian local and let $I\subseteq\mathfrak n$. The **minimal relation space** of the presentation $P\twoheadrightarrow R=P/I$ is

$$
\operatorname{Rel}_P(R)=I/\mathfrak nI.
$$

Viewed through the conormal module, the same space is

$$
\frac{I/I^2}{\mathfrak m_R(I/I^2)}
\simeq \frac{I}{\mathfrak nI+I^2}.
$$

Since $I^2\subseteq\mathfrak nI$, these descriptions agree. The conormal form is conceptually useful because it regards relations modulo consequences generated by other relations; the ideal form is best for applying Nakayama.

The exact count is

$$
\mu_P(I)=\dim_k\operatorname{Rel}_P(R).
$$

Choose $f_1,\ldots,f_s\in I$. They minimally generate $I$ if and only if their classes form a $k$-basis of $I/\mathfrak nI$. Because $P$ is Noetherian, this dimension is finite. Thus every complete local ring in our category has a finite presentation once a finite-variable power-series source has been chosen.

We shall call

$$
R\simeq\mathcal O[[X_1,\ldots,X_r]]/(f_1,\ldots,f_s)
$$

a **minimal generators-and-relations presentation** when the variables form a relative cotangent basis and the $f_j$ form a minimal generating set of the kernel. Minimality of variables and minimality of equations are separate requirements.

### 5.3 Relations in the conormal sequence

For $P\twoheadrightarrow R$, tensoring the conormal sequence with $k$ gives

$$
\operatorname{Rel}_P(R)
\xrightarrow{d}
C_{P/\mathcal O}
\longrightarrow C_{R/\mathcal O}
\longrightarrow0.
$$

The kernel of $d$ measures minimal ideal generators whose first derivative vanishes. In a minimal variable presentation, $d=0$ on all of $\operatorname{Rel}_P(R)$. There is no contradiction: a quadratic equation is a minimal algebraic relation while being invisible in first-order tangent geometry.

In a nonminimal presentation, the rank of $d$ counts removable linear directions. If $d$ has rank $q$, choose bases so that $q$ relations have independent linear parts in $q$ variables. Formal elimination removes those variables and relations. The remaining presentation has

$$
r-q=\dim_kC_{R/\mathcal O}
$$

variables. This procedure explains why relation count alone is not invariant until the source presentation has been made minimal.

The left arrow need not be injective even before minimalization. For $P=k[[X]]$ and $I=(X^p)$ in characteristic $p$, the nonzero relation class maps to $d(X^p)=0$. For $I=(X^2)$ in characteristic different from $2$, its differential $2X\,dX$ also vanishes after tensoring with $k$. The closed-point differential sees linear terms, not order of vanishing.

### 5.4 Relative and special-fiber relation counts

Over a coefficient ring, $I/\mathfrak nI$ counts every equation needed in the chosen $\mathcal O$-presentation, including an equation that kills or torsionizes a coefficient element. It is therefore relative only in the sense that the source $P$ is free over the fixed base; it does not discard equations involving $\varpi$.

Passing to the special fiber changes the source and kernel. Put

$$
\bar P=P/\mathfrak m_{\mathcal O}P,
\qquad
\bar R=R/\mathfrak m_{\mathcal O}R,
$$

and let

$$
\bar I=(I+\mathfrak m_{\mathcal O}P)/\mathfrak m_{\mathcal O}P.
$$

Then the minimal special-fiber relation space is

$$
\bar I/\mathfrak m_{\bar P}\bar I.
$$

There is a natural map from the original relation space after scalar reduction, but it need not be an isomorphism without a suitable flatness hypothesis. A relation divisible by $\varpi$ can vanish in the special fiber; torsion can also create new dependencies.

For example, $R=\mathcal O/(\varpi)$ has presentation $P=\mathcal O$ with one minimal relation $\varpi$. After base change to $k$, the induced presentation is $k\to k$ with zero kernel, so the relation disappears. This is the simplest warning that nonflat coefficient change does not preserve relation counts.

Under a local extension $\mathcal O\to\mathcal O'$ with residue extension $k\to k'$, assume that the induced map on the power-series sources is flat and that the presentation kernel base-changes exactly. Then extension of a minimal relation module behaves as expected:

$$
\operatorname{Rel}_{P'}(R')
\simeq \operatorname{Rel}_P(R)\otimes_k k',
$$

where $P'=\mathcal O'[[\mathbf X]]$ and $R'=R\widehat\otimes_{\mathcal O}\mathcal O'$. We will prove the base-change statement in Chapter 12 and state explicitly where flatness enters.

### 5.5 Changing a presentation

Suppose two presentations of $R$ use minimal variables over the same $\mathcal O$. Their sources are power-series rings in the same number of variables and are related by a continuous coordinate isomorphism after choices. This isomorphism carries one kernel to the other, so it identifies their relation spaces. Consequently

$$
\dim_k\operatorname{Rel}_P(R)
$$

is an invariant of a minimal presentation over the fixed coefficient base, although the vector space is not canonically identified without choosing the coordinate comparison.

If nonminimal variables are allowed, the relation count can be enlarged at will. Adding a variable $Y$ and the relation $Y-g(\mathbf X)$ adds one variable and one relation without changing $R$. Thus only the pair

$$
(r,s)=(\text{minimal relative variables},\text{relations in a minimal source})
$$

has stable numerical meaning.

Even for a minimal source, the individual orders and shapes of the $f_j$ are coordinate-dependent. Their initial ideal and the associated graded ring retain more information, but no obstruction-space calculation by itself normally chooses canonical equations.

### 5.6 Examples and counterexamples

For

$$
R=k[[X,Y]]/(X^2,XY),
$$

the source is minimal and the two displayed equations are minimal: neither lies in $\mathfrak n$ times the ideal generated by both. Hence $r=2$ and $s=2$. The ideal has common factor $X$, so two equations do not force a two-dimensional drop; in fact $\dim R=1$. Relation number and codimension can differ.

For

$$
R=k[[X,Y]]/(X^2,XY,Y^2),
$$

there are three minimal quadratic relations, embedding dimension $2$, and Krull dimension $0$. Here $s>r$, which is perfectly possible for a finite local ring.

For

$$
R=\mathcal O[[X]]/(\varpi X),
$$

there is one relative variable and one minimal relation. The ring has both a horizontal component $(X)$ and a vertical component $(\varpi)$. Its dimension is $1$, not something obtained by indiscriminately subtracting one from every component dimension. Prime geometry, developed next, controls the actual answer.

### 5.7 Relation modules, syzygies, and redundancy

The space $I/\mathfrak nI$ counts generators of the ideal $I$; it does not record relations among those generators. If $f_1,\ldots,f_s$ generate $I$, the surjection

$$
P^s\longrightarrow I,
\qquad (a_1,\ldots,a_s)\longmapsto\sum_ia_if_i
$$

has kernel $Z$, the first **syzygy module**. An element of $Z$ is an algebraic identity among the equations. Replacing an equation by itself plus a combination of the others changes the chosen basis of $P^s$ but not the ideal or the quotient.

Minimality has a useful exact form. If the classes of the $f_i$ form a basis of $I/\mathfrak nI$, then

$$
Z\subseteq\mathfrak nP^s.
$$

Indeed, reducing a syzygy modulo $\mathfrak n$ gives a linear dependence among those basis classes. Conversely, if a generating list has this containment, its residue classes are linearly independent and the list is minimal. Thus a minimal presentation has no syzygy with a unit coefficient. It may still have many higher syzygies. For $I=(X^2,XY)$, the identity

$$
Y\cdot X^2-X\cdot XY=0
$$

is a nontrivial syzygy, but both coefficients lie in the maximal ideal, so neither equation is redundant.

This distinction matters in obstruction calculations. An obstruction space that bounds the number of ideal generators need not describe all identities among the resulting equations. Those identities enter homological invariants and cannot be recovered from the mere dimension of $I/\mathfrak nI$.

### 5.8 Relative relation modules for a map

Often one does not present a ring over the coefficient ring directly. Instead one has a local map $A\to R$ and wants to count only the new global equations beyond those already present in $A$. Choose a relative minimal surjection

$$
P=A[[X_1,\ldots,X_g]]\twoheadrightarrow R
$$

and write $I$ for its kernel and $\mathfrak n$ for the maximal ideal of $P$. The **relation module of $R$ over $A$ in this presentation** is

$$
\operatorname{Rel}_{P/A}(R)=I/\mathfrak nI.
$$

The variables are counted by

$$
g=\dim_k\frac{\mathfrak m_R}
{\mathfrak m_R^2+\mathfrak m_AR},
$$

provided $A$ and $R$ have the same residue field. The relations are counted by $\dim_k I/\mathfrak nI$. All equations already defining $A$ are built into the base and are not counted again.

Two relative minimal presentations over the same $A$ are related by an $A$-linear formal coordinate change, exactly as in Section 4.8. Their relation spaces therefore have the same dimension. This number depends on the map $A\to R$, not merely on the abstract ring $R$. Taking $A=\mathcal O$ counts all deformation equations; taking $A$ to be a completed product of prescribed local rings counts only the global compatibility equations.

The relative conormal sequence is

$$
I/I^2\longrightarrow
\Omega_{P/A}\otimes_PR
\longrightarrow\Omega_{R/A}\longrightarrow0.
$$

After tensoring with $k$, a relative minimal presentation again makes the first arrow zero. The ideal generators survive in $I/\mathfrak nI$ even though their closed-point differentials vanish.

### 5.9 The universal small extension attached to a relation

A nonzero functional

$$
\lambda:I/\mathfrak nI\longrightarrow k
$$

isolates one relation direction. This statement can be made into an explicit small extension. Choose $N$ large enough that a representative of the selected relation is nonzero in $P/\mathfrak n^N$. Form

$$
E_N=
\frac{P}{L_\lambda+\mathfrak n^N},
$$

where

$$
L_\lambda
=\ker\left(I\longrightarrow I/\mathfrak nI
\xrightarrow{\lambda}k\right).
$$

Artin--Rees permits $N$ to be chosen so large that

$$
I\cap\mathfrak n^N\subseteq\mathfrak nI\subseteq L_\lambda.
$$

Consequently the image $K_\lambda$ of $I$ in $E_N$ is canonically $I/L_\lambda\simeq k$. It is killed by the maximal ideal because $\mathfrak nI\subseteq L_\lambda$. Quotienting it out gives the Artinian quotient

$$
A_N=P/(I+\mathfrak n^N)
$$

of $R$. Hence

$$
E_N\twoheadrightarrow A_N
$$

is a principal small extension. It asks whether the universal object over $A_N$ can be lifted while relaxing precisely the equation selected by $\lambda$.

This extension is genuinely nontrivial from the viewpoint of the represented functor. Suppose the universal map $R\to A_N$ lifted to $R\to E_N$. Compare the two maps $P\to E_N$: the quotient map and the composite through the alleged lift. Their difference takes values in the square-zero kernel $K_\lambda$ and is an $\mathcal O$-derivation. Such a derivation factors through $C_{P/\mathcal O}$. Since the presentation is relatively minimal, $I$ maps to zero in that cotangent space, so the derivation vanishes on $I$. But the quotient map sends some $f\in I$ with $\lambda(\bar f)\neq0$ to a nonzero element of $K_\lambda$, whereas the map through $R=P/I$ sends it to zero. This contradiction proves that no lift exists.

Different sufficiently large $N$ give equivalent tests under pushout. This is the algebra behind the injection from the dual relation space into a complete obstruction space in Chapter 13. The construction also explains why the dual appears: a relation itself is an element of a kernel, while pushing that kernel out to a one-dimensional small extension requires a linear functional on its residue fiber.

## 6. Krull dimension in the complete local setting

### 6.1 Dimension as chains of irreducible constraints

Cotangent space measures how many first-order directions leave the closed point. Krull dimension measures how many genuinely independent specializations can occur in succession. The latter is defined by prime ideals because primes describe irreducible closed conditions: a chain of primes records a chain of increasingly special irreducible loci.

For a ring $R$, its **Krull dimension** is

$$
\dim R=\sup\{n:\mathfrak p_0\subsetneq\mathfrak p_1
\subsetneq\cdots\subsetneq\mathfrak p_n\text{ are prime}\}.
$$

For a Noetherian local ring, every prime lies under the unique maximal ideal, and maximal chains end at $\mathfrak m_R$. Completeness does not change the definition. It supplies structure theorems and reliable presentations through which dimension can be calculated.

The distinction from embedding dimension is fundamental:

$$
\dim R\leq\operatorname{edim}R.
$$

Equality characterizes regular local rings. The inequality follows because $\mathfrak m_R$ can be generated by $e=\operatorname{edim}R$ elements, and the height theorem bounds the height of $\mathfrak m_R$ by $e$.

### 6.2 Prime chains and quotients

Prime ideals of $R/I$ correspond to primes of $R$ containing $I$. Therefore

$$
\dim(R/I)
=\sup_{\mathfrak p\supseteq I}\dim(R/\mathfrak p)
\leq\dim R.
$$

If $I\subseteq J$, then $\dim R/J\leq\dim R/I$. Each added equation can lower dimension, leave it unchanged on some component, or remove an entire component. There is no general exact subtraction law based only on the number of equations.

For a prime $\mathfrak p$ in a Noetherian local ring,

$$
\operatorname{ht}(\mathfrak p)=\dim R_{\mathfrak p}
$$

is the maximum length of chains ending at $\mathfrak p$. In well-behaved power-series sources, the dimension formula

$$
\dim(P/\mathfrak p)=\dim P-\operatorname{ht}(\mathfrak p)
$$

holds. Consequently the dimension of $P/I$ is governed by the minimal height among primes containing $I$, equivalently among minimal primes over $I$.

### 6.3 Power-series dimensions

Let $A$ be Noetherian. Then

$$
\dim A[[X_1,\ldots,X_r]]=\dim A+r
$$

in the local complete settings used here. Thus

$$
\dim k[[X_1,\ldots,X_r]]=r,
$$

and for a complete discrete valuation ring,

$$
\dim\mathcal O[[X_1,\ldots,X_r]]=r+1.
$$

The extra mixed-characteristic dimension is the coefficient direction. It is present in Krull dimension even though relative tangent space omits it.

**Proof idea.** Adjoining one formal variable creates chains by extending primes and then adjoining the variable, giving the lower bound. The upper bound is the formal power-series dimension theorem, proved by analyzing contractions of prime chains and using the principal ideal theorem. Iterating gives the formula. Completeness ensures that the formal series ring is Noetherian and that its maximal ideal is the expected one.

For a complete local ring $R\simeq P/I$, this reduces dimension questions to the height of the kernel. It does not make the answer depend only on $\mu_P(I)$.

### 6.4 Generator--relation inequalities

Suppose

$$
R\simeq P/(f_1,\ldots,f_s),
\qquad
P=\mathcal O[[X_1,\ldots,X_r]],
$$

where $\mathcal O$ is a field or a discrete valuation ring. Krull's height theorem says that every minimal prime over an ideal generated by $s$ elements has height at most $s$. Therefore

$$
\dim R\geq\dim P-s.
$$

Together with the quotient inequality,

$$
\dim P-s\leq\dim R\leq\dim P.
$$

Explicitly,

$$
\dim R\geq r-s
$$

over a field, and

$$
\dim R\geq 1+r-s
$$

over a coefficient discrete valuation ring. A negative lower bound is true but uninformative; dimension is always nonnegative for a nonzero local ring.

These are inequalities, not equalities. For $P=k[[X,Y]]$ and $I=(X^2,XY)$, one has $s=2$ but $\operatorname{ht}I=1$, so $\dim P/I=1>0=\dim P-s$. The two equations share the same underlying codimension-one condition.

### 6.5 Height, minimal primes, and equality

In the regular power-series source $P$, one has the exact formula

$$
\dim(P/I)
=\dim P-\operatorname{ht}(I),
$$

where

$$
\operatorname{ht}(I)=
\min\{\operatorname{ht}(\mathfrak p):\mathfrak p\supseteq I\}.
$$

The reason is that formal power-series rings over a field or complete discrete valuation ring have the dimension formula for primes. Taking the largest $\dim(P/\mathfrak p)$ among primes above $I$ is the same as taking the smallest height.

Hence equality

$$
\dim(P/I)=\dim P-s
$$

holds exactly when $\operatorname{ht}(I)=s$, provided $s$ is the minimal number of ideal generators under discussion. Chapter 8 proves that, in the regular source $P$, this equality is exactly the condition that a minimal generating list be a regular sequence; it is therefore the numerical complete-intersection criterion.

For one nonzero equation in the domain $P$, the principal ideal theorem and absence of height-zero containment give height exactly one. Thus, if $0\neq f\in P$ is a nonunit,

$$
\dim P/(f)=\dim P-1.
$$

If $f=0$, of course no drop occurs. Calling a ring “hypersurface-shaped” should always retain this nonzero hypothesis when a dimension conclusion is drawn.

### 6.6 Dimension is not embedding dimension

Consider the following comparison:

$$
\begin{array}{c|c|c|c}
R&\operatorname{edim}R&\dim R&\text{minimal relations}\\ \hline
k[[X,Y]]&2&2&0\\
k[[X,Y]]/(XY)&2&1&1\\
k[[X,Y]]/(X^2,XY)&2&1&2\\
k[[X,Y]]/(X,Y)^2&2&0&3.
\end{array}
$$

All but the first have the same two-dimensional tangent space. Their prime chains and relation modules are different. No tangent calculation can distinguish them without higher-order data.

In mixed characteristic, the comparison must specify which embedding dimension is meant. The ring $\mathcal O[[X]]$ has relative embedding dimension $1$, absolute embedding dimension $2$, and Krull dimension $2$. The ring $\mathcal O[[X,Y]]/(XY-\varpi)$ has relative and absolute embedding dimensions both $2$, and Krull dimension $2$. Equality with dimension is therefore an absolute regularity statement, not a relative tangent statement.

## 7. Regular local rings

### 7.1 The smallest possible cotangent space

Every Noetherian local ring satisfies $\dim R\leq\operatorname{edim}R$. A **regular local ring** is one for which equality holds:

$$
\dim R=\dim_k\mathfrak m_R/\mathfrak m_R^2.
$$

This definition says that the closed point has no excess first-order directions beyond the actual dimension. It does not mean that the ring contains no equations in every ambient presentation. Rather, after choosing an appropriate intrinsic coefficient structure, its maximal ideal behaves like the coordinate ideal of a formal affine space.

Regularity is absolute. A ring can be relatively generated by few variables over $\mathcal O$ while failing to be regular because the coefficient parameter becomes singular or torsion. Conversely, a smooth power-series extension of a regular coefficient ring is regular.

### 7.2 Equivalent characterizations

Let $(R,\mathfrak m,k)$ be Noetherian local of dimension $d$. The following are equivalent:

1. $R$ is regular local.
2. The maximal ideal can be generated by $d$ elements.
3. Every minimal generating set of $\mathfrak m$ has $d$ elements.
4. There exist $x_1,\ldots,x_d\in\mathfrak m$ such that, for every $n\geq0$, the degree-$n$ monomials in their initial classes form a $k$-basis of $\mathfrak m^n/\mathfrak m^{n+1}$.
5. The natural graded map

   $$
   k[T_1,\ldots,T_d]\longrightarrow
   \operatorname{gr}_{\mathfrak m}R,
   \qquad T_i\mapsto\operatorname{in}(x_i),
   $$

   is an isomorphism.

The equivalence of the first three is immediate from Nakayama and the definition. The associated graded equivalence requires more substance and is proved next. It is especially useful because it tests every order of the maximal-ideal filtration, not just degree one.

### 7.3 The associated graded criterion

The **associated graded ring** is

$$
\operatorname{gr}_{\mathfrak m}R
=\bigoplus_{n\geq0}\mathfrak m^n/\mathfrak m^{n+1}.
$$

Choose minimal generators $x_1,\ldots,x_e$ of $\mathfrak m$. Their initial classes generate the graded ring, giving a surjection

$$
k[T_1,\ldots,T_e]\twoheadrightarrow
\operatorname{gr}_{\mathfrak m}R.
$$

If $R$ is regular, $e=d$. A nonzero homogeneous kernel would lower the dimension of the graded quotient below $d$, while the associated graded ring has the same Krull dimension as $R$. Hence the kernel is zero and the graded ring is polynomial.

Conversely, if $\operatorname{gr}_{\mathfrak m}R\simeq k[T_1,\ldots,T_d]$, then its degree-one part has dimension $d$ and its Krull dimension is $d$. Equality of dimensions of $R$ and its associated graded ring gives

$$
\operatorname{edim}R=d=\dim R,
$$

so $R$ is regular.

This criterion is stronger than the statement that the cotangent space has dimension $d$: the polynomial graded ring asserts that no hidden initial relation appears at any order.

### 7.4 Complete regular rings and coefficient bases

If $R$ is complete equicharacteristic regular local and a coefficient field $k\hookrightarrow R$ has been fixed, lifting a basis of $\mathfrak m/\mathfrak m^2$ gives a surjection

$$
k[[X_1,\ldots,X_d]]\twoheadrightarrow R.
$$

Both rings have dimension $d$. A nonzero kernel would have positive height and lower the quotient dimension, so the kernel is zero. Hence

$$
R\simeq k[[X_1,\ldots,X_d]].
$$

This is the equal-characteristic portion of the complete structure theory needed here.

Over a fixed complete discrete valuation ring $\mathcal O$, the power-series ring $\mathcal O[[X_1,\ldots,X_r]]$ is regular of dimension $r+1$. If an admissible $R$ is formally smooth over $\mathcal O$, Chapter 12 will show that it is noncanonically such a power-series ring and hence regular.

The converse needs care. A complete mixed-characteristic regular local ring need not come with the particular coefficient DVR one wishes to use, and ramified regular rings need not be power-series rings over an unramified coefficient DVR in the naive sense. We use no coefficient-ring claim beyond the fixed-base and equal-characteristic statements already available or proved here.

### 7.5 Detecting singularity in examples

The node

$$
R=k[[X,Y]]/(XY)
$$

has dimension $1$ and embedding dimension $2$, so it is not regular. Its associated graded ring is itself and has the quadratic relation $XY$.

The fat point $k[[X]]/(X^n)$ for $n\geq2$ has dimension $0$ and embedding dimension $1$, so it is not regular. A zero-dimensional regular local ring must have maximal ideal generated by zero elements and is therefore a field.

The mixed-characteristic ring

$$
R=\mathcal O[[X,Y]]/(XY-\varpi)
$$

has dimension $2$. Its maximal ideal is $(X,Y)$ because $\varpi=XY$, so its embedding dimension is also $2$. It is regular even though its special fiber $k[[X,Y]]/(XY)$ is singular. Regularity of the total local ring and regularity of its special fiber are different questions.

By contrast,

$$
\mathcal O[[X]]/(\varpi X)
$$

has dimension $1$ and maximal ideal minimally generated by $\varpi,X$, hence embedding dimension $2$. It is not regular.

### 7.6 From regularity to regular sequences

The associated graded criterion does more than recognize a smooth formal space. If $x_1,\ldots,x_d$ minimally generate the maximal ideal of a regular local ring, then their initial forms are polynomial variables. It follows successively that $x_1$ is a non-zero-divisor, that the image of $x_2$ is a non-zero-divisor modulo $x_1$, and so on. Indeed, if $x_i a$ belonged to the ideal generated by the preceding $x_j$, comparison of the first nonzero initial forms in the polynomial associated graded ring would force the initial form of $a$ into the same preceding ideal. Repeating by order and using separation gives the desired divisibility in the local ring.

Thus a regular system of parameters behaves not only like a coordinate list but also like a sequence of independent equations. Chapter 8 develops this idea carefully, including the exact distinction between a dimension-cutting parameter and a non-zero-divisor, and uses it to characterize the complete-intersection presentations needed later.

## 8. Parameters, depth, and complete intersections

### 8.1 Why dimension needs concrete witnesses

Prime chains define dimension, but later arguments often need elements that cut a local ring down to finite length. A system of parameters provides such elements. It turns a dimension statement into a finite quotient and lets one compare rings or modules through an explicit ideal.

At this level, parameters should not be confused with regular sequences. A parameter can be a zero divisor, and successive parameter choices need not act injectively. What matters is only that the final quotient has dimension zero. This elementary notion is enough for finite-map and dimension bookkeeping; depth theory begins when one asks how the parameters act on modules.

### 8.2 Systems of parameters

Let $(R,\mathfrak m)$ be Noetherian local of dimension $d$. A sequence

$$
x_1,\ldots,x_d\in\mathfrak m
$$

is a **system of parameters** if

$$
\sqrt{(x_1,\ldots,x_d)}=\mathfrak m.
$$

Equivalently, $R/(x_1,\ldots,x_d)$ has Krull dimension zero. Since it is Noetherian local, this is equivalent to being Artinian. The ideal $Q=(x_1,\ldots,x_d)$ is a **parameter ideal**.

For $d=0$, the empty sequence is a system of parameters and the zero ideal is parameter: a zero-dimensional Noetherian local ring is already Artinian.

The height theorem shows that no $\mathfrak m$-primary ideal can be generated by fewer than $d$ elements. Thus a system of parameters uses the smallest number of elements with which dimension can possibly be killed, even though these elements need not minimally generate the maximal ideal.

### 8.3 Existence and dimension cutting

**Theorem.** Every Noetherian local ring of dimension $d$ has a system of parameters.

**Proof strategy.** Choose an element outside every top-dimensional minimal prime, so quotienting genuinely lowers dimension. Induction supplies parameters in the quotient. Krull's height theorem then shows that the drop was exactly one and that the resulting list has the required length.

**Proof.** If $d=0$, there is nothing to choose. For $d>0$, prime avoidance gives $x_1\in\mathfrak m$ outside the finitely many minimal primes $\mathfrak p$ satisfying $\dim R/\mathfrak p=d$. Any prime containing $x_1$ therefore has quotient dimension strictly below $d$, so, with $e=\dim R/(x_1)$, one has $e\leq d-1$. By induction, $R/(x_1)$ has a system of parameters of length $e$; lift it to elements $x_2,\ldots,x_{e+1}$ of $R$. Their ideal together with $x_1$ is $\mathfrak m$-primary. The height theorem says that an $\mathfrak m$-primary ideal needs at least $d$ generators, so $d\leq e+1$. Thus $e=d-1$, and $x_1,\ldots,x_d$ is a system of parameters. $\square$

With a slightly refined choice at each stage, one can arrange

$$
\dim R/(x_1,\ldots,x_i)=d-i
$$

for every $i$. This is a dimension-cutting statement only; it makes no assertion that multiplication by $x_i$ is injective on the preceding quotient.

### 8.4 Parameter ideals and finite quotients

If $Q$ is a parameter ideal, then $R/Q$ is Artinian and therefore has finite length. Conversely, if an ideal generated by $d$ elements has Artinian quotient, those generators form a system of parameters.

In a complete local ring, parameter ideals are closed and the quotient is complete automatically. Powers of a parameter ideal are cofinal with powers of $\mathfrak m$ because $Q$ is $\mathfrak m$-primary. Thus the $Q$-adic and maximal-adic topologies agree.

For a finite $R$-module $M$, the quotient $M/QM$ has finite length. This gives a finite shadow of $M$ adapted to dimension rather than to a fixed maximal-ideal power. We do not attach multiplicities or depth to this quotient here.

### 8.5 Examples and limitations

In $k[[X,Y]]/(XY)$, the element $X+Y$ is a parameter: quotienting by it gives

$$
k[[X]]/(X^2),
$$

which is Artinian. Neither $X$ nor $Y$ is a parameter, because quotienting by one leaves a one-dimensional branch. Parameters can nevertheless be zero divisors in nonreduced or reducible rings, so “parameter” must not be read as “non-zero-divisor.”

In $k[[X,Y]]/(X^2,XY)$, the element $Y$ is a parameter and the quotient is $k[[X]]/(X^2)$. Yet $Y$ kills the nonzero class of $X$, so it is a zero divisor. Dimension cutting alone gives no regularity of action.

In a $d$-dimensional regular local ring, any minimal generating set of the maximal ideal is a system of parameters. The converse is false: a singular ring still has systems of parameters, but its maximal ideal needs more than $d$ generators. That excess is precisely the gap between embedding dimension and dimension.

### 8.6 Non-zero-divisors and regular sequences

Dimension measures how many equations can cut a space; injectivity measures whether an equation cuts without killing an existing component. Let $M$ be a finite module over a local ring $(R,\mathfrak m)$. An element $x\in\mathfrak m$ is **$M$-regular** if multiplication

$$
M\xrightarrow{x}M
$$

is injective and $M/xM\neq0$. A sequence $x_1,\ldots,x_c\in\mathfrak m$ is **$M$-regular** if $x_i$ is regular on

$$
M/(x_1,\ldots,x_{i-1})M
$$

for every $i$. For $M=R$ we simply say **regular sequence**.

The order matters in the definition, although in a Noetherian local ring permutations of a regular sequence are again regular. The local hypothesis and the requirement that all elements lie in $\mathfrak m$ exclude the vacuous use of units.

**Proposition (dimension drop).** If $x$ is a non-zero-divisor on a nonzero Noetherian local ring $R$, then

$$
\dim R/xR=\dim R-1.
$$

Consequently, if $x_1,\ldots,x_c$ is a regular sequence, then

$$
\dim R/(x_1,\ldots,x_c)=\dim R-c.
$$

**Proof strategy.** The principal ideal theorem gives a drop of at most one. The non-zero-divisor hypothesis keeps $x$ out of every associated minimal prime, so every prime minimal above $(x)$ has height exactly one over a minimal prime of maximal dimension.

**Proof.** Every prime minimal over $(x)$ has height at most one above some minimal prime by the principal ideal theorem. It cannot itself be minimal in $R$, since a zero divisor in a Noetherian ring is contained in an associated prime and every minimal prime is associated; the hypothesis excludes this. Thus the height increase is exactly one along the components that attain the dimension. Taking the supremum of chains gives the first equality. Apply it successively in the quotient rings to obtain the second. $\square$

The converse is false without further hypotheses. In the reduced node $k[[X,Y]]/(XY)$, quotienting by $X$ leaves dimension one, so no drop occurs; $X$ is a zero divisor. But a zero divisor can sometimes lower the maximum dimension by one if it kills only lower-dimensional embedded information. Dimension alone does not detect injectivity.

### 8.7 Depth and Cohen--Macaulay rings

The **depth** of a nonzero finite $R$-module $M$ is the largest length of an $M$-regular sequence in $\mathfrak m$. We put $\operatorname{depth}_R0=\infty$. Every regular sequence cuts support dimension once at each step, so

$$
\operatorname{depth}_RM\leq\dim\operatorname{Supp}_R(M).
$$

A Noetherian local ring $R$ is **Cohen--Macaulay** if

$$
\operatorname{depth}R=\dim R.
$$

Equivalently, some system of parameters is a regular sequence; in that case every system of parameters is regular. The equivalence is worth seeing. A regular sequence of length $d=\dim R$ has an Artinian quotient by the dimension-drop proposition, so it is a system of parameters. Conversely, if depth is $d$, a maximal regular sequence has length $d$ and its quotient has dimension zero. For the assertion about every system, choose the parameters one at a time. In a Cohen--Macaulay ring no associated prime has dimension below $d$; a parameter avoids all associated primes and is therefore a non-zero-divisor. The quotient remains Cohen--Macaulay of dimension $d-1$, and induction finishes.

The key exact-sequence rule is the **depth lemma**. If

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

is exact with finite modules over a local ring, then

$$
\operatorname{depth}M\geq
\min(\operatorname{depth}M',\operatorname{depth}M''),
$$

with the two companion inequalities obtained by cyclically moving one term and increasing the smaller depth by one. To prove it, choose an element outside the finite union of associated primes obstructing regularity on the relevant modules, reduce the sequence modulo that element, and induct. The connecting kernel after reduction is exactly the submodule killed by the element, so regularity on two terms supplies regularity on the third in precisely the stated ranges.

Depth is the module-theoretic refinement of dimension needed in patching. A parameter may cut dimension while killing torsion; a regular parameter cuts dimension and preserves exact control.

### 8.8 Regular local rings are Cohen--Macaulay

Let $(P,\mathfrak n)$ be regular local of dimension $d$, and choose a minimal generating set $x_1,\ldots,x_d$ of $\mathfrak n$. Section 7.3 identifies

$$
\operatorname{gr}_{\mathfrak n}P\simeq k[T_1,\ldots,T_d].
$$

The sequence $x_1,\ldots,x_d$ is regular. We prove the first step; the rest follows after quotienting. Suppose $x_1a=0$ with $a\neq0$, and choose the least $n$ with $a\in\mathfrak n^n\setminus\mathfrak n^{n+1}$. In the associated graded ring,

$$
T_1\operatorname{in}(a)=0,
$$

which is impossible in a polynomial ring. Hence $x_1$ is a non-zero-divisor. The associated graded ring of $P/x_1P$ is $k[T_2,\ldots,T_d]$, so the quotient is regular of dimension $d-1$. Induction proves regularity of the full sequence.

Therefore every regular local ring is Cohen--Macaulay. In the power-series sources used here this is also visible directly:

$$
X_1,\ldots,X_r
$$

is regular in $k[[X_1,\ldots,X_r]]$, while

$$
\varpi,X_1,\ldots,X_r
$$

is regular in $\mathcal O[[X_1,\ldots,X_r]]$ for a coefficient discrete valuation ring.

### 8.9 Quotients by regular sequences

Let $P$ be Cohen--Macaulay local of dimension $d$, and let $f_1,\ldots,f_c$ be a $P$-regular sequence. Repeated dimension drop gives

$$
\dim P/(f_1,\ldots,f_c)=d-c.
$$

The quotient is again Cohen--Macaulay: a system of parameters of the quotient lifts to elements which, appended to the $f_i$, form a system of parameters of $P$; in a Cohen--Macaulay ring that full system is regular, so the lifted tail is regular on the quotient.

There is also a converse in the form used for presentations.

**Theorem (height equals number of equations).** Let $P$ be Cohen--Macaulay local and let $I=(f_1,\ldots,f_c)$ be generated minimally by $c$ elements. If

$$
\operatorname{ht}(I)=c,
$$

then $f_1,\ldots,f_c$ is a regular sequence.

**Proof strategy.** Choose among the generators an element outside the finitely many associated primes of $P$ that contain too little of $I$. It is a non-zero-divisor. The height of the remaining ideal modulo that element is $c-1$, and induction applies. Minimality ensures that the remaining images still need $c-1$ generators.

**Proof.** Since $\operatorname{ht}I>0$, the ideal $I$ is not contained in any associated prime of height zero of the Cohen--Macaulay ring $P$. If the residue field is finite, first make the faithfully flat local extension $P\to P[T]_{\mathfrak nP[T]}$, whose residue field $k(T)$ is infinite; height, minimal number of generators, and regularity all descend along this extension. Over an infinite residue field, prime avoidance permits a linear change of the minimal generators so that $f_1$ avoids every associated prime; it is a non-zero-divisor. The quotient $P/(f_1)$ is Cohen--Macaulay. The image $I'$ of $I$ has height $c-1$: prime chains above $I$ lose exactly the first regular cut. Its remaining $c-1$ displayed generators are minimal by reduction of $I/\mathfrak nI$. Induction makes them regular in the quotient. Faithful flatness descends injectivity of each multiplication map, so the conclusion holds over the original ring. $\square$

The height condition is essential. In $k[[X,Y]]$, the ideal $(X^2,XY)$ has two minimal generators but height one. Its generators cannot be a regular sequence because $XY$ is killed modulo $X^2$ by the nonzero class of $X$.

### 8.10 Complete intersections

A complete Noetherian local ring $R$ is a **complete intersection** over a fixed coefficient base if it has a presentation

$$
R\simeq P/(f_1,\ldots,f_c),
$$

where $P$ is a regular complete local power-series ring over that base and $f_1,\ldots,f_c$ is a $P$-regular sequence. A hypersurface is the case $c=1$. The empty sequence gives a regular local ring.

For a minimal Cohen presentation $R=P/I$, the following numerical criterion is exact:

$$
R\text{ is a complete intersection}
\quad\Longleftrightarrow\quad
\mu_P(I)=\operatorname{ht}(I).
$$

The forward direction follows because a regular sequence of length $c$ has height $c$. For the reverse direction, choose a minimal set of $c=\mu_P(I)$ generators and apply the theorem of Section 8.9. Coordinate changes between minimal Cohen presentations preserve the criterion. Thus the property does not depend on the chosen minimal coordinates over the fixed coefficient structure.

Every complete intersection is Cohen--Macaulay, and

$$
\dim R=\dim P-c.
$$

It is not generally regular: $k[[X,Y]]/(XY)$ is a hypersurface and hence a complete intersection, but its embedding dimension exceeds its dimension. Nor is every Cohen--Macaulay ring a complete intersection. The Artinian ring

$$
k[[X,Y]]/(X,Y)^2
$$

is Cohen--Macaulay because its dimension and depth are both zero, but its defining ideal has height two and needs three generators.

### 8.11 Regular sequences under flat base change

Let $P\to P'$ be flat and local. If $f_1,\ldots,f_c$ is $P$-regular and $P'/(f_1,\ldots,f_c)P'$ is nonzero, then their images form a $P'$-regular sequence. Tensor the exact multiplication sequence

$$
0\longrightarrow P/(f_1,\ldots,f_{i-1})
\xrightarrow{f_i}
P/(f_1,\ldots,f_{i-1})
$$

with $P'$. Flatness preserves injectivity at every step. The nonzero quotient condition prevents a terminal unit.

Consequently flat coefficient extension preserves complete-intersection presentations when the kernel base-changes exactly. Nonflat specialization can behave differently. The regular element $\varpi$ in $\mathcal O$ becomes zero after passage to $k$, so a presentation involving it may lose both a relation and a dimension. Flatness is the hypothesis that keeps independent equations independent.

## 9. Finite local homomorphisms

### 9.1 Why finite maps matter

Maps of universal rings arise contravariantly from maps of deformation problems. In patching arguments, one often needs to know that a target ring is controlled by a source through finitely many module generators. Finiteness is strong enough to impose integrality, preserve prime-chain dimensions after accounting for the kernel, and make completion harmless. It is not the same as surjectivity, and it is not the same as faithfulness.

A homomorphism $A\to B$ is **finite** if $B$ is a finitely generated $A$-module. It is a **finite local homomorphism** when $A$ and $B$ are local and the map is local. Every surjective local map between Noetherian local rings is finite, generated by $1$ as a module. The converse fails: adjoining an integral element usually gives a finite inclusion rather than a quotient.

The distinction is geometrically important. A quotient map cuts out a closed subspace and induces an injection on prime sets. A finite injective map can fold or normalize a space while retaining its dimension. Algebraically, cotangent behavior separates these cases better than finiteness alone.

### 9.2 Integrality, lying over, and going up

If $B$ is finite over $A$, every $b\in B$ is integral over $A$: multiplication by $b$ on the finite module $B$ satisfies a monic polynomial by the determinant trick. Thus finite maps belong to the integral theory of primes.

Let $K=\ker(A\to B)$. Then $B$ is integral over $A/K$, and the following properties hold.

- **Lying over:** every prime of $A/K$ is the contraction of a prime of $B$.
- **Going up:** if $\mathfrak p_0\subseteq\mathfrak p_1$ in $A/K$ and $\mathfrak q_0$ lies over $\mathfrak p_0$, then some $\mathfrak q_1\supseteq\mathfrak q_0$ lies over $\mathfrak p_1$.
- **Incomparability:** two distinct primes of $B$ lying over the same prime of $A/K$ cannot contain one another.

Together these statements say that prime chains can be lifted and that contraction does not shorten a strict chain. They are exactly what dimension preservation needs.

**Proof idea for going up.** Localize $A/K$ at $\mathfrak p_1$ and $B$ at the multiplicative set below it, then quotient by $\mathfrak q_0$. One reduces to lying over for an integral extension of domains over a local base. A maximal ideal of the localized integral algebra contracts to the maximal ideal of the base, giving the desired prime. The other assertions follow from the same localization and integrality argument.

### 9.3 The exact dimension formula

**Theorem.** If $A\to B$ is finite, then

$$
\dim B=\dim(A/\ker(A\to B)).
$$

**Proof strategy.** Contract a chain in $B$ and use incomparability for one inequality. Lift a chain from $A/K$ by going up for the other.

**Proof.** A strict chain of primes in $B$ contracts to a strict chain in $A/K$: contractions contain $K$, and equality of two consecutive contractions would contradict incomparability. Hence $\dim B\leq\dim A/K$. Conversely, start with a prime chain in $A/K$. Lying over chooses a prime above its first term, and repeated going up lifts the entire chain. Thus $\dim B\geq\dim A/K$. $\square$

Consequently

$$
\dim B\leq\dim A,
$$

with equality whenever $A\to B$ is injective. The formula, not the inequality, is the reliable statement. A finite map with nonzero kernel can lower dimension exactly as its kernel does.

For a finite local map, one can also calculate the dimension through the closed fiber only under additional hypotheses; finiteness by itself gives the exact kernel formula above and nothing stronger is needed.

### 9.4 Faithfully finite maps

View $B$ as an $A$-module. Its annihilator is

$$
\operatorname{Ann}_A(B)=\ker(A\to B),
$$

because an element killing $B$ in particular kills $1$. Therefore $B$ is a faithful $A$-module exactly when the ring map is injective.

A **faithfully finite map** in this book means a finite map for which $B$ is faithful as an $A$-module. Such a map is injective, and hence

$$
\dim B=\dim A.
$$

The word *faithful* is essential. The quotient $A\to A/I$ is finite, but it is faithful only when $I=0$. Thus one must not infer dimension preservation merely from module-finiteness.

For any local homomorphism $A\to B$, if $B$ is a nonzero finite $A$-module then it is faithfully flat only under the much stronger assumption of flatness; finite and faithful does not mean flat. In this book, “faithfully finite” records injective control and dimension preservation, not flat descent.

### 9.5 Residue fields and maximal ideals

Let $(A,\mathfrak m_A,k_A)\to(B,\mathfrak m_B,k_B)$ be finite local. Then $k_B$ is a finite extension of $k_A$. Indeed, $B/\mathfrak m_AB$ is a finite-dimensional $k_A$-algebra, and its quotient by $\mathfrak m_B/\mathfrak m_AB$ is $k_B$.

The ideal $\mathfrak m_AB$ is $\mathfrak m_B$-primary. The quotient $B/\mathfrak m_AB$ is Artinian local, so its maximal ideal is nilpotent. Hence for some $N$,

$$
\mathfrak m_B^N\subseteq\mathfrak m_AB\subseteq\mathfrak m_B.
$$

Therefore the $\mathfrak m_A$-adic topology induced on $B$ and the intrinsic $\mathfrak m_B$-adic topology are equivalent. This cofinality is the key to completion.

If the two rings belong to a fixed-residue deformation category, then the residue extension is the specified identity $k_A=k_B=k$. Outside that category, silently identifying the residue fields would corrupt tangent-space formulas.

### 9.6 Finite maps and completion

Let $(A,\mathfrak m_A)$ be Noetherian and let $B$ be a finite $A$-algebra. Completion commutes with this finite module:

$$
B\otimes_A\widehat A
\xrightarrow{\sim}
\varprojlim_n B/\mathfrak m_A^nB.
$$

If $B$ is local and finite over the local ring $A$, the topology on the right is equivalent to the $\mathfrak m_B$-adic topology. Thus

$$
\widehat B\simeq B\otimes_A\widehat A.
$$

In particular, if $A$ is complete, every finite local $A$-algebra $B$ is complete. It is also Noetherian. This is why finite algebra extensions stay inside the complete local world without requiring a second completion step.

If a finite $A$-algebra is not local, completion at $\mathfrak m_A$ can decompose into a finite product of completions at maximal ideals over $\mathfrak m_A$. The local hypothesis selects one factor. In deformation theory the fixed closed point normally supplies this selection.

### 9.7 Finite does not mean quotient

Let

$$
A=k[[T^2,T^3]]\simeq k[[U,V]]/(V^2-U^3)
\subseteq B=k[[T]].
$$

The element $T$ is integral over $A$, satisfying $Z^2-T^2=0$ with $T^2\in A$, and $B$ is generated by $1,T$ as an $A$-module. The inclusion is finite, local, injective, and hence faithful. Both rings have dimension one. It is not surjective because $T\notin A$.

The cotangent map

$$
\mathfrak m_A/\mathfrak m_A^2\longrightarrow
\mathfrak m_B/\mathfrak m_B^2
$$

is zero: $T^2$ and $T^3$ vanish modulo $(T)^2$. Thus finite faithful maps can decrease embedding dimension and need not resemble quotient maps.

By contrast, if a local map of complete Noetherian rings with the same residue field is finite and surjective on cotangent spaces, the cotangent criterion makes it surjective as a ring map. If it is also faithful, it is both injective and surjective, hence an isomorphism. This compact criterion will reappear in the patching dictionary.

## 10. Finite modules as geometric detectors

### 10.1 Support and annihilators

A ring appearing in patching often acts on a finite module rather than being compared directly with another ring. The module sees only those prime ideals at which it remains nonzero. This is encoded by support.

For a finite $R$-module $M$, define

$$
\operatorname{Supp}_R(M)
=\{\mathfrak p\in\operatorname{Spec}R:M_{\mathfrak p}\neq0\}.
$$

Then

$$
\operatorname{Supp}_R(M)=V(\operatorname{Ann}_R(M)).
$$

**Proof strategy.** If an annihilator becomes a unit after localization, the module vanishes. Conversely, if a finite module vanishes after localization, one denominator kills all finitely many generators and becomes an annihilator outside the prime.

**Proof.** If $a\in\operatorname{Ann}M$ and $a\notin\mathfrak p$, then $a$ is a unit in $R_{\mathfrak p}$ and kills $M_{\mathfrak p}$, so the localization is zero. Conversely, choose generators $m_1,\ldots,m_r$. If $M_{\mathfrak p}=0$, for each $i$ some $s_i\notin\mathfrak p$ kills $m_i$. Their product $s\notin\mathfrak p$ kills all of $M$, so $\operatorname{Ann}M\not\subseteq\mathfrak p$. $\square$

Thus the support has dimension

$$
\dim\operatorname{Supp}_R(M)
=\dim R/\operatorname{Ann}_R(M).
$$

This is the module-theoretic form of the kernel formula for finite ring maps.

### 10.2 Faithful modules

A module $M$ is **faithful** if $\operatorname{Ann}_R(M)=0$. For a finite module, this is equivalent to

$$
\operatorname{Supp}_R(M)=\operatorname{Spec}R.
$$

Consequently a faithful finite module has full-dimensional support:

$$
\dim\operatorname{Supp}_R(M)=\dim R.
$$

The converse “full dimension implies faithful” is false. In a ring with several components, a module can be supported on one component of maximal dimension while being annihilated by the others. For example, in $R=k[[X,Y]]/(XY)$, the module $R/(X)$ has dimension one, equal to $\dim R$, but its annihilator $(X)$ is nonzero.

Faithfulness is therefore a statement about seeing every function, not merely about attaining the largest component dimension. Later arguments that promote module information to ring information must establish the actual annihilator statement.

### 10.3 What reduction modulo the maximal ideal detects

For a finite module $M$ over $(R,\mathfrak m,k)$,

$$
M=0\quad\Longleftrightarrow\quad M/\mathfrak mM=0,
$$

and

$$
\mu_R(M)=\dim_kM/\mathfrak mM.
$$

For a map $f:M\to N$ of finite modules,

$$
f\text{ is surjective}
\quad\Longleftrightarrow\quad
\bar f:M/\mathfrak mM\to N/\mathfrak mN
\text{ is surjective}.
$$

All three statements follow by applying Nakayama to $M$, or to the cokernel of $f$.

Injectivity is not detected this way. The quotient map

$$
R/(X^2)\twoheadrightarrow R/(X)
$$

for $R=k[[X]]$ induces an isomorphism after reduction modulo $\mathfrak m$, yet has nonzero kernel generated by $X$. Even the dimensions of the closed fibers do not measure torsion hidden at higher order.

Flatness or a known free rank can turn this into an injectivity statement, as Sections 10.6--10.11 explain. Without such an additional hypothesis the safe rule is asymmetric: residue reduction detects zero objects, generators, and surjections of finite modules; it does not by itself detect injections, faithfulness, or freeness.

### 10.4 Closed submodules and exact limits

Let $R$ be complete Noetherian local and

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

an exact sequence of finite modules. Every term is complete, $M'$ is closed in $M$, and

$$
0\longrightarrow
\varprojlim_nM'/\mathfrak m^nM'
\longrightarrow
\varprojlim_nM/\mathfrak m^nM
\longrightarrow
\varprojlim_nM''/\mathfrak m^nM''
\longrightarrow0
$$

is exact. Artin--Rees is the decisive input: it makes the filtration induced on $M'$ cofinal with its intrinsic maximal-adic filtration.

Consequently, an $R$-linear action on compatible finite quotients defines an action on the limit, and a compatible system of surjections between finite modules remains surjective at the limit once the resulting modules are known to be finite. These statements should not be transferred to arbitrary inverse systems without a Mittag--Leffler or finiteness argument.

### 10.5 Examples of support and failure of detection

For $R=k[[X,Y]]/(XY)$, the ideals $(X)$ and $(Y)$ are the two minimal primes. The modules $R/(X)$ and $R/(Y)$ each see one branch. Their direct sum is faithful because

$$
\operatorname{Ann}(R/(X)\oplus R/(Y))
=(X)\cap(Y)=0
$$

inside the reduced node. Thus several nonfaithful modules can jointly detect the whole ring.

For the nonreduced ring $R=k[[X]]/(X^2)$, the residue field $k=R/(X)$ has support equal to the only point of $\operatorname{Spec}R$, hence full support, but is not faithful because $X$ annihilates it. Topological support does not see nilpotent functions.

Finally, $M=R^a$ is faithful for every $a>0$, and its closed fiber has dimension $a$. The converse is false: knowing $\dim_kM/\mathfrak mM=a$ only gives the number of generators, not a free basis. Relations among their lifts may occur in higher order.

### 10.6 Why coefficient flatness is torsion control

Let $(\mathcal O,(\varpi),k)$ be a discrete valuation ring. A deformation ring over $\mathcal O$ is meant to connect its special fiber to characteristic-zero information. If $\varpi$ kills a nonzero element, part of the ring exists only in the special fiber. Flatness is the condition excluding precisely this phenomenon.

An $\mathcal O$-module $M$ is **torsion-free** if

$$
\varpi m=0\quad\Longrightarrow\quad m=0.
$$

Because every nonzero element of $\mathcal O$ is a unit times a power of $\varpi$, this is equivalent to having no nonzero element killed by any nonzero coefficient.

**Theorem (flatness over a discrete valuation ring).** An $\mathcal O$-module is flat if and only if it is torsion-free.

**Proof strategy.** Flatness preserves the injection $(\varpi^n)\hookrightarrow\mathcal O$, giving torsion-freeness. Conversely, the criterion for flatness may be tested on finitely generated ideals; every such ideal is principal, and torsion-freeness makes the relevant multiplication map injective.

**Proof.** If $M$ is flat, tensoring

$$
0\longrightarrow\mathcal O\xrightarrow{\varpi} \mathcal O
$$

with $M$ proves that multiplication by $\varpi$ on $M$ is injective. Conversely, flatness of a module over a ring is equivalent to injectivity of

$$
J\otimes_{\mathcal O}M\longrightarrow M
$$

for every finitely generated ideal $J$. Here $J=(\varpi^n)$ is free of rank one, and the displayed map identifies with multiplication by $\varpi^n$, which is injective on a torsion-free module. $\square$

For an $\mathcal O$-algebra $R$, therefore,

$$
R\text{ is }\mathcal O\text{-flat}
\quad\Longleftrightarrow\quad
\varpi\text{ is a non-zero-divisor on }R.
$$

This is the flatness test used throughout the mixed-characteristic theory.

### 10.7 Finite flat modules are free

Let $A$ be a Noetherian local ring and let $M$ be a finite flat $A$-module. Then $M$ is free. Choose elements $m_1,\ldots,m_r$ lifting a basis of $M/\mathfrak m_AM$. Nakayama gives a surjection

$$
A^r\twoheadrightarrow M.
$$

Let $K$ be its kernel. Since $M$ is flat, tensoring the sequence with $A/\mathfrak m_A$ remains exact on the left. The chosen basis makes $K/\mathfrak m_AK=0$. The kernel is finite because $A$ is Noetherian, so Nakayama gives $K=0$. Thus $M\simeq A^r$.

Over a discrete valuation ring this combines with Section 10.6:

$$
M\text{ finite and torsion-free}
\quad\Longleftrightarrow\quad
M\text{ finite free}.
$$

If $R$ is a nonzero finite flat local $\mathcal O$-algebra with residue field $k$, its rank is

$$
\operatorname{rank}_{\mathcal O}R
=\dim_k R/\varpi R.
$$

The equality follows by reducing a free basis. Thus the length of the special fiber measures the degree of a finite flat coefficient algebra exactly.

### 10.8 The torsion exact sequence and specialization

For any $\mathcal O$-module $M$, tensor the exact sequence

$$
0\longrightarrow\mathcal O\xrightarrow{\varpi}\mathcal O
\longrightarrow k\longrightarrow0
$$

with $M$. The resulting exact sequence begins

$$
0\longrightarrow M[\varpi]
\longrightarrow M\xrightarrow{\varpi}M
\longrightarrow M/\varpi M\longrightarrow0,
$$

where

$$
M[\varpi]=\{m\in M:\varpi m=0\}.
$$

Equivalently, the failure of tensoring with $k$ to preserve the injection on the left is exactly $M[\varpi]$. This makes coefficient torsion visible at the first derived stage, but no derived language is needed for the calculation.

For a finite $R$-module $M$ over an $\mathcal O$-flat complete local algebra, the special fiber $M/\varpi M$ cannot by itself detect whether $M$ is $\mathcal O$-torsion-free. One must inspect the kernel of multiplication by $\varpi$. For example,

$$
M=\mathcal O\oplus k
$$

has a nonzero special fiber and a free summand, but its second summand is pure coefficient torsion.

### 10.9 Flatness of a presented algebra

Let $P=\mathcal O[[X_1,\ldots,X_r]]$ and $R=P/I$. Since $P$ is $\mathcal O$-flat, multiplication by $\varpi$ on $R$ is injective exactly when

$$
(I:\varpi)=I,
$$

where

$$
(I:\varpi)=\{a\in P:\varpi a\in I\}.
$$

Indeed a class $\bar a\in R$ is killed by $\varpi$ precisely when $a\in(I:\varpi)$, and it is zero precisely when $a\in I$. Thus the colon-ideal equality is an exact presentation test for flatness.

The relation $\varpi X$ illustrates failure:

$$
R=\mathcal O[[X]]/(\varpi X)
$$

has $X\in(I:\varpi)\setminus I$. The special fiber is $k[[X]]$, while the generic fiber is the coefficient fraction field: the entire $X$-branch disappears after inverting $\varpi$.

By contrast,

$$
R=\mathcal O[[X,Y]]/(XY-\varpi)
$$

is flat. The source is a domain and $XY-\varpi$ is not divisible by $\varpi$; if $\varpi a$ lies in the principal ideal, reduction modulo $\varpi$ shows that $XY$ divides the reduction of $a$. Lifting the quotient and iterating $\varpi$-adically yields $a\in(XY-\varpi)$. Equivalently, the quotient is the regular local domain already identified in Section 7.5, so $\varpi=XY$ is nonzero.

### 10.10 Dimension of special and generic fibers

Let $R$ be a nonzero complete Noetherian local $\mathcal O$-algebra which is flat over the discrete valuation ring $\mathcal O$. Then $\varpi$ is a non-zero-divisor, and Section 8.6 gives

$$
\dim R/\varpi R=\dim R-1.
$$

The special fiber therefore has exactly one dimension less than the total ring. The generic fiber $R[1/\varpi]$ need not be local, but every maximal-dimensional component of $R$ meets it because $\varpi$ lies in no minimal prime. In the topologically finite-type setting its dimension is also $\dim R-1$.

Without flatness the special fiber can have the same dimension as the total ring. For $R=\mathcal O[[X]]/(\varpi X)$, both $R$ and $R/\varpi R\simeq k[[X]]$ have dimension one. The vertical component prevents the expected drop.

If $R$ is finite over $\mathcal O$, then $\dim R\leq1$. When $R$ is nonzero and $\mathcal O$-flat, integrality and injectivity give $\dim R=1$ and the generic fiber is a nonzero finite-dimensional algebra over the fraction field. When $R$ is killed by a power of $\varpi$, it has dimension zero. Mixed horizontal and vertical components require separate torsion analysis.

### 10.11 Exactness under completed scalar extension

Let $\mathcal O\to\mathcal O'$ be a flat local map of complete Noetherian coefficient rings. Let $R$ be a topologically finite-type complete $\mathcal O$-algebra, put

$$
R'=R\widehat\otimes_{\mathcal O}\mathcal O',
$$

and assume that $R'$ is flat over $R$. This last hypothesis holds in the coefficient extensions used below, such as finite flat local extensions and extensions of coefficient fields, but it must not be inferred from the completion symbol alone. If

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

is an exact sequence of finite $R$-modules, finite presentation gives natural identifications

$$
M\widehat\otimes_{\mathcal O}\mathcal O'
\simeq M\otimes_RR',
$$

and similarly for $M'$ and $M''$. Tensoring the sequence over $R$ with the flat $R$-algebra $R'$ therefore gives

$$
0\longrightarrow
M'\widehat\otimes_{\mathcal O}\mathcal O'
\longrightarrow
M\widehat\otimes_{\mathcal O}\mathcal O'
\longrightarrow
M''\widehat\otimes_{\mathcal O}\mathcal O'
\longrightarrow0
$$

as an exact sequence.

This is the legitimate reason the indicated flat completed coefficient extensions preserve kernels, relation modules, and regular sequences. Ordinary flatness of $\mathcal O'$ over $\mathcal O$ does not by itself justify claiming that an uncompleted tensor product is already complete. Completion alone is not exact on arbitrary modules, and a nonflat coefficient quotient can create a kernel. The map $\mathcal O\to k$ sends the injection $\mathcal O\xrightarrow{\varpi}\mathcal O$ to the zero map $k\to k$, the smallest possible counterexample.

## 11. Completed tensor products

### 11.1 Combining two formal local problems

Two deformation problems over the same coefficient ring can often be chosen independently. On representing rings, independence is expressed by a completed tensor product. The ordinary tensor product contains only finite sums and is generally incomplete; it misses formal series involving unbounded degrees from both factors. Completion restores exactly those convergent combinations.

For example,

$$
k[[X]]\widehat\otimes_k k[[Y]]
\simeq k[[X,Y]],
$$

whereas $k[[X]]\otimes_k k[[Y]]$ does not contain every two-variable formal series. The topology is part of the construction, not an afterthought.

The cleanest theory requires both algebras to have compatible residue field and to be topologically of finite type over the base. Under these hypotheses the completed tensor product stays complete Noetherian local and has a concrete presentation.

### 11.2 Construction and universal property

Let $(A,\mathfrak a)$ be complete Noetherian local, and let $(R,\mathfrak m)$ and $(S,\mathfrak n)$ be complete local $A$-algebras. Define

$$
R\widehat\otimes_AS
=\varprojlim_{p,q}
(R/\mathfrak m^p)\otimes_A(S/\mathfrak n^q),
$$

with the inverse-limit topology. Under the finite-type hypotheses used below, this agrees with completing $R\otimes_AS$ for the ideal generated by the images of $\mathfrak m$ and $\mathfrak n$.

Its universal property is topological: for a complete separated local $A$-algebra $U$, continuous local maps

$$
R\widehat\otimes_AS\longrightarrow U
$$

correspond to pairs of continuous local $A$-maps $R\to U$ and $S\to U$. Multiplication combines the pair on the ordinary tensor product; continuity and completeness extend it uniquely.

The residue compatibility matters. If $R$ and $S$ have residue field $k$ and both structural maps agree with $A\to k$, then the completed product has the intended single closed point. If the residue fields tensor to a product or a nonfield, locality can fail.

### 11.3 Noetherianity and locality

Assume

$$
R=A[[X_1,\ldots,X_r]]/I,
\qquad
S=A[[Y_1,\ldots,Y_s]]/J,
$$

with local residue-compatible structure maps. Then

$$
R\widehat\otimes_AS
\simeq
A[[X_1,\ldots,X_r,Y_1,\ldots,Y_s]]/(I,J),
$$

where the two ideals are extended to the common power-series ring. This proves that the result is Noetherian, complete, and local. Its maximal ideal is generated by the image of $\mathfrak a$, all $X_i$, and all $Y_j$.

Every admissible complete local $A$-algebra with the same residue field is topologically of finite type over $A$: lift a finite basis of its relative cotangent space and use the cotangent surjectivity criterion. Hence the concrete formula covers the category used in deformation theory.

Outside this setting, an inverse-limit completed tensor product is still a complete topological algebra, but it need not be Noetherian or local. Noetherianity must come from a finite power-series presentation, not from the completion symbol alone.

### 11.4 Relative tangent spaces add

Let $T=R\widehat\otimes_AS$ in the residue-compatible topologically finite-type setting, with common residue field $k$. Then

$$
C_{T/A}\simeq C_{R/A}\oplus C_{S/A}.
$$

**Proof strategy.** Choose presentations, reduce the common maximal ideal modulo its square and the base ideal, and observe that the $X$- and $Y$-linear terms cannot mix.

**Proof.** In the joint presentation, the relative cotangent space of the source is the direct sum of the spans of the $X_i$ and $Y_j$. Relations from $I$ involve only $X$-variables and relations from $J$ only $Y$-variables. Their linear images therefore impose exactly the separate cotangent relations defining $C_{R/A}$ and $C_{S/A}$. Taking the quotient gives the direct sum. $\square$

Consequently

$$
\operatorname{edim}_A T
=\operatorname{edim}_A R+\operatorname{edim}_A S.
$$

Over a field this is also the absolute tangent formula. Over a discrete valuation ring, absolute cotangent spaces do **not** simply add: the one coefficient direction is shared, and it may map noninjectively into either factor. Relative spaces are the correct invariant for completed products over the coefficient base.

### 11.5 Dimension over a field

Let $R$ and $S$ be complete Noetherian local $k$-algebras with residue field $k$. Then

$$
\dim(R\widehat\otimes_kS)=\dim R+\dim S.
$$

One proof uses presentations and the dimension theory of formal fibers over a field. More geometrically, the projection from the formal product to either factor is flat, and every closed fiber is the other formal local space; the dimension formula for flat local maps adds base and fiber dimensions.

For quotients

$$
R=k[[\mathbf X]]/I,
\qquad
S=k[[\mathbf Y]]/J,
$$

the formula reads

$$
\dim k[[\mathbf X,\mathbf Y]]/(I,J)
=\dim k[[\mathbf X]]/I+\dim k[[\mathbf Y]]/J.
$$

The field hypothesis prevents a common coefficient direction or coefficient torsion from coupling the factors.

### 11.6 Dimension over a discrete valuation ring

Let $\mathcal O$ be a complete discrete valuation ring. Suppose $R$ and $S$ are nonzero complete Noetherian local $\mathcal O$-algebras, topologically of finite type and flat over $\mathcal O$, and that both structural maps induce the same residue field $k$. Then their completed tensor product is complete Noetherian local, is $\mathcal O$-flat, and

$$
\dim(R\widehat\otimes_{\mathcal O}S)
=\dim R+\dim S-1.
$$

The subtraction reflects the shared one-dimensional coefficient base.

**Proof strategy.** Flatness over a discrete valuation ring is equivalent to absence of $\varpi$-torsion. It makes $\varpi$ a non-zero-divisor on each nonzero ring and on the completed tensor product. Quotient by $\varpi$, use the field formula, and restore the one coefficient dimension.

**Proof.** Flatness gives

$$
\dim R=1+\dim(R/\varpi R),
\qquad
\dim S=1+\dim(S/\varpi S).
$$

The completed tensor product $T$ remains $\mathcal O$-flat in this topologically finite-type setting, and

$$
T/\varpi T
\simeq(R/\varpi R)\widehat\otimes_k(S/\varpi S).
$$

The field formula gives

$$
\dim(T/\varpi T)
=(\dim R-1)+(\dim S-1).
$$

Adding back the non-zero-divisor $\varpi$ yields the claimed equality. $\square$

Without flatness the equality can fail. Take $R=S=k=\mathcal O/(\varpi)$. Then

$$
R\widehat\otimes_{\mathcal O}S\simeq k
$$

has dimension zero, whereas the expression $\dim R+\dim S-1$ equals $-1$. Coefficient torsion destroys the flat dimension formula.

### 11.7 Examples and topology warnings

First,

$$
\frac{k[[X]]}{(X^a)}\widehat\otimes_k
\frac{k[[Y]]}{(Y^b)}
\simeq\frac{k[[X,Y]]}{(X^a,Y^b)}.
$$

Both factors and the product have dimension zero. The relative tangent dimensions add to two.

Second,

$$
\mathcal O[[X]]\widehat\otimes_{\mathcal O}
\frac{\mathcal O[[Y]]}{(Y^2-\varpi)}
\simeq
\frac{\mathcal O[[X,Y]]}{(Y^2-\varpi)}.
$$

The second factor is finite free over $\mathcal O$ and the first is flat, so dimensions are $2$, $1$, and $2=2+1-1$. The uniformizer is shared, not duplicated.

Third,

$$
\frac{k[[X,Y]]}{(XY)}\widehat\otimes_k k[[Z]]
\simeq\frac{k[[X,Y,Z]]}{(XY)}.
$$

The node acquires one independent smooth direction; both dimension and embedding dimension increase by one.

Finally, closures in quotient formulas are indispensable outside Noetherian settings. Under our hypotheses every extended ideal is finitely generated and hence closed. If finite generation is dropped, quotienting before completion can differ from quotienting by the closure after completion, and the result can cease to be separated.

### 11.8 Fiber products solve a different problem

Completed tensor products combine two independent choices over a common base. Fiber products glue two coefficient rings that have already been identified after passing to a common quotient. The arrows point in the opposite pattern:

$$
\begin{array}{ccc}
D&\longrightarrow&B\\
\downarrow&&\downarrow\\
A&\longrightarrow&C,
\end{array}
\qquad
D=A\times_CB.
$$

Explicitly,

$$
A\times_CB=
\{(a,b)\in A\times B:\alpha(a)=\beta(b)\}.
$$

A map $T\to A\times_CB$ is the same as a pair of maps $T\to A$ and $T\to B$ whose composites to $C$ agree. This is a pullback universal property. By contrast, a map *out of* $A\widehat\otimes_CB$ is a pair of maps out of $A$ and $B$. Interchanging the two constructions reverses the deformation problem being represented.

### 11.9 Locality, completeness, and the exact sequence

Assume $A\twoheadrightarrow C$ and $B\twoheadrightarrow C$ are surjective local maps of complete Noetherian local rings inducing the same residue field. Then $D=A\times_CB$ is local, with

$$
\mathfrak m_D=
\mathfrak m_A\times_{\mathfrak m_C}\mathfrak m_B,
$$

and residue field equal to the common residue field. A pair is a unit exactly when either, hence both, of its residues is nonzero; its inverse is the compatible pair of inverses.

There is an exact sequence of rings viewed additively,

$$
0\longrightarrow D
\longrightarrow A\oplus B
\xrightarrow{(a,b)\mapsto\alpha(a)-\beta(b)}C
\longrightarrow0.
$$

It proves that $D$ is closed in the complete module $A\oplus B$, hence complete for the induced topology. It is Noetherian as well. The exact sequence shows that $A\oplus B$ is finite as a $D$-module, because the quotient is the cyclic $D$-module $C$. A subring over which a Noetherian ring is module-finite is Noetherian; the proof applies the determinant trick to finite module generators and then contracts finitely generated extended ideals. Thus $D$ is Noetherian. The induced topology and the maximal-ideal topology are cofinal, because the kernels of the finite-level projections have radical $\mathfrak m_D$. Hence $D$ is complete in its intrinsic maximal-adic topology.

The same exact sequence gives the length formula in the Artinian case:

$$
\ell(D)=\ell(A)+\ell(B)-\ell(C),
$$

when all residue fields are the same and length is measured in residue-field composition factors.

### 11.10 Prime spectra and dimension of a fiber product

Put $I_A=\ker(D\to A)$ and $I_B=\ker(D\to B)$. Their product is zero: an element supported in the $A$-kernel times one supported in the $B$-kernel vanishes coordinatewise. Every prime of $D$ therefore contains $I_A$ or $I_B$. Primes containing $I_A$ correspond to primes of $A$, and primes containing $I_B$ correspond to primes of $B$. The overlap consists of primes coming from $C$. Thus

$$
\operatorname{Spec}D
=\operatorname{Spec}A\cup_{\operatorname{Spec}C}\operatorname{Spec}B
$$

as a union of closed pieces, and

$$
\dim D=\max(\dim A,\dim B).
$$

This behavior differs sharply from a completed tensor product, whose dimensions add under flatness. A fiber product glues branches; it does not form their Cartesian product.

For example,

$$
k[[X]]\times_k k[[Y]]
\simeq k[[X,Y]]/(XY).
$$

The two one-dimensional formal discs are glued at their closed points. The result has dimension one, not two, and has two minimal primes.

### 11.11 Cotangent spaces of fiber products

The cleanest formula occurs when the common quotient is the residue field:

$$
D=A\times_kB.
$$

Then

$$
\mathfrak m_D=\mathfrak m_A\oplus\mathfrak m_B,
\qquad
\mathfrak m_D^2=\mathfrak m_A^2\oplus\mathfrak m_B^2,
$$

because mixed products vanish. Therefore

$$
C_D\simeq C_A\oplus C_B.
$$

For a general common quotient $C$, the cotangent space is the fiber product of the first-order compatibility conditions, with an additional term measuring the two kernels. It is safer to compute from

$$
\mathfrak m_D/\mathfrak m_D^2
$$

or from a presentation than to assert a direct sum. Directions already identified in $C$ must be identified, while kernel directions from the two sides remain independent.

### 11.12 Fiber products in lifting arguments

Let $A'\twoheadrightarrow A$ be a small extension and let $B\to A$ be any local map of Artinian coefficient rings. The pullback

$$
B'=A'\times_AB
$$

is an Artinian local ring and $B'\twoheadrightarrow B$ is again a small extension. Its kernel is canonically the kernel of $A'\to A$, with the residue-field action transported through $B$. This base-change stability is what permits obstruction classes to be compared after changing a test object.

If two lifts over $A'$ and $B$ agree over $A$, the universal property gives one object over the fiber product. Represented functors preserve this pullback automatically:

$$
h_R(A'\times_AB)
\simeq h_R(A')\times_{h_R(A)}h_R(B).
$$

This identity is categorical, whereas the completed tensor product identity

$$
h_{R\widehat\otimes_{\mathcal O}S}(T)
\simeq h_R(T)\times h_S(T)
$$

combines two represented functors. The two formulas look similar only because both involve pairs; their variance and their algebra are different.

## 12. Base change and formal smoothness

### 12.1 Base-changing a presentation

Let $\mathcal O\to\mathcal O'$ be a continuous local map of complete Noetherian local rings, and let

$$
R=\mathcal O[[X_1,\ldots,X_r]]/I.
$$

The completed coefficient extension is

$$
R'=R\widehat\otimes_{\mathcal O}\mathcal O'.
$$

In the topologically finite-presentation setting,

$$
R'\simeq
\mathcal O'[[X_1,\ldots,X_r]]/I',
$$

where $I'$ is the closed ideal generated by the image of $I$. Since the target power-series ring is Noetherian, the closure is automatic, but writing it records that completed base change is the operation being used.

This formula gives a presentation, not automatically a minimal presentation. Nonflat base change may kill equations or alter dependencies among them. It may also change dimension by turning a coefficient direction into zero.

Base change respects quotients:

$$
(R/J)\widehat\otimes_{\mathcal O}\mathcal O'
\simeq R'/\overline{JR'}.
$$

It respects finite modules under the corresponding completed tensor construction, but exactness requires flatness of $\mathcal O'$ over $\mathcal O$ or a separate exactness argument.

### 12.2 Cotangent spaces after coefficient extension

Suppose the residue field of $\mathcal O'$ is $k'$ and the induced residue map is $k\to k'$. Under the preceding finite-type hypotheses there is a natural isomorphism

$$
C_{R'/\mathcal O'}
\simeq C_{R/\mathcal O}\otimes_k k'.
$$

This follows either from the base-change property of Kähler differentials or directly from a power-series presentation: the same variables remain, and the linear relation matrix is extended from $k$ to $k'$.

Consequently

$$
\operatorname{edim}_{\mathcal O'}R'
=\operatorname{edim}_{\mathcal O}R
$$

when $k'/k$ is a field extension and the cotangent space is finite. A minimal set of relative variables stays minimal after such coefficient extension.

Absolute cotangent spaces need not obey this simple formula. They also contain whatever first-order directions come from $\mathcal O'$, modulo the possibly noninjective image of the old coefficient directions. Relative cotangent space is designed precisely to make coefficient extension transparent.

### 12.3 When relation counts survive base change

Let $P=\mathcal O[[\mathbf X]]$, $R=P/I$, and $P'=\mathcal O'[[\mathbf X]]$. Assume that the induced local map $P\to P'$ is flat and that completed base change identifies the kernel of $P'\to R'$ with $IP'$. These are the exact hypotheses needed below; they hold, for example, for finite flat local coefficient extensions and for extensions of coefficient fields. Then finite presentation gives

$$
(I/\mathfrak n_PI)\otimes_k k'
\xrightarrow{\sim}
IP'/\mathfrak n_{P'}IP'.
$$

Thus a minimal set of relations remains minimal after residue-field extension, and the relation count is unchanged.

**Proof strategy.** Flatness preserves the exact kernel sequence $0\to I\to P\to R\to0$, while the kernel hypothesis rules out an extra relation introduced by completion. Quotienting by the maximal ideal then identifies the fiber of $I$ with the fiber of its extension. Nakayama turns a basis of one fiber into a minimal generating set on the other side.

Without flatness, there is no such assertion. The change $\mathcal O\to k$ sends the presentation

$$
\mathcal O\twoheadrightarrow\mathcal O/(\varpi)
$$

with kernel $(\varpi)$ to the identity $k\to k$ with zero kernel. More generally, tensoring a presentation can create a kernel through a torsion term measured by a first derived tensor group, or annihilate coefficient-divisible relations. We use no numerical base-change equality in that setting.

### 12.4 Formal smoothness as a lifting property

A map $A\to B$ of admissible complete local rings is **formally smooth** if, for every surjection $C'\twoheadrightarrow C$ of local Artinian $A$-algebras and every compatible $A$-map $B\to C$, there exists an $A$-map $B\to C'$ lifting it. It is enough to test principal small extensions, because every Artinian surjection factors into them.

The definition solves a precise problem: can every finite-order point be lifted across every nilpotent thickening? Power-series rings solve it because the images of their variables can be lifted arbitrarily. Quotients can fail because their equations may not remain satisfied after lifting.

For example, $A[[X]]$ is formally smooth over $A$. The quotient $k[[X]]/(X^2)$ is not formally smooth over $k$: the map to $k[\epsilon]/(\epsilon^2)$ sending $X$ to $\epsilon$ cannot lift to $k[\epsilon]/(\epsilon^3)$, since every lift has square congruent to $\epsilon^2\neq0$.

Formal smoothness is relative. The map $\mathcal O\to\mathcal O[[X]]$ is smooth in this infinitesimal sense, while the quotient $\mathcal O\to k$ is not: the identity $k\to k$ does not lift as an $\mathcal O$-map to $\mathcal O/(\varpi^2)$.

### 12.5 The power-series characterization

**Theorem.** Let $A\to B$ be a continuous local map of complete Noetherian local rings with the same residue field. Assume $B$ is topologically of finite type over $A$. If $B$ is formally smooth over $A$ and

$$
s=\dim_k\frac{\mathfrak m_B}
{\mathfrak m_B^2+\mathfrak m_AB},
$$

then, after choosing lifts of a relative cotangent basis,

$$
B\simeq A[[Y_1,\ldots,Y_s]]
$$

as an $A$-algebra. The isomorphism is noncanonical.

**Proof strategy.** Tangent lifts give a surjection from the power-series ring. Formal smoothness constructs inverse maps at every Artinian order; tangent minimality permits the errors to be corrected one layer at a time. Completeness passes the compatible inverses to the limit.

**Proof.** Let $\phi:P=A[[\mathbf Y]]\twoheadrightarrow B$ be induced by the chosen lifts. Its relative cotangent map is an isomorphism. We construct compatible $A$-maps

$$
s_n:B\longrightarrow P/\mathfrak m_P^n
$$

such that the composite of $s_n$ with the map $P/\mathfrak m_P^n\to B/\mathfrak m_B^n$ induced by $\phi$ is the residue of the identity of $B$. Begin with the common residue map. Given $s_n$, formal smoothness lifts it across

$$
P/\mathfrak m_P^{n+1}\twoheadrightarrow P/\mathfrak m_P^n.
$$

The new composite with $\phi$ can differ from the identity modulo order $n+1$ only by an $A$-derivation into the square-zero layer $\mathfrak m_B^n/\mathfrak m_B^{n+1}$. Such a derivation factors through $C_{B/A}$. The map $C_{P/A}\to C_{B/A}$ is an isomorphism, and the surjection $P\to B$ is surjective on every graded layer. We may therefore lift the values of the derivation to $\mathfrak m_P^n/\mathfrak m_P^{n+1}$ and change the lifted map by the resulting derivation $B\to\mathfrak m_P^n/\mathfrak m_P^{n+1}$. This cancels the error without changing the preceding stage. Thus the $s_n$ may be chosen compatibly with the asserted composite property.

Passing to inverse limits gives an $A$-map $s:B\to P$ with $\phi\circ s=\operatorname{id}_B$. The endomorphism $\alpha=s\circ\phi$ of $P$ induces the identity on relative cotangent spaces, so the relative cotangent surjectivity criterion makes $\alpha$ surjective. A surjective endomorphism of the Noetherian ring $P$ is an automorphism. Since $\alpha^2=\alpha$, an idempotent automorphism is the identity. Hence $s\circ\phi=\operatorname{id}_P$, and $\phi$ is an isomorphism. $\square$

The zero-dimensional relative case says that a formally smooth map with no relative tangent directions is an isomorphism. Thus formal etaleness at one complete local point has no hidden finite extension when the residue field is fixed.

### 12.6 The functorial interpretation

If complete rings $R$ and $S$ represent functors and a natural transformation corresponds contravariantly to a ring map $R\to S$, then formal smoothness of the transformation is exactly the lifting property of $S$ over $R$. Under the theorem's hypotheses,

$$
S\simeq R[[Y_1,\ldots,Y_s]].
$$

Thus forgetting a freely liftable choice adds formal variables to the ring representing the more structured problem. The direction is easy to reverse accidentally: a transformation from the functor represented by $S$ to the one represented by $R$ comes from $R\to S$.

This conclusion uses representability, topological finite type, and formal smoothness. Merely having a tangent-space difference of dimension $s$ does not imply a power-series extension. Higher lifting obstructions may impose relations, and automorphisms may prevent the relevant set-valued functor from being represented at all.

## 13. From tangent and obstruction spaces to equations

### 13.1 Tangent dimension counts variables

We now connect the algebra to a represented deformation problem. Let $F$ be a deformation functor over $\mathcal O$, and suppose $F$ is represented by an admissible complete local ring $R$. Then

$$
t_F\simeq T_{R/\mathcal O}
=\operatorname{Hom}_k(C_{R/\mathcal O},k).
$$

If

$$
r=\dim_kt_F,
$$

choosing a basis of $t_F$ and its dual basis of $C_{R/\mathcal O}$ gives a minimal surjection

$$
P=\mathcal O[[X_1,\ldots,X_r]]\twoheadrightarrow R.
$$

This is an exact conclusion: tangent dimension is the minimal number of relative formal variables. It depends on representability or at least on a chosen hull whose tangent map is an isomorphism. For a functor with only a tangent set and no hull, the same number does not by itself produce a ring.

In representation deformation problems, $t_F$ may be a space of continuous cocycles, a first cohomology group, a trace-kernel, or a Selmer group. The algebra does not depend on which cohomological description produced it. Once the functor is represented, its dimension is converted into $r$ minimal variables by duality and tangent lifts.

The word *minimal* must be retained. A direct construction from topological generators of a Galois group or from matrix entries often yields many more variables. Linear relations among those coordinates can be eliminated until the number is exactly $\dim_kt_F$.

### 13.2 When obstruction dimension bounds relations

Let

$$
R=P/I,
\qquad
P=\mathcal O[[X_1,\ldots,X_r]],
$$

be a minimal presentation. Suppose $F$ has a finite-dimensional obstruction space $V$ with a complete obstruction theory for small extensions. Completeness means that an obstruction vanishes exactly when the desired lift exists, not merely that liftability forces vanishing.

For the numerical bound, the phrase **complete obstruction theory in $V$** includes the following standard linearity data:

1. obstruction classes are functorial under morphisms and pushouts of small extensions;
2. for a small extension with kernel $J$, the obstruction to lifting $\xi$ is an element of $V\otimes_kJ$;
3. this assignment is additive in $J$ and vanishes if and only if $\xi$ lifts.

It is equivalent to give the theory on principal small extensions together with pushout functoriality and additivity. Under this package, universal obstructions define an injection

$$
\operatorname{Rel}_P(R)^\vee
\hookrightarrow V.
$$

Therefore

$$
s:=\mu_P(I)
=\dim_k\operatorname{Rel}_P(R)
\leq\dim_kV.
$$

**Proof strategy.** Work on one sufficiently deep Artinian truncation of $P$. Its universal small extension has kernel $I/\mathfrak nI$. The universal obstruction is therefore a tensor in $V\otimes_k(I/\mathfrak nI)$, hence a linear map from the dual relation space to $V$. Pushing out along any nonzero functional gives the principal extension of Section 5.9, which cannot admit a lift. Completeness forces the corresponding obstruction to be nonzero, proving injectivity.

**Proof.** Write $\mathfrak n=\mathfrak m_P$. By Artin--Rees, choose $N$ so large that

$$
I\cap\mathfrak n^N\subseteq\mathfrak nI.
$$

Set

$$
E=P/(\mathfrak nI+\mathfrak n^N),
\qquad
A_N=P/(I+\mathfrak n^N).
$$

Then $E\twoheadrightarrow A_N$ is a small extension with kernel

$$
J=I/(\mathfrak nI+I\cap\mathfrak n^N)
\simeq I/\mathfrak nI.
$$

Let $\xi_N\in F(A_N)$ be induced by the representing map $R\to A_N$. Its obstruction

$$
\omega_N\in V\otimes_kJ
$$

corresponds to a linear map $J^\vee\to V$. Given $0\neq\lambda\in J^\vee$, push the extension out along $\lambda:J\to k$. Functoriality identifies the resulting obstruction with $(1\otimes\lambda)(\omega_N)$. The pushed-out ring is exactly the principal extension constructed in Section 5.9, and that section proves directly from relative minimality that $\xi_N$ cannot lift to it. Completeness of the obstruction theory therefore gives

$$
(1\otimes\lambda)(\omega_N)\neq0.
$$

Every nonzero functional has nonzero image, so $J^\vee\to V$ is injective. Since $J\simeq\operatorname{Rel}_P(R)$, this is the required injection. $\square$

The proof explains why the hypotheses are substantive. An arbitrarily enlarged obstruction space still gives a true but weak bound. An incomplete obstruction assignment might miss genuine failures, while an obstruction assignment lacking pushout linearity does not produce a linear map from the dual relation space.

### 13.3 The basic dimension bound

Combine the exact variable count, the relation bound, and the height theorem. Put

$$
r=\dim_kt_F,
\qquad
o=\dim_kV.
$$

Under the obstruction hypotheses of Section 13.2, $R$ has a presentation with $r$ variables and at most $o$ relations. Hence

$$
\dim R\geq\dim\mathcal O+r-o.
$$

For a coefficient field,

$$
\dim R\geq r-o,
$$

while for a coefficient discrete valuation ring,

$$
\dim R\geq1+r-o.
$$

This is the elementary numerical inequality most often exported from deformation cohomology to commutative algebra.

The derivation contains two inequalities:

$$
\mu_P(I)\leq o,
\qquad
\operatorname{ht}(I)\leq\mu_P(I).
$$

Either can be strict. The obstruction space may contain classes never realized as universal equations, and minimal equations may have dependent height. Therefore one must not replace the final lower bound by an equality unless both missing equalities have been proved separately.

There is also the evident upper bound

$$
\dim R\leq\dim\mathcal O+r.
$$

It merely says that quotienting the tangent-coordinate source cannot increase dimension. Together,

$$
\dim\mathcal O+r-o
\leq\dim R
\leq\dim\mathcal O+r.
$$

### 13.4 What cohomology does not determine

A tangent space and an obstruction space do not determine the isomorphism class of $R$. Rings

$$
k[[X]]/(X^2),
\qquad
k[[X]]/(X^3),
\qquad
k[[X]]/(X^4)
$$

all have one tangent variable and one minimal relation, but different nilpotent thickness. Even the pair $(r,s)$ does not determine length, associated graded ring, reducedness, number of components, or the order of the equations.

A nonzero obstruction group does not prove that $R$ has a relation. It supplies a receptacle for obstruction classes; the actual universal obstruction map may be zero. Conversely, a chosen obstruction space can be larger than necessary. Thus

$$
\dim_kV=o
$$

means “at most $o$ universal relation directions” only under the complete linear obstruction hypotheses above, not “exactly $o$ equations.”

Nor does the numerical equality $s=o$ identify the equations canonically. The injection of dual relation space into $V$ may become an isomorphism, but changing tangent coordinates or obstruction coordinates changes the displayed functions. Cohomology controls their number and sometimes their leading operations, not their unique formulas.

Finally, cohomology cannot replace representability. Automorphisms can obstruct unique gluing even when tangent and obstruction spaces are finite. In that case one may have a hull or a framed universal ring, and its algebra can still be studied, but it is incorrect to call an unrepresented coarse functor's tangent dimension the number of variables of a nonexistent universal ring.

### 13.5 Unobstructed problems

Suppose the obstruction theory is complete and $V=0$. Then every small-extension lifting problem is solvable. If $F$ is represented, the ring $R$ is formally smooth over $\mathcal O$. The power-series characterization gives

$$
R\simeq\mathcal O[[X_1,\ldots,X_r]].
$$

Thus an unobstructed represented problem has no relations in a minimal presentation.

The order of logic matters:

$$
\text{complete obstruction theory with }V=0
\Longrightarrow\text{formal smoothness},
$$

and

$$
\text{formal smoothness + represented finite tangent problem}
\Longrightarrow\text{power-series ring}.
$$

Vanishing of a group merely containing all obstruction classes is not enough if the obstruction theory has not been shown complete. Vanishing also does not cure automorphism failures in a coarse moduli functor. Those categorical issues were settled before the ring-theoretic conclusion is invoked.

### 13.6 Framed and fixed-determinant bookkeeping

For a framed representation problem, tangent vectors are usually cocycles, while for an unframed problem under the scalar-centralizer hypothesis they are cohomology classes. If both rings exist and forgetting the frame is formally smooth of relative tangent dimension $q$, then

$$
R^{\square}\simeq R[[Y_1,\ldots,Y_q]]
$$

noncanonically. Both dimension and relative embedding dimension increase by $q$; the relation count is unchanged after transporting a minimal presentation through this power-series extension.

Fixing a determinant usually replaces the ambient tangent space by the kernel of the differential of determinant. When the coefficient characteristic divides the representation dimension, that kernel must be calculated exactly; it need not be obtained by a naive direct-sum removal of scalar matrices. Once the correct tangent space $t^{\delta}$ is known, its dimension counts the variables of the fixed-determinant ring.

The corresponding obstruction space must also be the one controlling determinant-preserving lifts. If its dimension is $o^{\delta}$ and the complete functorial linear obstruction hypotheses hold, then

$$
\dim R^{\delta}
\geq\dim\mathcal O+\dim_kt^{\delta}-o^{\delta}.
$$

This formula is relative to the fixed coefficient base and determinant. Coefficient deformations and determinant deformations that have been frozen must not be restored as variables in the count.

### 13.7 Relative tangent and obstruction theory

Global deformation problems are assembled from prescribed local ones. Algebraically, this means that the natural base is not merely $\mathcal O$ but a complete local ring $A$ already representing all chosen local conditions. Let $A\to R$ be the induced local map. The relative tangent space is

$$
t_{R/A}=
\operatorname{Hom}_k
\left(
\frac{\mathfrak m_R}
{\mathfrak m_R^2+\mathfrak m_AR},k
\right).
$$

If its dimension is $g$, relative cotangent lifts give a minimal surjection

$$
A[[X_1,\ldots,X_g]]\twoheadrightarrow R.
$$

Suppose a finite-dimensional space $V_{R/A}$ carries a complete, functorial, additive obstruction theory for lifting the global object while the local object over $A$ is held fixed. The universal relation argument applies word for word relative to $A$, and gives

$$
\operatorname{Rel}_{A[[\mathbf X]]/A}(R)^\vee
\hookrightarrow V_{R/A}.
$$

Thus, with $r=\dim_kV_{R/A}$,

$$
R\simeq
A[[X_1,\ldots,X_g]]/(f_1,\ldots,f_s),
\qquad s\leq r.
$$

No regularity of $A$ is required for this presentation. Krull's height theorem still yields

$$
\dim R\geq\dim A+g-s
\geq\dim A+g-r,
$$

because $\dim A[[\mathbf X]]=\dim A+g$ in the complete Noetherian setting. This is the relative generator--relation inequality used for a global ring over its local deformation base.

### 13.8 Local products and the global presentation

Suppose a finite collection of local conditions is represented by complete local $\mathcal O$-algebras $R_v$, all with residue field $k$. Their simultaneous independent choice is represented by

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v,\mathcal O}R_v.
$$

The relative cotangent space is the direct sum of the local relative cotangent spaces. If every $R_v$ is $\mathcal O$-flat, then so is $R_{\mathrm{loc}}$, and repeated use of the DVR dimension formula gives

$$
\dim R_{\mathrm{loc}}
=1+\sum_v(\dim R_v-1).
$$

Now let $R_{\mathrm{glob}}$ represent global objects equipped with their prescribed localizations. The localization transformation induces

$$
R_{\mathrm{loc}}\longrightarrow R_{\mathrm{glob}}.
$$

If the relative tangent space has dimension $g$ and a complete functorial linear relative obstruction space has dimension $r$, then

$$
R_{\mathrm{glob}}
\simeq
R_{\mathrm{loc}}[[X_1,\ldots,X_g]]
/(f_1,\ldots,f_s),
\qquad s\leq r,
$$

and therefore

$$
\dim R_{\mathrm{glob}}
\geq\dim R_{\mathrm{loc}}+g-r.
$$

This formula is exact about what is local and what is global. Equations already cutting out the $R_v$ sit inside $R_{\mathrm{loc}}$. The $g$ new variables measure global tangent classes invisible to the fixed local base, while the at most $r$ new equations measure global compatibility obstructions.

In arithmetic applications the relative tangent space is often a Selmer group and the chosen obstruction space may inject into the dual of a dual Selmer group, possibly with explicit local correction terms. The local algebra uses only the resulting finite dimensions and the complete functorial obstruction assignment; it does not identify a cohomology group with equations without that assignment.

### 13.9 Balanced presentations

A relative presentation is **balanced** when it has no more relations than variables:

$$
s\leq g.
$$

Equivalently, the elementary dimension bound gives

$$
\dim R\geq\dim A.
$$

Balanced does not mean complete intersection, flat, or finite. The ring

$$
A[[X,Y]]/(X^2,XY)
$$

has two variables and two relations, hence is balanced, but the equations have height one and are not a regular sequence. Balance is a numerical lower bound; equality of relation number and height is the extra condition that produces a complete intersection.

The power of balance appears when an independent argument gives an upper dimension bound or finiteness over the base. Then the height of the kernel is forced to be as large as the number of available variables. Chapter 15 makes this forcing argument precise and records the hypotheses under which it also yields flatness.

## 14. A gallery of deformation-shaped local rings

### 14.1 A smooth universal ring

Let

$$
R=\mathcal O[[X_1,\ldots,X_r]].
$$

It represents $r$ independent parameters in the maximal ideal of every Artinian coefficient algebra. Its relative cotangent and tangent dimensions are $r$, it has no relation module, and it is formally smooth over $\mathcal O$.

If $\mathcal O=k$, then $\dim R=r$ and $\operatorname{edim}R=r$. If $\mathcal O$ is a discrete valuation ring, then $\dim R=r+1$, absolute embedding dimension is $r+1$, and relative embedding dimension is $r$. In both cases $R$ is regular.

This is the exact algebraic shape produced by a represented deformation problem with complete zero obstruction space. It is not merely suggested by tangent dimension; formal smoothness eliminates the possibility of hidden higher equations.

### 14.2 A fat infinitesimal direction

Let

$$
R_n=k[[X]]/(X^n),\qquad n\geq2.
$$

Then

$$
C_{R_n}=k\bar X,
\qquad
\operatorname{Rel}_{k[[X]]}(R_n)=k\overline{X^n},
\qquad
\dim R_n=0.
$$

There is one tangent direction and one relation for every $n$, but the length is $n$. A map sending $X$ to a first-order nilpotent can lift only as long as its $n$th power remains zero. The tangent direction therefore exists even though the formal space has no positive-dimensional prime chain.

This example is the standard counterweight to any claim that nonzero tangent dimension forces positive Krull dimension. Nilpotent directions thicken a point without creating a new generic point.

### 14.3 A nodal relation

Let

$$
R=k[[X,Y]]/(XY).
$$

The presentation is minimal with two variables and one relation. The dimension bound gives $\dim R\geq1$, and the nonzero principal equation in the two-dimensional domain gives equality. The ring is reduced with two minimal primes $(X)$ and $(Y)$, and it is not regular because its embedding dimension is two.

The tangent space sees all pairs $(a,b)$ over the dual numbers, since $(a\epsilon)(b\epsilon)=0$. At second order, the product can become visible. Thus the equation imposes no linear restriction but couples the two directions nonlinearly.

The quotient maps to $k[[X]]$ and $k[[Y]]$ describe the two branches. Their direct product as functors should not be confused with their union inside the node: products of functors correspond to completed tensor products, while this union is encoded by the single equation $XY=0$.

### 14.4 A mixed-characteristic smoothing

Consider

$$
R=\mathcal O[[X,Y]]/(XY-\varpi).
$$

The relative presentation has two variables and one minimal relation. Since the source has dimension three and the equation is nonzero, $\dim R=2$. The maximal ideal is $(X,Y)$, so the absolute embedding dimension is two and $R$ is regular.

The special fiber is

$$
R/\varpi R\simeq k[[X,Y]]/(XY),
$$

which is singular and reducible. The total ring is a regular two-dimensional local ring whose special fiber is a nodal curve. The coefficient relation turns the uniformizer into the product of two parameters and removes its independent absolute cotangent class.

This example prevents two mistakes. Regularity need not pass to a singular special fiber, and relative relation count need not measure singularity of the total ring by itself. The position of the coefficient uniformizer in the equation matters.

### 14.5 A finite normalization-shaped map

Return to

$$
A=k[[U,V]]/(V^2-U^3)
\longrightarrow B=k[[T]],
\qquad U\mapsto T^2,\quad V\mapsto T^3.
$$

The map is finite, injective, local, and residue-preserving. Hence it is faithful and preserves dimension: both rings are one-dimensional. The source has embedding dimension two and is singular; the target has embedding dimension one and is regular.

Because the cotangent map is zero, it is as far from a surjection as first-order coordinates can detect. This shows that a finite map from a deformation ring to a better-behaved ring can preserve dimension without identifying their tangent theories or their rings.

If one additionally knew that a finite residue-preserving map of complete local rings was surjective on cotangent spaces and faithful, then it would be an isomorphism. The cusp example demonstrates why neither property follows from finiteness and dimension equality.

### 14.6 A completed product of constrained problems

Let

$$
R_1=k[[X,Y]]/(XY),
\qquad
R_2=k[[Z]]/(Z^3).
$$

Then

$$
R_1\widehat\otimes_kR_2
\simeq k[[X,Y,Z]]/(XY,Z^3).
$$

The relative tangent dimension is $2+1=3$, and there are two minimal relations. The dimension is $1+0=1$. One factor contributes a one-dimensional reducible geometry; the other contributes only nilpotent thickness. The product retains both phenomena without confusing them.

Over a discrete valuation ring, take instead two flat rings

$$
R_1=\mathcal O[[X,Y]]/(XY-\varpi),
\qquad
R_2=\mathcal O[[Z]].
$$

Their completed product is

$$
\mathcal O[[X,Y,Z]]/(XY-\varpi),
$$

with relative tangent dimension three and dimension $2+2-1=3$. The shared uniformizer appears only once. This is the basic local-algebra shape of assembling independent conditions over one coefficient system.

## 15. The patching dictionary

### 15.1 Reading cohomology as a presentation

Suppose a deformation problem over $\mathcal O$ has been proved representable by $R$, with tangent space $t$ and a complete functorial linear obstruction theory in $V$. Write

$$
r=\dim_kt,
\qquad o=\dim_kV.
$$

The precise translation is:

$$
\begin{array}{c|c}
\text{deformation-theoretic datum}&\text{ring-theoretic conclusion}\\ \hline
t& C_{R/\mathcal O}^\vee\\
\dim_kt=r&\text{exactly }r\text{ minimal relative variables}\\
V\text{ functorial, linear, and complete}&
\mu(I)\leq o\text{ in a minimal presentation}\\
V=0\text{ with complete theory}&R\simeq\mathcal O[[X_1,\ldots,X_r]]\\
\text{formally smooth relative map of tangent size }q&
\text{adjoin }q\text{ power-series variables}.
\end{array}
$$

The presentation conclusion is

$$
R\simeq\mathcal O[[X_1,\ldots,X_r]]/(f_1,\ldots,f_s),
\qquad s\leq o.
$$

It yields

$$
\dim R\geq\dim\mathcal O+r-o.
$$

Nothing in this dictionary says $s=o$ or $\dim R=\dim\mathcal O+r-o$. Those are additional mathematical conclusions requiring surjectivity of the universal obstruction map and equality between height and relation number.

### 15.2 Reading a ring map

Let $A\to B$ be a continuous local homomorphism of complete Noetherian local rings with the same residue field.

- If $C_A\to C_B$ is surjective, then $A\to B$ is surjective.
- The same holds for relative cotangent spaces over a common coefficient base.
- If $B$ is finite over $A$, then

  $$
  \dim B=\dim(A/\ker(A\to B)).
  $$

- If the finite map is faithful, it is injective and $\dim B=\dim A$.
- If it is finite, faithful, and cotangent-surjective, it is an isomorphism.

These implications have deliberately different hypotheses. Cotangent surjectivity uses completeness to build all target elements. Finiteness uses integrality to compare primes. Faithfulness removes the kernel. No one of the three substitutes for the other two.

A finite map with equal dimensions need not be faithful if its kernel kills only lower-dimensional components, and even a faithful finite map need not be surjective. A surjection with equal dimensions need not be an isomorphism when its kernel has height zero. Thus every proposed ring comparison should identify which mechanism supplies injectivity and which supplies surjectivity.

### 15.3 Reading completed products

For residue-compatible topologically finite-type $\mathcal O$-algebras,

$$
R\widehat\otimes_{\mathcal O}S
$$

represents simultaneous compatible choices. Relative tangent spaces add:

$$
C_{(R\widehat\otimes S)/\mathcal O}
\simeq C_{R/\mathcal O}\oplus C_{S/\mathcal O}.
$$

Over a field, dimensions add. Over a coefficient discrete valuation ring, dimensions add and then subtract one when both factors are flat:

$$
\dim(R\widehat\otimes_kS)=\dim R+\dim S,
$$

$$
\dim(R\widehat\otimes_{\mathcal O}S)
=\dim R+\dim S-1
\quad(\mathcal O\text{-flat factors}).
$$

Without flatness, only presentation-based inequalities should be asserted. Without residue compatibility, the product may not be local. Without topological finite type, it may not be Noetherian. The completion symbol guarantees none of these properties by itself.

Base-changing a minimal presentation preserves relative tangent variables under residue-field extension. It preserves minimal relations under flat base change with exact kernel extension. Nonflat specialization can make relations disappear, create new kernel, or alter dimension.

### 15.4 A disciplined numerical workflow

When a deformation ring enters a patching argument, the following order keeps the logic visible.

1. Fix the coefficient ring, residue field, determinant data, and whether the problem is framed.
2. Prove representability or specify that only a hull is available.
3. Identify the exact tangent space and compute its dimension $r$.
4. Choose dual cotangent lifts to obtain a minimal power-series source in $r$ variables.
5. State the exact obstruction theory. Verify completeness, pushout functoriality, and additivity in the small-extension kernel before bounding relations.
6. Obtain $s\leq o$ and then the lower bound $\dim R\geq\dim\mathcal O+r-o$.
7. Keep equality conditional until height $s$, flatness, or another dimension theorem proves it.
8. For every ring map, decide separately whether it is surjective, finite, injective, or faithful.
9. For every completed tensor product, verify common residue field, Noetherian topological finite type, and the flatness needed for a dimension equality.
10. For an acting finite module, distinguish full-dimensional support from faithfulness and distinguish residue generators from freeness.

This workflow is not bureaucratic. Each checkpoint blocks a characteristic error: counting $\varpi$ as a deformation variable, treating all obstruction classes as equations, subtracting relation number as though it were height, or concluding an isomorphism from finiteness and equal dimension.

### 15.5 Balance plus finiteness over a regular base

The most useful numerical forcing theorem begins with a balanced presentation and ends with a complete intersection.

**Theorem (balanced finite criterion).** Let $A$ be a regular complete local ring of dimension $d$, let

$$
P=A[[X_1,\ldots,X_g]],
$$

and suppose

$$
R=P/(f_1,\ldots,f_s)
$$

is a nonzero local ring finite over $A$. Assume $A\to R$ is injective and $s\leq g$. Then:

1. $s=g$ and the kernel has height $g$;
2. $f_1,\ldots,f_g$ is a regular sequence;
3. $R$ is a complete intersection and Cohen--Macaulay of dimension $d$;
4. $R$ is finite free over $A$.

**Proof strategy.** Finiteness and injectivity impose the upper and lower dimension $d$. Balance imposes the opposite lower bound from the presentation. Equality forces height to equal relation number. Cohen--Macaulayness then turns the parameters of $A$ into a regular sequence on $R$, and a finite-module lifting argument gives freeness.

**Proof.** Since $R$ is finite and faithful over $A$,

$$
\dim R=\dim A=d.
$$

The source has dimension $d+g$, while the height theorem gives

$$
d=\dim R\geq d+g-s.
$$

Thus $s\geq g$. Since $s\leq g$, equality holds. The kernel has height

$$
\dim P-\dim R=(d+g)-d=g.
$$

It is minimally generated by $g$ elements after redundancies are removed, so the height criterion of Section 8.9 makes those generators a regular sequence. Hence $R$ is Cohen--Macaulay of dimension $d$.

Let $a_1,\ldots,a_d$ be a regular system of parameters of $A$. Because $R$ is finite local over $A$, the ideal $(a_1,\ldots,a_d)R$ is $\mathfrak m_R$-primary, so the $a_i$ form a system of parameters of $R$. Cohen--Macaulayness makes them an $R$-regular sequence. We prove freeness over $A$ by induction on $d$. For $d=0$, $A$ is a field. For $d>0$, $R/a_1R$ is finite free over $A/a_1A$ by induction. Lift a basis to obtain a surjection $A^n\twoheadrightarrow R$. If $K$ is its kernel, reduction modulo $a_1$ remains left exact because $a_1$ is a non-zero-divisor on $R$. The reduced map is an isomorphism, so $K/a_1K=0$. Nakayama gives $K=0$. Thus $R\simeq A^n$. $\square$

For $A=\mathcal O$, the injectivity hypothesis can be replaced by the assertion that $\varpi$ is not nilpotent. Indeed, every nonzero ideal of the discrete valuation ring is $(\varpi^n)$ for some $n$; a nonzero kernel of $\mathcal O\to R$ would therefore make $\varpi$ nilpotent in $R$. Thus nonnilpotence gives injectivity, and the theorem applies. Geometrically, the resulting one-dimensional Cohen--Macaulay ring is unmixed, so it has no vertical zero-dimensional component; equivalently, $\varpi$ lies in no associated prime and $R$ is $\mathcal O$-flat.

Each hypothesis has a job. Without balance there may be too many equations. Without finiteness there is no upper dimension bound. Without injectivity, a quotient such as $A/(a)$ can satisfy a presentation while living over a smaller base. Without regularity of $A$, its parameters need not form the regular sequence required for freeness.

### 15.6 The local-to-global numerical package

Let

$$
R_{\mathrm{loc}}
=\widehat\bigotimes_{v,\mathcal O}R_v
$$

be the completed product of prescribed local rings, and assume every factor is $\mathcal O$-flat. Suppose a global deformation ring has a relative presentation

$$
R_{\mathrm{glob}}
\simeq
R_{\mathrm{loc}}[[X_1,\ldots,X_g]]
/(f_1,\ldots,f_s),
\qquad s\leq r.
$$

Then the complete numerical statement is

$$
\dim R_{\mathrm{glob}}
\geq
1+\sum_v(\dim R_v-1)+g-r.
$$

When a global duality calculation gives $g-r=q$, adjoining $q$ auxiliary formally smooth directions balances the presentation against an auxiliary regular ring of dimension $1+q$. The equality is numerical bookkeeping, not yet a ring isomorphism. Its purpose is to arrange that a finite or faithful module argument can force all inequalities to become equalities.

A common schematic arrangement is

$$
S_\infty=\mathcal O[[Z_1,\ldots,Z_q]],
$$

with augmentation ideal

$$
\mathfrak a=(Z_1,\ldots,Z_q),
$$

and a patched ring $R_\infty$ carrying an $S_\infty$-algebra structure. One aims for a presentation of $R_\infty$ whose variable-minus-relation count matches

$$
\dim S_\infty=1+q.
$$

The local rings contribute their already known dimensions; global tangent directions add variables; dual obstruction directions bound equations; and the auxiliary variables supply exactly the surplus required to reach the regular base dimension.

### 15.7 A faithful patched module controls its ring

The module is the bridge from the regular auxiliary ring to the patched deformation ring.

**Theorem (faithful free control).** Let $S$ be a Noetherian local ring, let $R$ be a local $S$-algebra, and let $M$ be a nonzero module with commuting actions such that:

- $M$ is finite free over $S$;
- $M$ is finite over $R$;
- the action of $R$ on $M$ is faithful.

Then $S\to R$ is injective, $R$ is finite as an $S$-module, and

$$
\dim R=\dim S.
$$

**Proof.** The $R$-action gives an injective map

$$
R\hookrightarrow\operatorname{End}_S(M)
$$

by faithfulness. If $M$ has $S$-rank $n$, the endomorphism module is isomorphic to a matrix module of rank $n^2$ over $S$. Since $S$ is Noetherian, its submodule $R$ is finite over $S$. If $s\in S$ maps to zero in $R$, it acts as zero on the nonzero free $S$-module $M$, so $s=0$. Hence the map is finite and injective, and the finite-map dimension theorem gives $\dim R=\dim S$. $\square$

If faithfulness is not initially known, the same argument applies to

$$
R/\operatorname{Ann}_R(M).
$$

It proves that the support of $M$ has the auxiliary dimension, but it does not remove the annihilator. This is exactly why full-dimensional support is weaker than faithfulness.

Combine this theorem with the balanced finite criterion. If $S$ is regular and $R$ has a balanced power-series presentation over $S$, a faithful $S$-free module makes $R$ finite and faithful over $S$. The criterion then proves that $R$ is a complete intersection and finite free over $S$. Thus the chain is

$$
\text{free module over }S
\Longrightarrow
\text{finite faithful ring over }S
\Longrightarrow
\text{height equality}
\Longrightarrow
\text{regular-sequence equations}.
$$

No arrow may be omitted: freeness over $S$ alone controls only the quotient of $R$ acting faithfully, and balance alone supplies only a lower dimension bound.

### 15.8 Augmentation and descent to finite level

Let $S_\infty=\mathcal O[[Z_1,\ldots,Z_q]]$ and $\mathfrak a=(Z_1,\ldots,Z_q)$. If $M_\infty$ is finite free over $S_\infty$, then

$$
M_0=M_\infty/\mathfrak aM_\infty
$$

is finite free over $\mathcal O$ of the same rank. If $R_\infty$ acts $S_\infty$-linearly, the action descends through

$$
R_0=R_\infty/\mathfrak aR_\infty.
$$

These quotient identities are exact because the $Z_i$ form an $S_\infty$-regular sequence and $M_\infty$ is free. In particular, successively tensoring

$$
0\longrightarrow S_\infty\xrightarrow{Z_i}S_\infty
$$

with the relevant successive quotients of $M_\infty$ preserves injectivity.

Faithfulness does not automatically descend: an element of $R_0$ may annihilate $M_0$ even when no lift annihilates $M_\infty$. A descent argument must therefore prove that

$$
\operatorname{Ann}_{R_\infty}(M_\infty)
\quad\text{and}\quad
\operatorname{Ann}_{R_0}(M_0)
$$

have the required relation, or must establish faithfulness anew at finite level. Similarly, an isomorphism between a finite-level deformation ring and a comparison ring requires both a surjection and a mechanism killing its kernel; equal dimensions alone do not suffice.

When there is a surjection $R_0\twoheadrightarrow T_0$ and $T_0$ acts faithfully on $M_0$, a standard final route is:

1. use the patched module to prove $R_0$ has the predicted complete-intersection and flatness properties;
2. compare cotangent or congruence data to show the surjection has no residual relation direction;
3. use completeness, faithfulness, or a length equality to kill the full kernel.

The first step is the local algebra developed here. The second and third require the particular comparison invariants of the problem, but the logical roles of their hypotheses are now explicit.

### 15.9 Conclusion

Complete local algebra turns infinitesimal deformation data into geometry around one closed point. The relative cotangent space is the hinge: its dual is the deformation tangent space, while its basis lifts provide the smallest possible system of formal coordinates. Cohen structure supplies the coefficient field or coefficient ring over which those coordinates live. Topological Nakayama and completeness promote first-order spanning to a power-series surjection, and the relation module counts the genuinely necessary equations in its kernel.

Krull dimension measures something different. It follows prime chains, so equations lower it according to height rather than raw number. Regular sequences are precisely the equations that cut dimension without introducing torsion at each stage. A quotient of a regular local ring is a complete intersection when minimal relation number equals codimension; it is then Cohen--Macaulay, so parameter sequences have the injectivity needed for flatness and freeness arguments.

Over a coefficient discrete valuation ring, flatness is exactly absence of coefficient torsion. This criterion explains when special fibers drop dimension by one, when completed tensor-product dimensions subtract a single shared coefficient direction, and when finite coefficient algebras are free. Fiber products serve a different purpose: they glue compatible quotients and create unions of branches, with dimension given by a maximum rather than a sum.

The global presentation over $R_{\mathrm{loc}}$ now has a precise reading. Relative tangent classes give variables; a complete functorial linear obstruction theory bounds global equations; duality supplies the balance; and a patched module free over an auxiliary regular ring can force the patched ring to be finite, faithful, and equal in dimension to that base. Balance plus finiteness turns the equations into a regular sequence. Augmentation then returns to the original coefficient level, with faithfulness and kernel control checked rather than assumed.

The resulting dictionary is exact: tangent dimension gives variables, complete functorial obstructions bound relations, height detects complete intersections, torsion detects coefficient flatness, completed tensor products combine independent local conditions, fiber products glue common reductions, and faithful free modules convert numerical balance into structural theorems. These are the complete-local algebraic moves by which local and global deformation calculations become the ring statements used in patching.
