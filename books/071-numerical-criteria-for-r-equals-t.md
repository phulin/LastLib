# Numerical Criteria for $R=T$

## Contents

1. [The numerical bridge](#1-the-numerical-bridge)
   - [Why a point can determine a ring map](#11-why-a-point-can-determine-a-ring-map)
   - [The two measurements](#12-the-two-measurements)
   - [Standing conventions](#13-standing-conventions)
   - [The shape of the argument](#14-the-shape-of-the-argument)
2. [Augmented local algebras over a discrete valuation ring](#2-augmented-local-algebras-over-a-discrete-valuation-ring)
   - [The distinguished integral point](#21-the-distinguished-integral-point)
   - [Finite, torsion-free, and flat](#22-finite-torsion-free-and-flat)
   - [The augmentation kernel](#23-the-augmentation-kernel)
   - [Generic isolation](#24-generic-isolation)
3. [Cotangent and conormal modules at the point](#3-cotangent-and-conormal-modules-at-the-point)
   - [First-order motion along the fiber](#31-first-order-motion-along-the-fiber)
   - [Relative and absolute differentials](#32-relative-and-absolute-differentials)
   - [Conormal sequences for a quotient](#33-conormal-sequences-for-a-quotient)
   - [Length and the order of tangency](#34-length-and-the-order-of-tangency)
4. [Congruence ideals and integral separation of branches](#4-congruence-ideals-and-integral-separation-of-branches)
   - [Why annihilate the augmentation kernel](#41-why-annihilate-the-augmentation-kernel)
   - [The congruence ideal and module](#42-the-congruence-ideal-and-module)
   - [Normalization and the missing idempotent](#43-normalization-and-the-missing-idempotent)
   - [Two crossing branches](#44-two-crossing-branches)
   - [Several branches and strictness](#45-several-branches-and-strictness)
5. [Trace, different, discriminant, and duality](#5-trace-different-discriminant-and-duality)
   - [Perfect pairings on the generic fiber](#51-perfect-pairings-on-the-generic-fiber)
   - [The complementary module and the different](#52-the-complementary-module-and-the-different)
   - [Gorenstein duality and the congruence ideal](#53-gorenstein-duality-and-the-congruence-ideal)
   - [Fitting ideals and what they do not say](#54-fitting-ideals-and-what-they-do-not-say)
6. [Complete intersections and Jacobian calculations](#6-complete-intersections-and-jacobian-calculations)
   - [Presentations adapted to the augmentation](#61-presentations-adapted-to-the-augmentation)
   - [The Jacobian presents the cotangent module](#62-the-jacobian-presents-the-cotangent-module)
   - [The determinant computes both lengths](#63-the-determinant-computes-both-lengths)
   - [Hypersurfaces in detail](#64-hypersurfaces-in-detail)
   - [A two-variable calculation](#65-a-two-variable-calculation)
7. [The fundamental inequality and the converse theorem](#7-the-fundamental-inequality-and-the-converse-theorem)
   - [The sign of the inequality](#71-the-sign-of-the-inequality)
   - [A determinant proof of the inequality](#72-a-determinant-proof-of-the-inequality)
   - [Equality detects complete intersections](#73-equality-detects-complete-intersections)
   - [Exact hypotheses and boundary cases](#74-exact-hypotheses-and-boundary-cases)
8. [The numerical isomorphism criterion](#8-the-numerical-isomorphism-criterion)
   - [The comparison problem](#81-the-comparison-problem)
   - [Precise criterion](#82-precise-criterion)
   - [Proof: conormal information](#83-proof-conormal-information)
   - [Proof: comparison of relation lattices](#84-proof-comparison-of-relation-lattices)
   - [What the equality proves](#85-what-the-equality-proves)
9. [Finite modules with ring actions](#9-finite-modules-with-ring-actions)
   - [Why a module can reveal the congruence ideal](#91-why-a-module-can-reveal-the-congruence-ideal)
   - [Self-dual lattices and orthogonal branches](#92-self-dual-lattices-and-orthogonal-branches)
   - [A matrix-action calculation](#93-a-matrix-action-calculation)
   - [Faithfulness and cyclicity hypotheses](#94-faithfulness-and-cyclicity-hypotheses)
10. [Defect modules and quantitative failure](#10-defect-modules-and-quantitative-failure)
    - [From a difference of lengths to an object](#101-from-a-difference-of-lengths-to-an-object)
    - [The intrinsic complete-intersection defect](#102-the-intrinsic-complete-intersection-defect)
    - [The defect of a surjection](#103-the-defect-of-a-surjection)
    - [Exact sequences locating the loss](#104-exact-sequences-locating-the-loss)
11. [Transporting numerical criteria](#11-transporting-numerical-criteria)
    - [Localization and completion](#111-localization-and-completion)
    - [Extension of coefficient discrete valuation rings](#112-extension-of-coefficient-discrete-valuation-rings)
    - [Ramification and numerical lengths](#113-ramification-and-numerical-lengths)
    - [Quotients by regular sequences](#114-quotients-by-regular-sequences)
12. [A gallery of examples](#12-a-gallery-of-examples)
    - [A smooth point and an isolated branch](#121-a-smooth-point-and-an-isolated-branch)
    - [Tangential branches](#122-tangential-branches)
    - [A nonreduced special fiber](#123-a-nonreduced-special-fiber)
    - [A strict non-complete-intersection example](#124-a-strict-non-complete-intersection-example)
    - [A quotient comparison](#125-a-quotient-comparison)
13. [Why every hypothesis matters](#13-why-every-hypothesis-matters)
    - [Without surjectivity](#131-without-surjectivity)
    - [Without finite flatness](#132-without-finite-flatness)
    - [Without compatible augmentations](#133-without-compatible-augmentations)
    - [The source condition that is not needed](#134-the-source-condition-that-is-not-needed)
    - [Without generic isolation](#135-without-generic-isolation)
14. [A reusable numerical package](#14-a-reusable-numerical-package)
    - [The augmented-algebra lemma](#141-the-augmented-algebra-lemma)
    - [The surjective comparison lemma](#142-the-surjective-comparison-lemma)
    - [The self-dual-module lemma](#143-the-self-dual-module-lemma)
    - [The base-change lemma](#144-the-base-change-lemma)
    - [A disciplined verification protocol](#145-a-disciplined-verification-protocol)
    - [Conclusion](#146-conclusion)

## 1. The numerical bridge

### 1.1 Why a point can determine a ring map

Books 69 and 70 developed two complementary languages. Presentations and cotangent spaces describe equations near a closed point; depth, regular sequences, and Fitting ideals decide whether those equations are independent. We now use both languages to answer a sharper question. Suppose there is a surjection

$$
R\longrightarrow T
$$

between complete local algebras. Under what circumstances can information measured at one distinguished integral point force this map to be an isomorphism?

At first the ambition seems unreasonable. A point usually sees little of a scheme. Here, however, the point lies on a one-dimensional finite flat object over a discrete valuation ring. Its generic incarnation is an isolated branch, and all other generic branches can approach it only through powers of the uniformizer. Two finite torsion modules record that approach. One measures infinitesimal tangency at the point. The other measures how far the idempotent separating the distinguished branch fails to be integral. The surprise is that the second can never be larger than the first, and that equality forces the local equations to be a regular sequence.

This is the numerical bridge from infinitesimal information to a global statement about a finite local algebra. It is entirely commutative algebra. No origin for $R$ or $T$ is assumed, and no structure beyond the hypotheses stated below will be smuggled into the argument.

### 1.2 The two measurements

Let $\mathcal O$ be a discrete valuation ring and let $A$ be an augmented local $\mathcal O$-algebra with augmentation $\lambda:A\to\mathcal O$. Write $I_A=\ker\lambda$. The first module is

$$
\Phi_A=I_A/I_A^2.
$$

It is the relative cotangent module at the chosen point. If it has finite $\mathcal O$-length, the chosen point has no relative tangent direction on the generic fiber.

The second invariant begins with the elements of $A$ that kill every function vanishing at the point:

$$
\eta_A=\lambda(\operatorname{Ann}_A(I_A))\subseteq\mathcal O,
\qquad
\Psi_A=\mathcal O/\eta_A.
$$

The ideal $\eta_A$ is the **congruence ideal** and $\Psi_A$ the **congruence module**. The distinction is essential: an ideal and its quotient have opposite size conventions. If $\eta_A=(\varpi^c)$, then $\Psi_A$ has length $c$. A smaller ideal therefore gives a larger congruence module.

Under the finite-flat and generically separated hypotheses made precise later, the fundamental inequality is

$$
\boxed{\operatorname{length}_{\mathcal O}\Phi_A
\ \geq\ 
\operatorname{length}_{\mathcal O}\Psi_A.}
$$

The arrow of comparison must be remembered in this form: cotangent length dominates congruence length. Complete intersections give equality. A failure of complete intersection gives excess cotangent length.

### 1.3 Standing conventions

Throughout, $(\mathcal O,(\varpi),k)$ is a complete discrete valuation ring with fraction field $K$. Length without a subscript means $\mathcal O$-length. Every ring is commutative with identity. A complete local $\mathcal O$-algebra $(A,\mathfrak m_A)$ is Noetherian, complete and separated for its maximal-ideal topology, and carries a continuous local structural map $\mathcal O\to A$ inducing the fixed map on residue fields.

An **augmentation** is a continuous local $\mathcal O$-homomorphism $\lambda_A:A\to\mathcal O$. Since it is an $\mathcal O$-map, it is automatically surjective and splits the structural map as a map of $\mathcal O$-modules and rings. Thus

$$
A=\mathcal O\oplus I_A
$$

as $\mathcal O$-modules, though almost never as a product of rings.

The numerical criterion will use algebras finite flat over $\mathcal O$. Over a discrete valuation ring, a finite module is flat exactly when it is torsion-free, and then it is free. We nevertheless retain all three words where they express different roles: finite gives control of rank and length, torsion-free prevents vertical embedded pieces, and flat gives exact base change.

When we say that $A_K=A\otimes_{\mathcal O}K$ is **generically separated at $\lambda$**, we mean that the induced $K$-point $\lambda_K:A_K\to K$ is an étale factor. Equivalently,

$$
A_K\simeq K\times B
$$

with $\lambda_K$ the first projection, for a finite $K$-algebra $B$. It is enough, and often more convenient, to assume that $A_K$ is reduced; the $K$-valued factor is then automatically a field factor. We will say explicitly which form is used.

### 1.4 The shape of the argument

The proof architecture has four stages. First, the splitting $A_K=K\times B$ produces a generic idempotent $e_\lambda=(1,0)$. Its failure to belong to $A$ is measured by the lattice

$$
A\cap Ke_\lambda\subseteq Ke_\lambda.
$$

Second, a presentation of $A$ turns the first-order relations at the point into a matrix. Its maximal minors generate a Fitting ideal for $\Phi_A$. Third, determinant and depth arguments compare that Fitting ideal with $\eta_A$. Finally, equality prevents hidden relations and forces the presentation ideal to be generated by a regular sequence.

For a surjection $R\twoheadrightarrow T$, there are then three sizes:

$$
\operatorname{length}\Phi_R,
\qquad
\operatorname{length}\Phi_T,
\qquad
\operatorname{length}\Psi_T.
$$

The quotient map gives the first inequality and the intrinsic theorem gives the second:

$$
\operatorname{length}\Phi_R
\geq
\operatorname{length}\Phi_T
\geq
\operatorname{length}\Psi_T.
$$

The numerical criterion is activated by an estimate in the opposite direction,

$$
\operatorname{length}\Phi_R\leq\operatorname{length}\Psi_T.
$$

All three terms must then be equal. The complete-intersection form of Wiles's argument assumes enough equations on the source to kill the kernel. Lenstra's refinement is stronger: equality first proves that the target is a complete intersection, and a comparison of relation lattices then kills the kernel without assuming in advance that the source is finite, flat, or a complete intersection. We will prove that stronger form.

## 2. Augmented local algebras over a discrete valuation ring

### 2.1 The distinguished integral point

An augmentation $\lambda:A\to\mathcal O$ is more than a closed point. It is a section over the whole coefficient ring. Modulo $\varpi$ it gives the closed point $A\to k$, while after inverting $\varpi$ it gives a characteristic-zero point $A_K\to K$. The same map therefore connects the special and generic fibers.

Its kernel $I=I_A$ is the ideal of the section. Because $\lambda$ is split by $\mathcal O\to A$, every $a\in A$ has a unique expression

$$
a=\lambda(a)+i,\qquad i\in I.
$$

Multiplication in $A$ is consequently encoded by the $\mathcal O$-module $I$ and its multiplication $I\otimes I\to I$. The quotient $I/I^2$ deletes this nonlinear part and keeps the first-order data. The annihilator $\operatorname{Ann}_A(I)$ goes in the opposite direction: it asks for the part of $A$ supported entirely on the distinguished branch.

The local condition matters. A finite product $\mathcal O\times C$ already contains the branch idempotent $(1,0)$ and has zero congruence module at the first projection. A local algebra cannot contain a nontrivial idempotent. Thus, if its generic fiber splits, the separating idempotent must acquire denominators. Those denominators are precisely the numerical phenomenon of interest.

### 2.2 Finite, torsion-free, and flat

Let $A$ be finite over $\mathcal O$. The following are equivalent:

1. $A$ is $\mathcal O$-flat;
2. $A$ is $\mathcal O$-torsion-free;
3. $A$ is finite free as an $\mathcal O$-module.

The equivalence is special to a discrete valuation ring. It allows us to regard $A$ as an $\mathcal O$-lattice in $A_K$. In particular, the natural map $A\to A_K$ is injective. Ideals can then be compared with their generic fibers without losing vertical torsion.

Flatness is not automatic from the existence of an augmentation. For example,

$$
A=\mathcal O[[X]]/(\varpi X,X^2),\qquad \lambda(X)=0,
$$

has the direct summand $\mathcal O$, but $X$ is nonzero $\varpi$-torsion. The generic fiber is just $K$, so every generic calculation misses the embedded special-fiber direction. Here $I/I^2\simeq k$, while $\operatorname{Ann}_A(I)$ contains both $\varpi$ and $X$ and hence $\eta_A=(\varpi)$. The familiar equality happens accidentally; it says nothing about complete intersection or flatness. This example will guard against extending the criterion beyond its natural category.

If $A$ is finite flat and augmented, then $I$ is also finite free over $\mathcal O$, since $A=\mathcal O\oplus I$ as $\mathcal O$-modules. The quotient $I/I^2$ need not be free and is usually torsion. Its length is the relevant finite number.

### 2.3 The augmentation kernel

The powers

$$
I\supseteq I^2\supseteq I^3\supseteq\cdots
$$

form the infinitesimal filtration normal to the distinguished section. The first quotient $I/I^2$ is conormal. Its dual $\operatorname{Hom}_{\mathcal O}(I/I^2,M)$ classifies $\mathcal O$-derivations from $A$ to an $\mathcal O$-module $M$ on which $A$ acts through $\lambda$.

The word **relative** is indispensable. The absolute maximal ideal is

$$
\mathfrak m_A=(\varpi)+I.
$$

Its quotient $\mathfrak m_A/\mathfrak m_A^2$ includes the coefficient direction represented by $\varpi$. By contrast, $I/I^2$ measures only motion relative to $\mathcal O$. The numerical criterion compares branches over the same coefficient base and must ignore the coefficient direction.

There is also a useful differential description. Evaluation through $\lambda$ gives

$$
\Omega_{A/\mathcal O}\otimes_{A,\lambda}\mathcal O
\simeq I/I^2.
$$

Indeed the conormal sequence for $A\twoheadrightarrow\mathcal O$ has zero terminal differential module because $\Omega_{\mathcal O/\mathcal O}=0$. This identity makes clear that the construction depends on the augmentation, not merely on the abstract ring $A$.

### 2.4 Generic isolation

The module $\Phi_A=I/I^2$ is torsion precisely when its localization at $K$ vanishes. Since localization commutes with conormal quotients,

$$
\Phi_A\otimes K\simeq I_K/I_K^2.
$$

For a finite-dimensional $K$-algebra, $I_K/I_K^2=0$ says that the $K$-point is unramified. Because the residue extension is $K/K$, this is equivalent to the point being étale and hence to a product decomposition $A_K\simeq K\times B$ at that factor.

Thus, for finite flat $A$, the following are equivalent:

1. $\Phi_A$ has finite $\mathcal O$-length;
2. $\Phi_A$ is $\mathcal O$-torsion;
3. the distinguished generic point is an étale factor of $A_K$.

This equivalence explains why finite cotangent length is the right isolation hypothesis. It neither requires every other generic factor to be reduced nor declares the entire generic fiber étale. It isolates only the branch selected by $\lambda$. Assuming $A_K$ reduced is a stronger, convenient condition used when normalization and trace pairings for all branches are discussed.

## 3. Cotangent and conormal modules at the point

### 3.1 First-order motion along the fiber

Suppose $M$ is an $\mathcal O$-module, viewed as an $A$-module through $\lambda$, and form the square-zero algebra $\mathcal O\oplus M$. An $\mathcal O$-algebra lift of $\lambda$ to $\mathcal O\oplus M$ has the form

$$
a\longmapsto (\lambda(a),d(a)),
$$

where $d$ is an $\mathcal O$-derivation. Since $d(I^2)=0$, the derivation factors through $I/I^2$; conversely every $\mathcal O$-linear map $I/I^2\to M$ gives a derivation. Hence

$$
\operatorname{Der}_{\mathcal O}(A,M)
\simeq
\operatorname{Hom}_{\mathcal O}(\Phi_A,M).
$$

If $\Phi_A$ is killed by $\varpi^n$, then relative infinitesimal motion exists only to bounded coefficient precision. A large length means that branches remain tangent through many powers of $\varpi$. This is a more refined measurement than the dimension of $\Phi_A/\varpi\Phi_A$, which counts directions but forgets their persistence.

By the structure theorem,

$$
\Phi_A\simeq\bigoplus_{j=1}^r\mathcal O/(\varpi^{a_j})
$$

when it has finite length. Its length is $\sum_j a_j$, whereas its minimum number of generators is $r$. Numerical criteria need the sum, not just the number of first-order directions.

### 3.2 Relative and absolute differentials

The transitivity sequence for $\mathbb Z\to\mathcal O\to A$, evaluated at $\lambda$, gives a right-exact sequence

$$
\Omega_{\mathcal O/\mathbb Z}\otimes_{\mathcal O}\mathcal O
\longrightarrow
\Omega_{A/\mathbb Z}\otimes_{A,\lambda}\mathcal O
\longrightarrow
\Phi_A
\longrightarrow0.
$$

Thus the absolute differential module contains a coefficient contribution. In mixed characteristic this contribution can itself be torsion and can corrupt a length comparison if it is silently included. The invariant in this book is always relative to $\mathcal O$ unless the word absolute is displayed.

At the closed point there is another distinction. The relative cotangent space of the special fiber is

$$
I/(I^2+\varpi I)\simeq\Phi_A/\varpi\Phi_A,
$$

whereas the full cotangent space of $A$ at its maximal ideal is

$$
\mathfrak m_A/\mathfrak m_A^2.
$$

There is a right-exact sequence

$$
k\cdot\overline\varpi
\longrightarrow
\mathfrak m_A/\mathfrak m_A^2
\longrightarrow
I/(I^2+\varpi I)
\longrightarrow0.
$$

The first arrow can fail to be injective if $\varpi\in\mathfrak m_A^2$. None of these vector spaces determines the $\mathcal O$-length of $\Phi_A$.

For the crossing algebra

$$
A_m=\mathcal O[X]/(X(X-\varpi^m)),
$$

the maximal ideal is $(\varpi,X)$. Its absolute cotangent space has the two evident classes of $\varpi$ and $X$, while its relative special-fiber cotangent space has only the class of $X$. Both vector-space dimensions are independent of $m$. The torsion module

$$
\Phi_{A_m}\simeq\mathcal O/(\varpi^m)
$$

remembers $m$. Thus there are three successive losses of information: passing from absolute to relative removes the coefficient direction; passing from the integral relative module to its reduction removes the order of tangency; taking only a dimension forgets the elementary divisors entirely.

### 3.3 Conormal sequences for a quotient

Let $f:R\twoheadrightarrow T$ be a surjective augmented $\mathcal O$-homomorphism, with kernel $J$. Compatibility means $\lambda_T\circ f=\lambda_R$, so $J\subseteq I_R$ and $f(I_R)=I_T$. Passing to conormal modules gives the exact sequence

$$
J/(J\cap I_R^2)
\longrightarrow
\Phi_R
\longrightarrow
\Phi_T
\longrightarrow0.
$$

The first arrow is injective by the way its source was written, so more explicitly

$$
0\longrightarrow
\frac{J+I_R^2}{I_R^2}
\longrightarrow
\Phi_R
\longrightarrow
\Phi_T
\longrightarrow0.
$$

If the two outer modules have finite length, then

$$
\operatorname{length}\Phi_R-
\operatorname{length}\Phi_T
=
\operatorname{length}\frac{J}{J\cap I_R^2}.
$$

This locates the first visible part of the kernel. But $J\subseteq I_R^2$ can make that quotient zero without making $J$ zero. The decisive role of complete-intersection and depth hypotheses is to prevent a kernel from hiding indefinitely in higher conormal order.

For a general, not necessarily surjective map, no such right-exact sequence exists. This is one reason surjectivity is structural rather than cosmetic in the isomorphism criterion.

### 3.4 Length and the order of tangency

Consider

$$
A_a=\mathcal O[X]/(X(X-a)),
\qquad \lambda(X)=0,
$$

where $0\ne a\in(\varpi)$. It is finite free of rank two with basis $1,X$. Its augmentation ideal is $(X)$, and the relation $X^2=aX$ gives

$$
\Phi_{A_a}=(X)/(X^2)\simeq\mathcal O/(a).
$$

Thus $\operatorname{length}\Phi_{A_a}=v_{\mathcal O}(a)$. The generic fiber has two points, $X=0$ and $X=a$, and the valuation of their difference measures their integral tangency.

The absolute closed-point cotangent space cannot see this order: for every $a\in(\varpi)$ it has the same relative dimension one over $k$. The length of the relative conormal module distinguishes crossing modulo $\varpi$ from crossing modulo $\varpi^{10}$. This is exactly the precision needed by a numerical comparison.

## 4. Congruence ideals and integral separation of branches

### 4.1 Why annihilate the augmentation kernel

Over the fraction field, an isolated distinguished point is separated from the rest of the algebra by an idempotent. Integrally, a local ring cannot contain that idempotent. We therefore seek integral multiples of it. The condition that an element $a\in A$ live only on the distinguished branch can be expressed without mentioning a decomposition: it must annihilate every element vanishing at that branch. This is why $\operatorname{Ann}_A(I)$, rather than $\operatorname{Ann}_{\mathcal O}(I/I^2)$, is the correct source of the congruence ideal.

Suppose $A$ is finite flat and $A_K\simeq K\times B$, with $\lambda_K$ the first projection. Then

$$
I_K=0\times B,
\qquad
\operatorname{Ann}_{A_K}(I_K)=K\times0=Ke_\lambda,
$$

where $e_\lambda=(1,0)$. Because $A\hookrightarrow A_K$,

$$
\operatorname{Ann}_A(I)=A\cap Ke_\lambda.
$$

This is a rank-one $\mathcal O$-lattice. There is therefore a unique nonzero ideal $\eta\subseteq\mathcal O$ such that

$$
A\cap Ke_\lambda=\eta e_\lambda.
$$

Applying $\lambda$ identifies this ideal with $\lambda(\operatorname{Ann}_A(I))$. Thus the annihilator definition and the denominator-of-an-idempotent picture agree.

### 4.2 The congruence ideal and module

For an augmented algebra with finite cotangent length, define

$$
\eta_A=\lambda(\operatorname{Ann}_A I_A),
\qquad
\Psi_A=\mathcal O/\eta_A.
$$

When $A$ is finite flat and the generic point is isolated, $\eta_A$ is nonzero. If $\eta_A=(\varpi^c)$, the least integral multiple of the generic idempotent has valuation $c$, up to a unit. Consequently

$$
\operatorname{length}\Psi_A=c.
$$

The ideal itself is sometimes represented by a generator and called a congruence number. A generator is only defined up to a unit; the ideal and its colength are canonical.

The annihilator of the cotangent module is a different object. In the elementary divisor decomposition

$$
\Phi_A\simeq\bigoplus_j\mathcal O/(\varpi^{a_j}),
$$

one has

$$
\operatorname{Ann}_{\mathcal O}(\Phi_A)
=(\varpi^{\max a_j}),
\qquad
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)
=(\varpi^{\sum a_j}).
$$

Only the Fitting ideal records total length. Neither ideal is equal to $\eta_A$ without further hypotheses. In the complete-intersection case the zeroth Fitting ideal equals $\eta_A$; this is a theorem, not part of the definition.

### 4.3 Normalization and the missing idempotent

Assume for this section that $A_K$ is finite étale over $K$. Its normalization in $A_K$ is a product

$$
\widetilde A=\mathcal O_1\times\cdots\times\mathcal O_s
$$

of finite extensions of $\mathcal O$, after choosing the integral closures in the field factors. The distinguished $K$-factor is $K$ itself, so its integral ring is $\mathcal O$. The idempotent $e_\lambda$ belongs to $\widetilde A$ but not to the local subring $A$ unless there are no other branches.

The finite quotient $\widetilde A/A$ measures all failures of normality and all integral contacts among branches. The congruence module sees only the distinguished coordinate of this failure. Indeed the least $c$ such that $\varpi^c e_\lambda\in A$ is the exponent at which the distinguished branch can be cut away integrally. Equivalently, its class in $\widetilde A/A$ is killed by $\eta_A$ and has annihilator exactly $\eta_A$.

Two characteristic-zero points can therefore be distinct while being congruent modulo a large power of $\varpi$. If $\mu:A\to\mathcal O'$ is another augmentation into a finite extension and

$$
\mu(a)\equiv\lambda(a)\pmod{\mathfrak p'^n}
$$

for every $a\in A$, their branches do not separate in the integral model before precision $n$. The normalization separates them instantly; the original local order remembers their congruence.

One must not identify $\widetilde A/A$ with $\Psi_A$. The normalization quotient includes contacts among all branches and internal nonnormality within them. The congruence module is a one-branch projection, canonically defined by the augmentation.

For a split monogenic example this projection is concrete. Suppose

$$
f(X)=\prod_{i=1}^d(X-a_i),\qquad a_i\in\mathcal O,
$$

with distinct roots in $K$, all congruent modulo $\varpi$, and distinguish $a_1$. Evaluation embeds $A=\mathcal O[X]/(f)$ in $\mathcal O^d$. The Lagrange idempotent for $a_1$ is

$$
e_1(X)=\prod_{i>1}\frac{X-a_i}{a_1-a_i}.
$$

Its denominator ideal is generated by

$$
\prod_{i>1}(a_1-a_i)=f'(a_1).
$$

Consequently the distinguished congruence length is

$$
\sum_{i>1}v_{\mathcal O}(a_1-a_i).
$$

This counts contacts with the distinguished branch but not contacts among $a_2,\ldots,a_d$. The latter do appear in the full normalization quotient and in the discriminant.

### 4.4 Two crossing branches

Return to

$$
A_a=\mathcal O[X]/(X(X-a)),
\qquad \lambda(X)=0.
$$

Inside $K\times K$, evaluation at $0$ and $a$ identifies

$$
A_a=\{(u,v)\in\mathcal O^2:u\equiv v\pmod a\}.
$$

The distinguished idempotent is $(1,0)$, and

$$
A_a\cap K(1,0)=a\mathcal O(1,0).
$$

Thus $\eta_{A_a}=(a)$ and

$$
\Psi_{A_a}\simeq\mathcal O/(a).
$$

We already found $\Phi_{A_a}\simeq\mathcal O/(a)$. The two lengths agree. Geometrically, there is one independent equation cutting two branches, and its derivative at the distinguished branch records exactly their separation.

The element $X-a$ annihilates $I=(X)$, and its augmentation is $-a$. This gives the same calculation without normalization. It also displays a useful rule for a factorization $f(X)=Xg(X)$: at the root $X=0$, the complementary factor $g(X)$ kills the augmentation ideal, and $g(0)=f'(0)$ generates the congruence ideal when the quotient is flat.

### 4.5 Several branches and strictness

Consider the local order

$$
A=\{(a_1,a_2,a_3)\in\mathcal O^3:
a_1\equiv a_2\equiv a_3\pmod\varpi\},
$$

augmented by the first projection. It is finite free of rank three. With

$$
x=(0,\varpi,0),\qquad y=(0,0,\varpi),
$$

it has the presentation

$$
A\simeq
\mathcal O[X,Y]/(X^2-\varpi X,\ XY,\ Y^2-\varpi Y).
$$

The augmentation ideal is $I=(x,y)$ and

$$
I^2=(\varpi x,\varpi y),
\qquad
\Phi_A\simeq k\oplus k.
$$

An element annihilating $I$ has the form $(\varpi b,0,0)$, so $\eta_A=(\varpi)$ and $\Psi_A\simeq k$. Therefore

$$
\operatorname{length}\Phi_A=2>1=
\operatorname{length}\Psi_A.
$$

The ring has codimension two in a two-variable regular local ring but requires three displayed relations; it is not a complete intersection. This example fixes the direction of the fundamental inequality and previews the equality criterion.

## 5. Trace, different, discriminant, and duality

### 5.1 Perfect pairings on the generic fiber

Assume $A$ is finite flat and $A_K$ is finite étale. The trace pairing

$$
A_K\times A_K\longrightarrow K,
\qquad (x,y)\longmapsto\operatorname{Tr}_{A_K/K}(xy)
$$

is perfect. It identifies $A_K$ with its $K$-dual. The integral dual lattice is the **complementary module** or **codifferent**

$$
A^\#=\{x\in A_K:
\operatorname{Tr}_{A_K/K}(xA)\subseteq\mathcal O\}
\simeq\operatorname{Hom}_{\mathcal O}(A,\mathcal O).
$$

It contains $A$. The finite quotient $A^\#/A$ is measured globally by the discriminant: if $a_1,\ldots,a_d$ is an $\mathcal O$-basis, then the determinant of $(\operatorname{Tr}(a_i a_j))$ generates the discriminant ideal, and its valuation is the length of $A^\#/A$.

This global discriminant must not be confused with a one-branch congruence ideal. The discriminant counts all pairwise collisions, with multiplicity, whereas $\eta_A$ records the denominator of one idempotent. In the two-branch algebra $A_a$, the discriminant is generated by $a^2$, while the congruence ideal is $(a)$. The square is not an error: the trace determinant sees the pair of branches symmetrically.

Indeed, in the basis $1,X$ of $A_a$ the trace matrix is

$$
\begin{pmatrix}
2&a\\
a&a^2
\end{pmatrix},
$$

whose determinant is $a^2$. The complementary lattice therefore has index of length $2v(a)$, even though the distinguished idempotent needs only $v(a)$ powers of the uniformizer. Choosing the other branch gives the same congruence length; adding the two branch contributions recovers the discriminant exponent in this example.

### 5.2 The complementary module and the different

The **Dedekind different** of the order is the conductor-like ideal

$$
\mathfrak D_A=(A:A^\#)=\{d\in A:dA^\#\subseteq A\}.
$$

For a monogenic finite flat algebra $A=\mathcal O[X]/(f)$ with étale generic fiber, the class $\alpha$ of $X$ satisfies

$$
\mathfrak D_A=(f'(\alpha))
$$

provided $f$ is monic. If the augmentation is evaluation at a simple root $a\in\mathcal O$, then

$$
\lambda(\mathfrak D_A)=(f'(a)).
$$

Writing $f=(X-a)g$ gives $f'(a)=g(a)$, the product of the separations from the other roots after a splitting extension. This is also the congruence ideal at that branch.

In several variables, the Kähler different is generated by maximal minors of a Jacobian matrix. It always annihilates the module of relative differentials. For a complete intersection of relative dimension zero it agrees with the appropriate different, and evaluation at the augmented point gives $\eta_A$. Outside the complete-intersection or Gorenstein setting, the various differents can differ. Only inclusions are safe in general.

### 5.3 Gorenstein duality and the congruence ideal

A finite flat $\mathcal O$-algebra is **Gorenstein over $\mathcal O$** when its dual

$$
A^\vee=\operatorname{Hom}_{\mathcal O}(A,\mathcal O)
$$

is free of rank one as an $A$-module. Finite flat complete intersections have this property. Choosing a generator $\theta:A\xrightarrow{\sim}A^\vee$ supplies a perfect associative pairing

$$
\langle x,y\rangle=\theta(x)(y).
$$

After tensoring with $K$, the distinguished idempotent line $Ke_\lambda$ is orthogonal to the complementary factor. The integral intersection of that line with $A$ is $\eta_A e_\lambda$. Duality identifies its index with the failure of the distinguished evaluation functional to generate an integral direct summand.

In a complete-intersection presentation, the relative dual generator obtained from the Jacobian determinant spans this branch line. Evaluation therefore yields

$$
\eta_A=\operatorname{Fitt}_{\mathcal O}^0(\Phi_A).
$$

Gorenstein duality explains conceptually why one determinant controls both invariants. Yet the Gorenstein property alone should not be substituted casually for complete intersection in converse statements: a Gorenstein ring need not be a complete intersection. For the forward equality, one needs a hypothesis that identifies the relevant different with the Jacobian different, or one states that identification separately.

### 5.4 Fitting ideals and what they do not say

If $M$ is a finite torsion $\mathcal O$-module, then

$$
\operatorname{Fitt}_{\mathcal O}^0(M)
=(\varpi^{\operatorname{length}M}).
$$

Thus length inequalities reverse to ideal inclusions:

$$
\operatorname{length}M\geq\operatorname{length}(\mathcal O/J)
\quad\Longleftrightarrow\quad
\operatorname{Fitt}_{\mathcal O}^0(M)\subseteq J.
$$

The fundamental numerical inequality is therefore equivalent to

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)\subseteq\eta_A.
$$

This direction is a frequent source of sign errors. Larger torsion modules have smaller Fitting ideals.

For a cyclic module, the annihilator and zeroth Fitting ideal agree. For a direct sum they generally do not. In the three-branch example,

$$
\operatorname{Ann}_{\mathcal O}(\Phi_A)=(\varpi),
\qquad
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=(\varpi^2),
\qquad
\eta_A=(\varpi).
$$

Replacing the Fitting ideal by the annihilator would erase the strictness that detects failure of complete intersection.

## 6. Complete intersections and Jacobian calculations

### 6.1 Presentations adapted to the augmentation

Let $A$ be a finite flat complete local $\mathcal O$-algebra with augmentation $\lambda$. Choose elements $x_1,\ldots,x_n$ generating $I_A$ topologically and send formal variables to them. This gives an augmented surjection

$$
S=\mathcal O[[X_1,\ldots,X_n]]\twoheadrightarrow A,
\qquad X_i\longmapsto x_i,
$$

where the augmentation on $S$ sends every $X_i$ to zero. Its kernel $J$ is contained in $(X_1,\ldots,X_n)$ because every relation evaluates to zero.

Since $A$ is finite flat, $\dim A=1$, while $\dim S=n+1$. Thus $J$ has height $n$. If $A$ is a complete intersection, $J$ is generated by an $S$-regular sequence $f_1,\ldots,f_n$. The equality between number of variables and number of equations is not an arbitrary square-matrix assumption; it follows from relative dimension zero and complete intersection.

Each $f_i$ can be expanded as

$$
f_i=\sum_{j=1}^n a_{ij}X_j+\text{terms in }(X_1,\ldots,X_n)^2,
\qquad a_{ij}\in\mathcal O.
$$

The matrix $J_\lambda=(a_{ij})$ is the Jacobian matrix evaluated at the augmentation. Formally, $a_{ij}=\lambda(\partial f_i/\partial X_j)$.

### 6.2 The Jacobian presents the cotangent module

Apply the conormal sequence to $S\twoheadrightarrow A$ and then evaluate at $\lambda$. Since

$$
\Omega_{S/\mathcal O}\otimes_{S,\lambda}\mathcal O
\simeq\mathcal O^n
$$

with basis $dX_1,\ldots,dX_n$, the classes of $df_i$ give a presentation

$$
\mathcal O^n\xrightarrow{J_\lambda}
\mathcal O^n\longrightarrow\Phi_A\longrightarrow0.
$$

The transpose may appear depending on whether vectors are written as rows or columns; its determinant generates the same ideal. Generic isolation is equivalent to $\det J_\lambda\ne0$ in this complete-intersection setting.

Smith normal form gives

$$
\operatorname{length}\Phi_A=v_{\mathcal O}(\det J_\lambda),
\qquad
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=(\det J_\lambda).
$$

This calculation also shows why merely reducing the Jacobian modulo $\varpi$ is insufficient. Its nullity counts generators of $\Phi_A$, while the valuation of its determinant adds all elementary-divisor exponents.

### 6.3 The determinant computes both lengths

**Theorem (Jacobian congruence formula).** Let $A$ be finite flat and local over $\mathcal O$, let $A_K$ be generically separated at $\lambda$, and suppose

$$
A\simeq\mathcal O[[X_1,\ldots,X_n]]/(f_1,\ldots,f_n)
$$

with $f_1,\ldots,f_n$ a regular sequence and $\lambda(X_i)=0$. Then

$$
\eta_A=(\det J_\lambda),
$$

and consequently

$$
\operatorname{length}\Psi_A
=\operatorname{length}\Phi_A
=v_{\mathcal O}(\det J_\lambda).
$$

**Proof strategy.** The cotangent calculation has already produced the determinant. To connect it to congruences, one uses the determinant form of complete-intersection duality. The Koszul resolution of $A$ over $S$ is self-dual. After applying $\operatorname{Hom}_S(-,S)$, its top exterior map identifies $A^\vee$ with a free rank-one $A$-module. Under this identification, the element supported on the distinguished generic factor evaluates to the Jacobian determinant.

**Proof.** The regular sequence gives the Koszul resolution

$$
0\to\bigwedge^nS^n\to\cdots\to S^n\to S\to A\to0.
$$

Dualizing and then taking the relative residue along $X_1=\cdots=X_n=0$ identifies the generator of $\operatorname{Hom}_{\mathcal O}(A,\mathcal O)$ with the Grothendieck residue functional. Multiplication by an element of $\operatorname{Ann}_A(I)$ is supported generically on $Ke_\lambda$. The residue of the branch idempotent is $1/\det J_\lambda$; equivalently, the smallest scalar making that idempotent integral is generated by $\det J_\lambda$. Therefore

$$
A\cap Ke_\lambda=(\det J_\lambda)e_\lambda.
$$

Applying $\lambda$ gives the ideal formula. The two length formulas follow from the square presentation of $\Phi_A$. $\square$

The residue language in the proof can be replaced by iterated adjugate matrices. The decisive facts are the regularity of the sequence, which makes the Koszul complex a resolution, and the top exterior determinant, which appears both in the conormal presentation and in the dual generator.

### 6.4 Hypersurfaces in detail

Let $f(X)\in\mathcal O[X]$ be monic, let $a\in\mathcal O$ satisfy $f(a)=0$, and suppose $f'(a)\ne0$. Put

$$
A=\mathcal O[X]/(f),
\qquad \lambda(X)=a.
$$

After replacing $X$ by $X+a$, assume $a=0$ and write $f=Xg$. Then

$$
I=(X),\qquad
\Phi_A\simeq\mathcal O/(f'(0)).
$$

Moreover $g(X)I=0$, so $g(X)\in\operatorname{Ann}_A(I)$ and $\lambda(g)=g(0)=f'(0)$. Conversely, after inverting $\varpi$, every annihilator of $I$ is a scalar multiple of the branch idempotent, and integrality forces its augmentation to be divisible by $f'(0)$; hence

$$
\eta_A=(f'(0)).
$$

For $f=X(X-\varpi^m)$ both modules are $\mathcal O/(\varpi^m)$. For

$$
f=X(X-\varpi^a)(X-u\varpi^b),
$$

with $u$ a unit and distinct generic roots, the distinguished congruence and cotangent lengths are $a+b$, because

$$
f'(0)=u\varpi^{a+b}.
$$

Each other branch contributes its distance from the distinguished one.

### 6.5 A two-variable calculation

Let $a,b\in(\varpi)$ be nonzero and consider

$$
A=\mathcal O[[X,Y]]/(X(X-a),\ Y(Y-b)),
\qquad \lambda(X)=\lambda(Y)=0.
$$

It is finite free of rank four, and the two equations form a regular sequence. The evaluated Jacobian is

$$
J_\lambda=
\begin{pmatrix}
-a&0\\
0&-b
\end{pmatrix}.
$$

Therefore

$$
\Phi_A\simeq\mathcal O/(a)\oplus\mathcal O/(b),
\qquad
\eta_A=(ab),
$$

and both numerical lengths are $v(a)+v(b)$. Notice again that

$$
\operatorname{Ann}_{\mathcal O}(\Phi_A)
=(\varpi^{\max\{v(a),v(b)\}})
$$

need not equal $(ab)$. The determinant, not the exponent, combines independent congruence directions.

## 7. The fundamental inequality and the converse theorem

### 7.1 The sign of the inequality

The complete-intersection calculation suggests the invariant

$$
\delta(A)=
\operatorname{length}\Phi_A-
\operatorname{length}\Psi_A.
$$

The basic theorem says that $\delta(A)\ge0$ in the finite-flat isolated-branch setting. In ideal language,

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)\subseteq\eta_A.
$$

The three-branch order has $\delta(A)=1$. A complete intersection has $\delta(A)=0$. These two tests should always be performed when a formula is in doubt.

Why should cotangent length be larger? Congruence length measures the denominator necessary to separate one generic branch. Cotangent length measures that separation plus any surplus first-order relations caused by a non-complete-intersection singularity. Surplus singularity can enlarge $\Phi_A$ without making the branch idempotent harder to clear.

### 7.2 A determinant proof of the inequality

**Theorem (fundamental numerical inequality).** Let $A$ be a finite flat local $\mathcal O$-algebra with augmentation $\lambda$. Assume the distinguished point is a factor of $A_K$, equivalently that $\Phi_A$ has finite length. Then

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)\subseteq\eta_A,
$$

or equivalently

$$
\operatorname{length}\Phi_A\ge
\operatorname{length}\Psi_A.
$$

**Proof strategy.** Present $A$ by a regular formal power-series ring. The linear terms of all relations give a rectangular Jacobian matrix presenting $\Phi_A$. Its maximal minors generate the Fitting ideal. Each maximal minor is a Jacobian different: an adjugate calculation shows that its image on the distinguished factor clears the denominator of the branch idempotent. Hence every minor belongs to $\eta_A$.

**Proof.** Choose an augmented presentation

$$
S=\mathcal O[[X_1,\ldots,X_n]]\twoheadrightarrow A
$$

and finite generators $f_1,\ldots,f_m$ of its kernel. Since $A$ is finite flat, the kernel has height $n$, so $m\ge n$. Evaluating differentials at $\lambda$ gives

$$
\mathcal O^m\xrightarrow{J_\lambda}
\mathcal O^n\longrightarrow\Phi_A\longrightarrow0.
$$

Thus $\operatorname{Fitt}^0(\Phi_A)$ is generated by the $n\times n$ minors of $J_\lambda$.

Fix such a minor, arising from relations $g_1,\ldots,g_n$. The adjugate identity

$$
\operatorname{adj}(J_g)J_g=(\det J_g)I_n
$$

is the linear shadow of the corresponding identity for Kähler differentials. In the quotient $A$, it says that the Jacobian determinant lies in the Kähler different and annihilates every relative differential. More precisely, the standard determinant construction for the diagonal $A\otimes_{\mathcal O}A\to A$ produces an element $d_g\in\operatorname{Ann}_A(I)$ whose augmentation is $\det J_g(0)$. One may verify this directly by writing

$$
g_i(X)-g_i(Y)=\sum_j h_{ij}(X,Y)(X_j-Y_j)
$$

and applying the adjugate matrix $(h_{ij})$ before setting $Y=0$. Therefore every maximal minor belongs to $\lambda(\operatorname{Ann}_A I)=\eta_A$.

The minors generate $\operatorname{Fitt}^0(\Phi_A)$, proving the ideal inclusion. Since both ideals are nonzero principal ideals of the DVR, taking valuations gives the length inequality. $\square$

The proof uses flatness when $A$ is embedded into its generic fiber and when generic isolation is translated into nonzero determinants. Without it, a vertical torsion direction can be invisible to the branch decomposition.

### 7.3 Equality detects complete intersections

The converse is the rigidity behind the numerical method.

We first isolate the commutative-algebra step that prevents the converse from becoming circular.

**Lemma (relation--determinant lemma).** Let

$$
S=\mathcal O[[X_1,\ldots,X_n]],\qquad A=S/J,
$$

where $A$ is finite flat over $\mathcal O$, the augmentation sends every $X_i$ to zero, and the selected generic point is isolated. Let

$$
d_\lambda:J\longrightarrow\mathcal O^n,
\qquad
g\longmapsto
\left(\lambda\left(\frac{\partial g}{\partial X_1}\right),
\ldots,
\lambda\left(\frac{\partial g}{\partial X_n}\right)\right).
$$

Then the determinant ideal of the full-rank lattice $d_\lambda(J)\subseteq\mathcal O^n$ is contained in $\eta_A$. Equality holds if and only if $J$ can be generated by $n$ elements. In that event those generators form an $S$-regular sequence.

**Proof strategy.** The ideal inclusion is the maximal-minor argument of Section 7.2. For the equality statement one selects a parameter reduction inside $J$, compares its Koszul complex with a presentation of $A$, and filters the additional relations by augmentation order. Regularity of $\varpi$ prevents cancellation between successive determinant contributions.

**Proof.** The image $d_\lambda(J)$ has rank $n$: its cokernel is $\Phi_A$, which is torsion. Its determinant ideal is precisely

$$
\bigwedge^n d_\lambda(J)subseteq
\bigwedge^n\mathcal O^n\simeq\mathcal O,
$$

and hence is $\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)$. Section 7.2 shows that every determinant arising from $n$ relations belongs to $\eta_A$, proving the inclusion.

For the equality case, it is useful to spell out the standard reduction argument. After a faithfully flat extension of complete DVRs with ramification index one, if necessary, the residue field may be assumed infinite. This extension need not be finite; a finite unramified extension of a finite residue field would still have finite residue field. One can then choose $g_1,\ldots,g_n\in J$ simultaneously so that their reductions generate a reduction of the maximal-primary ideal $(J,\varpi)/(\varpi)$ and so that their evaluated differential determinant has the least possible valuation, namely the valuation of $\operatorname{Fitt}^0(\Phi_A)$. These are simultaneous generic conditions on the coefficient matrix used to combine a finite generating set of $J$: the first avoids the finitely many proper linear conditions coming from the special-fiber minimal primes, and the second asks that a maximal minor generating the determinant lattice have unit coefficient. Put $Q=(g_1,\ldots,g_n)$ and $B=S/Q$.

The sequence $\varpi,g_1,\ldots,g_n$ is a system of parameters of the regular local ring $S$. In a Cohen--Macaulay ring every system of parameters is regular, in every order. Consequently $g_1,\ldots,g_n$ is regular, $\varpi$ is regular on $B$, and $B$ is finite flat over $\mathcal O$. Complete-intersection duality gives

$$
\eta_B=operatorname{Fitt}_{\mathcal O}^0(\Phi_B)
=\operatorname{Fitt}_{\mathcal O}^0(\Phi_A).
$$

The quotient $B\twoheadrightarrow A$ has kernel $J/Q$. Compare the Koszul resolution of $B$ with a finite free presentation of $A$, and pass to the Rees modules for the $(X_1,\ldots,X_n)$-adic filtrations. In degree one the comparison map is the evaluated conormal map; in top degree it is its exterior determinant. If $J/Q$ is nonzero, separatedness gives a nonzero initial class. The top Koszul boundary sends the first such class to a nonzero quotient of

$$
\eta_A/\eta_B.
$$

There is no cancellation with later filtration terms: multiplication by $\varpi$ is injective on both $B$ and $A$, so every finite-length Koszul homology term occurring in the determinant comparison contributes with the same sign. Artin--Rees identifies the induced filtration on $J/Q$ with its Rees filtration and ensures that the initial class detected in the associated graded module comes from an actual element of the kernel. It follows that

$$
J/Q\ne0\quad\Longrightarrow\quad \eta_B\subsetneq\eta_A.
$$

This implication is often called the determinant-defect step. Notice that it compares actual ideals, not a signed Euler characteristic. If

$$
\eta_A=operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=\eta_B,
$$

the implication forces $J=Q$, so $J$ has $n$ generators. Conversely, if $J$ has $n$ generators, its height is $n$ and those generators are a regular sequence in the Cohen--Macaulay ring $S$; the Jacobian congruence formula gives equality. Faithfully flat descent removes the auxiliary ramification-index-one coefficient extension. $\square$

**Theorem (Lenstra's numerical complete-intersection characterization).** Let $A$ be a finite flat complete local $\mathcal O$-algebra with augmentation $\lambda$, and suppose $\Phi_A$ has finite length. Then

$$
A\text{ is a complete intersection over }\mathcal O
\quad\Longleftrightarrow\quad
\operatorname{length}\Phi_A=
\operatorname{length}\Psi_A.
$$

When these conditions hold, $A$ is Gorenstein and

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=\eta_A.
$$

**Proof.** Choose an augmented presentation $S\twoheadrightarrow A$. Finite flatness makes $A$ one-dimensional Cohen--Macaulay, so the presentation ideal has height equal to the number of variables. The forward implication is the Jacobian congruence formula. For the converse, equality of lengths is equality of the principal ideals

$$
\operatorname{Fitt}_{\mathcal O}^0(\Phi_A)=\eta_A.
$$

The relation--determinant lemma says that the presentation ideal is generated by the expected number of elements, hence by a regular sequence. Thus $A$ is a complete intersection. $\square$

The proof is not a tangent-space argument. Its technical heart is the filtered determinant-defect step, which rules out extra relations whose first derivatives happen to vanish. This is why equality detects an actual complete-intersection presentation rather than only its linear approximation.

### 7.4 Exact hypotheses and boundary cases

Completeness is convenient for the adapted power-series presentation and for Nakayama applied to closed kernels. An equivalent statement holds for a finite local $\mathcal O$-algebra before completion because such an algebra is already complete for its maximal ideal when $\mathcal O$ is complete. More generally, the theorem can be checked after completion.

Finite flatness supplies three facts at once: $A$ has dimension one, $\varpi$ is a nonzerodivisor, and $A$ is a lattice in $A_K$. Replacing it merely by “finite” is not legitimate. Replacing it by “torsion-free finite” is legitimate over a DVR because that is equivalent to finite flatness.

Reducedness of all of $A_K$ is not required for the intrinsic inequality or converse. What is required is that the distinguished $K$-point be an étale factor, equivalently that $\Phi_A$ have finite length. Reducedness of $A_K$ is already sufficient for this selected-factor statement: a finite reduced $K$-algebra is a product of fields, and a $K$-algebra augmentation splits off a $K$-factor. Over an imperfect $K$, however, the other field factors can be inseparable. Finite étaleness of the whole generic fiber, not mere reducedness, is the hypothesis needed for the perfect trace pairing of Chapter 5.

Finally, $\eta_A\ne0$ is not an independent assumption once finite flatness and generic isolation hold. It is the nonzero denominator ideal of $e_\lambda$. If generic isolation fails, both $\Phi_A$ and $\Psi_A$ may have infinite length or $\eta_A$ may be zero, and the numerical statement no longer exists.

## 8. The numerical isomorphism criterion

### 8.1 The comparison problem

Let

$$
R\xrightarrow{f}T
$$

be a map of complete local $\mathcal O$-algebras, and suppose both rings carry augmentations to $\mathcal O$. A numerical isomorphism theorem is useful only after four structural questions have been answered.

First, is $f$ surjective? The criterion eliminates a kernel; it does not manufacture missing elements of the target. Second, are the augmentations compatible? Otherwise the two cotangent modules are attached to different points. Third, is the target finite flat, so that its congruence ideal has the branch-lattice interpretation? Fourth, is the source cotangent module finite? No finiteness, flatness, or complete-intersection hypothesis on the source is needed in the strongest form of the theorem.

Once these questions have affirmative answers, the required numerical input is deliberately one-sided:

$$
\operatorname{length}\Phi_R
\leq
\operatorname{length}\Psi_T.
$$

This may look opposite to the intrinsic inequality. That is precisely why it is powerful. Surjectivity and the intrinsic inequality already force the reverse chain. Equality first detects that $T$ is a complete intersection. Its regular sequence of relations then supplies the basis against which all source relations are compared.

### 8.2 Precise criterion

**Theorem (Wiles--Lenstra numerical isomorphism criterion).** Let $\mathcal O$ be a complete DVR. Suppose:

1. $R$ and $T$ are complete Noetherian local $\mathcal O$-algebras with compatible augmentations $\lambda_R$ and $\lambda_T$;
2. $f:R\twoheadrightarrow T$ is a surjective local $\mathcal O$-homomorphism;
3. $T$ is finite flat over $\mathcal O$;
4. $\Phi_R=I_R/I_R^2$ has finite $\mathcal O$-length; and
5. the numerical estimate

   $$
   \operatorname{length}\Phi_R
   \leq
   \operatorname{length}\Psi_T
   $$

   holds.

Then $f$ is an isomorphism, and both $R$ and $T$ are finite flat complete intersections over $\mathcal O$. Moreover

$$
\operatorname{length}\Phi_R
=\operatorname{length}\Phi_T
=\operatorname{length}\Psi_T.
$$

The quotient map makes $\Phi_T$ a quotient of $\Phi_R$, so hypothesis 4 already implies that the distinguished point of $T_K$ is isolated and that $\eta_T\ne0$. Thus no separate generic reducedness assumption is hidden in the statement.

The version in which $R$ is assumed beforehand to be finite flat and a complete intersection is the classical complete-intersection-source form of Wiles's criterion. The theorem above includes Lenstra's refinement: the numerical hypothesis itself forces those source properties. One should therefore not add source flatness or a square presentation when invoking the strongest form, and one should not silently omit them when invoking only the shorter Wiles-form proof.

A common equivalent input is an ideal inclusion. Since $\operatorname{Fitt}^0(\Phi_R)$ and $\eta_T$ are principal,

$$
\operatorname{length}\Phi_R\leq\operatorname{length}\Psi_T
\quad\Longleftrightarrow\quad
\eta_T\subseteq\operatorname{Fitt}_{\mathcal O}^0(\Phi_R).
$$

Notice the direction: the hypothesis places the congruence ideal inside the cotangent Fitting ideal.

### 8.3 Proof: conormal information

We prove the theorem rather than invoking it as a named black box. Put $J=\ker f$. Compatibility gives $J\subseteq I_R$, and the conormal sequence gives

$$
0\longrightarrow
C_f:=\frac{J}{J\cap I_R^2}
\longrightarrow
\Phi_R
\longrightarrow
\Phi_T
\longrightarrow0.
$$

Consequently

$$
\operatorname{length}\Phi_R
=\operatorname{length}C_f+\operatorname{length}\Phi_T.
$$

The target satisfies the fundamental inequality,

$$
\operatorname{length}\Phi_T\geq
\operatorname{length}\Psi_T.
$$

Combining this with the assumed opposite estimate produces

$$
\operatorname{length}\Psi_T
\geq
\operatorname{length}\Phi_R
=
\operatorname{length}C_f+\operatorname{length}\Phi_T
\geq
\operatorname{length}C_f+\operatorname{length}\Psi_T.
$$

Every length is nonnegative. Therefore

$$
C_f=0,
\qquad
\operatorname{length}\Phi_T=\operatorname{length}\Psi_T,
\qquad
\operatorname{length}\Phi_R=\operatorname{length}\Phi_T.
$$

The converse theorem of Chapter 7 now shows that $T$ is a complete intersection. At this stage we know $J\subseteq I_R^2$, but not yet $J=0$. Conormal information alone never justifies that final step. Notice also that $\eta_R$ need not even be a nonzero finite-colength ideal before the theorem has proved that $R\simeq T$; using an intrinsic inequality for $R$ here would assume precisely the source finiteness that Lenstra's refinement is designed to deduce.

### 8.4 Proof: comparison of relation lattices

It remains to prove $J=0$. We use the complete-intersection structure just proved for the target, not an unproved complete-intersection assertion about the source.

Choose finitely many elements of $I_R$ whose classes generate $I_R/I_R^2$ over $\mathcal O$. Relative topological Nakayama gives an augmented surjection

$$
S=\mathcal O[[X_1,\ldots,X_n]]\twoheadrightarrow R.
$$

Let $K_R$ and $K_T$ be the kernels of $S\to R$ and $S\to T$. Then

$$
K_R\subseteq K_T.
$$

Evaluation of differentials at the augmentation gives two sublattices of $\mathcal O^n$,

$$
N_R=d_\lambda(K_R),
\qquad
N_T=d_\lambda(K_T),
$$

and

$$
\Phi_R\simeq\mathcal O^n/N_R,
\qquad
\Phi_T\simeq\mathcal O^n/N_T.
$$

The map $\Phi_R\to\Phi_T$ was proved to be an isomorphism, so $N_R=N_T$ as actual submodules, not merely as lattices of the same index.

Because $T$ is a one-dimensional complete intersection and $S$ is regular of dimension $n+1$, the ideal $K_T$ is generated by an $S$-regular sequence $q_1,\ldots,q_n$. The finite length of $\Phi_T$ says that the evaluated differential vectors $d_\lambda q_i$ are linearly independent over $K$. Since they generate $N_T=N_R$, choose $p_i\in K_R$ with

$$
d_\lambda p_i=d_\lambda q_i
\qquad(1\leq i\leq n).
$$

Write

$$
p_i=\sum_{j=1}^n h_{ij}q_j,
\qquad h_{ij}\in S.
$$

Differentiating and evaluating at the augmentation eliminates the terms containing $q_j$, because every $q_j$ has augmentation zero. Hence

$$
d_\lambda p_i=
\sum_{j=1}^n\lambda(h_{ij})d_\lambda q_j.
$$

Linear independence of the $d_\lambda q_j$ and the chosen equalities imply that the matrix $(\lambda(h_{ij}))$ is the identity. Therefore $\det(h_{ij})$ has augmentation one and is a unit of the local ring $S$. The matrix $(h_{ij})$ is invertible, so every $q_j$ belongs to $(p_1,\ldots,p_n)\subseteq K_R$. Thus

$$
K_T\subseteq K_R.
$$

The reverse inclusion was automatic, and consequently $K_R=K_T$. Hence $R\simeq T$. In particular the source is now known, rather than assumed, to be finite flat and a complete intersection. $\square$

This final argument explains the force of equality. It says that the source relations and the target regular sequence have the same evaluated relation lattice. The change-of-generators matrix is therefore a unit, so no higher-order relation can remain hidden.

### 8.5 What the equality proves

The conclusion has three parts and their order matters. The intrinsic equality for $T$ proves that $T$ is a complete intersection. Equality of the conormal map then identifies the source and target relation lattices. Only the resulting unit change-of-generators proves that the surjection is an isomorphism; source finite flatness and complete-intersection structure follow afterward by transport across the isomorphism.

Conversely, if $R\simeq T$ and this common ring is a finite flat complete intersection, then the numerical equality follows automatically. Thus the theorem is both an isomorphism test and a structural test. The stronger formulation is especially useful when $R$ begins life only as a complete local ring with a finite cotangent module: no premature torsion-freeness or relation-count claim is required.

## 9. Finite modules with ring actions

### 9.1 Why a module can reveal the congruence ideal

In applications a finite algebra often appears through its action on an $\mathcal O$-lattice rather than through an explicit presentation. A faithful module $M$ embeds $A$ into $\operatorname{End}_{\mathcal O}(M)$, and the distinguished character $\lambda$ selects a generic eigenspace

$$
M_K[\lambda]=\{m\in M_K:am=\lambda(a)m
\text{ for every }a\in A\}.
$$

If $A_K=K\times B$, the branch idempotent projects $M_K$ onto this eigenspace. The integral lattice need not split as the sum of its intersections with the two generic summands. The quotient measuring this failure is a module-theoretic congruence module.

Define

$$
M_\lambda=M\cap e_\lambda M_K,
\qquad
M^c=M\cap(1-e_\lambda)M_K,
$$

and, when $M_K=e_\lambda M_K\oplus(1-e_\lambda)M_K$, set

$$
\Psi(M)=M/(M_\lambda+M^c).
$$

It is finite over $\mathcal O$. Its zeroth Fitting ideal

$$
\eta(M)=\operatorname{Fitt}_{\mathcal O}^0(\Psi(M))
$$

measures the integral failure of the eigenspace splitting. There is always a natural relationship with $\eta_A$, but equality requires a size hypothesis on the action.

### 9.2 Self-dual lattices and orthogonal branches

Suppose $M$ is finite free over $\mathcal O$ and carries a perfect pairing

$$
\langle , \rangle:M\times M\to\mathcal O
$$

for which every $a\in A$ is self-adjoint. Then the two generic summands are orthogonal:

$$
e_\lambda M_K\perp(1-e_\lambda)M_K.
$$

Consequently

$$
M^c=M\cap M_\lambda^\perp,
$$

There is a precise lattice formulation. Put

$$
P_\lambda=e_\lambda M={e_\lambda m:m\in M\}\subseteq e_\lambda M_K.
$$

Projection to the distinguished summand has kernel $M^c$, and therefore induces a canonical isomorphism

$$
\Psi(M)\simeq P_\lambda/M_\lambda.
$$

The perfect pairing identifies $P_\lambda$ with the integral dual lattice $M_\lambda^\vee$: a functional on the saturated sublattice $M_\lambda$ extends to $M$, perfectness represents it by an element of $M$, and orthogonal projection gives the representing element in $P_\lambda$. Thus

$$
\Psi(M)\simeq M_\lambda^\vee/M_\lambda,
$$

where $M_\lambda$ is embedded in its dual by the restricted pairing. If $M_\lambda$ has rank one, generated by $v$, the quotient is computed by the scalar relating $v$ to a primitive generator of its dual lattice.

The ring congruence ideal always gives an inclusion, but not automatically equality. Since $\eta_Ae_\lambda\subseteq A$, one has

$$
\eta_A P_\lambda\subseteq M_\lambda.
$$

When $M_\lambda$ has rank one, $P_\lambda/M_\lambda$ is cyclic and hence

$$
\eta_A\subseteq\eta(M).
$$

The exact **branch-saturation condition** needed to recover the ring invariant is

$$
M_\lambda=\eta_A P_\lambda.
$$

Under this condition $\eta(M)=\eta_A$. This formulation involves only canonically defined lattices; no map from $\operatorname{Ann}_A(I_A)$ to a dual eigenspace exists without choosing extra module data. Self-duality computes $P_\lambda/M_\lambda$, while the displayed saturation equality is the separate multiplicity-one input identifying it with the ring-theoretic congruence module.

### 9.3 A matrix-action calculation

Let

$$
A=\mathcal O[X]/(X(X-a)),
\qquad 0\ne a\in(\varpi),
$$

act on $M=\mathcal O^2$ through

$$
X\longmapsto
U=
\begin{pmatrix}
0&0\\
1&a
\end{pmatrix}.
$$

This is the regular action in the basis $1,X$ and is faithful. The generic $0$-eigenline and $a$-eigenline are

$$
K(-a,1),
\qquad
K(0,1).
$$

Their primitive integral generators form the columns of a matrix of determinant $-a$. Hence

$$
\Psi(M)\simeq\mathcal O/(a),
\qquad
\eta(M)=(a)=\eta_A.
$$

The pairing with Gram matrix

$$
P=
\begin{pmatrix}
0&1\\
1&a
\end{pmatrix}
$$

is perfect because $\det P=-1$, and $PU=U^{\mathsf t}P$. Thus the action is self-adjoint. The two generic eigenlines are visibly orthogonal:

$$
(-a,1)P(0,1)^{\mathsf t}=0.
$$

This elementary matrix example displays all pieces of the module variant: faithful action, perfect self-duality, orthogonal generic decomposition, and an integral index equal to the ring-theoretic congruence module.

### 9.4 Faithfulness and cyclicity hypotheses

If $M$ is not faithful, it sees only $A/\operatorname{Ann}_A(M)$. Its congruence ideal belongs to that quotient and cannot control the original ring. If the distinguished eigenspace has rank $r>1$ and the lattice splits identically in each copy, then

$$
\operatorname{Fitt}^0\Psi(M)=\eta_A^r,
$$

so its length is multiplied by $r$. A normalized determinant or a rank-one summand is then required.

For example, replace the matrix module of the preceding section by $M^{\oplus r}$ with the orthogonal direct-sum pairing. Its branch quotient is

$$
\Psi(M^{\oplus r})\simeq(\mathcal O/(a))^{\oplus r},
$$

so its Fitting ideal is $(a^r)$. Its annihilator remains $(a)$, another reminder that an annihilator cannot substitute for a determinant. Dividing the length by $r$ is justified here because the direct-sum structure is known; it would not be justified for an arbitrary rank-$r$ eigenspace with a nonsaturated lattice.

Even a faithful action can be nonsaturated. Replacing a self-dual lattice by a finite-index stable sublattice changes $\Psi(M)$ by lattice-index terms while leaving $A$ unchanged. This is why a module theorem must state perfectness and saturation integrally, not merely after tensoring with $K$.

A transparent sufficient case is the regular representation. If $M$ is free of rank one as an $A$-module and a chosen $A$-basis identifies its underlying lattice with $A$, then

$$
M_\lambda=A\cap Ke_\lambda=\eta_Ae_\lambda,
\qquad
P_\lambda=\mathcal Oe_\lambda,
$$

so branch saturation and $\eta(M)=\eta_A$ follow directly. More general multiplicity-one modules must verify the same lattice equality; faithfulness alone does not imply it.

Under the hypotheses of the preceding section, the numerical isomorphism theorem may be fed the module calculation:

$$
\operatorname{length}\Phi_R
\leq\operatorname{length}\Psi(M)
=\operatorname{length}\Psi_T.
$$

The module supplies the right-hand number; the ring theorem supplies the conclusion. The two roles should remain separate.

## 10. Defect modules and quantitative failure

### 10.1 From a difference of lengths to an object

A difference of lengths is informative, but an actual module says where the difference lives and behaves better under base change. The fundamental ideal inclusion provides such an object canonically:

$$
D_A=\eta_A/\operatorname{Fitt}_{\mathcal O}^0(\Phi_A).
$$

This is well-defined because $\operatorname{Fitt}^0(\Phi_A)\subseteq\eta_A$. There is an exact sequence

$$
0\longrightarrow D_A
\longrightarrow
\mathcal O/\operatorname{Fitt}^0(\Phi_A)
\longrightarrow
\mathcal O/\eta_A
\longrightarrow0.
$$

Since the middle module has the same length as $\Phi_A$,

$$
\operatorname{length}D_A
=\operatorname{length}\Phi_A-
\operatorname{length}\Psi_A
=\delta(A).
$$

Thus $D_A$ is the **intrinsic numerical defect module**.

### 10.2 The intrinsic complete-intersection defect

Under the finite-flat isolated-point hypotheses,

$$
D_A=0
\quad\Longleftrightarrow\quad
A\text{ is a complete intersection}.
$$

For the three-branch order of Chapter 4,

$$
D_A=(\varpi)/(\varpi^2)\simeq k.
$$

The module records exactly one surplus relation. It does not claim that the kernel of a chosen presentation is one-dimensional; rather, it records the determinant-level failure of a height-$n$ ideal to behave like an $n$-generated regular sequence at the augmented branch.

There are more elaborate homological defect modules, built from the first homology of a Koszul complex or from the conormal module $J/J^2$. Their alternating lengths recover the same number under Cohen--Macaulay hypotheses. The ideal quotient above is the smallest canonical package needed here.

### 10.3 The defect of a surjection

For a compatible surjection $f:R\twoheadrightarrow T$ with kernel $J$, define its visible conormal defect by

$$
C_f=J/(J\cap I_R^2).
$$

Then

$$
0\longrightarrow C_f
\longrightarrow\Phi_R
\longrightarrow\Phi_T
\longrightarrow0.
$$

There is also a branch-lattice defect. Since $\eta_R\subseteq\eta_T$, put

$$
B_f=\eta_T/\eta_R.
$$

It fits into

$$
0\longrightarrow B_f
\longrightarrow\Psi_R
\longrightarrow\Psi_T
\longrightarrow0.
$$

If $R$ is a finite flat complete intersection and $T$ is finite flat with isolated point, the three canonical exact sequences above imply the numerical identity

$$
\operatorname{length}B_f
=\operatorname{length}D_T+\operatorname{length}C_f.
$$

Indeed the left side is $\operatorname{length}\Psi_R-\operatorname{length}\Psi_T$, while $R$ has zero intrinsic defect and the conormal sequence gives the other two terms. After choosing compatible determinant presentations, this identity can be realized by a filtration of $B_f$ whose subquotients have the lengths of $D_T$ and $C_f$. There is no reason in the bare intrinsic setup for that filtration, or for an extension between the particular modules $D_T$ and $C_f$, to be canonical. The canonical exact sequences are the three separately displayed ones.

### 10.4 Exact sequences locating the loss

The preceding exact sequences and length identity separate two reasons a quotient can fail the criterion:

$$
\text{loss of branch lattice }B_f
\quad=
\quad
\text{intrinsic singular defect }D_T
+
\text{visible kernel }C_f.
$$

A kernel can vanish in degree one and appear only at higher augmentation order. To locate its initial terms, use the $I_R$-adic filtration

$$
C_f^{(q)}=
\frac{J\cap I_R^q}{J\cap I_R^{q+1}}.
$$

Because $J\subseteq I_R$, the degree-one piece is exactly $C_f$. Separatedness shows that a nonzero kernel has a first nonzero initial piece; Artin--Rees controls the induced filtration when the modules are finite. These graded pieces are useful diagnostics, but there is no canonical injection of each one into $B_f$ in the bare setup.

The rigorous kernel-elimination statements used in this book are more precise. In the finite-flat complete-intersection-source setting, the determinant-defect comparison packages the nonnegative contributions and proves that $B_f=0$ forces $J=0$. In the stronger Wiles--Lenstra setting, Chapter 8 first proves that the target is a complete intersection and then compares the two evaluated relation lattices; the unit change-of-generators proves $J=0$ directly. Either argument remedies the invalid inference “$J\subseteq I_R^2$, therefore $J=0$,” while avoiding an unsupported exact sequence between higher initial pieces and $B_f$.

## 11. Transporting numerical criteria

### 11.1 Localization and completion

Although the main rings are local, they often arise by localizing a finite algebra at the maximal ideal selected by an augmentation. If $A$ is finite flat over $\mathcal O$ and $\mathfrak m=\lambda^{-1}((\varpi))$, then localization preserves the augmentation kernel, annihilators, and Fitting ideals:

$$
\Phi_{A_{\mathfrak m}}
\simeq(\Phi_A)_{\mathfrak m},
\qquad
\eta_{A_{\mathfrak m}}=\eta_A
$$

after discarding factors on which the augmentation is unavailable. One must localize at the distinguished maximal ideal, not at an unrelated prime.

Completion is faithfully flat. For a Noetherian local augmented algebra,

$$
\Phi_{\widehat A}\simeq\Phi_A\otimes_A\widehat A
$$

evaluated at the augmented point, and finite-module Fitting ideals extend. If $A$ is already finite over complete $\mathcal O$, it is complete, so no change occurs. Complete-intersection structure is equivalent before and after completion.

Annihilators do not commute with arbitrary flat base change for arbitrary modules. Here finite presentation and faithful flatness give the needed compatibility. This qualification is important: the congruence ideal should be transported through its branch-lattice description or through a finite presentation, not through a blanket assertion about annihilators.

### 11.2 Extension of coefficient discrete valuation rings

Let $\mathcal O\to\mathcal O'$ be a finite extension of complete DVRs, with fraction fields $K\subseteq K'$ and ramification index $e$. Form

$$
A'=A\otimes_{\mathcal O}\mathcal O'
$$

and localize at the maximal ideal selected by the extended augmentation if the tensor product is semilocal. Flat base change gives

$$
\Phi_{A'}\simeq\Phi_A\otimes_{\mathcal O}\mathcal O'.
$$

If the distinguished factor remains isolated, the idempotent is $e_\lambda\otimes1$ and

$$
\eta_{A'}=\eta_A\mathcal O'.
$$

Consequently $D_{A'}\simeq D_A\otimes\mathcal O'$. Complete-intersection structure ascends under this flat base change and descends under faithful flatness.

If new generic factors split after extending $K$, only the localization containing the extended distinguished augmentation is retained. The formula still holds for that factor because the distinguished idempotent itself is unchanged. Combining several new maximal factors without localization can destroy locality and change the interpretation of the congruence module.

### 11.3 Ramification and numerical lengths

Let $M$ be a finite-length $\mathcal O$-module. If

$$
M\simeq\bigoplus_i\mathcal O/(\varpi^{a_i}),
$$

then

$$
M\otimes_{\mathcal O}\mathcal O'
\simeq
\bigoplus_i\mathcal O'/(u_i(\varpi')^{ea_i}).
$$

Therefore

$$
\operatorname{length}_{\mathcal O'}(M\otimes\mathcal O')
=e\operatorname{length}_{\mathcal O}(M).
$$

The residue degree does not appear when length is measured over the new DVR. It would appear if one converted both sides to dimensions over the original residue field. Thus

$$
\operatorname{length}_{\mathcal O'}\Phi_{A'}
=e\operatorname{length}_{\mathcal O}\Phi_A,
\qquad
\operatorname{length}_{\mathcal O'}\Psi_{A'}
=e\operatorname{length}_{\mathcal O}\Psi_A.
$$

Both the inequality and equality survive. Forgetting the factor $e$ is harmless for the truth of equality but wrong for every quantitative statement.

For instance, base-changing $A_m$ to $\mathcal O'$ changes the separation $\varpi^m$ to one of $\mathcal O'$-valuation $em$. Both the evaluated derivative and the denominator of the branch idempotent acquire that valuation. The residue degree does not change this length calculation; it appears only if one converts the underlying residue spaces to dimensions over the original field $k$.

### 11.4 Quotients by regular sequences

Regular quotients require more care than localization or flat base change. A nonzero regular element of a one-dimensional finite flat $\mathcal O$-algebra produces a zero-dimensional quotient and generally destroys $\mathcal O$-flatness. Thus the finite-flat numerical criterion is not literally closed under arbitrary regular quotients.

The useful operation occurs before reaching relative dimension zero. Suppose $A$ is an augmented Cohen--Macaulay $\mathcal O$-algebra of relative dimension $r$, and $z_1,\ldots,z_r\in I_A$ is an $A$-regular sequence such that

$$
\overline A=A/(z_1,\ldots,z_r)
$$

is finite flat. The conormal sequence is

$$
(z)/(z)^2\otimes_A\mathcal O
\longrightarrow\Phi_A
\longrightarrow\Phi_{\overline A}
\longrightarrow0.
$$

If the linearization of the $z_i$ splits off a free direct summand, quotienting removes exactly those free relative directions. The remaining torsion cotangent module is the one used numerically. On the dual side, the Koszul determinant of the regular sequence multiplies the relative different; after removing the same determinant contribution, the congruence ideal of $\overline A$ is obtained.

In comparisons, take compatible regular sequences in $R$ and $T$, require their images to agree, require regularity on both rings, and verify that the quotients are finite flat. Under those assumptions the conormal and Koszul diagrams commute, and complete-intersection presentations pass to the quotients. The numerical inequality itself does not follow from regularity alone: one must also verify that the two determinant contributions agree, or recompute $\Phi$ and $\eta$ after quotienting. Once that quotient-level bound is known, the numerical criterion applies. If a sequence is regular only on the source, its image can be a zerodivisor on the target and even this comparison fails.

A basic model is

$$
A^+=A_m[[Z_1,\ldots,Z_r]]
$$

with every $Z_i$ sent to zero by the augmentation. The sequence $Z_1,\ldots,Z_r$ is regular and the quotient is $A_m$. Before quotienting,

$$
I_{A^+}/I_{A^+}^2
\simeq
\Phi_{A_m}\oplus\mathcal O^r
$$

has a free part and therefore no finite length. Quotienting removes exactly those formal directions and leaves the torsion module $\Phi_{A_m}$. This is the clean situation in which a regular quotient transports the numerical problem. A relation such as $\varpi Z_1=0$ would make $Z_1$ nonregular and introduce a vertical defect instead.

## 12. A gallery of examples

### 12.1 A smooth point and an isolated branch

The smallest example is $A=\mathcal O$ with its identity augmentation. Then

$$
I_A=0,\qquad \Phi_A=0,\qquad
\operatorname{Ann}_A(I_A)=A,\qquad \eta_A=\mathcal O.
$$

Thus $\Psi_A=0$ and both lengths vanish. The generic idempotent is already integral because there is no complementary branch. This is the zero point from which all positive congruence lengths should be measured.

At the opposite extreme, take a nontrivial finite unramified local extension $C/\mathcal O$. It has no $\mathcal O$-algebra augmentation to $\mathcal O$: such a retraction would induce an impossible retraction of the nontrivial residue-field extension. It can contribute a generic branch to a larger algebra but cannot itself be distinguished by an $\mathcal O$-valued point. The existence of the augmentation is therefore genuine arithmetic structure, not an automatic feature of finite flat algebras.

For a product $A=\mathcal O\times C$ with first projection, the invariants again vanish at the distinguished branch. But this algebra is not local. Passing to a local order inside the same generic product forces the idempotent to acquire a denominator and creates a nonzero congruence module. Locality is the source of the contact.

### 12.2 Tangential branches

For $m\ge1$, put

$$
A_m=\mathcal O[X]/(X(X-\varpi^m)),
\qquad \lambda(X)=0.
$$

The two generic points are separated by $\varpi^m$. Direct computation gives

$$
\Phi_{A_m}\simeq\mathcal O/(\varpi^m),
\qquad
\eta_{A_m}=(\varpi^m),
\qquad
\Psi_{A_m}\simeq\mathcal O/(\varpi^m).
$$

The normalization is $\mathcal O^2$, and

$$
A_m=\{(u,v):u\equiv v\pmod{\varpi^m}\}.
$$

The quotient $\mathcal O^2/A_m$ has length $m$ and is already concentrated in the contact involving the distinguished branch. Hence in this two-branch example it agrees with the congruence module. For three or more branches, the full normalization quotient is larger and this agreement generally fails.

If $m=0$, the polynomial is $X(X-1)$ and the algebra is the product $\mathcal O^2$, not local. Both numerical modules vanish at either factor. Thus positive congruence length and locality meet at exactly the condition that the two roots coincide modulo the maximal ideal.

### 12.3 A nonreduced special fiber

Although $A_m$ has reduced generic fiber, its special fiber is

$$
A_m/\varpi A_m\simeq k[X]/(X^2).
$$

It is nonreduced for every $m\ge1$. This is not a defect in the hypotheses. The nilpotent special-fiber direction is precisely the shadow of two generic branches becoming congruent. Finite flatness permits nonreduced special fibers; it forbids $\varpi$-torsion in the total algebra.

The integer $m$ is invisible in the special fiber, since all $A_m/\varpi A_m$ are isomorphic. It is also invisible in the dimension of the relative tangent space, which is one. It survives in the integral length

$$
\operatorname{length}\Phi_{A_m}=m.
$$

This example explains why a criterion based only on residue-field dimensions would be too coarse.

One can separate nonreduced special fiber from nonreduced generic fiber. For

$$
B=\mathcal O[X]/(X^2),
$$

the element $X$ remains nilpotent after inverting $\varpi$. The augmentation is not generically isolated,

$$
\Phi_B\simeq\mathcal O,\qquad \eta_B=0,
$$

and neither relevant length is finite. The numerical theory includes $A_m$ and excludes $B$ for a conceptual reason.

### 12.4 A strict non-complete-intersection example

Let

$$
A=\mathcal O[X,Y]/
(X^2-\varpi X,XY,Y^2-\varpi Y)
$$

with augmentation $X,Y\mapsto0$. The basis $1,X,Y$ shows that $A$ is finite free of rank three. Its generic fiber is $K^3$, and its image there consists integrally of triples congruent modulo $\varpi$.

The cotangent presentation is the reduction of the three-by-two Jacobian matrix at the augmentation:

$$
\begin{pmatrix}
-\varpi&0\\
0&0\\
0&-\varpi
\end{pmatrix}.
$$

Thus

$$
\Phi_A\simeq k^2,
\qquad
\operatorname{Fitt}^0(\Phi_A)=(\varpi^2).
$$

The maximal minors are $0,\varpi^2,0$, confirming the Fitting ideal. On the other hand, the least multiple of $(1,0,0)$ lying in the order is $\varpi(1,0,0)$, so

$$
\eta_A=(\varpi),\qquad \Psi_A\simeq k.
$$

The intrinsic defect is

$$
D_A=(\varpi)/(\varpi^2)\simeq k.
$$

To verify non-complete-intersection structure without appealing only to the inequality, work in the regular local ring $S=\mathcal O[[X,Y]]$. The kernel has height two because the quotient has dimension one, but its image modulo the maximal ideal times the kernel requires three generators. Hence it cannot be generated by a regular sequence of length two. The strict numerical inequality detects exactly this surplus.

### 12.5 A quotient comparison

Let $a,b\in(\varpi)$ be nonzero and set

$$
R=\mathcal O[[X,Y]]/(X(X-a),Y(Y-b)),
$$

augmented at $(0,0)$. Quotienting by $Y$ gives

$$
T=\mathcal O[X]/(X(X-a)).
$$

Both rings are finite flat complete intersections, and the map is compatible and surjective. Their invariants are

$$
\begin{aligned}
\Phi_R&\simeq\mathcal O/(a)\oplus\mathcal O/(b),
&\eta_R&=(ab),\\
\Phi_T&\simeq\mathcal O/(a),
&\eta_T&=(a).
\end{aligned}
$$

The visible kernel module and branch defect are

$$
C_f\simeq\mathcal O/(b),
\qquad
B_f=(a)/(ab),
$$

and both have length $v(b)$. Since $D_T=0$, the defect length identity reduces to

$$
\operatorname{length}B_f=\operatorname{length}C_f.
$$

The numerical isomorphism hypothesis fails by exactly $v(b)$:

$$
\operatorname{length}\Phi_R
=v(a)+v(b)>v(a)
=\operatorname{length}\Psi_T.
$$

This is how a proper quotient should announce itself numerically.

## 13. Why every hypothesis matters

### 13.1 Without surjectivity

Let $T=A_m$ and map $R=\mathcal O$ into $T$ by the structural inclusion. The augmentations are compatible, $R$ is a complete intersection, and $T$ is finite flat with isolated generic point. Moreover

$$
\operatorname{length}\Phi_R=0
\le m=
\operatorname{length}\Psi_T.
$$

Yet $R\to T$ is not an isomorphism. There is no contradiction: the map is not surjective. Numerical control at a point cannot prove that the target is generated by the image of the source.

It is not enough to know that the map becomes surjective after reducing modulo $\varpi$ unless finiteness and a suitable Nakayama argument are also provided. The theorem begins after surjectivity has been established.

### 13.2 Without finite flatness

Take

$$
R=\mathcal O[X]/(X(X-\varpi)),
\qquad
T=R/(\varpi X)
\simeq\mathcal O[X]/(\varpi X,X^2),
$$

with $X\mapsto0$. The source is finite flat and a hypersurface; the target is finite but has $\varpi$-torsion. We compute

$$
\Phi_R\simeq k,
\qquad
\Phi_T\simeq k,
\qquad
\eta_T=(\varpi),
\qquad
\Psi_T\simeq k.
$$

Thus the numerical equality required by the criterion holds, but $R\to T$ has the nonzero kernel generated by $\varpi X=X^2$. The generic fiber of $T$ is merely $K$, so it has forgotten the vertical embedded direction. Flatness is exactly what prevents this loss.

The example also shows why “finite” cannot be substituted for “finite flat.” Over a DVR the missing adjective is equivalent to the absence of coefficient torsion.

### 13.3 Without compatible augmentations

Fix $N\ge2$ and let

$$
R=\mathcal O[X]/(X(X-\varpi^N)(X-\varpi)),
\qquad
T=\mathcal O[X]/(X(X-\varpi^N)).
$$

There is a natural surjection $R\twoheadrightarrow T$. Give $R$ the augmentation $X\mapsto\varpi$, but give $T$ the augmentation $X\mapsto0$. These augmentations select different generic branches and are not compatible.

At the selected point of $R$,

$$
f'(\varpi)=\varpi(\varpi-\varpi^N),
$$

which has valuation two. At the selected point of $T$, the congruence length is $N$. Hence

$$
\operatorname{length}\Phi_R=2
\le N=
\operatorname{length}\Psi_T,
$$

but the map is plainly not an isomorphism. The inequality compares the tangency of the branch $X=\varpi$ in the source with the branch $X=0$ in the target. They are unrelated measurements. Compatibility is what makes $J\subseteq I_R$ and creates the conormal sequence.

### 13.4 The source condition that is not needed

A complete-intersection hypothesis on the source is not among the hypotheses of the Wiles--Lenstra theorem. The classical shorter proof assumes such a presentation, but the refinement derives it. What replaces the assumption is not another structural condition on $R$; it is the combination of finite cotangent length, a finite flat target, and the sharp numerical inequality.

For comparison, let

$$
R=\mathcal O[[X]]/(\varpi X,X^3)
\twoheadrightarrow
T=\mathcal O[[X]]/(\varpi X,X^2).
$$

The kernel is generated by $X^2$, and

$$
\Phi_R\simeq k\simeq\Phi_T,
\qquad
\Psi_T\simeq k.
$$

Thus a bare tangent equality does not kill a kernel in $I_R^2$. This example does not contradict the refined theorem because $T$ has $\varpi$-torsion. It shows why target flatness, rather than source complete-intersection structure, is the indispensable hypothesis. Once $T$ is finite flat, intrinsic equality makes $T$ a complete intersection and the relation-lattice argument of Chapter 8 eliminates the hidden kernel.

The distinction is useful in practice. If a square complete-intersection presentation of $R$ has already been proved, the classical Wiles form is shorter to apply. If it has not, one should use the refined theorem and record source finite flatness and complete-intersection structure as conclusions, not assumptions.

### 13.5 Without generic isolation

Let

$$
A=\mathcal O[X]/(X^2),
\qquad \lambda(X)=0.
$$

This algebra is finite flat, local, and a hypersurface. Nevertheless the distinguished generic point is nonreduced rather than étale. One finds

$$
\Phi_A\simeq\mathcal O,
\qquad
\eta_A=0.
$$

Neither $\Phi_A$ nor $\Psi_A=\mathcal O$ has finite length. There is no finite inequality to compare. The Jacobian determinant is zero, accurately recording failure of isolation.

One should not assign infinity informally and continue manipulating differences such as $\infty-\infty$. The criterion applies only after finiteness of the cotangent module, or equivalently isolation of the selected generic factor, has been proved.

## 14. A reusable numerical package

### 14.1 The augmented-algebra lemma

The first reusable statement concerns a single ring.

**Lemma (augmented algebra).** Let $A$ be a finite flat complete local $\mathcal O$-algebra with augmentation $\lambda$, and suppose $\Phi_A=I_A/I_A^2$ has finite length. Then:

1. $\eta_A=\lambda(\operatorname{Ann}_A I_A)$ is a nonzero ideal;
2. $\operatorname{Fitt}^0_{\mathcal O}(\Phi_A)\subseteq\eta_A$;
3. $\operatorname{length}\Phi_A\ge\operatorname{length}(\mathcal O/\eta_A)$; and
4. equality holds if and only if $A$ is a complete intersection over $\mathcal O$.

In the equality case, $A$ is Gorenstein and the two ideals in part 2 are equal.

This is the intrinsic theorem traditionally associated with Lenstra's refinement of the numerical method. Its value is that complete-intersection structure is a conclusion once finite flatness and numerical equality are already available.

### 14.2 The surjective comparison lemma

**Lemma (surjective numerical comparison).** Let $R\twoheadrightarrow T$ be a compatible surjection of augmented complete Noetherian local $\mathcal O$-algebras. Assume $T$ is finite flat, $\Phi_R$ has finite length, and

$$
\operatorname{length}\Phi_R
\leq
\operatorname{length}\Psi_T.
$$

Then $R\simeq T$, and both are finite flat complete intersections.

**Proof.** This is an immediate special case of the Wiles--Lenstra theorem of Chapter 8. $\square$

In particular, the lemma does not assume finite flatness, generic isolation, or complete-intersection structure for $R$. The numerical inequality and the finite cotangent hypothesis supply all three source properties after the isomorphism is proved.

### 14.3 The self-dual-module lemma

**Lemma (module-supplied congruence number).** Let $T$ be a finite flat augmented local $\mathcal O$-algebra acting faithfully on a finite free $\mathcal O$-module $M$. Assume:

1. $M$ has a perfect pairing making the $T$-action self-adjoint;
2. the distinguished generic eigenspace has rank one;
3. the complementary generic summand is its orthogonal complement; and
4. with $P_\lambda=e_\lambda M$, the integral branch lattices satisfy

   $$
   M_\lambda=\eta_TP_\lambda.
   $$

Then

$$
\operatorname{Fitt}_{\mathcal O}^0
\left(M/(M_\lambda+M^c)\right)=\eta_T.
$$

Consequently a compatible surjection $R\twoheadrightarrow T$ satisfying the hypotheses of the surjective comparison lemma is an isomorphism as soon as

$$
\operatorname{length}\Phi_R
\leq
\operatorname{length}
\left(M/(M_\lambda+M^c)\right).
$$

**Proof.** Projection gives

$$
M/(M_\lambda+M^c)\simeq P_\lambda/M_\lambda.
$$

By part 4 this is $P_\lambda/\eta_TP_\lambda$, and $P_\lambda$ has rank one. Its zeroth Fitting ideal is therefore $\eta_T$. $\square$

The lemma deliberately displays faithfulness, rank, and saturation. The perfect pairing identifies $P_\lambda$ with the dual of $M_\lambda$ and makes the quotient computable, but it does not by itself identify the module congruence ideal with the ring congruence ideal.

### 14.4 The base-change lemma

**Lemma (coefficient extension).** Let $\mathcal O'/\mathcal O$ be a finite extension of complete DVRs of ramification index $e$. Under finite flat base change and localization at the extended augmentation,

$$
\Phi_{A'}\simeq\Phi_A\otimes\mathcal O',
\qquad
\eta_{A'}=\eta_A\mathcal O',
\qquad
D_{A'}\simeq D_A\otimes\mathcal O'.
$$

In particular,

$$
\operatorname{length}_{\mathcal O'}\Phi_{A'}
=e\operatorname{length}_{\mathcal O}\Phi_A,
\qquad
\operatorname{length}_{\mathcal O'}\Psi_{A'}
=e\operatorname{length}_{\mathcal O}\Psi_A.
$$

The fundamental inequality, its equality case, and the numerical isomorphism criterion are invariant under such extension. Faithful flatness also permits descent of isomorphism and complete-intersection structure.

### 14.5 A disciplined verification protocol

The reusable lemmas are short because their hypotheses carry the real work. A reliable verification proceeds in the following order.

1. Fix the complete DVR, its normalized valuation, and the augmentation on every ring.
2. Prove that the comparison map is a surjective local $\mathcal O$-homomorphism and that augmentations commute with it.
3. Establish finite flatness, or finite torsion-freeness, for every ring to which an intrinsic numerical theorem will be applied.
4. Prove that the selected generic point is isolated; equivalently, prove that the relative cotangent module has finite length.
5. Compute $\Phi$ from the augmentation ideal or an evaluated Jacobian, keeping it relative to $\mathcal O$.
6. Compute $\eta$ from $\lambda(\operatorname{Ann} I)$, from the branch idempotent lattice, or from a self-dual module with the rank-one saturation hypotheses.
7. Translate ideal inclusions to length inequalities with the direction reversed.
8. Apply the intrinsic inequality before inserting any external upper bound.
9. Distinguish the conclusions “target is a complete intersection” and “the map is an isomorphism.”
10. Under coefficient extension, multiply both lengths by the ramification index measured in the new DVR.

This order catches the most common errors: using an absolute cotangent space, calling $\eta$ a module, replacing a Fitting ideal by an annihilator, forgetting flatness, or claiming that first-order vanishing alone kills a kernel.

### 14.6 Conclusion

The numerical method compresses a remarkable amount of local algebra into two finite modules. The cotangent module

$$
\Phi_A=I_A/I_A^2
$$

measures how long infinitesimal motion persists along the distinguished integral point. The congruence module

$$
\Psi_A=\mathcal O/\lambda(\operatorname{Ann}_A I_A)
$$

measures how many powers of the uniformizer are needed to make the generic branch idempotent integral. Their universal relation is

$$
\operatorname{length}\Phi_A
\geq
\operatorname{length}\Psi_A,
$$

and the excess is the complete-intersection defect.

For a compatible surjection $R\twoheadrightarrow T$, an estimate in the opposite direction closes a chain of inequalities. Conormal exactness removes the visible kernel, the determinant-defect theorem makes the target a complete intersection, and equality of the source and target relation lattices makes the change-of-generators matrix a unit. The source is therefore identified with the target before finite flatness or complete-intersection structure is claimed for it.

The final lesson is not merely that two lengths happen to agree. It is that infinitesimal tangency, integral branch separation, duality, and regular sequences are four views of one determinant. When the determinant loses no valuation between source and target, there is no algebraic room for a proper quotient. That is the durable numerical mechanism behind $R=T$.
