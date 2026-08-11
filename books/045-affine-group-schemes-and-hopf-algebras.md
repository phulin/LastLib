# Affine Group Schemes and Hopf Algebras

## Contents

1. [Groups whose elements vary with the ring](#1-groups-whose-elements-vary-with-the-ring)
   - [Why a group should be a geometric object](#11-why-a-group-should-be-a-geometric-object)
   - [The functor of points and its variance](#12-the-functor-of-points-and-its-variance)
   - [Elementary Yoneda reasoning](#13-elementary-yoneda-reasoning)
   - [Affine group schemes](#14-affine-group-schemes)
2. [Commutative Hopf algebras](#2-commutative-hopf-algebras)
   - [The coalgebra identities](#21-the-coalgebra-identities)
   - [Antipodes and convolution](#22-antipodes-and-convolution)
   - [Complete translation of the group axioms](#23-complete-translation-of-the-group-axioms)
   - [Further antipode identities](#24-further-antipode-identities)
3. [Morphisms, products, and base change](#3-morphisms-products-and-base-change)
   - [Hopf morphisms and arrow reversal](#31-hopf-morphisms-and-arrow-reversal)
   - [Products and fiber products](#32-products-and-fiber-products)
   - [Arbitrary base change](#33-arbitrary-base-change)
   - [Restriction to fibers and descent warnings](#34-restriction-to-fibers-and-descent-warnings)
4. [Standard affine group schemes](#4-standard-affine-group-schemes)
   - [The additive and multiplicative groups](#41-the-additive-and-multiplicative-groups)
   - [Roots of unity and infinitesimal additive groups](#42-roots-of-unity-and-infinitesimal-additive-groups)
   - [Constant finite groups](#43-constant-finite-groups)
   - [Diagonalizable groups](#44-diagonalizable-groups)
   - [Matrix groups as a coordinate calculation](#45-matrix-groups-as-a-coordinate-calculation)
5. [Closed subgroup schemes and Hopf ideals](#5-closed-subgroup-schemes-and-hopf-ideals)
   - [Why equations must respect the group law](#51-why-equations-must-respect-the-group-law)
   - [Coordinate checks in basic examples](#52-coordinate-checks-in-basic-examples)
   - [Intersections, products, and generated subgroup closures](#53-intersections-products-and-generated-subgroup-closures)
   - [Base change of closed subgroups](#54-base-change-of-closed-subgroups)
6. [Kernels, equalizers, and schematic images](#6-kernels-equalizers-and-schematic-images)
   - [Kernels are always representable in the affine setting](#61-kernels-are-always-representable-in-the-affine-setting)
   - [Equalizers and fixed loci](#62-equalizers-and-fixed-loci)
   - [When a kernel remains finite locally free](#63-when-a-kernel-remains-finite-locally-free)
   - [Schematic images and their limits](#64-schematic-images-and-their-limits)
   - [Geometric images are not enough](#65-geometric-images-are-not-enough)
7. [Normal subgroup schemes and conjugation](#7-normal-subgroup-schemes-and-conjugation)
   - [Conjugation as a morphism](#71-conjugation-as-a-morphism)
   - [The coaction criterion for normality](#72-the-coaction-criterion-for-normality)
   - [Normality after base change and descent](#73-normality-after-base-change-and-descent)
8. [Actions, invariants, and torsors](#8-actions-invariants-and-torsors)
   - [Actions and coactions](#81-actions-and-coactions)
   - [Invariants and coinvariants](#82-invariants-and-coinvariants)
   - [Torsors and the canonical map](#83-torsors-and-the-canonical-map)
   - [Descent along a torsor](#84-descent-along-a-torsor)
9. [Quotients under exact hypotheses](#9-quotients-under-exact-hypotheses)
   - [Three different quotient questions](#91-three-different-quotient-questions)
   - [An affine quotient criterion](#92-an-affine-quotient-criterion)
   - [Faithfully flat Hopf subalgebras](#93-faithfully-flat-hopf-subalgebras)
   - [Quotients by finite locally free subgroups](#94-quotients-by-finite-locally-free-subgroups)
   - [Quotient coordinates in examples](#95-quotient-coordinates-in-examples)
10. [Exact sequences of affine group schemes](#10-exact-sequences-of-affine-group-schemes)
    - [Pointwise exactness is not the right default](#101-pointwise-exactness-is-not-the-right-default)
    - [An exactness criterion in Hopf algebras](#102-an-exactness-criterion-in-hopf-algebras)
    - [Failure of surjectivity on rational points](#103-failure-of-surjectivity-on-rational-points)
    - [Exactness and base change](#104-exactness-and-base-change)
11. [Commutative group schemes and cocommutativity](#11-commutative-group-schemes-and-cocommutativity)
    - [The tensor flip](#111-the-tensor-flip)
    - [Consequences for subgroups and quotients](#112-consequences-for-subgroups-and-quotients)
    - [Multiplication by an integer](#113-multiplication-by-an-integer)
12. [The identity, cotangent space, and Lie algebra](#12-the-identity-cotangent-space-and-lie-algebra)
    - [Why the augmentation ideal matters](#121-why-the-augmentation-ideal-matters)
    - [Dual-number points](#122-dual-number-points)
    - [Calculations for the basic groups](#123-calculations-for-the-basic-groups)
    - [Lie algebra and commutators](#124-lie-algebra-and-commutators)
13. [Finite locally free group schemes](#13-finite-locally-free-group-schemes)
    - [Hopf algebras finite projective over the base](#131-hopf-algebras-finite-projective-over-the-base)
    - [Translation and uniformity of fibers](#132-translation-and-uniformity-of-fibers)
    - [Closed subgroups and rank](#133-closed-subgroups-and-rank)
    - [Products, kernels, and exact sequences](#134-products-kernels-and-exact-sequences)
    - [Base change and fiberwise traps](#135-base-change-and-fiberwise-traps)
14. [Connected, reduced, and nonreduced behavior](#14-connected-reduced-and-nonreduced-behavior)
    - [Identity components over a field](#141-identity-components-over-a-field)
    - [Reduced finite group schemes over perfect fields](#142-reduced-finite-group-schemes-over-perfect-fields)
    - [Characteristic-$p$ contrasts](#143-characteristic-p-contrasts)
    - [Frobenius and its kernel](#144-frobenius-and-its-kernel)
15. [Coordinate methods for subgroup schemes](#15-coordinate-methods-for-subgroup-schemes)
    - [Kernels of characters](#151-kernels-of-characters)
    - [Subgroups of additive groups](#152-subgroups-of-additive-groups)
    - [Matrix equations and stabilizers](#153-matrix-equations-and-stabilizers)
    - [Scheme-theoretic closure over a DVR](#154-scheme-theoretic-closure-over-a-dvr)
16. [The translation dictionary for torsion subgroup schemes](#16-the-translation-dictionary-for-torsion-subgroup-schemes)
    - [The basic dictionary](#161-the-basic-dictionary)
    - [The exactness checklist](#162-the-exactness-checklist)
    - [Constructing torsion](#163-constructing-torsion)
    - [What geometric fibers can and cannot prove](#164-what-geometric-fibers-can-and-cannot-prove)
    - [A working protocol](#165-a-working-protocol)
17. [The augmentation filtration](#17-the-augmentation-filtration)
    - [Why first order is not enough](#171-why-first-order-is-not-enough)
    - [Coproduct estimates for powers of the augmentation ideal](#172-coproduct-estimates-for-powers-of-the-augmentation-ideal)
    - [The associated graded algebra](#173-the-associated-graded-algebra)
    - [Completion at the identity](#174-completion-at-the-identity)
    - [Calculations in the standard examples](#175-calculations-in-the-standard-examples)
18. [Distributions supported at the identity](#18-distributions-supported-at-the-identity)
    - [Finite-order functionals](#181-finite-order-functionals)
    - [Convolution and the order filtration](#182-convolution-and-the-order-filtration)
    - [Order one and the Lie bracket](#183-order-one-and-the-lie-bracket)
    - [Finite group schemes and the local factor at the identity](#184-finite-group-schemes-and-the-local-factor-at-the-identity)
    - [Base change and finiteness hypotheses](#185-base-change-and-finiteness-hypotheses)
19. [Representations and comodules](#19-representations-and-comodules)
    - [Why representations become coactions](#191-why-representations-become-coactions)
    - [Matrix coefficients](#192-matrix-coefficients)
    - [Invariant vectors and equivariant maps](#193-invariant-vectors-and-equivariant-maps)
    - [Constant and diagonalizable groups](#194-constant-and-diagonalizable-groups)
    - [Additive and multiplicative one-parameter actions](#195-additive-and-multiplicative-one-parameter-actions)
20. [Torsors as descent objects](#20-torsors-as-descent-objects)
    - [Trivial torsors and local triviality](#201-trivial-torsors-and-local-triviality)
    - [Cocycles from a chosen cover](#202-cocycles-from-a-chosen-cover)
    - [The affine descent calculation](#203-the-affine-descent-calculation)
    - [Kummer and Artin--Schreier torsors](#204-kummer-and-artin--schreier-torsors)
    - [Twisting and forms](#205-twisting-and-forms)
21. [Representable quotients and the boundary of the theory](#21-representable-quotients-and-the-boundary-of-the-theory)
    - [Universal properties before coordinates](#211-universal-properties-before-coordinates)
    - [Normality and descended multiplication](#212-normality-and-descended-multiplication)
    - [Images, closures, and purity](#213-images-closures-and-purity)
    - [A base-change ledger](#214-a-base-change-ledger)
    - [Failure patterns](#215-failure-patterns)
22. [Extended calculations and structural examples](#22-extended-calculations-and-structural-examples)
    - [Constant groups and locally constant points](#221-constant-groups-and-locally-constant-points)
    - [Diagonalizable groups and character lattices](#222-diagonalizable-groups-and-character-lattices)
    - [Additive polynomials and their kernels](#223-additive-polynomials-and-their-kernels)
    - [Multiplicative isogenies](#224-multiplicative-isogenies)
    - [Semidirect products and noncommutativity](#225-semidirect-products-and-noncommutativity)
23. [The affine group-scheme theorem](#23-the-affine-group-scheme-theorem)
    - [Statement](#231-statement)
    - [Proof architecture](#232-proof-architecture)
    - [Consequences for finite locally free groups](#233-consequences-for-finite-locally-free-groups)
    - [The final checklist](#234-the-final-checklist)
    - [Conclusion](#235-conclusion)

## 1. Groups whose elements vary with the ring

### 1.1 Why a group should be a geometric object

Many groups in arithmetic are defined by polynomial equations. The additive group is the affine line with addition, the multiplicative group is the punctured affine line with multiplication, and a matrix group is cut out by polynomial relations among matrix entries. Over a field one might study only the solutions in that field. That loses two essential kinds of information. Solutions over extension rings reveal descent and families, while solutions over rings with nilpotents reveal infinitesimal directions. Both become indispensable for torsion in characteristic dividing its order.

Fix a commutative ring $R$ and put $S=\operatorname{Spec}R$. An **$S$-scheme** is a scheme equipped with a morphism to $S$. Products in this category are fiber products over $S$; thus $X\times_S Y$ means that both coordinates lie over the same point of the base. A **group scheme over $S$** is an $S$-scheme $G$ together with morphisms

$$
m:G\times_SG\longrightarrow G,\qquad
e:S\longrightarrow G,\qquad
i:G\longrightarrow G
$$

called multiplication, identity, and inverse, satisfying the usual diagrams. Associativity says

$$
m\circ(m\times\operatorname{id})
=m\circ(\operatorname{id}\times m):G\times_SG\times_SG\longrightarrow G.
$$

The identity equations are

$$
m\circ(e\times\operatorname{id})=\operatorname{id}
=m\circ(\operatorname{id}\times e),
$$

after the canonical identifications $S\times_SG\simeq G\simeq G\times_SS$. The inverse equations are

$$
m\circ(i,\operatorname{id})=e\circ p
=m\circ(\operatorname{id},i),
$$

where $p:G\to S$ is the structure morphism. These are equalities of morphisms, not merely equalities on points over one field.

This definition solves a representability problem. It packages a group law that works uniformly after every change of base. The next section makes that statement precise and gives a practical way to reason without repeatedly drawing diagrams.

### 1.2 The functor of points and its variance

For an $S$-scheme $X$, define its functor of points on $S$-schemes by

$$
h_X(T)=\operatorname{Hom}_S(T,X).
$$

A morphism $u:T'\to T$ induces

$$
h_X(T)\longrightarrow h_X(T'),\qquad x\longmapsto x\circ u.
$$

Thus $h_X$ is contravariant in the test scheme. A morphism $f:X\to Y$, on the other hand, gives a natural transformation $h_X\to h_Y$ by postcomposition. The two variances must not be conflated.

When $S=\operatorname{Spec}R$ and $X=\operatorname{Spec}A$ is affine, it is often more convenient to use $R$-algebras as test objects. For an $R$-algebra $C$ set

$$
X(C)=\operatorname{Hom}_{R\text{-alg}}(A,C).
$$

A homomorphism $C\to C'$ sends an $A$-point $x:A\to C$ to the composite $A\to C\to C'$. Hence $X(C)$ is covariant in the test algebra. This is the same functor as $h_X$ on affine test schemes because

$$
\operatorname{Hom}_S(\operatorname{Spec}C,\operatorname{Spec}A)
\cong\operatorname{Hom}_{R\text{-alg}}(A,C).
$$

The apparent change from contravariance to covariance comes from applying the already contravariant spectrum construction to the test ring.

If $G$ is a group scheme, then $G(T)$ is a group for every $T$: multiply two maps $x,y:T\to G$ using the diagonal $T\to T\times_ST$ followed by $x\times y$ and $m$. Every pullback map $G(T)\to G(T')$ is a group homomorphism. In affine-ring notation, each $G(C)$ is a group functorially in $C$.

### 1.3 Elementary Yoneda reasoning

The fundamental observation is that a geometric morphism is determined by what it does to all points.

**Theorem 1.1 (Yoneda principle).** For $S$-schemes $X$ and $Y$, the map

$$
\operatorname{Hom}_S(X,Y)\longrightarrow
\operatorname{Nat}(h_X,h_Y),\qquad f\longmapsto(x\mapsto f\circ x)
$$

is a bijection.

**Proof.** Injectivity follows by evaluating a natural transformation at the test scheme $X$ and the point $\operatorname{id}_X$: the image is $f$. Conversely, let $\eta:h_X\to h_Y$ be natural and put $f=\eta_X(\operatorname{id}_X)$. For any $x:T\to X$, naturality for $x$ gives

$$
\eta_T(x)=\eta_T(\operatorname{id}_X\circ x)
=\eta_X(\operatorname{id}_X)\circ x=f\circ x.
$$

Thus $\eta$ is induced by $f$, uniquely. $\square$

Consequently, giving a group scheme structure on $G$ is equivalent to making every $G(T)$ a group naturally in $T$. The qualification “naturally” is decisive. An accidental group structure on $G(S)$ alone need not extend to any geometric multiplication. To verify an identity between morphisms, it suffices to verify the induced identity on $T$-points for every test scheme $T$; for affine schemes, affine tests suffice.

There is an especially explicit affine form. If $X=\operatorname{Spec}A$, the identity point in $X(A)$ is the identity map $A\to A$. A natural rule $X(C)\to Y(C)$ is determined by its value at that universal point. This is often all that is hiding behind a “Yoneda argument.”

### 1.4 Affine group schemes

An **affine group scheme over $R$** is a group scheme $G\to\operatorname{Spec}R$ whose underlying scheme is affine. Write

$$
G=\operatorname{Spec}A,\qquad A=\mathcal O(G).
$$

The fiber product $G\times_SG$ has coordinate ring $A\otimes_RA$. Therefore multiplication, identity, and inverse correspond contravariantly to maps

$$
\Delta:A\longrightarrow A\otimes_RA,\qquad
\varepsilon:A\longrightarrow R,\qquad
S:A\longrightarrow A.
$$

The direction is worth reading twice: geometric multiplication gives algebraic **comultiplication**. The identity section gives a map from functions on $G$ to functions on the base, and inversion gives an endomorphism of the coordinate ring. Chapter 2 translates every group axiom exactly.

Not every group scheme is affine, but the affine class is already broad enough for finite group schemes and for the torsion objects motivating this book. Affineness also lets every construction be checked by tensor products and quotients of rings.

## 2. Commutative Hopf algebras

### 2.1 The coalgebra identities

Let $A$ be a commutative $R$-algebra. An **$R$-bialgebra** structure on $A$ consists of $R$-algebra homomorphisms

$$
\Delta:A\to A\otimes_RA,\qquad \varepsilon:A\to R
$$

such that

$$
(\Delta\otimes\operatorname{id})\Delta
=(\operatorname{id}\otimes\Delta)\Delta
$$

and

$$
(\varepsilon\otimes\operatorname{id})\Delta=\operatorname{id}
=(\operatorname{id}\otimes\varepsilon)\Delta.
$$

Here we use the canonical identifications $R\otimes_RA\simeq A\simeq A\otimes_RR$. The first equation is coassociativity; the other two are the counit equations. They are precisely the pullbacks of associativity and the two identity laws.

Sweedler notation suppresses summation signs:

$$
\Delta(a)=\sum a_{(1)}\otimes a_{(2)}.
$$

Then coassociativity says that the two meanings of

$$
\sum a_{(1)}\otimes a_{(2)}\otimes a_{(3)}
$$

agree, and the counit equations say

$$
\sum\varepsilon(a_{(1)})a_{(2)}=a
=\sum a_{(1)}\varepsilon(a_{(2)}).
$$

The indices are placeholders, not individually defined components. One may manipulate them only through the structural identities.

Because $\Delta$ and $\varepsilon$ are algebra homomorphisms,

$$
\Delta(ab)=\Delta(a)\Delta(b),\quad \Delta(1)=1\otimes1,
\qquad \varepsilon(ab)=\varepsilon(a)\varepsilon(b).
$$

This compatibility is what makes multiplication on points preserve the equations defining the scheme.

### 2.2 Antipodes and convolution

For $R$-linear maps $f,g:A\to A$, define their **convolution product** by

$$
f*g=m_A\circ(f\otimes g)\circ\Delta,
$$

so that

$$
(f*g)(a)=\sum f(a_{(1)})g(a_{(2)}).
$$

Coassociativity and associativity of $A$ make convolution associative. Its identity is $u\varepsilon$, where $u:R\to A$ is the unit map. An **antipode** is a convolution inverse of $\operatorname{id}_A$:

$$
S*\operatorname{id}_A=u\varepsilon
=\operatorname{id}_A*S.
$$

Equivalently,

$$
\sum S(a_{(1)})a_{(2)}=\varepsilon(a)1
=\sum a_{(1)}S(a_{(2)}).
$$

An $R$-bialgebra possessing an antipode is an **$R$-Hopf algebra**. In this book its underlying algebra is always commutative, because it is the coordinate algebra of an affine scheme. Commutativity of the *group* is a different condition and will correspond to cocommutativity of $\Delta$.

The convolution formulation gives uniqueness immediately: if $S$ and $T$ are both convolution inverses of the identity, then

$$
S=S*(\operatorname{id}*T)=(S*\operatorname{id})*T=T.
$$

Thus an antipode is structure, but never a choice once it exists.

### 2.3 Complete translation of the group axioms

**Theorem 2.1.** Affine group schemes over $R$ are contravariantly equivalent to commutative $R$-Hopf algebras.

**Proof strategy.** We translate the three structure maps and then reverse each diagram. Let $G=\operatorname{Spec}A$. The multiplication map gives $\Delta$, the identity gives $\varepsilon$, and inversion gives $S$. Since a composite of scheme maps pulls back functions in reverse order, the associativity diagram becomes coassociativity. The left and right identity diagrams become the two counit equations. Finally the maps

$$
G\xrightarrow{(i,\operatorname{id})}G\times_SG\xrightarrow{m}G
$$

and

$$
G\xrightarrow{p}S\xrightarrow{e}G
$$

pull back to $m_A(S\otimes\operatorname{id})\Delta$ and $u\varepsilon$ respectively. This gives one antipode identity; the other inverse diagram gives the other.

Conversely, reverse the construction. A Hopf algebra produces the three scheme maps, and the displayed algebra identities imply the group diagrams because spectrum is faithful on ring maps. These assignments are inverse on objects and morphisms. $\square$

On $C$-points, the group law has a useful formula. If $x,y:A\to C$, then

$$
(xy)(a)=m_C(x\otimes y)\Delta(a)
=\sum x(a_{(1)})y(a_{(2)}),
$$

the identity point is $u_C\varepsilon:A\to C$, and

$$
x^{-1}=x\circ S.
$$

These formulas both explain the Hopf identities and provide a reliable check on tensor-factor order.

### 2.4 Further antipode identities

For any Hopf algebra, the antipode reverses products and coproducts:

$$
S(ab)=S(b)S(a),\qquad S(1)=1,
$$

$$
\Delta(S(a))=\sum S(a_{(2)})\otimes S(a_{(1)}),\qquad
\varepsilon(S(a))=\varepsilon(a).
$$

In a commutative coordinate algebra the first identity simplifies to ordinary multiplicativity, so $S$ is an $R$-algebra endomorphism. The reversal of tensor factors remains meaningful for a noncommutative group scheme.

Here is the proof idea. Give $\operatorname{Hom}_R(A\otimes A,A)$ its convolution product using the tensor-product coalgebra. The multiplication map $m_A$ has convolution inverse $S\circ m_A$, while the map $(a,b)\mapsto S(b)S(a)$ is another inverse, obtained by inserting the two antipode equations in the opposite order. Uniqueness gives antimultiplicativity. The coproduct formula follows similarly by comparing two convolution inverses of $\Delta$ in $\operatorname{Hom}_R(A,A\otimes A)$, where the target multiplication is reversed in the appropriate tensor factor. Applying counits yields the last identity.

Geometrically these facts merely say that inversion reverses multiplication, $(gh)^{-1}=h^{-1}g^{-1}$, and fixes the identity. The algebraic proof shows they follow from the two inverse axioms rather than requiring extra assumptions.

## 3. Morphisms, products, and base change

### 3.1 Hopf morphisms and arrow reversal

A morphism of group schemes $f:G\to H$ is an $S$-morphism commuting with multiplication, identity, and inverse. If

$$
G=\operatorname{Spec}A,\qquad H=\operatorname{Spec}B,
$$

then it corresponds to an $R$-algebra map

$$
f^*:B\longrightarrow A.
$$

It is a **Hopf-algebra morphism** when

$$
\Delta_Af^*=(f^*\otimes f^*)\Delta_B,\qquad
\varepsilon_Af^*=\varepsilon_B,\qquad
S_Af^*=f^*S_B.
$$

The antipode condition follows from the first two: a bialgebra morphism carries the antipode to a convolution inverse, and uniqueness of antipodes applies. It is nevertheless useful to display all three compatibilities when checking formulas.

Closed immersions and dominant-looking maps reverse as usual. A closed subgroup inclusion $H\hookrightarrow G$ corresponds to a surjective map $\mathcal O(G)\twoheadrightarrow\mathcal O(H)$. A faithfully flat morphism $G\to Q$ corresponds to a faithfully flat inclusion $\mathcal O(Q)\to\mathcal O(G)$. Forgetting this reversal is the most common source of false quotient statements.

### 3.2 Products and fiber products

The product of two affine group schemes over $S$ has underlying scheme $G\times_SH$ and coordinate algebra

$$
\mathcal O(G\times_SH)=A\otimes_RB.
$$

Its Hopf structure is determined by

$$
\Delta(a\otimes b)
=\sum (a_{(1)}\otimes b_{(1)})\otimes(a_{(2)}\otimes b_{(2)}),
$$

where the middle tensor factors have been interchanged to identify

$$
(A\otimes B)\otimes(A\otimes B)
\cong A\otimes A\otimes B\otimes B.
$$

Also $\varepsilon(a\otimes b)=\varepsilon_A(a)\varepsilon_B(b)$ and $S(a\otimes b)=S_A(a)\otimes S_B(b)$.

More generally, given $G\to K\leftarrow H$, their fiber product is an affine group scheme. If the corresponding Hopf maps are

$$
C=\mathcal O(K)\longrightarrow A=\mathcal O(G),
\qquad C\longrightarrow B=\mathcal O(H),
$$

then

$$
\mathcal O(G\times_KH)=A\otimes_CB.
$$

The Hopf structure descends to the relative tensor product because both maps respect all structure operations. On points this is simply

$$
(G\times_KH)(T)=G(T)\times_{K(T)}H(T).
$$

Thus fiber products of representable group functors are representable without an additional hypothesis.

### 3.3 Arbitrary base change

For a ring map $R\to R'$, set

$$
A_{R'}=A\otimes_RR',\qquad G_{R'}=G\times_{\operatorname{Spec}R}\operatorname{Spec}R'.
$$

The base-changed Hopf structure is

$$
\Delta_{R'}=\Delta\otimes_RR',\qquad
\varepsilon_{R'}:A\otimes_RR'\to R',\quad a\otimes r'\mapsto\varepsilon(a)r',
$$

$$
S_{R'}=S\otimes_RR'.
$$

Under the canonical tensor reassociation, $\Delta_{R'}$ lands in

$$
(A\otimes_RR')\otimes_{R'}(A\otimes_RR').
$$

No flatness hypothesis on $R'$ is needed. Every Hopf identity is an equality of maps and remains true after tensoring. Products, fiber products, kernels defined as fiber products, and closed subgroups defined by base-change-stable quotients all commute with base change in the precise forms developed later.

If $A$ is finite projective over $R$, then $A_{R'}$ is finite projective of the same pulled-back rank. Thus a finite locally free group scheme remains finite locally free under every base change, including passage to a residue field or an algebraic closure.

### 3.4 Restriction to fibers and descent warnings

For $s\in\operatorname{Spec}R$, the fiber $G_s$ has Hopf algebra $A\otimes_R\kappa(s)$. A property expressed by an isomorphism of finite projective modules can often be tested after faithfully flat base change. A property expressed merely by the number of geometric points usually cannot detect nilpotents.

For example, a morphism of finite locally free group schemes may be an isomorphism if it becomes one after a faithfully flat base change: the kernel and cokernel of the coordinate-module map vanish by faithful flatness. By contrast, a morphism inducing bijections on geometric points need not be an isomorphism. In characteristic $p$, the map $\mu_p\to\operatorname{Spec}k$ has only one geometric point but its coordinate algebra has dimension $p$.

Base change also may create subgroup schemes or connected components not defined over the original base. A geometric-fiber calculation is evidence, not automatically descent data. To descend a subgroup from $R'$ one needs compatibility of its defining Hopf ideal under the two pullbacks to $R'\otimes_RR'$.

## 4. Standard affine group schemes

### 4.1 The additive and multiplicative groups

The **additive group** is

$$
\mathbf G_a=\operatorname{Spec}R[T]
$$

with

$$
\Delta(T)=T\otimes1+1\otimes T,\qquad
\varepsilon(T)=0,\qquad S(T)=-T.
$$

An $R$-algebra map $R[T]\to C$ is determined by the image of $T$, so $\mathbf G_a(C)=C$ and the point formula gives ordinary addition.

The **multiplicative group** is

$$
\mathbf G_m=\operatorname{Spec}R[T,T^{-1}]
$$

with

$$
\Delta(T)=T\otimes T,\qquad \varepsilon(T)=1,\qquad S(T)=T^{-1}.
$$

Thus $\mathbf G_m(C)=C^\times$. The coordinate $T$ is **group-like**: an element $g$ of a Hopf algebra is group-like if $\Delta(g)=g\otimes g$ and $\varepsilon(g)=1$. By contrast $T$ in $\mathcal O(\mathbf G_a)$ is **primitive**: $\Delta(T)=T\otimes1+1\otimes T$.

These examples explain why coproducts encode laws. Polynomial functions are evaluated at a product by pulling them back along multiplication: the additive coordinate becomes the sum of the two coordinates, while the multiplicative coordinate becomes their product.

### 4.2 Roots of unity and infinitesimal additive groups

For an integer $n\ge1$, the $n$th roots of unity form the kernel of $[n]:\mathbf G_m\to\mathbf G_m$, $z\mapsto z^n$:

$$
\mu_n=\operatorname{Spec}R[T,T^{-1}]/(T^n-1)
\cong\operatorname{Spec}R[T]/(T^n-1).
$$

The ideal is stable under the Hopf operations because

$$
\Delta(T^n-1)=T^n\otimes T^n-1\otimes1
=(T^n-1)\otimes T^n+1\otimes(T^n-1),
$$

$\varepsilon(T^n-1)=0$, and $S(T^n-1)=-T^{-n}(T^n-1)$. Its coordinate algebra is free over $R$ with basis $1,T,\ldots,T^{n-1}$, so $\mu_n$ is finite locally free of rank $n$ over every base.

If $k$ has characteristic $p$, then

$$
T^p-1=(T-1)^p.
$$

Thus $\mu_p$ has one geometric point and length $p$. Its nontriviality is entirely infinitesimal; counting points would erase it.

There is an additive analogue in characteristic $p$:

$$
\alpha_p=\ker(F:\mathbf G_a\to\mathbf G_a)
=\operatorname{Spec}k[T]/(T^p),
$$

where $F(x)=x^p$. The ideal $(T^p)$ is Hopf because

$$
\Delta(T^p)=T^p\otimes1+1\otimes T^p
$$

in characteristic $p$. Both $\alpha_p$ and $\mu_p$ have only the identity over every reduced algebraically closed extension field, but they are not isomorphic: their Hopf structures and their behavior in infinitesimal test rings differ.

### 4.3 Constant finite groups

Let $\Gamma$ be a finite abstract group. The **constant group scheme** $\underline\Gamma_R$ is the disjoint union of copies of $S$ indexed by $\Gamma$. Its coordinate algebra is

$$
R^\Gamma=\{f:\Gamma\to R\}
\cong\prod_{\gamma\in\Gamma}R.
$$

Writing $e_\gamma$ for the characteristic idempotent of $\gamma$, the Hopf structure is most transparently given on functions:

$$
(\Delta f)(\gamma,\delta)=f(\gamma\delta),\qquad
\varepsilon(f)=f(1),\qquad
(Sf)(\gamma)=f(\gamma^{-1}).
$$

Equivalently,

$$
\Delta(e_\eta)=\sum_{\gamma\delta=\eta}e_\gamma\otimes e_\delta.
$$

The scheme is finite locally free of rank $|\Gamma|$ and is a disjoint union of open-and-closed sections. For a connected $R$-algebra $C$, its $C$-points are just $\Gamma$; for a disconnected $C$, a point is a locally constant function from $\operatorname{Spec}C$ to $\Gamma$. Thus the slogan “constant points equal $\Gamma$” requires connected tests.

The coordinate algebra $R^\Gamma$ is commutative for every $\Gamma$, because the scheme is affine. Its comultiplication is cocommutative exactly when $\Gamma$ is abelian. This cleanly separates commutativity of functions from commutativity of the represented group.

### 4.4 Diagonalizable groups

Let $M$ be an abelian group. Its group algebra

$$
R[M]=\bigoplus_{m\in M}R\,X^m,\qquad X^mX^{m'}=X^{m+m'},
$$

is a commutative Hopf algebra with

$$
\Delta(X^m)=X^m\otimes X^m,\qquad
\varepsilon(X^m)=1,\qquad S(X^m)=X^{-m}.
$$

The affine group scheme

$$
D_R(M)=\operatorname{Spec}R[M]
$$

is **diagonalizable**. Its points satisfy

$$
D_R(M)(C)=\operatorname{Hom}_{\mathrm{Ab}}(M,C^\times),
$$

because an algebra map must send each $X^m$ to a unit and preserve addition in $M$ as multiplication in $C^\times$.

Examples include $D(\mathbb Z)=\mathbf G_m$ and $D(\mathbb Z/n\mathbb Z)=\mu_n$. If $M$ is finite, $R[M]$ is free of rank $|M|$, so $D(M)$ is finite locally free. A homomorphism $u:M\to N$ induces $R[M]\to R[N]$ and therefore a group-scheme map

$$
D(N)\longrightarrow D(M).
$$

Diagonalization reverses arrows. This contravariance will later be one half of the constant/diagonalizable duality picture.

### 4.5 Matrix groups as a coordinate calculation

The general linear group is represented by

$$
\mathrm{GL}_{n,R}=\operatorname{Spec}R[x_{ij},d^{-1}],
\qquad d=\det(x_{ij}).
$$

If $X=(x_{ij})$ is the universal matrix, multiplication gives

$$
\Delta(x_{ij})=\sum_kx_{ik}\otimes x_{kj},
$$

the identity gives $\varepsilon(x_{ij})=\delta_{ij}$, and inversion gives entries of $S(X)=X^{-1}$. The determinant is group-like: $\Delta(d)=d\otimes d$.

The special linear group is the closed subgroup defined by $d-1$. Upper triangular, diagonal, and unipotent matrix groups arise by imposing the expected coordinate equations. A proposed family of equations defines a subgroup scheme precisely when its ideal satisfies the Hopf stability conditions of Chapter 5; checking closure only over field-valued points is insufficient over nonreduced bases.

## 5. Closed subgroup schemes and Hopf ideals

### 5.1 Why equations must respect the group law

A closed subscheme of a group scheme is not automatically a subgroup. Its equations must remain true after multiplying or inverting points, and they must hold at the identity. This requirement has an exact algebraic form.

Let $A$ be a commutative Hopf algebra. An ideal $I\subseteq A$ is a **Hopf ideal** if

$$
\Delta(I)\subseteq I\otimes_RA+A\otimes_RI,
\qquad \varepsilon(I)=0,
\qquad S(I)\subseteq I.
$$

In the first condition, the displayed sum means its image inside $A\otimes_RA$. These conditions ensure that $A/I$ inherits maps

$$
\bar\Delta:A/I\to(A/I)\otimes_R(A/I),
\quad \bar\varepsilon:A/I\to R,
\quad \bar S:A/I\to A/I.
$$

Conversely, if the quotient map $A\to A/I$ is a Hopf morphism, all three inclusions hold. Therefore closed subgroup schemes $H\hookrightarrow G=\operatorname{Spec}A$ correspond exactly to Hopf ideals, with

$$
\mathcal O(H)=A/I.
$$

**Proof of the correspondence.** Let $q:A\to A/I$. The kernel of

$$
q\otimes q:A\otimes_RA\longrightarrow(A/I)\otimes_R(A/I)
$$

is exactly $I\otimes_RA+A\otimes_RI$, understood as the images of these tensor modules. One way to see this without a flatness assumption is to factor $q\otimes q$ as

$$
A\otimes A\longrightarrow(A/I)\otimes A
\longrightarrow(A/I)\otimes(A/I).
$$

Right exactness of tensor product identifies the first kernel with the image of $I\otimes A$ and the second, modulo that image, with the image of $(A/I)\otimes I$. Its inverse image is the stated sum. Hence $\Delta$ descends precisely when $\Delta(I)$ lies in that sum. The counit descends precisely when $I\subseteq\ker\varepsilon$, and the antipode descends precisely when $S(I)\subseteq I$.

The descended maps satisfy all Hopf identities because composing either side of an identity with the surjection $q$ gives the corresponding identity in $A$, and $q$ and its tensor powers are surjective. Conversely, if $A/I$ is the coordinate Hopf algebra of a closed subgroup and $q$ respects the structures, applying the quotient maps to $I$ gives the three conditions. $\square$

The counit and antipode conditions are genuinely needed. A coideal compatible with multiplication may define a submonoid containing no inverse, while an ideal stable under inversion but missing the identity cannot define a subgroup.

### 5.2 Coordinate checks in basic examples

Inside $\mathbf G_a$, the equation $aT=0$ defines a subgroup for every $a\in R$: indeed

$$
\Delta(aT)=aT\otimes1+1\otimes aT,
$$

and the counit and antipode conditions are immediate. The resulting subgroup need not be flat. For example, over a DVR with uniformizer $\pi$, the algebra $R[T]/(\pi T)$ is not finite, while adding $T^2=0$ may make it finite but still introduce $\pi$-torsion. Being a subgroup does not force finite local freeness.

Inside $\mathbf G_m$, the ideal $(T^n-1)$ is Hopf, giving $\mu_n$. The ideal $(T-a)$ defines a section, but it is a subgroup only when $a=1$: the counit sends $T-a$ to $1-a$. Thus a translate of a subgroup generally is not a subgroup.

Inside $\mathrm{GL}_n$, the determinant-one ideal is Hopf because

$$
\Delta(d-1)=(d-1)\otimes d+1\otimes(d-1),
$$

while $\varepsilon(d-1)=0$ and $S(d-1)=d^{-1}-1=-d^{-1}(d-1)$. Similarly, equations $x_{ij}=0$ below the diagonal define the upper triangular subgroup: the formula for $\Delta(x_{ij})$ shows that when $i>j$, every summand has either $i>k$ or $k>j$.

### 5.3 Intersections, products, and generated subgroup closures

If $H_1,H_2\hookrightarrow G$ have Hopf ideals $I_1,I_2$, their scheme-theoretic intersection is the fiber product $H_1\times_GH_2$ and has coordinate algebra

$$
A/(I_1+I_2).
$$

The sum of Hopf ideals is a Hopf ideal, so the intersection is a closed subgroup. Arbitrary scheme-theoretic intersections correspond to sums of ideals when the sum is formed in $A$; no finiteness is needed for the subgroup statement.

The product of two closed subgroup functors need not itself be represented by a closed subgroup without hypotheses. If $G$ is commutative, the multiplication map $H_1\times H_2\to G$ has pointwise image $H_1(T)H_2(T)$, but a functorial image need not be representable and its schematic closure need not commute with base change. Over a field and for affine group schemes of finite type, the scheme-theoretic image is a closed subgroup. Over a general base, one should instead construct a Hopf ideal or invoke a representability theorem with its flatness and finiteness hypotheses stated.

This warning also applies to the “subgroup generated by equations.” The largest Hopf ideal contained in a given ideal, when it exists as the evident sum of all contained Hopf ideals, defines the smallest closed subgroup containing the corresponding closed subscheme in the order-reversing sense. It need not describe the pointwise subgroup generated over every ring, and formation can behave poorly under base change.

### 5.4 Base change of closed subgroups

If $I$ is a Hopf ideal of $A$, then the image $I_{R'}$ of $I\otimes_RR'$ in $A\otimes_RR'$ is a Hopf ideal and

$$
(A/I)\otimes_RR'\cong(A\otimes_RR')/I_{R'}.
$$

Thus the base change $H_{R'}\hookrightarrow G_{R'}$ is the closed subgroup defined by the extended ideal. No flatness is required for this quotient identity.

Descent runs in the other direction. A Hopf ideal $J\subseteq A\otimes_RR'$ descends along a faithfully flat map only if its two pullbacks to $R'\otimes_RR'$ agree. Under that compatibility, faithful flat descent gives an ideal $I\subseteq A$, and the Hopf conditions descend because equality and inclusion of the relevant submodules are faithfully flat local.

## 6. Kernels, equalizers, and schematic images

### 6.1 Kernels are always representable in the affine setting

For a morphism $f:G\to H$, the kernel functor is

$$
(\ker f)(T)=\{g\in G(T):f(g)=1\}.
$$

It is the fiber product

$$
\ker f=G\times_{H,e_H}S.
$$

Hence it is representable whenever $G$ and $H$ are, and it is affine when they are affine. If $f^*:B\to A$ is the coordinate Hopf map and $B^+=\ker(\varepsilon_B)$ is the augmentation ideal, then

$$
\mathcal O(\ker f)=A\otimes_BR\cong A/Af^*(B^+).
$$

The ideal $Af^*(B^+)$ is a Hopf ideal. This formula is often the fastest route to a coordinate calculation.

For $[n]:\mathbf G_m\to\mathbf G_m$, the augmentation ideal of the target is $(T-1)$ and its pullback is $(T^n-1)$, recovering $\mu_n$. For Frobenius $F:\mathbf G_a\to\mathbf G_a$ in characteristic $p$, pullback sends $T$ to $T^p$, giving $\alpha_p$.

Kernels commute with arbitrary base change because fiber products do. Algebraically, tensoring $A/Af^*(B^+)$ with $R'$ gives the corresponding quotient for $f_{R'}$.

### 6.2 Equalizers and fixed loci

Given group morphisms $f,g:G\rightrightarrows H$, their equalizer is the fiber product of $(f,g):G\to H\times_SH$ with the diagonal $H\to H\times_SH$. It is a closed subgroup because affine group schemes are separated. In coordinates its ideal in $A=\mathcal O(G)$ is generated by

$$
f^*(b)-g^*(b),\qquad b\in B=\mathcal O(H).
$$

When $H$ is of finite type, finitely many algebra generators of $B$ suffice. Equalizers commute with arbitrary base change as fiber products, although a presentation by a chosen generating set may become nonminimal.

The fixed locus of an automorphism $\sigma:G\to G$ is the equalizer of $\sigma$ and the identity. It is therefore a closed subscheme. If $\sigma$ is a group automorphism, it is a closed subgroup. Fixed loci of general group actions are subtler: one must equalize the action and projection over the acting group, which leads naturally to invariants and stabilizers in Chapter 8.

### 6.3 When a kernel remains finite locally free

If $G$ is finite over $S$, then every closed subgroup, in particular every kernel, is finite. It need not be flat. The coordinate quotient

$$
A\twoheadrightarrow A/Af^*(B^+)
$$

may acquire base torsion even when $A$ and $B$ are finite projective over $R$.

A precise sufficient criterion is immediate from finite-algebra theory.

**Proposition 6.1.** Let $G$ be finite locally free over $S$, and let $K\hookrightarrow G$ be a closed subgroup. If $\mathcal O(K)$ is flat and finitely presented as an $R$-module, then $K$ is finite locally free. Over a noetherian base, flatness alone suffices; over a DVR, torsion-freeness of $\mathcal O(K)$ suffices.

**Proof.** The closed immersion makes $\mathcal O(K)$ a quotient of the finite $R$-module
$\mathcal O(G)$, so it is finite. A finitely presented flat module is finite projective, proving
the first assertion. Over a noetherian ring, every finite module is finitely presented. Over a
DVR, a finite torsion-free module is free. These arguments are affine-local on the base and
therefore prove the corresponding scheme statements. $\square$

This criterion is intentionally not replaced by a blanket assertion. Later structural theorems may prove flatness of kernels in special categories, but it is not a formal consequence of being a closed subgroup of a finite flat group scheme.

If $f:G\to H$ is faithfully flat and both are finite locally free of constant ranks $g$ and $h$, then its kernel is finite locally free and

$$
\operatorname{rk}(G)=\operatorname{rk}(\ker f)\operatorname{rk}(H).
$$

This follows once $G\to H$ is recognized as a torsor under its kernel; Chapter 9 proves the coordinate statement. In particular $h$ divides $g$ on every connected component.

### 6.4 Schematic images and their limits

For a morphism of affine schemes $f:G=\operatorname{Spec}A\to H=\operatorname{Spec}B$, its scheme-theoretic image as a closed subscheme of $H$ is

$$
\operatorname{SIm}(f)=\operatorname{Spec}(B/\ker f^*).
$$

It is the smallest closed subscheme through which $f$ factors. This construction always exists for affine schemes, but two further claims require care: that the image is a subgroup scheme, and that it commutes with base change.

Over a field, tensor products preserve injections. If $b\in\ker f^*$ then $\Delta_B(b)$ maps to zero in $A\otimes A$, so it maps to zero in $(B/\ker f^*)\otimes(B/\ker f^*)$; hence the kernel is a Hopf ideal. Thus the schematic image of a morphism of affine group schemes over a field is a closed subgroup scheme.

Over a general ring, an injection $B/I\hookrightarrow A$ can cease to be injective after tensoring, so the same argument can fail. A sufficient hypothesis is that $B/I\to A$ be **pure**, meaning it remains injective after tensoring with every module; flat cokernel is sufficient. Under this hypothesis its tensor square injects into $A\otimes_RA$, $I$ is a Hopf ideal, and the schematic image is a subgroup. Flatness of $B/I$ over $R$ is not by itself enough to make its inclusion into $A$ pure.

Likewise, $\ker(f^*)$ need not commute with nonflat scalar extension. If $R\to R'$ is flat, kernels do commute with base change, so schematic images do. Without flatness one should not identify the base change of an image with the image after base change.

### 6.5 Geometric images are not enough

A map can be trivial on every geometric point and still have a nontrivial schematic image. Over a field $k$ of characteristic $p$, the inclusion $\alpha_p\hookrightarrow\mathbf G_a$ has only the zero point over every algebraically closed field extension, yet its schematic image is $\alpha_p$, not the identity subgroup. Similarly $\mu_p\hookrightarrow\mathbf G_m$ is invisible as a set of geometric points.

This is why “take the closure of the pointwise image” is not a definition suitable for nonreduced group schemes. The correct construction uses the kernel of the map on coordinate rings, and even then subgroup and base-change properties must be justified by exact hypotheses.

## 7. Normal subgroup schemes and conjugation

### 7.1 Conjugation as a morphism

For any group scheme $G$, conjugation is the morphism

$$
c:G\times_SG\longrightarrow G,\qquad (g,x)\longmapsto gxg^{-1}.
$$

It is built from multiplication, inversion, and projections, so it is defined over the base and works on every test scheme. A closed subgroup $H\hookrightarrow G$ is **normal** if conjugation restricts to

$$
G\times_SH\longrightarrow H.
$$

Equivalently, for every $T$, every $g\in G(T)$, and every $h\in H(T)$, the element $ghg^{-1}$ lies in $H(T)$. By Yoneda, quantifying over all $T$ is equivalent to factorization of the conjugation morphism. Checking only geometric points is not equivalent when $H$ has infinitesimal structure.

Every kernel is normal: if $h\in\ker f(T)$, then

$$
f(ghg^{-1})=f(g)f(h)f(g)^{-1}=1.
$$

This pointwise calculation is valid because it is natural for every $T$.

### 7.2 The coaction criterion for normality

Let $G=\operatorname{Spec}A$ and let $H$ be defined by a Hopf ideal $I$. Pullback along conjugation gives a coaction

$$
\operatorname{ad}:A\longrightarrow A\otimes_RA.
$$

With the first tensor factor recording the conjugating element, one convenient Sweedler formula is

$$
\operatorname{ad}(a)
=\sum a_{(1)}S(a_{(3)})\otimes a_{(2)}.
$$

Indeed, evaluating the first factor at $g$ and the second at $x$ yields the value of $a$ on $gxg^{-1}$; a different convention for conjugating by $g^{-1}$ exchanges the formula. The subgroup is normal exactly when

$$
\operatorname{ad}(I)\subseteq A\otimes_RI.
$$

Then the second factor descends from $A$ to $A/I$, giving the restricted action on $H$. This is often called stability under the adjoint coaction.

If $G$ is commutative, conjugation is the second projection, so every closed subgroup is normal. Algebraically, cocommutativity simplifies the adjoint coaction to $1\otimes a$.

### 7.3 Normality after base change and descent

Normality is preserved by arbitrary base change because factorization of conjugation survives pullback. It can be checked after a faithfully flat base change: if the base-changed map $G'\times H'\to G'$ factors through $H'$, then the corresponding coordinate map kills the descended ideal after a faithfully flat extension and therefore already killed it.

Normality of every geometric fiber need not by itself imply global normality unless one has finiteness or flatness conditions allowing vanishing of the obstruction to be detected fiberwise. A module map can vanish after tensoring with every residue field while retain infinitesimal information over a nonreduced base. Faithfully flat testing is the robust substitute.

## 8. Actions, invariants, and torsors

### 8.1 Actions and coactions

Let $G=\operatorname{Spec}H$ be an affine group scheme and $X=\operatorname{Spec}A$ an affine $S$-scheme. A right action

$$
\rho:X\times_SG\longrightarrow X,\qquad (x,g)\longmapsto xg
$$

corresponds to an $R$-algebra map

$$
\rho^*:A\longrightarrow A\otimes_RH.
$$

The action axioms become

$$
(\rho^*\otimes\operatorname{id})\rho^*
=(\operatorname{id}\otimes\Delta_H)\rho^*,
\qquad
(\operatorname{id}\otimes\varepsilon_H)\rho^*=\operatorname{id}_A.
$$

Thus an action is a **coaction**. For a left action the target is naturally $H\otimes_RA$, and silently swapping factors can reverse conventions in conjugation and quotient calculations.

If $A=\mathcal O(G)$ and a subgroup $K\hookrightarrow G$ acts on the right by multiplication, the coaction is

$$
A\xrightarrow{\Delta_A}A\otimes_RA\longrightarrow A\otimes_R\mathcal O(K).
$$

This is the coaction relevant to right cosets $G/K$.

### 8.2 Invariants and coinvariants

For a right $H$-coaction $\rho^*:A\to A\otimes_RH$, define the invariant subalgebra

$$
A^G=\{a\in A:\rho^*(a)=a\otimes1\}.
$$

It is an $R$-subalgebra because $\rho^*$ is an algebra map. Equalizer notation is useful:

$$
A^G=\operatorname{Eq}\bigl(A\rightrightarrows A\otimes_RH\bigr),
$$

where the arrows are $\rho^*$ and $a\mapsto a\otimes1$. This immediately shows why invariants commute with flat base change under suitable finite-presentation conditions but may fail to commute with arbitrary nonflat base change: equalizers are kernels.

For a right action of $K$ on $G$, write $A^{\operatorname{co}K}$ for these invariants. The prefix “co” emphasizes that the action on schemes is encoded by a coaction on functions. Functions in $A^{\operatorname{co}K}$ are constant along right $K$-orbits in the functorial sense.

An invariant ring always exists, but $\operatorname{Spec}(A^G)$ need not represent an orbit functor. It may identify more than orbits, and formation of invariants can lack desirable base-change or finiteness properties. Quotient theorems therefore require more than writing down invariants.

### 8.3 Torsors and the canonical map

Let $P\to X$ carry a right action of $G$. It is a **$G$-torsor for the faithfully flat topology** if

1. $P\to X$ is faithfully flat and locally of finite presentation; and
2. the map

$$
P\times_SG\longrightarrow P\times_XP,\qquad(p,g)\longmapsto(p,pg)
$$

is an isomorphism.

The second condition says that two points of a fiber differ by a unique group element. The first says that local sections exist after a faithfully flat base change; indeed pulling a torsor back along itself trivializes it:

$$
P\times_XP\simeq P\times_SG.
$$

In affine coordinates, let $X=\operatorname{Spec}B$, $P=\operatorname{Spec}A$, and $G=\operatorname{Spec}H$. Then $B\to A$ is faithfully flat and the torsor isomorphism is equivalent to bijectivity of the **canonical map**

$$
\beta:A\otimes_BA\longrightarrow A\otimes_RH,
\qquad a\otimes a'\longmapsto(a\otimes1)\rho^*(a').
$$

For the right multiplication action of a subgroup on a group, this becomes

$$
\beta(a\otimes a')=\sum aa'_{(1)}\otimes\overline{a'_{(2)}}.
$$

This explicit map is the safest criterion for quotient claims.

### 8.4 Descent along a torsor

Suppose $P\to X$ is an affine torsor as above. Faithfully flat descent identifies functions on $X$ with invariant functions on $P$:

$$
B\xrightarrow{\sim}A^G.
$$

Indeed $B$ is the equalizer of $A\rightrightarrows A\otimes_BA$. Through the torsor isomorphism, these arrows become $a\mapsto a\otimes1$ and the coaction $\rho^*(a)$. This proves the claim.

More generally, quasi-coherent modules on $X$ correspond to $A$-modules equipped with compatible descent data, which the torsor isomorphism rewrites as equivariant $G$-modules on $P$. Only the elementary function-level consequence is needed here, but it explains why torsors are the correct foundation for effective quotients.

A torsor need not have a section over $X$. If it does, choosing a section identifies it with $X\times_SG$, but the identification depends on the section. Thus torsors are locally trivial groups of choices, not globally products by definition.

## 9. Quotients under exact hypotheses

### 9.1 Three different quotient questions

Given a normal closed subgroup $H\hookrightarrow G$, the notation $G/H$ can refer to three distinct objects.

First, the pointwise quotient $T\mapsto G(T)/H(T)$ is a presheaf of groups. It generally fails descent: elements may exist locally and glue only up to an $H$-valued discrepancy. Second, its sheafification for the faithfully flat topology is a sheaf quotient. Third, one may ask whether that sheaf is represented by a scheme, and more specifically by an affine group scheme. None of these transitions is automatic.

The pointwise quotient is usually too small. A torsor over $T$ may be locally represented by a point of $G$ without having a global representative. Sheafification adds precisely these locally defined cosets. Representability then requires an effective algebraic construction.

We will use the notation $G/H$ only after specifying a representing object or explicitly saying “quotient sheaf.” There is no blanket existence theorem in this book for arbitrary subgroup schemes.

### 9.2 An affine quotient criterion

Let $H=\operatorname{Spec}C$ act on the right on $G=\operatorname{Spec}A$, and put

$$
B=A^{\operatorname{co}H}.
$$

Assume:

1. $A$ is faithfully flat and locally of finite presentation over $B$;
2. the canonical map

$$
\beta:A\otimes_BA\xrightarrow{\sim}A\otimes_RC
$$

is an isomorphism.

Then $G\to Q=\operatorname{Spec}B$ is an $H$-torsor. Consequently $Q$ represents the faithfully flat sheaf quotient of $G$ by $H$.

**Proof strategy.** The two assumptions are exactly the affine translations of the torsor definition. It remains to verify the quotient property. For any $T$, two maps $T\to G$ have the same image in $Q$ precisely when, after a faithfully flat cover of $T$, their pair factors through $G\times_QG$. Through the torsor isomorphism, this says that locally the second is obtained from the first by a unique $H$-element. Thus the fibers of $G\to Q$ are exactly the sheafified $H$-orbits. Since $G\to Q$ is a cover, every $Q$-point is locally lifted to $G$. These statements give the universal property of the quotient sheaf. $\square$

If $G$ is a group scheme, $H$ is normal, and $B$ is stable under the Hopf operations so that $B\subseteq A$ is a Hopf subalgebra, then $Q$ is an affine group scheme and $G\to Q$ a group morphism. Normality is what makes multiplication of right cosets well defined.

### 9.3 Faithfully flat Hopf subalgebras

A particularly useful algebraic situation begins with an injective Hopf map

$$
B\hookrightarrow A
$$

such that $A$ is faithfully flat over $B$. It gives a faithfully flat group morphism

$$
G=\operatorname{Spec}A\longrightarrow Q=\operatorname{Spec}B.
$$

Let $B^+=\ker(\varepsilon_B)$ and

$$
C=A/AB^+.
$$

Then $H=\operatorname{Spec}C$ is the kernel. Under the standard Hopf-descent hypotheses

$$
B=A^{\operatorname{co}C}
$$

and

$$
A\otimes_BA\xrightarrow{\sim}A\otimes_RC,\qquad
a\otimes a'\longmapsto\sum aa'_{(1)}\otimes\overline{a'_{(2)}},
$$

the sequence $H\to G\to Q$ is a torsor quotient. For commutative Hopf algebras, faithful flatness of $A$ over the Hopf subalgebra $B$ is the familiar setting in which these Hopf-descent conclusions hold; recording the two displayed conclusions remains valuable because they are the exact facts used in proofs.

The inverse of the canonical map is suggested by the antipode: informally,

$$
a\otimes\bar c\longmapsto\sum aS(c_{(1)})\otimes c_{(2)}.
$$

Independence from a lift of $\bar c$ and landing in the relative tensor product are precisely where the augmentation ideal and Hopf-subalgebra hypotheses enter. The antipode identities verify that the two formulas compose to the identity.

### 9.4 Quotients by finite locally free subgroups

The quotient case needed most often later is the following affine theorem.

We first isolate the effectivity input and prove it in the form required here.

**Finite-relation lemma.** Let

$$
R_1\mathrel{\substack{\xrightarrow{s}\\[-.35em]\xrightarrow[t]{}}}X
$$

be an equivalence relation over $S$. Suppose that $X$ is affine over $S$, both $s$ and $t$ are
finite locally free of the same rank $n$ locally on $S$, and $(s,t):R_1\to X\times_SX$ is a
closed immersion. Then the faithfully flat quotient sheaf $X/R_1$ is affine over $S$. If
$S=\operatorname{Spec}R$,
$X=\operatorname{Spec}A$, and $R_1=\operatorname{Spec}D$, its coordinate algebra is

$$
B=\operatorname{Eq}\bigl(A\mathrel{\substack{\xrightarrow{s^*}\\[-.35em]
\xrightarrow[t^*]{}}}D\bigr).
$$

Moreover, $A$ is finite locally free and faithfully flat over $B$, and the relation map induces

$$
A\otimes_BA\xrightarrow{\sim}D. \tag{9.1}
$$

**Proof.** The assertion is local on $S$, so work with the displayed rings. We recall the
finite-orbit calculation rather than hiding the decisive step in a descent citation. Restricting
to a clopen stratum of $S$, let $D$ have rank $n$ as an $A$-module through $s^*$. For $a\in A$, form the
characteristic polynomial

$$
P_a(Z)=\det\bigl(Z-m_{t^*(a)};D\bigr)\in A[Z].
$$

The identity arrow pulls Cayley--Hamilton back to $P_a(a)=0$. The composition and inverse arrows
of the relation identify the two pullbacks of the finite family of targets of a source fiber.
Functoriality of characteristic polynomials under base change therefore gives

$$
s^*(\operatorname{coeff}P_a)=t^*(\operatorname{coeff}P_a);
$$

all coefficients of $P_a$ lie in $B$.

We now give the finite-orbit determinant argument that supplies effectivity. Because $(s,t)$ is a
closed immersion, the map $A\otimes_RA\to D$ is surjective. Choose finitely many tensors whose
images generate the rank-$n$ $A$-module $D$. On an open where its determinant line is trivial,
the $n$-fold wedges of those images give finitely many minors $d_\nu\in A$ generating the unit
ideal. The open $D(d_\nu)$ is the locus where the corresponding $n$ images form a basis of $D$.

Transport a minor around the relation and take its norm along the finite locally free source
map. Composition says that transporting twice is the same as transporting once around the
composite arrow, so the resulting norm has equal pullbacks by $s^*$ and $t^*$. It is therefore
an element $b_\nu\in B$. The invariant principal opens $D(b_\nu)\subseteq\operatorname{Spec}A$
are saturated for the relation. They cover: over any source point, one of the minors is
invertible at every point of its finite relation class after replacing the chosen finite family
by the union of its finitely many transports, and its norm is then invertible at that source
point.

Localize at one $b_\nu$. The adjugate identities for the chosen invertible minor express every
element of $D$ uniquely in its $n$ basis columns. Pulling those identities to the double relation
and using composition shows that their transition coefficients have equal $s^*$- and
$t^*$-pullbacks. Pulling back by the identity arrow therefore gives elements
$u_1,\ldots,u_n\in A_{b_\nu}$ such that

$$
A_{b_\nu}=\bigoplus_{i=1}^nB_{b_\nu}u_i.
$$

Before applying the identity arrow, the same adjugate identities say that the surjection

$$
A\otimes_BA\longrightarrow D,\qquad a\otimes a'\longmapsto s^*(a)t^*(a'),
$$

maps the left $A_{b_\nu}$-basis $1\otimes u_i$ to the chosen $A_{b_\nu}$-basis of
$D_{b_\nu}$. It is therefore an isomorphism on every $D(b_\nu)$. These invariant opens cover,
so they prove globally that $A$ is finite locally free of rank $n$ over $B$ and that (9.1) is an
isomorphism. Its rank is positive because the relation has identity arrows, so $A$ is faithfully
flat over $B$.

Equation (9.1) says exactly that two maps into $X$ have the same image in
$\operatorname{Spec}B$ precisely when they are related by $R_1$, after a faithfully flat cover.
Faithful flatness of $B\to A$ gives local lifts of every point of $\operatorname{Spec}B$.
Therefore $\operatorname{Spec}B$ represents the quotient sheaf. The construction commutes with
localization on $S$, so the affine quotients glue over a nonaffine base. $\square$

**Theorem 9.1 (finite locally free affine quotient).** Let $G$ be an affine group scheme over an arbitrary base scheme $S$, and let $H\hookrightarrow G$ be a closed subgroup that is finite locally free over $S$. Then the faithfully flat quotient sheaf $G/H$ is represented by an affine $S$-scheme. On an affine base, it is

$$
\operatorname{Spec}\bigl(\mathcal O(G)^{\operatorname{co}H}\bigr),
$$

and $G\to G/H$ is finite locally free, faithfully flat, and an $H$-torsor. If $H$ is normal, the quotient is an affine group scheme.

**Proof strategy.** Right translation makes

$$
G\times_SH\rightrightarrows G
$$

a finite locally free equivalence relation: the arrows are projection and action. The automorphism

$$
G\times_SG\longrightarrow G\times_SG,\qquad(g,x)\longmapsto(g,g^{-1}x)
$$

carries the image of the relation to $G\times_SH$, so the relation map to $G\times_SG$ is a
closed immersion because $H\hookrightarrow G$ is. The finite-relation lemma applies. Its
equalizer is exactly $B=A^{\operatorname{co}H}$, and (9.1) becomes the canonical torsor
isomorphism

$$
A\otimes_BA\xrightarrow{\sim}A\otimes_RC.
$$

Thus $G\to\operatorname{Spec}B$ is finite locally free and faithfully flat, and §9.2 identifies
its target with the quotient sheaf. If $H$ is normal, multiplication, identity, and inversion
are constant on cosets. They descend uniquely through the torsor, and their group identities
descend by faithful flatness. $\square$

The finite locally free conclusion can be seen after pulling back along the faithfully flat cover $G\to G/H$. There the map becomes

$$
G\times_SH\longrightarrow G,
$$

which is finite locally free of rank $\operatorname{rk}(H)$. Finite local freeness and rank descend faithfully flatly. Thus on every connected component,

$$
\operatorname{rk}(G)=\operatorname{rk}(H)\operatorname{rk}(G/H)
$$

whenever $G$ itself is finite locally free.

The theorem is not a claim that arbitrary quotient presheaves are representable. Its force comes from the finite locally free subgroup and the effective affine torsor theorem. If one works outside that theorem's scope, the two conditions of §9.2 are the exact replacement hypotheses.

### 9.5 Quotient coordinates in examples

Let $\mu_n$ act on $\mathbf G_m$ by multiplication. On coordinates the coaction sends

$$
T\longmapsto T\otimes U,\qquad U^n=1.
$$

The invariants are $R[T^n,T^{-n}]$. Setting $V=T^n$ identifies the quotient with $\mathbf G_m$, and the quotient map is $[n]:\mathbf G_m\to\mathbf G_m$. It is a $\mu_n$-torsor for the faithfully flat topology because

$$
R[T,T^{-1}]
$$

is free of rank $n$ over $R[V,V^{-1}]$ with basis $1,T,\ldots,T^{n-1}$. This remains true even when $n$ is not invertible and $\mu_n$ is nonreduced.

In characteristic $p$, $\alpha_p$ acts on $\mathbf G_a$ by translation. The coaction is

$$
T\longmapsto T\otimes1+1\otimes U,\qquad U^p=0.
$$

The invariants are $k[T^p]$, and the quotient map is Frobenius $F:\mathbf G_a\to\mathbf G_a$. The extension $k[T^p]\subseteq k[T]$ is free of rank $p$. Thus Frobenius is an $\alpha_p$-torsor in the faithfully flat topology, although it is not a torsor in the étale topology and induces a bijection on algebraically closed points. This example captures why the topology and the scheme structure both matter.

## 10. Exact sequences of affine group schemes

### 10.1 Pointwise exactness is not the right default

For group-valued functors, a sequence

$$
1\longrightarrow H\xrightarrow{i}G\xrightarrow{q}Q\longrightarrow1
$$

can be interpreted in several ways. **Pointwise exactness** demands exactness of

$$
1\to H(T)\to G(T)\to Q(T)\to1
$$

for every $T$. This is too strong for most quotient maps because $G(T)\to Q(T)$ need not be surjective: a point of $Q$ can lift only after a faithfully flat cover.

The robust notion is **sheaf exactness for the faithfully flat topology**. It requires $H\to G$ to identify with the kernel of $q$, and requires $G\to Q$ to be locally surjective for faithfully flat covers, with $Q$ the associated sheaf quotient. For affine group schemes it is customary to require $q$ faithfully flat (and usually locally of finite presentation in the torsor setting). Then local surjectivity follows.

Pointwise exactness implies sheaf exactness when representability and kernels behave as stated, but the converse does not imply surjectivity on $T$-points. The obstruction is the possible nontriviality of an $H$-torsor over $T$.

### 10.2 An exactness criterion in Hopf algebras

Let the coordinate maps be

$$
R\longrightarrow B=\mathcal O(Q)
\xrightarrow{q^*}A=\mathcal O(G)
\xrightarrow{i^*}C=\mathcal O(H)
\longrightarrow R.
$$

A standard faithfully flat exact sequence is characterized by the following data:

1. $q^*$ is injective and $A$ is faithfully flat over $B$;
2. $i^*$ is surjective;
3. $\ker(i^*)=AB^+$, where $B^+=\ker\varepsilon_B$;
4. $B=A^{\operatorname{co}C}$ for the right $C$-coaction on $A$;
5. the canonical map $A\otimes_BA\to A\otimes_RC$ is an isomorphism.

Conditions 1 and 3 say that $H$ is the scheme-theoretic kernel of $q$. Conditions 4 and 5 say that $Q$ is the effective quotient and $G\to Q$ an $H$-torsor. In common Hopf-descent settings some conditions follow from others, but keeping the full list visible prevents a ring-theoretic injection from being mistaken for an exact quotient.

For finite locally free group schemes of constant ranks, exactness yields

$$
\operatorname{rk}G=\operatorname{rk}H\operatorname{rk}Q.
$$

The proof is torsor descent as in §9.4, not a count of geometric points.

### 10.3 Failure of surjectivity on rational points

Consider $[n]:\mathbf G_m\to\mathbf G_m$. It is faithfully flat with kernel $\mu_n$, so

$$
1\to\mu_n\to\mathbf G_m\xrightarrow{[n]}\mathbf G_m\to1
$$

is exact as a faithfully flat sheaf sequence. On $R$-points the last map is

$$
R^\times\longrightarrow R^\times,\qquad u\longmapsto u^n,
$$

which is rarely surjective. The missing lift becomes available after adjoining a root, a finite faithfully flat extension when the equation is monic and the root is a unit.

In characteristic $p$, the sequence

$$
0\to\alpha_p\to\mathbf G_a\xrightarrow{F}\mathbf G_a\to0
$$

is faithfully flat exact. For a nonperfect field $k$, $F:k\to k$ is not surjective. Even over a perfect field, testing only field points misses the kernel because $\alpha_p(k)=0$. These two failures show independently why pointwise exactness is unsuitable.

### 10.4 Exactness and base change

Fiber products preserve kernels under arbitrary base change. Faithfully flat morphisms and finite locally free torsors also remain so under arbitrary base change. Hence an exact torsor sequence stays exact after any change of base.

At the Hopf-algebra level, the caution is that equalizers such as $B=A^{\operatorname{co}C}$ do not always commute with nonflat tensor products in isolation. In an actual torsor sequence, the geometric quotient and torsor base-change first; their descended invariant description then remains valid. This is a useful proof strategy: base-change the represented structure rather than commute a raw kernel past a nonflat tensor product without justification.

Conversely, exactness can be checked after a faithfully flat base change when all objects and maps are already defined over the original base. Kernel identification, faithful flatness, and the torsor isomorphism descend. This allows a quotient sequence to be verified after passing to a cover where coordinates or groups split.

## 11. Commutative group schemes and cocommutativity

### 11.1 The tensor flip

Let $\tau:A\otimes_RA\to A\otimes_RA$ be the flip $a\otimes b\mapsto b\otimes a$. An affine group scheme $G=\operatorname{Spec}A$ is commutative exactly when

$$
\tau\circ\Delta=\Delta.
$$

A Hopf algebra satisfying this identity is **cocommutative**. The proof is a direct reversal of arrows: commutativity says $m=m\circ\operatorname{swap}$, and pullback turns this into $\Delta=\tau\Delta$.

Every coordinate algebra here is commutative as an algebra. Thus:

$$
\begin{array}{c|c}
\text{geometric property}&\text{coordinate property}\\
\hline
G\text{ affine scheme}&A\text{ commutative algebra}\\
G\text{ group scheme}&A\text{ Hopf algebra}\\
G\text{ commutative group scheme}&\Delta\text{ cocommutative}
\end{array}
$$

The additive, multiplicative, diagonalizable, and constant abelian examples are cocommutative. The constant group scheme attached to a nonabelian finite group has a commutative coordinate ring but noncocommutative coproduct.

### 11.2 Consequences for subgroups and quotients

Every closed subgroup of a commutative group scheme is normal. Kernels, intersections, and representable quotients remain commutative. Exact sequences may therefore be written additively,

$$
0\longrightarrow H\longrightarrow G\longrightarrow Q\longrightarrow0,
$$

even when the coordinate rings use multiplicative notation.

For a cocommutative Hopf algebra, left and right coset coactions agree after the tensor flip, and the adjoint coaction is trivial. This removes much of the normality bookkeeping. It does not remove representability or flatness hypotheses for quotients.

### 11.3 Multiplication by an integer

On a commutative group scheme $G$, multiplication by $n\in\mathbb Z$ is the morphism

$$
[n]:G\longrightarrow G,\qquad g\longmapsto ng,
$$

using additive notation. For $n\ge1$ it is the composite of the diagonal $G\to G^n$ with iterated multiplication; $[0]=e\circ p$ and $[-n]=i\circ[n]$. Its kernel

$$
G[n]=\ker[n]
$$

is the **$n$-torsion subgroup scheme**. It is always a closed subgroup scheme and commutes with arbitrary base change.

If $A=\mathcal O(G)$, the map $[n]^*:A\to A$ is the $n$-fold convolution power of the identity map:

$$
[n]^*=\underbrace{\operatorname{id}_A*\cdots*\operatorname{id}_A}_{n\text{ times}}.
$$

Then

$$
\mathcal O(G[n])=A/A\,[n]^*(A^+),
\qquad A^+=\ker\varepsilon.
$$

For $\mathbf G_m$ this gives $T\mapsto T^n$ and $\mu_n$; for $\mathbf G_a$ it gives $T\mapsto nT$. In characteristic $p$, $[p]$ on $\mathbf G_a$ is zero, whereas Frobenius is $T\mapsto T^p$ on coordinate pullback. The two maps must not be confused.

## 12. The identity, cotangent space, and Lie algebra

### 12.1 Why the augmentation ideal matters

The identity section is encoded by the counit $\varepsilon:A\to R$. Its ideal is

$$
I=A^+=\ker\varepsilon.
$$

The quotient $I/I^2$ is the conormal module of the identity section. It records functions vanishing to first order at the identity, modulo those vanishing to second order. Its dual

$$
\operatorname{Lie}(G)=\operatorname{Hom}_R(I/I^2,R)
$$

is the tangent module at the identity when this elementary global description has the expected finite-presentation behavior. More generally one can sheafify over a nonaffine base.

This construction detects infinitesimal directions invisible to geometric points. It is not intended here as a full theory of smooth group schemes; it supplies a diagnostic for connected and nonreduced finite fibers.

### 12.2 Dual-number points

Let $C$ be an $R$-algebra and $C[\epsilon]/(\epsilon^2)$ its dual numbers. A tangent vector at the identity is a point

$$
x:A\longrightarrow C[\epsilon]/(\epsilon^2)
$$

whose reduction modulo $\epsilon$ is the identity point $A\xrightarrow\varepsilon R\to C$. Such a map has the form

$$
x(a)=\varepsilon(a)+\epsilon D(a),
$$

where $D:A\to C$ is an $R$-derivation relative to the augmentation:

$$
D(ab)=\varepsilon(a)D(b)+\varepsilon(b)D(a).
$$

These derivations are naturally

$$
\operatorname{Hom}_C((I/I^2)\otimes_RC,C).
$$

Thus $I/I^2$ represents first-order identity directions. This direct computation is the elementary bridge between functorial infinitesimals and the cotangent module.

### 12.3 Calculations for the basic groups

For $\mathbf G_a$, $I=(T)$ and $I/I^2$ is free of rank one, generated by $T$. Hence $\operatorname{Lie}(\mathbf G_a)\cong R$. For $\mathbf G_m$, $I=(T-1)$ and the same conclusion holds.

For $\mu_n$, write $u=T-1$. Its equation is $(1+u)^n-1$, whose linear term is $nu$. Therefore

$$
I/I^2\cong R/(n).
$$

If $n$ is invertible, the cotangent space vanishes: $\mu_n$ has no infinitesimal identity direction. In characteristic dividing $n$, it is nonzero. For $\mu_p$ over a field of characteristic $p$, it is one-dimensional.

For $\alpha_p=k[T]/(T^p)$, the augmentation ideal is $(T)$ and $I/I^2$ is one-dimensional. Thus $\alpha_p$ and $\mu_p$ both have a tangent direction, even though their group laws differ.

For a constant finite group scheme, the identity section is open and closed, so its augmentation ideal is idempotent near the complementary components and $I/I^2=0$. This matches the absence of infinitesimal directions.

### 12.4 Lie algebra and commutators

For a sufficiently well-behaved group scheme, left translation identifies tangent spaces at all points with the tangent space at the identity. Commutators induce a Lie bracket on $\operatorname{Lie}(G)$. In matrix groups this is the usual bracket

$$
[X,Y]=XY-YX.
$$

For commutative $G$ the bracket is zero. The construction can be derived by evaluating commutators on rings with two independent square-zero parameters and extracting the mixed coefficient. We do not need its full general theory; the cotangent module and its rank already give the relevant infinitesimal information.

A zero Lie algebra does not by itself prove that a finite group scheme is étale over an arbitrary base without further finiteness and flatness hypotheses. For finite locally free group schemes over a field, vanishing of the cotangent space at the identity propagates by translations and characterizes the reduced étale case. The hypotheses matter because tangent spaces detect first-order nilpotents, not every failure of flatness over a varying base.

## 13. Finite locally free group schemes

### 13.1 Hopf algebras finite projective over the base

An affine group scheme $G=\operatorname{Spec}A$ is **finite locally free over $R$** when the underlying $R$-module of $A$ is finite projective. All conclusions for finite locally free algebras apply: the rank is locally constant on $\operatorname{Spec}R$, arbitrary base change preserves it, every fiber has that scheme-theoretic length, and over a local base $A$ is free.

The Hopf maps are additional algebraic structure on this finite projective module:

$$
\Delta:A\to A\otimes_RA,\qquad
\varepsilon:A\to R,\qquad S:A\to A.
$$

The counit splits the unit $R\to A$, so as $R$-modules

$$
A\cong R\oplus A^+.
$$

If $A$ has constant rank $n$, the augmentation ideal $A^+$ is finite projective of rank $n-1$. This splitting does not generally split $A$ as a product of algebras: the identity section is closed but need not be an open component. For $\mu_p$ or $\alpha_p$ in characteristic $p$, it is the unique topological point of the fiber.

Finite locally free group schemes have positive rank on every nonempty component of the base because the counit shows that $R$ is a direct summand of $A$. Hence their structure morphisms are faithfully flat and surjective. This is stronger than the statement for arbitrary finite locally free schemes, where a rank-zero component may occur.

### 13.2 Translation and uniformity of fibers

For any $T$ and $g\in G(T)$, left translation

$$
L_g:G_T\longrightarrow G_T,\qquad x\longmapsto gx
$$

is an automorphism with inverse $L_{g^{-1}}$. Thus every rational point looks locally like the identity. Over a field extension containing a point, its local ring and tangent space are isomorphic to those at the identity.

This uniformity has strong consequences over an algebraically closed field. The local Artinian rings at all geometric points of a finite group scheme have the same length, because translations permute points transitively within cosets of the identity component, and in the group itself every point translates the identity to that point. Therefore

$$
\operatorname{rk}(G)=|G(k)|\cdot\operatorname{length}(\mathcal O_{G,e})
$$

when $k$ is algebraically closed. In particular the number of geometric points divides the rank. For a reduced finite group scheme, every local length is one, so the number of points equals the rank. For $\alpha_p$ and $\mu_p$, it is one while the rank is $p$.

### 13.3 Closed subgroups and rank

Let $H\hookrightarrow G$ be a closed subgroup of a finite locally free group scheme. Then $H$ is finite, but its coordinate algebra $A/I$ need not be flat without an additional theorem or hypothesis. Whenever $H$ is finite locally free, its rank behaves like the order of a subgroup.

If the quotient $G/H$ is represented by the finite locally free torsor theorem, then

$$
\operatorname{rk}H\mid\operatorname{rk}G,\qquad
\operatorname{rk}(G/H)=\frac{\operatorname{rk}G}{\operatorname{rk}H}
$$

on each connected component. This is the scheme-theoretic form of Lagrange's theorem. Its proof uses ranks of finite projective modules and faithful descent, so it remains valid for nonreduced fibers where cardinality arguments fail.

Over a field, every finite-dimensional vector space is flat, so every closed subgroup of a finite group scheme is finite locally free. Over a DVR, the quotient coordinate algebra must be torsion-free; this is not automatic for an arbitrary closed subscheme, and must be established for the subgroup in question. Bookkeeping with the quotient algebra rather than generic-point cardinalities is the reliable test.

### 13.4 Products, kernels, and exact sequences

Products of finite locally free group schemes are finite locally free, with ranks multiplying:

$$
\operatorname{rk}(G\times_SH)=\operatorname{rk}G\operatorname{rk}H.
$$

A base change preserves rank. A kernel of a morphism between such groups is finite, and it is finite locally free under any of the flatness criteria in Proposition 6.1. In particular, if the morphism is faithfully flat, the kernel is finite locally free because the map is a torsor under its kernel in the exact Hopf-descent setting.

Suppose

$$
1\to H\to G\to Q\to1
$$

is a faithfully flat exact sequence and two of the groups are known finite locally free in a configuration that permits descent. If $H$ and $Q$ are finite locally free, then $G$ is: locally over $Q$, the torsor becomes $Q\times H$, and finite local freeness descends. If $G$ and $H$ are finite locally free and the quotient theorem applies, then $Q$ is finite locally free by rank descent. Merely having a pointwise exact sequence does not justify either conclusion.

### 13.5 Base change and fiberwise traps

For every $R\to R'$,

$$
\mathcal O(G_{R'})=A\otimes_RR'
$$

with all Hopf operations tensored accordingly. The rank function pulls back. If $R'$ is faithfully flat, finite projectivity, morphism isomorphisms, normality, and torsor exactness can be detected after base change.

Several plausible fiberwise arguments are invalid. Equality of the number of geometric points does not imply equality of subgroup schemes. A morphism can be bijective on all geometric points without being an isomorphism, as Frobenius on $\mathbf G_a$ shows. Fiberwise injectivity of a map of finite projective modules does not imply a locally split injection unless the cokernel is flat. Constancy of fiber cardinality says less than constancy of fiber length, and even constant length does not replace a global flatness proof unless finite presentation and a valid flatness criterion are present.

## 14. Connected, reduced, and nonreduced behavior

### 14.1 Identity components over a field

Let $G$ be a finite group scheme over a field $k$. Its coordinate algebra is Artinian and decomposes as a product of local Artinian algebras. The connected component $G^0$ containing the identity is an open-and-closed subgroup scheme.

To see subgroup stability, multiplication sends the connected scheme $G^0\times G^0$ into the connected component containing the identity, and inversion sends $G^0$ to itself. More algebraically, the idempotent selecting the identity factor is compatible with the Hopf maps. Every other connected component becomes a translate of $G^0$ after a field extension containing a point on it.

The quotient $G/G^0$ is finite étale over a perfect field; over an arbitrary field, the reduced subgroup and component quotient require care with inseparability. The general connected–étale sequence belongs to a more specialized treatment. Here the key point is that connectedness and nilpotence carry genuine group information not visible in the abstract group of geometric points.

### 14.2 Reduced finite group schemes over perfect fields

Over a perfect field $k$, a finite reduced $k$-algebra is a product of finite separable field extensions. Hence a finite reduced group scheme is finite étale. After an algebraic closure it becomes a constant finite group scheme.

Over an imperfect field, a finite reduced algebra can be inseparable and become nonreduced after extending scalars. Thus “reduced” is not geometrically stable there. Geometric reducedness, rather than reducedness over the original field, is the condition corresponding to finite étaleness.

For a finite group scheme over a field, translations show that smoothness or reducedness behavior is uniform across geometric points. The identity cotangent space is therefore a useful detector: in the finite locally free setting, vanishing after extension to an algebraic closure means every local Artinian factor is a field and the group is étale.

### 14.3 Characteristic-$p$ contrasts

Over a field $k$ of characteristic $p$, compare three rank-$p$ commutative group schemes:

$$
\underline{\mathbb Z/p\mathbb Z},\qquad \mu_p,\qquad \alpha_p.
$$

The first is reduced and has $p$ geometric points. The other two are connected, nonreduced, and have one geometric point. Yet $\mu_p$ and $\alpha_p$ are distinct. Their Hopf algebras, written with a nilpotent coordinate near the identity, are

$$
\mathcal O(\alpha_p)=k[t]/(t^p),
\qquad \Delta(t)=t\otimes1+1\otimes t,
$$

and

$$
\mathcal O(\mu_p)=k[u]/(u^p),
\qquad \Delta(u)=u\otimes1+1\otimes u+u\otimes u,
$$

where $u=T-1$. The extra quadratic term remembers multiplication.

On dual-number points $k[\epsilon]/(\epsilon^2)$, both have a one-dimensional tangent space. Higher nilpotent test rings distinguish their group laws. This is a useful methodological lesson: tangent spaces are first approximations, not complete invariants.

### 14.4 Frobenius and its kernel

For a scheme in characteristic $p$, the absolute Frobenius is the identity on the underlying
topological space and sends every function to its $p$th power. It is a morphism of schemes, but
over a field $k$ it is generally not a $k$-morphism: on scalars it induces
$a\mapsto a^p$. For a $k$-scheme $G$, the base-compatible map is the relative Frobenius

$$
F_{G/k}:G\longrightarrow G^{(p)},
$$

where $G^{(p)}$ is the pullback along Frobenius of $k$. If $G$ is a group scheme, functoriality of
absolute Frobenius with respect to multiplication, identity, and inversion makes $F_{G/k}$ a
$k$-group morphism. This fixes both its variance and its scalar convention.

For $\mathbf G_a$, after using the standard coordinate on the Frobenius twist, the pullback is
$T\mapsto T^p$ and the kernel is $\alpha_p$. For $\mathbf G_m$, it is $T\mapsto T^p$ and the
kernel is $\mu_p$. Both relative Frobenius maps are finite locally free of rank $p$ and are
torsor quotients in the faithfully flat topology. Their kernels have the same rank and
geometric-point count but different coproducts.

The relative Frobenius of an étale group scheme is an isomorphism, while nontrivial Frobenius kernels signal infinitesimal structure. We use this only as illumination; a systematic classification of finite flat group schemes in characteristic $p$ lies beyond the present scope.

## 15. Coordinate methods for subgroup schemes

### 15.1 Kernels of characters

A character of an affine group scheme $G$ is a morphism

$$
\chi:G\longrightarrow\mathbf G_m.
$$

It corresponds to a group-like unit $u=\chi^*(T)\in A$:

$$
\Delta(u)=u\otimes u,\qquad \varepsilon(u)=1.
$$

Its kernel is the closed subgroup defined by $u-1$:

$$
\mathcal O(\ker\chi)=A/(u-1).
$$

For a family of characters $\chi_i$, the common kernel is defined by all $u_i-1$. This reduces many diagonal subgroup calculations to lattice algebra.

For $D(M)$, a homomorphism $\mathbb Z\to M$ selecting $m\in M$ induces a character $D(M)\to\mathbf G_m$. If $M=\mathbb Z^r$, integer matrices describe all morphisms of split tori, with arrows reversed on character lattices. Kernels are diagonalizable precisely when the relevant cokernel group gives the expected group algebra; torsion in the lattice quotient produces finite diagonalizable factors such as $\mu_n$.

### 15.2 Subgroups of additive groups

A morphism $\mathbf G_a\to\mathbf G_a$ corresponds to a primitive polynomial $P(T)$ satisfying

$$
P(X+Y)=P(X)+P(Y).
$$

Over a characteristic-zero domain, such polynomials are linear. In characteristic $p$, additive polynomials

$$
P(T)=a_0T+a_1T^p+\cdots+a_rT^{p^r}
$$

occur. Their kernels are closed subgroup schemes with coordinate algebra $R[T]/(P(T))$. If the
leading coefficient $a_r$ is a unit, scaling $P$ by $a_r^{-1}$ makes it monic without changing
its ideal, so the kernel is finite locally free of rank $p^r$.

The derivative $P'(0)=a_0$ controls the cotangent space at the identity. If $a_0$ is a unit, the kernel has no infinitesimal tangent direction and is étale in the finite locally free field case. If $a_0=0$, nonreduced behavior can occur. The polynomial $T^p$ gives $\alpha_p$.

### 15.3 Matrix equations and stabilizers

Suppose $G\hookrightarrow\mathrm{GL}_n$ acts on an affine scheme $X$ and $x:S\to X$ is a section. Its stabilizer is the fiber product expressing the equality $gx=x$:

$$
\operatorname{Stab}_G(x)=G\times_{X,x}S,
$$

where $G\to X$ is the orbit map $g\mapsto gx$. When $X$ is separated, this is a closed subgroup scheme. In coordinates, its ideal is generated by the differences between the coordinate functions of the orbit map and those of the fixed section.

For the standard action of $\mathrm{GL}_n$ on affine $n$-space, the stabilizer of the first basis vector is defined by

$$
x_{11}-1,\quad x_{i1}\ (i>1).
$$

The Hopf-ideal condition relative to the stabilizer law follows conceptually from the fiber-product construction; a direct coproduct calculation gives the same result. This illustrates a useful division of labor: geometry proves subgroup closure, while coordinates give an explicit algebra.

### 15.4 Scheme-theoretic closure over a DVR

Let $R$ be a DVR with fraction field $K$, and let $G=\operatorname{Spec}A$ be affine and flat over $R$. If $H_K\hookrightarrow G_K$ is a closed subgroup with Hopf ideal $I_K\subseteq A_K$, its scheme-theoretic closure in $G$ is defined by

$$
I=A\cap I_K\subseteq A_K.
$$

Because $A/I$ injects into $A_K/I_K$, it is $R$-torsion-free. If it is finite over $R$, it is
therefore finite free. Put $C=A/I$. The quotient $A\to C$ then splits as a map of $R$-modules,
so the kernel of

$$
A\otimes_RA\longrightarrow C\otimes_RC
$$

is exactly the image of $I\otimes_RA+A\otimes_RI$. For $x\in I$, the image of $\Delta(x)$ in
$C\otimes_RC$ vanishes after tensoring with $K$, because $I_K$ is a Hopf ideal. The module
$C\otimes_RC$ is torsion-free, so the image already vanishes over $R$. Hence

$$
\Delta(I)\subseteq I\otimes A+A\otimes I
$$

inside $A\otimes_RA$. Likewise $\varepsilon(x)$ vanishes in $K$ and hence in $R$, while the
class of $S(x)$ in the torsion-free module $C$ vanishes after tensoring with $K$ and hence is
zero. Thus $I$ is a Hopf ideal. We have proved the precise statement: if the contracted quotient
$A/I$ is finite over the DVR, then the schematic closure is a finite locally free subgroup.

The finiteness qualification is important. An arbitrary subalgebra of a finite-dimensional
generic fiber need not be finite over $R$. If $G$ itself is finite locally free, finiteness of
$C$ is automatic because it is a quotient of $A$, so the closure theorem applies without an
extra condition. Over a general base, contraction need not make the quotient flat and the
torsion-free argument above is unavailable. A systematic use of finite-flat schematic closure
belongs to the next stage of the subject.

## 16. The translation dictionary for torsion subgroup schemes

### 16.1 The basic dictionary

Let $G=\operatorname{Spec}A$ and $H=\operatorname{Spec}B$ be affine group schemes over $S=\operatorname{Spec}R$. The reusable translations are:

$$
\begin{array}{c|c}
\text{group-scheme statement}&\text{Hopf-algebra statement}\\
\hline
G\times_SH&A\otimes_RB\\
G\to H&B\to A\\
H\hookrightarrow G\text{ closed}&A\twoheadrightarrow B\\
H\subseteq G\text{ closed subgroup}&\ker(A\to B)\text{ is a Hopf ideal}\\
\ker(G\to H)&A/Af^*(B^+)\\
G\text{ commutative}&\tau\Delta_A=\Delta_A\\
G_{R'}&A\otimes_RR'\\
G\text{ finite locally free}&A\text{ finite projective over }R
\end{array}
$$

Multiplication, identity, and inverse always pull back to $\Delta$, $\varepsilon$, and $S$. On points,

$$
(xy)(a)=\sum x(a_{(1)})y(a_{(2)}),\qquad
1(a)=\varepsilon(a),\qquad x^{-1}(a)=x(S(a)).
$$

These formulas fix the variance and tensor-factor conventions in every calculation.

### 16.2 The exactness checklist

To claim an exact sequence

$$
1\to H\to G\to Q\to1,
$$

one should verify, in order:

1. $H$ is the scheme-theoretic kernel, not merely the kernel on geometric points;
2. $G\to Q$ is faithfully flat, so it is locally surjective in the chosen topology;
3. $Q$ represents the associated sheaf quotient;
4. equivalently in the affine torsor setting, invariants give $\mathcal O(Q)$ and the canonical map

$$
\mathcal O(G)\otimes_{\mathcal O(Q)}\mathcal O(G)
\longrightarrow
\mathcal O(G)\otimes_R\mathcal O(H)
$$

is an isomorphism.

Surjectivity on $T$-points is not required and usually fails. If all groups are finite locally free, ranks multiply. Base change preserves the exact torsor sequence.

### 16.3 Constructing torsion

For a commutative affine group scheme $G$ and $n\ge1$, the torsion subgroup scheme is

$$
G[n]=\ker([n]:G\to G).
$$

It is automatically representable, affine, closed, commutative, and compatible with every base change. If $[n]^*:A\to A$ is the convolution power map, then

$$
\mathcal O(G[n])=A/A[n]^*(A^+).
$$

What is not automatic is finite local freeness. To prove that, one must show the quotient algebra is finite projective over $R$—for example by a direct monic presentation, by flatness plus finite presentation, by torsion-freeness over a DVR, or by faithfully flat descent. Once this is done, rank and fiber length are stable under arbitrary base change.

If $[n]:G\to G$ is finite locally free and faithfully flat, it is a $G[n]$-torsor and gives a sheaf-exact sequence

$$
0\to G[n]\to G\xrightarrow{[n]}G\to0.
$$

This statement does not assert that every $T$-point is globally divisible by $n$.

### 16.4 What geometric fibers can and cannot prove

Geometric fibers are useful for computing rank, detecting reduced étale behavior under suitable hypotheses, and recognizing familiar group schemes after scalar extension. They cannot, by themselves, distinguish all infinitesimal subgroup schemes or prove a global quotient flat.

The correct hierarchy is:

$$
\text{geometric points}
\quad<\quad
\text{geometric fibers as schemes}
\quad<\quad
\text{the family over the base}.
$$

At the first level, $\alpha_p$ and $\mu_p$ both look trivial. At the second, their nilpotent algebras and coproducts distinguish them. At the third, one also sees whether the rank is constant, whether torsion appears from the base, and whether formation commutes with specialization.

Thus a pointwise calculation should be converted into an equality of natural transformations, a coordinate-ring identity, or a faithfully flat descent statement before it is used as a structural proof.

### 16.5 A working protocol

Affine group schemes are groups whose elements may be evaluated in every algebra over the base. The functor of points makes this idea concrete, and elementary Yoneda reasoning turns natural pointwise laws back into geometric morphisms. Passing to coordinate rings reverses every arrow: products become tensor products, multiplication becomes comultiplication, the identity becomes a counit, and inversion becomes the uniquely determined antipode.

That reversal is not merely a formal dictionary. It makes subgroup equations into Hopf ideals, kernels into quotients by pulled-back augmentation ideals, commutativity into cocommutativity, and base change into tensor extension. It also exposes the limits of naive constructions. Images require purity or field hypotheses to inherit a Hopf structure reliably; closed subgroups of finite flat groups need a flatness argument to remain finite flat; quotients require effective descent, not just an invariant ring or a pointwise orbit set.

The faithfully flat topology is the natural setting for exactness because roots, coset representatives, and torsor sections often exist only after a cover. Torsors express the needed effectivity through one decisive isomorphism,

$$
G\times_SH\simeq G\times_QG,
$$

whose coordinate form is the canonical Hopf–Galois map. Under finite locally free hypotheses, this geometry becomes finite projective algebra: ranks multiply in exact sequences, arbitrary base change preserves the objects, and descent recovers them from split calculations.

Finally, infinitesimal examples show why the scheme structure cannot be discarded. In characteristic $p$, $\mu_p$ and $\alpha_p$ may have only the identity as a geometric point while retaining rank $p$, nonzero cotangent space, and distinct Hopf laws. Torsion subgroup schemes must therefore be built as scheme-theoretic kernels and judged by their coordinate algebras, not by sets of points. With that principle in place, the passage from a commutative group object to its finite torsion kernels becomes a controlled sequence of operations: form the multiplication morphism, take its affine kernel, prove finite projectivity under the relevant hypotheses, and use Hopf algebra, rank, base change, and faithfully flat exactness to carry the resulting structure through arithmetic families.

The dictionary developed so far constructs and compares affine group schemes. Two further layers make it more useful. Powers of the augmentation ideal retain higher-order information around the identity, and linear functionals on those neighborhoods turn the group law into an algebra of infinitesimal operators. Representations, torsors, and quotients then place the same formulas into a descent framework.

## 17. The augmentation filtration

The cotangent space $I/I^2$ records only the first infinitesimal neighborhood of the identity. That is enough to count tangent directions, but it cannot distinguish group laws that agree to first order. The full sequence

$$
A/I\leftarrow A/I^2\leftarrow A/I^3\leftarrow\cdots
$$

remembers successively higher jets. Its compatibility with comultiplication is the reason one can multiply finite-order distributions and recover the Lie bracket from a generally noncommutative group.

### 17.1 Why first order is not enough

Let $A$ be the coordinate Hopf algebra of $G$ and $I=\ker\varepsilon$. The quotient $A/I$ is $R$, the coordinate algebra of the identity section. The quotient $A/I^{n+1}$ is the algebraic $n$th infinitesimal neighborhood of that section. A map from it to an $R$-algebra $C$ is a point whose displacement from the identity is nilpotent to the indicated order.

The powers $I^n$ need not be Hopf ideals. Multiplication of two points close to the identity can mix their orders, so an individual infinitesimal neighborhood need not be a subgroup. What is true is filtered compatibility: comultiplication of an element vanishing to order $n$ is a sum of terms whose orders in the two factors add to at least $n$.

The distinction appears already for $\mathbf G_m$. Put $u=T-1$. Then

$$
\Delta(u)=u\otimes1+1\otimes u+u\otimes u.
$$

Modulo terms of total degree at least two, this is the additive formula. Thus $\mathbf G_m$ and $\mathbf G_a$ have the same first-order group law. The product term first appears at second order and separates them.

### 17.2 Coproduct estimates for powers of the augmentation ideal

The basic estimate is

$$
\Delta(I)\subseteq I\otimes_RA+A\otimes_RI.
$$

Using the splitting $A=R\oplus I$, for $x\in I$ one may write

$$
\Delta(x)=x\otimes1+1\otimes x+\widetilde\Delta(x),
\qquad \widetilde\Delta(x)\in I\otimes_RI.
$$

The counit identities prove this formula. The last term is the reduced coproduct.

Because $\Delta$ is an algebra map, multiplying $n$ such expressions proves

$$
\Delta(I^n)\subseteq
\sum_{a+b=n} I^a\otimes_R I^b,
$$

where $I^0=A$ and each tensor product denotes its image in $A\otimes_RA$. Terms of larger total degree already lie in a displayed summand after exponents are lowered. No flatness is used.

The antipode preserves the filtration. Since $S(I)\subseteq I$ and $S$ is multiplicative for a commutative coordinate algebra,

$$
S(I^n)\subseteq I^n.
$$

Consequently inversion acts on every quotient $A/I^{n+1}$. The coproduct estimate also gives compatible maps

$$
A/I^{r+s+1}\longrightarrow
(A/I^{r+1})\otimes_R(A/I^{s+1}).
$$

These are the source of the order-addition law for distributions.

### 17.3 The associated graded algebra

Package the layers into

$$
\operatorname{gr}_I(A)=\bigoplus_{n\ge0}I^n/I^{n+1}.
$$

Its degree-zero part is $R$, and its degree-one part is $I/I^2$. Multiplication gives canonical surjections

$$
\operatorname{Sym}^n_R(I/I^2)\longrightarrow I^n/I^{n+1}.
$$

They need not be isomorphisms. Such an isomorphism is a regularity statement about the identity embedding, not a formal property of a Hopf algebra. For a smooth group of relative dimension $d$, locally at the identity the completed algebra behaves like a power-series algebra in $d$ variables and the associated graded is symmetric. A nonreduced finite group has extra relations.

The coproduct estimate always gives a graded coproduct into the associated graded of the tensor-product filtration. When the natural comparison with $\operatorname{gr}_I(A)\otimes_R\operatorname{gr}_I(A)$ is an isomorphism—for example under suitable projectivity of the graded pieces—this makes the associated graded a graded bialgebra. On degree one the induced coproduct is primitive:

$$
\overline x\longmapsto\overline x\otimes1+1\otimes\overline x.
$$

The reduced term has total degree two. This is why every group law linearizes to addition on its tangent space.

For $\mu_p$ in characteristic $p$, with $u=T-1$, both $\mu_p$ and $\alpha_p$ have graded algebra $k[u]/(u^p)$. Their distinction remains in the filtered coproduct: the term $u\otimes u$ is present for $\mu_p$ and absent for $\alpha_p$.

### 17.4 Completion at the identity

The inverse limit

$$
\widehat A_I=\varprojlim_n A/I^{n+1}
$$

is the algebra of formal functions near the identity. It is a topological algebra, and the coproduct extends continuously to

$$
\widehat\Delta:\widehat A_I\longrightarrow
\widehat A_I\,\widehat\otimes_R\,\widehat A_I.
$$

Here the completed tensor product means the completion of $A\otimes_RA$ for the total filtration

$$
F^n(A\otimes_RA)=\sum_{r+s=n}I^r\otimes_RI^s.
$$

The estimate of §17.2 is exactly what gives the continuous map to this completion. This is the
coordinate form of completion along the identity.

Completion notation hides hypotheses. Tensor product need not commute with inverse limit, completion need not preserve exact sequences, and base change of a completion need not equal completion after base change. Finite presentation, noetherian hypotheses, or explicit power-series coordinates repair these issues when needed. Here completion only synthesizes the finite quotients already constructed.

If $G$ is finite and connected over a field, $A$ is local Artinian and $I$ is nilpotent, so the completion equals $A$. If $G$ is a nontrivial constant finite group, $I$ contains idempotents and is not nilpotent; completion discards every component except the identity factor.

### 17.5 Calculations in the standard examples

For $\mathbf G_a$,

$$
A/I^{n+1}=R[T]/(T^{n+1}),\qquad \widehat A_I=R[[T]],
$$

with formal law $T\mapsto T\otimes1+1\otimes T$. For $\mathbf G_m$, writing $u=T-1$ gives the same underlying power-series algebra but law

$$
u\longmapsto u\otimes1+1\otimes u+u\otimes u.
$$

If all positive integers are invertible in $R$, the series

$$
\log(1+u)=u-\frac{u^2}{2}+\frac{u^3}{3}-\cdots
$$

changes the multiplicative formal law to the additive one. Over $\mathbb Z$ or in positive characteristic, denominators obstruct this identification.

For $D(M)$, the augmentation ideal is generated by the elements $X^m-1$, and relations in $M$ become nonlinear relations among them. For a constant group, completion isolates the identity immediately. These opposite behaviors anticipate the contrast between character-type and point-type finite groups.

## 18. Distributions supported at the identity

Higher infinitesimal neighborhoods become easier to use after dualizing their functions. A distribution is a linear rule that reads only a finite jet at the identity. Convolution transfers the group law to a multiplication of such rules and places the Lie algebra inside an algebra of infinitesimal operators.

### 18.1 Finite-order functionals

Define

$$
\operatorname{Dist}_n(G)=
\{\lambda\in\operatorname{Hom}_R(A,R):\lambda(I^{n+1})=0\}
=\operatorname{Hom}_R(A/I^{n+1},R).
$$

There is an increasing filtration

$$
R\varepsilon=\operatorname{Dist}_0(G)
\subseteq\operatorname{Dist}_1(G)\subseteq\cdots,
$$

and

$$
\operatorname{Dist}(G)=\bigcup_{n\ge0}\operatorname{Dist}_n(G)
$$

inside $\operatorname{Hom}_R(A,R)$. No projectivity is needed for the definition. Projectivity matters when dualization is expected to commute with base change.

An order-zero distribution is a scalar multiple of evaluation at the identity. An order-one distribution has the form $r\varepsilon+D$, where $D$ is an augmentation derivation. Thus tangent vectors are precisely the order-one distributions vanishing on $1$.

### 18.2 Convolution and the order filtration

Define

$$
(\lambda*\mu)(a)=(\lambda\otimes\mu)(\Delta(a)).
$$

Coassociativity makes convolution associative and $\varepsilon$ is its identity. If $\lambda$ has order at most $r$ and $\mu$ order at most $s$, then

$$
\lambda*\mu\in\operatorname{Dist}_{r+s}(G).
$$

Indeed, every term in the coproduct of an element of $I^{r+s+1}$ lies in $I^i\otimes I^j$ with $i+j=r+s+1$. Either $i\ge r+1$ or $j\ge s+1$, so one functional kills it.

The antipode acts by $\lambda\mapsto\lambda\circ S$. If $G$ is commutative, its coproduct is cocommutative and convolution is commutative. If $G$ is noncommutative, the distribution algebra can be noncommutative even though $A$ is a commutative algebra.

For finite locally free $G$, the full dual $A^\vee$ is finite projective and convolution makes it an associative algebra. Distributions form a filtered subalgebra. They need not fill $A^\vee$, since functionals supported at the identity do not see other open-and-closed components.

### 18.3 Order one and the Lie bracket

For augmentation derivations $D,E:A\to R$, put

$$
[D,E]=D*E-E*D.
$$

Although each product can have order two, their commutator again has order one. Expanding $\Delta(ab)$ and using the derivation identities shows that the mixed second-order terms cancel and

$$
[D,E](ab)=\varepsilon(a)[D,E](b)+\varepsilon(b)[D,E](a).
$$

Thus convolution commutator defines the Lie bracket. Associativity supplies the Jacobi identity. If $G$ is commutative, the bracket vanishes.

For $\mathrm{GL}_n$, an augmentation derivation is the first-order displacement of the universal matrix from the identity. Convolution commutator gives $XY-YX$. In favorable smooth settings the associated graded distribution algebra is symmetric on the Lie algebra. Positive characteristic introduces divided powers, so no unrestricted comparison is asserted here.

### 18.4 Finite group schemes and the local factor at the identity

Suppose $k$ is algebraically closed and $G$ finite. Its coordinate algebra is a product of local Artinian algebras, and the identity selects one factor $A_e$. Powers of $I$ eventually kill the maximal ideal in $A_e$ but act as the unit ideal on every other factor. Therefore

$$
\operatorname{Dist}(G)\cong A_e^\vee,
\qquad
\dim_k\operatorname{Dist}(G)=\operatorname{length}(G^0).
$$

For a constant finite group this dimension is one. For $\alpha_p$ and $\mu_p$ it is $p$.

For $\alpha_p$, let $d_i$ be dual to $T^i$ for $0\le i<p$. Since

$$
\Delta(T^n)=\sum_{a+b=n}\binom{n}{a}T^a\otimes T^b,
$$

one obtains

$$
d_a*d_b=\binom{a+b}{a}d_{a+b}
$$

when $a+b<p$, and zero otherwise. This truncated divided-power algebra shows why the first derivative alone does not control positive-characteristic infinitesimal groups.

### 18.5 Base change and finiteness hypotheses

There is a natural map

$$
\operatorname{Dist}_n(G)\otimes_RR'
\longrightarrow\operatorname{Dist}_n(G_{R'}).
$$

It is an isomorphism if $A/I^{n+1}$ is finite projective over $R$, because duals of finite projective modules commute with arbitrary base change. Without that hypothesis it can fail: Hom does not generally commute with scalar extension.

The safe method is bounded. Fix $n$, prove projectivity of the corresponding infinitesimal quotient, and only then use duality or base change. Passing to the union over all orders is an additional filtered-colimit step and must not be hidden inside a finite argument.

## 19. Representations and comodules

An affine group scheme acts on algebraic families, not merely on sets of points. Linear actions are especially important because they turn geometric symmetry into module theory. Once again arrows reverse: a group action on a module-valued functor is encoded by a coaction of the coordinate Hopf algebra.

### 19.1 Why representations become coactions

Let $G=\operatorname{Spec}H$ and let $M$ be an $R$-module. A linear representation on $M$ is a
coaction

$$
\delta:M\longrightarrow M\otimes_RH
$$

satisfying

$$
(\delta\otimes\operatorname{id})\delta
=(\operatorname{id}\otimes\Delta)\delta,
\qquad
(\operatorname{id}\otimes\varepsilon)\delta=\operatorname{id}_M.
$$

It induces, functorially in every $R$-algebra $C$, an action of $G(C)$ on $M\otimes_RC$ by
$C$-linear automorphisms. Conversely, when $M$ is finite locally free, every such functorial
linear action is represented by a morphism $G\to\mathrm{GL}(M)$ and hence yields this coaction.
For an arbitrary module, taking the coaction as the definition avoids imposing an unproved
representability assertion on its automorphism functor.

If $\delta(m)=\sum m_{(0)}\otimes m_{(1)}$ and $g:H\to C$, then

$$
g\cdot(m\otimes c)=
\sum m_{(0)}\otimes c\,g(m_{(1)}).
$$

Coassociativity expresses multiplication of points, while the counit gives the identity. The antipode supplies inverse operators.

### 19.2 Matrix coefficients

If $M$ is free with basis $e_1,\ldots,e_n$, write

$$
\delta(e_j)=\sum_i e_i\otimes a_{ij}.
$$

Then

$$
\Delta(a_{ij})=\sum_k a_{ik}\otimes a_{kj},
\qquad \varepsilon(a_{ij})=\delta_{ij}.
$$

The matrix $(a_{ij})$ is invertible with inverse obtained from the antipode. Hence $x_{ij}\mapsto a_{ij}$ defines $G\to\mathrm{GL}_n$. Conversely, such a morphism gives a coaction. For finite projective $M$, dual bases make the same construction locally and it glues.

Tensor products and duals follow from Hopf structure. The coefficients on $M\otimes N$ multiply in $H$, while the antipode gives the contragredient action on $M^\vee$. The regular representation is $\Delta:H\to H\otimes_RH$.

### 19.3 Invariant vectors and equivariant maps

The invariant submodule is

$$
M^G=\{m\in M:\delta(m)=m\otimes1\}.
$$

It is an equalizer, so flat base change preserves it under the usual finite-presentation hypotheses, whereas arbitrary base change need not. A map $f:M\to N$ is equivariant when

$$
(f\otimes\operatorname{id})\delta_M=\delta_Nf.
$$

Kernels of equivariant maps inherit coactions when tensoring with $H$ preserves the kernel; flatness of $H$ over $R$ suffices. Cokernels behave more readily because tensor product is right exact.

If $P\to X$ is a $G$-torsor and $M$ finite locally free, descent of the trivial bundle on $P$ with its equivariant structure produces the associated vector bundle on $X$. This is the geometric link between representations and torsors.

### 19.4 Constant and diagonalizable groups

For a constant finite group $\underline\Gamma$, a comodule is an ordinary action of $\Gamma$ on $M$. Evaluation at components recovers the operators and the coproduct forces the group law.

For $D(L)$, where $H=R[L]$, a comodule is an $L$-graded module

$$
M=\bigoplus_{\ell\in L}M_\ell,
$$

with $\delta(m)=m\otimes X^\ell$ on $M_\ell$. Conversely, the basis $X^\ell$ uniquely separates a coaction into finite-support weight components. Invariants are the weight-zero part. This remains valid for infinite $L$ because each coaction value is a finite sum.

In particular, representations of $\mathbf G_m=D(\mathbb Z)$ are $\mathbb Z$-graded modules and representations of $\mu_n=D(\mathbb Z/n\mathbb Z)$ are cyclically graded modules.

### 19.5 Additive and multiplicative one-parameter actions

A $\mathbf G_a$-coaction can be written

$$
\delta(m)=\sum_{n\ge0}D_n(m)\otimes T^n,
$$

with finitely many nonzero terms for each $m$. Its identities say

$$
D_0=\operatorname{id},\qquad
D_aD_b=\binom{a+b}{a}D_{a+b}.
$$

If $R$ contains the rational numbers, then $D_n=N^n/n!$ for a locally nilpotent operator $N=D_1$. In positive characteristic the higher $D_n$ are not determined by $D_1$; suppressing them loses divided-power information. For $\alpha_p$, only $0\le n<p$ remain.

By contrast a $\mathbf G_m$-action is a grading. Additive one-parameter symmetry is therefore governed by iterative operators, while multiplicative symmetry is governed by weights. This conceptual distinction mirrors primitive versus group-like elements in their coordinate Hopf algebras.

## 20. Torsors as descent objects

The definition of a torsor in Chapter 8 is concise; its content emerges when one trivializes it over a cover and watches the trivializations disagree. That disagreement is a cocycle. The cocycle viewpoint explains why quotients are sheaves rather than pointwise orbit sets and how group schemes create twisted forms.

### 20.1 Trivial torsors and local triviality

For an $S$-scheme $X$, the projection

$$
X\times_SG\longrightarrow X
$$

with right multiplication on the second factor is the trivial $G$-torsor. The inverse of its
canonical torsor map is

$$
(X\times_SG)\times_X(X\times_SG)\longrightarrow
(X\times_SG)\times_SG.
$$

A point $(x,g_1,g_2)$ is sent to $(x,g_1,g_1^{-1}g_2)$. This specifies the direction and the
factor order.

A section $s:X\to P$ of a $G$-torsor trivializes it by $(x,g)\mapsto s(x)g$. The inverse sends $p$ to the unique $g$ with $p=s(\pi(p))g$. The torsor identity guarantees existence and uniqueness as a morphism, not merely on points.

Every torsor becomes trivial after pulling back along its own faithfully flat cover $P\to X$. Global nontriviality is therefore encoded by how two trivializations compare over $P\times_XP$.

### 20.2 Cocycles from a chosen cover

Let $U\to X$ be a faithfully flat cover over which $P$ has a section. On $U_1=U\times_XU$, the two pulled-back sections differ by a unique

$$
g_{12}\in G(U_1).
$$

On $U\times_XU\times_XU$, uniqueness gives

$$
g_{13}=g_{12}g_{23}.
$$

Changing the section by $h\in G(U)$ changes the cocycle to $h_1^{-1}g_{12}h_2$. Conversely, effective faithfully flat descent glues $U\times G$ from such a cocycle. Thus torsors are precisely descent data for locally trivial principal homogeneous spaces.

This also explains the topology. Requiring a global section would classify only trivial torsors. Requiring an étale section would exclude infinitesimal examples such as Frobenius with kernel $\alpha_p$.

### 20.3 The affine descent calculation

Take $X=\operatorname{Spec}B$, $P=\operatorname{Spec}A$, and $G=\operatorname{Spec}H$. Under the canonical isomorphism

$$
\beta:A\otimes_BA\xrightarrow{\sim}A\otimes_RH,
$$

the maps $a\mapsto a\otimes1$ and $a\mapsto1\otimes a$ become the trivial coaction and the given coaction. Faithfully flat descent therefore gives

$$
B=\operatorname{Eq}(A\rightrightarrows A\otimes_BA)
\cong A^{\operatorname{co}H}.
$$

The same equalizer recovers modules from equivariant modules on $P$. Exactness here uses faithful flatness; a merely surjective map on spectra is not enough.

This dictates the proof strategy for an affine quotient. Construct a candidate invariant algebra $B$, prove $A$ faithfully flat over it, and prove the canonical map is an isomorphism. Only then identify $\operatorname{Spec}B$ with the sheaf quotient.

### 20.4 Kummer and Artin--Schreier torsors

Let $a\in B^\times$. The algebra

$$
A=B[z]/(z^n-a)
$$

is finite free of rank $n$, and $\mu_n$ acts by $z\mapsto z\otimes T$. Since $z$ is a unit, the ratio of the two roots identifies the canonical map with an isomorphism. Thus $\operatorname{Spec}A\to\operatorname{Spec}B$ is a $\mu_n$-torsor. No invertibility of $n$ is required for faithful flatness. If $n$ is invertible it is finite étale; otherwise it can be infinitesimal.

In characteristic $p$,

$$
B[z]/(z^p-z-a)
$$

is a torsor under the constant group $\underline{\mathbb Z/p\mathbb Z}$ by translation and is finite étale because the derivative is $-1$. By contrast

$$
B[z]/(z^p-a)
$$

with the translation action of $\alpha_p$ is finite faithfully flat and generally not étale. Equations of the same degree can therefore carry very different group-scheme symmetries.

### 20.5 Twisting and forms

Let $P$ be a right $G$-torsor and let $G$ act on an affine scheme $X$ on the left. The contracted product, when representable, is

$$
P\times^G X=(P\times_SX)/G,
$$

where $(p,x)g=(pg,g^{-1}x)$. After pullback to $P$ it becomes $P\times_SX$, so it is a form of $X$ obtained by twisting descent data by the torsor cocycle.

For a finite locally free representation this gives an associated vector bundle. For an algebra with a compatible action it gives a descended algebra and hence an affine scheme. Effective descent from Book 44 supplies representability in these finite projective and affine cases. The notation alone does not prove representability for an arbitrary contracted product.

## 21. Representable quotients and the boundary of the theory

Quotients are where existence becomes a theorem. This chapter separates the universal property, the algebraic construction, and the hypotheses connecting them, then collects the exact base-change statements used in applications.

### 21.1 Universal properties before coordinates

For a right action of $H$ on $G$, a categorical quotient $q:G\to Q$ satisfies

$$
\operatorname{Hom}(Q,X)
\cong\{f:G\to X:f(gh)=f(g)\}
$$

naturally in $X$. A sheaf quotient asks in addition that every local orbit have a local representative and that two representatives agree precisely when they differ locally by $H$. The identity

$$
G\times_SH\cong G\times_QG
$$

expresses this effectiveness.

If an affine quotient is $Q=\operatorname{Spec}B$, invariant functions force $B\to A^{\operatorname{co}H}$. For an effective affine torsor it is an isomorphism. Without the torsor hypotheses, $\operatorname{Spec}(A^{\operatorname{co}H})$ can have an affine categorical property without representing the orbit sheaf. One must name the universal property being claimed.

### 21.2 Normality and descended multiplication

Assume $G\to Q$ is an $H$-torsor quotient and $H$ normal. Then

$$
(g_1h_1)(g_2h_2)=g_1g_2(g_2^{-1}h_1g_2)h_2,
$$

and the last two factors lie in $H$. Multiplication is therefore constant on cosets and descends. Identity and inversion descend similarly, making $Q$ a group scheme.

Conversely, the kernel of any group morphism is normal. Thus normality is exactly what makes the quotient group law descend. In coordinates it says the invariant subalgebra is stable under the Hopf operations. Descending an already represented multiplication is often cleaner than proving that stability directly, because the direct calculation may require tensor purity.

### 21.3 Images, closures, and purity

The scheme-theoretic image of $f:G\to H$ is cut out by $\ker f^*$ and is the smallest closed subscheme through which $f$ factors. The sheaf image consists of sections locally lifted from $G$. The closure of the image of geometric points remembers neither nilpotents nor descent.

Over a field, the scheme-theoretic image of an affine group morphism is a closed subgroup because tensoring preserves injections. Over a general base, purity of

$$
\mathcal O(\operatorname{SIm}f)\hookrightarrow\mathcal O(G)
$$

is sufficient. Without it, tensor products can create kernel elements and the defining ideal need not visibly satisfy the coproduct condition.

Schematic closure has different input. Over a DVR, a generic-fiber subgroup is closed in an integral model by intersecting ideals. Saturation proves torsion-freeness of the quotient and, once finiteness is known, finite local freeness. Closure and image should not be conflated even when one is later applied to the other.

### 21.4 A base-change ledger

The following commute with arbitrary base change: products and fiber products; kernels and equalizers defined by fiber products; closed subgroups defined by extended Hopf ideals; finite local freeness and rank; represented torsors and their sheaf-exact sequences.

Other constructions require hypotheses. Scheme-theoretic images commute with flat base change, not unconditionally with nonflat base change. Raw invariant rings commute when the defining equalizer is preserved. Bounded distributions commute when the infinitesimal quotient is finite projective. Generic-fiber closure requires suitable saturation and flatness. Connected components and reduced subschemes can change after inseparable extension.

This ledger prevents the common invalid step of tensoring an exact sequence whose exactness was never known to survive tensor product.

### 21.5 Failure patterns

Frobenius on $\mathbf G_a$ can be bijective on geometric points while having kernel $\alpha_p$. The group $\mu_p$ can have one geometric point and rank $p$. A closed subgroup of a finite locally free group is finite but needs a flatness theorem to be finite locally free over a general base. An invariant ring need not represent an orbit sheaf. A point of a quotient need not lift globally, as $u\mapsto u^n$ on units shows.

Each failure has one repair: replace points by functors or coordinate rings; replace cardinality by rank; prove flatness of the quotient module; verify the canonical torsor map; and replace global lifting by faithfully flat local lifting. These repairs all express the same principle—control the family before trusting its fibers.

## 22. Extended calculations and structural examples

The general theory is best tested where every arrow can be written down. The four fundamental families—constant, diagonalizable, additive, and multiplicative—exercise every variance convention. A semidirect product then shows how noncommutativity enters the coproduct.

### 22.1 Constant groups and locally constant points

For a finite group $\Gamma$, a point of $\underline\Gamma$ over $C$ is a family of orthogonal idempotents $(c_\gamma)$ with sum $1$. It partitions $\operatorname{Spec}C$ into open-and-closed pieces labeled by $\Gamma$. Multiplication labels an intersection by the product of its labels.

A homomorphism $u:\Gamma\to\Lambda$ pulls functions back by

$$
R^\Lambda\longrightarrow R^\Gamma,\qquad f\longmapsto f\circ u.
$$

Its kernel group scheme is $\underline{\ker u}$. If $u$ is surjective, the map is finite locally free and faithfully flat, with quotient $\underline\Lambda$. The rank formula recovers the ordinary order formula over every connected component of the base.

If $\Gamma$ is nonabelian, $R^\Gamma$ is still a commutative algebra. Noncommutativity appears in

$$
\Delta(e_\eta)=\sum_{\gamma\delta=\eta}e_\gamma\otimes e_\delta,
$$

which is not fixed by the tensor flip.

### 22.2 Diagonalizable groups and character lattices

For $D(M)$, a homomorphism $M\to N$ gives $D(N)\to D(M)$. In particular the exact sequence

$$
\mathbb Z\xrightarrow{n}\mathbb Z\to\mathbb Z/n\mathbb Z\to0
$$

becomes

$$
1\to\mu_n\to\mathbf G_m\xrightarrow{[n]}\mathbf G_m\to1.
$$

If $M=\mathbb Z^r$, then $D(M)=\mathbf G_m^r$. Integer matrices define Laurent-monomial maps of split tori. Smith normal form decomposes their kernels and quotients into split tori and factors $\mu_d$. This is a lattice calculation with arrows reversed.

When $M$ is finite, $D(M)$ is finite locally free of rank $|M|$ but can be nonreduced where the residue characteristic divides $|M|$. Diagonalizable means governed by characters, not reduced.

### 22.3 Additive polynomials and their kernels

In characteristic $p$, an additive polynomial

$$
P(T)=a_0T+a_1T^p+\cdots+a_rT^{p^r}
$$

defines $\mathbf G_a\to\mathbf G_a$. If $a_r$ is a unit, its kernel is finite locally free of rank $p^r$ after normalizing the leading coefficient. Its cotangent module is $R/(a_0)$, since the linear term is $a_0T$.

The map $T^p-T$ has constant kernel $\underline{\mathbb F_p}$ and is étale because its derivative is $-1$. The map $T^p$ has kernel $\alpha_p$, only one geometric root, and a tangent direction. Equal degree and faithful flatness do not distinguish étale from infinitesimal behavior.

Composition of additive polynomials can be noncommutative when coefficients are moved by Frobenius. Thus the endomorphism algebra of the commutative group $\mathbf G_a$ can itself be noncommutative.

### 22.4 Multiplicative isogenies

The map $[n]:\mathbf G_m\to\mathbf G_m$ corresponds to

$$
R[V,V^{-1}]\longrightarrow R[T,T^{-1}],\qquad V\longmapsto T^n.
$$

The target is free of rank $n$ with basis $1,T,\ldots,T^{n-1}$. Hence $[n]$ is a finite locally free $\mu_n$-torsor over every base. Its derivative at the identity is multiplication by $n$, so it is étale exactly where $n$ is invertible.

In characteristic $p$, the kernel of $[p]$ has equation $(T-1)^p=0$. Rank remains $p$ while the geometric points collapse to one. This single family separates faithful flatness from étaleness, sheaf surjectivity from surjectivity on units, and rank from point count.

### 22.5 Semidirect products and noncommutativity

If $H$ acts on $N$ by group automorphisms, the semidirect product has multiplication

$$
(n,h)(n',h')=(n(h\cdot n'),hh')
$$

and a split exact sequence $1\to N\to N\rtimes H\to H\to1$.

Take $N=\mathbf G_a$, $H=\mathbf G_m$, and $h\cdot n=hn$. With additive coordinate $X$ and invertible coordinate $T$,

$$
\Delta(T)=T\otimes T,
\qquad
\Delta(X)=X\otimes1+T\otimes X,
$$

$$
\varepsilon(T)=1,\quad\varepsilon(X)=0,
\qquad
S(T)=T^{-1},\quad S(X)=-T^{-1}X.
$$

The coproduct of $X$ is not fixed by the tensor flip, so the group is noncommutative. These formulas directly encode composition and inversion of affine transformations $x\mapsto hx+n$.

## 23. The affine group-scheme theorem

The preceding chapters now assemble into a theorem whose clauses distinguish formal constructions from those needing finiteness, flatness, purity, or representability. This is the reusable endpoint of the book.

### 23.1 Statement

**Theorem 23.1 (affine group-scheme structure theorem).** Let $R$ be a commutative ring.

1. Affine group schemes over $\operatorname{Spec}R$ are anti-equivalent to commutative $R$-Hopf algebras. Products correspond to tensor products, morphisms reverse direction, and scalar extension is tensor extension.
2. Closed subgroup schemes of $\operatorname{Spec}A$ correspond to Hopf ideals. Kernels and equalizers exist as affine closed subgroups and commute with arbitrary base change.
3. The scheme-theoretic image exists for every affine morphism. It is a closed subgroup over a field, or when its coordinate inclusion is pure, and it commutes with flat base change.
4. Affine actions correspond to coactions, linear representations to comodules, and affine torsors to faithfully flat extensions with bijective canonical map.
5. If $H\hookrightarrow G$ is finite locally free and $G$ affine, the faithfully flat sheaf quotient $G/H$ is affine; $G\to G/H$ is a finite locally free $H$-torsor. If $H$ is normal, the quotient is an affine group scheme.
6. Sheaf exactness is encoded by a scheme-theoretic kernel, faithful flatness, invariants, and the canonical torsor isomorphism. It survives arbitrary base change but need not give surjectivity on points.
7. If $A$ is finite projective, $G$ is finite locally free of locally constant positive rank. Ranks multiply componentwise in finite locally free exact sequences.
8. The augmentation ideal controls infinitesimal structure. Its powers define higher neighborhoods, $I/I^2$ gives the cotangent module, and finite-order distributions form a filtered convolution algebra. Base change of their duals requires projectivity of the bounded quotients.

No stronger assertion is implicit: a subgroup need not be flat over an arbitrary base, an invariant ring need not represent an orbit sheaf, and geometric bijectivity need not imply isomorphism.

### 23.2 Proof architecture

The anti-equivalence reverses the group diagrams into the Hopf identities. Quotients of coordinate rings turn subgroup factorizations into Hopf ideals. Fiber products give kernels, equalizers, and their base-change properties.

For an image, the coordinate kernel is stable under Hopf operations when tensoring preserves the needed injection; fields and purity provide this. For a torsor, reversing

$$
P\times_SG\cong P\times_XP
$$

gives $A\otimes_BA\cong A\otimes_RH$, and faithful descent identifies $B$ with invariants.

A finite locally free subgroup defines a finite locally free closed equivalence relation. The
finite-orbit calculation in §9.4 constructs its affine quotient and proves the torsor identity;
normality then descends the group operations. Torsor trivialization after a faithfully flat cover
proves rank multiplication using Book 44.

Finally, the counit splits $A=R\oplus I$. Multiplicativity of $\Delta$ gives the filtration estimate, which gives the convolution order law. Duals commute with base change exactly in the finite projective cases already isolated. This proves every clause with its stated scope.

### 23.3 Consequences for finite locally free groups

If $G$ has constant rank $n$, every geometric fiber has length $n$. Over an algebraically closed field, translations identify local structures and give

$$
n=|G(k)|\cdot\operatorname{length}(\mathcal O_{G,e}).
$$

Reduced fibers have local length one; infinitesimal fibers are measured by the identity local algebra and its distributions.

For a finite locally free subgroup $H\hookrightarrow G$,

$$
\operatorname{rk}G=\operatorname{rk}H\operatorname{rk}(G/H)
$$

componentwise. This is Lagrange's theorem with rank replacing cardinality. A general kernel inside a finite locally free group is finite but requires a flatness argument before this formula applies.

For commutative $G$, the torsion kernel $G[n]$ commutes with every base change. Its finite local freeness is not formal: prove it by a monic presentation, a valid flatness criterion, torsion-freeness over a DVR, or faithful descent. Once proved, its rank survives even where its points collide.

### 23.4 The final checklist

1. State the base and whether the coordinate algebra is flat, finitely presented, finite, or finite projective.
2. Write $\Delta$, $\varepsilon$, and $S$ on generators and check convolution inverse identities.
3. Reverse every group morphism when passing to coordinates.
4. Define closed subgroups by Hopf ideals and kernels by pulled-back augmentation ideals.
5. State the field, purity, or flatness hypothesis used for an image.
6. Fix left or right action conventions before writing a coaction.
7. Distinguish presheaf quotient, sheaf quotient, and representing scheme; verify faithful flatness and the canonical map.
8. Test exactness scheme-theoretically, not only on rational or geometric points.
9. Prove finite projectivity before using rank laws.
10. Match each base-change claim to its construction: fiber product, kernel, image, invariant equalizer, closure, or dual.
11. Use $A/I^{n+1}$ when tangent space is insufficient, and dualize only under the required finiteness hypothesis.

This order is short enough for calculations and strong enough to prevent the standard errors.

### 23.5 Conclusion

Affine group schemes reconcile functorial and algebraic symmetry. Their points vary through every algebra over the base, including nilpotent ones; their Hopf algebras turn that variation into explicit maps. Contravariance changes multiplication into comultiplication, identity into counit, and inversion into antipode.

The same reversal governs all constructions. Hopf ideals are subgroup equations, augmentation ideals cut out kernels, coactions encode actions, and the canonical torsor map expresses effective descent. Quotients exist at the scope proved here—most importantly for finite locally free subgroups—and exactness belongs to the faithfully flat topology rather than to pointwise surjectivity.

Finite locally free groups add rank, an invariant that survives specialization when points merge and multiplies in exact sequences. The augmentation filtration and distributions retain the higher infinitesimal structure left invisible by rank and tangent space alone.

The resulting method moves among four levels without confusing them: points suggest formulas, coordinate rings prove them, descent constructs quotients, and finite projective algebra carries structure across the base. Keeping those levels aligned is the central discipline of affine group-scheme theory and the foundation for the finite flat commutative groups that follow.
