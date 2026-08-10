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
    - [Final synthesis](#165-final-synthesis)

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
G\xrightarrow{(i,\operatorname{id})}G\times_SG\xrightarrow mG
$$

and

$$
G\xrightarrow pS\xrightarrow eG
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

**Theorem 9.1 (finite locally free affine quotient).** Let $G$ be an affine group scheme over an arbitrary base scheme $S$, and let $H\hookrightarrow G$ be a closed subgroup that is finite locally free over $S$. Then the faithfully flat quotient sheaf $G/H$ is represented by an affine $S$-scheme. On an affine base, it is

$$
\operatorname{Spec}\bigl(\mathcal O(G)^{\operatorname{co}H}\bigr),
$$

and $G\to G/H$ is finite locally free, faithfully flat, and an $H$-torsor. If $H$ is normal, the quotient is an affine group scheme.

**Proof strategy.** Right translation makes

$$
G\times_SH\rightrightarrows G
$$

a finite locally free equivalence relation: the arrows are projection and action, and the map to $G\times_SG$ is a closed immersion because $H\hookrightarrow G$ is. The affine theorem for a finite locally free equivalence relation constructs its effective quotient as the spectrum of the equalizer of functions. In the present notation this equalizer is exactly $B=A^{\operatorname{co}H}$.

Here is the algebra behind effectivity. Since $C=\mathcal O(H)$ is finite projective, a finite dual basis permits every coaction coefficient of $A\to A\otimes C$ to be extracted by finitely many $R$-linear functionals on $C$. The relations saying that two elements of $G$ lie in one orbit are therefore controlled by a finite projective algebra. The equalizer $B$ is stable under localization, and after the faithfully flat cover that supplies a local orbit representative, the relation becomes the split relation

$$
(G/H)\times_SH\rightrightarrows (G/H)\times_SH.
$$

In that split case the equalizer is visibly the coordinate algebra of $G/H$, the extension to the total space is finite locally free with underlying module obtained from $C$, and the canonical map is an isomorphism. Faithful descent carries these three assertions—affineness, finite local freeness, and the canonical-map isomorphism—back to $B\subseteq A$. Thus $G\to\operatorname{Spec}B$ is an $H$-torsor and §9.2 identifies its target with the quotient sheaf. Normality makes multiplication and inversion invariant on cosets, hence descends the group structure uniquely. $\square$

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

For any affine scheme over a field of characteristic $p$, raising functions to $p$th powers defines the absolute Frobenius on the scheme with its characteristic-$p$ base behavior. For group schemes it is a group morphism because $(xy)^p=x^py^p$ in commutative coordinate rings. Relative Frobenius keeps track of the Frobenius twist of the base and is the base-compatible version.

For $\mathbf G_a$, the coordinate pullback is $T\mapsto T^p$ and the kernel is $\alpha_p$. For $\mathbf G_m$, it is $T\mapsto T^p$ and the kernel is $\mu_p$. Both maps are finite locally free of rank $p$ and are torsor quotients in the faithfully flat topology. Their kernels have the same rank and geometric-point count but different coproducts.

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

occur. Their kernels are closed subgroup schemes with coordinate algebra $R[T]/(P(T))$. When the leading coefficient is a unit and $P$ is monic of degree $p^r$, the kernel is finite locally free of rank $p^r$.

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

Because $A/I$ injects into $A_K/I_K$, it is $R$-torsion-free. If it is finite over $R$, it is therefore finite free. The Hopf conditions descend from $I_K$: for example, flatness makes the relevant maps inject into the generic-fiber tensor products, allowing one to show

$$
\Delta(I)\subseteq I\otimes A+A\otimes I
$$

under the finite flat quotient hypotheses. Thus the closure is a finite flat subgroup when finiteness and tensor-intersection conditions are established.

Those qualifications are important. An arbitrary subalgebra of a finite-dimensional generic fiber need not be finite over $R$, and intersection with a generic Hopf ideal does not by itself resolve every tensor-purity issue over a general base. Over a DVR, torsion-freeness supplies much of the missing control once finiteness is known. A systematic theory of finite-flat schematic closure belongs to the next stage of the subject.

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

### 16.5 Final synthesis

Affine group schemes are groups whose elements may be evaluated in every algebra over the base. The functor of points makes this idea concrete, and elementary Yoneda reasoning turns natural pointwise laws back into geometric morphisms. Passing to coordinate rings reverses every arrow: products become tensor products, multiplication becomes comultiplication, the identity becomes a counit, and inversion becomes the uniquely determined antipode.

That reversal is not merely a formal dictionary. It makes subgroup equations into Hopf ideals, kernels into quotients by pulled-back augmentation ideals, commutativity into cocommutativity, and base change into tensor extension. It also exposes the limits of naive constructions. Images require purity or field hypotheses to inherit a Hopf structure reliably; closed subgroups of finite flat groups need a flatness argument to remain finite flat; quotients require effective descent, not just an invariant ring or a pointwise orbit set.

The faithfully flat topology is the natural setting for exactness because roots, coset representatives, and torsor sections often exist only after a cover. Torsors express the needed effectivity through one decisive isomorphism,

$$
G\times_SH\simeq G\times_QG,
$$

whose coordinate form is the canonical Hopf–Galois map. Under finite locally free hypotheses, this geometry becomes finite projective algebra: ranks multiply in exact sequences, arbitrary base change preserves the objects, and descent recovers them from split calculations.

Finally, infinitesimal examples show why the scheme structure cannot be discarded. In characteristic $p$, $\mu_p$ and $\alpha_p$ may have only the identity as a geometric point while retaining rank $p$, nonzero cotangent space, and distinct Hopf laws. Torsion subgroup schemes must therefore be built as scheme-theoretic kernels and judged by their coordinate algebras, not by sets of points. With that principle in place, the passage from a commutative group object to its finite torsion kernels becomes a controlled sequence of operations: form the multiplication morphism, take its affine kernel, prove finite projectivity under the relevant hypotheses, and use Hopf algebra, rank, base change, and faithfully flat exactness to carry the resulting structure through arithmetic families.
