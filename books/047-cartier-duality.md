# Cartier Duality

## Contents

1. [Why characters must themselves form a scheme](#1-why-characters-must-themselves-form-a-scheme)
   - [The duality problem](#11-the-duality-problem)
   - [Why geometric characters fail](#12-why-geometric-characters-fail)
   - [Why the target is $\mathbf G_m$](#13-why-the-target-is-mathbf-g_m)
   - [The roadmap](#14-the-roadmap)
2. [Dualizing a finite Hopf algebra](#2-dualizing-a-finite-hopf-algebra)
   - [The finite-projective doorway](#21-the-finite-projective-doorway)
   - [Multiplication and unit on the dual](#22-multiplication-and-unit-on-the-dual)
   - [Coproduct, counit, and antipode on the dual](#23-coproduct-counit-and-antipode-on-the-dual)
   - [Compatibility of the algebra and coalgebra structures](#24-compatibility-of-the-algebra-and-coalgebra-structures)
3. [The Cartier dual and the character functor](#3-the-cartier-dual-and-the-character-functor)
   - [Definition and first properties](#31-definition-and-first-properties)
   - [Representation of characters](#32-representation-of-characters)
   - [Contravariant functoriality](#33-contravariant-functoriality)
   - [Arbitrary base change](#34-arbitrary-base-change)
   - [Products](#35-products)
   - [Descent and locality](#36-descent-and-locality)
4. [Evaluation and biduality](#4-evaluation-and-biduality)
   - [The universal evaluation pairing](#41-the-universal-evaluation-pairing)
   - [The map to the bidual](#42-the-map-to-the-bidual)
   - [Detailed proof of biduality](#43-detailed-proof-of-biduality)
   - [Reflexivity and anti-equivalence](#44-reflexivity-and-anti-equivalence)
5. [Constant and diagonalizable groups](#5-constant-and-diagonalizable-groups)
   - [The expected exchange](#51-the-expected-exchange)
   - [Dual of a constant group](#52-dual-of-a-constant-group)
   - [Dual of a diagonalizable group](#53-dual-of-a-diagonalizable-group)
   - [Roots of unity in every characteristic](#54-roots-of-unity-in-every-characteristic)
   - [A noncanonical pointwise shadow](#55-a-noncanonical-pointwise-shadow)
   - [Twisted forms of the standard exchange](#56-twisted-forms-of-the-standard-exchange)
6. [Additive infinitesimal duality](#6-additive-infinitesimal-duality)
   - [Why $\alpha_p$ is a decisive test](#61-why-alpha_p-is-a-decisive-test)
   - [Explicit calculation of the dual Hopf algebra](#62-explicit-calculation-of-the-dual-hopf-algebra)
   - [The pairing behind self-duality](#63-the-pairing-behind-self-duality)
   - [What does not generalize naively](#64-what-does-not-generalize-naively)
7. [Exact sequences and reversal of subquotients](#7-exact-sequences-and-reversal-of-subquotients)
   - [Why exactness needs flatness](#71-why-exactness-needs-flatness)
   - [The exactness theorem](#72-the-exactness-theorem)
   - [Closed subgroups and their annihilators](#73-closed-subgroups-and-their-annihilators)
   - [Double annihilators](#74-double-annihilators)
   - [Kernels and images under a morphism](#75-kernels-and-images-under-a-morphism)
   - [A worked cyclic sequence](#76-a-worked-cyclic-sequence)
   - [Sums, intersections, and annihilator identities](#77-sums-intersections-and-annihilator-identities)
8. [Bilinear pairings and perfectness](#8-bilinear-pairings-and-perfectness)
   - [Pairings as morphisms into duals](#81-pairings-as-morphisms-into-duals)
   - [Perfect pairings](#82-perfect-pairings)
   - [Radicals and degeneracy](#83-radicals-and-degeneracy)
   - [Pairings killed by an integer](#84-pairings-killed-by-an-integer)
9. [Orthogonality and rank calculus](#9-orthogonality-and-rank-calculus)
   - [Orthogonal subgroup schemes](#91-orthogonal-subgroup-schemes)
   - [Double orthogonals](#92-double-orthogonals)
   - [Isotropic and Lagrangian subgroups](#93-isotropic-and-lagrangian-subgroups)
   - [Orthogonals in an exact sequence](#94-orthogonals-in-an-exact-sequence)
10. [Multiplication kernels and self-duality](#10-multiplication-kernels-and-self-duality)
    - [Duality commutes with multiplication](#101-duality-commutes-with-multiplication)
    - [Dual of a multiplication kernel](#102-dual-of-a-multiplication-kernel)
    - [Elementary self-dual patterns](#103-elementary-self-dual-patterns)
    - [Kernels of dual isogenies](#104-kernels-of-dual-isogenies)
11. [Fibers and structural types over fields](#11-fibers-and-structural-types-over-fields)
    - [Fiberwise duality without loss of rank](#111-fiberwise-duality-without-loss-of-rank)
    - [Multiplicative type and étale groups](#112-multiplicative-type-and-étale-groups)
    - [The connected–étale sequence and its dual](#113-the-connectedétale-sequence-and-its-dual)
    - [Henselian local bases](#114-henselian-local-bases)
    - [Order-$p$ comparison](#115-order-p-comparison)
    - [The local-local remainder](#116-the-local-local-remainder)
12. [Duality over DVRs and schematic closure](#12-duality-over-dvrs-and-schematic-closure)
    - [Generic and special fibers](#121-generic-and-special-fibers)
    - [Closure and annihilator commute](#122-closure-and-annihilator-commute)
    - [Quotients and closure](#123-quotients-and-closure)
    - [Henselian consequences](#124-henselian-consequences)
    - [Beyond DVRs](#125-beyond-dvrs)
    - [Dual lattices and saturation](#126-dual-lattices-and-saturation)
13. [Finite-flat models and Tate-twisted module duals](#13-finite-flat-models-and-tate-twisted-module-duals)
    - [From an étale generic fiber to a module](#131-from-an-étale-generic-fiber-to-a-module)
    - [Why the twist is unavoidable](#132-why-the-twist-is-unavoidable)
    - [Dual models over a DVR](#133-dual-models-over-a-dvr)
    - [Submodules, quotients, and exact models](#134-submodules-quotients-and-exact-models)
    - [Limits of the geometric-point formula](#135-limits-of-the-geometric-point-formula)
    - [Determinants, similitudes, and orthogonal modules](#136-determinants-similitudes-and-orthogonal-modules)
14. [Abelian schemes, torsion, and the Weil pairing](#14-abelian-schemes-torsion-and-the-weil-pairing)
    - [Why proper groups enter the story](#141-why-proper-groups-enter-the-story)
    - [Construction of the group-scheme Weil pairing](#142-construction-of-the-group-scheme-weil-pairing)
    - [Perfectness in all characteristics](#143-perfectness-in-all-characteristics)
    - [Polarizations and self-duality](#144-polarizations-and-self-duality)
    - [Elliptic curves](#145-elliptic-curves)
    - [Isogenies and orthogonal kernels](#146-isogenies-and-orthogonal-kernels)
    - [Compatibility through levels](#147-compatibility-through-levels)
    - [Determinants of elliptic torsion](#148-determinants-of-elliptic-torsion)
15. [Worked structural patterns](#15-worked-structural-patterns)
    - [A cyclic homomorphism and its dual](#151-a-cyclic-homomorphism-and-its-dual)
    - [A split hyperbolic group](#152-a-split-hyperbolic-group)
    - [The additive perfect pairing on test algebras](#153-the-additive-perfect-pairing-on-test-algebras)
    - [Dualizing a connected exact sequence](#154-dualizing-a-connected-exact-sequence)
    - [Two mixed-characteristic models](#155-two-mixed-characteristic-models)
    - [A failure caused by dropping flatness](#156-a-failure-caused-by-dropping-flatness)
16. [A reusable duality dictionary](#16-a-reusable-duality-dictionary)
    - [Five duals and their domains](#161-five-duals-and-their-domains)
    - [The structural table](#162-the-structural-table)
    - [The exactness table](#163-the-exactness-table)
    - [The arithmetic table](#164-the-arithmetic-table)
    - [A safe proof protocol](#165-a-safe-proof-protocol)
    - [Conclusion](#166-conclusion)

## 1. Why characters must themselves form a scheme

### 1.1 The duality problem

The preceding books developed finite locally free commutative group schemes as the correct integral form of finite abelian groups. Their order survives specialization even when their points coalesce, and their Hopf algebras remember the infinitesimal group law that a point set loses. We now ask for a duality on this category.

For a finite abelian group $M$, the most natural dual object is its character group. If all relevant roots of unity lie in a field $K$, one may write

$$
M^*=\operatorname{Hom}(M,K^\times).
$$

This formula suggests two principles. The target should be the multiplicative group, because a character converts addition in the source into multiplication. And characters must be allowed to vary with the test algebra, because over a general base there is no single field containing all of the information. Thus the desired dual of an $S$-group $G$ is not initially a set but the functor

$$
T\longmapsto \operatorname{Hom}_{T\text{-groups}}(G_T,\mathbf G_{m,T}). \tag{1.1}
$$

The central theorem of this book says that if $G$ is finite locally free and commutative, this functor is represented by another finite locally free commutative group scheme. It is denoted

$$
G^D=\underline{\operatorname{Hom}}(G,\mathbf G_m)
$$

and called the **Cartier dual** of $G$.

There are several dualities nearby, and confusing them obscures the theorem. If $P$ is a finite projective module, $P^\vee=\operatorname{Hom}(P,R)$ is its module linear dual. If $A$ is a finite projective Hopf algebra, $A^\vee$ acquires a new Hopf structure by transposing every structure map. If $G=\operatorname{Spec}A$, the spectrum of that new Hopf algebra is $G^D$. Over a field, geometric points of an étale group form a finite Galois module, whose character module is yet another manifestation of the same construction when the relevant roots of unity are étale. These statements are connected, but they live in different categories and have different variance.

### 1.2 Why geometric characters fail

Suppose $k$ is algebraically closed of characteristic $p$. The group schemes

$$
\underline{\mathbf Z/p\mathbf Z},\qquad \mu_p,\qquad \alpha_p
$$

all have order $p$, but

$$
\mu_p(k)=\{1\},\qquad \alpha_p(k)=\{0\}.
$$

If one formed only homomorphisms of abstract groups of $k$-points into $k^\times$, both nonétale examples would appear to have trivial dual. A true duality cannot send two nontrivial order-$p$ objects to the trivial group and still satisfy biduality.

The missing characters appear over nonreduced test algebras. For instance, if $C$ is a $k$-algebra and $x\in C$ satisfies $x^p=0$, then $x$ is a point of $\alpha_p(C)$. A character of group schemes must prescribe its value on such nilpotent points naturally in $C$. Likewise, an element $1+u$ with $u^p=0$ is a $C$-point of $\mu_p$. The functor (1.1) sees these elements because it tests every $C$, not merely fields.

This is the first decisive lesson of Cartier duality:

$$
\text{characters of a finite group scheme are natural morphisms, not pointwise functions.}
$$

The characteristic-dividing cases will therefore require no repair. Once the functor is represented, its nilpotents carry precisely the characters invisible on geometric points.

### 1.3 Why the target is $\mathbf G_m$

A duality is useful only if it comes with evaluation. For ordinary characters, evaluation is the bilinear map

$$
M\times M^*\longrightarrow K^\times,\qquad (m,\chi)\longmapsto\chi(m).
$$

Replacing $K^\times$ by $\mathbf G_m$ makes this formula natural over every base. Bilinearity means that evaluation is a homomorphism in each variable. It then converts a pairing into a map to a dual, which will be the organizing principle for perfect pairings and orthogonal subgroup schemes.

The additive group would solve a different problem. Morphisms $G\to\mathbf G_a$ are additive functionals, and for infinitesimal groups they can be plentiful, but they do not exchange constant and diagonalizable groups and do not produce the root-of-unity targets of the Weil pairing. The multiplicative target is forced by the character theory we want.

If $G$ is killed by $n$, every character $\chi:G\to\mathbf G_m$ lands in $\mu_n$, since

$$
\chi(g)^n=\chi(ng)=1.
$$

Thus pairings of $n$-torsion groups naturally take values in $\mu_n$. The larger target $\mathbf G_m$ remains preferable in the definition because it is independent of a chosen annihilator.

### 1.4 The roadmap

We begin by dualizing a finite projective Hopf algebra and proving that every required identity survives with the correct variance. The resulting group represents the character functor, commutes with arbitrary base change, and is contravariantly functorial. Evaluation then gives a completely explicit proof of biduality.

The standard examples reveal the geometry: constant groups and diagonalizable groups exchange places, $\mu_n$ is dual to the constant cyclic group even in characteristic dividing $n$, and $\alpha_p$ is self-dual in characteristic $p$. We next show that Cartier duality is exact under the finite locally free and faithfully flat hypotheses established in Book 46. This produces annihilators, rank formulas, and a precise reversal of subgroups and quotients.

The later chapters develop bilinear and perfect pairings, behavior over fields and DVRs, finite-flat models of Galois modules, and torsion on abelian schemes. The endpoint is a dictionary that can be used without reopening the Hopf calculation, while keeping the distinction between schematic duality and later cohomological dualities completely visible.

## 2. Dualizing a finite Hopf algebra

### 2.1 The finite-projective doorway

Let $R$ be a ring and let

$$
G=\operatorname{Spec}A
$$

be a finite locally free commutative $R$-group scheme. Thus $A$ is a commutative, cocommutative Hopf $R$-algebra, finite projective as an $R$-module, with maps

$$
\Delta:A\to A\otimes_R A,\qquad
\varepsilon:A\to R,\qquad
S:A\to A,\qquad
u:R\to A.
$$

Set

$$
A^\vee=\operatorname{Hom}_R(A,R).
$$

Finite projectivity supplies the canonical isomorphisms

$$
A^\vee\otimes_R A^\vee\xrightarrow{\sim}(A\otimes_R A)^\vee,\qquad
(A^\vee)^\vee\xrightarrow{\sim}A. \tag{2.1}
$$

These are the entire reason the construction closes inside finite flat groups. For an arbitrary module, the first arrow need not be an isomorphism and the second need not be one either. One could still write convolution formulas, but there would be no reason for them to define a finite locally free representing object or to yield biduality.

Before giving formulas, it is helpful to track what must reverse. The coproduct $\Delta$ encodes multiplication on $G$, so its transpose should define multiplication on the dual algebra. The product $m_A$ is part of the coordinate algebra, so its transpose should define the coproduct of the dual group. Unit and counit likewise exchange. The antipode transposes to itself.

### 2.2 Multiplication and unit on the dual

For $f,g\in A^\vee$, define their product by convolution:

$$
(fg)(a)=(f\otimes g)(\Delta a)
=\sum f(a_{(1)})g(a_{(2)}). \tag{2.2}
$$

Define the unit $1_{A^\vee}$ to be the counit of $A$:

$$
1_{A^\vee}=\varepsilon,\qquad
(r\cdot1_{A^\vee})(a)=r\varepsilon(a). \tag{2.3}
$$

Coassociativity of $\Delta$ proves associativity of (2.2). Indeed

$$
((fg)h)(a)=\sum f(a_{(1)})g(a_{(2)})h(a_{(3)})=(f(gh))(a),
$$

where the equality is exactly the equality between the two iterated coproducts. The counit identities give

$$
(\varepsilon f)(a)=\sum\varepsilon(a_{(1)})f(a_{(2)})=f(a),
$$

and similarly on the other side.

Because $G$ is commutative, $\Delta$ is cocommutative. Applying the tensor flip in (2.2) gives $fg=gf$. Thus cocommutativity of the original Hopf algebra becomes commutativity of the dual algebra. This is one of the two places where commutativity of the group is essential.

### 2.3 Coproduct, counit, and antipode on the dual

Transpose multiplication $m_A:A\otimes A\to A$. Using (2.1), this gives

$$
\Delta^D:A^\vee\longrightarrow A^\vee\otimes_R A^\vee
$$

characterized by

$$
\text{if }\Delta^D(f)=\sum f_{(1)}\otimes f_{(2)},\quad
f(ab)=\sum f_{(1)}(a)f_{(2)}(b). \tag{2.4}
$$

Transpose the unit $u:R\to A$ to obtain the counit

$$
\varepsilon^D(f)=f(1). \tag{2.5}
$$

Finally define

$$
S^D(f)=f\circ S. \tag{2.6}
$$

Associativity and unitality of $A$ transpose to coassociativity and the counit laws for $A^\vee$. Because $A$ is a commutative algebra, $m_A=m_A\circ\tau$, so $\Delta^D$ is cocommutative. This is the second required variance: commutativity of the coordinate algebra, automatic for every affine scheme, makes the represented dual group commutative.

The antipode equation is equally concrete. If $\Delta^D(f)=\sum f_{(1)}\otimes f_{(2)}$, then for $a\in A$,

$$
\begin{aligned}
\bigl(m_{A^\vee}(S^D\otimes\operatorname{id})\Delta^D(f)\bigr)(a)
&=\sum f_{(1)}(S(a_{(1)}))f_{(2)}(a_{(2)})\\
&=f\!\left(\sum S(a_{(1)})a_{(2)}\right)\\
&=f(\varepsilon(a)1)\\
&=\varepsilon(a)f(1).
\end{aligned} \tag{2.7}
$$

The last expression is $(u_{A^\vee}\varepsilon^D)(f)$ evaluated at $a$. The other antipode identity follows from the other antipode identity in $A$. Therefore $A^\vee$ is a commutative, cocommutative Hopf $R$-algebra.

### 2.4 Compatibility of the algebra and coalgebra structures

It remains to check that $\Delta^D$ and $\varepsilon^D$ are algebra homomorphisms. This is not an extra miracle: it is the transpose of the assertion that $\Delta$ and $\varepsilon$ are algebra homomorphisms. Because tensor factors can conceal a reversal, we spell out the decisive calculation.

For $f,g\in A^\vee$ and $a,b\in A$,

$$
\begin{aligned}
\Delta^D(fg)(a\otimes b)
&=(fg)(ab)\\
&=\sum f(a_{(1)}b_{(1)})g(a_{(2)}b_{(2)}).
\end{aligned}
$$

On the other hand, multiplication in $(A^\vee\otimes A^\vee)$, followed by evaluation on $a\otimes b$, gives exactly the same expression, since

$$
\Delta(ab)=\Delta(a)\Delta(b)
=\sum a_{(1)}b_{(1)}\otimes a_{(2)}b_{(2)}.
$$

Thus $\Delta^D(fg)=\Delta^D(f)\Delta^D(g)$. Also

$$
\varepsilon^D(fg)=(fg)(1)=f(1)g(1).
$$

The unit compatibilities follow from $\Delta(1)=1\otimes1$ and $\varepsilon(1)=1$. We have proved the fundamental algebraic result.

**Theorem 2.1 (dual Hopf algebra).** If $A$ is a commutative, cocommutative Hopf $R$-algebra finite projective over $R$, then $A^\vee$ with (2.2)--(2.6) is again a commutative, cocommutative Hopf $R$-algebra finite projective over $R$.

For completeness, if $(a_i,f_i)$ is a finite dual basis of $A$, then $(f_i,\operatorname{ev}_{a_i})$ is a dual basis of $A^\vee$. Tensoring two dual bases proves the first isomorphism in (2.1), and evaluation proves the second. Thus $A^\vee$ is finite projective of the same rank as $A$. The proof also shows exactly what fails outside the stated category: without finite projectivity the tensor-dual comparison can fail, and without cocommutativity the convolution algebra need not be commutative.

## 3. The Cartier dual and the character functor

### 3.1 Definition and first properties

The Hopf calculation solves the representability problem.

**Definition 3.1.** For $G=\operatorname{Spec}A$ finite locally free and commutative over $R$, its **Cartier dual** is

$$
G^D=\operatorname{Spec}(A^\vee), \tag{3.1}
$$

where $A^\vee$ has the Hopf structure of Chapter 2.

It is finite locally free, commutative, and of the same rank as $G$. The definition glues over a general base scheme $S$: on overlaps, duals of finite locally free modules and all transposed structure maps agree canonically. We therefore obtain $G^D$ for every $G\in\mathrm{FFCG}(S)$.

This definition begins with a module dual but ends with a group scheme. The notation $A^\vee$ refers to the linear dual equipped with its transposed Hopf operations; the notation $G^D$ refers to its spectrum. Treating the two as interchangeable would reverse arrows incorrectly.

### 3.2 Representation of characters

We now verify that (3.1) represents (1.1). Let $C$ be an $R$-algebra. A homomorphism of $C$-group schemes

$$
G_C\longrightarrow\mathbf G_{m,C}
$$

corresponds to a Hopf map

$$
C[T,T^{-1}]\longrightarrow A\otimes_R C.
$$

It is determined by the image $x$ of $T$. The Hopf conditions say

$$
\Delta(x)=x\otimes x,\qquad \varepsilon(x)=1. \tag{3.2}
$$

The antipode condition then says $S(x)=x^{-1}$, so invertibility is already forced by (3.2).

Finite projectivity gives a natural identification

$$
A\otimes_R C\xrightarrow{\sim}\operatorname{Hom}_R(A^\vee,C),\qquad
x\longmapsto(f\mapsto(f\otimes1)(x)). \tag{3.3}
$$

Under this identification, condition $\Delta(x)=x\otimes x$ says precisely that the corresponding map $A^\vee\to C$ preserves multiplication, while $\varepsilon(x)=1$ says that it preserves the unit. Consequently

$$
G^D(C)=\operatorname{Hom}_{R\text{-alg}}(A^\vee,C)
\cong\operatorname{Hom}_{C\text{-groups}}(G_C,\mathbf G_{m,C}). \tag{3.4}
$$

The correspondence is natural in $C$, so it identifies represented functors. This proof also identifies the universal character: it corresponds under (3.3) to the identity of $A^\vee$, or equivalently to the canonical coevaluation tensor in $A\otimes A^\vee$.

### 3.3 Contravariant functoriality

Let $f:G\to H$ be a homomorphism, with coordinate map

$$
f^*:B=\mathcal O(H)\longrightarrow A=\mathcal O(G).
$$

Linear duality reverses it:

$$
(f^*)^\vee:A^\vee\longrightarrow B^\vee.
$$

Because $f^*$ respects every Hopf operation, its transpose does also. Taking spectra reverses once more and gives

$$
f^D:H^D\longrightarrow G^D. \tag{3.5}
$$

On characters, $f^D$ is precomposition: $\chi\mapsto\chi\circ f$. Thus Cartier duality is contravariant, and

$$
(g\circ f)^D=f^D\circ g^D,\qquad
(\operatorname{id}_G)^D=\operatorname{id}_{G^D}. \tag{3.6}
$$

There are two arrow reversals in the construction—linear transpose and spectrum—but the character interpretation leaves one net reversal. Keeping (3.5) in view prevents a common mistake in exact sequences.

### 3.4 Arbitrary base change

Let $R\to R'$ be any ring map. Finite projectivity supplies a canonical isomorphism

$$
A^\vee\otimes_RR'\xrightarrow{\sim}
(A\otimes_RR')^\vee. \tag{3.7}
$$

It respects the dual Hopf operations because each is obtained by tensoring and transposing a structure map of $A$. Therefore

$$
(G^D)_{R'}\xrightarrow{\sim}(G_{R'})^D. \tag{3.8}
$$

No flatness hypothesis is needed. In particular, duality commutes with generic fibers, special fibers, residue-field extensions, strict henselization, completion after base change, and passage to an algebraic closure. The strength of this statement comes from finite local freeness.

Over general schemes, for every $S'\to S$ there is a canonical isomorphism

$$
(G^D)_{S'}\simeq(G_{S'})^D,
$$

compatible with composition of base changes. Thus changing the base and taking characters may be done in either order.

### 3.5 Products

If $G=\operatorname{Spec}A$ and $H=\operatorname{Spec}B$, then

$$
\mathcal O(G\times H)=A\otimes_RB.
$$

Finite projectivity gives

$$
(A\otimes_RB)^\vee\simeq A^\vee\otimes_RB^\vee,
$$

and the isomorphism respects Hopf structures. Hence

$$
(G\times H)^D\simeq G^D\times H^D. \tag{3.9}
$$

On characters this says that a character of a product is uniquely the product of a character from each factor:

$$
\chi(g,h)=\chi(g,0)\chi(0,h).
$$

Finite products are also finite coproducts in the category of commutative group objects, which explains why a contravariant duality can preserve their displayed form.

### 3.6 Descent and locality

The affine construction is enough to define the dual globally, but applications frequently recognize a duality only after extending the base. It is therefore important to separate construction from verification. Finite locally free modules, their duals, and homomorphisms between them descend effectively along faithfully flat maps. The Hopf identities are equalities of maps between finite locally free modules, so they descend as well. Consequently a dual computed after a faithfully flat cover carries canonical descent data and descends to the dual over the original base.

This gives a useful recognition principle. Let $u:G\to H^D$ be a morphism of finite locally free commutative groups. If there is a faithfully flat cover $S'\to S$ for which

$$
u_{S'}:G_{S'}\xrightarrow{\sim}(H_{S'})^D
$$

is an isomorphism, then $u$ is already an isomorphism. In particular, perfectness of a pairing is local for the faithfully flat topology. The same conclusion holds if one checks over an open cover, over strict henselizations at all geometric points, or by another conservative faithfully flat base change.

There is a related warning. An isomorphism $G_{S'}\simeq H_{S'}^D$ chosen after a cover need not descend: on the double overlap its two pullbacks may differ by an automorphism. What descends automatically is the canonical dual and any morphism already equipped with compatible descent data. This is the mechanism behind nonsplit finite étale groups and nonsplit groups of multiplicative type.

## 4. Evaluation and biduality

### 4.1 The universal evaluation pairing

A character should be evaluated, not merely collected. The representing property produces a canonical bilinear morphism

$$
\operatorname{ev}_G:G\times_SG^D\longrightarrow\mathbf G_m,\qquad
(g,\chi)\longmapsto\chi(g). \tag{4.1}
$$

Its meaning on a test scheme $T$ is literal: a $T$-point of $G^D$ is a character $G_T\to\mathbf G_{m,T}$, and it may be applied to a $T$-point of $G$. Naturality ensures that the result is a morphism of schemes. It is a homomorphism separately in $g$ and $\chi$.

Choose a local dual basis $(a_i,f_i)$ of $A$; thus $a=\sum_i f_i(a)a_i$. The canonical tensor

$$
\mathscr E_A=\sum_i a_i\otimes f_i\in A\otimes_RA^\vee \tag{4.2}
$$

is independent of the dual basis. The coordinate map of evaluation sends the standard coordinate $T$ of $\mathbf G_m$ to $\mathscr E_A$. The identities

$$
(\Delta_A\otimes1)(\mathscr E_A)=\mathscr E_{13}\mathscr E_{23},\qquad
(1\otimes\Delta^D)(\mathscr E_A)=\mathscr E_{12}\mathscr E_{13} \tag{4.3}
$$

express bilinearity in the two variables. Applying either counit gives $1$. These identities also show directly that $\mathscr E_A$ is invertible, with inverse obtained by applying $S$ or $S^D$ to the corresponding factor.

### 4.2 The map to the bidual

Fixing the first argument of evaluation turns (4.1) into a character of $G^D$. By representability there is a canonical homomorphism

$$
\delta_G:G\longrightarrow G^{DD}. \tag{4.4}
$$

On a test algebra, it sends $g$ to the character $\chi\mapsto\chi(g)$. This is the geometric analogue of the evaluation map from a finite-dimensional vector space into its double dual.

The order of the two variables matters only up to the symmetry of the product. With the convention (4.1), $\delta_G(g)(\chi)=\chi(g)$. This convention makes naturality read

$$
\delta_H\circ f=f^{DD}\circ\delta_G. \tag{4.5}
$$

### 4.3 Detailed proof of biduality

**Theorem 4.1 (Cartier biduality).** For every finite locally free commutative group scheme $G/S$, the evaluation map

$$
\delta_G:G\xrightarrow{\sim}G^{DD}
$$

is an isomorphism, natural in $G$ and compatible with arbitrary base change.

**Proof strategy.** The underlying module statement is finite-projective biduality. The only issue is to verify that the canonical module isomorphism respects the transposed Hopf structures and is the same map as evaluation. Both facts follow directly from how double transposition acts on each structure map.

Work first over $S=\operatorname{Spec}R$. The canonical module map

$$
j_A:A\longrightarrow A^{\vee\vee},\qquad
j_A(a)(f)=f(a), \tag{4.6}
$$

is an isomorphism because $A$ is finite projective. We compare structure maps. Multiplication on $A^{\vee\vee}$ is the transpose of the coproduct on $A^\vee$, which was itself the transpose of multiplication on $A$. For $a,b\in A$ and $f\in A^\vee$,

$$
(j_A(a)j_A(b))(f)
=(j_A(a)\otimes j_A(b))(\Delta^D f)
=f(ab)
=j_A(ab)(f). \tag{4.7}
$$

Thus $j_A$ preserves multiplication. It preserves the unit because $j_A(1)(f)=f(1)=\varepsilon^D(f)$. For the coproduct, evaluate both sides against $f\otimes g$:

$$
(f\otimes g)(\Delta_{A^{\vee\vee}}j_A(a))
=(fg)(a)
=(f\otimes g)(\Delta_Aa). \tag{4.8}
$$

Finite projectivity makes pairings with $f\otimes g$ jointly separating, so

$$
\Delta_{A^{\vee\vee}}j_A=(j_A\otimes j_A)\Delta_A.
$$

The counit identity is $j_A(a)(\varepsilon)=\varepsilon(a)$, and the antipode identity is

$$
S^{DD}(j_A(a))(f)=j_A(a)(f\circ S)=f(S(a))=j_A(S(a))(f). \tag{4.9}
$$

Hence $j_A$ is a Hopf isomorphism.

There is a small variance point. A morphism $G\to G^{DD}$ corresponds to a Hopf map $A^{\vee\vee}\to A$, whereas (4.6) points from $A$ to $A^{\vee\vee}$. The coordinate map of $\delta_G$ is therefore $j_A^{-1}$. Formula (4.2) shows that this is exactly the morphism induced by evaluation: after pairing with a functional, it sends the universal double character to its value on $a$. Thus the module biduality map and the character-evaluation map agree after the necessary spectrum reversal.

The construction is local on $S$ and canonical, so the affine isomorphisms glue. Naturality follows from naturality of $j_A$, and base-change compatibility follows from (3.7). $\square$

Biduality proves more than equality of ranks. It says that no schematic information is lost by passing to all characters. In particular, the infinitesimal directions invisible on field-valued points reappear in the dual Hopf algebra and are recovered on dualizing again.

### 4.4 Reflexivity and anti-equivalence

Cartier duality is therefore an exact-looking involutive contravariant equivalence of the category of finite locally free commutative $S$-group schemes with itself. At this stage “exact-looking” anticipates a theorem: exactness requires the faithfully flat quotient structure treated in Chapter 7. Independently of exactness, biduality already implies that $f$ is an isomorphism if and only if $f^D$ is an isomorphism.

It also implies that either variable of evaluation determines the other. If two points of $G$ induce the same character on $G^D$ functorially on every test scheme, they are equal. This is schematic nondegeneracy, far stronger than separation by geometric characters.

## 5. Constant and diagonalizable groups

### 5.1 The expected exchange

Constant and diagonalizable groups were introduced in Books 45 and 46 as opposite standard families. Cartier duality explains that opposition. Let $M$ be a finite abelian group. Over $S=\operatorname{Spec}R$, write

$$
\underline M=\operatorname{Spec}(R^M),\qquad
D(M)=\operatorname{Spec}(R[M]).
$$

Here $R^M$ is the algebra of functions $M\to R$, while $R[M]$ is the group algebra with basis $X^m$. These two finite free modules are naturally dual.

### 5.2 Dual of a constant group

Let $e_m\in R^M$ be the characteristic function of $m$. The coproduct encoding addition on $M$ is

$$
\Delta(e_c)=\sum_{a+b=c}e_a\otimes e_b,\qquad
\varepsilon(e_c)=
\begin{cases}1,&c=0,\\0,&c\ne0.\end{cases} \tag{5.1}
$$

Let $x_m\in(R^M)^\vee$ be dual to $e_m$. Convolution gives

$$
x_ax_b=x_{a+b},\qquad x_0=1. \tag{5.2}
$$

The transposed product of $R^M$ gives

$$
\Delta(x_m)=x_m\otimes x_m,\qquad
\varepsilon(x_m)=1,\qquad
S(x_m)=x_{-m}. \tag{5.3}
$$

These are precisely the Hopf formulas for $R[M]$. Consequently

$$
\underline M^D\simeq D(M). \tag{5.4}
$$

On $C$-points, this is the familiar identity

$$
D(M)(C)=\operatorname{Hom}(M,C^\times).
$$

The important advance is that (5.4) holds over every base ring, with no assumption that $|M|$ is invertible or that the base contains roots of unity.

### 5.3 Dual of a diagonalizable group

Conversely, let $A=R[M]$ and let $\lambda_m$ extract the coefficient of $X^m$. Since each $X^m$ is group-like,

$$
(\lambda_m\lambda_n)(X^r)=\lambda_m(X^r)\lambda_n(X^r).
$$

Hence

$$
\lambda_m\lambda_n=
\begin{cases}
\lambda_m,&m=n,\\
0,&m\ne n,
\end{cases}
\qquad
\sum_{m\in M}\lambda_m=1. \tag{5.5}
$$

Thus $A^\vee\simeq R^M$ as an algebra. Transposing multiplication $X^aX^b=X^{a+b}$ yields exactly (5.1). Therefore

$$
D(M)^D\simeq\underline M. \tag{5.6}
$$

This is also a worked instance of biduality. Notice that $D$ itself is contravariant in $M$: a map $M\to N$ gives $D(N)\to D(M)$. Cartier duality changes it back into the corresponding map of constant group schemes.

### 5.4 Roots of unity in every characteristic

Taking $M=\mathbf Z/n\mathbf Z$ gives

$$
\mu_n=D(\mathbf Z/n\mathbf Z),
$$

and therefore

$$
\mu_n^D\simeq\underline{\mathbf Z/n\mathbf Z},\qquad
\underline{\mathbf Z/n\mathbf Z}^D\simeq\mu_n. \tag{5.7}
$$

These isomorphisms hold over $\mathbf Z$, hence after arbitrary base change. If $n$ is invertible on the base, both sides become finite étale after a suitable étale cover and (5.7) resembles ordinary character theory. If the characteristic divides $n$, their geometry differs sharply.

Over a field $k$ of characteristic $p$, $\mu_p$ is connected and nonreduced, while $\underline{\mathbf Z/p\mathbf Z}$ is étale with $p$ components. Yet they are Cartier dual. Looking only at $k$-points would give

$$
\mu_p(k)=\{1\}
$$

when $k$ is reduced, and would miss all nontrivial characters of the constant group. The coordinate calculation (5.5), not a count of roots in $k$, proves duality. This example is the cleanest reason Cartier duality must be schematic.

### 5.5 A noncanonical pointwise shadow

If $K$ is a field, $n$ is invertible in $K$, and a primitive $n$th root $\zeta_n$ has been chosen, then

$$
\mathbf Z/n\mathbf Z\xrightarrow{\sim}\mu_n(K),\qquad a\mapsto\zeta_n^a.
$$

This may make the constant group and $\mu_n$ appear identical. The identification depends on $\zeta_n$ and need not respect Galois action. Cartier duality itself uses no such choice. Later, the failure of Galois invariance will be recorded by the Tate twist.

### 5.6 Twisted forms of the standard exchange

The formulas for $\underline M$ and $D(M)$ are split formulas. Over a field $k$, a finite étale commutative group need not be constant: after passage to a separable closure it becomes $\underline M$, but descent is governed by a continuous action of $\Gamma_k$ on $M$. Its Cartier dual becomes $D(M)$ after the same extension, with descent action obtained by contragredience. Thus duality exchanges not only the split families but all their twisted forms:

$$
\{\text{finite étale commutative groups}\}
\quad\xleftrightarrow{\ D\ }\quad
\{\text{finite groups of multiplicative type}\}. \tag{5.8}
$$

Both sides are descent categories, not just lists of split examples. Concretely, if a finite étale group becomes $\underline M$ over a finite Galois extension $L/k$, then its dual becomes $D(M)$ over $L$, and the descent action on a character $\chi$ is

$$
(\sigma\chi)(m)=\sigma\bigl(\chi(\sigma^{-1}m)\bigr). \tag{5.9}
$$

The outer $\sigma$ acts on the value in $\mathbf G_m$. Formula (5.9) is the first appearance of the action that will become the Tate twist when $M$ is killed by $n$.

For example, over $\mathbf R$ the group $\mu_3$ is finite étale but not constant: complex conjugation interchanges the two nonidentity geometric points. Its dual is the constant group $\underline{\mathbf Z/3\mathbf Z}$. Conversely, a constant cyclic group dualizes to $\mu_3$, whose geometric character module has the cyclotomic action. The split Hopf calculation remains valid; descent records why the resulting groups need not look alike over the ground field.

## 6. Additive infinitesimal duality

### 6.1 Why $\alpha_p$ is a decisive test

Constant and diagonalizable groups might leave the impression that duality merely exchanges components with roots of unity. The additive infinitesimal group shows more. Let $p$ be prime and let $R$ be an $\mathbf F_p$-algebra, equivalently a ring in which $p=0$. Define

$$
\alpha_{p,R}=\operatorname{Spec}R[t]/(t^p)
$$

with primitive coproduct

$$
\Delta(t)=t\otimes1+1\otimes t,\qquad
\varepsilon(t)=0,\qquad S(t)=-t. \tag{6.1}
$$

The characteristic-$p$ hypothesis is essential: the ideal $(t^p)$ is stable under the primitive coproduct precisely because the intermediate binomial coefficients vanish. Over a ring on which $p$ is not zero, this quotient with (6.1) is not a Hopf algebra in general.

### 6.2 Explicit calculation of the dual Hopf algebra

Put $A=R[t]/(t^p)$ and let $\lambda_i\in A^\vee$ be dual to $t^i$ for $0\le i<p$. The binomial formula gives

$$
\Delta(t^n)=\sum_{i+j=n}\binom ni t^i\otimes t^j.
$$

Therefore convolution on the dual satisfies

$$
\lambda_i\lambda_j=
\begin{cases}
\binom{i+j}{i}\lambda_{i+j},&i+j<p,\\
0,&i+j\ge p.
\end{cases} \tag{6.2}
$$

Let $y=\lambda_1$. Induction using (6.2) gives

$$
y^i=i!\lambda_i\qquad(0\le i<p). \tag{6.3}
$$

Every $i!$ with $i<p$ is a unit in any ring of characteristic $p$, since its residue modulo $p$ is invertible and an integer inverse modulo $p$ gives an inverse in $R$. Thus $1,y,\ldots,y^{p-1}$ is a basis and $y^p=0$. Hence

$$
A^\vee\simeq R[y]/(y^p) \tag{6.4}
$$

as algebras.

To identify the group law, transpose multiplication in $A$. Since $\lambda_1(ab)$ can be nonzero only when the total degree is one,

$$
\Delta^D(y)=y\otimes1+1\otimes y. \tag{6.5}
$$

Also $\varepsilon^D(y)=0$ and $S^D(y)=-y$. Therefore (6.4) is a Hopf isomorphism and

$$
\alpha_p^D\simeq\alpha_p. \tag{6.6}
$$

This self-duality is canonical once $\alpha_p$ is presented as the Frobenius kernel with its standard coordinate. More intrinsically, scalar automorphisms of $\alpha_p$ act contragrediently on the dual, so one should not turn the displayed coordinate into an unstated universal normalization.

### 6.3 The pairing behind self-duality

Under the isomorphism above, evaluation gives a perfect pairing

$$
\alpha_p\times\alpha_p\longrightarrow\mathbf G_m. \tag{6.7}
$$

For a $k$-algebra $C$ over a field of characteristic $p$, it can be expressed through the truncated exponential

$$
E(X)=\sum_{i=0}^{p-1}\frac{X^i}{i!}.
$$

If $x^p=y^p=0$ and the tensor nilpotence is interpreted in the coordinate algebra, evaluation is represented by

$$
E(xy)=\sum_{i=0}^{p-1}\frac{x^iy^i}{i!}. \tag{6.8}
$$

The Hopf identities, rather than an unrestricted analytic exponential identity, ensure bilinearity in the universal quotient. Formula (6.8) is useful intuition: an additive infinitesimal parameter produces a multiplicative infinitesimal character.

### 6.4 What does not generalize naively

The same basis computation for $R[t]/(t^{p^r})$ with primitive $t$ produces a divided-power algebra on the dual. For $r>1$, factorials divisible by $p$ cannot be inverted, so the argument that one generator $\lambda_1$ produces the whole dual fails. Thus one must not infer $\alpha_{p^r}^D\simeq\alpha_{p^r}$ from the $r=1$ calculation.

Likewise, equality of tangent-space dimensions does not imply duality or isomorphism. Both $\alpha_p$ and $\mu_p$ have one-dimensional tangent space, yet

$$
\alpha_p^D\simeq\alpha_p,\qquad
\mu_p^D\simeq\underline{\mathbf Z/p\mathbf Z}.
$$

The full multiplication and coproduct, not first-order data, decide the answer.

## 7. Exact sequences and reversal of subquotients

### 7.1 Why exactness needs flatness

Duality should turn a quotient into a subgroup and a subgroup into a quotient. In the finite-flat category, those words have the precise meaning fixed in Book 46. A sequence

$$
0\longrightarrow H\xrightarrow{i}G\xrightarrow{q}Q\longrightarrow0 \tag{7.1}
$$

is exact when $H$ is the scheme-theoretic kernel of $q$ and $q$ is faithfully flat, equivalently when $Q$ represents the faithfully flat sheaf quotient $G/H$. All three groups are assumed finite locally free and commutative.

These hypotheses cannot be shortened to pointwise exactness. Nor can one dualize an arbitrary closed kernel that is not flat: its coordinate algebra may not be projective, so its linear dual need not represent a finite locally free group. Cartier duality is exact on the exact category just described, not on a category obtained by admitting every finite closed subscheme.

### 7.2 The exactness theorem

**Theorem 7.1 (exactness of Cartier duality).** The dual of (7.1) is a faithfully flat exact sequence

$$
0\longrightarrow Q^D\xrightarrow{q^D}G^D
\xrightarrow{i^D}H^D\longrightarrow0. \tag{7.2}
$$

Thus Cartier duality reverses kernels and quotients. Formation of (7.2) commutes with arbitrary base change.

**Proof strategy.** Merely dualizing the underlying short sequence of $R$-modules proves only that one dual map is surjective and the other injective; it does not prove faithful flatness over a dual Hopf subalgebra. The algebraic heart is the finite-projective Hopf exactness lemma below. That lemma dualizes the kernel relation and the entire torsor identity together. Biduality then explains conceptually why no term can be lost.

Write

$$
B=\mathcal O(Q),\qquad A=\mathcal O(G),\qquad C=\mathcal O(H).
$$

The maps in (7.1) correspond to Hopf maps

$$
B\hookrightarrow A\twoheadrightarrow C. \tag{7.3}
$$

The first is faithfully flat, the second is surjective, and

$$
C\simeq A\otimes_B R,
$$

where $B\to R$ is the counit. The torsor identity is

$$
A\otimes_BA\xrightarrow{\sim}A\otimes_RC. \tag{7.4}
$$

We use the following finite-projective Hopf lemma. Suppose that $B\to A\to C$ are Hopf maps between commutative, cocommutative Hopf $R$-algebras finite projective over $R$, and that

$$
C=A/AB^+,\qquad B=A^{\operatorname{co}C},\qquad
A\otimes_BA\xrightarrow{\sim}A\otimes_RC, \tag{7.5}
$$

with $A$ faithfully flat over $B$. Then the transposed Hopf maps fit into

$$
C^\vee\longrightarrow A^\vee\longrightarrow B^\vee,
$$

where

$$
\begin{aligned}
A^\vee/A^\vee(C^\vee)^+&\xrightarrow{\sim}B^\vee,\\
A^\vee\otimes_{C^\vee}A^\vee&\xrightarrow{\sim}
A^\vee\otimes_RB^\vee.
\end{aligned} \tag{7.6}
$$

Moreover $A^\vee$ is finite locally free and faithfully flat over $C^\vee$. These conclusions commute with arbitrary extension of scalars.

Here is why finite projectivity is essential in this lemma. The inclusion $B\to A$ is universally injective, so its finitely presented cokernel is flat and hence projective; the quotient $A\to C$ also splits as an $R$-module map because $C$ is projective. Their transposes are therefore respectively surjective and universally injective. The remaining claims are the following torsor matrix calculation.

We give the basis calculation more explicitly, because this is the decisive exactness step. Let

$$
r:A^\vee\longrightarrow B^\vee
$$

be restriction and let $j:C^\vee\hookrightarrow A^\vee$ be precomposition with $A\twoheadrightarrow C$. Put

$$
J=A^\vee j((C^\vee)^+).
$$

If $b\in B=A^{\operatorname{co}C}$, $u\in A^\vee$, and $v\in(C^\vee)^+$, then

$$
(u\,j(v))(b)
=\sum u(b_{(1)})v(\overline{b_{(2)}})
=u(b)v(1)=0. \tag{7.6a}
$$

Thus restriction induces a surjection

$$
\overline r:A^\vee/J\longrightarrow B^\vee. \tag{7.6b}
$$

To prove that it is injective and simultaneously obtain the torsor identity, localize on $R$ so that the three split module sequences have compatible bases. In those bases write the original canonical map and its inverse as

$$
\begin{aligned}
\beta(a\otimes a')&=\sum aa'_{(1)}\otimes\overline{a'_{(2)}},\\
\beta^{-1}(a\otimes\overline c)&=
\sum aS(\widetilde c_{(1)})\otimes \widetilde c_{(2)},
\end{aligned} \tag{7.6c}
$$

where $\widetilde c\in A$ is any lift of $\overline c\in C$; changing the lift by $AB^+$ changes the displayed tensor by the balancing relation over $B$. Now transpose the matrix coefficients in the $A$-, $B$-, and $C$-slots, using multiplication in $A$ to identify the transpose coproduct on $A^\vee$. The two identities $\beta^{-1}\beta=1$ and $\beta\beta^{-1}=1$ become, respectively,

$$
\ker r=J
$$

and bijectivity of

$$
\Theta:A^\vee\otimes_{C^\vee}A^\vee
\longrightarrow A^\vee\otimes_RB^\vee,\qquad
x\otimes y\longmapsto
\sum xy_{(1)}\otimes r(y_{(2)}). \tag{7.6d}
$$

No dimension count is being substituted here: (7.6c) supplies inverse matrices for (7.6d), while (7.6a) is exactly the balancing relation that removes $(C^\vee)^+$. Consequently $\overline r$ is an isomorphism and $\Theta$ is the canonical torsor map. The same inverse matrices exhibit $A^\vee$ locally as a finite projective $C^\vee$-module of the constant positive rank $\operatorname{rk}_RB$; it is therefore faithful. This proves (7.6) and faithful flatness. Every construction used a split finite-projective sequence, so tensoring with an arbitrary $R$-algebra preserves the calculation. Notice that all three parts of (7.5) are used: dualizing a raw equalizer alone would not justify the result after a nonflat base change.

The exact Hopf-algebra criterion from Book 45 says that (7.3)--(7.4) satisfy the hypotheses of the lemma. In particular, the transpose

$$
A^\vee\twoheadrightarrow B^\vee
$$

defines $Q^D$ as a closed subgroup of $G^D$, while the transpose

$$
C^\vee\hookrightarrow A^\vee
$$

defines $i^D:G^D\to H^D$. The first identity in (7.6) says exactly that $Q^D$ is its scheme-theoretic kernel. The second is the torsor identity for $G^D\to H^D$ under $Q^D$, and the final assertion of the lemma says that this map is faithfully flat. Hence (7.2) is exact.

Ranks now give

$$
|G^D|=|G|=|H|\,|Q|=|H^D|\,|Q^D|. \tag{7.7}
$$

All module splittings and tensor-dual identifications in the lemma commute with extension of scalars, and the represented torsor sequence (7.1) does as well. Thus the dual exact sequence is preserved by arbitrary base change. $\square$

One may also close the proof conceptually. Once the kernel is identified and the candidate quotient has the correct finite locally free rank, dualizing the resulting sequence again and using biduality recovers (7.1); a failure of faithful flatness would contradict the original torsor after a faithfully flat local check. This is why biduality and rank are so effective together.

### 7.3 Closed subgroups and their annihilators

Let $H\hookrightarrow G$ be a finite locally free closed subgroup. Its quotient $G/H$ exists and is finite locally free, so

$$
0\to H\to G\to G/H\to0
$$

is exact. Duality gives

$$
0\to(G/H)^D\longrightarrow G^D\longrightarrow H^D\to0. \tag{7.8}
$$

The first term is the subgroup of characters trivial on $H$. It is called the **annihilator** of $H$ and written

$$
H^\perp=\ker(G^D\to H^D). \tag{7.9}
$$

Thus there is a canonical identification

$$
H^\perp\simeq(G/H)^D. \tag{7.10}
$$

Ranks satisfy

$$
|H^\perp|=\frac{|G|}{|H|},\qquad
|H|\,|H^\perp|=|G| \tag{7.11}
$$

on each connected component of the base. This is a length statement, not a count of characters over a field.

### 7.4 Double annihilators

Biduality identifies $G$ with $G^{DD}$. Under this identification,

$$
(H^\perp)^\perp=H. \tag{7.12}
$$

Here the left annihilator is taken inside $G^{DD}$. To prove the equality, dualize (7.8). The kernel of $G\to(H^\perp)^D$ is precisely $H$, while the definition of the second annihilator gives the same kernel. Alternatively, one inclusion follows because every character in $H^\perp$ is trivial on $H$, and equality follows from (7.11).

The rank argument is legitimate only because both subgroup schemes are finite locally free. Equality on geometric points would be insufficient in characteristic dividing the order.

### 7.5 Kernels and images under a morphism

Suppose $f:G\to H$ admits a finite-flat image factorization

$$
G\twoheadrightarrow I\hookrightarrow H, \tag{7.13}
$$

with finite locally free kernel $K$. Dualizing the two exact sequences gives

$$
0\to I^D\to G^D\to K^D\to0
$$

and

$$
0\to(H/I)^D\to H^D\to I^D\to0.
$$

It follows that

$$
\ker(f^D)\simeq(H/I)^D,\qquad
\operatorname{im}(f^D)\simeq I^D,\qquad
\operatorname{coker}(f^D)\simeq K^D, \tag{7.14}
$$

where image and cokernel are understood in the finite-flat exact sense.

Without the factorization hypotheses, (7.14) is not a valid automatic statement. Book 46 exhibited morphisms over a DVR whose scheme-theoretic kernel is not flat and whose generic image closure is not a faithfully flat image. Duality does not turn such a morphism into an admissible exact sequence by force. It preserves the exact structure that exists.

### 7.6 A worked cyclic sequence

For positive integers $a,b$, Book 46 established

$$
0\to\mu_a\to\mu_{ab}\xrightarrow{[a]}\mu_b\to0 \tag{7.15}
$$

over every base. Dualizing and using (5.7) yields

$$
0\to\underline{\mathbf Z/b\mathbf Z}
\longrightarrow\underline{\mathbf Z/ab\mathbf Z}
\longrightarrow\underline{\mathbf Z/a\mathbf Z}\to0. \tag{7.16}
$$

The first map sends $1$ to $a$, and the second is reduction modulo $a$. This elementary sequence checks the arrow order. It remains exact in residue characteristics dividing $ab$, even though (7.15) then contains nonreduced groups. The proof through Cartier duality uses finite flat exactness, not surjectivity on roots in a chosen ring.

### 7.7 Sums, intersections, and annihilator identities

Annihilators do more than reverse a single inclusion: they reverse the entire admissible subgroup calculus. Let $H,J\subset G$ be finite locally free closed subgroups. Assume that their scheme-theoretic intersection and their sum are finite locally free, where the sum is the represented image of

$$
H\times J\longrightarrow G,\qquad(h,j)\longmapsto h+j. \tag{7.17}
$$

These hypotheses hold over a field. Over a DVR they hold for the saturated intersection and saturated generic sum inside a fixed finite-flat ambient group, but need not hold for the raw scheme-theoretic image over an arbitrary base. Under them,

$$
(H+J)^\perp=H^\perp\cap J^\perp, \tag{7.18}
$$

because a character is trivial on the sum exactly when it is trivial on each summand. Applying double annihilators gives the companion formula

$$
(H\cap J)^\perp=H^\perp+J^\perp. \tag{7.19}
$$

The second identity can also be proved from the exact sequence

$$
0\longrightarrow H\cap J\longrightarrow H\times J
\xrightarrow{(h,j)\mapsto h-j}H+J\longrightarrow0. \tag{7.20}
$$

Dualizing (7.20) reverses the sequence, and the two maps become restriction and multiplication of characters. This proof makes clear why flatness of the intersection and the represented image cannot be hidden.

There is also a quotient version. If $H\subset J\subset G$, then restriction gives an exact sequence

$$
0\longrightarrow J^\perp\longrightarrow H^\perp
\longrightarrow(J/H)^D\longrightarrow0, \tag{7.21}
$$

and hence

$$
H^\perp/J^\perp\simeq(J/H)^D. \tag{7.22}
$$

Thus $H\mapsto H^\perp$ is an inclusion-reversing bijection between finite locally free subgroups of $G$ and finite locally free subgroups of $G^D$, wherever the admissible sum and intersection operations exist. It exchanges the identity with the whole group, products with intersections in the sense of (7.18), and subquotients with reversed dual subquotients. This is the precise finite-flat replacement for the annihilator lattice of a finite abelian group.

## 8. Bilinear pairings and perfectness

### 8.1 Pairings as morphisms into duals

Let $G,H$ be finite locally free commutative $S$-group schemes. A **bilinear pairing** is a morphism

$$
b:G\times_SH\longrightarrow\mathbf G_m \tag{8.1}
$$

that is a group homomorphism in each variable. Fixing the first variable produces a character of $H$, hence a homomorphism

$$
b^\sharp:G\longrightarrow H^D,\qquad
g\longmapsto(h\mapsto b(g,h)). \tag{8.2}
$$

Fixing the second produces

$$
{}^\sharp b:H\longrightarrow G^D. \tag{8.3}
$$

These maps are Cartier transposes of one another:

$$
{}^\sharp b=(b^\sharp)^D\circ\delta_H. \tag{8.4}
$$

Conversely, any map $G\to H^D$ followed by evaluation defines a bilinear pairing. Thus

$$
\operatorname{Bil}(G,H;\mathbf G_m)
\cong\operatorname{Hom}(G,H^D)
\cong\operatorname{Hom}(H,G^D). \tag{8.5}
$$

Formula (8.5) is the universal working form of Cartier duality. It converts a two-variable problem into an ordinary morphism problem, with the second equivalence accounting for transposition.

### 8.2 Perfect pairings

The pairing $b$ is **perfect** if $b^\sharp:G\to H^D$ is an isomorphism. By (8.4) and biduality, this is equivalent to ${}^\sharp b:H\to G^D$ being an isomorphism. A perfect pairing therefore forces

$$
|G|=|H|. \tag{8.6}
$$

The converse is false: equality of ranks does not imply that a pairing is perfect. One must also prove that its radical is trivial as a subgroup scheme. If the kernel of $b^\sharp$ is finite locally free and the map has a finite-flat image factorization, trivial kernel plus equal rank suffices. Over a field those flatness qualifications are automatic; over a general base they must be supplied.

Evaluation $G\times G^D\to\mathbf G_m$ is perfect by biduality. Hence every finite locally free commutative group possesses a canonical perfect pairing with its Cartier dual, even when neither group has enough geometric points to reveal it.

### 8.3 Radicals and degeneracy

The **left radical** and **right radical** of $b$ are

$$
\operatorname{rad}_L(b)=\ker(b^\sharp),\qquad
\operatorname{rad}_R(b)=\ker({}^\sharp b). \tag{8.7}
$$

They are always finite closed subgroup schemes. They need not be finite locally free over an arbitrary base unless the corresponding kernels are flat. When they are finite locally free and the maps admit flat image factorizations, duality shows that the quotient pair

$$
G/\operatorname{rad}_L(b),\qquad
H/\operatorname{rad}_R(b)
$$

inherits a perfect pairing between the finite-flat images. This is the scheme-theoretic analogue of dividing a bilinear form by its radicals.

A pairing can be nondegenerate on every geometric point set and still require a flatness argument globally. Conversely, in characteristic $p$, a perfect pairing can look completely degenerate on geometric points: the perfect self-pairing of $\alpha_p$ has only the identity point in either variable over an algebraically closed field.

### 8.4 Pairings killed by an integer

If $G$ is killed by $n$, every pairing (8.1) factors uniquely through $\mu_n$:

$$
G\times H\longrightarrow\mu_n\hookrightarrow\mathbf G_m. \tag{8.8}
$$

The same is true if $H$ is killed by $n$. Thus for $n$-torsion group schemes it is customary to display the target as $\mu_n$. The induced map is still a map into the Cartier dual, because $\mu_n$ sits in $\mathbf G_m$.

This observation distinguishes two roles of $\mu_n$. It is itself a finite group scheme with dual $\underline{\mathbf Z/n\mathbf Z}$, and it is also the natural value group for pairings of $n$-torsion objects. No chosen primitive root identifies it with a constant cyclic group over a general base.

## 9. Orthogonality and rank calculus

### 9.1 Orthogonal subgroup schemes

Let $b:G\times H\to\mathbf G_m$ be perfect, and let $K\hookrightarrow G$ be a finite locally free closed subgroup. The **orthogonal complement** of $K$ is

$$
K^\perp=\ker\bigl(H\xrightarrow{{}^\sharp b}G^D\longrightarrow K^D\bigr). \tag{9.1}
$$

Equivalently, it represents those $h$ for which $b(k,h)=1$ for every $k$, functorially on test schemes. Since ${}^\sharp b$ is an isomorphism, $K^\perp$ is the inverse image of the annihilator of $K$ in $G^D$. Exactness gives

$$
K^\perp\simeq(G/K)^D. \tag{9.2}
$$

In particular $K^\perp$ is finite locally free and

$$
|K^\perp|=\frac{|G|}{|K|}. \tag{9.3}
$$

The perfect pairing descends to a perfect pairing

$$
(G/K)\times K^\perp\longrightarrow\mathbf G_m. \tag{9.4}
$$

This is often the most efficient way to identify the dual of a quotient.

### 9.2 Double orthogonals

Assume $b$ perfect. Using the transpose pairing to regard $G$ as $H^D$, one obtains

$$
(K^\perp)^\perp=K. \tag{9.5}
$$

The first inclusion is formal from the definition. For equality, either apply double-annihilator biduality or compare ranks:

$$
|(K^\perp)^\perp|
=\frac{|H|}{|K^\perp|}
=\frac{|G|}{|G|/|K|}=|K|.
$$

Because the inclusion is between finite locally free closed subgroup schemes of equal rank and arises inside an exact annihilator sequence, it is an isomorphism. Merely comparing the number of geometric points would not prove this.

### 9.3 Isotropic and Lagrangian subgroups

Suppose $G=H$ and $b$ is a perfect alternating pairing. A finite locally free subgroup $K\subset G$ is **isotropic** if $K\subseteq K^\perp$. It is **Lagrangian** if $K=K^\perp$. Rank calculus gives

$$
|K|^2\le |G|
$$

for an isotropic subgroup, in the divisibility sense supplied by the quotient $K^\perp/K$. A Lagrangian has

$$
|K|^2=|G|. \tag{9.6}
$$

Equality of ranks plus isotropy implies the Lagrangian condition under the finite-flat subgroup hypotheses.

For a rank-$n^2$ elliptic torsion group $E[n]$, a cyclic finite-flat subgroup of rank $n$ is therefore a natural candidate for a Lagrangian. When $n$ is invertible, this recovers the elementary fact that a cyclic line in a two-dimensional symplectic module is its own orthogonal. When $n$ is not invertible, the statement must be checked as one about subgroup schemes.

### 9.4 Orthogonals in an exact sequence

Suppose $K_1\subseteq K_2\subseteq G$. Reversal is visible in

$$
K_2^\perp\subseteq K_1^\perp. \tag{9.7}
$$

Moreover, the perfect pairing induces a perfect pairing

$$
(K_2/K_1)\times(K_1^\perp/K_2^\perp)\longrightarrow\mathbf G_m. \tag{9.8}
$$

To prove it, dualize

$$
0\to K_2/K_1\to G/K_1\to G/K_2\to0
$$

and identify the two duals by (9.2). Thus

$$
(K_2/K_1)^D\simeq K_1^\perp/K_2^\perp. \tag{9.9}
$$

This formula is the finite-flat version of the duality between a subquotient and the reversed orthogonal subquotient. It will later underlie annihilator statements in cohomology, but no cohomology is used here.

## 10. Multiplication kernels and self-duality

### 10.1 Duality commutes with multiplication

For any integer $n$, multiplication $[n]_G:G\to G$ is a homomorphism. Precomposing a character with $[n]$ raises that character to the $n$th power. Consequently

$$
([n]_G)^D=[n]_{G^D}. \tag{10.1}
$$

This also follows on Hopf algebras: the $n$-fold convolution power on $A$ transposes to the $n$-fold convolution power on $A^\vee$. Negative $n$ are handled by the antipode.

If $G$ is killed by a positive integer $n$, then so is $G^D$. More generally, exactly the same integers annihilate $G$ and $G^D$, because $[n]_{G^D}=0$ dualizes back to $[n]_G=0$ under biduality. Thus they have the same exponent whenever that terminology is being used. The primary decomposition of Book 46 is preserved:

$$
\left(\prod_{\ell\mid n}G[\ell^{v_\ell(n)}]\right)^D
\simeq\prod_{\ell\mid n}G[\ell^{v_\ell(n)}]^D. \tag{10.2}
$$

### 10.2 Dual of a multiplication kernel

Let $K=G[n]$ and assume $K$ is finite locally free. The inclusion $K\hookrightarrow G$ gives an exact sequence

$$
0\to(G/K)^D\to G^D\to K^D\to0. \tag{10.3}
$$

The annihilator of $K$ contains the image of $[n]_{G^D}$, because a character of the form $n\chi$ is trivial on $G[n]$. Under a finite-flat image factorization for $[n]$, this containment is equality:

$$
G[n]^D\simeq G^D/[n]G^D. \tag{10.4}
$$

Here $[n]G^D$ means the represented finite-flat image, not the pointwise set of $n$-multiples. Formula (10.4) should not be asserted when $G[n]$ is nonflat or when $[n]$ has no admissible flat image. The quotient statement is a consequence of exactness, not a formal manipulation of kernels.

For a finite group killed by $n$, (10.4) reduces to $G^D=G[n]^D$, since $[n]G^D=0$. For larger ambient smooth groups, multiplication kernels become especially important, even though Cartier duality is applied only to the finite kernel.

### 10.3 Elementary self-dual patterns

A **self-duality** of $G$ is an isomorphism $G\xrightarrow{\sim}G^D$, equivalently a perfect pairing $G\times G\to\mathbf G_m$. It is extra structure; biduality alone identifies $G$ with $G^{DD}$, not with $G^D$.

The group $\alpha_p$ has the self-duality of Chapter 6. The product

$$
\underline M\times D(M)
$$

is self-dual after exchanging its two factors, using the two evaluation pairings. By contrast, $\mu_n$ is generally not canonically self-dual: its dual is constant, and an isomorphism between them requires additional roots of unity and a choice even when it exists.

An alternating self-duality is more restrictive than an arbitrary one. A symmetric or alternating condition refers to the pairing after identifying both variables with $G$; it is not built into Cartier duality. In particular, the evaluation pairing between $G$ and $G^D$ has no reason to become alternating under an arbitrary self-duality.

### 10.4 Kernels of dual isogenies

The dual abelian scheme and its Poincaré bundle are constructed from rigidified line bundles in §14.1. We isolate their finite-kernel consequence here because it is the bridge from abstract multiplication kernels to Weil pairings. The argument below uses only that construction, its base-change property, and faithfully flat descent; it does not use the torsion perfectness later deduced from it.

Let $A$ and $B$ be abelian schemes over $S$, and let

$$
\varphi:A\longrightarrow B
$$

be an isogeny with finite locally free kernel. The dual homomorphism

$$
\varphi^\vee:B^\vee\longrightarrow A^\vee
$$

is again an isogeny. Put $H=\ker\varphi$. The quotient map $A\to B=A/H$ is an $H$-torsor, and descent of rigidified line bundles along this torsor identifies the kernel of $\varphi^\vee$.

Indeed, after a faithfully flat base change on a test scheme $T$, a point of $\ker\varphi^\vee(T)$ may be represented by a rigidified algebraically trivial line bundle $L$ on $B_T$ together with a trivialization of $\varphi_T^*L$. Translating that trivialization by $h\in H(T')$ changes it by a unit $\chi(h)$. The cocycle condition for descent says

$$
\chi(h+h')=\chi(h)\chi(h'),
$$

so $\chi:H_{T'}\to\mathbf G_{m,T'}$ is a character. Changing the chosen trivialization multiplies it by a unit pulled back from $T'$ and does not change $\chi$. Conversely, a character of $H$ twists the canonical descent datum on the trivial line bundle over $A$ and descends it to a rigidified line bundle $M$ on $B$ whose pullback is trivial. For every section $b$ of $B$, lift $b$ fppf-locally to a section $a$ of $A$. Then the pullback of $t_b^*M\otimes M^{-1}$ to $A$ is $t_a^*\varphi^*M\otimes(\varphi^*M)^{-1}$ and is trivial. Faithful descent makes $t_b^*M\otimes M^{-1}$ trivial; the translation criterion proved in §14.1 therefore puts $M$ in $\operatorname{Pic}^0_{B/S}$. These constructions are inverse, compatible with further base change, and descend from $T'$ to $T$. Thus the character functor of $H$ is canonically represented by $\ker\varphi^\vee$:

$$
H^D\xrightarrow{\sim}\ker\varphi^\vee. \tag{10.5}
$$

Under this isomorphism, Cartier evaluation is the restriction of the Poincaré biextension. It gives a canonical perfect pairing

$$
\ker\varphi\times\ker\varphi^\vee\longrightarrow\mathbf G_m. \tag{10.6}
$$

Therefore

$$
(\ker\varphi)^D\simeq\ker\varphi^\vee. \tag{10.7}
$$

This is the geometric source of many self-duality phenomena. Taking $\varphi=[n]_A$, whose dual is $[n]_{A^\vee}$, gives

$$
A[n]^D\simeq A^\vee[n]. \tag{10.8}
$$

Unlike (10.4), this formula does not attempt to dualize the whole abelian scheme. It dualizes the finite locally free multiplication kernel and identifies the result using the dual isogeny. This distinction is essential because an abelian scheme is proper, positive-dimensional, and not an object of the finite Cartier-duality category.

## 11. Fibers and structural types over fields

### 11.1 Fiberwise duality without loss of rank

For $G/S$ finite locally free and every point $s\in S$,

$$
(G_s)^D\simeq(G^D)_s. \tag{11.1}
$$

Thus generic and special fibers are dualized by the same operation, and

$$
|G_s|=|(G_s)^D|.
$$

This statement is valid over arbitrary residue fields and requires no perfection. What can require perfection is the interpretation of a fiber through reducedness, connected components, and a clean connected–étale sequence.

Over a field $k$, Cartier duality is an anti-equivalence on finite commutative $k$-group schemes. It sees the entire finite-dimensional Hopf algebra. Only in the étale case may that structure be replaced by geometric points with Galois action.

### 11.2 Multiplicative type and étale groups

A finite commutative group scheme $G/k$ is **of multiplicative type** if after a separable field extension it becomes diagonalizable, equivalently isomorphic to $D(M)$ for a finite abelian group $M$ after such an extension. Over a general base, the same definition is made fppf locally.

Since constant finite groups are finite étale and diagonalizable groups are their Cartier duals, descent and base change give:

**Theorem 11.1.** For a finite locally free commutative group scheme $G/S$,

$$
G\text{ is finite étale}\quad\Longleftrightarrow\quad G^D\text{ is of multiplicative type}, \tag{11.2}
$$

and

$$
G\text{ is of multiplicative type}\quad\Longleftrightarrow\quad G^D\text{ is finite étale}. \tag{11.3}
$$

These assertions are fppf local. No perfection hypothesis is needed when multiplicative type is defined by fppf-local diagonalizability and étaleness is used in its geometric sense.

The theorem does **not** say that connected and étale exchange. In characteristic $p$, $\mu_p$ is connected and dual to an étale group, whereas $\alpha_p$ is connected and dual to another connected group. Connectedness alone has no single dual adjective.

### 11.3 The connected–étale sequence and its dual

Let $k$ be a perfect field. Book 46 constructed

$$
0\to G^0\to G\to G^{\mathrm{et}}\to0. \tag{11.4}
$$

Duality gives

$$
0\to(G^{\mathrm{et}})^D\to G^D\to(G^0)^D\to0. \tag{11.5}
$$

The first term is of multiplicative type. It is the maximal multiplicative-type subgroup of $G^D$: a multiplicative-type subgroup dualizes to an étale quotient of $G$, which factors through the maximal étale quotient $G^{\mathrm{et}}$.

Thus $G$ is connected precisely when $G^D$ has no nontrivial multiplicative-type subgroup. This is the correct dual shadow of connectedness over a perfect field. It does not imply that $G^D$ is connected.

The perfection assumption belongs to the clean form of (11.4), not to Cartier duality itself. Over an imperfect field, reduced finite schemes need not be geometrically reduced, and the maximal étale quotient requires more careful formulation. Base change and biduality remain valid without change.

### 11.4 Henselian local bases

Let $R$ be a henselian local ring with perfect residue field $k$. For $G/R$ finite locally free and commutative, Book 46 gives

$$
0\to G^0\to G\to G^{\mathrm{et}}\to0, \tag{11.6}
$$

where $G^0$ has connected special fiber and $G^{\mathrm{et}}$ is finite étale. Dualizing,

$$
0\to(G^{\mathrm{et}})^D\to G^D\to(G^0)^D\to0. \tag{11.7}
$$

Again $(G^{\mathrm{et}})^D$ is the maximal finite multiplicative-type subgroup of $G^D$. Henselianity is used to lift idempotents and the étale quotient; perfection identifies the reduced component quotient cleanly. Neither is needed for the bare equality $(G_k)^D=(G^D)_k$.

The mixed-characteristic example

$$
\mu_p^D=\underline{\mathbf Z/p\mathbf Z}
$$

shows the force of (11.7): a connected special fiber on one side can correspond to a fully étale object on the other. Duality transports rank and Hopf structure, not connectedness.

### 11.5 Order-$p$ comparison

Over an algebraically closed field of characteristic $p$, the basic groups and duals are

$$
\begin{array}{c|c|c}
G&G^D&\text{geometric behavior}\\
\hline
\underline{\mathbf Z/p\mathbf Z}&\mu_p&\text{étale versus connected multiplicative}\\
\mu_p&\underline{\mathbf Z/p\mathbf Z}&\text{connected multiplicative versus étale}\\
\alpha_p&\alpha_p&\text{connected additive on both sides}.
\end{array} \tag{11.8}
$$

All six displayed occurrences have order $p$. Point sets distinguish only the constant group from the other two; tangent spaces distinguish the constant group but not $\mu_p$ from $\alpha_p$; Cartier duality distinguishes all three through the full Hopf structure.

### 11.6 The local-local remainder

Over a perfect field $k$ of characteristic $p$, a finite commutative $p$-group scheme is called **local-local** if both $G$ and $G^D$ are connected. The name isolates the part that is neither detected by the maximal étale quotient nor produced by dualizing such a quotient. The group $\alpha_p$ is local-local; $\mu_p$ is connected but not local-local because its dual is étale.

There is a canonical three-step filtration

$$
0\subset G^{\mathrm{mult}}\subset G^0\subset G, \tag{11.9}
$$

where

$$
G^{\mathrm{mult}}=\bigl((G^D)^{\mathrm{et}}\bigr)^D. \tag{11.10}
$$

The first term is the maximal subgroup of multiplicative type, the last quotient $G/G^0$ is étale, and the middle quotient $G^0/G^{\mathrm{mult}}$ is local-local. To see maximality, dualize a multiplicative-type subgroup of $G$: it becomes an étale quotient of $G^D$ and hence factors through $(G^D)^{\mathrm{et}}$. To see that the middle quotient has connected dual, dualize its defining exact sequence and use maximality of the étale quotient on the dual side. The $p$-primary hypothesis ensures that a multiplicative-type group is connected, so $G^{\mathrm{mult}}\subset G^0$.

Duality reverses the filtration. The étale quotient of $G$ corresponds to the multiplicative subgroup of $G^D$, the multiplicative subgroup of $G$ corresponds to the étale quotient of $G^D$, and the local-local middle part dualizes within the same class. It is important that this is a filtration, not usually a product decomposition. For instance, ordinary elliptic $p$-torsion over an algebraically closed field fits into

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\underline{\mathbf Z/p\mathbf Z}\longrightarrow0, \tag{11.11}
$$

and the corresponding connected–étale extension over a more general base need not split in a family, even when its geometric fibers do. Supersingular elliptic $p$-torsion is local-local: it is connected, and the principal-polarization duality established in Chapter 14 makes its dual connected as well. Thus the connected–étale label alone does not measure the whole residue-characteristic structure.

Outside the $p$-primary category the three adjectives overlap. A group of order prime to $p$ is étale, while a diagonalizable group of such order is also étale. The filtration (11.9) is therefore intended for the residue-characteristic primary part; the prime-to-$p$ part is already governed by finite étale descent.

## 12. Duality over DVRs and schematic closure

### 12.1 Generic and special fibers

Let $R$ be a DVR with fraction field $K$ and residue field $k$. For a finite flat commutative $R$-group $G$,

$$
(G^D)_K\simeq(G_K)^D,\qquad
(G^D)_k\simeq(G_k)^D. \tag{12.1}
$$

On Hopf algebras, the integral lattice $A\subset A_K$ is replaced by its dual lattice

$$
A^\vee=\{f\in A_K^\vee:f(A)\subseteq R\}. \tag{12.2}
$$

Thus duality retains valuation depth. Two distinct Hopf lattices in the same generic algebra can yield distinct dual lattices, even when their generic duals are isomorphic. The generic-fiber functor does not determine the integral dual model unless the original integral model is fixed.

### 12.2 Closure and annihilator commute

Let $H_K\hookrightarrow G_K$ be a closed subgroup, and let $H\hookrightarrow G$ be its schematic closure. By the DVR closure theorem, $H$ is finite flat. Define

$$
H^\perp=\ker(G^D\to H^D). \tag{12.3}
$$

This is finite flat by exactness, and its generic fiber is the annihilator

$$
H_K^\perp=\ker((G_K)^D\to H_K^D). \tag{12.4}
$$

Since $H^\perp$ is a finite flat closed subgroup of $G^D$ with generic fiber $H_K^\perp$, uniqueness of finite-flat closure inside a fixed ambient group gives

$$
H^\perp=\overline{H_K^\perp}^{\,G^D}. \tag{12.5}
$$

This formula is one of the most useful compatibilities in integral applications: close first and annihilate, or annihilate generically and close, with the same result.

### 12.3 Quotients and closure

The exact sequence

$$
0\to H\to G\to G/H\to0
$$

dualizes to

$$
0\to H^\perp\to G^D\to H^D\to0. \tag{12.6}
$$

Consequently

$$
(G/H)^D\simeq H^\perp,\qquad
(G^D/H^\perp)^D\simeq H. \tag{12.7}
$$

Every group in these formulas is finite flat. If one used the raw scheme-theoretic intersection or image of arbitrary models without saturation, flatness could fail and duality would no longer apply. The fixed ambient model and the saturated closure are part of the statement.

Flat extensions of DVRs preserve closure and Cartier duality, so (12.5)--(12.7) commute with such scalar extension. For a nonflat change of base, Cartier duality itself still commutes with base change, but schematic closure need not; these are distinct operations with distinct hypotheses.

### 12.4 Henselian consequences

Assume now that $R$ is henselian with perfect residue field. The connected–étale sequence and its dual multiplicative-type sequence from §11.4 may be read on the special fiber. A finite étale model is dual to a finite multiplicative-type model, and both are uniquely controlled by the corresponding descent data.

If $R$ has mixed characteristic $(0,p)$ and contains the relevant generic roots of unity, the generic fibers of $\mu_{p^r}$ and $\underline{\mathbf Z/p^r\mathbf Z}$ may be isomorphic after a choice. Their integral models remain dual rather than canonically identical: one has connected special fiber, the other étale special fiber. Henselianity does not erase this distinction; it makes the étale part rigid.

### 12.5 Beyond DVRs

Cartier duality itself works over every base scheme for finite locally free commutative groups. The special strength of a DVR enters only when extending generic subgroups: torsion-free finite modules are free, so saturation produces finite flat closure. Over a Dedekind base, the same argument works locally and glues.

Over a higher-dimensional normal base, a closure may be torsion-free without being locally free. In that setting its Cartier dual is not automatically an object of the finite locally free category. One must either prove flatness separately or restrict the claim. Duality does not repair a defective closure.

### 12.6 Dual lattices and saturation

The closure formula has a useful linear-algebraic explanation. If $V$ is a finite-dimensional $K$-vector space and $L\subset V$ is an $R$-lattice, define

$$
L^\#=\{\lambda\in V^\vee:\lambda(L)\subset R\}. \tag{12.8}
$$

Then $L^\#$ is a lattice and $(L^\#)^\#=L$. Moreover, for a saturated submodule $M\subset L$, restriction is surjective,

$$
L^\#\longrightarrow M^\#, \tag{12.9}
$$

because $L/M$ is torsion-free and hence free. Its kernel is

$$
M^0=\{\lambda\in L^\#:\lambda(M)=0\}, \tag{12.10}
$$

which is itself saturated. These are exactly the module facts behind integral annihilators.

For a finite-flat group $G=\operatorname{Spec}A$, formula (12.2) says that the coordinate lattice of $G^D$ is $A^\#$. If the closure $H$ of $H_K$ has coordinate algebra $C$, then $C$ is the torsion-free image of $A$ in $C_K$. Thus $A\twoheadrightarrow C$ is a saturated quotient, and (12.9) embeds $C^\vee$ as a saturated Hopf submodule of $A^\vee$. Exactness of Hopf structures converts this embedded dual into the faithfully flat map $G^D\to H^D$; its kernel is the annihilator closure. The Hopf equations are essential, but saturation is what prevents a vertical torsion layer from appearing.

This viewpoint also proves uniqueness in (12.5) without counting ranks. The closure of $H_K^\perp$ has a saturated coordinate quotient of $A^\vee$. The annihilator $H^\perp$ has the same generic quotient, and both are obtained by intersecting that generic quotient with the fixed lattice $A^\vee$. Hence their Hopf ideals coincide.

The dual-lattice operation reverses inclusions but not indices naively. If $L'\subset L$ has finite index, then $L^\#\subset(L')^\#$, and the quotient records the same valuation length. This is the integral analogue of rank reversal for annihilators. It explains how dual models can have opposite-looking special fibers while retaining the same generic rank and the same total defect along the closed point.

## 13. Finite-flat models and Tate-twisted module duals

### 13.1 From an étale generic fiber to a module

Let $K$ be a field with separable closure $K^s$ and absolute Galois group $\Gamma_K$. Suppose $G/K$ is finite étale, commutative, and killed by $n$, where $n$ is prime to $\operatorname{char}K$. Then

$$
M=G(K^s)
$$

is a finite continuous $\Gamma_K$-module killed by $n$. Because $n$ is invertible, $\mu_n$ is also finite étale, and the Cartier dual is determined by its geometric points. The character interpretation gives

$$
G^D(K^s)=\operatorname{Hom}\bigl(M,\mu_n(K^s)\bigr). \tag{13.1}
$$

The Galois action is the contragredient action with the natural action on roots of unity:

$$
(\sigma f)(m)=\sigma\bigl(f(\sigma^{-1}m)\bigr). \tag{13.2}
$$

This module is often denoted

$$
M^*(1)=\operatorname{Hom}_{\mathbf Z/n\mathbf Z}
\bigl(M,\mathbf Z/n\mathbf Z(1)\bigr), \tag{13.3}
$$

where $\mathbf Z/n\mathbf Z(1)=\mu_n(K^s)$. The notation does not choose an isomorphism $\mu_n\cong\mathbf Z/n\mathbf Z$ with trivial action. The parenthetical $(1)$ records precisely the Galois action that such a choice would conceal.

If $M$ is merely a finite abelian group killed by $n$, (13.1) is the safest notation. If $M$ is free over $\mathbf Z/n\mathbf Z$, one may separate it as the ordinary module dual tensored with $\mathbf Z/n\mathbf Z(1)$. For modules with more general exponent, $\operatorname{Hom}(M,\mu_n)$ remains canonical.

### 13.2 Why the twist is unavoidable

Choose a primitive $n$th root $\zeta_n\in K^s$. It identifies $\mu_n(K^s)$ with $\mathbf Z/n\mathbf Z$ as abstract groups. Under Galois,

$$
\sigma(\zeta_n)=\zeta_n^{\chi_n(\sigma)},
$$

so this identification changes the action by the mod-$n$ cyclotomic character. Thus the underlying abstract character group $\operatorname{Hom}(M,\mathbf Z/n\mathbf Z)$ becomes the Galois module

$$
\operatorname{Hom}(M,\mathbf Z/n\mathbf Z)\otimes\mathbf Z/n\mathbf Z(1)
$$

in the familiar free-module cases.

Forgetting the twist would make the evaluation pairing Galois invariant with values in a trivial module, which is false unless all $n$th roots of unity are fixed. The Tate twist is not an embellishment added by representation theory; it is the geometric action on the target $\mu_n$ of Cartier evaluation.

### 13.3 Dual models over a DVR

Let $R$ be a DVR with fraction field $K$, and assume $n$ is invertible in $K$. Let $\mathcal G/R$ be a finite flat commutative group killed by $n$ whose generic fiber is finite étale. It is a finite-flat model of

$$
M=\mathcal G(K^s).
$$

Then $\mathcal G^D$ is a finite-flat model of

$$
M^*(1)=\operatorname{Hom}(M,\mu_n(K^s)). \tag{13.4}
$$

This follows by combining arbitrary base change with (13.1):

$$
(\mathcal G^D)_K\simeq(\mathcal G_K)^D.
$$

The integral dual contains more information than the generic twisted dual module. It is the dual Hopf lattice, and its special fiber can be connected, étale, or mixed. For example, over a mixed-characteristic DVR,

$$
\underline{\mathbf Z/p\mathbf Z}^D=\mu_p
$$

turns an étale model of the trivial constant module into a multiplicative model of its cyclotomic dual.

### 13.4 Submodules, quotients, and exact models

Suppose

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0 \tag{13.5}
$$

is an exact sequence of finite-flat models over $R$. Its generic geometric points give

$$
0\to M'\to M\to M''\to0.
$$

Duality gives an exact model sequence

$$
0\to(\mathcal G'')^D\to\mathcal G^D\to(\mathcal G')^D\to0, \tag{13.6}
$$

whose generic module sequence is

$$
0\to(M'')^*(1)\to M^*(1)\to(M')^*(1)\to0. \tag{13.7}
$$

Thus finite-flat subobjects turn into finite-flat quotient models, and generic annihilators extend by schematic closure as in Chapter 12.

This chapter deliberately stops short of a general theory deciding which Galois modules admit finite-flat models or classifying all such models. Those existence, uniqueness, and extension questions belong to the next book. Here the reusable conclusion is narrower and exact: the dual of a chosen model is a chosen model of the Tate-twisted module dual, and admissible exact sequences reverse.

### 13.5 Limits of the geometric-point formula

The assumption that $n$ is prime to $\operatorname{char}K$ ensures that the relevant generic group schemes are étale and hence recoverable from geometric points. If the characteristic divides $n$, formula (13.1) as a statement about point groups can lose information. Cartier duality still exists and commutes with base change, but it must be computed from Hopf algebras or character functors.

For example, in characteristic $p$ the group of geometric points of $\alpha_p$ is trivial, while $\alpha_p^D\simeq\alpha_p$ is nontrivial. There is no contradiction: the equivalence between finite étale groups and Galois modules never applied.

### 13.6 Determinants, similitudes, and orthogonal modules

Suppose $M$ is a free $\mathbf Z/n\mathbf Z$-module of rank $2g$ with continuous $\Gamma_K$-action and a perfect alternating equivariant pairing

$$
e:M\times M\longrightarrow\mu_n(K^s). \tag{13.8}
$$

Equivariance means

$$
e(\sigma x,\sigma y)=\sigma(e(x,y))
=e(x,y)^{\chi_n(\sigma)}, \tag{13.9}
$$

where $\chi_n$ is the cyclotomic character modulo $n$. After choosing a symplectic basis and a primitive root of unity, the matrix $J$ of the pairing satisfies

$$
\rho(\sigma)^{\mathsf t}J\rho(\sigma)
=\chi_n(\sigma)J. \tag{13.10}
$$

Thus the representation is symplectic up to the cyclotomic similitude factor. Taking determinants gives

$$
(\det\rho(\sigma))^2=\chi_n(\sigma)^{2g}. \tag{13.11}
$$

For a symplectic similitude the sharper identity is

$$
\det\rho(\sigma)=\chi_n(\sigma)^g. \tag{13.12}
$$

This identity remains valid over the possibly nonreduced coefficient ring $\mathbf Z/n\mathbf Z$ and has no hidden sign. Apply the Pfaffian identity

$$
\operatorname{Pf}(U^{\mathsf t}JU)=\det(U)\operatorname{Pf}(J)
$$

to (13.10). Since $\operatorname{Pf}(aJ)=a^g\operatorname{Pf}(J)$ and the standard $J$ has unit Pfaffian, one obtains $\det(U)=a^g$ for every symplectic similitude of multiplier $a$. In rank two this becomes

$$
\det\rho=\chi_n. \tag{13.13}
$$

No primitive root is involved in the intrinsic assertion: changing the chosen root changes the displayed scalar coordinates but not the target $\mu_n$ or its Galois action.

If $N\subset M$ is a Galois-stable submodule corresponding to a finite étale subgroup, its orthogonal

$$
N^\perp=\{m\in M:e(N,m)=1\} \tag{13.14}
$$

is Galois stable by (13.9), and perfectness gives

$$
N^\perp\simeq(M/N)^*(1),\qquad
M/N^\perp\simeq N^*(1). \tag{13.15}
$$

Over a DVR, if the pairing comes from a perfect pairing of finite-flat models, the closure of $N^\perp$ is the schematic orthogonal of the closure of $N$. Formula (13.15) therefore survives integrally even when its special fiber ceases to be étale and can no longer be read from point modules.

## 14. Abelian schemes, torsion, and the Weil pairing

### 14.1 Why proper groups enter the story

Cartier duality is a theory of finite affine groups, whereas an abelian scheme $A/S$ is proper and positive-dimensional. The connection is through multiplication kernels. For every $n\ge1$, Book 46 established that

$$
A[n]=\ker([n]:A\to A)
$$

is finite locally free of rank $n^{2g}$ when $A$ has relative dimension $g$. It therefore has a Cartier dual.

The dual abelian scheme $A^\vee$ parametrizes algebraically trivial line bundles on $A$. Its universal Poincaré line bundle carries a biextension structure: it is multiplicative separately in the $A$- and $A^\vee$-variables. Restricting this structure to $n$-torsion produces the finite pairing that identifies the Cartier dual.

We now prove exactly the part of abelian duality needed here. For an $S$-scheme $T$, let $\operatorname{Pic}^0_{A/S}(T)$ be the group of line bundles on $A_T$, rigidified along the zero section, whose restriction to every geometric fiber is algebraically equivalent to zero. Rigidification removes the ambiguity of tensoring by a line bundle from $T$: an isomorphism between two rigidified bundles, if it exists, is unique because every function on a proper geometrically connected fiber is constant.

The first required fact is representability. We recall its construction rather than treating it as an unnamed input. Work locally on $S$ and choose a symmetric relatively very ample bundle $L$. We first need the cube lemma. For any rigidified line bundle $N$ on $A$, the alternating tensor product of its pullbacks along the three-variable sum, the three two-variable sums, and the three projections is canonically trivial on $A^3$. On each coordinate plane cancellation gives a rigidified trivialization. The scheme of extensions of such a trivialization is affine, while every function on a proper geometrically connected fiber of $A$ is constant; applying this rigidity successively in the three variables extends the trivializations uniquely and makes them agree. Restricting one variable gives the theorem of the square.

We shall also use its translation criterion. On a geometric fiber, a rigidified line bundle $N$ is algebraically equivalent to zero if and only if $t_a^*N\otimes N^{-1}$ is trivial for every point $a$ after every field extension. The forward implication follows by applying the square identity to a connected family joining $N$ to the identity. Conversely, in the divisor-pair chart constructed below, the displayed trivializations identify all translates of the point defined by $N$; the unique rigidified local slices therefore place that point in the connected identity slice. This criterion is stable under extension of the ground field.

Now embed $A$ in a projective space by a power of $L$. For each Hilbert polynomial $P$, choose $d$ beyond the uniform regularity bound. Degree-$d$ equations in the homogeneous coordinate ring then describe a quotient of fixed rank; the condition that multiplication by every homogeneous coordinate preserves the quotient is closed, and regularity recovers the entire saturated ideal from this degree. Thus a closed subscheme of a Grassmannian represents flat closed subschemes of $A$ with polynomial $P$. On the open locus of relative effective Cartier divisors, the universal ideal is invertible and gives a universal line bundle.

Every fiberwise algebraically trivial bundle $M$ is, locally on its parameter scheme, a difference

$$
M\simeq\mathcal O(D_1-D_2) \tag{14.0a}
$$

of two such relative divisors with the same Hilbert polynomial: after tensoring by a sufficiently high power of $L$, relative Serre vanishing makes both $M\otimes L^r$ and $L^r$ generated by sections with vanishing higher direct images, and a section avoiding the associated points gives the required Cartier divisor. The rank and multiplication conditions just used are determinantal, so the construction works uniformly on each quasi-compact parameter chart and commutes with base change. Pairs $(D_1,D_2)$ therefore give a smooth cover of the desired functor.

Two pairs give the same rigidified bundle precisely when the quotient of their universal invertible sheaves is pulled back from the parameter and its rigidification is $1$. The isomorphism scheme between the two rigidified bundles is then either empty or a single section; hence this equivalence relation is closed, separated, and effective on the Grassmannian charts. Gluing the resulting quotients gives a separated group scheme locally of finite presentation representing $\operatorname{Pic}^0_{A/S}$. Tensor product, inversion, and pullback commute with the equivalence relation and give its group law.

It remains to identify the representing group geometrically. The theorem of the square makes

$$
\phi_L:A\longrightarrow\operatorname{Pic}^0_{A/S},\qquad
x\longmapsto t_x^*L\otimes L^{-1} \tag{14.0b}
$$

a homomorphism. On every geometric fiber its kernel is finite: a positive-dimensional stabilizer would make the ample class of $L$ trivial along a positive-dimensional orbit. Intersecting $g$ general translates of a divisor in a high power of $L$ computes a positive finite kernel length and shows that the image has dimension $g$. The local slices in the divisor construction show that every algebraically trivial class lies in this image after a finite extension of the geometric ground field. Hence $\phi_L$ is surjective on every geometric fiber. Because $A$ is proper and the Picard space is separated, $\phi_L$ is proper; its finite fibers make it finite. Its kernel length is locally constant by the same intersection calculation, so the fiberwise flatness criterion makes $\phi_L$ finite locally free and faithfully flat. Properness and smoothness descend from $A$ along this cover. Thus the representing group is an abelian scheme $A^\vee/S$ of relative dimension $g$. The construction commutes with arbitrary base change, since the Grassmannian equations, divisor opens, rigidifications, intersection calculation, and quotient torsors all do.

There is consequently a universal rigidified line bundle

$$
\mathcal P\quad\text{on}\quad A\times_SA^\vee,
$$

the **Poincaré bundle**. Its restriction to $A\times\{y\}$ is the line bundle represented by $y$, and its restrictions along either zero section are trivialized.

The universal property supplies $\mathcal P$, and applying the theorem of the cube to it gives canonical isomorphisms

$$
(m_A\times1)^*\mathcal P
\simeq p_{13}^*\mathcal P\otimes p_{23}^*\mathcal P,
\qquad
(1\times m_{A^\vee})^*\mathcal P
\simeq p_{12}^*\mathcal P\otimes p_{13}^*\mathcal P.
$$

The rigidifications make these isomorphisms unique and force their associativity compatibilities. This is the biextension law.

Pullback of line bundles defines, for every homomorphism $f:A\to B$, a contravariant homomorphism

$$
f^\vee:B^\vee\longrightarrow A^\vee.
$$

The universal bundle also defines a biduality morphism $\delta_A:A\to A^{\vee\vee}$. To prove it is an isomorphism, one may work on geometric fibers. Over an algebraically closed field choose an ample $L$. The theorem of the cube gives

$$
\phi_L^\vee\circ\delta_A=\phi_L.
$$

Both $\phi_L$ and $\phi_L^\vee$ are isogenies. If $c_1(L)$ has alternating Riemann form matrix $E_L$ on a prime-to-characteristic torsion level, the two maps have transpose matrices $E_L$ and $E_L^{\mathsf t}$; hence their degrees are equal. The equality is integral and remains valid in every characteristic because both degrees are the top-intersection number

$$
\frac{c_1(L)^g}{g!}
$$

squared, a formula obtained by pulling back $c_1(L)^g$ along the finite map $\phi_L$. Multiplicativity of degree in $\phi_L^\vee\delta_A=\phi_L$ forces $\deg\delta_A=1$, so $\delta_A$ is an isomorphism on every geometric fiber. The fiberwise isomorphism criterion for a proper finitely presented morphism then shows that $\delta_A$ is an isomorphism over $S$. Finally, pullback by $[n]_A$ sends a line bundle represented by $y$ to the one represented by $ny$, so

$$
([n]_A)^\vee=[n]_{A^\vee}.
$$

These facts prove the abelian-duality input used below; no later theory of abelian varieties is being invoked, and no duality for the positive-dimensional schemes is being conflated with Cartier duality. Cartier duality enters only after restricting to finite isogeny kernels.

### 14.2 Construction of the group-scheme Weil pairing

Let $x\in A[n](T)$ and $y\in A^\vee[n](T)$. The point $y$ represents a rigidified algebraically trivial line bundle $L_y$ on $A_T$, obtained from the Poincaré bundle. The equality $ny=0$ says that $L_y^{\otimes n}$ is trivial in the relative Picard group, but it does not by itself choose a trivialization. Locally one may choose the translation and tensor trivializations needed to compare $L_y$ along the $n$-torsion point $x$. The biextension commutator is independent of those choices and descends to a unit whose $n$th power is $1$.

Concretely, the biextension laws give two ways to trivialize the $n$th tensor power of the fiber $\mathcal P_{x,y}$: add $x$ to itself $n$ times and use $nx=0$, or add $y$ to itself $n$ times and use $ny=0$. Their ratio is a unit. Associativity of the two biextension laws shows that changing either local trivialization multiplies numerator and denominator by the same unit, so the ratio descends. Repeating either addition once more shows that its $n$th power is $1$. Interchanging the order of the two additions in three variables proves multiplicativity in each argument.

Carrying this construction out universally gives the **Weil pairing**

$$
e_n:A[n]\times_SA^\vee[n]\longrightarrow\mu_n. \tag{14.1}
$$

The biextension law makes it bilinear. It is compatible with arbitrary base change because the dual abelian scheme, Poincaré bundle, multiplication kernels, and rigidifications all base-change. It is also functorial: for a homomorphism $f:A\to B$ with dual $f^\vee:B^\vee\to A^\vee$,

$$
e_n^B(fx,y)=e_n^A(x,f^\vee y). \tag{14.2}
$$

This identity follows directly by pulling the Poincaré bundle on $B\times B^\vee$ back along $f\times1$ and using its universal property. It is the scheme-theoretic adjointness relation for the pairing.

### 14.3 Perfectness in all characteristics

**Theorem 14.1 (perfect Weil pairing).** For every abelian scheme $A/S$ and every $n\ge1$, the pairing (14.1) is perfect. Equivalently,

$$
A[n]^D\xrightarrow{\sim}A^\vee[n]. \tag{14.3}
$$

**Proof strategy.** The Poincaré bundle realizes $A^\vee$ as the dual of $A$ and identifies the dual of an isogeny kernel with the kernel of the dual isogeny. Apply this to $[n]_A$, whose dual is $[n]_{A^\vee}$. The construction of the kernel pairing is exactly (14.1).

More explicitly, the dual-isogeny identification (10.7) gives

$$
(\ker[n]_A)^D\simeq\ker([n]_A^\vee).
$$

The dual of multiplication by $n$ is multiplication by $n$ on $A^\vee$, so the right side is $A^\vee[n]$. Under this isomorphism, evaluation is the biextension comparison defining $e_n$. Hence the associated map is (14.3) and is an isomorphism. $\square$

No invertibility hypothesis on $n$ appears. If a residue characteristic divides $n$, perfectness is schematic. The induced pairing on geometric point groups may be degenerate or tiny because $A[n]$ and $\mu_n$ can be nonreduced. The theorem asserts an isomorphism of finite locally free group schemes, which is the correct stronger statement.

### 14.4 Polarizations and self-duality

A **polarization** is a homomorphism $\lambda:A\to A^\vee$ which, on every geometric fiber, is induced by an ample line bundle. It is an isogeny and is symmetric under abelian biduality. Such a polarization turns (14.1) into a pairing on $A[n]$:

$$
e_n^\lambda(x,y)=e_n(x,\lambda(y)). \tag{14.4}
$$

Write

$$
\beta_n:A^\vee[n]\xrightarrow{\sim}A[n]^D,\qquad
\beta_n(z)(x)=e_n(x,z). \tag{14.4a}
$$

Symmetry of $\lambda$ and antisymmetry of the Poincaré commutator give

$$
e_n(x,\lambda y)=e_n(y,\lambda x)^{-1}. \tag{14.4b}
$$

Therefore the adjoint $A[n]\to A[n]^D$ of (14.4) is

$$
[-1]\circ\beta_n\circ\lambda[n], \tag{14.4c}
$$

not the unsigned composite. The sign does not affect perfectness, so (14.4) is perfect exactly when $\lambda[n]$ is an isomorphism; in particular it is perfect for a principal polarization. Alternation is stronger than (14.4b) when $n$ is even. The normalized cubical structure of an ample bundle canonically trivializes the commutator on the diagonal, and hence gives, for every $n$ including $n=2$,

$$
e_n^\lambda(x,x)=1. \tag{14.5}
$$

Thus a principally polarized abelian scheme has a canonical alternating self-duality of its $n$-torsion, dependent on the chosen principal polarization and carrying the sign in (14.4c). A general abelian scheme has the canonical duality (14.3) with the torsion of $A^\vee$, not a canonical self-duality with itself.

If $e_n^\lambda$ is perfect—for example, if $\lambda$ is principal—and $K\subset A[n]$ is finite locally free, its orthogonal has rank

$$
|K^\perp|=\frac{n^{2g}}{|K|}. \tag{14.6}
$$

For a Lagrangian subgroup the rank is $n^g$. Without perfectness, the radical contributes to the orthogonal and this quotient formula need not hold. These are scheme-theoretic ranks and, under the stated perfectness hypothesis, remain valid in characteristic dividing $n$.

### 14.5 Elliptic curves

An elliptic scheme $E/S$ carries the canonical principal polarization determined by the zero section,

$$
E\xrightarrow{\sim}E^\vee.
$$

Consequently the Weil pairing is a perfect alternating group-scheme pairing

$$
e_n:E[n]\times E[n]\longrightarrow\mu_n, \tag{14.7}
$$

and it induces

$$
E[n]^D\simeq E[n]. \tag{14.8}
$$

When $n$ is prime to the characteristic of a field, taking geometric points gives the classical alternating pairing on a free rank-two torsion module. A symplectic basis identifies its matrix with

$$
\begin{pmatrix}0&1\\-1&0\end{pmatrix},
$$

and Galois equivariance forces the determinant to be cyclotomic. When the characteristic divides $n$, (14.7) remains perfect even though no basis of $n^2$ geometric points exists. This is exactly the extension that pointwise character theory could not provide.

### 14.6 Isogenies and orthogonal kernels

Let $\varphi:E\to E'$ be an isogeny and $\widehat\varphi:E'\to E$ its dual. Formula (14.2) becomes

$$
e_n^{E'}(\varphi P,Q')=e_n^E(P,\widehat\varphi Q'). \tag{14.9}
$$

At the level of isogeny kernels, the canonical perfect pairing gives

$$
(\ker\varphi)^D\simeq\ker\widehat\varphi. \tag{14.10}
$$

If $C\subset E[n]$ is finite flat of rank $n$ and the Weil pairing restricts trivially to $C\times C$, then $C$ is isotropic. Its orthogonal also has rank $n$, so $C=C^\perp$. In the prime-to-characteristic case a cyclic subgroup is locally generated by one element and alternation gives the required triviality. At the residue characteristic, “cyclic” has several inequivalent meanings, so isotropy should be stated or proved scheme-theoretically rather than inferred from a nonexistent geometric generator. The quotient $E/C$ and the dual isogeny then encode the reversed quotient character group.

### 14.7 Compatibility through levels

For positive integers $m,n$, $P\in A[mn]$, and $Q\in A^\vee[mn]$, the Weil pairings satisfy the level compatibility

$$
e_{mn}(P,Q)^m=e_n(mP,mQ). \tag{14.11}
$$

On prime-to-characteristic geometric points this follows at once from bilinearity on compatible torsion bases. Scheme-theoretically it is an equality of morphisms obtained from the functoriality of the Poincaré biextension. For a prime $\ell$ invertible on the field, inverse limits yield

$$
T_\ell A\times T_\ell A^\vee\longrightarrow\mathbf Z_\ell(1), \tag{14.12}
$$

and for a principally polarized elliptic curve,

$$
T_\ell E\simeq(T_\ell E)^*(1). \tag{14.13}
$$

Equations (14.12)--(14.13) are module-theoretic inverse-limit shadows of the finite group-scheme duality (14.3). They should not be used backwards to prove residue-characteristic group-scheme perfectness; inverse limits of geometric points have already discarded connected infinitesimal torsion there.

### 14.8 Determinants of elliptic torsion

Let $E/K$ be an elliptic curve and suppose $n$ is prime to $\operatorname{char}K$. The perfect pairing on geometric points is Galois equivariant:

$$
e_n(\sigma P,\sigma Q)=\sigma(e_n(P,Q)). \tag{14.14}
$$

Choose a basis $P,Q$ of $E[n](K^s)$ with $e_n(P,Q)$ primitive. If $\rho_n(\sigma)$ is the matrix of $\sigma$ in this basis, alternation and bilinearity give

$$
e_n(\sigma P,\sigma Q)
=e_n(P,Q)^{\det\rho_n(\sigma)}. \tag{14.15}
$$

The right side of (14.14) is $e_n(P,Q)^{\chi_n(\sigma)}$. Primitivity therefore yields

$$
\det\rho_n=\chi_n. \tag{14.16}
$$

This conclusion is independent of the chosen symplectic basis. It is the rank-two instance of (13.12), now derived directly from the elliptic Weil pairing. At residue-characteristic level, the group-scheme pairing (14.7) remains the correct integral statement even when a two-element basis of geometric torsion does not exist.

## 15. Worked structural patterns

### 15.1 A cyclic homomorphism and its dual

Abstract variance becomes clearer in a calculation. Let $d,m\ge1$ and consider

$$
[d]:\mu_m\longrightarrow\mu_m,\qquad z\longmapsto z^d. \tag{15.1}
$$

Under $\mu_m^D=\underline{\mathbf Z/m\mathbf Z}$, its Cartier dual is multiplication by $d$ on the constant cyclic group. Indeed a character indexed by $a\in\mathbf Z/m\mathbf Z$ is $z\mapsto z^a$, and precomposition gives $z\mapsto z^{da}$.

Put $c=\gcd(d,m)$. The scheme-theoretic kernel is $\mu_c$, and the finite-flat image is isomorphic to $\mu_{m/c}$. Duality turns the kernel into the cokernel of multiplication by $d$ on $\mathbf Z/m\mathbf Z$, and the image into the annihilator of that kernel. Concretely,

$$
\ker[d]_{\underline{\mathbf Z/m\mathbf Z}}
\simeq\underline{\mathbf Z/c\mathbf Z},
$$

while the quotient by the image also has order $c$. These statements remain valid when the residue characteristic divides $m$; only the multiplicative side becomes nonreduced.

The example illustrates three levels that happen to agree here. The abstract group computation determines the constant side, the diagonalizable construction determines the multiplicative side, and Cartier exactness proves that the scheme-theoretic kernel and quotient have the expected rank over every base.

### 15.2 A split hyperbolic group

Let

$$
G=\underline M\times D(M).
$$

Using evaluation in each direction, define

$$
b\bigl((m,\chi),(m',\chi')\bigr)
=\chi'(m)\chi(m')^{-1}. \tag{15.2}
$$

This is a perfect alternating pairing. Perfectness follows because its associated map sends the constant factor to the dual of the diagonalizable factor and vice versa, with an inverse on one factor. Alternation follows immediately:

$$
b((m,\chi),(m,\chi))=1.
$$

Both factors are Lagrangian: each pairs trivially with itself, and each has rank $|M|$ inside a group of rank $|M|^2$. Thus

$$
\underline M^\perp=\underline M,\qquad D(M)^\perp=D(M) \tag{15.3}
$$

when they are viewed as the two coordinate factors of this hyperbolic pairing.

Over a field of characteristic dividing $|M|$, the two Lagrangians can have radically different geometry. For $M=\mathbf Z/p\mathbf Z$, one is étale and the other is connected multiplicative. A perfect alternating group scheme can therefore possess Lagrangians whose point sets have different sizes. Rank and exactness, not a symplectic basis of geometric points, control the calculation.

### 15.3 The additive perfect pairing on test algebras

Let $k$ have characteristic $p$ and use the standard self-duality of $\alpha_p$. On a $k$-algebra $C$, take $x,y\in C$ with $x^p=y^p=0$. The value

$$
\langle x,y\rangle=\sum_{i=0}^{p-1}\frac{(xy)^i}{i!} \tag{15.4}
$$

is a unit with inverse obtained by replacing $x$ with $-x$. In the universal coordinate ring, the truncated exponential identity gives

$$
\langle x_1+x_2,y\rangle
=\langle x_1,y\rangle\langle x_2,y\rangle,
$$

and similarly in $y$. Terms whose total exponent reaches $p$ vanish because of the relevant $p$th-power relation; below $p$, the usual factorial identity is valid. Hence (15.4) is bilinear.

If $C$ is a field, then $x=y=0$ and the pairing has only the value $1$. Nevertheless it is perfect as a group-scheme pairing. Taking $C=k[u,v]/(u^p,v^p)$ reveals the universal nontrivial value

$$
1+uv+\frac{u^2v^2}{2!}+\cdots+\frac{u^{p-1}v^{p-1}}{(p-1)!}.
$$

This is a worked counterexample to the assertion that perfectness can be checked from algebraically closed field-valued points for arbitrary finite group schemes.

### 15.4 Dualizing a connected exact sequence

In characteristic $p$, consider the Frobenius sequence from Book 46,

$$
0\to\alpha_p\to\alpha_{p^r}\xrightarrow{F}\alpha_{p^{r-1}}\to0,
\qquad r\ge2. \tag{15.5}
$$

Cartier duality yields

$$
0\to\alpha_{p^{r-1}}^D\longrightarrow
\alpha_{p^r}^D\longrightarrow\alpha_p\to0. \tag{15.6}
$$

For $r=1$, the endpoint is self-dual. For $r>1$, the coordinate algebra of $\alpha_{p^r}^D$ is the finite divided-power Hopf algebra dual to $k[t]/(t^{p^r})$; it should not be replaced without proof by another truncated polynomial algebra. Sequence (15.6) gives useful structural information without forcing a false elementary identification.

Every geometric point in (15.5) and (15.6) is the identity over an algebraically closed field, yet both sequences are nontrivial and faithfully flat exact. Their ranks multiply as $p^r=p\cdot p^{r-1}$, and exactness reverses them exactly as it does for ordinary finite groups. This example isolates the advantage of Hopf-algebra duality: it retains extension structure after pointwise group theory has become completely silent.

### 15.5 Two mixed-characteristic models

Let $R$ be a mixed-characteristic DVR with residue characteristic $p$, and suppose $K$ contains a primitive $p$th root of unity. The generic fibers

$$
(\mu_p)_K,\qquad
(\underline{\mathbf Z/p\mathbf Z})_K
$$

are isomorphic after choosing such a root. Their special fibers are not: the first is connected and the second is étale. Cartier duality exchanges the two integral models.

This produces a useful four-step cycle:

$$
\begin{array}{ccc}
\underline{\mathbf Z/p\mathbf Z}_R&\xleftrightarrow{\ D\ }&\mu_{p,R}\\
\downarrow&&\downarrow\\
\underline{\mathbf Z/p\mathbf Z}_K&\xleftrightarrow{\ D\ }&\mu_{p,K}.
\end{array} \tag{15.7}
$$

The bottom objects may be identified noncanonically, but the top objects cannot. Thus a generic self-duality of a Galois module need not extend as a self-duality of a chosen finite-flat model. It may instead identify that model with the generic fiber of a different, dual model. This is precisely the sort of integral distinction needed when finite-flat conditions are imposed later.

### 15.6 A failure caused by dropping flatness

Book 46 exhibited morphisms of finite flat groups over a DVR whose scheme-theoretic kernel is finite but not flat. Suppose one attempted to dualize such a kernel as though it occurred in an admissible exact sequence. Its coordinate algebra contains base torsion, so its module dual can have the wrong rank after specialization and the tensor-dual isomorphism (2.1) no longer applies. There is then no reason for the spectrum of that module dual to represent characters or for the purported dual quotient to be faithfully flat.

The repair is not to weaken the meaning of duality. One must replace the raw kernel or image by a genuine finite-flat object when the geometry supplies one—over a DVR, often by saturation or a flat image factorization—and only then apply exactness. Cartier duality is powerful because its category is rigid; dropping the category's defining hypotheses destroys the mechanism that proves the theorem.

## 16. A reusable duality dictionary

### 16.1 Five duals and their domains

The word “dual” now has five precise meanings.

1. For a finite projective $R$-module $P$,

   $$
   P^\vee=\operatorname{Hom}_R(P,R)
   $$

   is the **module linear dual**. It reverses linear maps and is reflexive.

2. For a finite projective Hopf algebra $A$, the same module $A^\vee$ with transposed product, coproduct, unit, counit, and antipode is the **Hopf-algebra dual**.

3. For $G=\operatorname{Spec}A$, the group scheme

   $$
   G^D=\operatorname{Spec}A^\vee
   $$

   is the **Cartier dual**, representing characters into $\mathbf G_m$.

4. For a finite abelian group or an étale geometric-point module $M$, a **character group** is $\operatorname{Hom}(M,L^\times)$ or, with exponent $n$, $\operatorname{Hom}(M,\mu_n)$. It captures the Cartier dual only when geometric points retain the whole scheme.

5. For a finite $\Gamma_K$-module $M$ killed by $n$ with $n$ invertible in $K$,

   $$
   M^*(1)=\operatorname{Hom}(M,\mu_n(K^s))
   $$

   is the **Tate-twisted Galois dual**. Its twist is the Galois action on roots of unity.

The first construction makes the second possible; spectrum turns the second into the third; geometric points turn the third into the fourth only in the étale range; Galois descent turns the fourth into the fifth with its essential action.

### 16.2 The structural table

For finite locally free commutative group schemes, the following translations are safe over an arbitrary base unless an extra hypothesis is displayed:

$$
\begin{array}{c|c}
\text{object or operation}&\text{Cartier-dual form}\\
\hline
G=\operatorname{Spec}A&G^D=\operatorname{Spec}A^\vee\\
|G|&|G^D|=|G|\\
G_{S'}&(G_{S'})^D\simeq(G^D)_{S'}\\
G\times H&(G\times H)^D\simeq G^D\times H^D\\
f:G\to H&f^D:H^D\to G^D\\
G&G^{DD}\simeq G\\
\underline M&D(M)\\
D(M)&\underline M\\
\mu_n&\underline{\mathbf Z/n\mathbf Z}\\
\alpha_p\ (p=0\text{ on }S)&\alpha_p\\
G\text{ finite étale}&G^D\text{ multiplicative type}\\
G\text{ multiplicative type}&G^D\text{ finite étale}.
\end{array} \tag{16.1}
$$

Every line is compatible with arbitrary base change. The $\alpha_p$ line includes its characteristic hypothesis; without it the displayed primitive truncated polynomial is not the same group scheme construction.

### 16.3 The exactness table

If

$$
0\to H\to G\to Q\to0
$$

is faithfully flat exact with all terms finite locally free and commutative, then

$$
0\to Q^D\to G^D\to H^D\to0 \tag{16.2}
$$

is faithfully flat exact, and

$$
H^\perp=(G/H)^D,\qquad
(H^\perp)^\perp=H,\qquad
|H|\,|H^\perp|=|G|. \tag{16.3}
$$

For a perfect pairing $G\times H\to\mathbf G_m$ and a finite-flat subgroup $K\subset G$,

$$
K^\perp\simeq(G/K)^D,\qquad
|K^\perp|=|G|/|K|,\qquad
(K^\perp)^\perp=K. \tag{16.4}
$$

These formulas require actual finite-flat subgroups and represented faithfully flat quotients. For arbitrary morphisms whose kernels or images are nonflat, one must first establish an admissible exact factorization.

### 16.4 The arithmetic table

Over a DVR $R$ with fraction field $K$ and residue field $k$,

$$
(G^D)_K=(G_K)^D,\qquad (G^D)_k=(G_k)^D. \tag{16.5}
$$

If $H$ is the finite-flat closure in $G$ of $H_K\subset G_K$, then

$$
H^\perp=\overline{H_K^\perp}^{\,G^D}. \tag{16.6}
$$

If $n$ is invertible in $K$ and $G_K$ corresponds to the Galois module $M$, then $(G^D)_K$ corresponds to

$$
M^*(1)=\operatorname{Hom}(M,\mu_n(K^s)). \tag{16.7}
$$

For an abelian scheme $A/S$,

$$
A[n]^D\simeq A^\vee[n], \tag{16.8}
$$

and for an elliptic scheme,

$$
E[n]^D\simeq E[n] \tag{16.9}
$$

through the canonical principal polarization and perfect alternating Weil pairing.

### 16.5 A safe proof protocol

When a duality claim arises in later arithmetic work, the following order of questions prevents most errors.

First, is the object finite locally free and commutative? If not, the Cartier dual developed here does not automatically apply. Second, is a proposed subgroup finite flat, so that its quotient and dual exist in the exact category? Third, is a statement being made scheme-theoretically or only on geometric points? The latter is sufficient only after étaleness has been proved. Fourth, if Galois modules are used, where does $\mu_n$ carry its action, and has the Tate twist been retained? Fifth, if generic closure is involved, is the base a DVR or Dedekind scheme, or has flatness been proved by another method?

Once these checks pass, the efficient route is usually to turn a pairing into a map to a Cartier dual, prove that map is an isomorphism, and then obtain annihilators and rank formulas from exactness. This replaces repeated pointwise calculations by one structural argument without hiding any hypothesis.

### 16.6 Conclusion

Cartier duality turns the character idea into geometry. A finite flat group cannot be dualized by looking at its visible points, because specialization may compress all of those points into a nonreduced identity while preserving the full order. Its finite projective Hopf algebra retains what was compressed. Transposing that Hopf algebra exchanges multiplication with comultiplication, unit with counit, and subgroups with quotients; taking its spectrum produces the representing scheme of characters into $\mathbf G_m$.

The evaluation pairing is the center of the theory. It recovers every group from its double dual, converts bilinear pairings into ordinary morphisms, and makes perfectness a schematic isomorphism rather than a point-counting condition. Constant and diagonalizable groups exchange, $\mu_n$ remains dual to the constant cyclic group even in characteristic dividing $n$, and the explicit self-duality of $\alpha_p$ demonstrates that infinitesimal additive characters are fully present. Exactness yields annihilators, double orthogonals, and rank identities with the same reliability as finite-dimensional linear algebra, provided finite local freeness and faithful-flat quotient hypotheses are kept visible.

Over a DVR, and similarly over a Dedekind base after working locally, the construction commutes with both generic and special fibers and carries the closure of a generic subgroup to the closure of its generic annihilator inside the fixed dual model. On an étale generic fiber it becomes the Tate-twisted Galois dual because evaluation takes values in roots of unity. On torsion of abelian schemes it becomes the perfect Weil pairing and the canonical identification $A[n]^D\simeq A^\vee[n]$; for elliptic curves the principal polarization supplies the familiar alternating self-duality.

The resulting dictionary is deliberately finite and geometric. It prepares finite-flat Galois representations by identifying the correct dual model, and it prepares later local and global duality by supplying the annihilator formalism from which orthogonal conditions will grow. The cohomological pairings to come will not replace Cartier evaluation; they will build on it.
