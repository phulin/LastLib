# Tate Local Duality

## Contents

1. [Why a local obstruction has a dual](#1-why-a-local-obstruction-has-a-dual)
   - [From dimensions to canonical partners](#11-from-dimensions-to-canonical-partners)
   - [Standing field hypotheses](#12-standing-field-hypotheses)
   - [The three degrees and their later jobs](#13-the-three-degrees-and-their-later-jobs)
2. [The coefficient dual and the unavoidable twist](#2-the-coefficient-dual-and-the-unavoidable-twist)
   - [What ordinary duality fails to remember](#21-what-ordinary-duality-fails-to-remember)
   - [Evaluation and biduality](#22-evaluation-and-biduality)
   - [Exactness and variance](#23-exactness-and-variance)
   - [Coefficient rings](#24-coefficient-rings)
   - [Cartier duality and finite étale coefficients](#25-cartier-duality-and-finite-étale-coefficients)
   - [A twist calculus](#26-a-twist-calculus)
3. [Products, boundaries, and signs](#3-products-boundaries-and-signs)
   - [Why cochain-level control matters](#31-why-cochain-level-control-matters)
   - [Graded interchange](#32-graded-interchange)
   - [Compatibility with connecting maps](#33-compatibility-with-connecting-maps)
   - [Restriction, corestriction, and projection](#34-restriction-corestriction-and-projection)
   - [Bocksteins and the sign ledger](#35-bocksteins-and-the-sign-ledger)
4. [The Brauer coordinate](#4-the-brauer-coordinate)
   - [Why degree two needs a number](#41-why-degree-two-needs-a-number)
   - [Finite-level invariants](#42-finite-level-invariants)
   - [Behavior under extension](#43-behavior-under-extension)
   - [Relative fundamental classes](#44-relative-fundamental-classes)
5. [Construction of the local Tate pairing](#5-construction-of-the-local-tate-pairing)
   - [The only possible construction](#51-the-only-possible-construction)
   - [What perfectness means](#52-what-perfectness-means)
   - [Immediate formal symmetries](#53-immediate-formal-symmetries)
6. [The cyclic and Kummer calculation](#6-the-cyclic-and-kummer-calculation)
   - [Why the first detector is reciprocity](#61-why-the-first-detector-is-reciprocity)
   - [Perfectness in the middle cyclic case](#62-perfectness-in-the-middle-cyclic-case)
   - [The endpoint cyclic calculation](#63-the-endpoint-cyclic-calculation)
   - [Continuous Hilbert 90](#64-continuous-hilbert-90)
7. [The descent engine behind perfectness](#7-the-descent-engine-behind-perfectness)
   - [Why cyclic groups do not suffice by themselves](#71-why-cyclic-groups-do-not-suffice-by-themselves)
   - [The local class formation](#72-the-local-class-formation)
   - [The Tate Nakayama comparison](#73-the-tate-nakayama-comparison)
   - [Proof from the class-formation axioms](#74-proof-from-the-class-formation-axioms)
   - [From lattices to arbitrary finite modules](#75-from-lattices-to-arbitrary-finite-modules)
   - [Passage to the absolute Galois group](#76-passage-to-the-absolute-galois-group)
   - [The exact-sequence audit](#77-the-exact-sequence-audit)
   - [The finite-module Tate--Nakayama form](#78-the-finite-module-tate--nakayama-form)
8. [Proof and exact forms of Tate local duality](#8-proof-and-exact-forms-of-tate-local-duality)
   - [Finiteness before duality](#81-finiteness-before-duality)
   - [Nondegeneracy in both variables](#82-nondegeneracy-in-both-variables)
   - [Degree zero and degree two](#83-degree-zero-and-degree-two)
   - [The middle-degree theorem](#84-the-middle-degree-theorem)
   - [Exact-sequence devissage as a reusable corollary](#85-exact-sequence-devissage-as-a-reusable-corollary)
   - [Euler--Poincaré formulas in dual form](#86-euler--poincaré-formulas-in-dual-form)
9. [Functoriality in fields and modules](#9-functoriality-in-fields-and-modules)
   - [Restriction and corestriction are adjoint](#91-restriction-and-corestriction-are-adjoint)
   - [Kernels and images under extension](#92-kernels-and-images-under-extension)
   - [Adjoint coefficient maps and Shapiro](#93-adjoint-coefficient-maps-and-shapiro)
10. [Exact annihilators of local conditions](#10-exact-annihilators-of-local-conditions)
    - [Orthogonals as exact data](#101-orthogonals-as-exact-data)
    - [The unramified condition away from $p$](#102-the-unramified-condition-away-from-p)
    - [Failure of unramified self-complementarity at $p$](#103-failure-of-unramified-self-complementarity-at-p)
    - [Image, quotient, and norm conditions](#104-image-quotient-and-norm-conditions)
    - [Finite and singular local quotients](#105-finite-and-singular-local-quotients)
    - [Residual conditions and saturation](#106-residual-conditions-and-saturation)
11. [Kummer classes and Hilbert symbols](#11-kummer-classes-and-hilbert-symbols)
    - [From cup products to symbols](#111-from-cup-products-to-symbols)
    - [Cyclic algebras and norms](#112-cyclic-algebras-and-norms)
    - [Units and the unramified direction](#113-units-and-the-unramified-direction)
    - [A tame computation and an even-order warning](#114-a-tame-computation-and-an-even-order-warning)
    - [Principal-unit depth](#115-principal-unit-depth)
12. [Finite levels, torsion modules, and lattices](#12-finite-levels-torsion-modules-and-lattices)
    - [Why algebraic duality is no longer enough](#121-why-algebraic-duality-is-no-longer-enough)
    - [Passing the finite pairing to the limit](#122-passing-the-finite-pairing-to-the-limit)
    - [Starting with a discrete torsion module](#123-starting-with-a-discrete-torsion-module)
    - [Coefficients in a finite extension of $\mathbf Q_\ell$](#124-coefficients-in-a-finite-extension-of-mathbf-q_ell)
    - [Vector-space duality](#125-vector-space-duality)
    - [What breaks in equal characteristic $p$](#126-what-breaks-in-equal-characteristic-p)
    - [Exact triples and integral orthogonals](#127-exact-triples-and-integral-orthogonals)
    - [Unramified conditions for lattices](#128-unramified-conditions-for-lattices)
13. [Dimension formulas and deformation-theoretic consequences](#13-dimension-formulas-and-deformation-theoretic-consequences)
    - [Removing the mysterious $H^2$](#131-removing-the-mysterious-h2)
    - [Self-dual modules and parity](#132-self-dual-modules-and-parity)
    - [Adjoint representations](#133-adjoint-representations)
    - [Tangent spaces and their dual conditions](#134-tangent-spaces-and-their-dual-conditions)
    - [Framed dimensions](#135-framed-dimensions)
    - [The local correction term used in Selmer theory](#136-the-local-correction-term-used-in-selmer-theory)
    - [Changing coefficient rings](#137-changing-coefficient-rings)
14. [Five families of examples](#14-five-families-of-examples)
    - [Trivial and cyclotomic lines away from $p$](#141-trivial-and-cyclotomic-lines-away-from-p)
    - [An unramified character](#142-an-unramified-character)
    - [A concrete quadratic Hilbert pairing](#143-a-concrete-quadratic-hilbert-pairing)
    - [Elliptic-curve torsion](#144-elliptic-curve-torsion)
    - [Mixed-characteristic cyclotomic coefficients](#145-mixed-characteristic-cyclotomic-coefficients)
15. [The local-duality dictionary](#15-the-local-duality-dictionary)
    - [A calculation protocol](#151-a-calculation-protocol)
    - [Formula table](#152-formula-table)
    - [Normalization ledger for Selmer structures](#153-normalization-ledger-for-selmer-structures)
    - [Counterexamples that fix the hypotheses](#154-counterexamples-that-fix-the-hypotheses)
    - [Boundaries of the dictionary](#155-boundaries-of-the-dictionary)
16. [Conclusion](#16-conclusion)
    - [Detection rather than numerical coincidence](#161-detection-rather-than-numerical-coincidence)
    - [The reusable local endpoint](#162-the-reusable-local-endpoint)

## 1. Why a local obstruction has a dual

### 1.1 From dimensions to canonical partners

Book 30 showed that the cohomology of a finite Galois module over a nonarchimedean local field is concentrated in degrees $0,1,2$, subject to one important equal-characteristic exception. It also computed Euler characteristics. Those results tell us how large the groups are, but not why a class in one group should be detected by a class in another. That missing detection theorem is the subject of this book.

The guiding observation is elementary. If $M$ is finite, a point of its dual evaluates on a point of $M$. If both points vary as Galois cohomology classes, cup product raises their degrees. The local field supplies one canonical coordinate on degree two, the Brauer invariant. The sum of complementary degrees must therefore be two, and the dual coefficient must contain one Tate twist:

$$
H^r(K,M)\times H^{2-r}(K,M^*(1))
\longrightarrow \mathbf Q/\mathbf Z.
$$

The theorem will say that this pairing loses no information in either variable. This is stronger than equality of orders. A cardinality calculation can show that an already injective map between finite groups is bijective; it cannot produce the injection. We shall construct detectors first and count only at the final step of an exact-sequence argument.

The result has a second role. A local deformation condition is usually a subgroup or subspace of $H^1(K,M)$. Duality assigns to it an exact orthogonal condition in $H^1(K,M^*(1))$. Books 32 and 33 will assemble such local conditions globally. We stop before that assembly: every statement here concerns one local field.

### 1.2 Standing field hypotheses

Let $K$ be a nonarchimedean local field, with normalized valuation $v_K$, ring of integers $\mathcal O_K$, maximal ideal $\mathfrak m_K$, residue field $k=\mathbf F_q$, and residue characteristic $p$. Fix a separable closure $K^s$ and write

$$
G_K=\operatorname{Gal}(K^s/K).
$$

Arithmetic Frobenius is $x\mapsto x^q$ on $\overline{k}$. The reciprocity convention is

$$
\operatorname{rec}_K(\pi_K)|_{K^{\mathrm{nr}}}=\operatorname{Frob}_K
$$

for every uniformizer $\pi_K$. Thus geometric Frobenius is the inverse of the element used here.

The finite-level duality theorem applies to a finite discrete continuous $G_K$-module $M$ killed by an integer $n$ satisfying

$$
\gcd(n,\operatorname{char}K)=1. \tag{1.1}
$$

In mixed characteristic, $\operatorname{char}K=0$, so this permits $p$-primary modules. In equal characteristic $p$, it excludes $p$-primary modules. This is exactly the range in which $\mu_n(K^s)$ is a finite étale Galois module of order $n$, Kummer theory has its usual form, the relevant cohomology groups are finite, and $G_K$ has cohomological dimension two at primes dividing $n$.

The exclusion in equal characteristic is structural. There $\mu_{p^a}(K^s)=1$, Artin--Schreier classes can make $H^1(K,\mathbf Z/p\mathbf Z)$ infinite, and no twisted finite Galois module built from $p^a$th roots of unity can play the role required below. Flat duality for finite group schemes is a different theorem; it is not disguised by our notation.

### 1.3 The three degrees and their later jobs

Each degree has a distinct meaning.

* $H^0(K,M)=M^{G_K}$ records genuine symmetries. Its dual partner in degree two turns obstructions into invariant functionals.
* $H^1(K,M)$ records torsors and extension classes. Its pairing with another $H^1$ identifies the exact orthogonal of any local tangent condition.
* $H^2(K,M)$ records the last local obstruction. Its dual partner is the fixed submodule of the Tate dual.

There are no further degrees in the range (1.1). Consequently local duality is not an infinite ladder: it is a reflection about degree one.

For a finite group $A$, write

$$
A^D=\operatorname{Hom}(A,\mathbf Q/\mathbf Z)
$$

for its Pontryagin dual. Since $A$ is finite, both groups carry the discrete topology and $A\to A^{DD}$ is an isomorphism. Later, compact and infinite discrete groups will force us to retain the topology explicitly.

## 2. The coefficient dual and the unavoidable twist

### 2.1 What ordinary duality fails to remember

The abstract character group $\operatorname{Hom}(M,\mathbf Q/\mathbf Z)$ reverses the Galois action, but evaluation into $\mathbf Q/\mathbf Z$ has trivial Galois action. Cup product with it would land in $H^2(K,\mathbf Q/\mathbf Z)$, which is not the canonical finite-level Brauer target. The local degree-two coordinate comes instead from roots of unity. The dual must therefore be adjusted so that evaluation lands in $\mu_n$.

Choose an integer $n$ annihilating $M$ and satisfying (1.1). Define

$$
M^*=\operatorname{Hom}_{\mathbf Z/n\mathbf Z}(M,\mathbf Z/n\mathbf Z),
$$

with contragredient action

$$
(g f)(m)=f(g^{-1}m).
$$

The **Tate dual** is

$$
M^*(1)=\operatorname{Hom}(M,\mu_n), \tag{2.1}
$$

where the action is

$$
(g\lambda)(m)=g\bigl(\lambda(g^{-1}m)\bigr).
$$

If $M$ is killed by a proper divisor of $n$, definition (2.1) is independent of the chosen common exponent in the evident canonical sense. Equivalently one may write $M^D(1)$ primary component by primary component.

### 2.2 Evaluation and biduality

The reason for (2.1) is the $G_K$-equivariant evaluation pairing

$$
e_M:M\times M^*(1)\longrightarrow\mu_n,
\qquad e_M(m,\lambda)=\lambda(m). \tag{2.2}
$$

Indeed,

$$
e_M(gm,g\lambda)=g\lambda(m)=g e_M(m,\lambda).
$$

The action on the value is essential. Suppressing it is precisely the error that loses the Tate twist.

Evaluation is perfect on the coefficient groups. Every finite abelian group killed by $n$ is a direct sum of cyclic groups, and $\operatorname{Hom}(\mathbf Z/d\mathbf Z,\mu_n)$ has order $d$ when $d\mid n$. Hence

$$
M\xrightarrow{\sim}\operatorname{Hom}(M^*(1),\mu_n),
\qquad m\longmapsto(\lambda\mapsto\lambda(m)). \tag{2.3}
$$

The twist cancels on taking the Tate dual twice, so (2.3) is Galois equivariant. This coefficient biduality will be mirrored by cohomological biduality.

### 2.3 Exactness and variance

If

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0 \tag{2.4}
$$

is exact, applying $\operatorname{Hom}(-,\mu_n)$ gives

$$
0\longrightarrow M''^*(1)\longrightarrow M^*(1)
\longrightarrow M'^*(1)\longrightarrow0. \tag{2.5}
$$

Surjectivity on the right holds because $\mu_n$, abstractly isomorphic to $\frac1n\mathbf Z/\mathbf Z$, is injective among groups killed by $n$. Thus Tate duality is exact and contravariant.

For a homomorphism $f:M\to N$, let

$$
f^*(1):N^*(1)\longrightarrow M^*(1),
\qquad \lambda\longmapsto\lambda\circ f.
$$

Evaluation then gives

$$
e_N(fm,\lambda)=e_M(m,f^*(1)\lambda). \tag{2.6}
$$

Equation (2.6) will become adjointness on cohomology. It is the formal source of the reversal that later sends a local condition on $M$ to one on $M^*(1)$.

### 2.4 Coefficient rings

Suppose $R$ is a finite commutative local ring of residue characteristic $\ell$, killed by $n$, and $M$ is finite free over $R$. If a chosen character identifies a rank-one $R$-module $R(1)$ with the relevant roots-of-unity coefficient, one may write

$$
M_R^*(1)=\operatorname{Hom}_R(M,R)(1).
$$

The canonical theorem, however, is the underlying finite-abelian-group theorem with target $\mathbf Q/\mathbf Z$. An $R$-valued perfect pairing requires an additional choice of a generator for the dualizing rank-one $R$-module. Keeping the invariant $\mathbf Q/\mathbf Z$-valued avoids a false canonical identification.

### 2.5 Cartier duality and finite étale coefficients

The notation $M^*(1)$ has a geometric origin. It is not an artificial correction inserted after ordinary duality fails. If $G$ is a finite commutative group scheme over $K$, its **Cartier dual** is

$$
G^D=\operatorname{Hom}(G,\mathbf G_m),
$$

with evaluation $G\times G^D\to\mathbf G_m$. When $G$ is killed by $n$, every character has image in $\mu_n$, so evaluation factors through

$$
G\times G^D\longrightarrow\mu_n. \tag{2.7}
$$

Assume $n$ is invertible in $K$ and $G$ is finite étale. Taking geometric points gives a finite $G_K$-module $M=G(K^s)$. A character of $G$ over $K^s$ is exactly a homomorphism $M\to\mu_n(K^s)$, and descent acts by

$$
(g\lambda)(m)=g\bigl(\lambda(g^{-1}m)\bigr).
$$

Consequently

$$
G^D(K^s)=\operatorname{Hom}(M,\mu_n)=M^*(1). \tag{2.8}
$$

Thus Cartier duality on finite étale coefficients becomes Tate duality on geometric points. Biduality is also the same statement on both sides: evaluation identifies $G$ with $G^{DD}$ and $M$ with $M^{**}$ after the twists cancel.

This perspective explains the characteristic restriction sharply. In characteristic $p$, the Cartier dual of the constant group $\mathbf Z/p\mathbf Z$ is $\mu_p$. The first is étale and the second is connected; its group of geometric points is trivial. Cartier duality remains nontrivial, but the category of finite étale groups is not closed under it. A theorem formulated only with discrete geometric points has therefore thrown away the correct dual. The finite-module theorem in this book excludes that case; a flat-cohomological theorem would retain the whole finite group object and use (2.7).

Two examples fix the convention. The Cartier dual of $\mathbf Z/n\mathbf Z$ is $\mu_n$, while the Cartier dual of $\mu_n$ is $\mathbf Z/n\mathbf Z$. For an elliptic curve $A$ and $n$ invertible in $K$, the Weil pairing identifies the Cartier dual of $A[n]$ with the $n$-torsion of the dual elliptic curve; a principal polarization then gives a self-duality. These are exactly the coefficient pairings that later induce local pairings on first cohomology.

### 2.6 A twist calculus

Twists are easiest to control by recording what evaluation is required to produce. For an $\ell$-primary module, write

$$
M^\vee=\operatorname{Hom}(M,\mathbf Q_\ell/\mathbf Z_\ell),
\qquad M^\vee(1)=M^*(1).
$$

For finite free coefficients over a field $F$ of characteristic $\ell$, one may instead use $M^\vee=\operatorname{Hom}_F(M,F)$ and then tensor by the cyclotomic line $F(1)$. The following identities are canonical whenever the objects are defined:

$$
(M(r))^*(1)\simeq M^*(1)(-r), \tag{2.9}
$$

$$
(M^*(1))^*(1)\simeq M, \tag{2.10}
$$

$$
(M\otimes N)^*(1)
\simeq M^*\otimes N^*(1)
$$

when the coefficients are finite free over a common ring and one of the two displayed stars is interpreted as the untwisted linear dual. The safe rule is to count cyclotomic powers in the target rather than manipulate stars by typography.

For a character $\psi:G_K\to F^\times$, the Tate dual of $F(\psi)$ is

$$
F(\psi^{-1}\bar\chi_\ell). \tag{2.11}
$$

If $\psi$ is unramified and arithmetic Frobenius acts by $\alpha$, then it acts on the dual by $q\alpha^{-1}$. This exchanges the exceptional eigenvalues $1$ and $q$ in local cohomology. An untwisted dual would send $\alpha$ merely to $\alpha^{-1}$ and would miss the degree-two cyclotomic class.

For $W$ finite free, the trace form identifies $\operatorname{End}(W)$ with its untwisted linear dual. Its Tate dual is therefore

$$
\operatorname{End}(W)^*(1)\simeq\operatorname{End}(W)(1). \tag{2.12}
$$

If $W$ has rank $d$ and the coefficient characteristic does not divide $d$, the same holds for trace-zero endomorphisms. When the characteristic divides $d$, scalar matrices have trace zero and the trace form becomes degenerate on that subspace. This is a useful counterexample: a familiar-looking self-duality can fail because a coefficient-theoretic hypothesis, not a Galois-theoretic one, has been omitted.

## 3. Products, boundaries, and signs

### 3.1 Why cochain-level control matters

Perfectness will be propagated through exact sequences. That argument works only if cup products commute with connecting maps with the correct sign. It is therefore not enough to know that a product exists abstractly; we must fix its cochain behavior.

For a $p$-cochain $a$ with values in $M$ and a $q$-cochain $b$ with values in $M^*(1)$, the evaluation cup product is

$$
(a\smile b)(g_1,\ldots,g_{p+q})
=e_M\!\left(a(g_1,\ldots,g_p),
(g_1\cdots g_p)b(g_{p+1},\ldots,g_{p+q})\right). \tag{3.1}
$$

The Galois translate on the second factor is forced by equivariance. The continuous-cochain differential satisfies

$$
d(a\smile b)=da\smile b+(-1)^p a\smile db. \tag{3.2}
$$

Thus (3.1) induces

$$
H^p(K,M)\times H^q(K,M^*(1))
\longrightarrow H^{p+q}(K,\mu_n). \tag{3.3}
$$

### 3.2 Graded interchange

Switching the two cohomology classes switches the coefficient pairing as well. If $e_M^\tau(\lambda,m)=e_M(m,\lambda)$, then

$$
x\smile y=(-1)^{pq}y\smile x \tag{3.4}
$$

after interpreting the right side through $e_M^\tau$. In the middle degree this contributes a minus sign. It does not say that every self-dual local pairing is alternating: the symmetry type of the coefficient pairing contributes another sign.

For example, if $M$ has an alternating perfect pairing $M\times M\to\mu_n$, then the induced pairing on $H^1(K,M)$ is symmetric: one minus sign comes from degree $1$, the other from the alternating coefficient pairing. If the coefficient pairing is symmetric, the induced middle pairing is skew-symmetric. In characteristic two neither sign alone forces a diagonal value to vanish.

### 3.3 Compatibility with connecting maps

Consider (2.4) and its dual (2.5). Let $\delta$ denote a connecting map, with its source and target determined by context. Lift a cocycle, apply (3.2), and observe that evaluation of the two lifts agrees. One obtains

$$
\langle \delta x,y\rangle
=(-1)^{\deg x+1}\langle x,\delta y\rangle, \tag{3.5}
$$

under the standard long-exact-sequence conventions. Replacing all connecting maps by the simultaneously sign-adjusted convention changes both sides together. What matters is that the two long exact sequences are adjoint up to the displayed Koszul sign.

This identity is the hinge of devissage. It implies, for example, that the annihilator of the image of $H^1(K,M')$ is the kernel of the adjoint map out of $H^1(K,M^*(1))$. Exactness then identifies that kernel with the appropriate image from $M''^*(1)$.

### 3.4 Restriction, corestriction, and projection

Let $L/K$ be finite. Restriction respects cups:

$$
\operatorname{res}_{L/K}(x\smile y)
=\operatorname{res}_{L/K}x\smile\operatorname{res}_{L/K}y. \tag{3.6}
$$

Corestriction satisfies the projection formulas

$$
\operatorname{cor}_{L/K}(\operatorname{res}x\smile y)
=x\smile\operatorname{cor}_{L/K}y, \tag{3.7}
$$

and, with the appropriate switched coefficient pairing and graded sign,

$$
\operatorname{cor}_{L/K}(x\smile\operatorname{res}y)
=\operatorname{cor}_{L/K}x\smile y. \tag{3.8}
$$

These identities will turn restriction in one variable into corestriction in the other. They also explain why the normalization of the Brauer invariant cannot be chosen independently over each field.

### 3.5 Bocksteins and the sign ledger

Selmer calculations frequently compare two adjacent torsion levels. The connecting map then is a Bockstein, and its adjoint must be known exactly. Consider

$$
0\longrightarrow M[\ell]
\longrightarrow M[\ell^{a+1}]
\xrightarrow{\ell}M[\ell^a]\longrightarrow0. \tag{3.9}
$$

Dualizing reverses (3.9). If $\beta$ is its connecting map and $\beta^\vee$ is the connecting map for the dual sequence, equation (3.5) gives

$$
\langle\beta x,y\rangle
=(-1)^{\deg x+1}\langle x,\beta^\vee y\rangle. \tag{3.10}
$$

The exponent depends on whether the connecting map is placed before or after the cup. Rather than memorize an isolated sign, one should use the differential identity (3.2). Orthogonal complements are unaffected by multiplying a functional by $-1$, but symmetry assertions are not.

Here is the complete middle-degree sign ledger. Suppose $b:M\times M\to\mu_n$ is an equivariant perfect coefficient pairing and let $\varepsilon=1$ if $b$ is symmetric and $\varepsilon=-1$ if it is alternating, so $b(y,x)=\varepsilon b(x,y)$. Then the induced pairing on $H^1(K,M)$ satisfies

$$
\langle y,x\rangle=-\varepsilon\langle x,y\rangle. \tag{3.11}
$$

Thus a symmetric coefficient pairing produces a skew-symmetric middle pairing, while an alternating coefficient pairing produces a symmetric one. If $2$ is invertible, skew-symmetric implies alternating. At exponent two it does not: $2\langle x,x\rangle=0$ is automatic and says nothing about the diagonal. Quadratic Hilbert symbols and two-torsion on elliptic curves provide concrete instances where ignoring this distinction gives a false parity claim.

Finally, switching from arithmetic to geometric Frobenius replaces $\varphi$ by $\varphi^{-1}$ and the reciprocity map by its inverse. If the invariant normalization is held fixed, all cyclic-symbol formulas acquire a minus sign. We fix arithmetic Frobenius, arithmetic reciprocity, and (4.2) together; no one of these conventions may be changed independently of the other two.

## 4. The Brauer coordinate

### 4.1 Why degree two needs a number

A cup product in complementary degrees lands in $H^2(K,\mu_n)$, still a cohomology group. To turn it into a scalar pairing we need a canonical coordinate on that group. Local central simple algebras provide exactly one.

There is a canonical isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)
=H^2(K,(K^s)^\times)\xrightarrow{\sim}\mathbf Q/\mathbf Z. \tag{4.1}
$$

Its normalization agrees with arithmetic reciprocity: if $K_m/K$ is unramified of degree $m$, $\varphi$ is arithmetic Frobenius, and $\pi_K$ is a uniformizer, then

$$
\operatorname{inv}_K(K_m/K,\varphi,\pi_K^a)=\frac{a}{m}\pmod{\mathbf Z}. \tag{4.2}
$$

Using geometric Frobenius in (4.2) would negate the invariant. We never make that switch silently.

### 4.2 Finite-level invariants

The Kummer sequence

$$
1\longrightarrow\mu_n\longrightarrow(K^s)^\times
\xrightarrow{n}(K^s)^\times\longrightarrow1
$$

is exact precisely under (1.1). Hilbert's Theorem 90 and surjectivity of multiplication by $n$ on $\mathbf Q/\mathbf Z$ give

$$
H^2(K,\mu_n)\xrightarrow{\sim}\operatorname{Br}(K)[n]
\xrightarrow{\operatorname{inv}_K}\frac1n\mathbf Z/\mathbf Z. \tag{4.3}
$$

We denote the composite by $\operatorname{inv}_{K,n}$, usually suppressing $n$. The inclusion into $\mathbf Q/\mathbf Z$ makes the maps for varying $n$ compatible. Identifying $a/n$ with $a\bmod n$ is sometimes convenient, but it depends on the displayed denominator; the $\mathbf Q/\mathbf Z$ target is canonical.

### 4.3 Behavior under extension

For a finite extension $L/K$ of degree $d$,

$$
\operatorname{inv}_L(\operatorname{res}_{L/K}\beta)
=d\operatorname{inv}_K(\beta), \tag{4.4}
$$

whereas

$$
\operatorname{inv}_K(\operatorname{cor}_{L/K}\gamma)
=\operatorname{inv}_L(\gamma). \tag{4.5}
$$

Formula (4.4) follows on the normalized cyclic algebra (4.2): unramified degree raises Frobenius to the residue-degree power, while ramification multiplies the valuation of $\pi_K$ by the ramification index. Formula (4.5) then agrees with $\operatorname{cor}\operatorname{res}=d$.

This asymmetry is exactly right. Restricting both inputs of a local pairing multiplies its value by $[L:K]$; restricting one and corestricting the other preserves it.

### 4.4 Relative fundamental classes

Let $L/K$ be finite Galois with group $\Delta$ and degree $d$. Inflation identifies

$$
H^2(\Delta,L^\times)
\simeq\ker\bigl(\operatorname{Br}(K)\to\operatorname{Br}(L)\bigr).
$$

By (4.4), the kernel corresponds under $\operatorname{inv}_K$ to the subgroup of elements killed by $d$. The **fundamental class** is the unique element

$$
u_{L/K}\in H^2(\Delta,L^\times)
$$

whose image in $\operatorname{Br}(K)$ has invariant $1/d$. This normalization includes an orientation. Replacing the chosen reciprocity isomorphism by its inverse replaces $u_{L/K}$ by $-u_{L/K}$.

Three compatibilities will drive the proof of duality. If $J\leq\Delta$ and $E=L^J$, then

$$
\operatorname{res}^{\Delta}_{J}(u_{L/K})=u_{L/E}. \tag{4.6}
$$

Indeed restriction multiplies the invariant by $[E:K]=d/|J|$, leaving $1/|J|$. If $K\subset E\subset L$ with $E/K$ Galois and quotient group $\Delta/J$, then deflation followed by the norm on coefficients sends the appropriate relative class to $u_{E/K}$; this is the transitivity behind local reciprocity. Finally, if $L'/K$ is a larger finite Galois extension containing $L$ and $e=[L':L]$, inflation satisfies

$$
\operatorname{inf}(u_{L/K})=e\,u_{L'/K}. \tag{4.7}
$$

Both sides have invariant $1/[L:K]=e/[L':K]$. The factor $e$ is indispensable. Fundamental classes are compatible in a normalized system, not literally constant under inflation.

For the unramified extension $K_d/K$, arithmetic Frobenius $\varphi$ generates its Galois group and

$$
u_{K_d/K}=[(K_d/K,\varphi,\pi_K)]. \tag{4.8}
$$

The crossed-product generator has $d$th power $\pi_K$, so its invariant is $1/d$. This example fixes simultaneously the sign of the class, the direction of Frobenius, and the numerator used later in Tate--Nakayama.

## 5. Construction of the local Tate pairing

### 5.1 The only possible construction

We now have three maps, each solving a separate problem: evaluation combines dual coefficients, cup product combines degrees, and the invariant turns the degree-two result into a canonical scalar. Their composite is the **local Tate pairing**

$$
\begin{aligned}
\langle\ ,\ \rangle_{K,M}:
H^r(K,M)\times H^{2-r}(K,M^*(1))
&\longrightarrow\mathbf Q/\mathbf Z,\\
(x,y)&\longmapsto
\operatorname{inv}_K(x\smile y),
\end{aligned} \tag{5.1}
$$

for $r=0,1,2$.

Continuity is automatic at finite level because both cohomology groups are finite discrete groups. Bilinearity follows from cup product. Naturality in $M$ follows from (2.6):

$$
\langle f_*x,y\rangle_{K,N}
=\langle x,f^*(1)_*y\rangle_{K,M}. \tag{5.2}
$$

### 5.2 What perfectness means

A pairing $A\times B\to\mathbf Q/\mathbf Z$ of finite groups is **perfect** if the adjoint maps

$$
A\longrightarrow B^D,
\qquad B\longrightarrow A^D
$$

are isomorphisms. It is enough to prove one is an isomorphism, but it is not enough merely to prove $|A|=|B|$. The hard assertion is nondegeneracy: every nonzero class has a class in the opposite group on which it evaluates nontrivially.

The central theorem, whose proof occupies Chapters 7 and 8, is the following.

**Tate local duality theorem.** Let $K$ be a nonarchimedean local field and let $M$ be a finite continuous $G_K$-module annihilated by an integer prime to $\operatorname{char}K$. For $r=0,1,2$, the pairing (5.1) is perfect. Moreover $H^i(K,M)=0$ for $i>2$.

The theorem includes $p$-primary modules when $K/\mathbf Q_p$ and excludes them when $\operatorname{char}K=p$. No assumption that $K$ contains the relevant roots of unity is made; the Tate twist records their action.

### 5.3 Immediate formal symmetries

Coefficient biduality and graded interchange imply

$$
\langle x,y\rangle_{K,M}
=(-1)^{r(2-r)}\langle y,x\rangle_{K,M^*(1)}, \tag{5.3}
$$

after the canonical double-dual identification. In degrees zero and two there is no sign. In degree one there is a minus sign before any symmetry of an additional self-dual coefficient pairing is considered.

For a subgroup $L\subseteq H^1(K,M)$, define

$$
L^\perp=\{y\in H^1(K,M^*(1)):
\langle x,y\rangle=0\text{ for all }x\in L\}. \tag{5.4}
$$

Once perfectness is known,

$$
|L|\,|L^\perp|=|H^1(K,M)|,
\qquad (L^\perp)^\perp=L. \tag{5.5}
$$

These are consequences, not substitutes for the theorem.

## 6. The cyclic and Kummer calculation

### 6.1 Why the first detector is reciprocity

Before treating an arbitrary action, we calculate the pairing whose two entries already have concrete meanings. Kummer theory gives

$$
H^1(K,\mu_n)=K^\times/(K^\times)^n, \tag{6.1}
$$

and local reciprocity gives

$$
H^1(K,\mathbf Z/n\mathbf Z)
=\operatorname{Hom}_{\mathrm{cts}}(G_K,\mathbf Z/n\mathbf Z)
\simeq\operatorname{Hom}_{\mathrm{cts}}(K^\times,\mathbf Z/n\mathbf Z). \tag{6.2}
$$

No hypothesis $\mu_n\subset K$ is needed. The Tate dual of $\mu_n$ is canonically $\mathbf Z/n\mathbf Z$: an equivariant endomorphism of the root group is a power map.

Let $a\in K^\times$, and let $\chi$ be a character with values in $\mathbf Z/n\mathbf Z$. Reading $\chi$ as a character of $K^\times$ through arithmetic reciprocity, the cup product and cyclic-algebra calculation give

$$
\operatorname{inv}_K\bigl((a)\smile\chi\bigr)
=\frac{\chi(a)}{n}\pmod{\mathbf Z}. \tag{6.3}
$$

Here a value in $\mathbf Z/n\mathbf Z$ is represented by an integer. To verify the sign, let $d$ be the exact order of $\chi$. Let $L/K$ be the cyclic extension cut out by $\chi$ and choose a generator $\sigma$ with $\chi(\sigma)=n/d$ after replacing $\sigma$ by a suitable power. The cup is the pushout to $\mu_n$ of the crossed product $(L/K,\sigma,a)$, so its invariant is $\chi(a)/n$. For an unramified character with $\sigma$ arithmetic Frobenius and $a=\pi_K$, this is $1/d$, exactly (4.2). This formulation does not tacitly assume that every character is surjective onto $\mathbf Z/n\mathbf Z$.

### 6.2 Perfectness in the middle cyclic case

The topology of $K^\times$ has a neighborhood basis of $1$ formed by the principal unit groups. Its quotient by $n$th powers is finite under (1.1). Every homomorphism from this finite quotient is continuous, so ordinary finite Pontryagin duality yields

$$
\operatorname{Hom}_{\mathrm{cts}}(K^\times,\mathbf Z/n\mathbf Z)
\simeq\operatorname{Hom}\bigl(K^\times/(K^\times)^n,
\tfrac1n\mathbf Z/\mathbf Z\bigr). \tag{6.4}
$$

Equations (6.1)--(6.4) prove directly that

$$
H^1(K,\mu_n)\times H^1(K,\mathbf Z/n\mathbf Z)
\longrightarrow\tfrac1n\mathbf Z/\mathbf Z \tag{6.5}
$$

is perfect. This is genuine detection. If the Kummer class of $a$ is nonzero, finite abelian duality supplies a character nonzero on it; local reciprocity realizes that character as a Galois class. Conversely, a nonzero character is nonzero on some $a$.

The reversed pairing for $M=\mathbf Z/n\mathbf Z$ is perfect as well. The graded sign changes (6.3) by a minus sign, which does not affect nondegeneracy.

### 6.3 The endpoint cyclic calculation

Degree zero against degree two can also be seen without counting. For the constant module,

$$
H^0(K,\mathbf Z/n\mathbf Z)=\mathbf Z/n\mathbf Z,
\qquad H^2(K,\mu_n)=\tfrac1n\mathbf Z/\mathbf Z,
$$

and the pairing is multiplication followed by the invariant. The element $1$ detects every nonzero Brauer class, while the class of invariant $1/n$ detects every nonzero constant.

The companion assertion

$$
H^2(K,\mathbf Z/n\mathbf Z)
\simeq \mu_n(K)^D \tag{6.6}
$$

is less visible. If $K$ contains $\mu_n$, a chosen primitive root reduces it to the degree-zero calculation above. In general one may adjoin $\mu_n$, but descent is not obtained merely by taking invariants on one side and coinvariants on the other: the higher terms in the inflation--restriction sequences and their boundary maps must also be controlled. The class-formation and mapping-cone argument in Chapter 7 supplies exactly that control and proves (6.6) as the cup-and-invariant adjoint map. We record the formula here as the endpoint that the descent argument must reach, not as an input to that argument.

For example, if $n$ is prime to $p$ and $g=\gcd(n,q-1)$, then $|\mu_n(K)|=g$ and (6.6) says $|H^2(K,\mathbf Z/n\mathbf Z)|=g$. If $K/\mathbf Q_p$ and $n=p^a$, the same statement holds with $g$ replaced by $|\mu_n(K)|$.

### 6.4 Continuous Hilbert 90

The descent argument will use the multiplicative group of the separable closure, not merely one finite extension. We therefore prove the continuous form of Hilbert 90.

**Theorem 6.1 (continuous Hilbert 90).** For every algebraic extension $F/K$ inside $K^s$,

$$
H^1(G_F,(K^s)^\times)=0. \tag{6.7}
$$

Here $(K^s)^\times$ has the discrete topology and its natural continuous action.

**Proof strategy.** A continuous cocycle from a profinite group to a discrete algebraic group contains only finite information. We force that information into one finite Galois extension and then apply the finite theorem.

Let $c:G_F\to(K^s)^\times$ be a continuous cocycle. Its image is finite because $G_F$ is compact and the target is discrete. Choose a finite Galois extension $L/F$ inside $K^s$ containing every value of $c$. Continuity at the identity supplies an open subgroup on which $c$ is $1$. After intersecting its finitely many conjugates and the subgroup fixing $L$, we obtain an open normal subgroup $U\trianglelefteq G_F$ such that $U$ fixes $L$ and $c(u)=1$ for $u\in U$.

For $g\in G_F$ and $u\in U$,

$$
c(gu)=c(g)\,g(c(u))=c(g),
$$

so $c$ factors through the finite group $\Gamma=G_F/U$. If $E=(K^s)^U$, then all its values lie in $E^\times$ and it is a $1$-cocycle of $\Gamma=\operatorname{Gal}(E/F)$ with coefficients in $E^\times$. The finite multiplicative theorem gives $b\in E^\times$ with

$$
c(g)=b^{-1}g(b).
$$

Hence $c$ is a continuous coboundary, proving (6.7).

For completeness, the finite multiplicative theorem itself follows from one linear-independence argument. Given a cocycle $c:\Gamma\to E^\times$, choose $x\in E$ such that

$$
b=\sum_{\sigma\in\Gamma}c(\sigma)^{-1}\sigma(x)\neq0.
$$

Such an $x$ exists because distinct field embeddings are linearly independent. Changing index and using the cocycle identity gives $\tau(b)=c(\tau)b$, so $c(\tau)=b^{-1}\tau(b)$. This also shows exactly where the field structure is used.

The topology matters. A discontinuous cocycle need not factor through any finite quotient, so the proof would not apply. The algebraic closure also matters: replacing $(K^s)^\times$ by the multiplicative group of a fixed infinite extension without checking where cocycle values lie would leave a gap. The compact-to-discrete argument closes it.

## 7. The descent engine behind perfectness

### 7.1 Why cyclic groups do not suffice by themselves

An arbitrary finite $G_K$-module need not have a filtration by trivial cyclic $G_K$-modules. A prime-to-$\ell$ quotient can act irreducibly on an $\mathbf F_\ell$-space, and an $\ell$-group can act unipotently. Therefore the phrase “devissage to $\mathbf Z/n\mathbf Z$” is incomplete unless the action is also descended.

The missing ingredient is the duality theorem of a local class formation. Its arithmetic input is the normalized fundamental class for every finite extension; its algebraic input is Tate--Nakayama and a permutation-lattice resolution. We state and prove it in the precise range needed here.

### 7.2 The local class formation

Put $C=(K^s)^\times$. For every finite extension $F/K$ inside $K^s$, let $U=G_F$. Hilbert's Theorem 90 and the local invariant give

$$
H^1(U,C)=0,
\qquad
H^2(U,C)=\operatorname{Br}(F)
\xrightarrow{\operatorname{inv}_F}\mathbf Q/\mathbf Z. \tag{7.1}
$$

Now let $V\trianglelefteq U$ be open, let $L=(K^s)^V$, and put $\Delta=U/V=\operatorname{Gal}(L/F)$. Inflation identifies

$$
H^2(\Delta,L^\times)
=\ker\bigl(\operatorname{Br}(F)\to\operatorname{Br}(L)\bigr). \tag{7.2}
$$

The element of invariant $1/|\Delta|$ is the **relative fundamental class**

$$
u_{L/F}\in H^2(\Delta,L^\times). \tag{7.3}
$$

These classes satisfy the decisive subgroup condition. If $J\leq\Delta$, then $L/L^J$ is Galois with group $J$ and

$$
\operatorname{res}^{\Delta}_{J}(u_{L/F})=u_{L/L^J}. \tag{7.4}
$$

Indeed, restriction of the Brauer class from $F$ to $L^J$ multiplies its invariant by $[L^J:F]=|\Delta|/|J|$, turning $1/|\Delta|$ into $1/|J|$. Thus the restricted class has exact order $|J|$ and generates $H^2(J,L^\times)$. Also

$$
H^1(J,L^\times)=0 \tag{7.5}
$$

for every $J$, again by Hilbert 90. Statements (7.4)--(7.5), for **every** subgroup rather than only cyclic or Sylow subgroups, are the local class-formation axioms. Local reciprocity supplies them with the normalization (4.2). No assertion about refining a noncyclic group into cyclic Galois steps is needed.

### 7.3 The Tate Nakayama comparison

The algebraic theorem that extracts duality from (7.4)--(7.5) is Tate--Nakayama. We give the version needed here.

**Tate--Nakayama theorem.** Let $\Delta$ be finite, let $C_0$ be a $\Delta$-module, and let $u\in H^2(\Delta,C_0)$. Suppose that for every subgroup $J\leq\Delta$,

$$
H^1(J,C_0)=0,
\qquad
\operatorname{res}^{\Delta}_{J}(u)
\text{ generates a cyclic group }H^2(J,C_0)
\text{ of order }|J|. \tag{7.6}
$$

Then, for every finitely generated $\mathbf Z$-free $\Delta$-module $X$, cup product with $u$ induces isomorphisms

$$
\widehat H^i(\Delta,X)
\xrightarrow{\sim}
\widehat H^{i+2}(\Delta,X\otimes_{\mathbf Z}C_0)
\qquad(i\in\mathbf Z). \tag{7.7}
$$

These isomorphisms are functorial for restriction, corestriction, and homomorphisms of lattices. The theorem is a statement about **relative Tate cohomology**. It does not claim that ordinary cohomology of one fixed finite quotient is already paired in complementary local degrees; that complementary-degree statement appears only after the compatible relative comparisons are passed through the directed system of finite extensions.

The last sentence is the form we shall use. It is stronger than an equality of Herbrand quotients: it gives an actual chain comparison and hence detects individual nonzero classes.

### 7.4 Proof from the class-formation axioms

Choose a complete resolution $P_\bullet$ of $\mathbf Z$ by finitely generated free $\mathbf Z[\Delta]$-modules. A cocycle representing $u$ defines, by the cup formula, a degree-two chain map from the complete cochain complex with coefficients in a lattice $X$ to the one with coefficients in $X\otimes C_0$. Let $Q_\bullet(X)$ be its mapping cone. Proving Tate--Nakayama amounts to proving that $Q_\bullet(X)$ is exact for every $X$.

Begin with the trivial lattice over a subgroup $J$. In Tate degrees $-1$ and $0$, the comparison is respectively

$$
0=\widehat H^{-1}(J,\mathbf Z)
\longrightarrow H^1(J,C_0)
\quad\text{and}\quad
\mathbf Z/|J|\mathbf Z=\widehat H^0(J,\mathbf Z)
\xrightarrow{\,1\mapsto\operatorname{res}_J u\,}H^2(J,C_0). \tag{7.8}
$$

The first map is an isomorphism because both groups vanish, and the second is an isomorphism because the restricted fundamental class has exact order $|J|$ and generates. Thus the cone is exact in two adjacent degrees for the trivial lattice over every subgroup. This is the only base calculation; in particular, it is not a disguised assertion of local duality for arbitrary coefficients.

For a permutation lattice $\mathbf Z[\Delta/J]$, Shapiro identifies its cone with the cone for the trivial lattice over $J$. For a general lattice $X$, embed it equivariantly into a finite sum $P$ of regular permutation lattices so that the quotient $X'$ is again $\mathbf Z$-free. Concretely, the diagonal map

$$
x\longmapsto\sum_{g\in\Delta}g\otimes g^{-1}x
$$

embeds $X$ in $\mathbf Z[\Delta]\otimes_{\mathbf Z}X$, where $\Delta$ acts only on the left factor; projection to the coefficient of the identity is a retraction of underlying abelian groups, so the quotient is free. We obtain

$$
0\longrightarrow X\longrightarrow P\longrightarrow X'\longrightarrow0 \tag{7.9}
$$

with $P$ permutation. The long exact Tate-cohomology sequences for (7.9), together with the corresponding sequence after tensoring with $C_0$, form a ladder whose vertical arrows are cup product with $u$. The permutation term is already known, so the comparison for $X$ in one degree is equivalent to the comparison for $X'$ in the preceding degree. The analogous surjection from a permutation lattice onto $X$ shifts in the other direction. Iterating along the complete resolution propagates the two base degrees through every degree. This proves (7.7). It is precisely here that the hypothesis for every subgroup is used: every permutation summand is $\mathbf Z[\Delta/J]$, and Shapiro sends it to the $J$-calculation. The mapping cone records actual isomorphisms, not merely equalities of Herbrand quotients.

For the local class formation, (7.4)--(7.5) verify (7.6) with $C_0=L^\times$ and $u=u_{L/F}$. In the unramified cyclic case the construction reduces to the familiar two-periodic complex alternating $\varphi-1$ and the norm, and $u$ is represented by $(L/F,\varphi,\pi_F)$. That computation fixes the sign and shows that the abstract chain map has invariant $1/[L:F]$, not an unspecified generator.

### 7.5 From lattices to arbitrary finite modules

We next prepare the coefficient devissage, where another hidden gap can otherwise occur. Let $A$ be a finite $\Delta$-module killed by $n$. Form the permutation lattice

$$
X_0=\mathbf Z[A],
$$

on the underlying finite $\Delta$-set of $A$, and map the basis element $[a]$ to $a$. Its kernel $X_1$ is a finitely generated free abelian group, so

$$
0\longrightarrow X_1\longrightarrow X_0\longrightarrow A\longrightarrow0 \tag{7.10}
$$

is an equivariant permutation-lattice resolution of length one: $X_0$ is permutation and $X_1$ is a lattice. Tate--Nakayama applies directly to both terms. Its proof for $X_1$ is exactly the dimension shifting of Section 7.4 through regular permutation lattices and the subgroup calculations supplied by Shapiro. No filtration of $A$, and no finite permutation resolution of an arbitrary lattice, is being assumed.

At this point we deliberately do **not** apply $\operatorname{Hom}(-,L^\times)$ and claim exactness: $L^\times$ is not a divisible abelian group, so that would be false in general. We first pass the compatible lattice comparisons through all finite splitting fields. Their coefficient module becomes $C=(K^s)^\times$. Multiplication by $n$ on $C$ is surjective under (1.1), which is exactly the divisibility needed for a quotient killed by $n$. Only then does the reversed Hom sequence become exact. This order is essential in equal characteristic as well as in mixed characteristic.

### 7.6 Passage to the absolute Galois group

Continuous cohomology of a discrete torsion module is the filtered colimit of finite-quotient cohomology. More precisely, a continuous cochain has finite image and is locally constant, so after shrinking an open normal subgroup $V$ that acts trivially on $A$, it factors through $U/V$. The same is true simultaneously for finitely many cochains, their differentials, and chosen coboundaries. Therefore

$$
H^r(U,A)=\varinjlim_V H^r(U/V,A) \tag{7.11}
$$

with the usual inflation transition maps.

On the dual side,

$$
\operatorname{Hom}(A,C)=\operatorname{Hom}(A,\mu_n)=A^*(1). \tag{7.12}
$$

Now apply $\operatorname{Hom}(-,C)$ to (7.10). Since $A$ is killed by $n$ and $C/nC=0$, the obstruction group $\operatorname{Ext}^1(A,C)$ vanishes; decomposing the underlying group of $A$ into cyclic groups makes this explicit. Hence

$$
0\longrightarrow\operatorname{Hom}(A,C)
\longrightarrow\operatorname{Hom}(X_0,C)
\longrightarrow\operatorname{Hom}(X_1,C)\longrightarrow0 \tag{7.13}
$$

is exact. Evaluation makes (7.10) and (7.13) adjoint term by term.

For a lattice $X$, write $X^\vee=\operatorname{Hom}_{\mathbf Z}(X,\mathbf Z)$. The internal Hom module is

$$
\operatorname{Hom}(X,C)=X^\vee\otimes C.
$$

Apply Tate--Nakayama to $X^\vee$. On a complete free resolution, evaluation identifies cochains with coefficients in $X$ with the character dual of the corresponding chain complex with coefficients in $X^\vee$; the norm differential is adjoint to inflation and the augmentation differential is adjoint to restriction. Composing this evaluation identification with the two-degree cup shift (7.7) gives the complementary-degree comparison for each lattice term. This explicit composition is why the dual coefficient is $\operatorname{Hom}(X,C)$ and why the final shift is two.

The tower compatibility requires a degree factor that must not be suppressed. If $V'\subseteq V$, with fixed fields $L'\supseteq L$ and $e=[L':L]$, then coefficient inclusion followed by inflation satisfies

$$
\operatorname{inf}(u_{L/F})=e\,u_{L'/F}. \tag{7.14}
$$

Indeed, both sides have invariant $1/[L:F]=e/[L':F]$. Together with restriction to every subgroup and the invariant-preserving corestriction formula (4.5), equation (7.14) is the precise compatibility used in the chain maps. Thus normalized fundamental classes are not naively unchanged under inflation.

In the complete resolution, the positive-degree part passes to continuous cohomology by (7.11). The negative-degree part consists of invariant kernels modulo norm images. Under the finite evaluation pairing, inflation on the $A$-complex is adjoint to the norm transition on the Hom complex; the factor in (7.14) is exactly the restriction--corestriction degree appearing in that adjunction. The inverse limit of these finite character groups is therefore the Pontryagin character group of the positive-degree colimit. Filtered colimits of abelian groups are exact, while character duality turns this colimit into the indicated inverse limit, so no unmentioned derived-limit term occurs. This is the chain-level source of the reversal $r\mapsto2-r$.

The long exact cohomology sequences of (7.10) and (7.13) form a ladder. Boundary adjointness gives its commuting squares, including the Koszul sign. The relative isomorphisms (7.7) supply isomorphisms on the lattice terms after passage to the directed system, so the five lemma supplies the finite module term. Equivalently, the lattice resolution and the adjoint inflation/norm transitions give a quasi-isomorphism

$$
R\Gamma(U,A)
\simeq
R\operatorname{Hom}\bigl(R\Gamma(U,A^*(1)),\mathbf Q/\mathbf Z\bigr)[-2]. \tag{7.15}
$$

This is the duality theorem of a class formation, proved here from Tate--Nakayama. Because the local cohomology groups are finite, taking character duals introduces neither completion nor derived-limit terms.

We obtain, for every finite $A$ killed by $n$ prime to $\operatorname{char}F$,

$$
H^r(F,A)\xrightarrow{\sim}
H^{2-r}(F,A^*(1))^D,
\qquad r=0,1,2. \tag{7.16}
$$

Tracing the chain map shows that (7.16) sends $x$ to

$$
y\longmapsto\operatorname{inv}_F(x\smile y). \tag{7.17}
$$

Thus the class-formation proof constructs exactly the pairing of Chapter 5. It does not first manufacture an abstract isomorphism and then identify it by cardinality.

### 7.7 The exact-sequence audit

For a final check, consider $0\to A\to B\to C\to0$ and its reversed Tate-dual sequence. Place the long exact cohomology sequence of the first above the Pontryagin dual of the second. Cup-and-invariant supplies the vertical arrows, and boundary adjointness makes every square commute up to the harmless Koszul sign. If the vertical arrows are isomorphisms for two modules, the five lemma gives the third.

This two-of-three statement agrees with the lattice-resolution proof: a permutation module is handled by Shapiro and the class-formation calculation for its stabilizer, while successive kernels are handled by the long exact ladder. The proof never assumes that a Sylow subgroup is cyclic, and it never requires a tower of fixed fields whose steps are all cyclic Galois in a prescribed orientation.

### 7.8 The finite-module Tate--Nakayama form

The proof can now be packaged in the form needed for repeated use.

**Theorem 7.1 (finite-module Tate--Nakayama).** Let $F$ be a nonarchimedean local field, let $n$ be prime to $\operatorname{char}F$, and let $A$ be a finite continuous $G_F$-module killed by $n$. Put

$$
A'=\operatorname{Hom}(A,\mu_n).
$$

Then the normalized local fundamental classes produce a functorial quasi-isomorphism

$$
R\Gamma(F,A)\longrightarrow
R\operatorname{Hom}\bigl(R\Gamma(F,A'),\mathbf Q/\mathbf Z\bigr)[-2], \tag{7.18}
$$

whose map on cohomology is $x\mapsto(y\mapsto\operatorname{inv}_F(x\smile y))$. It is compatible with short exact sequences, restriction, corestriction, and change of $n$.

**Proof.** Choose a finite Galois extension through which the action on $A$ factors and resolve $A$ by (7.10). For every lattice in the resolution, the comparison of Sections 7.3--7.4 is the cup-product isomorphism furnished by the fundamental class. Continuous Hilbert 90 supplies the required first-cohomology vanishing for every stabilizer, while (4.6) supplies the normalized generator in degree two. Passing over larger splitting fields is legitimate because (4.7) matches inflation with the adjoint norm transition.

The group $(K^s)^\times$ is $n$-divisible under the stated characteristic hypothesis. Applying $\operatorname{Hom}(-,(K^s)^\times)$ to the lattice resolution is therefore exact at the finite quotient, and its left term is $A'$. Evaluation identifies the two resolutions term by term. The boundary identity (3.5) identifies their connecting maps up to the required Koszul sign. The two-of-three argument in Section 7.7 gives (7.18). Finally, tracing the fundamental class through the chain map gives cup product, and (4.2) gives precisely $\operatorname{inv}_F$, not its negative. This proves every asserted compatibility.

The characteristic condition is used at one decisive point: surjectivity of the $n$th-power map on $(K^s)^\times$. In characteristic $p$ it fails for $p\mid n$, and $\operatorname{Hom}(A,\mu_n)$ may lose the Cartier dual entirely. Thus the hypothesis is structural rather than a convenience of the proof.

The theorem is stronger than the statement that complementary groups have equal orders. It identifies complexes, so connecting maps, local conditions defined by images, and restriction--corestriction adjunction all descend from the same construction. The perfect pairings are its degreewise shadow.

## 8. Proof and exact forms of Tate local duality

### 8.1 Finiteness before duality

The class-formation comparison identifies character groups only after passage to continuous cohomology, so finiteness must be justified independently. When $\ell\ne p$, inertia has an exact prime-to-$p$ calculation: wild inertia has no higher $\ell$-cohomology, tame inertia contributes one degree, and the procyclic residue quotient contributes one more. All kernels and cokernels are finite. When $\ell=p$ and $K/\mathbf Q_p$, choose a finite extension trivializing the module; Kummer theory and the structure of $L^\times$ give finite cohomology for trivial cyclic modules, and Hochschild--Serre plus module devissage descends finiteness. Vanishing above degree two was established independently from the cohomological dimension of $G_K$.

In equal characteristic $p$, these statements fail for $p$-primary coefficients, exactly as warned in Chapter 1. For prime-to-$p$ coefficients the tame argument works unchanged.

### 8.2 Nondegeneracy in both variables

Let $0\ne x\in H^r(K,M)$. The class-formation quasi-isomorphism (7.15) says that evaluation on $x$ is a nonzero character of the complementary cohomology group. Equivalently, the Tate--Nakayama and lattice-resolution construction produces a class

$$
y\in H^{2-r}(K,M^*(1))
$$

with $\operatorname{inv}_K(x\smile y)\ne0$. Thus every nonzero class in the left variable has a detector. Apply the same construction to $M^*(1)$ and use coefficient biduality to detect every nonzero class in the right variable.

More strongly, (7.16) is already the left adjoint map and proves that it is an isomorphism; the argument for the Tate dual proves the same for the right adjoint. Finiteness, established independently in Section 8.1, now says that these are perfect pairings of finite groups. No equality-of-orders step is being used to manufacture nondegeneracy. This proves the Tate local duality theorem.

### 8.3 Degree zero and degree two

For $r=0$, perfectness gives the canonical identification

$$
H^2(K,M^*(1))\xrightarrow{\sim}H^0(K,M)^D. \tag{8.1}
$$

Replacing $M$ by $M^*(1)$ gives the form usually used for obstructions:

$$
H^2(K,M)\xrightarrow{\sim}
H^0(K,M^*(1))^D. \tag{8.2}
$$

Thus $H^2(K,M)=0$ if and only if $M^*(1)$ has no $G_K$-fixed point. This is a structural criterion, not an Euler-characteristic inference.

At the level of elements, a fixed $\lambda\in M^*(1)$ defines a coefficient map $M\to\mu_n$. The functional on $H^2(K,M)$ is

$$
x\longmapsto\operatorname{inv}_K(\lambda_*x). \tag{8.3}
$$

Every functional arises uniquely this way.

### 8.4 The middle-degree theorem

The central local pairing is

$$
H^1(K,M)\xrightarrow{\sim}
H^1(K,M^*(1))^D. \tag{8.4}
$$

It pairs torsors against dual torsors. In deformation theory, a tangent direction in $H^1(K,M)$ is therefore invisible to a chosen dual local condition precisely when it belongs to the orthogonal subgroup defined by (5.4).

If $F$ is a finite field and $M$ an $F$-representation, the additive character group of an $F$-space is naturally a vector space over the oppositely acting field; after fixing a nonzero trace character $F\to\mathbf F_\ell\to\mathbf Q/\mathbf Z$, (8.4) becomes an $F$-linear duality. Dimensions therefore agree:

$$
h^1_K(M)=h^1_K(M^*(1)). \tag{8.5}
$$

The equality is canonical as a statement about Pontryagin duals; an $F$-valued scalar pairing uses the chosen trace character.

### 8.5 Exact-sequence devissage as a reusable corollary

For (2.4), the long exact cohomology sequence for $M$ is adjoint, under local duality, to the reversed long exact sequence for (2.5). Consequently

$$
\operatorname{im}\bigl(H^r(K,M')\to H^r(K,M)\bigr)^\perp
=\ker\bigl(H^{2-r}(K,M^*(1))
\to H^{2-r}(K,M'^*(1))\bigr). \tag{8.6}
$$

By exactness, the right side is the image from $H^{2-r}(K,M''^*(1))$. Formula (8.6) is the exact annihilator statement attached to a short exact sequence. It is often more useful than the bare assertion of perfectness because local deformation conditions frequently arise as images of extension problems.

### 8.6 Euler--Poincaré formulas in dual form

Duality detects classes, while the Euler characteristic measures their total imbalance. We record both normalizations because later local conditions use dimensions and integral lengths interchangeably.

Let $M$ be a finite $\ell$-primary module. When $\ell\neq p$, or when $K/\mathbf Q_p$ and $\ell=p$, all three cohomology groups are finite. Define

$$
\chi_K^\times(M)=
\frac{|H^0(K,M)|\,|H^2(K,M)|}{|H^1(K,M)|}. \tag{8.7}
$$

Then

$$
\chi_K^\times(M)=
\begin{cases}
1,&\ell\neq p,\\
|M|^{-[K:\mathbf Q_p]},&\ell=p\text{ and }M\text{ is measured over }\mathbf F_p.
\end{cases} \tag{8.8}
$$

The second line means the following invariant statement. If $M$ has finite length over the integers $\mathcal O$ of a finite extension of $\mathbf Q_p$, with residue field $F$, then

$$
\sum_{i=0}^2(-1)^i
\operatorname{length}_{\mathcal O}H^i(K,M)
=-[K:\mathbf Q_p]\operatorname{length}_{\mathcal O}M. \tag{8.9}
$$

**Proof strategy.** Additivity reduces the calculation to simple coefficients. Away from $p$, the two rows supplied by inertia cancel kernel against cokernel. At $p$, the multiplicative group of $K$ supplies the basic calculation and finite-group induction removes the action.

For $\ell\neq p$, put $N=M^{I_K}$ and $P=H^1(I_K,M)$. The residue quotient is procyclic, and the two-row calculation expresses the three orders as

$$
|H^0|=|\ker(\varphi-1\mid N)|,
$$

$$
|H^1|=|\operatorname{coker}(\varphi-1\mid N)|
|\ker(\varphi-1\mid P)|,
$$

$$
|H^2|=|\operatorname{coker}(\varphi-1\mid P)|.
$$

Kernel and cokernel of an endomorphism of a finite group have equal order, so both ratios cancel.

Now let $K/\mathbf Q_p$ and first take $M=\mathbf F_p(1)$ after a prime-to-$p$ extension containing $\mu_p$. Kummer theory, the structure of $K^\times$, and (4.3) give dimensions

$$
(h^0,h^1,h^2)=(1,[K:\mathbf Q_p]+2,1).
$$

Thus the Euler characteristic is $-[K:\mathbf Q_p]$. For a general module killed by $p$, choose a finite quotient controlling the action. Restriction to a Sylow $p$-subgroup gives a filtration with trivial simple factors; the complementary quotient is semisimple by averaging. Shapiro's lemma and additivity then reduce to the trivial calculation over finite extensions. Since $[L:\mathbf Q_p]=[L:K][K:\mathbf Q_p]$, division by the induction degree gives the displayed formula over $K$. Devissage along powers of the coefficient uniformizer proves (8.9). This proof uses no perfectness assertion, so the Euler formula is an independent numerical check on duality.

Using degree-two duality, (8.7) becomes the particularly useful identity

$$
|H^1(K,M)|=
|H^0(K,M)|\,|H^0(K,M^*(1))|\,
\chi_K^\times(M)^{-1}. \tag{8.10}
$$

For a finite-dimensional coefficient field $F$, this reads

$$
h^1_K(M)=h^0_K(M)+h^0_K(M^*(1))
+\delta_{\ell,p}[K:\mathbf Q_p]\dim_FM, \tag{8.11}
$$

where the last term occurs only in mixed characteristic. In equal characteristic $p$ with $p$-primary coefficients, $H^1$ can be infinite and neither (8.7) nor (8.9) is asserted.

## 9. Functoriality in fields and modules

### 9.1 Restriction and corestriction are adjoint

Let $L/K$ be finite. The projection formula and invariance under corestriction give

$$
\boxed{\langle\operatorname{res}_{L/K}x,y\rangle_L
=\langle x,\operatorname{cor}_{L/K}y\rangle_K}, \tag{9.1}
$$

and the other projection formula gives

$$
\boxed{\langle\operatorname{cor}_{L/K}x,y\rangle_K
=\langle x,\operatorname{res}_{L/K}y\rangle_L}. \tag{9.2}
$$

The variables lie in complementary cohomological degrees and in Tate-dual modules. Neither formula contains a degree factor. If both entries are restricted, then (4.4) instead gives

$$
\langle\operatorname{res}x,\operatorname{res}y\rangle_L
=[L:K]\langle x,y\rangle_K. \tag{9.3}
$$

This is consistent with (9.1) and $\operatorname{cor}\operatorname{res}=[L:K]$. Restriction of a Brauer class multiplies its invariant; corestriction preserves it.

### 9.2 Kernels and images under extension

Perfect adjunction converts kernels into annihilators:

$$
\ker(\operatorname{res}_{L/K}:H^r(K,M)\to H^r(L,M))
=\operatorname{im}(\operatorname{cor}_{L/K}:H^{2-r}(L,M^*(1))
\to H^{2-r}(K,M^*(1)))^\perp, \tag{9.4}
$$

and

$$
\operatorname{im}(\operatorname{res}_{L/K})^\perp
=\ker(\operatorname{cor}_{L/K}) \tag{9.5}
$$

in the dual group over $L$. These include the case $\ell\mid[L:K]$, when restriction need not be injective and corestriction need not be surjective.

### 9.3 Adjoint coefficient maps and Shapiro

For $f:M\to N$, naturality gives

$$
\ker H^r(f)=\operatorname{im}H^{2-r}(f^*(1))^\perp,
\qquad
\operatorname{im}H^r(f)^\perp=\ker H^{2-r}(f^*(1)). \tag{9.6}
$$

Thus injection, quotient, and extension conditions have exact dual descriptions. For an open subgroup $G_L\subset G_K$, finite-index induction is also coinduction and

$$
\bigl(\operatorname{Ind}_{G_L}^{G_K}N\bigr)^*(1)
\simeq\operatorname{Ind}_{G_L}^{G_K}(N^*(1)).
$$

Under Shapiro's isomorphism, local duality over $K$ becomes local duality over $L$. The transfer in Shapiro is exactly the corestriction in the projection formula, and the invariant is preserved by (4.5).

## 10. Exact annihilators of local conditions

### 10.1 Orthogonals as exact data

A local condition is a subgroup $\mathcal L\subseteq H^1(K,M)$. Perfectness gives

$$
0\longrightarrow\mathcal L^\perp
\longrightarrow H^1(K,M^*(1))
\longrightarrow\mathcal L^D\longrightarrow0. \tag{10.1}
$$

Hence

$$
|\mathcal L^\perp|=\frac{|H^1(K,M^*(1))|}{|\mathcal L|}. \tag{10.2}
$$

For finite-field coefficients, after the scalar-dual identification,

$$
\dim_F\mathcal L+\dim_F\mathcal L^\perp=h^1_K(M). \tag{10.3}
$$

### 10.2 The unramified condition away from $p$

Let $M$ be finite $\ell$-primary with $\ell\ne p$. Then

$$
H^1_{\mathrm{ur}}(K,M)^\perp
=H^1_{\mathrm{ur}}(K,M^*(1)). \tag{10.4}
$$

Both unramified classes inflate from the procyclic residue-field Galois group. The prime-to-$p$ root module is unramified, and that procyclic group has $\ell$-cohomological dimension one, so their degree-two cup is zero. This proves containment.

For equality, use

$$
|H^1_{\mathrm{ur}}(K,M)|=|H^0(K,M)|, \tag{10.5}
$$

because kernel and cokernel of $\varphi-1$ on the finite group $M^{I_K}$ have equal order. The Euler characteristic is one and degree-two duality identifies $|H^2(K,M)|$ with $|H^0(K,M^*(1))|$. Thus

$$
|H^1(K,M)|=|H^0(K,M)|\,|H^0(K,M^*(1))|. \tag{10.6}
$$

Applying (10.5) to both modules proves that the containment has equal finite orders.

### 10.3 Failure of unramified self-complementarity at $p$

When $K/\mathbf Q_p$ and $M$ is $p$-primary, the Euler characteristic contains the principal-unit factor. Take $M=\mathbf Z/p\mathbf Z$ and suppose $\mu_p\subset K$. Each unramified subgroup has order $p$, but $H^1(K,M)$ has order $p^{[K:\mathbf Q_p]+2}$. The annihilator of an order-$p$ subgroup therefore has order $p^{[K:\mathbf Q_p]+1}$, not $p$. The missing directions are ramified unit classes. Thus (10.4) genuinely requires $\ell\ne p$.

### 10.4 Image, quotient, and norm conditions

If $0\to M'\to M\to M''\to0$ and

$$
\mathcal L=\operatorname{im}(H^1(K,M')\to H^1(K,M)),
$$

then boundary adjointness gives the exact formula

$$
\mathcal L^\perp
=\operatorname{im}(H^1(K,M''^*(1))\to H^1(K,M^*(1))). \tag{10.7}
$$

Upper-triangular extension conditions are typical examples. This formula applies only when the condition really is the displayed image; an extra integral constraint needs an extra argument.

If $L/K$ is finite and

$$
\mathcal N=\operatorname{im}(\operatorname{cor}_{L/K}:H^1(L,M)\to H^1(K,M)),
$$

then

$$
\mathcal N^\perp
=\ker(\operatorname{res}_{L/K}:H^1(K,M^*(1))
\to H^1(L,M^*(1))). \tag{10.8}
$$

Thus coming by norm from $L$ is exactly orthogonal to becoming trivial over $L$.

### 10.5 Finite and singular local quotients

At a place away from the coefficient prime, Selmer theory separates a class into an unramified part and its ramified residue. For finite $\ell$-primary $M$ with $\ell\neq p$, set

$$
H^1_f(K,M)=H^1_{\mathrm{ur}}(K,M),
\qquad
H^1_s(K,M)=H^1(K,M)/H^1_f(K,M). \tag{10.9}
$$

The letters $f$ and $s$ mean **finite** and **singular**. They do not denote finite cardinality: both groups here are already finite. The terminology records the local condition and its quotient.

Equation (10.4) yields two induced perfect pairings:

$$
H^1_f(K,M)\times H^1_s(K,M^*(1))
\longrightarrow\mathbf Q/\mathbf Z, \tag{10.10}
$$

$$
H^1_s(K,M)\times H^1_f(K,M^*(1))
\longrightarrow\mathbf Q/\mathbf Z. \tag{10.11}
$$

To prove (10.10), pair a representative in the second factor with the first. Changing the representative by an unramified dual class changes the value by zero. Nondegeneracy follows because the annihilator of $H^1_f(K,M)$ is exactly $H^1_f(K,M^*(1))$. The proof of (10.11) is identical with the variables reversed.

These pairings make localization sequences numerically transparent. For finite-field coefficients,

$$
\dim H^1_f(K,M)=h^0_K(M),
\qquad
\dim H^1_s(K,M)=h^0_K(M^*(1)). \tag{10.12}
$$

The second equality uses both the Euler characteristic away from $p$ and duality. Thus the singular quotient measures the twisted invariant space. A Frobenius eigenvalue $q$ creates a singular direction; an eigenvalue $1$ creates a finite direction.

The definition must not be transported unchanged to a $p$-adic place. There, the annihilator of the unramified subgroup is much larger than the unramified subgroup on the dual. A condition denoted $H^1_f$ at $p$ must be specified by its arithmetic origin—such as local points or an integral comparison condition—and its duality theorem must be proved for that condition.

### 10.6 Residual conditions and saturation

Let $F$ be a finite coefficient field, let $M$ be an $F$-module, and let

$$
\mathcal L\subseteq H^1(K,M)
$$

be a local condition. Fix a nonzero additive character

$$
\psi_F:F\xrightarrow{\operatorname{Tr}_{F/\mathbf F_\ell}}
\mathbf F_\ell\longrightarrow\tfrac1\ell\mathbf Z/\mathbf Z.
$$

Composing the canonical pairing with $\psi_F$ identifies its Pontryagin dual with the ordinary $F$-linear dual. The **dual local condition** is, by definition,

$$
\mathcal L^*=\mathcal L^\perp
\subseteq H^1(K,M^*(1)). \tag{10.13}
$$

Changing the nonzero character $\psi_F$ rescales the scalar pairing and leaves the zero locus (10.13) unchanged. Hence the orthogonal condition is canonical even when an $F$-valued pairing is not.

If $M$ is the reduction of a lattice $T$, two operations must be distinguished. A condition on $T$ has a **residual image**, the image of its reduction in $H^1(K,M)$; a condition on the associated vector space has an **integral preimage**, its inverse image in $H^1(K,T)$. Torsion in $H^2(K,T)$ can make reduction on $H^1$ fail to be surjective, so these operations are not inverse in general.

A submodule $L\subseteq H^1(K,T)$ is saturated if $H^1(K,T)/L$ is torsion-free. Equivalently,

$$
L=H^1(K,T)\cap(L\otimes E)
$$

inside $H^1(K,T)\otimes E$, provided $H^1(K,T)$ is torsion-free. Saturation is what allows a vector-space orthogonal equality to descend integrally without an unnoticed finite error. When saturation fails, the orthogonal contains information about the finite quotient; replacing $L$ by its saturation changes the residual local condition. This is why a Selmer structure must record its condition at the actual coefficient object, rather than only at the vector-space level.

## 11. Kummer classes and Hilbert symbols

### 11.1 From cup products to symbols

The canonical Kummer--character pairing is

$$
H^1(K,\mu_n)\times H^1(K,\mathbf Z/n\mathbf Z)
\longrightarrow\tfrac1n\mathbf Z/\mathbf Z. \tag{11.1}
$$

If $\mu_n\subset K$ and a primitive root $\zeta_n$ is chosen, the identification $1\mapsto\zeta_n$ turns (11.1) into the Hilbert symbol

$$
(\ ,\ )_n:K^\times/(K^\times)^n\times
K^\times/(K^\times)^n\longrightarrow\mu_n. \tag{11.2}
$$

With our convention, $(a,b)_n$ is the action of $\operatorname{rec}_K(a)$ on an $n$th root of $b$, divided by that root. Reversing reciprocity or swapping entries inverts the symbol. Perfectness of (11.1) proves perfectness of (11.2); changing $\zeta_n$ changes only its coordinate.

### 11.2 Cyclic algebras and norms

Let $L/K$ be cyclic with character $\chi$. The class $(a)\smile\chi$ is the cyclic algebra $(L/K,\sigma,a)$, where $\chi(\sigma)=1$. It vanishes exactly when

$$
a\in N_{L/K}(L^\times). \tag{11.3}
$$

Consequently

$$
N_{L/K}(L^\times)/(K^\times)^n=\langle\chi\rangle^\perp. \tag{11.4}
$$

For a finite abelian extension, its norm group is the simultaneous annihilator of its full character group. This is the norm theorem expressed as cohomological orthogonality.

### 11.3 Units and the unramified direction

Let $U_K$ be the image of $\mathcal O_K^\times$ in $K^\times/(K^\times)^n$. Unramified characters are precisely those trivial on $\mathcal O_K^\times$, so

$$
U_K^\perp=H^1_{\mathrm{ur}}(K,\mathbf Z/n\mathbf Z). \tag{11.5}
$$

When $\mu_n\subset K$, transport the character group back to Kummer cohomology and call the resulting line $U_{K,\mathrm{ur}}$. It consists of classes whose radical extension is unramified. Then

$$
U_K^\perp=U_{K,\mathrm{ur}},
\qquad U_{K,\mathrm{ur}}^\perp=U_K. \tag{11.6}
$$

If $(n,p)=1$, the $n$th-power map is an automorphism of $1+\mathfrak m_K$, and

$$
K^\times/(K^\times)^n\simeq
\langle\pi_K\rangle/\langle\pi_K^n\rangle
\oplus k^\times/(k^\times)^n. \tag{11.7}
$$

Under $\mu_n\subset K$, both summands have order $n$, $U_{K,\mathrm{ur}}=U_K$, and

$$
U_K^\perp=U_K. \tag{11.8}
$$

### 11.4 A tame computation and an even-order warning

Write $a=\pi_K^r u$ and $b=\pi_K^s v$ with units, still assuming $(n,p)=1$ and $\mu_n\subset K$. Then

$$
(a,b)_n=
\left((-1)^{rs}\frac{\overline v^{\,r}}{\overline u^{\,s}}
\right)^{(q-1)/n}\in\mu_n. \tag{11.9}
$$

If $a$ is a unit, varying its residue detects every nonzero valuation $s\bmod n$, proving (11.8) directly. But the decomposition (11.7) need not be orthogonal. For $n=2$,

$$
(\pi_K,\pi_K)_2=(-1)^{(q-1)/2}.
$$

When $q\equiv3\pmod4$, the raw valuation line is not isotropic; its orthogonal is a unit-tilted valuation line.

### 11.5 Principal-unit depth

Let $U_K^a=1+\mathfrak m_K^a$ and write $\overline U_K^a$ for its Kummer image. A character has conductor at most $a$ precisely when it is trivial on $U_K^a$. Therefore

$$
(\overline U_K^a)^\perp
=\{\chi\in H^1(K,\mathbf Z/n\mathbf Z):\chi(U_K^a)=0\}. \tag{11.10}
$$

For prime-to-$p$ $n$, $\overline U_K^1=0$. For $n=p^r$ over $K/\mathbf Q_p$, the principal-unit layers supply the $[K:\mathbf Q_p]$ extra directions. Formula (11.10) is exact without pretending that the $p$th-power map shifts depth uniformly; the shift depends on ramification and roots of unity.

If $\mu_{p^r}\subset K$, the unit subgroup has index $p^r$ in the full Kummer group, and

$$
\bigl(\mathcal O_K^\times/(\mathcal O_K^\times)^{p^r}\bigr)^\perp
=H^1_{\mathrm{ur}}(K,\mu_{p^r}). \tag{11.11}
$$

The right side is a special unit line, not the valuation line. Its orthogonal is the entire unit subgroup. This is the concrete $p$-adic correction to unramified self-complementarity.

## 12. Finite levels, torsion modules, and lattices

### 12.1 Why algebraic duality is no longer enough

At finite level every group is both compact and discrete, so topology is invisible. An inverse limit of finite groups is compact; its Pontryagin dual is a direct limit and is discrete. Pairing two inverse limits and calling the result perfect would confuse algebraic and continuous duals. The correct limit theorem always places a compact object opposite a discrete one.

Fix a prime $\ell$. We remain in the standard range

$$
\ell\ne\operatorname{char}K. \tag{12.1}
$$

Thus $\ell=p$ is allowed for $K/\mathbf Q_p$, while equal-characteristic $p$-adic coefficients are excluded. Let $T$ be a finite free $\mathbf Z_\ell$-module with continuous $G_K$-action and its $\ell$-adic topology. Put

$$
T^\vee=\operatorname{Hom}_{\mathbf Z_\ell}(T,\mathbf Z_\ell),
\qquad
T^\vee(1)=T^\vee\otimes\mathbf Z_\ell(1), \tag{12.2}
$$

and

$$
D(T)=T^\vee(1)\otimes_{\mathbf Z_\ell}\mathbf Q_\ell/\mathbf Z_\ell. \tag{12.3}
$$

The module $D(T)$ is discrete. It is the continuous Tate--Pontryagin dual of the compact group $T$.

### 12.2 Passing the finite pairing to the limit

At level $m$, finite local duality gives

$$
H^r(K,T/\ell^mT)\times
H^{2-r}(K,T^\vee(1)/\ell^mT^\vee(1))
\longrightarrow\tfrac1{\ell^m}\mathbf Z/\mathbf Z. \tag{12.4}
$$

The transition map on the first factor is induced by reduction; the adjoint transition on the second is induced by the inclusion of one torsion level into the next. The projection formula for coefficient maps verifies this adjointness.

Finite-level cohomology is finite in the range (12.1). The inverse systems are therefore Mittag--Leffler, and

$$
H^r(K,T)\simeq\varprojlim_m H^r(K,T/\ell^mT). \tag{12.5}
$$

Continuous cohomology with discrete coefficients commutes with filtered unions, giving

$$
H^{2-r}(K,D(T))
\simeq\varinjlim_m
H^{2-r}(K,T^\vee(1)/\ell^mT^\vee(1)). \tag{12.6}
$$

Taking inverse and direct limits in (12.4) yields

$$
H^r(K,T)\times H^{2-r}(K,D(T))
\longrightarrow\mathbf Q_\ell/\mathbf Z_\ell. \tag{12.7}
$$

**Compact--discrete local duality.** The pairing (12.7) is perfect in the Pontryagin sense:

$$
H^r(K,T)\xrightarrow{\sim}
\operatorname{Hom}_{\mathrm{cts}}
\bigl(H^{2-r}(K,D(T)),\mathbf Q_\ell/\mathbf Z_\ell\bigr), \tag{12.8}
$$

and conversely. The group on the left is compact and finitely generated over $\mathbf Z_\ell$; the opposite group is discrete and cofinitely generated. A continuous character of the compact inverse limit has finite image and therefore factors through a finite level, which proves surjectivity in (12.8). This last observation is the topological step that an abstract inverse-limit argument misses.

### 12.3 Starting with a discrete torsion module

Let

$$
V=T\otimes\mathbf Q_\ell,
\qquad A=V/T.
$$

Then $A$ is discrete and cofinitely generated, and its Tate--Pontryagin dual is the compact lattice

$$
D(A)=\operatorname{Hom}_{\mathrm{cts}}
(A,\mathbf Q_\ell/\mathbf Z_\ell)(1)
\simeq T^\vee(1). \tag{12.9}
$$

Finite-level duality now gives a perfect pairing

$$
H^r(K,A)\times H^{2-r}(K,T^\vee(1))
\longrightarrow\mathbf Q_\ell/\mathbf Z_\ell. \tag{12.10}
$$

The first cohomology group is given its natural discrete topology and the second its profinite topology. Divisible subgroups are not to be discarded: under Pontryagin duality they correspond to torsion-free quotients on the compact side.

More generally, if $A$ is any discrete $\ell$-primary module that is a filtered union of finite $G_K$-submodules and has finite corank, its continuous Tate dual $D(A)$ is compact. Passing through the finite submodules gives

$$
H^r(K,A)^D\simeq H^{2-r}(K,D(A)). \tag{12.11}
$$

Without finite-corank or finite-level finiteness hypotheses, (12.11) requires additional control of limits and need not be a statement about finitely generated groups.

### 12.4 Coefficients in a finite extension of $\mathbf Q_\ell$

Let $E/\mathbf Q_\ell$ be finite with ring of integers $\mathcal O$. An $\mathcal O$-lattice is also a finite free $\mathbf Z_\ell$-module, so the preceding theorem applies canonically after taking the $\mathbf Z_\ell$-linear dual. If one instead writes

$$
T_E^*=\operatorname{Hom}_{\mathcal O}(T,\mathcal O),
$$

then the trace pairing identifies the $\mathbf Z_\ell$-dual of $\mathcal O$ with the inverse different $\mathfrak D_{E/\mathbf Q_\ell}^{-1}$, not automatically with $\mathcal O$. An $\mathcal O$-linear perfect integral pairing must account for this different, or choose a generating additive character. At the $E$-vector-space level the issue disappears after scalar extension.

### 12.5 Vector-space duality

Let $V$ be a finite-dimensional $E$-representation with a stable lattice, and put

$$
V^*(1)=\operatorname{Hom}_E(V,E)(1).
$$

The compatible finite invariants identify

$$
H^2(K,E(1))\simeq E. \tag{12.12}
$$

Cup product and (12.12) give

$$
H^r(K,V)\times H^{2-r}(K,V^*(1))\longrightarrow E. \tag{12.13}
$$

Tensoring lattice duality with $E$ proves that (12.13) is a perfect pairing of finite-dimensional $E$-vector spaces. It is independent of the stable lattice: two lattices are commensurable, and their finite-index discrepancy vanishes after inverting $\ell$.

Thus three assertions must be kept distinct:

| coefficient object | topology | dual partner | meaning of perfect |
|---|---|---|---|
| finite $M$ | finite discrete | finite $M^*(1)$ | finite Pontryagin dual |
| compact lattice $T$ | profinite | discrete $D(T)$ | continuous Pontryagin dual |
| vector space $V$ | $\ell$-adic | vector space $V^*(1)$ | perfect $E$-bilinear form |

### 12.6 What breaks in equal characteristic $p$

If $\operatorname{char}K=p$ and $\ell=p$, then $\mathbf Z_p(1)=\varprojlim\mu_{p^m}(K^s)$ is zero, not a rank-one lattice. Finite $p$-primary $H^1$ can be infinite, the Mittag--Leffler finiteness argument above is unavailable, and (12.12) has no usual Galois-module meaning. One must change the coefficient theory, for example to flat finite group schemes or logarithmic dualizing objects. None of the displayed $p$-adic limit statements is asserted in that setting.

### 12.7 Exact triples and integral orthogonals

The coefficient triple used in Selmer theory is

$$
0\longrightarrow T\longrightarrow V\longrightarrow A\longrightarrow0,
\qquad
V=T\otimes_{\mathbf Z_\ell}\mathbf Q_\ell,
\quad A=V/T. \tag{12.14}
$$

Put

$$
T'=\operatorname{Hom}_{\mathbf Z_\ell}(T,\mathbf Z_\ell)(1),
\quad V'=T'\otimes\mathbf Q_\ell,
\quad A'=V'/T'. \tag{12.15}
$$

Evaluation gives compatible perfect pairings

$$
H^1(K,T)\times H^1(K,A')\to\mathbf Q_\ell/\mathbf Z_\ell,
$$

$$
H^1(K,A)\times H^1(K,T')\to\mathbf Q_\ell/\mathbf Z_\ell,
$$

and

$$
H^1(K,V)\times H^1(K,V')\to\mathbf Q_\ell. \tag{12.16}
$$

Let $L_V\subseteq H^1(K,V)$ and $L_{V'}\subseteq H^1(K,V')$ be exact orthogonal complements. Propagate them by

$$
L_T=\{x\in H^1(K,T):x_V\in L_V\},
\qquad
L_A=\operatorname{im}(L_V\to H^1(K,A)), \tag{12.17}
$$

and similarly on the primed side. Then

$$
L_T^\perp=L_{A'},
\qquad
L_A^\perp=L_{T'}. \tag{12.18}
$$

**Proof strategy.** Orthogonality over $\mathbf Q_\ell$ first proves containment. Exactness of the long cohomology sequences accounts for the classes that die on passage between $T,V,A$; boundary adjointness proves that those kernels are paired with the corresponding images on the dual side. The quotient pairings left after removing those kernels are the vector-space pairing (12.16). Hence any class annihilating $L_T$ differs by an appropriate boundary from the image of a class in $L_{V'}$, which puts it in $L_{A'}$. This proves the first equality; reversing the triple proves the second. Equivalently, place the two long exact sequences in an adjoint diagram and apply exactness at the four middle terms.

The image and preimage in (12.17) are part of the theorem. Replacing both by raw reduction modulo $\ell^m$ can change the condition when adjacent cohomology has torsion. Likewise, an arbitrary lattice $T'\subset V'$ that is merely commensurable with the evaluation dual of $T$ introduces a finite index into (12.18). Exact integral orthogonality requires the actual dual lattice.

For coefficients in the integers $\mathcal O$ of a finite extension of $\mathbf Q_\ell$, one may use the $\mathcal O$-linear dual provided the scalar character and inverse different are normalized as in Section 12.4. Working first over $\mathbf Z_\ell$ keeps (12.18) canonical.

### 12.8 Unramified conditions for lattices

Assume $\ell\neq p$. On the vector space define

$$
H^1_f(K,V)=H^1_{\mathrm{ur}}(K,V)
=\ker\bigl(H^1(K,V)\to H^1(I_K,V)\bigr). \tag{12.19}
$$

Define the integral and discrete conditions by propagation:

$$
H^1_f(K,T)=\operatorname{preim}\bigl(H^1_f(K,V)\bigr),
$$

$$
H^1_f(K,A)=\operatorname{im}\bigl(H^1_f(K,V)\to H^1(K,A)\bigr). \tag{12.20}
$$

Vector-space local duality and the finite-level unramified calculation give

$$
H^1_f(K,V)^\perp=H^1_f(K,V'). \tag{12.21}
$$

Applying (12.18) yields the exact integral statements

$$
H^1_f(K,T)^\perp=H^1_f(K,A'),
\qquad
H^1_f(K,A)^\perp=H^1_f(K,T'). \tag{12.22}
$$

There is a subtle but useful distinction between (12.20) and the raw kernel

$$
\ker\bigl(H^1(K,T)\to H^1(I_K,T)\bigr).
$$

The latter maps into $H^1_f(K,T)$, but equality can fail if a ramified integral class becomes unramified after division by a power of $\ell$. The propagated condition is saturated by construction and is the one compatible with (12.22). At finite torsion level, one must likewise specify whether the condition is the intrinsic unramified kernel or the image propagated from $A$; they agree under additional torsion-freeness hypotheses but not by notation alone.

For an unramified rank-one lattice on which arithmetic Frobenius acts by $\alpha$, the vector-space condition vanishes if $\alpha\neq1$, while the raw integral quotient $\mathbf Z_\ell/(\alpha-1)$ may be nonzero. This finite congruence is exactly the phenomenon that saturation separates from the rational local condition.

## 13. Dimension formulas and deformation-theoretic consequences

### 13.1 Removing the mysterious $H^2$

Let $F$ be a finite field of characteristic $\ell$, and let $M$ be a finite-dimensional $F$-representation in the duality range. Degree-two duality gives

$$
h^2_K(M)=h^0_K(M^*(1)). \tag{13.1}
$$

Combining this with the Euler characteristic from Book 30 yields

$$
h^1_K(M)=h^0_K(M)+h^0_K(M^*(1)) \tag{13.2}
$$

when $\ell\ne p$, and

$$
h^1_K(M)=h^0_K(M)+h^0_K(M^*(1))
+[K:\mathbf Q_p]\dim_FM \tag{13.3}
$$

when $K/\mathbf Q_p$ and $\ell=p$. Formula (13.3) separates three sources of tangent directions: automorphisms, dual automorphisms or obstructions, and the bulk of principal-unit directions.

For an $E$-representation $V$, the same formulas hold with $E$-dimensions. For a finite-length $\mathcal O$-module, they hold with lengths. These equalities are compatible with short exact sequences because Euler characteristics, Tate duals, and invariant dimensions all have the corresponding additivity relation.

### 13.2 Self-dual modules and parity

Suppose an equivariant perfect coefficient pairing identifies

$$
M\simeq M^*(1). \tag{13.4}
$$

Then

$$
h^2_K(M)=h^0_K(M),
$$

and

$$
h^1_K(M)=
\begin{cases}
2h^0_K(M),&\ell\ne p,\\
2h^0_K(M)+[K:\mathbf Q_p]\dim_FM,&\ell=p.
\end{cases} \tag{13.5}
$$

The symmetry type changes in degree one. A symmetric coefficient pairing produces a skew-symmetric pairing on $H^1$; if $2$ is invertible, it is alternating and $h^1$ is even. An alternating coefficient pairing produces a symmetric pairing on $H^1$. One must include both the coefficient sign and the graded sign before drawing a parity conclusion.

### 13.3 Adjoint representations

Let $W$ be a $d$-dimensional $F$-representation and

$$
\operatorname{ad}W=\operatorname{End}_F(W)
$$

with conjugation action. The trace pairing is perfect and equivariant, so

$$
(\operatorname{ad}W)^*(1)\simeq\operatorname{ad}W(1). \tag{13.6}
$$

Therefore the local obstruction dimension is

$$
h^2_K(\operatorname{ad}W)
=h^0_K(\operatorname{ad}W(1)). \tag{13.7}
$$

The right side consists of endomorphisms $X$ satisfying

$$
\rho(g)X\rho(g)^{-1}=\bar\chi_\ell(g)^{-1}X.
$$

It is often easier to calculate than a two-cocycle group. For example, if $W$ is absolutely irreducible, $h^0(\operatorname{ad}W)=1$, while (13.7) vanishes unless $W$ admits a cyclotomic self-twist of the relevant kind.

If $\ell\nmid d$, trace restricts nondegenerately to

$$
\operatorname{ad}^0W=\ker(\operatorname{tr}),
$$

so

$$
(\operatorname{ad}^0W)^*(1)\simeq\operatorname{ad}^0W(1) \tag{13.8}
$$

and

$$
h^1_K(\operatorname{ad}^0W)
=h^0_K(\operatorname{ad}^0W)
+h^0_K(\operatorname{ad}^0W(1))
+\delta_{\ell,p}[K:\mathbf Q_p](d^2-1). \tag{13.9}
$$

Here $\delta_{\ell,p}$ is present only in mixed characteristic. When $\ell\mid d$, scalar matrices lie in $\operatorname{ad}^0$, the trace pairing on it is degenerate, and (13.8)--(13.9) cannot be used without replacing $\operatorname{ad}^0$ by its correct dual quotient.

### 13.4 Tangent spaces and their dual conditions

For a residual representation $\bar\rho$, an unframed first-order deformation problem has ambient tangent space $H^1(K,\operatorname{ad}\bar\rho)$, or $H^1(K,\operatorname{ad}^0\bar\rho)$ with fixed determinant. A chosen local deformation condition supplies a subspace

$$
L_K\subseteq H^1(K,M).
$$

Its exact dual condition is $L_K^\perp\subseteq H^1(K,M^*(1))$. Thus

$$
\dim L_K-h^0_K(M)
=h^0_K(M^*(1))+\delta_{\ell,p}[K:\mathbf Q_p]\dim M
-\dim L_K^\perp. \tag{13.10}
$$

This is just (10.3) and (13.2)--(13.3) rearranged, but it is the form used in local tangent bookkeeping: the excess of allowed tangent directions over infinitesimal automorphisms is measured by the dual invariants, the $p$-adic field term, and the codimension of the dual condition.

For $\ell\ne p$, the unramified condition is paired with the unramified dual condition. Equation (10.5) gives

$$
\dim H^1_{\mathrm{ur}}(K,M)=h^0_K(M), \tag{13.11}
$$

so the left side of (13.10) is zero. At $p$, a finite-flat or other integral condition is not determined by the ambient duality theorem alone; one must prove its annihilator using the integral model. Local duality then converts that proof into an exact dimension statement.

### 13.5 Framed dimensions

The framed cocycle space has

$$
\dim_F Z^1(K,M)=h^1_K(M)+\dim_FM-h^0_K(M) \tag{13.12}
$$

when $M$ is an adjoint module and coboundaries arise from changing the frame. Substitution gives

$$
\dim Z^1
=h^0_K(M^*(1))+(1+\delta_{\ell,p}[K:\mathbf Q_p])\dim M. \tag{13.13}
$$

The centralizer term cancels. The remaining twisted invariant is the genuine local obstruction contribution.

### 13.6 The local correction term used in Selmer theory

For a finite-dimensional $F$-module $M$ and a local condition $L_K\subseteq H^1(K,M)$, define the normalized local correction

$$
c_K(M,L_K)=\dim_F L_K-h^0_K(M). \tag{13.14}
$$

Subtracting $h^0$ is not cosmetic. Degree zero measures infinitesimal automorphisms, and this normalization is the one that makes an unramified condition away from $\ell$ contribute zero:

$$
c_K(M,H^1_{\mathrm{ur}})=0 \qquad(\ell\neq p). \tag{13.15}
$$

Let $L_K^\perp$ be the orthogonal condition on $M^*(1)$. Perfectness and (8.11) give the exact identity

$$
c_K(M,L_K)+c_K(M^*(1),L_K^\perp)
=\delta_{\ell,p}[K:\mathbf Q_p]\dim_FM. \tag{13.16}
$$

**Proof.** Since the middle pairing is perfect,

$$
\dim L_K^\perp=h^1_K(M)-\dim L_K.
$$

Subtract $h^0_K(M^*(1))$ and insert (8.11). The remaining terms are $h^0_K(M)-\dim L_K$ and the mixed-characteristic field term, which gives (13.16).

Away from the coefficient prime, the two normalized corrections are negatives of one another. At a place above the coefficient prime, their sum is the full principal-unit contribution. This is the local numerical identity used when a Selmer condition and its dual are compared globally. It also catches a common sign error: defining the correction as $h^0-\dim L_K$ would reverse every away-from-$\ell$ contribution.

For finite-length $\mathcal O$-modules, define

$$
c_K(M,L_K)=\operatorname{length}_{\mathcal O}L_K
-\operatorname{length}_{\mathcal O}H^0(K,M).
$$

The same proof gives (13.16) with lengths and with the right side $[K:\mathbf Q_p]\operatorname{length}_{\mathcal O}M$. For vector spaces, use $E$-dimensions. These three versions agree under passage through a stable lattice when the local conditions are propagated as in (12.17).

### 13.7 Changing coefficient rings

Let $F\subseteq F'$ be a finite extension of finite coefficient fields and put $M'=M\otimes_FF'$. Flatness and finite-dimensionality give

$$
H^i(K,M')\simeq H^i(K,M)\otimes_FF'. \tag{13.17}
$$

If $L_K' = L_K\otimes_FF'$, then orthogonals commute with scalar extension:

$$
(L_K')^\perp=L_K^\perp\otimes_FF'. \tag{13.18}
$$

To prove this, choose $a\in F'$ with $\operatorname{Tr}_{F'/F}(a)=1$ and use the additive character $x\mapsto\psi_F(\operatorname{Tr}_{F'/F}(ax))$; its restriction to $F$ is $\psi_F$. Evaluation and cup product commute with scalar extension, so the right side is contained in the left. Their dimensions agree by perfectness, proving equality. In particular $c_K(M',L_K')=c_K(M,L_K)$ as a dimension, even though the underlying finite cardinalities change.

For a quotient $\mathcal O\to\mathcal O/\varpi^a$, scalar change is no longer flat and (13.17) can acquire adjacent torsion terms. The safe construction is to propagate the local condition through the exact coefficient sequence and use boundary adjointness. If $L_T$ is saturated, its reduction is well behaved; without saturation, reduction can gain classes from the $\varpi$-torsion of the quotient. Thus residual Selmer conditions should be defined by an explicit image or preimage, not by the phrase “the same condition modulo $\varpi$.”

## 14. Five families of examples

### 14.1 Trivial and cyclotomic lines away from $p$

Let $F$ be a finite field of characteristic $\ell\ne p$, and write $q$ also for its image in $F^\times$. For the trivial line $F$, the Tate dual is $F(1)$. Hence

$$
h^0_K(F)=1,
\qquad
h^2_K(F)=h^0_K(F(1))=[q=1], \tag{14.1}
$$

and

$$
h^1_K(F)=1+[q=1]. \tag{14.2}
$$

The first degree-one direction is unramified: it records the value of a character on arithmetic Frobenius. If $q=1$ in $F$, a second tame direction appears because Frobenius fixes the $\ell$-part of tame inertia.

For the cyclotomic line $F(1)$, the dual is $F$. Thus

$$
h^0_K(F(1))=[q=1],
\qquad h^2_K(F(1))=1,
\qquad h^1_K(F(1))=1+[q=1]. \tag{14.3}
$$

The permanent degree-two class is the finite Brauer invariant. Duality exchanges the fixed trivial vector in (14.1) with that Brauer class, while the two middle groups pair perfectly.

Suppose $q\not\equiv1\pmod\ell$. Then $H^1(K,F)$ is the one-dimensional unramified character line and $H^1(K,F(1))$ is the one-dimensional tame Kummer line. Their pairing is nonzero: the valuation character detects the Kummer class of a uniformizer. This is the simplest visible form of Frobenius--inertia duality.

### 14.2 An unramified character

Let $M=F(\psi)$ be unramified and put $\alpha=\psi(\varphi)$. Arithmetic Frobenius on the Tate dual has eigenvalue $q\alpha^{-1}$. Therefore

$$
h^0_K(M)=[\alpha=1],
\qquad h^2_K(M)=[\alpha=q], \tag{14.4}
$$

and

$$
h^1_K(M)=[\alpha=1]+[\alpha=q]. \tag{14.5}
$$

Thus a generic unramified line has no cohomology. At $\alpha=1$ an unramified class appears; at $\alpha=q$ a tame class and its degree-two obstruction appear. Duality exchanges these two exceptional eigenvalues, since

$$
\alpha\longmapsto q\alpha^{-1}
$$

interchanges $1$ and $q$.

When $K/\mathbf Q_p$ and $F$ has characteristic $p$, the same invariant terms occur, but (14.5) acquires $[K:\mathbf Q_p]$ additional dimensions. Even if $\psi$ is unramified, those classes arise from the ramified principal-unit part of $G_K^{\mathrm{ab}}$; they are not visible from the Frobenius eigenvalue alone.

### 14.3 A concrete quadratic Hilbert pairing

Let $K=\mathbf Q_p$ with $p$ odd, and take $n=2$. Choose a nonsquare residue unit $u$. Then

$$
K^\times/(K^\times)^2=\{1,u,\pi,u\pi\}.
$$

The unit subgroup $\{1,u\}$ is self-orthogonal. The value

$$
(u,\pi)_2=-1
$$

shows that neither nonzero line lies in the radical. Meanwhile

$$
(\pi,\pi)_2=(-1)^{(p-1)/2}.
$$

If $p\equiv1\pmod4$, the valuation line $\{1,\pi\}$ is self-orthogonal. If $p\equiv3\pmod4$, then $(\pi,\pi)_2=-1$ and its orthogonal is $\{1,u\pi\}$. In both cases the matrix of the pairing is nonsingular. This four-element computation displays both perfectness and the even-order diagonal warning.

### 14.4 Elliptic-curve torsion

Let $E/K$ be an elliptic curve and let $n$ satisfy (1.1). The Weil pairing

$$
e_n:E[n]\times E[n]\longrightarrow\mu_n
$$

is perfect, alternating, and $G_K$-equivariant. It identifies

$$
E[n]\simeq E[n]^*(1). \tag{14.6}
$$

Local Tate duality therefore supplies a perfect self-pairing

$$
H^1(K,E[n])\times H^1(K,E[n])
\longrightarrow\tfrac1n\mathbf Z/\mathbf Z. \tag{14.7}
$$

Because both cup interchange and the Weil pairing contribute a minus sign, (14.7) is symmetric. It is not automatically alternating, especially at $n$ even.

The Kummer sequence gives

$$
0\longrightarrow E(K)/nE(K)
\xrightarrow{\delta_n}H^1(K,E[n])
\longrightarrow H^1(K,E)[n]\longrightarrow0. \tag{14.8}
$$

The image of $\delta_n$ is self-annihilating under (14.7):

$$
\delta_n(E(K)/nE(K))^\perp
=\delta_n(E(K)/nE(K)). \tag{14.9}
$$

This assertion uses more than ambient finite-module duality: it also uses compatibility of Kummer boundaries with the Weil pairing. We make that extra input explicit. Let $\phi:E\to E'$ be an isogeny of degree $m$ prime to $\operatorname{char}K$, and let $\widehat\phi:E'\to E$ be its dual. The isogeny Weil pairing identifies $E[\phi]^*(1)$ with $E'[\widehat\phi]$. The needed boundary lemma says

$$
\operatorname{inv}_K\bigl(\delta_\phi(P')\smile
\delta_{\widehat\phi}(Q)\bigr)=0
\qquad(P'\in E'(K),\ Q\in E(K)).
$$

This is not a formal consequence of finite-module duality. It follows from the defining adjunction of $\phi$ and $\widehat\phi$ for the Poincaré biextension: pull the biextension back along the two isogenies, use its canonical trivializations, and take Galois boundaries. The resulting two-cocycle is exactly the cup of the two Kummer boundary cocycles, while the biextension trivialization makes it a coboundary. Hence the two Kummer images are orthogonal. This establishes the required containment before any comparison of orders.

To see that the containment is exact, normalize $|x|_K=q^{-v_K(x)}$. For an elliptic curve choose a Néron invariant differential and let $\mu_A$ be the resulting Haar measure on $A(K)$. If $\psi:A\to B$ is an isogeny and $\psi^*\omega_B=a_\psi\omega_A$, put $|d\psi(0)|_K=|a_\psi|_K$. Changing either Néron differential by a unit changes neither the measure nor this number. The local index formula is

$$
\frac{|\operatorname{coker}(\psi:A(K)\to B(K))|}
{|\ker(\psi:A(K)\to B(K))|}
=\frac{\mu_B(B(K))}{\mu_A(A(K))}
|d\psi(0)|_K^{-1}. \tag{14.10}
$$

It follows by comparing Haar measure on sufficiently small formal neighborhoods and then the finite reduction quotients; it remains valid when the residue characteristic divides the degree. When (14.10) is multiplied for $\phi$ and $\widehat\phi$, the two total-volume ratios cancel. Since $d\widehat\phi(0)d\phi(0)=m$, this gives

$$
|E'(K)/\phi E(K)|\,|E(K)/\widehat\phi E'(K)|
=|E[\phi](K)|\,|E'[\widehat\phi](K)|\,|m|_K^{-1}. \tag{14.11}
$$

The local Euler characteristic for $E[\phi]$, together with degree-zero and degree-two duality, identifies the right side of (14.11) with $|H^1(K,E[\phi])|$: the factor $|m|_K^{-1}$ is $1$ away from the residue characteristic and is exactly the mixed-characteristic Euler factor otherwise. Perfectness now upgrades the established orthogonal containment to

$$
\delta_\phi(E'(K)/\phi E(K))^\perp
=\delta_{\widehat\phi}(E(K)/\widehat\phi E'(K)). \tag{14.12}
$$

Taking $\phi=[n]=\widehat\phi$ gives (14.9). Thus the familiar finite local condition furnished by local points is not merely isotropic; it is its full annihilator. The hypotheses are essential: $K$ is local, the isogeny is separable in the coefficient range, the opposite kernel is that of the dual isogeny, and the pairing is normalized by the isogeny Weil pairing. An arbitrary self-dual finite module or arbitrary subgroup of its $H^1$ has no analogous automatic self-annihilator statement.

Passing to $T_\ell E$ and $V_\ell E$ uses Chapter 12. The Weil pairing identifies

$$
T_\ell E^\vee(1)\simeq T_\ell E,
\qquad V_\ell E^*(1)\simeq V_\ell E. \tag{14.13}
$$

These identifications yield compact--discrete and $\ell$-adic self-dualities in complementary degrees. Good, multiplicative, or additive reduction affects the Kummer local subspace and inertia action, but not the existence of the perfect ambient pairing.

### 14.5 Mixed-characteristic cyclotomic coefficients

Let $K/\mathbf Q_p$ have degree $d_K$, take $M=\mu_{p^r}$, and put $u_r=|\mu_{p^r}(K)|$. Kummer theory, the Brauer invariant, and duality give

$$
|H^0(K,\mu_{p^r})|=u_r,
\qquad |H^2(K,\mu_{p^r})|=p^r, \tag{14.14}
$$

while the Euler characteristic gives

$$
|H^1(K,\mu_{p^r})|=p^{r(d_K+1)}u_r. \tag{14.15}
$$

The Tate dual is the constant module $\mathbf Z/p^r\mathbf Z$. Consequently

$$
|H^2(K,\mathbf Z/p^r\mathbf Z)|=u_r,
$$

and its $H^1$ has the same order as (14.15). The factors have distinct origins: $p^r$ from valuation, $p^{rd_K}$ from principal units, and $u_r$ from roots of unity in the kernel of the power map.

For $r=1$ and $\mu_p\subset K$, both coefficient modules are trivial. Nevertheless the orthogonal of the unramified line in $H^1(K,\mu_p)$ has dimension $d_K+1$, not one. Under Kummer theory it is the full image of $\mathcal O_K^\times$. This example simultaneously checks the Tate twist, the $p$-adic Euler term, and the warning in Section 10.3.

## 15. The local-duality dictionary

### 15.1 A calculation protocol

For later use, a local duality calculation should proceed in this order.

1. Record $\operatorname{char}K$, the residue characteristic $p$, and the coefficient exponent. In equal characteristic, exclude the $p$-primary Galois-module theorem.
2. Form the actual Tate dual $M^*(1)=\operatorname{Hom}(M,\mu_n)$; do not replace it by an untwisted linear dual.
3. Compute $H^0(K,M)$ and $H^0(K,M^*(1))$. Duality immediately gives both $H^2$ groups.
4. Insert these dimensions into the Euler formula to obtain $h^1$.
5. Describe the proposed local condition $\mathcal L$ as a kernel, image, unramified subgroup, norm subgroup, Kummer image, or genuinely integral condition.
6. Use adjunction or boundary compatibility to prove a containment in the expected annihilator. Then use perfectness to prove equality, checking dimensions or orders only after containment.
7. Under field extension, pair restriction with corestriction and remember that restricting both entries multiplies the invariant by the degree.
8. At infinite level, state which group is compact and which is discrete. For vector spaces, pass from a stable lattice only after establishing the finite-level compatibility.

This order prevents the common circular argument in which a guessed annihilator is assigned the correct size and then treated as proved.

### 15.2 Formula table

The principal identifications are

| input | exact dual statement |
|---|---|
| $H^0(K,M)$ | $H^2(K,M^*(1))^D$ |
| $H^1(K,M)$ | $H^1(K,M^*(1))^D$ |
| $H^2(K,M)$ | $H^0(K,M^*(1))^D$ |
| coefficient map $f$ | adjoint map $f^*(1)$ |
| restriction to $L$ | corestriction from $L$ |
| image of a coefficient submodule | kernel for the dual quotient |
| unramified condition, $\ell\ne p$ | unramified condition on the Tate dual |
| norms from $L$ | dual classes trivialized by $L$ |
| Kummer units | unramified characters |
| $U_K^a$ | characters of conductor at most $a$ |
| compact lattice $T$ | discrete $D(T)$ |
| vector space $V$ | $E$-linear $V^*(1)$ |

The normalization formulas are

$$
\operatorname{inv}_L(\operatorname{res}\beta)
=[L:K]\operatorname{inv}_K(\beta),
\qquad
\operatorname{inv}_K(\operatorname{cor}\gamma)
=\operatorname{inv}_L(\gamma), \tag{15.1}
$$

and therefore

$$
\langle\operatorname{res}x,y\rangle_L
=\langle x,\operatorname{cor}y\rangle_K. \tag{15.2}
$$

The dimension formulas are

$$
h^2(M)=h^0(M^*(1)), \tag{15.3}
$$

and

$$
h^1(M)=h^0(M)+h^0(M^*(1))
+\delta_{\ell,p}[K:\mathbf Q_p]\dim M, \tag{15.4}
$$

where the last term occurs only in mixed characteristic with coefficient characteristic $p$.

### 15.3 Normalization ledger for Selmer structures

A Selmer structure on a coefficient module $M$ assigns a subgroup $L_K\subseteq H^1(K,M)$ at each relevant local field. The local input furnished by this book is normalized as follows.

1. Arithmetic Frobenius acts on the residue closure by $x\mapsto x^q$.
2. Arithmetic reciprocity sends a uniformizer to arithmetic Frobenius on the maximal unramified extension.
3. The cyclic algebra $(K_m/K,\varphi,\pi_K)$ has invariant $1/m$.
4. The local pairing is $\operatorname{inv}_K(x\smile y)$, with $x$ written first.
5. The coefficient dual is $M^*(1)=\operatorname{Hom}(M,\mu_n)$, not the untwisted character group.
6. The dual condition is the exact zero locus $L_K^\perp$ under that pairing.
7. Away from the coefficient prime, $H^1_f=H^1_{\mathrm{ur}}$ and $H^1_s=H^1/H^1_f$.
8. At the coefficient prime, the symbol $H^1_f$ carries no meaning until an arithmetic condition is specified and its orthogonal theorem is proved.
9. For $0\to T\to V\to A\to0$, integral conditions are preimages from $V$ and discrete conditions are images from $V$ when propagation is intended.
10. The normalized numerical correction is $\dim L_K-h^0_K(M)$.

Every item affects a later sign, quotient, or dimension. For example, replacing arithmetic reciprocity by its inverse negates all symbol pairings but does not change orthogonal subgroups; replacing $M^*(1)$ by $M^*$ changes the subgroup itself. Replacing a propagated lattice condition by the raw inertia kernel can alter a finite index even when the rational subspace is unchanged.

At finite-field level a trace character is needed to display an $F$-valued pairing, but the subgroup $L_K^\perp$ is independent of that choice. At lattice level the evaluation-dual lattice, including the inverse different for general coefficient rings, is needed for an exact integral statement. At vector-space level commensurable lattices give the same pairing after scalar extension.

### 15.4 Counterexamples that fix the hypotheses

The hypotheses are best remembered through their failures.

* In characteristic $p$, the geometric points of $\mu_p$ are trivial, although $\mu_p$ is the Cartier dual of $\mathbf Z/p\mathbf Z$. The discrete-module Tate dual therefore cannot express the correct $p$-primary theorem.
* For $K=\mathbf F_q((t))$, $H^1(K,\mathbf F_p)$ is infinite. A finite-cardinality Euler product is meaningless even though higher cohomology vanishes.
* At a $p$-adic place containing $\mu_p$, the unramified line in $H^1(K,\mathbf F_p)$ has an annihilator of dimension $[K:\mathbf Q_p]+1$. It is not self-complementary.
* For the quadratic Hilbert symbol with $q\equiv3\pmod4$, the valuation line is not isotropic because $(\pi_K,\pi_K)_2=-1$. Skew-symmetry language at exponent two cannot be replaced by alternation.
* If the coefficient characteristic divides $d$, the trace pairing on $\operatorname{ad}^0$ is degenerate because the identity matrix has trace zero. The usual trace-zero self-duality fails.
* An unramified lattice with Frobenius eigenvalue $\alpha\neq1$ can have the finite group $\mathcal O/(\alpha-1)$ in integral unramified cohomology while its vector-space unramified cohomology is zero. Rational and integral local conditions are not interchangeable.
* If $\ell\mid[L:K]$, restriction can have a kernel and corestriction can fail to be onto. The adjunction formulas remain valid, but injectivity cannot be inferred from them.

Each counterexample singles out a precise repair: retain the full Cartier dual, impose the characteristic range, include the principal-unit term, distinguish alternating from skew-symmetric, use the correct dual quotient, saturate integral conditions, or retain kernel--image formulas.

### 15.5 Boundaries of the dictionary

Three limitations are part of the theorem, not editorial cautions.

First, equal-characteristic $p$-primary Galois modules have no usual root-of-unity Tate twist and can have infinite $H^1$. Second, an integral local condition at $p$ is not automatically the orthogonal of another integral condition merely because the ambient modules are dual; the integral models must supply the containment. Third, perfectness for lattices means Pontryagin duality between compact and discrete groups, not an algebraic isomorphism between two compact cohomology groups.

The local theorem also does not itself assemble conditions over several places. It prepares the exact pieces: a pairing at each place, a rule for orthogonal subgroups, and restriction--corestriction compatibility. The global assembly and its long exact sequences belong to the next stages.

## 16. Conclusion

### 16.1 Detection rather than numerical coincidence

Tate local duality begins with a simple evaluation map and ends with a complete detection theorem. The Tate twist makes evaluation land in roots of unity; cup product moves complementary classes to degree two; the normalized Brauer invariant turns that obstruction into a scalar. Cyclic algebras and local reciprocity prove that Kummer classes and characters detect one another. The local fundamental classes for every subgroup, Tate--Nakayama, and permutation-lattice resolutions carry that detection through arbitrary finite Galois actions. Only after nondegeneracy is established does finiteness turn the adjoint injections into isomorphisms.

The theorem consequently explains every low degree. Fixed vectors are dual to final obstructions, middle-degree torsors pair perfectly with dual torsors, and the vanishing of $H^2$ is the absence of a twisted invariant. It also explains the arithmetic shape of natural conditions: norms are orthogonal to restriction kernels, prime-to-$p$ unramified classes are exact complements, units are orthogonal to unramified characters, and deeper unit groups are dual to conductor bounds.

### 16.2 The reusable local endpoint

At finite level the result is a perfect pairing of finite groups. At lattice level it is a compact--discrete Pontryagin duality. At vector-space level it is a perfect bilinear pairing. These are compatible but not interchangeable. In mixed characteristic the $p$-primary theory includes the principal-unit term; in equal characteristic the ordinary $p$-primary Galois-module formulation is deliberately absent.

For deformation calculations, the final formulas replace the obstruction group $H^2(K,M)$ by the dual of $H^0(K,M^*(1))$ and attach to every tangent subspace an exact dual orthogonal. The local field has therefore supplied not just dimensions but a canonical geometry of allowable and forbidden directions. That geometry is the local input needed when conditions from different places are later compared.
