# Fontaine--Laffaille Modules and Torsion Representations

## Contents

1. [The integral linearization problem](#1-the-integral-linearization-problem)
   - [From a filtered crystal to generic torsion](#11-from-a-filtered-crystal-to-generic-torsion)
   - [Standing hypotheses and conventions](#12-standing-hypotheses-and-conventions)
   - [The boundary of this book](#13-the-boundary-of-this-book)
   - [The route through the argument](#14-the-route-through-the-argument)
2. [Divided filtered modules](#2-divided-filtered-modules)
   - [Why Frobenius must be divided](#21-why-frobenius-must-be-divided)
   - [Free objects of weights zero and one](#22-free-objects-of-weights-zero-and-one)
   - [Normal decompositions](#23-normal-decompositions)
   - [Morphisms and strictness](#24-morphisms-and-strictness)
3. [Torsion objects and their exact structure](#3-torsion-objects-and-their-exact-structure)
   - [Why arbitrary filtered torsion modules are too large](#31-why-arbitrary-filtered-torsion-modules-are-too-large)
   - [Admissible torsion objects](#32-admissible-torsion-objects)
   - [Strict short exact sequences](#33-strict-short-exact-sequences)
   - [Reduction, length, and dévissage](#34-reduction-length-and-dévissage)
4. [The two atomic weights](#4-the-two-atomic-weights)
   - [The weight-zero line](#41-the-weight-zero-line)
   - [The weight-one line](#42-the-weight-one-line)
   - [Unramified factors and extensions](#43-unramified-factors-and-extensions)
   - [The first boundary in the prime](#44-the-first-boundary-in-the-prime)
5. [Crystalline period coefficients](#5-crystalline-period-coefficients)
   - [The geometric period object](#51-the-geometric-period-object)
   - [Filtration and divided Frobenius](#52-filtration-and-divided-frobenius)
   - [The two fundamental sequences](#53-the-two-fundamental-sequences)
   - [Finite levels and continuity](#54-finite-levels-and-continuity)
6. [The syntomic solution functor](#6-the-syntomic-solution-functor)
   - [Filtered Frobenius morphisms as solutions](#61-filtered-frobenius-morphisms-as-solutions)
   - [The Galois action and variance](#62-the-galois-action-and-variance)
   - [Finiteness and the rank calculation](#63-finiteness-and-the-rank-calculation)
   - [The atomic calculations revisited](#64-the-atomic-calculations-revisited)
7. [The small-weight lifting lemma](#7-the-small-weight-lifting-lemma)
   - [Statement of the local lemma](#71-statement-of-the-local-lemma)
   - [Successive approximation](#72-successive-approximation)
   - [Descent of matrices](#73-descent-of-matrices)
   - [Why the weight bound is sharp for the proof](#74-why-the-weight-bound-is-sharp-for-the-proof)
8. [Exactness of the generic realization](#8-exactness-of-the-generic-realization)
   - [The exactness theorem](#81-the-exactness-theorem)
   - [Proof by strict lifting](#82-proof-by-strict-lifting)
   - [Kernels, cokernels, and length](#83-kernels-cokernels-and-length)
   - [A warning about non-strict sequences](#84-a-warning-about-non-strict-sequences)
9. [Full faithfulness](#9-full-faithfulness)
   - [The comparison map on morphisms](#91-the-comparison-map-on-morphisms)
   - [Integral reconstruction](#92-integral-reconstruction)
   - [The full-faithfulness theorem](#93-the-full-faithfulness-theorem)
   - [Subrepresentations and what is not yet proved](#94-subrepresentations-and-what-is-not-yet-proved)
10. [Duality and Tate twist](#10-duality-and-tate-twist)
    - [The filtered Cartier dual](#101-the-filtered-cartier-dual)
    - [Constructing the divided Frobenius on the dual](#102-constructing-the-divided-frobenius-on-the-dual)
    - [Compatibility with generic duality](#103-compatibility-with-generic-duality)
    - [Perfect pairings and adjoints](#104-perfect-pairings-and-adjoints)
11. [Geometry in degree one](#11-geometry-in-degree-one)
    - [Hodge and crystalline input](#111-hodge-and-crystalline-input)
    - [Abelian torsion](#112-abelian-torsion)
    - [Ordinary and local--local examples](#113-ordinary-and-local--local-examples)
    - [Polarizations](#114-polarizations)
12. [Coefficients and change of ground field](#12-coefficients-and-change-of-ground-field)
    - [Commuting coefficient actions](#121-commuting-coefficient-actions)
    - [Scalar extension of coefficients](#122-scalar-extension-of-coefficients)
    - [Unramified extension of the ground field](#123-unramified-extension-of-the-ground-field)
    - [Statements deliberately not inferred](#124-statements-deliberately-not-inferred)
13. [A theorem and hypothesis ledger](#13-a-theorem-and-hypothesis-ledger)
    - [The main package](#131-the-main-package)
    - [Dependency closure](#132-dependency-closure)
    - [Failure modes](#133-failure-modes)
14. [Conclusion](#14-conclusion)

## 1. The integral linearization problem

Crystalline cohomology produces a lattice with two structures that pull in opposite directions. Its Hodge filtration records how a class lifts through differential forms, while Frobenius records arithmetic on the special fiber. Generic Galois cohomology, by contrast, sees a finite discrete module on which the absolute Galois group acts. The purpose of this book is to pass from the first kind of object to the second without inverting $p$ and without forgetting the filtration.

### 1.1 From a filtered crystal to generic torsion

The essential local phenomenon already appears in degree one. Let $k$ be perfect of characteristic $p$, let $W=W(k)$, and let $K_0=W[1/p]$. A good-reduction geometric object over $W$ supplies a finite free module $M$ with a decreasing Hodge filtration and a semilinear crystalline Frobenius. On the first filtered step Frobenius is divisible by $p$. Thus one has two integral operators,

$$
\varphi _0:M\longrightarrow M,
\qquad
\varphi _1:\operatorname{Fil}^1M\longrightarrow M,
\qquad
\varphi _0|_{\operatorname{Fil}^1M}=p\varphi _1.
$$

The divided operator $\varphi _1$ is not auxiliary notation. It remembers an integral quotient which cannot be recovered from $\varphi _0$ after reducing modulo $p^n$. The pair of operators, together with the requirement that their images generate $M$, is the algebraic core of a Fontaine--Laffaille module in weights zero and one.

The generic realization will be constructed as a space of filtered Frobenius-compatible maps into crystalline period coefficients. This is a syntomic fixed-point construction: in weight zero it solves $1-\varphi$, while in weight one it solves $1-\varphi _1$. Book 55 proved the two fundamental exact sequences underlying those equations. Here they are assembled with an arbitrary divided filtered module, and the resulting solutions are shown to be exact and fully faithful.

### 1.2 Standing hypotheses and conventions

Throughout the book, unless a statement explicitly says otherwise,

$$
p>2,
\qquad k\text{ is a perfect field of characteristic }p,
\qquad W=W(k),
\qquad K_0=W[1/p].
\tag{1.1}
$$

The Witt Frobenius is $\sigma$. Fix an algebraic closure $\overline K_0$ and put

$$
G_{K_0}=\operatorname{Gal}(\overline K_0/K_0).
$$

All Galois modules are finite discrete $p$-primary modules with continuous action. Continuity means that every element has an open stabilizer. A semilinear map $f$ satisfies $f(am)=\sigma(a)f(m)$.

Filtrations are decreasing. Our weight interval is $[0,1]$:

$$
\operatorname{Fil}^0M=M,
\qquad \operatorname{Fil}^2M=0.
\tag{1.2}
$$

We use the contravariant realization

$$
T_{\mathrm{FL}}(M)
=\operatorname{Hom}_{\mathrm{Fil},\varphi}(M,\mathscr A_{\mathrm{cris},\infty}).
\tag{1.3}
$$

Thus a morphism $M\to N$ induces $T_{\mathrm{FL}}(N)\to T_{\mathrm{FL}}(M)$. The normalization is chosen so that the weight-zero line realizes $\mathbf Z_p$ and the weight-one line realizes $\mathbf Z_p(1)=\varprojlim\mu_{p^n}$. It agrees with the covariant Tate-twist convention of Book 55 and with the contravariant Dieudonné convention of Book 57. Consequently, if a finite-flat group is sent contravariantly to a divided filtered module and that module is sent contravariantly to a Galois module, the composite has the usual covariance of geometric points.

### 1.3 The boundary of this book

Several nearby assertions belong to the next stage of the theory and are not smuggled into the arguments here. We prove that the syntomic realization of an admissible torsion divided filtered module is exact, duality-compatible, and fully faithful. We do not prove that every divided filtered module comes from a finite-flat group scheme, nor that every finite-flat torsion representation in the relevant range comes from such a module. We also do not prove the integral base-change and compatible-quotient theorem for stable lattices. Those are essential-surjectivity statements, not consequences of full faithfulness.

The base $W(k)$ is unramified. Over a ramified discrete valuation ring the divisibility of Frobenius is measured against the ramification index and the clean category below is no longer adequate without additional structure. Semistable objects require monodromy and logarithmic geometry. Neither generalization is asserted.

The inequality $1\le p-2$ explains the assumption $p>2$. At $p=2$, a module with weights $0$ and $1$ lies at the first forbidden boundary of the elementary Fontaine--Laffaille argument. Book 55 can still form its modified weight-one syntomic complex, but that fact alone does not give the full-faithfulness theorem proved here.

### 1.4 The route through the argument

The proof has three layers. First, Chapters 2--4 build the exact category of divided filtered modules and identify its two atomic lines. Second, Chapters 5--8 use crystalline period coefficients and the low-weight lifting lemma to construct an exact generic realization. Third, Chapters 9--12 reconstruct morphisms, establish duality, compare with degree-one geometry, and isolate safe coefficient and base-change statements.

The central chain is

$$
\text{Hodge filtration plus divided Frobenius}
\longrightarrow
\text{syntomic solutions}
\longrightarrow
\text{finite }G_{K_0}\text{-module}.
\tag{1.4}
$$

Every difficult point is integral: strictness of filtrations, division by $p$, lifting across a torsion quotient, and descent of a Galois-equivariant matrix. Once those four points are controlled, exactness and full faithfulness follow with no appeal to a classification theorem.

## 2. Divided filtered modules

A rational filtered Frobenius module records only subspaces and an invertible semilinear map. Integral arithmetic requires more: it must specify exactly where Frobenius is divisible by $p$. This chapter turns that divisibility into part of the object and proves the normal-decomposition lemma used in every later calculation.

### 2.1 Why Frobenius must be divided

Suppose $M$ is finite free over $W$ and $F\subset M$ is intended to be the first Hodge step. Knowing that a semilinear map $\varphi _0$ carries $F$ into $pM$ permits a unique quotient $\varphi _1=\varphi _0/p$ because $M$ is $p$-torsion-free. After passing to $M/p^nM$, however, the equation $px=y$ no longer determines $x$. Therefore a torsion theory cannot define $\varphi _1$ by division after reduction; $\varphi _1$ must be retained before reduction and transported as structure.

The second condition is generation. If the images of $\varphi _0$ and $\varphi _1$ lie in a proper direct summand, the corresponding fixed-point equations have too few solutions. Strong divisibility says precisely that no such loss occurs.

### 2.2 Free objects of weights zero and one

A **free divided filtered module of weights $[0,1]$** is a quadruple

$$
M=(M,F,\varphi _0,\varphi _1)
\tag{2.1}
$$

with the following properties.

1. $M$ is a finite free $W$-module.
2. $F=\operatorname{Fil}^1M$ is a direct summand of $M$; set $\operatorname{Fil}^0M=M$ and $\operatorname{Fil}^2M=0$.
3. The maps $\varphi _0:M\to M$ and $\varphi _1:F\to M$ are $\sigma$-semilinear.
4. On $F$ one has

   $$
   \varphi _0=p\varphi _1.
   \tag{2.2}
   $$

5. The $W$-span of $\varphi _0(M)$ and $\varphi _1(F)$ is all of $M$.

Condition 5 is called **strong divisibility**. Since $\varphi _0(F)$ is already contained in the span of $\varphi _1(F)$, it can equivalently be written

$$
M=W\varphi _0(C)+W\varphi _1(F)
\tag{2.3}
$$

for one, and hence every, complement $M=C\oplus F$.

It is useful to package semilinearity by linearization. For a $W$-module $P$, let $\sigma^*P=W\otimes_{\sigma,W}P$. A semilinear map $f:P\to M$ corresponds to a linear map $f^{\mathrm{lin}}:\sigma^*P\to M$.

### 2.3 Normal decompositions

The filtration gives a direct decomposition, but strong divisibility says something more precise about Frobenius.

**Proposition 2.1 (normal decomposition).** Let $M$ be a free divided filtered module and choose a complement $M=C\oplus F$. The map

$$
\Psi_M:\sigma^*C\oplus\sigma^*F\longrightarrow M,
\qquad
(c,f)\longmapsto\varphi _0(c)+\varphi _1(f),
\tag{2.4}
$$

is an isomorphism. Conversely, a finite free $M=C\oplus F$ together with a semilinear map (2.4) whose linearization is an isomorphism determines a unique free divided filtered module by setting $\varphi _1$ on $F$ equal to the second component and setting $\varphi _0|_F=p\varphi _1$.

**Proof strategy.** Generation gives surjectivity. Since source and target have the same finite rank over the local ring $W$, reduction modulo $p$ turns surjectivity into an isomorphism, and Nakayama lifts it.

**Proof.** Condition (2.3) says exactly that $\Psi_M$ is surjective. Both source and target are finite free of rank $\operatorname{rank}_WM$. Reducing modulo $p$ gives a surjective endomorphism between $k$-vector spaces of equal dimension, hence an isomorphism. The determinant of $\Psi_M$ is therefore a unit of $W$, proving that $\Psi_M$ is an isomorphism.

Conversely, define $F$ as the first filtered step, define $\varphi _0$ and $\varphi _1$ as stated, and observe that (2.2) holds by construction. The image of (2.4) is $M$, so strong divisibility follows. Uniqueness is immediate. $\square$

The ranks

$$
h^0(M)=\operatorname{rank}_W(M/F),
\qquad
h^1(M)=\operatorname{rank}_WF
\tag{2.5}
$$

are the Hodge numbers. They do not depend on the chosen complement. Proposition 2.1 says that the divided Frobenius has exactly $h^0+h^1$ independent output directions.

### 2.4 Morphisms and strictness

A morphism $u:M\to N$ is a $W$-linear map satisfying

$$
u(F_M)\subseteq F_N,
\qquad
u\varphi _0=\varphi _0u,
\qquad
u\varphi _1=\varphi _1u|_{F_M}.
\tag{2.6}
$$

It is **strict for the filtration** if

$$
u(F_M)=u(M)\cap F_N.
\tag{2.7}
$$

Strictness is automatic for an isomorphism but not for an arbitrary injection. For example, the inclusion $pM\hookrightarrow M$ is filtration-preserving; after identifying $pM$ abstractly with $M$, it is strict only when its first filtered step is chosen as the preimage of $F_M$, not when a larger submodule is assigned. This distinction is the source of many false torsion exactness claims.

Composition preserves strictness when one map is a strict epimorphism or the other a strict monomorphism in a short exact filtered sequence. Direct sums, tensor products in a range whose weights remain defined, and reduction modulo $p^n$ preserve the equations (2.2) and (2.6). Duality is subtler and will be constructed in Chapter 10.

## 3. Torsion objects and their exact structure

The generic representations of interest are killed by powers of $p$, so free lattices are only the starting point. An arbitrary finite-length module with an arbitrary submodule called a filtration is too permissive: divided Frobenius can acquire artificial quotients and strict lifting can fail. We therefore define the torsion category by integral presentations.

### 3.1 Why arbitrary filtered torsion modules are too large

Let $Q=W/p^2$ and give it the submodule $F=pQ$. A semilinear map on $F$ may be altered by an arbitrary element killed by $p$ without changing $p\varphi _1$. Hence the relation $\varphi _0|_F=p\varphi _1$ does not control the divided operator. Worse, if one takes a quotient of filtered modules and defines the quotient filtration by intersection rather than image, the underlying module sequence may be exact while the filtered sequence is not.

The correct torsion objects are those whose filtration and divided operators descend from a strict integral presentation. This retains the information which reduction alone forgets.

### 3.2 Admissible torsion objects

An **admissible torsion divided filtered module of weights $[0,1]$** is a finite-length $W$-module $M$ with $F_M$, $\varphi _0$, and $\varphi _1$ which admits a presentation

$$
0\longrightarrow L_1\xrightarrow{a}L_0\longrightarrow M\longrightarrow0
\tag{3.1}
$$

such that $L_0,L_1$ are free divided filtered modules, $a$ is an injective strict morphism, and the filtration and both divided Frobenius maps on $M$ are the quotient structures. Thus

$$
F_M=F_{L_0}/a(F_{L_1}).
\tag{3.2}
$$

Two presentations define the same object when they induce the same displayed structure on $M$; no presentation is retained as part of the datum.

Every quotient $L/p^nL$ of a free object is admissible, using multiplication by $p^n$ in (3.1). More generally, different elementary divisors are allowed. The presentation definition is stable under finite direct sums and under strict extensions: one lifts an extension to presentations, takes the fiber product over its quotient, and uses the horseshoe construction. Because the filtrations are direct summands on the free terms and all arrows are strict, the lifted sequence remains exact on $F$.

### 3.3 Strict short exact sequences

A sequence

$$
0\longrightarrow M'\xrightarrow{i}M\xrightarrow{q}M''\longrightarrow0
\tag{3.3}
$$

of admissible torsion objects is **admissibly exact** if it is exact as a sequence of $W$-modules, all maps commute with the divided filtered structures, and

$$
0\longrightarrow F_{M'}\xrightarrow{i}F_M\xrightarrow{q}F_{M''}\longrightarrow0
\tag{3.4}
$$

is exact. Equivalently, $i$ and $q$ are strict. These sequences make the category an exact category.

**Proposition 3.1.** Pullbacks of admissible epimorphisms and pushouts of admissible monomorphisms exist and are admissibly exact. The resulting objects are admissible torsion divided filtered modules.

**Proof.** Form the pullback or pushout on underlying $W$-modules and do the same on the first filtered steps. Exactness of (3.4) identifies the filtered step of the new module with the corresponding fiber product or pushout; thus no intersection--image discrepancy occurs. Lift the original objects and maps to strict free presentations. The ordinary horseshoe diagram gives a two-term free presentation of the new module. Applying the same diagram to the direct-summand filtrations proves strictness, while functoriality of $\varphi _0$ and $\varphi _1$ descends their relations. Hence the new object is admissible. $\square$

### 3.4 Reduction, length, and dévissage

If $L$ is free, then $L_n=L/p^nL$ has

$$
F_{L_n}=(F_L+p^nL)/p^nL,
\tag{3.5}
$$

not an independently chosen submodule. Both divided Frobenius maps reduce because they were present on $L$ before quotienting. Multiplication by $p$ gives admissibly exact sequences

$$
0\longrightarrow L/p^mL
\xrightarrow{p^n}L/p^{m+n}L
\longrightarrow L/p^nL\longrightarrow0.
\tag{3.6}
$$

For a finite-length $W$-module, write $\ell_W(M)$ for its length. Any admissible object has a finite filtration by the kernels of powers of $p$; strictness follows from a free presentation. Its successive quotients are killed by $p$. This dévissage will reduce rank and exactness calculations to level one, but it does not say that the category is semisimple. Extensions between the two weights carry genuine arithmetic information.

## 4. The two atomic weights

The names “weight zero” and “weight one” are fixed by two rank-one objects. Their calculation determines the Tate-twist convention, clarifies variance, and shows why both weights must be kept even before nontrivial extensions are considered.

### 4.1 The weight-zero line

Let $\mathbf 1$ be the free rank-one object $We_0$ with

$$
F_{\mathbf1}=0,
\qquad
\varphi _0(ae_0)=\sigma(a)e_0.
\tag{4.1}
$$

Strong divisibility is immediate. Its reduction $\mathbf1_n=\mathbf1/p^n$ is the weight-zero torsion line. A filtered Frobenius map from $\mathbf1_n$ to period coefficients is determined by an element fixed by ordinary Frobenius. The weight-zero fundamental sequence will identify these elements with $\mathbf Z/p^n$.

More generally, if $F_M=0$, Proposition 2.1 says that $\varphi _0^{\mathrm{lin}}:\sigma^*M\to M$ is an isomorphism. Such an object is a unit-root divided filtered module. Its generic realization is unramified in the sense that inertia acts through the coefficient descent attached to the Frobenius equation. No scalar formula for arithmetic versus geometric Frobenius will be used without stating that normalization.

### 4.2 The weight-one line

Let $\mathbf1(1)$ be $We_1$ with

$$
F_{\mathbf1(1)}=We_1,
\qquad
\varphi _1(ae_1)=\sigma(a)e_1,
\qquad
\varphi _0=p\varphi _1.
\tag{4.2}
$$

Its level-$n$ quotient is denoted $\mathbf1_n(1)$. A morphism to period coefficients now lands in the first filtration and is fixed by divided Frobenius. The weight-one fundamental sequence identifies its solutions with $\mu_{p^n}$, so

$$
T_{\mathrm{FL}}(\mathbf1_n(1))\simeq\mu_{p^n}(\overline K_0).
\tag{4.3}
$$

This equation fixes the twist: weight one realizes the cyclotomic character, not its inverse.

### 4.3 Unramified factors and extensions

Suppose $M=We_0\oplus We_1$, $F=We_1$, and

$$
\varphi _1(e_1)=e_1,
\qquad
\varphi _0(e_0)=e_0+c e_1,
\qquad c\in W.
\tag{4.4}
$$

Together with $\varphi _0(e_1)=pe_1$, this is strongly divisible: the two displayed images form a basis. It is an extension of the weight-zero and weight-one lines in the divided filtered category. Changing $e_0$ by $be_1$ alters $c$ by the corresponding semilinear coboundary, so the parameter itself is not an invariant; its class modulo those changes is.

After applying the contravariant functor, the order of an extension reverses. Thus the realization of a divided filtered extension must be read from the exact sequence, not guessed from the order of the chosen basis. This elementary example will later serve as a check on exactness and duality.

### 4.4 The first boundary in the prime

The general Fontaine--Laffaille small-weight argument works in an interval of length at most $p-2$. Our interval has length one, so $p>2$ is exactly what places it inside that safe range. At $p=2$ the two atomic equations of Book 55 still make sense individually, and the modified first filtration makes division by $2$ well defined. What fails is the mixed matrix estimate used to reconstruct an arbitrary extension: an error of filtration degree one is no longer forced into a strictly deeper $2$-adic neighborhood. We therefore make no $p=2$ full-faithfulness claim.

## 5. Crystalline period coefficients

The target of the realization must simultaneously contain divided-power infinitesimals, a filtration, Frobenius, and a Galois action. Only then can a filtered Frobenius morphism be interpreted as a generic Galois vector. Book 53 constructed the divided-power machinery, and Book 55 proved the local low-weight fixed-point sequences. We now recall their exact form at a geometric point and record the properties needed below.

### 5.1 The geometric period object

Let $\mathcal O_{\overline K_0}$ be the integral closure of $W$ in $\overline K_0$, and let $\widehat{\mathcal O}_{\overline K_0}$ be its $p$-adic completion. The compatible system of crystalline divided-power envelopes of

$$
\mathcal O_{\overline K_0}/p^n
$$

over $W/p^n$ gives a $p$-adically complete crystalline period object $\mathscr A_{\mathrm{cris}}$. It may equivalently be obtained by completing the universal divided-power thickening of the canonical map from the Witt vectors of the tilt to $\widehat{\mathcal O}_{\overline K_0}$. The universal description shows that it is independent of coordinates.

It carries:

- a continuous action of $G_{K_0}$;
- a decreasing divided-power filtration $\operatorname{Fil}^i\mathscr A_{\mathrm{cris}}$;
- a Frobenius $\varphi$ commuting with Galois;
- a divided map $\varphi _1=\varphi/p$ on $\operatorname{Fil}^1$.

The last quotient is integral. Locally, if $x$ lies in the defining ideal, then

$$
\varphi(x)=x^p+pa
=p\bigl((p-1)!x^{[p]}+a\bigr).
\tag{5.1}
$$

The same divided-power calculation handles sums and completed limits. At finite level one uses the modified filtration of Book 55, so division is independent of a lift.

For torsion realizations set

$$
\mathscr A_{\mathrm{cris},\infty}
=\mathscr A_{\mathrm{cris}}[1/p]/\mathscr A_{\mathrm{cris}}.
\tag{5.2}
$$

Its filtration is the image filtration, with the finite-level modification implicit before division by $p$. Every element is killed by a power of $p$, and all structures commute with passage to the $p^n$-torsion subgroup.

### 5.2 Filtration and divided Frobenius

The period object is a divided filtered coefficient object in every nonnegative weight. In the present book only the relations

$$
\varphi(\operatorname{Fil}^1)\subset p\mathscr A_{\mathrm{cris}},
\qquad
\varphi _0|_{\operatorname{Fil}^1}=p\varphi _1
\tag{5.3}
$$

are used. A $W$-linear map $f:M\to\mathscr A_{\mathrm{cris},\infty}$ is a morphism of divided filtered objects when

$$
f(F_M)\subseteq\operatorname{Fil}^1,
\qquad
f\varphi _0=\varphi f,
\qquad
f\varphi _1=\varphi _1f|_{F_M}.
\tag{5.4}
$$

The second equality restricted to $F_M$ follows from the third after multiplication by $p$, but in a torsion target it is safer to retain both; cancellation of $p$ is not legitimate.

Choose a compatible system of $p$-power roots of unity and let $t$ be its divided-power logarithmic period. Then

$$
t\in\operatorname{Fil}^1\mathscr A_{\mathrm{cris}},
\qquad \varphi(t)=pt.
$$

Changing the compatible system multiplies $t$ by a unit and does not change any descent statement. The total period algebra

$$
\mathscr B_{\mathrm{cris}}
=\mathscr A_{\mathrm{cris}}[1/p,1/t]
$$

is used only to invert evaluation matrices. All descended morphisms and all realized torsion groups remain integral; inverting $t$ is a proof device, not part of the definition (6.1).

### 5.3 The two fundamental sequences

At every finite level $n\ge1$, the local calculation of Book 55 gives exact sequences on the small syntomic site and hence on the geometric stalk:

$$
0\longrightarrow\mathbf Z/p^n
\longrightarrow\mathscr A_n
\xrightarrow{1-\varphi}\mathscr A_n
\longrightarrow0,
\tag{5.5}
$$

and

$$
0\longrightarrow\mu_{p^n}
\longrightarrow\operatorname{Fil}^1\mathscr A_n
\xrightarrow{1-\varphi _1}\mathscr A_n
\longrightarrow0.
\tag{5.6}
$$

In (5.6), a root of unity is sent by the divided-power logarithm to its filtered period. Exactness on the right is local for the syntomic topology. The proof solves the Frobenius-difference equation successively; its linear term has derivative one, and the divided-power filtration makes the correction converge. These are not merely rational exact sequences.

The injections identify the kernels with the indicated finite-flat coefficients. In particular, (5.5) and (5.6) are $G_{K_0}$-equivariant. They are the rank-one cases of the lifting lemma in Chapter 7.

### 5.4 Finite levels and continuity

The transition maps $\mathscr A_{n+1}\to\mathscr A_n$ are surjective on the relevant modified filtered terms. Consequently compatible solutions form inverse systems without a hidden choice of divided Frobenius. A solution killed by $p^n$ is defined over a finite syntomic extension of a finite level, so its stabilizer in $G_{K_0}$ is open. Hence every realization constructed from these coefficients is a continuous discrete representation.

One must distinguish finite-level reduction from naive reduction of a completed fixed-point group. Fixed points need not commute with tensor product because they are kernels of $1-\varphi_i$. The correct finite-level object is the $p^n$-torsion in (5.2), equipped with the modified filtration inherited from the compatible crystalline levels. This distinction will also govern base change in Chapter 12.

## 6. The syntomic solution functor

We can now turn a divided filtered module into a Galois module. The definition is short, but its consequences are not formal: finiteness uses the normal decomposition, exactness uses strict lifting, and full faithfulness uses integral descent. This chapter establishes the definition and the first size calculation.

### 6.1 Filtered Frobenius morphisms as solutions

For an admissible torsion divided filtered module $M$, define

$$
T_{\mathrm{FL}}(M)
=\operatorname{Hom}_{\mathrm{Fil},\varphi}
(M,\mathscr A_{\mathrm{cris},\infty}).
\tag{6.1}
$$

If $p^nM=0$, the image of every map lies in the $p^n$-torsion of the period object. Thus (6.1) is computed at a finite level. It is an abelian group under pointwise addition and is killed by $p^n$.

The description as a syntomic solution becomes explicit after choosing a normal decomposition $M=C\oplus F$. A map $f$ is determined by its values on bases of $C$ and $F$. Filtration requires the values on $F$ to lie in $\operatorname{Fil}^1$, and Frobenius compatibility gives the vector equations

$$
\varphi(f(c))=f(\varphi _0(c)),
\qquad
\varphi _1(f(f_1))=f(\varphi _1(f_1)).
\tag{6.2}
$$

The same letter $f$ occurs as the morphism and, temporarily, as an element $f_1\in F$; the equations are type-correct because the left sides use the period operators and the right sides use the divided filtered operators on $M$. In matrix form, (6.2) is a coupled system built from the two rank-one maps $1-\varphi$ and $1-\varphi _1$.

### 6.2 The Galois action and variance

Because the Galois action on the period object commutes with its filtration and Frobenius, define

$$
(g\cdot f)(m)=g(f(m)).
\tag{6.3}
$$

This preserves (5.4), so $T_{\mathrm{FL}}(M)$ is a $G_{K_0}$-module. Section 5.4 proves continuity.

For a morphism $u:M\to N$, precomposition gives

$$
T_{\mathrm{FL}}(u):T_{\mathrm{FL}}(N)\longrightarrow
T_{\mathrm{FL}}(M),
\qquad h\longmapsto h\circ u.
\tag{6.4}
$$

Thus $T_{\mathrm{FL}}$ is contravariant. If

$$
0\to M'\to M\to M''\to0
$$

is admissibly exact, left exactness of Hom gives

$$
0\to T_{\mathrm{FL}}(M'')\to T_{\mathrm{FL}}(M)
\to T_{\mathrm{FL}}(M').
\tag{6.5}
$$

Surjectivity of the last arrow is the substantive part of exactness and will be proved in Chapter 8.

### 6.3 Finiteness and the rank calculation

The number of solutions is controlled by the total $W$-length of $M$, not separately by its Hodge numbers.

**Proposition 6.1.** For every admissible torsion object $M$, $T_{\mathrm{FL}}(M)$ is a finite abelian $p$-group and

$$
\ell_{\mathbf Z_p}T_{\mathrm{FL}}(M)=\ell_W(M).
\tag{6.6}
$$

In particular, if $L$ is free of rank $d$, then

$$
T_{\mathrm{FL}}(L/p^nL)
$$

is a free $\mathbf Z/p^n$-module of rank $d$.

**Proof strategy.** At level one, a normal decomposition turns the solution space into the kernel of a syntomic map of $d$-dimensional additive groups. Its linearized Frobenius term has full rank, so the kernel is finite flat of rank $p^d$ on the generic stalk. Higher levels follow by lifting one $p$-adic digit at a time. General finite-length objects follow from a strict free presentation and the lifting argument proved in Chapter 7. We include the calculation now and isolate the lifting input there.

**Proof.** Let $L=C\oplus F$ be free of rank $d$. Modulo $p$, Proposition 2.1 makes the output matrix of $\varphi _0|_C$ and $\varphi _1|_F$ invertible. Equations (6.2), together with (5.5) and (5.6), therefore define locally a torsor under a kernel with $p^d$ geometric elements. Starting with a solution modulo $p^m$, the error modulo $p^{m+1}$ is a level-one vector equation with the same invertible output matrix. The fundamental sequences solve it syntomically, and its homogeneous solutions form $(\mathbf Z/p)^d$. Induction gives exactly $p^{nd}$ solutions modulo $p^n$ and shows that multiplication by $p$ has kernel and cokernel of the expected size. Hence the solution group is free of rank $d$ over $\mathbf Z/p^n$.

For a general $M$, choose a strict presentation (3.1). The relative lifting statement of Theorem 7.1 makes the induced sequence of solution groups exact. Applying the already established free calculation to $L_0$ and $L_1$ gives

$$
\ell_{\mathbf Z_p}T(M)
=\ell_{\mathbf Z_p}T(L_0/aL_1)
=\ell_W(L_0/aL_1)=\ell_W(M).
$$

Finiteness follows from the equality of finite lengths. $\square$

The use of Theorem 7.1 is forward only in exposition, not circular in proof: that theorem is proved directly from the period equations, without Proposition 6.1.

### 6.4 The atomic calculations revisited

For the two lines, (6.1) and the fundamental sequences give canonical identifications

$$
T_{\mathrm{FL}}(\mathbf1_n)=\mathbf Z/p^n,
\qquad
T_{\mathrm{FL}}(\mathbf1_n(1))=\mu_{p^n}(\overline K_0).
\tag{6.7}
$$

The first has trivial action. The second has the cyclotomic action. If $M$ is a direct sum of the two lines, its realization is the corresponding direct sum. For a nonsplit extension such as (4.4), the solution equations are coupled by $c$; exactness will show that its realization is an extension with the reversed order, and full faithfulness will show that the coupling cannot disappear generically.

## 7. The small-weight lifting lemma

Every major theorem in this book rests on one local fact: a partial filtered Frobenius solution can be lifted across a strict quotient, and a Galois-invariant map between solution spaces descends to an integral filtered Frobenius matrix. Both assertions fail if filtration and $p$-adic error do not improve together. The interval $[0,1]$ with $p>2$ supplies exactly that improvement.

### 7.1 Statement of the local lemma

Write $\mathscr A_\infty=\mathscr A_{\mathrm{cris},\infty}$. The following is the integral engine of the theory.

**Theorem 7.1 (small-weight lifting and descent lemma).** Assume (1.1). In the exact category of admissible torsion divided filtered modules of weights $[0,1]$:

1. If $M\twoheadrightarrow Q$ is an admissible epimorphism, every filtered Frobenius map from its kernel to $\mathscr A_\infty$ extends to $M$ after solving a syntomic-local equation. On a geometric stalk the extension exists.
2. If $M$ and $N$ are admissible torsion objects, every $G_{K_0}$-equivariant homomorphism

   $$
   T_{\mathrm{FL}}(N)\longrightarrow T_{\mathrm{FL}}(M)
   \tag{7.1}
   $$

   is induced by at most one $W$-linear filtered Frobenius map $M\to N$.
3. After choosing strict free presentations, the coefficient matrix of (7.1) descends to $W/p^n$ at every common annihilating level $p^n$ and satisfies the filtration and divided-Frobenius equations. Hence it is induced by such a map.

Parts 2 and 3 are separated to emphasize uniqueness and existence. Together they are the matrix form of period descent.

Before proving the theorem, we record the local vector calculation which prevents any circular use of the later rank theorem. Let $L=C\oplus F$ be free of rank $d$ and let $U$ be its normal Frobenius matrix. Work first modulo $p$. Choose additive crystalline coordinates for the weight-zero entries and divided-power logarithmic coordinates for the weight-one entries. In these coordinates the coupled solution equation has the form

$$
\mathcal L_U(z)=z-Uz^{(p)}-b=0
\tag{7.2}
$$

after an invertible linear change of variables. Here $z^{(p)}$ means coordinatewise $p$th power, with the Witt-semilinear coefficient action included in $U$. The Jacobian matrix of $\mathcal L_U$ is the identity because the differential of $z\mapsto z^p$ is zero in characteristic $p$. Its highest additive term has invertible matrix $U$, so the coordinate algebra is finite free of rank $p^d$: eliminate the variables successively after triangularizing $U$ over a faithfully flat extension, or observe that the monomials

$$
z_1^{a_1}\cdots z_d^{a_d},
\qquad 0\le a_i<p,
\tag{7.3}
$$

span and remain linearly independent by the highest-term filtration. Thus $\mathcal L_U$ is finite étale of degree $p^d$. Its geometric fiber is a torsor under its homogeneous kernel, a $d$-dimensional $\mathbf F_p$-vector space.

At level $p^n$, lift a solution modulo $p^r$ by writing $z'=z+p^rw$. Substitution and division of the error by $p^r$ reduce the new equation for $w$ to (7.2) modulo $p$. The weight-one entries use $\varphi_1$ before reduction, so no cancellation in a torsion ring occurs. Induction shows that the solution sheaf is finite locally free of rank $p^{nd}$ and is locally a free $\mathbf Z/p^n$-module of rank $d$. In particular, after a syntomic cover it admits a solution basis. The determinant of its evaluation matrix is $t^{h^1(L)}$ times a unit in the total period algebra, so the matrix becomes invertible in $\mathscr B_{\mathrm{cris}}$. This conclusion comes directly from (7.2), (5.5), and (5.6), not from Proposition 6.1.

### 7.2 Successive approximation

We prove the lifting assertion first. Consider an admissibly exact sequence

$$
0\to M'\xrightarrow{i}M\xrightarrow{q}M''\to0
\tag{7.4}
$$

and a solution $f':M'\to\mathscr A_\infty$. Choose strict free presentations and normal decompositions. It is enough to work modulo a common $p^n$ and then pass through the presentations.

Choose an arbitrary $W$-linear extension $f_0$ of $f'$ whose restriction to $F_M$ lands in $\operatorname{Fil}^1$. Such an extension exists because strictness makes

$$
0\to F_{M'}\to F_M\to F_{M''}\to0
$$

exact: extend independently on a complement of $F_{M'}$ in a lifted filtered presentation and on a complement of $M'$ compatible with the quotient. The map $f_0$ need not commute with Frobenius. Its defects are

$$
\delta _0(c)=\varphi(f_0(c))-f_0(\varphi _0c),
\qquad
\delta _1(x)=\varphi _1(f_0(x))-f_0(\varphi _1x).
\tag{7.5}
$$

They vanish on $M'$ and therefore factor through $M''$. We seek a correction $h$ vanishing on $M'$ such that $f_0+h$ has zero defect. In a normal decomposition of $M''$, this is a vector Frobenius-difference equation. Modulo $p$, the output matrix is invertible by Proposition 2.1. The two components are precisely of the forms in (5.5) and (5.6), so a correction exists on the geometric syntomic stalk.

Suppose inductively that the defect vanishes modulo $p^r$. Divide the defect by $p^r$ and reduce modulo $p$. The same level-one equation produces a correction $p^rh_r$. On the filtered component, (5.1) shows that applying $\varphi$ gains the required factor of $p$ before $\varphi _1$ is formed. The new error is divisible by $p^{r+1}$. Iterating to $r=n$ gives an exact solution modulo $p^n$.

Why does a correction not destroy the equation already solved in the other weight? With weights $0$ and $1$, the off-diagonal term crosses the filtration at most once. Such a crossing contributes a factor of $p$, while the divided Frobenius removes at most one factor. Since $p>2$ places the interval in the range $1\le p-2$, the remaining divided-power terms have strictly higher $p$-adic or PD order. Thus the alternating corrections converge and terminate at finite level. This proves Part 1.

### 7.3 Descent of matrices

We next reconstruct a map from (7.1). Choose a common level $p^n$ and strict free presentations of $M$ and $N$. Choose normal decompositions and bases. Evaluation of all syntomic solutions gives period matrices

$$
X_M\in\operatorname{Mat}_{d_M}(\mathscr B_{\mathrm{cris}}),
\qquad
X_N\in\operatorname{Mat}_{d_N}(\mathscr B_{\mathrm{cris}}),
\tag{7.6}
$$

whose rows record bases of the solution modules after a syntomic cover; compatible representatives of the torsion entries are chosen before passing to the total period algebra. Their determinants are $t^{h^1}$ times units because the normal Frobenius matrices are invertible and the homogeneous level-one solution group has full rank. Thus they are invertible in $\mathscr B_{\mathrm{cris}}$.

A homomorphism $\alpha:T(N)\to T(M)$ is represented in these solution bases by a matrix $A$ with entries in $\mathbf Z/p^n$: its rows express the images of the chosen basis of $T(N)$ in the chosen basis of $T(M)$. If $B$ is the desired matrix $M\to N$, precomposition says $X_NB=AX_M$. Thus transporting $\alpha$ back across evaluation gives

$$
B=X_N^{-1} A X_M.
\tag{7.7}
$$

Although the individual period matrices live after a syntomic extension, $G_{K_0}$-equivariance of $\alpha$ makes $B$ invariant under descent. We now show that its entries lie in $W/p^n$ and that it respects all structure.

Normalize each block of $B$ by the power of $t$ dictated by the difference of its source and target weights. The requirement that the resulting map preserve filtration says that no negative power remains, so the normalized blocks lie in the integral period lattice and may be reduced modulo $p$. The weight-zero invariant calculation in (5.5) says that an invariant coefficient whose Frobenius defect is zero is constant. On a coefficient carrying one filtered input, (5.6) says that the only additional invariant is the weight-one root coordinate, and the condition that $B$ map $F_M$ into $F_N$ removes the forbidden negative-weight term. Therefore $B$ modulo $p$ lies in $\operatorname{Mat}(k)$ with the required filtration blocks.

Assume $B$ has descended modulo $p^r$. Subtract a lift $B_r$ over $W/p^{r+1}$. The remaining matrix is $p^rE$. Frobenius compatibility of the period matrices turns the descent condition into a level-one equation for $E$ modulo $p$. Equations (5.5) and (5.6) again force $E$ to have constant coefficients and the correct filtered blocks. This lifts $B$ modulo $p^{r+1}$. Induction gives a matrix over $W/p^n$.

Finally, substitute (7.7) into the Frobenius equations satisfied by $X_M$ and $X_N$. Cancelling the invertible period matrices yields

$$
B\varphi _i^M=\varphi _i^N B
\quad(i=0,1),
\qquad
B(F_M)\subseteq F_N.
\tag{7.8}
$$

Thus $B$ defines a divided filtered morphism $M\to N$. Compatibility with the relations in the strict free presentations follows because the original map $\alpha$ is defined on their kernels and cokernels; Part 1 gives the necessary lift, and equality on all solution vectors forces the presentation relations. This proves Part 3.

For uniqueness, if two descended matrices induce the same map on solutions, their difference $D$ satisfies $X_ND=0$. The period matrix $X_N$ is invertible after the syntomic cover, so $D=0$. Faithfully flat descent then gives $D=0$ over $W/p^n$. This proves Part 2. $\square$

### 7.4 Why the weight bound is sharp for the proof

In a general interval $[0,r]$, a correction can cross $r$ filtration steps and divided Frobenius can remove $p^r$. The divided-power estimate which forces improvement is valid in the elementary form when $r\le p-2$. At $r=p-1$, a term of divided-power degree $p$ can have exactly the same valuation as the error being corrected, so the contraction used above need not be strict. Additional nilpotence conditions can sometimes repair the boundary, but none are assumed here.

Our theorem uses only $r=1$. Its hypothesis is therefore exactly $p>2$. This is a limitation of the integral full-faithfulness argument, not of the definitions of the two rank-one syntomic complexes.

## 8. Exactness of the generic realization

Contravariant Hom is automatically left exact. The lifting lemma supplies the missing surjectivity and thereby makes syntomic realization compatible with torsion subquotients. This is essential: later arithmetic arguments repeatedly pass between a lattice, its reduction, and its successive torsion layers.

### 8.1 The exactness theorem

**Theorem 8.1 (exactness).** If

$$
0\longrightarrow M'\longrightarrow M\longrightarrow M''\longrightarrow0
\tag{8.1}
$$

is admissibly exact, then

$$
0\longrightarrow T_{\mathrm{FL}}(M'')
\longrightarrow T_{\mathrm{FL}}(M)
\longrightarrow T_{\mathrm{FL}}(M')
\longrightarrow0
\tag{8.2}
$$

is an exact sequence of finite continuous $G_{K_0}$-modules.

The reversal is forced by contravariance. In particular, an admissible quotient of divided filtered modules realizes as a Galois-stable submodule, while an admissible subobject realizes as a Galois quotient.

### 8.2 Proof by strict lifting

**Proof.** Injectivity at the left and exactness in the middle are ordinary properties of precomposition: a map $M\to\mathscr A_\infty$ vanishes on $M'$ precisely when it factors uniquely through $M''$.

Let $f':M'\to\mathscr A_\infty$ be a filtered Frobenius morphism. Part 1 of Theorem 7.1 extends it to a filtered Frobenius morphism $f:M\to\mathscr A_\infty$. Hence the last arrow in (8.2) is surjective. All constructions commute with Galois, and continuity and finiteness were proved in Chapters 5 and 6. $\square$

The proof identifies why strictness is the correct hypothesis. It is used before any Frobenius equation is solved, to extend a filtered linear map while keeping $F_M$ inside the first period filtration.

### 8.3 Kernels, cokernels, and length

Exactness immediately gives useful bookkeeping.

**Corollary 8.2.** Let $u:M\to N$ be a morphism such that its kernel and cokernel, with the induced and quotient filtrations, are admissible and both associated sequences are strict. Then

$$
\ker T(u)=T(\operatorname{coker}u),
\qquad
\operatorname{coker}T(u)=T(\ker u).
\tag{8.3}
$$

Moreover lengths are preserved as in (6.6).

**Proof.** Factor $u$ as the strict epimorphism $M\to\operatorname{im}u$ followed by the strict monomorphism $\operatorname{im}u\to N$, and apply Theorem 8.1 twice. The length formula follows by induction from the atomic level calculation, or additively from any strict presentation. $\square$

For a free object $L$, exactness applied to (3.6) gives

$$
0\to T(L/p^n)	o T(L/p^{m+n})	o T(L/p^m)\to0,
\tag{8.4}
$$

with the order of $m$ and $n$ determined by the contravariant maps. These sequences identify the compatible finite-level realizations of a lattice.

### 8.4 A warning about non-strict sequences

If (8.1) is exact only on underlying $W$-modules, (8.2) can fail at the right. A filtered map on $M'$ may take an element of $F_{M'}=M'\cap F_M$ into $\operatorname{Fil}^1\mathscr A_\infty$, but if the chosen filtration on $M''$ is smaller than the image of $F_M$, an arbitrary extension is forced to satisfy contradictory filtered conditions. Conversely, an artificially enlarged quotient filtration imposes a divisibility condition absent upstairs.

Thus “torsion exactness” always means admissible exactness, including (3.4). Exactness is not a property of the underlying module sequence alone.

## 9. Full faithfulness

Exactness says that divided filtered subquotients remain visible. Full faithfulness says more: every Galois-equivariant map between the generic solutions already comes from a unique integral divided filtered morphism. In other words, generic realization loses neither morphisms nor their denominators in the low-weight range.

### 9.1 The comparison map on morphisms

Contravariance gives a natural map

$$
\Theta_{M,N}:
\operatorname{Hom}_{\mathrm{FL}}(M,N)
\longrightarrow
\operatorname{Hom}_{G_{K_0}}
(T_{\mathrm{FL}}(N),T_{\mathrm{FL}}(M)).
\tag{9.1}
$$

The direction is important. A map $M\to N$ acts on solutions by precomposition, so the generic arrow goes from $T(N)$ to $T(M)$.

Faithfulness can already be seen from period matrices. If $u$ induces zero on all solutions, choose a syntomic cover on which a solution basis gives an invertible evaluation matrix. Then the matrix of $u$ multiplied by this evaluation matrix is zero, so $u=0$ after the faithfully flat cover and hence before it.

### 9.2 Integral reconstruction

Fullness is the descent half of Theorem 7.1. Given

$$
\alpha:T(N)\to T(M),
$$

choose a common annihilating level and strict free presentations. On a syntomic cover, evaluation identifies both solution groups with standard free $\mathbf Z/p^n$-modules. Formula (7.7) transports $\alpha$ to a matrix between the divided filtered modules.

Three conditions must descend simultaneously:

1. $G_{K_0}$-equivariance forces the entries to descend from periods to $W/p^n$.
2. Preservation of the weight-one solution equation forces the matrix to carry $F_M$ into $F_N$.
3. Compatibility with both period Frobenii forces commutation with $\varphi _0$ and $\varphi _1$ separately.

The separate $\varphi _1$ condition cannot be recovered by cancelling $p$ in the $\varphi _0$ equation. The matrix descent proof retains it at each finite level, which is why the result is genuinely integral.

### 9.3 The full-faithfulness theorem

**Theorem 9.1 (Fontaine--Laffaille full faithfulness in weights zero and one).** Under (1.1), for all admissible torsion divided filtered modules $M,N$ of weights $[0,1]$, the map (9.1) is an isomorphism.

**Proof.** Injectivity is the evaluation argument of Section 9.1, equivalently the uniqueness assertion in Theorem 7.1. Given a Galois map $\alpha$, Part 3 of Theorem 7.1 descends its period matrix to a unique $W$-linear map $u:M\to N$ satisfying (2.6). By construction, precomposition with $u$ is $\alpha$. Hence (9.1) is surjective as well. $\square$

**Corollary 9.2.** Isomorphisms, idempotents, and direct-sum decompositions are detected by $T_{\mathrm{FL}}$. If $T(M)\simeq T(N)$ as Galois modules, the isomorphism comes from a unique isomorphism $N\simeq M$ in the reversed variance.

**Proof.** Lift the Galois map and its inverse by Theorem 9.1. Faithfulness shows that the two composites are identities. The same argument applies to idempotents; their images and kernels are admissible when the corresponding filtered sequences are strict. $\square$

### 9.4 Subrepresentations and what is not yet proved

Let $U\subset T(M)$ be a $G_{K_0}$-stable subgroup. Full faithfulness does not by itself produce an admissible quotient $M\twoheadrightarrow Q$ with $T(Q)=U$. To invoke full faithfulness one would first need a divided filtered object realizing $U$; that is exactly an essential-surjectivity or closure-under-subquotients problem.

What has been proved is the forward statement: every admissible quotient of $M$ gives a stable subrepresentation, and morphisms between already realized objects are uniquely controlled. The converse identification of all appropriate finite-flat torsion subrepresentations, its behavior under coefficient change, and compatible quotients of lattices belong to the integral equivalence theorem of the following book.

This logical separation prevents a common circular argument: one may not prove essential surjectivity by treating an arbitrary stable subrepresentation as though full faithfulness had already attached an object to it.

## 10. Duality and Tate twist

Cartier duality exchanges étale and multiplicative directions. In weights zero and one, the linear version must therefore exchange the two atomic lines. Because our realization is contravariant, the correct generic formula is a dual followed by a cyclotomic twist.

### 10.1 The filtered Cartier dual

Let

$$
E_W=K_0/W,
$$

an injective cogenerator for finite-length $W$-modules. For an admissible torsion object $M$, define its $W$-linear dual

$$
M^\vee=\operatorname{Hom}_W(M,E_W).
\tag{10.1}
$$

It has the same $W$-length as $M$. Define the first filtered step by

$$
F_{M^\vee}
=\{f\in M^\vee:f(F_M)=0\}.
\tag{10.2}
$$

This formula exchanges weights. If $F_M=0$, then $F_{M^\vee}=M^\vee$, while if $F_M=M$, then $F_{M^\vee}=0$. The notation $M^\vee$ here means the **Cartier-normalized filtered dual**, already twisted so that its weights remain in $[0,1]$; generically it will realize $T(M)^\vee(1)$.

Evaluation gives a perfect pairing

$$
\langle\ ,\ \rangle:M\times M^\vee\longrightarrow E_W(1),
\tag{10.3}
$$

where $E_W(1)$ denotes the torsion weight-one line. Filtration compatibility follows from (10.2): if both inputs contribute total filtration at least two, one of them lies in the annihilated step.

For a free lattice $L$, the corresponding integral dual is $L^*=\operatorname{Hom}_W(L,W)$ with

$$
F_{L^*(1)}=\operatorname{Ann}(F_L).
\tag{10.4}
$$

Passing to $L/p^nL$ identifies $L^*(1)/p^n$ with (10.1).

### 10.2 Constructing the divided Frobenius on the dual

The Frobenius maps on the dual are characterized by requiring evaluation to be a morphism into the weight-one line. Explicitly, for $x\in F_M$ and $f\in M^\vee$, and for $x\in M$ and $f\in F_{M^\vee}$, require

$$
\langle\varphi _1x,\varphi _0^\vee f\rangle
=\sigma\langle x,f\rangle,
\tag{10.5}
$$

$$
\langle\varphi _0x,\varphi _1^\vee f\rangle
=\sigma\langle x,f\rangle.
\tag{10.6}
$$

These equations determine $\varphi _0^\vee$ and $\varphi _1^\vee$ uniquely because the images of $\varphi _1(F_M)$ and $\varphi _0(C_M)$ form a basis under a normal decomposition. They also show

$$
\varphi _0^\vee|_{F_{M^\vee}}=p\varphi _1^\vee.
\tag{10.7}
$$

**Proposition 10.1.** The construction above makes $M^\vee$ an admissible torsion divided filtered module. It is exact and involutive:

$$
(M^\vee)^\vee\simeq M.
\tag{10.8}
$$

**Proof strategy and proof.** Choose a strict free presentation

$$
0\longrightarrow L_1\xrightarrow{a}L_0\longrightarrow M\longrightarrow0
$$

and normal decompositions of its terms. The free modules have the same rank because their cokernel has finite length. Their integral Cartier-normalized duals fit into

$$
0\longrightarrow L_0^*(1)\xrightarrow{a^*}L_1^*(1)
\longrightarrow M^\vee\longrightarrow0.
$$

Indeed $a^*$ becomes an isomorphism over $K_0$, so it is injective over the torsion-free source, and its cokernel is canonically $\operatorname{Hom}_W(M,K_0/W)$. In dual bases, the normal Frobenius matrix is the $\sigma$-inverse transpose of the original matrix, with the weight-zero and weight-one blocks interchanged. Since the original matrix is invertible over $W$, so is the dual matrix. Proposition 2.1 gives strong divisibility.

Equation (10.2) dualizes the exact sequence of filtered steps, so the displayed dual presentation is strict. Hence $M^\vee$ is admissible and duality reverses admissibly exact sequences. The evaluation map to the double dual is an isomorphism for finite-length modules, preserves (10.2), and respects (10.5)--(10.6); this proves (10.8). $\square$

### 10.3 Compatibility with generic duality

The quotient $\mathscr A_{\mathrm{cris},\infty}$ is an additive torsion object, not a ring, so its elements must not be multiplied naively. On its $p^n$-torsion define the normalized product

$$
x\star_n y=p^n\widetilde x\widetilde y\pmod {\mathscr A_{\mathrm{cris}}},
$$

where $\widetilde x,\widetilde y\in p^{-n}\mathscr A_{\mathrm{cris}}$ represent $x,y$. This is well defined: changing either representative by an integral element changes $p^n\widetilde x\widetilde y$ by an integral element. It again lies in the $p^n$-torsion subgroup.

Choose a strict free presentation of $M$, or first treat $M=L/p^nL$. For a basis $e_i$ of $L$ with Cartier-dual basis $e_i^\vee$, two solutions $x$ and $y$ pair by

$$
\sum_i x(e_i)\star_n y(e_i^\vee).
$$

The contraction is independent of the basis and descends through a strict presentation. Equations (10.5)--(10.6) put it in the weight-one fixed kernel. The fundamental sequence (5.6) therefore gives a Galois-equivariant pairing

$$
T(M)\times T(M^\vee)\longrightarrow\mu_{p^n}
\tag{10.9}
$$

when $p^nM=0$. The filtration conditions and (10.5)--(10.6) show that the product lies in the kernel of $1-\varphi _1$, which is $\mu_{p^n}$ by (5.6).

**Theorem 10.2 (duality).** The pairing (10.9) is perfect and induces a natural isomorphism

$$
T_{\mathrm{FL}}(M^\vee)
\xrightarrow{\sim}
\operatorname{Hom}_{\mathbf Z/p^n}
(T_{\mathrm{FL}}(M),\mu_{p^n}).
\tag{10.10}
$$

Equivalently,

$$
T_{\mathrm{FL}}(M^\vee)\simeq T_{\mathrm{FL}}(M)^\vee(1).
\tag{10.11}
$$

**Proof.** The construction gives the map (10.10). Choose a strict free presentation and pass to a syntomic cover on which the associated solution matrices are invertible. Equations (10.5)--(10.6) say that the solution matrix for $M^\vee$ is, up to the fixed weight-one period, the inverse transpose of the solution matrix for $M$. Thus the matrix of (10.9) has unit determinant on that cover. Faithfully flat descent makes the pairing nondegenerate before the cover, so (10.10) is injective. Proposition 6.1 gives both sides the same finite length $\ell_W(M)$, hence (10.10) is an isomorphism. The Galois action is compatible because multiplication and the fundamental weight-one sequence are equivariant. $\square$

For the atomic objects, $\mathbf1^\vee=\mathbf1(1)$ and $\mathbf1(1)^\vee=\mathbf1$, exactly as (6.7) requires.

### 10.4 Perfect pairings and adjoints

A perfect alternating or symmetric divided filtered pairing

$$
M\times M\longrightarrow E_W(1)
\tag{10.12}
$$

is equivalently an isomorphism $M\simeq M^\vee$ with the corresponding transpose sign. Applying $T$ gives a perfect Galois-equivariant pairing into $\mu_{p^n}$. Because $T$ is fully faithful, adjointness can be checked generically or on the divided filtered module: a pair of morphisms are adjoint in one category if and only if their realizations are adjoint in the other.

At $p=2$, alternating cannot be replaced by skew-symmetric: the condition $\langle x,x\rangle=0$ is separate. Our main theorems assume $p>2$, but retaining the distinction keeps geometric polarization statements correctly normalized.

## 11. Geometry in degree one

The divided filtered category was defined without assuming a geometric origin. We now verify that the degree-one crystalline lattices constructed earlier enter it with exactly the stated conventions, and that their syntomic realizations recover the generic torsion already present in geometry. This supplies examples without claiming that every abstract object is geometric.

### 11.1 Hodge and crystalline input

Let $A/W$ be an abelian scheme of relative dimension $g$, let $A_0=A\times_Wk$, and put

$$
H=H^1_{\mathrm{cris}}(A_0/W).
\tag{11.1}
$$

By crystalline--de Rham comparison for the lift $A/W$, this is identified with $H^1_{\mathrm{dR}}(A/W)$. Its first Hodge step is

$$
F=H^0(A,\Omega^1_{A/W})\subset H.
\tag{11.2}
$$

Book 52 proves that $F$ and $H/F$ are finite free of rank $g$ and that the sequence is compatible with base change. Book 54 supplies the crystalline Frobenius $\Phi$, duality, and the Poincaré pairing. Book 57 identifies the reduction of $H$ with the Dieudonné module of $A_0[p^n]$ at every level and proves

$$
\operatorname{im}V=\ker F_{\mathrm{D}}
$$

on the level-one Dieudonné module, with $F_{\mathrm D}V=VF_{\mathrm D}=p$ integrally.

The Hodge step satisfies

$$
\Phi(F)\subset pH.
\tag{11.3}
$$

Indeed relative Frobenius kills invariant differentials on the special fiber, so $\Phi(F)$ is zero modulo $p$; $H$ is $p$-torsion-free, hence the quotient by $p$ is unique. Define

$$
\varphi _0=\Phi,
\qquad
\varphi _1=\Phi/p\text{ on }F.
\tag{11.4}
$$

**Proposition 11.1.** The quadruple $(H,F,\varphi _0,\varphi _1)$ is a free divided filtered module of weights $[0,1]$.

**Proof strategy.** Only strong divisibility remains. It can be checked modulo $p$. The Dieudonné relations show that ordinary Frobenius supplies the quotient direction while divided Frobenius on the Hodge step supplies the complementary Verschiebung direction.

**Proof.** Choose a complement $H=C\oplus F$. Reduction of $F$ is the Hodge subspace $\operatorname{im}V=\ker F_{\mathrm D}$ from Book 57. Let $y\in H/pH$ be arbitrary. Since $V(y)$ lies in $F/pF$, choose $f\in F$, a lift $\widetilde y\in H$ of $y$, and $z\in H$ such that

$$
f=V(\widetilde y)+pz.
$$

Applying $F_{\mathrm D}$ and using $F_{\mathrm D}V=p$ gives

$$
\varphi _1(f)=y+\varphi _0(z)\pmod p.
\tag{11.5}
$$

Write $z=c+f_0$ with $c\in C$ and $f_0\in F$. Because $\varphi _0(F)\subset pH$, equation (11.5) becomes

$$
y=\overline\varphi _1(f)-\overline\varphi _0(c).
$$

Thus every $y$ lies in $\overline\varphi _0(C)+\overline\varphi _1(F)$. Nakayama gives strong divisibility over $W$. All other axioms follow from (11.3)--(11.4). $\square$

The same construction applies to $H^1$ of a smooth proper curve with good reduction by passing through its Jacobian, whose crystalline degree one and Hodge filtration agree with those of the curve.

### 11.2 Abelian torsion

Let $H_n=H/p^nH$. The group scheme $A[p^n]$ is finite locally free over $W$, and its generic fiber is finite étale. Thus

$$
A[p^n](\overline K_0)
$$

is a finite continuous $G_{K_0}$-module of order $p^{2gn}$.

**Theorem 11.2 (geometric comparison).** With the contravariant conventions above, there is a canonical functorial isomorphism

$$
T_{\mathrm{FL}}(H_n)
\xrightarrow{\sim}
A[p^n](\overline K_0).
\tag{11.6}
$$

It commutes with change of level, homomorphisms of abelian schemes, Cartier duality, and the Weil pairing.

**Proof strategy.** Both sides arise from the same crystalline extension class. The Dieudonné comparison identifies the special-fiber crystal with $H_n$, while the low-weight syntomic period map evaluates that crystal on the generic torsion section. We check the normalization on the étale and multiplicative lines and then use exactness.

**Proof.** Book 57 identifies the crystalline Dieudonné crystal of $A_0[p^n]$ with $H_n$, contravariantly in the group. Evaluating a torsion point of the generic fiber on the universal crystalline extension gives a filtered Frobenius morphism

$$
H_n\longrightarrow\mathscr A_{\mathrm{cris},\infty},
$$

hence a map from the right side of (11.6) to the left. On a maximal étale factor this is (5.5) and sends a constant point to its weight-zero fixed period. On the multiplicative dual factor it is (5.6) and sends a root of unity through the divided-power logarithm. Thus the map has the stated normalization.

Over the perfect special fiber, the finite Dieudonné module has a finite composition series. Exactness of crystalline Dieudonné theory from Book 57 and exactness of $T_{\mathrm{FL}}$ from Theorem 8.1 reduce bijectivity to the simple level-one factors; the local--local factors are handled by the same vector Frobenius equation in Theorem 7.1 rather than by geometric points of the special fiber. At each factor, Proposition 6.1 gives the correct length. Therefore the comparison is an isomorphism.

The construction uses the universal extension, so it is functorial in $A$ and compatible with multiplication by $p$. The evaluation pairing on a group and its Cartier dual is carried by the divided-power logarithm to (10.9); hence Cartier duality and the Weil pairing commute with (11.6). $\square$

This theorem starts with an actual abelian scheme and identifies its already existing torsion. It does not assert that an arbitrary divided filtered module is the crystalline module of a finite-flat group.

### 11.3 Ordinary and local--local examples

For an ordinary elliptic curve, the special-fiber $p$-torsion has a multiplicative connected part and an étale quotient. Its divided filtered module has rank two, with one weight-one and one weight-zero direction. After a suitable unramified extension, its associated graded resembles

$$
\mathbf1_n(1)\oplus\mathbf1_n,
$$

but the integral object need not split. The extension parameter records the Serre--Tate direction of the lift, and exactness realizes it as an extension of the cyclotomic and unramified generic characters in the contravariantly reversed order.

For a supersingular elliptic curve, the level-one special fiber is local--local: neither an étale nor a multiplicative direct summand exists. Nevertheless its rank-two module has a one-dimensional Hodge step, and the combined normal Frobenius map (2.4) is invertible. The syntomic solution group has $p^2$ elements by Proposition 6.1 even though the special fiber has only one geometric point. This is precisely why generic realization cannot be constructed from special-fiber points; divided Frobenius supplies the missing infinitesimal directions.

These examples also distinguish full faithfulness from semisimplicity. A generic representation may become a sum after extending scalars while the integral divided filtered lattice remains a nonsplit extension.

### 11.4 Polarizations

Let $\lambda:A\to A^\vee$ be a principal polarization. Book 54 constructs a perfect alternating pairing

$$
\psi_\lambda:H\times H\longrightarrow W(1)
\tag{11.7}
$$

for which $F$ is Lagrangian and

$$
\psi_\lambda(\Phi x,\Phi y)
=p\sigma(\psi_\lambda(x,y)).
\tag{11.8}
$$

Equations (11.7)--(11.8) make $H_n$ self-dual in the sense of Chapter 10. Under (11.6), the resulting pairing on $T(H_n)$ is the Weil pairing

$$
A[p^n]\times A[p^n]\longrightarrow\mu_{p^n}.
\tag{11.9}
$$

For a polarization of degree divisible by $p$, the integral crystalline pairing need not be perfect; it is a map to the dual with finite cokernel. After the degree is inverted it becomes perfect, but that rational statement does not yield an integral self-duality of $H_n$. The principal hypothesis in the perfect statement is therefore essential.

## 12. Coefficients and change of ground field

Arithmetic applications often carry an auxiliary coefficient algebra or enlarge the residue field. These operations look formal after rationalization, but kernels of $1-\varphi_i$ need not commute with tensor products. This chapter states what follows directly from the present theory and marks the stronger integral comparisons reserved for the base-change theorem.

### 12.1 Commuting coefficient actions

Let $\Lambda$ be a commutative finite $\mathbf Z_p$-algebra. A **$\Lambda$-object** is an admissible divided filtered module $M$ together with a homomorphism

$$
\Lambda\longrightarrow\operatorname{End}_{\mathrm{FL}}(M).
\tag{12.1}
$$

Because precomposition reverses products, one may regard $T(M)$ naturally as a right $\Lambda$-module. Commutativity identifies this with a left action by

$$
(a\cdot f)(m)=f(am).
\tag{12.2}
$$

For a noncommutative coefficient algebra, the opposite algebra must be retained; silently treating (12.2) as a left action would reverse multiplication.

**Proposition 12.1.** The functor $T_{\mathrm{FL}}$ on $\Lambda$-objects is exact for admissibly exact $\Lambda$-linear sequences, compatible with duality after applying the involution appropriate to the coefficient action, and fully faithful on $\Lambda$-linear morphisms.

**Proof.** Exactness and duality hold after forgetting $\Lambda$, and every construction commutes with (12.2). A Galois morphism between realizations is induced by a unique divided filtered morphism by Theorem 9.1. It is $\Lambda$-linear precisely when it commutes with the endomorphisms attached to every $a\in\Lambda$; faithfulness transfers these commutator equalities back to $M$. $\square$

No flatness of $\Lambda$ over $\mathbf Z_p$ is needed for this endomorphism statement. Flatness becomes relevant when tensoring objects or comparing lengths.

### 12.2 Scalar extension of coefficients

Suppose $\Lambda\to\Lambda'$ is finite flat and $M$ carries a compatible $W\otimes_{\mathbf Z_p}\Lambda$-module structure. The algebraic tensor product

$$
M_{\Lambda'}=\Lambda'\otimes_\Lambda M
\tag{12.3}
$$

inherits the filtration $\Lambda'\otimes F_M$ and the two divided Frobenius maps, acting trivially on $\Lambda'$. Flatness preserves the underlying and filtered exact sequences. If a strict free presentation remains finite projective over the new coefficient algebra, (12.3) is again admissible.

Contravariance changes the formal tensor rule. Currying a solution gives a natural identification

$$
T_{\mathrm{FL}}(M_{\Lambda'})
\longrightarrow
\operatorname{Hom}_\Lambda(\Lambda',T_{\mathrm{FL}}(M)),
\tag{12.4}
$$

where a map $f:\Lambda'\otimes_\Lambda M\to\mathscr A_\infty$ is sent to

$$
a\longmapsto(m\longmapsto f(a\otimes m)).
$$

This arrow is an isomorphism onto the homomorphisms for which every curried map satisfies the same filtered Frobenius equations; with the coefficient algebra fixed by Frobenius, that condition is automatic. If $\Lambda'$ is finite projective over $\Lambda$, the right side is

$$
(\Lambda')^\vee\otimes_\Lambda T_{\mathrm{FL}}(M),
$$

not canonically $\Lambda'\otimes_\Lambda T_{\mathrm{FL}}(M)$. Identifying extension with coextension requires a specified perfect trace pairing or other self-duality. Even after such an identification, compatibility with integral subquotients is not formal, because kernels of $1-\varphi_i$ need not commute with an arbitrary change of coefficients. The full integral coefficient-change theorem requires the compatible-quotient and base-change analysis developed in the next book.

If $\Lambda'$ is not flat, even admissibility can fail: tensoring a strict filtered sequence can create Tor in the underlying module or in its first filtered step. No exactness assertion is made in that case.

### 12.3 Unramified extension of the ground field

Let $k\subset k'$ be an extension of perfect fields, set

$$
W'=W(k'),\qquad K_0'=W'[1/p],
$$

and choose compatible algebraic closures. For a free object $L$, the tensor product $W'\otimes_WL$ carries

$$
F'=W'\otimes_WF,
\qquad
\varphi_i'(a\otimes x)=\sigma'(a)\otimes\varphi_i(x).
\tag{12.5}
$$

Flatness of $W'/W$ preserves the normal decomposition, so free objects remain strongly divisible. For a torsion object presented strictly by free objects, scalar extension of the presentation defines an admissible object $M_{W'}$.

Functoriality of crystalline period thickenings gives a natural map

$$
T_{\mathrm{FL},K_0}(M)|_{G_{K_0'}}
\longrightarrow
T_{\mathrm{FL},K_0'}(M_{W'}).
\tag{12.6}
$$

The arrow depends on the chosen compatible embeddings but is canonical up to the corresponding Galois conjugacy. On the two atomic lines it is the evident restriction map for $\mathbf Z/p^n$ and $\mu_{p^n}$.

We do not infer in this book that (12.6) is always an isomorphism for every admissible torsion object, nor do we descend arbitrary objects from $W'$ to $W$. Such statements require compatibility of strict presentations, period solutions, and torsion quotients under integral base change. They are part of the next book's equivalence and base-change package.

### 12.4 Statements deliberately not inferred

The following implications are tempting and invalid without further hypotheses.

- A rational isomorphism after tensoring with $\mathbf Q_p$ does not identify torsion lattices.
- A $G_{K_0}$-stable quotient of $T(M)$ does not automatically come from a divided filtered subobject of $M$.
- A coefficient tensor product need not commute with the kernel of $1-\varphi_i$.
- A Frobenius-stable subspace of $M[1/p]$ need not meet $M$ in a saturated direct summand.
- An isomorphism after unramified field extension does not automatically descend without compatible descent data.

Full faithfulness answers the morphism question between objects already in the category. It neither supplies missing objects nor proves saturation. Keeping this distinction visible is essential in deformation-theoretic applications.

## 13. A theorem and hypothesis ledger

The preceding chapters form one package, but its assertions use different parts of the hypotheses. This chapter consolidates the output and traces every substantial input to the earlier theory on which it depends.

### 13.1 The main package

**Theorem 13.1 (low-weight torsion Fontaine--Laffaille package).** Let $p>2$, let $k$ be perfect of characteristic $p$, put $W=W(k)$ and $K_0=W[1/p]$, and use admissible torsion divided filtered modules of weights $[0,1]$ with strict exact sequences. Then:

1. The syntomic formula

   $$
   T_{\mathrm{FL}}(M)
   =\operatorname{Hom}_{\mathrm{Fil},\varphi}
   (M,\mathscr A_{\mathrm{cris},\infty})
   $$

   defines a finite continuous $G_{K_0}$-module and a contravariant functor.
2. Length is preserved: $\ell_{\mathbf Z_p}T(M)=\ell_W(M)$.
3. The functor reverses every admissibly exact sequence and remains exact.
4. It is fully faithful:

   $$
   \operatorname{Hom}_{\mathrm{FL}}(M,N)
   \simeq
   \operatorname{Hom}_{G_{K_0}}(T(N),T(M)).
   $$

5. The atomic lines realize as $\mathbf Z/p^n$ and $\mu_{p^n}$.
6. Cartier-normalized duality satisfies

   $$
   T(M^\vee)\simeq T(M)^\vee(1),
   $$

   and perfect pairings and adjoints are preserved.
7. Commuting finite coefficient actions are preserved, with the opposite action retained when coefficients are noncommutative.
8. For an abelian scheme $A/W$, the strongly divisible module

   $$
   H^1_{\mathrm{cris}}(A_0/W)/p^n
   $$

   realizes canonically as $A[p^n](\overline K_0)$, compatibly with levels, duality, homomorphisms, and principal-polarization pairings.

**Proof.** Parts 1 and 2 are Chapters 5--7 and Proposition 6.1. Exactness is Theorem 8.1, full faithfulness is Theorem 9.1, and the atomic calculations are (6.7). Duality is Theorem 10.2. Coefficients are Proposition 12.1. The geometric assertion is Proposition 11.1 and Theorem 11.2. $\square$

This theorem does not include essential surjectivity, arbitrary integral scalar-extension isomorphisms, or closure under all Galois subquotients.

### 13.2 Dependency closure

The construction uses the preceding books in the following precise forms.

- Book 52 supplies the Hodge filtration on degree-one de Rham cohomology of curves and abelian schemes, its finite local freeness, duality, and base change. These are used in (11.2) and in the geometric pairing.
- Book 53 supplies divided-power envelopes, the crystalline site, crystals, finite torsion levels, Frobenius lifts, and the divisibility calculation which makes $\varphi/p$ integral. These underlie (5.1)--(5.3).
- Book 54 supplies finite free degree-one crystalline cohomology, crystalline--de Rham comparison, Frobenius, Poincaré duality, and polarizations. These are used in (11.1), (11.7), and (11.8).
- Book 55 supplies the modified first filtration at finite level, the weight-zero and weight-one fundamental exact sequences, the divided-power logarithm, coefficient reduction, and the integral period morphism. These are used in (5.5)--(5.6) and in every successive-approximation step of Chapter 7.
- Book 57 supplies contravariant Dieudonné theory, its exactness and Cartier duality, the comparison of abelian $p^n$-torsion with $H^1_{\mathrm{cris}}/p^n$, the relation between Frobenius, Verschiebung, and the Hodge subspace, and Raynaud full faithfulness in its stated ramification range. Only the Dieudonné and comparison results are used to prove Chapter 11; Raynaud's theorem provides compatible orientation but is not used to prove Fontaine--Laffaille full faithfulness.

The algebra of finite free modules over a complete DVR, Nakayama's lemma, exactness of duality into $K_0/W$, and faithfully flat descent of matrices are ordinary commutative-algebra background. No later classification theorem is used in Chapters 7--9.

### 13.3 Failure modes

| Assertion | Hypotheses actually used | Failure prevented |
|---|---|---|
| divided $\varphi_1$ on torsion | integral lift or modified finite-level filtration | cancellation of $p$ in a torsion module |
| normal decomposition | $M$ finite free, $F$ a direct summand, strong divisibility | a surjective output matrix with hidden torsion kernel |
| torsion admissibility | strict two-term free presentation | artificial filtered torsion objects |
| exact realization | exactness on $M$ and on $F_M$ | failure to extend a filtered solution |
| small-weight lifting | weights $[0,1]$ and $p>2$ | loss of $p$-adic contraction at the boundary |
| full faithfulness | unramified base $W(k)$, $k$ perfect | absence of canonical Witt Frobenius or invalid divisibility |
| finite continuous realization | finite-length input and geometric period stalk | infinite or discontinuous solution group |
| duality | finite length or finite freeness and Cartier-normalized twist | wrong weight interval or nonperfect evaluation |
| perfect polarization pairing | principal polarization | $p$-power cokernel for a nonprincipal polarization |
| coefficient exactness after tensoring | flat coefficient change and preserved admissibility | Tor in modules or filtered steps |
| base-change isomorphism | additional integral comparison theorem | fixed points need not commute with tensor product |
| geometric comparison | an actual good-reduction abelian scheme | unproved essential surjectivity for abstract modules |

The table is also a diagnostic protocol. When a proposed application fails, one should first ask whether the filtration sequence is strict, whether the weight interval lies inside $[0,p-2]$, and whether an asserted tensor comparison is being mistaken for a formal property of fixed points.

## 14. Conclusion

A divided filtered module is the smallest integral object which remembers both Hodge position and the exact divisibility of crystalline Frobenius. In weights zero and one it consists of a lattice, one direct-summand filtration step, ordinary Frobenius, and Frobenius divided once on that step. Strong divisibility turns these data into an invertible normal Frobenius matrix. Strict free presentations carry the same information to torsion without pretending that division by $p$ remains unique after reduction.

Crystalline period coefficients convert this linear algebra into arithmetic. Their two fundamental syntomic sequences identify ordinary Frobenius fixed points with $\mathbf Z/p^n$ and divided-Frobenius fixed points with $\mu_{p^n}$. Coupling those two equations through a normal decomposition produces the generic module $T_{\mathrm{FL}}(M)$. The small-weight lifting lemma shows that solutions lift across every strict quotient and that a Galois-equivariant matrix descends uniquely to the Witt lattice. Exactness and full faithfulness are the two consequences: subquotients already present in the category survive generically, and no integral morphism is lost.

Duality exchanges the two weights and becomes Galois duality with a cyclotomic twist. For a good-reduction abelian scheme, crystalline--de Rham comparison and Dieudonné theory place $H^1_{\mathrm{cris}}/p^n$ in the category, and syntomic realization recovers the actual generic points of $A[p^n]$, including ordinary, multiplicative, and local--local directions. Principal polarizations pass to the Weil pairing with the same normalization.

The resulting package is therefore

$$
\begin{array}{c}
\text{strict divided filtered torsion module of weights }0,1\\
\downarrow\;\operatorname{Hom}_{\mathrm{Fil},\varphi}(-,\mathscr A_{\mathrm{cris},\infty})\\
\text{finite continuous }G_{K_0}\text{-module}
\end{array}
$$

with exactness, duality, and full faithfulness. What remains is genuinely different: proving that the relevant integral objects all arise, that arbitrary suitable finite-flat torsion representations are captured, and that integral base change and compatible quotients preserve the classification. Those questions begin only after the faithful generic realization established here is in place.
