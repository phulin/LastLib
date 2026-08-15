# Quaternionic PEL Functors and Representability

## Contents

- [1. From a quaternionic datum to a moduli problem](#1-from-a-quaternionic-datum-to-a-moduli-problem)
  - [1.1 The task of this book](#11-the-task-of-this-book)
  - [1.2 What is inherited and what must be proved](#12-what-is-inherited-and-what-must-be-proved)
  - [1.3 PEL realizability is a hypothesis](#13-pel-realizability-is-a-hypothesis)
- [2. The fixed quaternionic PEL datum](#2-the-fixed-quaternionic-pel-datum)
  - [2.1 Rational tensors and the similitude group](#21-rational-tensors-and-the-similitude-group)
  - [2.2 Positivity and the quaternionic model](#22-positivity-and-the-quaternionic-model)
  - [2.3 Integral data and the good base](#23-integral-data-and-the-good-base)
  - [2.4 The Hodge module and reflex field](#24-the-hodge-module-and-reflex-field)
- [3. The moduli category](#3-the-moduli-category)
  - [3.1 Objects and arrows](#31-objects-and-arrows)
  - [3.2 Polarization type](#32-polarization-type)
  - [3.3 Level structures](#33-level-structures)
  - [3.4 The functor and the stack](#34-the-functor-and-the-stack)
- [4. The determinant condition](#4-the-determinant-condition)
  - [4.1 Why dimension is not enough](#41-why-dimension-is-not-enough)
  - [4.2 The universal determinant polynomial](#42-the-universal-determinant-polynomial)
  - [4.3 Closedness and base change](#43-closedness-and-base-change)
  - [4.4 Geometric meaning and limitations](#44-geometric-meaning-and-limitations)
- [5. Polarizations, adjoints, and pairings](#5-polarizations-adjoints-and-pairings)
  - [5.1 Rosati compatibility](#51-rosati-compatibility)
  - [5.2 The level pairing](#52-the-level-pairing)
  - [5.3 Positivity cannot be replaced by symmetry](#53-positivity-cannot-be-replaced-by-symmetry)
- [6. Descent of PEL objects](#6-descent-of-pel-objects)
  - [6.1 Descent in the correct order](#61-descent-in-the-correct-order)
  - [6.2 Effectivity](#62-effectivity)
  - [6.3 The stack theorem](#63-the-stack-theorem)
- [7. Isomorphisms and the finite diagonal](#7-isomorphisms-and-the-finite-diagonal)
  - [7.1 Rigidity of homomorphisms](#71-rigidity-of-homomorphisms)
  - [7.2 Finiteness for polarized automorphisms](#72-finiteness-for-polarized-automorphisms)
  - [7.3 The diagonal theorem](#73-the-diagonal-theorem)
- [8. Killing automorphisms with level](#8-killing-automorphisms-with-level)
  - [8.1 The congruence lemma](#81-the-congruence-lemma)
  - [8.2 Full level at least three](#82-full-level-at-least-three)
  - [8.3 Neat level](#83-neat-level)
- [9. Framed parameter spaces](#9-framed-parameter-spaces)
  - [9.1 A canonical ample bundle](#91-a-canonical-ample-bundle)
  - [9.2 Projective frames](#92-projective-frames)
  - [9.3 Cutting out the additional structures](#93-cutting-out-the-additional-structures)
  - [9.4 Algebraicity and finite presentation](#94-algebraicity-and-finite-presentation)
- [10. Fine representability](#10-fine-representability)
  - [10.1 From trivial inertia to an algebraic space](#101-from-trivial-inertia-to-an-algebraic-space)
  - [10.2 Why the algebraic space is a scheme](#102-why-the-algebraic-space-is-a-scheme)
  - [10.3 The representability theorem](#103-the-representability-theorem)
- [11. Infinitesimal deformation theory](#11-infinitesimal-deformation-theory)
  - [11.1 The characteristic-zero Hodge chart](#111-the-characteristic-zero-hodge-chart)
  - [11.2 Linearizing the PEL conditions](#112-linearizing-the-pel-conditions)
  - [11.3 The local-model diagram](#113-the-local-model-diagram)
  - [11.4 Cotangent complexes and obstruction groups](#114-cotangent-complexes-and-obstruction-groups)
- [12. The quaternionic curve calculation](#12-the-quaternionic-curve-calculation)
  - [12.1 The active real place](#121-the-active-real-place)
  - [12.2 The rank-two local model](#122-the-rank-two-local-model)
  - [12.3 Smoothness and dimension one](#123-smoothness-and-dimension-one)
  - [12.4 The cotangent and Hodge lines](#124-the-cotangent-and-hodge-lines)
- [13. Fine covers and finite quotients](#13-fine-covers-and-finite-quotients)
  - [13.1 Cofinal principal levels](#131-cofinal-principal-levels)
  - [13.2 Change of level](#132-change-of-level)
  - [13.3 Quotient stacks and coarse schemes](#133-quotient-stacks-and-coarse-schemes)
  - [13.4 When a universal family descends](#134-when-a-universal-family-descends)
- [14. The universal abelian family](#14-the-universal-abelian-family)
  - [14.1 Construction by Yoneda](#141-construction-by-yoneda)
  - [14.2 Universal endomorphisms and polarization](#142-universal-endomorphisms-and-polarization)
  - [14.3 Hodge and determinant bundles](#143-hodge-and-determinant-bundles)
  - [14.4 Functoriality under base change](#144-functoriality-under-base-change)
- [15. Generic fibers, properness, and the Shimura curve](#15-generic-fibers-properness-and-the-shimura-curve)
  - [15.1 Comparison with the canonical model](#151-comparison-with-the-canonical-model)
  - [15.2 Selecting the required components](#152-selecting-the-required-components)
  - [15.3 Properness in the division case](#153-properness-in-the-division-case)
  - [15.4 The boundary with integral-model theory](#154-the-boundary-with-integral-model-theory)
- [16. The representability package](#16-the-representability-package)
  - [16.1 Main theorem](#161-main-theorem)
  - [16.2 Hypothesis ledger](#162-hypothesis-ledger)
  - [16.3 Conclusion](#163-conclusion)

## 1. From a quaternionic datum to a moduli problem

### 1.1 The task of this book

A quaternionic Shimura curve first appears as an arithmetic quotient of a half-plane. That description reveals its complex points, but it does not yet provide a family of abelian varieties over an arbitrary base scheme. Arithmetic geometry needs the latter description. One wants to attach to every scheme $S$ a groupoid of abelian schemes over $S$, with quaternionic endomorphisms, a compatible polarization, and finite level structure, and then prove that this rule is represented after enough level has been imposed.

There are four logically separate problems.

First, the moduli data must be typed correctly. A noncommutative order action is a ring homomorphism, not a collection of commuting endomorphisms. A polarization is an actual positive isogeny to the dual, not merely an alternating form. The Hodge type is a determinant law on the Lie algebra, not just the dimension of the abelian scheme. A level structure must respect both the order and the polarization pairing.

Second, the data must descend. An object constructed after an fppf cover is useful only when compatible identifications on double overlaps, satisfying the cocycle on triple overlaps, produce an object downstairs.

Third, automorphisms must be controlled. Without rigid level, the natural answer is a stack. A scheme represents the set-valued moduli problem only when every geometric stabilizer has been killed.

Fourth, the representing object must have the geometry expected of a curve. This is an infinitesimal question. Deforming an abelian scheme amounts to moving its Hodge filtration; endomorphisms, polarization, and determinant law cut out a local model. In the quaternionic curve case that local model has one moving rank-two line and hence dimension one.

This book solves those four problems in that order. The resulting fine scheme carries a universal abelian scheme. At non-neat level the quotient stack still carries a universal object, whereas its coarse scheme generally does not. That distinction will remain visible throughout.

### 1.2 What is inherited and what must be proved

The descent theorems for schemes, vector bundles, bilinear forms, group laws, and projective morphisms are already available. The general language of fibered categories, stacks, diagonals, framed atlases, and PEL objects is also established. We use the dual abelian scheme, the Poincare bundle, Weil pairings, and the intrinsic definition of a polarization. Cotangent complexes supply the passage from a linearized deformation problem to smoothness. Finally, the quaternionic group, its symplectic realizations, its Shimura datum, reflex field, and canonical model have already been constructed.

Those results do not make the present theorem automatic. We must choose one exact integral PEL datum, write its determinant polynomial without ambiguity, prove that its level condition kills all automorphisms, construct the representing scheme, and identify its tangent problem. We must also say exactly where the construction stops. Complex uniformization with adelic components, descent of Hecke correspondences, and good or semistable models at bad primes require further arguments; they are not smuggled into representability.

All schemes below are locally noetherian when deformation or Hilbert-polynomial arguments are used. Abelian schemes are smooth, proper, finitely presented group schemes with geometrically connected fibers. The dual of $A$ is $A^\vee$. If $n$ is invertible on the base, $A[n]$ is finite etale. We work in characteristic zero for the final Shimura curve and over an explicitly localized number ring for the auxiliary integral functor.

### 1.3 PEL realizability is a hypothesis

A quaternion algebra by itself does not define a PEL moduli problem. Let $G$ be the connected reductive group underlying the desired quaternionic Shimura datum. A symplectic representation

$$
\rho:G\longrightarrow\operatorname{GSp}(V,\psi)
$$

may have extra tensors in its stabilizer besides endomorphisms and a pairing. If so, imposing only endomorphisms, polarization, and level gives a larger Shimura variety. Conversely, an arbitrary involution on the quaternion algebra may fail positivity at some real places. Neither defect can be repaired by writing down a determinant condition after the fact.

We therefore use the following precise term.

**Definition 1.1.** A **quaternionic PEL realization** of $(G,X)$ is a tuple

$$
\mathscr D=(D,*,V,\psi,h)
$$

such that:

1. $D$ is a finite-dimensional semisimple $\mathbf Q$-algebra and $*$ is a positive involution;
2. $V$ is a faithful left $D$-module and $\psi$ is a nondegenerate alternating form satisfying

   $$
   \psi(bx,y)=\psi(x,b^*y);
   $$

3. $h:\mathbb S\to\operatorname{GSp}(V,\psi)_{\mathbf R}$ gives $V$ Hodge types $(-1,0)$ and $(0,-1)$ and polarizes them;
4. the identity component of the $D$-linear similitude group of $(V,\psi)$ is the chosen central modification of $G$, and its adjoint Shimura datum is the desired quaternionic datum.

The fourth condition is the PEL condition. It excludes a mere Hodge-type embedding whose image requires higher tensors. The quaternionic trace construction, a split-corestriction construction when its central kernel has been treated, or its prescribed central modification supplies the realizations used here. We never claim that every quaternionic Shimura datum admits this exact PEL description. All representability theorems below begin with Definition 1.1.

There are two outcomes to keep distinct. If $G_{\mathscr D}=G$, the realization is **direct** and
the fine PEL scheme is a model of the original Shimura variety. If $G_{\mathscr D}$ is a
nontrivial central modification with the same adjoint datum, its fine PEL scheme is instead a
finite central cover from which the original Shimura variety is recovered by the effective
finite quotient constructed in Book 118. The universal abelian family lives on the PEL cover and
descends through that quotient only under the inertia criterion of Section 13.4.

This qualification is mathematically productive. It tells us that the tensors to be spread out are exactly an algebra action and an alternating pairing. It also makes the deformation space a homogeneous space for the group we intend, rather than for an accidentally larger centralizer.

## 2. The fixed quaternionic PEL datum

### 2.1 Rational tensors and the similitude group

Fix a quaternionic PEL realization $\mathscr D$. First put

$$
\widetilde G_{\mathscr D}(R)=
\left\{g\in\operatorname{GL}_{D\otimes R}(V\otimes R):
\psi(gx,gy)=\nu(g)\psi(x,y),\ \nu(g)\in R^\times\right\}
$$

for every $\mathbf Q$-algebra $R$, and let

$$
G_{\mathscr D}=\widetilde G_{\mathscr D}^{\circ}.
$$

Perfectness of $\psi$ makes the multiplier $\nu(g)$ unique. By hypothesis,
$G_{\mathscr D}$ is the connected central modification carrying the quaternionic adjoint datum
fixed in the preceding book. Keeping the identity component in the notation is important:
$\widetilde G_{\mathscr D}$ can have extra components, whereas a Shimura datum in the convention
of Book 118 starts with a connected reductive group.

There are two commuting actions hidden in this formula. The prescribed algebra $D$ acts on the left and will become endomorphisms of the universal abelian scheme. The group $G_{\mathscr D}$ is formed by automorphisms commuting with that action. Confusing these sides reverses multiplication in the moduli problem.

For example, let $F$ be totally real and let $B/F$ be quaternionic. On the $\mathbf Q$-space underlying $B$, right multiplication commutes with left multiplication. If $\delta\in B^\times$ is pure, a form of the shape

$$
\psi_\delta(x,y)=
\operatorname{Tr}_{F/\mathbf Q}\operatorname{Trd}_B(x\bar y\delta)
$$

is alternating. Its adjoint on the left action is

$$
b^*=\delta^{-1}\bar b\delta,
$$

because cyclicity of reduced trace gives

$$
\psi_\delta(bx,y)=\psi_\delta(x,b^*y).
$$

Right multiplication by $c$ scales the form by $\operatorname{Nrd}(c)$. Requiring this reduced norm to be a rational scalar gives the common-norm group. This calculation explains both the side convention and the rational multiplier condition.

It does not prove that the desired Hodge map lands in that group. Book 118, Proposition 8.2
shows that when the quaternionic adjoint datum has both an active split real factor and an
inactive compact real factor, the lift is impossible: the reduced-norm exponent is odd at the
active factor and even at the compact factor. Thus this direct common-norm example is not a
PEL realization of a mixed one-split datum. Such a datum must begin with a genuinely different
central modification satisfying Definition 1.1.

Book 118, Proposition 8.3 provides such a modification in the form needed below. If
$L=FK$ is a CM quadratic extension embedded in $B$, regard $B$ as a rank-two right $L$-space
with Hermitian norm $H(x,x)=\operatorname{Nrd}_B(x)$ and put

$$
\psi(x,y)=\operatorname{Tr}_{L/\mathbf Q}(\xi H(x,y)),
\qquad c(\xi)=-\xi.
\tag{2.1a}
$$

**Proposition 2.1A (the unitary datum is PEL-exact).** Let $L$ act on $B$ by right
multiplication and give it the positive involution $c$. The identity component of the
$L$-linear similitude group of (2.1a) is exactly the unitary common-multiplier group
$G^{\mathrm u}$ of Book 118, (8.3c). Its determinant law has multiplicities $(1,1)$ at the
active real place and $(2,0)$ at every inactive real place. Consequently

$$
(L,c,B,\psi,h^{\mathrm u})
\tag{2.1b}
$$

is a quaternionic PEL realization in the sense of Definition 1.1, with reflex field $L$ and
the same adjoint curve datum as $B^\times$.

**Proof.** Complex conjugation is the positive involution on the CM field $L$. The adjoint
of right multiplication by $a$ in (2.1a) is right multiplication by $c(a)$. If an
$L$-linear automorphism scales $\psi$ by a rational scalar, nondegeneracy of the trace pairing
forces it to scale $H$ by the same scalar; this is precisely (8.3c). Book 118, Proposition
8.3 verifies the real signatures, positivity, weight-one types, derived group, determinant
multiplicities, and reflex field. $\square$

### 2.2 Positivity and the quaternionic model

An alternating form alone produces a symplectic group, but an abelian variety requires a positive weight-one Hodge structure. The involution is called positive when, after extending to $\mathbf R$, the trace form associated with $xx^*$ is positive in the PEL sense. Equivalently in the chosen representation, for every $h\in X$ the form

$$
(x,y)_h=\psi(x,h(i)y)
$$

is symmetric positive definite after the fixed global sign choice.

This requirement is not cosmetic. Canonical quaternion conjugation is positive on a Hamilton quaternion factor but is not a positive involution on a split matrix factor. An orthogonal twist can be positive on a split factor and fail on a Hamilton factor. Thus a mixed quaternion algebra should not automatically be used as the endomorphism algebra $D$. A corestriction algebra, a central modification, or a larger commutant may be the correct $D$ in Definition 1.1.

The Hodge homomorphism gives a decomposition

$$
V_{\mathbf C}=V^{-1,0}\oplus V^{0,-1}.
$$

Let $W_h$ denote the quotient corresponding to the tangent space of the associated complex torus; with our homology convention it is $V_{\mathbf C}/F^0V_{\mathbf C}$. It has dimension

$$
g=\frac12\dim_{\mathbf Q}V.
$$

The action of $D$ on $W_h$ is the model for the action on $\operatorname{Lie}(A)$. Its characteristic polynomials will become the determinant condition.

### 2.3 Integral data and the good base

Rational tensors do not determine an integral moduli problem. Choose:

- a $*$-stable order $\mathcal O\subset D$;
- an $\mathcal O$-stable lattice $\Lambda\subset V$;
- an integer $c>0$ such that $c\psi$ is integral on $\Lambda$;
- a polarization type $\mathfrak t$ compatible with the dual lattice;
- a compact open $K\subset G_{\mathscr D}(\mathbf A_f)$ stabilizing $\widehat\Lambda$ and the pairing type.

Enlarge a finite set $S_{\mathrm{bad}}$ of rational primes until it contains $2$, every prime at which $\mathcal O$ or $\Lambda$ is not self-dual in the prescribed sense, every prime dividing $c$ or the polarization degree, and every prime at which the chosen level is not hyperspecial. Let $E$ be the reflex field and put

$$
R=\mathcal O_E[S_{\mathrm{bad}}^{-1}].
$$

Over $R$, the order, lattice, pairing, and polarization kernel type are finite locally free and their ranks are constant. This localization is a convenient domain for the representability construction. It is not asserted to be maximal, and it is not the good integral model theorem of a later book.

When a principal integer level $N$ is used, we assume

$$
N\geq3,
\qquad N\in R^\times,
\qquad \gcd(N,\deg\lambda)=1.
$$

The last condition is what makes the polarization pairing on $A[N]$ perfect. Omitting it turns a purported symplectic level structure into an ill-typed condition.

### 2.4 The Hodge module and reflex field

Choose a $\mathbf Z$-basis $e_1,\ldots,e_m$ of $\mathcal O$. The representation of $\mathcal O$ on $W_h$ defines the polynomial

$$
P_{\mathscr D}(T;X_1,\ldots,X_m)
=\det\left(T-\sum_{i=1}^mX_i e_i\mid W_h\right).                 \tag{2.1}
$$

Its coefficients are invariant under the Galois stabilizer of the Hodge cocharacter class and
therefore lie in $E$. After enlarging $S_{\mathrm{bad}}$, they lie in $R$. A change of the basis
$(e_i)$ merely makes an invertible integral substitution in the variables, so the equality of
determinant laws defined by (2.1) is intrinsic.

For a quaternion algebra split at exactly one real embedding $\tau_0$, the noncentral Hodge cocharacter occurs only at that label. The reflex field is the embedded copy $\tau_0(F)$. The other real factors influence the representation and positivity but contribute no tangent direction. This separation between abelian dimension $g$ and moduli dimension one is the central numerical feature of the construction.

## 3. The moduli category

### 3.1 Objects and arrows

We can now state the moduli problem without suppressing any datum. For an $R$-scheme $S$, a quaternionic PEL object is a tuple

$$
x=(A,\iota,\lambda,\eta)
$$

where:

1. $A\to S$ is an abelian scheme of relative dimension $g$;
2. $\iota:\mathcal O\to\operatorname{End}_S(A)$ is a unital ring homomorphism;
3. $\lambda:A\to A^\vee$ is a polarization of type $\mathfrak t$;
4. the Rosati identity

   $$
   \lambda\circ\iota(b)=\iota(b^*)^\vee\circ\lambda             \tag{3.1}
   $$

   holds for every $b\in\mathcal O$;
5. the action on $\operatorname{Lie}(A)$ satisfies the determinant law of Chapter 4;
6. $\eta$ is the chosen principal or $K$-orbit level structure of Chapter 3.3.

An arrow $f:x\to x'$ is an isomorphism of abelian schemes satisfying

$$
f\iota(b)=\iota'(b)f,
\qquad
f^\vee\lambda'f=\lambda,
\qquad
f(\eta)=\eta'.                                                     \tag{3.2}
$$

The direction in the middle formula matters. It says that $f$ pulls the target polarization back to the source polarization. A quasi-isogeny does not count as an arrow in this moduli category.

### 3.2 Polarization type

Over characteristic zero, a polarization has finite etale kernel. Its degree alone need not determine its elementary divisors. We fix the stronger locally constant type $\mathfrak t$: fppf locally, the kernel with its alternating commutator pairing has the prescribed standard form. For a principal polarization, $\mathfrak t$ is trivial and $\lambda$ is an isomorphism.

The type condition is stable under arbitrary base change and is open and closed among polarizations of a fixed degree. Indeed, after an etale cover trivializing the finite kernel, its elementary divisors are locally constant. Descent returns the decomposition-free statement. At primes dividing the degree the kernel can be nonreduced, which is one reason those primes were placed in $S_{\mathrm{bad}}$ for the present construction.

It is important that $\lambda$ be an actual polarization. A symmetric isogeny $A\to A^\vee$ can lie in a different component of the cone of symmetric homomorphisms. Positivity, supplied by a relatively ample line bundle fppf locally, selects the polarization cone.

### 3.3 Level structures

Suppose first that $N$ satisfies the conditions of Section 2.3 and that a primitive $N$th root of unity has been fixed after the finite etale base change $R_N=R[\zeta_N]$. A **full PEL level-$N$ structure** is an $\mathcal O$-linear isomorphism

$$
\eta_N:\Lambda/N\Lambda\xrightarrow{\sim}A[N]                  \tag{3.3}
$$

such that for one unit $u\in(\mathbf Z/N\mathbf Z)^\times$ fixed by the chosen component,

$$
   e_N^\lambda(\eta_Nx,\eta_Ny)=
   \zeta_N^{\,u\,(c\psi)(x,y)}.                                  \tag{3.4}
$$

Here $(c\psi)(x,y)$ is reduced modulo $N$, the exponent is interpreted in
$\mathbf Z/N\mathbf Z$, and

$$
e_N^\lambda(x,y)=e_N(x,\lambda y)
$$

is the Weil pairing obtained from the Poincare biextension. Because $N$ is prime to
$\deg\lambda$, it is perfect. Allowing the multiplier $u$ to vary gives similitude level;
fixing $u=1$ gives symplectic level. If a connected component fixes some other multiplier, that
value is part of the component datum rather than an unquantified choice in the definition.

The cyclotomic choice is only a framing device. Intrinsically, one records an isomorphism between the multiplier line of $c\psi$ modulo $N$ and $\mu_N$. A general prime-to-$S_{\mathrm{bad}}$ level $K$ is a $K$-orbit of compatible trivializations on the prime-to-bad Tate module. For finite-presentation moduli, it is enough to choose a normal principal congruence subgroup $K(N)\subset K$ and descend the full level-$N$ cover by the finite group $K/K(N)$.

### 3.4 The functor and the stack

Let $\mathscr Q_K(S)$ be the groupoid of the preceding objects over $S$. Pullback of abelian schemes, homomorphisms, duals, polarizations, Lie algebras, and finite etale torsion makes $S\mapsto\mathscr Q_K(S)$ a category fibered in groupoids over $R$-schemes.

Its set of isomorphism classes is only a presheaf. It can fail to be a sheaf because an object may have descent data whose underlying isomorphism class glues while no chosen representative does. The groupoid retains the overlap isomorphisms and their cocycle, which is exactly the information effective descent consumes.

At sufficiently rigid level all automorphisms vanish. Only then will the groupoid be equivalent to a sheaf of sets and eventually to a scheme. Until Chapter 8, the stack rather than its set of points is the honest moduli object.

## 4. The determinant condition

### 4.1 Why dimension is not enough

An action of $\mathcal O$ on an abelian scheme differentiates to

$$
\iota_{\mathrm{Lie}}:\mathcal O\longrightarrow
\operatorname{End}_{\mathcal O_S}(\operatorname{Lie}(A)).
$$

The rank of $\operatorname{Lie}(A)$ records $g$ but not how the embeddings or simple factors of $D$ occur. Even for a quadratic field $L$, a rank-two module can have both tangent directions through one embedding instead of one through each. These families have the correct abelian dimension and the wrong Hodge type.

The characteristic polynomial of every algebra element records the missing multiplicities. In a noncommutative order, however, checking only a convenient list of generators is unsafe: characteristic polynomial is not additive, and the polynomial for a product is not determined by the separate polynomials of its factors. The correct finite condition is equality of polynomial laws.

### 4.2 The universal determinant polynomial

For an object $(A,\iota,\lambda,\eta)$ over $S$, define

$$
P_A(T;X_1,\ldots,X_m)=
\det\left(T-\sum_iX_i\iota(e_i)\mid\operatorname{Lie}(A)\right).
                                                                    \tag{4.1}
$$

This belongs to $\Gamma(S,\mathcal O_S)[T,X_1,\ldots,X_m]$ and is homogeneous of the expected degrees in the $X_i$. The **Kottwitz determinant condition** is the coefficientwise equality

$$
P_A(T;X_1,\ldots,X_m)=P_{\mathscr D}(T;X_1,\ldots,X_m).           \tag{4.2}
$$

The right side is viewed in $\Gamma(S,\mathcal O_S)[T,\mathbf X]$ through $R\to\Gamma(S,\mathcal O_S)$. Substituting $X_i=a_i$ gives

$$
\det(T-\iota(b)\mid\operatorname{Lie}(A))
=\det(T-b\mid W_h)
$$

for every $b=\sum a_ie_i$ after every scalar extension. Conversely, equality after the universal substitution implies (4.2). Thus the condition is independent of both the chosen basis and the chosen presentation of $\mathcal O$.

### 4.3 Closedness and base change

**Proposition 4.1.** In any family with an $\mathcal O$-action, the determinant condition defines a closed subfunctor and commutes with arbitrary base change.

**Proof.** Work on an open set on which $\operatorname{Lie}(A)$ is free. Matrices for the finitely many $\iota(e_i)$ have entries in the coordinate ring. The coefficients of (4.1) are polynomial expressions in those entries. Equality with (2.1) is therefore the vanishing of finitely many functions. On overlaps, characteristic polynomials are invariant under change of basis, so the closed subschemes glue.

Exterior powers and determinants of finite locally free modules commute with base change. Hence pulling the equations to $S'$ produces exactly the determinant equations for $A_{S'}$. Closedness and compatibility descend from the chosen open cover. $\square$

The proof also explains why one should not quantify naively over the infinitely many elements of $\mathcal O$. One universal element $\sum X_ie_i$ produces a finite system of equations and captures the entire determinant law.

### 4.4 Geometric meaning and limitations

Over an algebraically closed field of characteristic zero, $D$ is semisimple and its modules are completely reducible. Equality of the determinant law fixes the multiplicity of every simple constituent of $\operatorname{Lie}(A)$. In the PEL realization hypothesis, those multiplicities are precisely the ones selected by the Hodge cocharacter. Thus (4.2) selects the desired Hodge-type locus.

The conclusion changes at bad primes. If $\mathcal O\otimes k$ is not semisimple, two nonisomorphic modules can have the same characteristic polynomial law, and nilpotent extensions can survive. The determinant locus can then be nonflat or nonreduced. Wedge, spin, or lattice-chain conditions may be required. This book makes no claim that (4.2) alone gives a good model at such a prime.

There is also an orientation issue in some orthogonal data: two components can have the same determinant law. Our quaternionic PEL datum includes the component selected by $h$; when necessary it is imposed as an open-and-closed orientation condition. It is never inferred from (4.2) without verification.

## 5. Polarizations, adjoints, and pairings

### 5.1 Rosati compatibility

For a polarization $\lambda$, the Rosati involution on $\operatorname{End}^0(A)$ is

$$
u\longmapsto u^\dagger=\lambda^{-1}u^\vee\lambda.
$$

Equation (3.1) says $\iota(b)^\dagger=\iota(b^*)$. It is enough to impose this equality on a ring-generating set of $\mathcal O$, because both sides reverse products:

$$
\iota(bc)^\dagger
=\iota(c)^\dagger\iota(b)^\dagger
=\iota(c^*)\iota(b^*)
=\iota((bc)^*).
$$

Unlike the determinant law, the Rosati condition really is propagated by the multiplication table.

**Proposition 5.1.** Rosati compatibility is a closed condition and is preserved by arbitrary base change.

**Proof.** The Hom functor between two abelian schemes is separated and unramified. Equality of the two homomorphisms in (3.1) is the inverse image of its diagonal, hence closed. Duality, composition, and the polarization all commute with base change, so the equality does as well. Finitely many generators suffice by the calculation above. $\square$

### 5.2 The level pairing

The Poincare biextension gives a perfect pairing

$$
e_N:A[N]\times A^\vee[N]\longrightarrow\mu_N.
$$

Composing the second input with $\lambda$ gives $e_N^\lambda$. If $N$ is prime to $\deg\lambda$, then $\lambda:A[N]\to A^\vee[N]$ is an isomorphism, so $e_N^\lambda$ is perfect and alternating. This conclusion holds scheme-theoretically, not merely on geometric points.

Rosati compatibility yields

$$
e_N^\lambda(\iota(b)x,y)
=e_N^\lambda(x,\iota(b^*)y).                                      \tag{5.1}
$$

Indeed, functoriality of the Poincare pairing moves $\iota(b)$ across to its dual, and (3.1) identifies the result. Thus the finite level module carries exactly the same adjoint algebra as $(\Lambda/N\Lambda,c\psi)$.

The isomorphism functor in (3.3) is finite etale over $S$: both source and target are finite etale of the same rank, and the locus where a homomorphism is invertible is open and closed in the finite Hom scheme. Equations for $\mathcal O$-linearity and (3.4) select an open-and-closed subscheme. Consequently full prime-to-base level is a finite etale cover of the moduli problem without level.

### 5.3 Positivity cannot be replaced by symmetry

The equality $\lambda^\vee=\lambda$ is necessary for a polarization but not sufficient. On a product $A_1\times A_2$, the difference of two positive product polarizations can define a symmetric isogeny with a negative direction. It has a perfectly nondegenerate alternating torsion pairing and still does not come from an ample class.

In the moduli functor, positivity means that fppf locally on $S$ there is a relatively ample rigidified line bundle $L$ with $\lambda=\lambda_L$. The property is fpqc local even when that particular $L$ has no descent datum: after the homomorphism $\lambda$ has descended, test each geometric fiber after the faithfully flat residue-field extension supplied by the cover. A symmetric isogeny of abelian varieties is a polarization if and only if its scalar extension is, because ampleness is invariant under field extension. Thus the intrinsic polarization homomorphism descends even when a chosen inducing bundle does not. The fixed type controls the finite kernel; it does not supply positivity.

The archimedean positivity in Definition 1.1 and the algebraic positivity of $\lambda$ are two faces of the same requirement on complex fibers. The former ensures that the target Hodge structures are abelian; the latter is the family-wise condition used by the moduli problem.

## 6. Descent of PEL objects

### 6.1 Descent in the correct order

Representability begins with the more basic fact that the proposed rule is a stack. The proof is clearest when structures are descended in the order in which they are typed:

$$
A\ ;\quad \iota\ ;\quad \lambda\ ;\quad
\text{determinant and type}\ ;\quad \eta.                         \tag{6.1}
$$

Let $T\to S$ be an fpqc cover and suppose $x_T$ is a PEL object with a descent isomorphism on $T\times_ST$ satisfying the cocycle. The underlying proper group scheme descends first. Only after $A$ exists downstairs does it make sense to descend its endomorphisms. Once the action exists, the polarization homomorphism and its compatibility can descend. The determinant equation is then a statement about the descended Lie bundle. Finally, the finite level trivialization descends.

Changing this order can conceal a gap. For example, an alternating pairing on a locally trivial Tate module does not manufacture a polarization of an abelian scheme that has not yet descended. Nor can a characteristic polynomial condition be descended before the vector bundle and action on which it is evaluated have been identified.

### 6.2 Effectivity

**Theorem 6.1 (effective descent for PEL objects).** The category of quaternionic PEL objects is an fpqc stack over $R$.

**Proof.** Effective descent for schemes gives an $S$-scheme $A$ from $A_T$. Multiplication, identity, and inversion are compatible morphisms, so they descend and obey the group laws because their defining diagrams commute after the faithfully flat cover. Smoothness, properness, finite presentation, and geometric connectedness are fpqc local on the base. Hence $A/S$ is an abelian scheme.

For every generator $e_i$ of $\mathcal O$, the endomorphism $\iota_T(e_i)$ is compatible with descent and therefore descends uniquely. Its addition and multiplication identities hold after pullback to $T$ and thus on $S$. This gives the ring map $\iota$. The map $\lambda_T:A_T\to A_T^\vee$ descends because formation of the dual and descent of morphisms commute. It remains a polarization: on every geometric fiber this can be tested after the faithfully flat field extension induced from $T$, where it follows from the ampleness defining $\lambda_T$. Its finite kernel type descends as a finite locally free group scheme with pairing.

Rosati compatibility and the determinant condition are equalities of descended morphisms or coefficients, so faithful flatness reflects them. The torsion $A[N]$ is a finite etale group scheme and commutes with base change. The isomorphism $\eta_T$ and its pairing equation descend by effective descent for finite schemes and morphisms.

The same argument proves descent of arrows. Two arrows equal after the cover were equal before it, so the category is also a prestack. Thus it is an fpqc stack. $\square$

The proof works for a $K$-orbit level by first refining to a principal level and then descending the finite orbit. It also works with a specified lattice chain, but it gives only stackhood, not flatness or smoothness of the resulting bad-prime model.

### 6.3 The stack theorem

Write $\mathscr Q_K$ for this stack. Its formation commutes with a change of coefficient
ring $R\to R'$ provided every piece of the datum is base changed, including the determinant
polynomial and multiplier line. There is a universal PEL object over the stack in the
tautological sense: over a map $S\to\mathscr Q_K$, its pullback is the object classified by
that map.

This statement is stronger than saying that isomorphism classes form an fppf sheaf and weaker than scheme representability. It retains automorphisms. The next three chapters respectively prove that the automorphisms form a finite scheme, show how level kills them, and construct a finite-presentation atlas.

## 7. Isomorphisms and the finite diagonal

### 7.1 Rigidity of homomorphisms

For abelian schemes $A$ and $A'$ over $S$, the functor

$$
\underline{\operatorname{Hom}}_S(A,A')
$$

is separated and unramified. Infinitesimally, a homomorphism that is zero modulo a square-zero ideal would give a homomorphism from the proper connected group $A$ to a vector group. Every function on $A$ comes from the base, and a constant homomorphism taking zero to zero is zero. Thus homomorphisms have no infinitesimal deformations.

The isomorphism functor $\underline{\operatorname{Isom}}(A,A')$ is the open subfunctor where a homomorphism is invertible. Commuting with each $\iota(e_i)$, preserving $\lambda$, and respecting level are equalities of homomorphisms, hence closed conditions. Therefore the diagonal of $\mathscr Q_K$ is representable, separated, and unramified. Finiteness requires polarization.

### 7.2 Finiteness for polarized automorphisms

**Lemma 7.1.** Let $(A,\lambda)$ be a polarized abelian variety over a field. Its polarization-preserving automorphism group is finite.

**Proof strategy.** Rosati positivity turns preservation of $\lambda$ into a positive norm equation in a lattice.

**Proof.** The endomorphism group $\operatorname{End}(A)$ is a free abelian group of finite rank. On $\operatorname{End}^0(A)$, Rosati defines the positive definite quadratic form

$$
q(u)=\operatorname{Tr}(uu^\dagger),
$$

where the trace is the rational trace of the action on a Tate module, or equivalently the reduced trace on the semisimple endomorphism algebra. If $f^\vee\lambda f=\lambda$, then $f^\dagger f=1$, so $q(f)=\operatorname{Tr}(1)$ is fixed. A positive definite sphere meets the lattice $\operatorname{End}(A)$ in finitely many points. $\square$

Over a family, the same argument yields a finite unramified automorphism scheme. To see properness in the finite-presentation setting, use the discrete-valuation criterion. An automorphism of the generic fiber of polarized abelian schemes over a DVR extends uniquely to a homomorphism, as does its inverse; their composites extend the identity and hence are identities. Preservation of the polarization extends by separatedness. Quasi-finiteness follows fiberwise from Lemma 7.1, and proper plus quasi-finite is finite.

The subgroup commuting with $\mathcal O$ and preserving level is closed in this finite scheme. It is therefore finite and unramified as well. In characteristic zero it is finite etale; over excluded residue characteristics it need not be etale.

### 7.3 The diagonal theorem

**Theorem 7.2.** The diagonal

$$
\Delta:\mathscr Q_K\longrightarrow
\mathscr Q_K\times_R\mathscr Q_K
$$

is representable, finite, unramified, and separated.

**Proof.** After a base change by a scheme carrying two objects $x$ and $x'$, the fiber of the diagonal is $\underline{\operatorname{Isom}}(x,x')$. It is a closed subfunctor of the isomorphisms of polarized abelian schemes with fixed degree. If it is nonempty fppf locally, choosing one isomorphism makes it a torsor under the finite automorphism scheme of $x$; hence it is finite. If it is empty, it is represented by the empty scheme. Rigidity gives unramifiedness, and finiteness gives separatedness. $\square$

One should not replace this argument by the statement that a polarized object has “usually” few automorphisms. Finiteness of every stabilizer is what makes the diagonal finite; triviality, needed for a fine scheme, is a separate level argument.

## 8. Killing automorphisms with level

### 8.1 The congruence lemma

The familiar threshold $N\geq3$ comes from an integral linear algebra fact.

**Lemma 8.1 (torsion congruence lemma).** Let $M$ be a finite free $\mathbf Z$-module and let $u\in\operatorname{GL}(M)$ have finite order. If $u\equiv1\pmod N$ for an integer $N\geq3$, then $u=1$. The same conclusion holds for a finite free $\mathbf Z_\ell$-module when $u\equiv1\pmod{\ell^a}$ and either $\ell$ is odd or $\ell=2$ and $a\geq2$.

**Proof.** It is enough to treat a prime power $p^a\mid N$ with either $p$ odd or $p=2$ and
$a\geq2$. If $u\ne1$, replace it by a nonidentity power of prime order $q$. Choose the largest
$p$-adic depth $s\geq a$ for which

$$
u=1+p^sX,
\qquad X\not\equiv0\pmod p.
$$

The binomial expansion gives

$$
0=u^q-1=qp^sX+\binom q2p^{2s}X^2+\cdots .                          \tag{8.1}
$$

If $q\ne p$, divide by $p^s$ and reduce modulo $p$. Every term after the first vanishes, leaving
$qX\equiv0\pmod p$, a contradiction. If $q=p$ is odd, divide by $p^{s+1}$: all later terms
have strictly larger $p$-adic valuation, so reduction again gives $X\equiv0\pmod p$. If
$p=q=2$, equation (8.1) has just the two terms $2^{s+1}X+2^{2s}X^2$; because $s\geq2$, the
second has strictly larger valuation and gives the same contradiction. Thus no nonidentity
torsion element occurs in the stated congruence subgroup. $\square$

The lemma fails at level two: $-1\equiv1\pmod2$. This is not an artificial counterexample. The inversion automorphism preserves every polarization and every endomorphism action centralizing it.

### 8.2 Full level at least three

**Theorem 8.2.** A quaternionic PEL object over an $R$-scheme with full level $N\geq3$ has no nontrivial automorphism.

**Proof.** First work over an algebraically closed field $k$ whose characteristic does not divide $N$. Let $f$ preserve the PEL object. The polarization makes $f$ a member of a finite group by Lemma 7.1, so $f$ has finite order. Choose a prime power $\ell^a\mid N$ with either $\ell$ odd or $\ell=2$ and $a\geq2$; such a factor exists because $N\ne2$. The full level structure says that $f$ acts trivially on $A[\ell^a]$. Its action on the free $\mathbf Z_\ell$-module $T_\ell A$ is therefore congruent to the identity modulo $\ell^a$. Lemma 8.1 makes that action the identity.

The Tate-module action on homomorphisms is faithful. Indeed, if an endomorphism $v$ kills $T_\ell A$, it kills $A[\ell^n]$ for every $n$ and hence factors as $v=[\ell^n]v_n$ for every $n$. The finite free abelian group $\operatorname{End}(A)$ has no nonzero element divisible by all powers of $\ell$. Thus $v=0$, and applying this to $f-1$ gives $f=1$.

For a general base, the equality locus of a proposed automorphism and the identity is closed because the Hom functor is separated and open because it is unramified. It contains every geometric point by the preceding argument, hence is the entire base. Thus the automorphism is globally trivial. $\square$

### 8.3 Neat level

Full principal level is a convenient cover, not the intrinsic endpoint. A compact open $K$ is neat when the multiplicative group generated by the eigenvalues of every rational arithmetic stabilizer is torsion-free. Since a polarized stabilizer has finite adjoint image, its eigenvalues are roots of unity. Neatness forces them all to be $1$; faithfulness on the center then eliminates the remaining scalar.

**Corollary 8.3.** If $K$ is neat and its chosen faithful level representation detects the center, every object of $\mathscr Q_K$ has trivial automorphism group.

Every compact open contains a neat normal principal congruence subgroup of finite index. Thus fine levels are cofinal. The central qualification is essential: a central root of unity may act trivially on the symmetric domain while acting nontrivially on the abelian family.

## 9. Framed parameter spaces

### 9.1 A canonical ample bundle

To construct a scheme atlas, one must put every abelian scheme into one bounded projective space without making a noncanonical choice of an inducing line bundle. The polarization itself supplies such a bundle.

Let $\mathcal P_A$ be the normalized Poincare bundle on $A\times_SA^\vee$. Define

$$
\mathcal L_\lambda=(1_A,\lambda)^*\mathcal P_A.                   \tag{9.1}
$$

The biextension identities show that $\mathcal L_\lambda$ is rigidified and symmetric. A calculation with the theorem of the square gives

$$
\lambda_{\mathcal L_\lambda}=2\lambda.                            \tag{9.2}
$$

Hence it is relatively ample. Its Hilbert polynomial depends only on $g$ and the polarization type. Formation of (9.1) commutes with arbitrary base change.

This canonical doubling is useful: the line bundle representing $\lambda$ may exist only fppf locally and may not descend, while $\mathcal L_\lambda$ is defined globally from the homomorphism $\lambda$. No choice in the Picard torsor remains.

### 9.2 Projective frames

Choose $m$ sufficiently large, depending only on the fixed Hilbert polynomial, so that for every geometric fiber

$$
\mathcal L_\lambda^m
$$

is very ample and has vanishing higher cohomology. Boundedness and cohomology-and-base-change then show that

$$
\mathcal E=p_*\mathcal L_\lambda^m
$$

is locally free of a fixed rank $r$, commutes with base change, and embeds $A$ into $\mathbf P(\mathcal E^\vee)$. A frame $\alpha:\mathcal O_S^r\simeq\mathcal E$ produces a closed immersion

$$
A\hookrightarrow\mathbf P_S^{r-1}
$$

with a fixed Hilbert polynomial.

The frame bundle is a $\operatorname{GL}_r$-torsor. Consequently every PEL object acquires a frame after an fppf cover. Changes of frame account for all ambiguity in the projective presentation.

### 9.3 Cutting out the additional structures

The relative Hilbert scheme for the fixed polynomial contains a universal projective family. We successively impose the following finite-presentation conditions.

- Smoothness, geometric connectedness, and the condition that a chosen section be the identity define open loci.
- Multiplication, inverse, and identity are represented by graphs in suitable relative Hilbert schemes. The group identities are closed equalities. The abelian-scheme locus is therefore locally closed.
- For finitely many generators of $\mathcal O$, graphs of endomorphisms with the prescribed multiplication table form locally closed conditions. Polarization bounds their degrees, so only finitely many Hilbert polynomials occur.
- A homomorphism $A\to A^\vee$ with fixed finite kernel type and induced by an ample class is locally closed; Rosati equations are closed.
- The universal determinant equality (4.2) is closed.
- Full level is finite etale over the locus without level.

The boundedness assertion for endomorphisms deserves explanation. With a polarization fixed,
the Rosati quadratic form

$$
q(f)=\operatorname{Tr}(f^\dagger f)
$$

is positive definite on the endomorphism lattice. For a prescribed generator $e_i$, Rosati
compatibility gives $\iota(e_i)^\dagger=\iota(e_i^*)$. The element $e_i^*e_i$ satisfies a fixed
integral polynomial, so on a rational Tate module of fixed rank the trace of
$\iota(e_i^*e_i)$ belongs to a finite set of possible sums of its roots. Thus
$q(\iota(e_i))$ is uniformly bounded, and only finitely many integral endomorphisms can occur in
that positive-definite ball. Their graphs have only finitely many Hilbert polynomials. Applying
this to the finite chosen generating set prevents the parameter space from becoming an infinite
disjoint union of unbounded endomorphism choices.

Let $H$ be the resulting locally closed parameter scheme of framed PEL objects. The group $\operatorname{GL}_r$ acts by changing the frame. The universal family on the Hilbert scheme restricts to a universal framed PEL object on $H$.

### 9.4 Algebraicity and finite presentation

**Theorem 9.1.** The natural morphism

$$
H\longrightarrow\mathscr Q_K
$$

is a smooth surjective atlas. In particular, $\mathscr Q_K$ is an algebraic stack of finite presentation over $R$ with finite diagonal.

**Proof.** Given a PEL object, its frame bundle for $p_*\mathcal L_\lambda^m$ is a $\operatorname{GL}_r$-torsor and hence an fppf cover on which the object maps to $H$. Two frames differ uniquely by $\operatorname{GL}_r$, so

$$
\mathscr Q_K\simeq[H/\operatorname{GL}_r].                         \tag{9.3}
$$

The projection from a quotient by a smooth group is smooth and surjective. Every condition defining $H$ was locally of finite presentation, and the Hilbert polynomial is fixed, so $H$ and the quotient stack are of finite presentation. The diagonal was proved finite in Theorem 7.2. $\square$

Algebraicity is not smoothness over $R$. The atlas is smooth over the stack because it is a frame torsor; the structural map $\mathscr Q_K\to\operatorname{Spec}R$ is smooth only when its local model is smooth. Chapter 11 treats that separate question.

## 10. Fine representability

### 10.1 From trivial inertia to an algebraic space

At full level $N\geq3$ or at neat level, Theorem 8.2 makes every inertia group trivial. The diagonal of $\mathscr Q_K$ is then a monomorphism with every fiber a point. More concretely, between any two objects there is at most one isomorphism. The stack is therefore equivalent to its fppf sheaf of isomorphism classes.

An algebraic stack with trivial inertia and representable diagonal is an algebraic space. In the quotient presentation (9.3), the equivalence relation

$$
H\times_{\mathscr Q_K}H\rightrightarrows H
$$

is a free smooth equivalence relation, and its fppf sheaf quotient is exactly this algebraic space. We denote it by $Q_K$.

### 10.2 Why the algebraic space is a scheme

Trivial inertia alone does not force an algebraic space to be a scheme. At principal level the polarization supplies a representable finite map to a known scheme, and every other neat level is a finite free quotient of such a principal level.

First take full PEL level $N\geq3$. Choose the fine Siegel moduli scheme $\mathcal A_{g,\mathfrak t,N}$ with the same polarization type and full underlying symplectic level. Forgetting the $\mathcal O$-action and retaining the polarization and level gives

$$
q:Q_{K(N)}\longrightarrow\mathcal A_{g,\mathfrak t,N}.           \tag{10.1}
$$

The map is representable and separated. Its geometric fibers are finite: homomorphisms are discrete, and the Rosati bound in Section 9.3 leaves only finitely many actions by the fixed order. It is proper by the valuative criterion. Over a discrete valuation ring, an action on the generic abelian scheme extends uniquely to the abelian scheme, as do its Rosati identities; the determinant equations extend by equality of regular functions. The target object already supplies the level structure over the valuation ring, so no extension of a generic torsion basis is being asserted. Thus $q$ is proper and quasi-finite, hence finite.

A finite algebraic space over a scheme is a scheme: affine locally on the target it is the relative spectrum of its finite direct-image algebra. Since the Siegel scheme is quasi-projective over $R$, $Q_{K(N)}$ is quasi-projective as well.

Now let $K$ be any neat level and choose $K(N)\triangleleft K$. The effective finite group $\Delta$ of level changes acts freely on $Q_{K(N)}$, because a fixed point would be an automorphism of a $K$-level object. A finite group acting on a quasi-projective scheme has a scheme quotient: tensor the finitely many translates of an ample bundle to obtain a linearized ample bundle, cover by invariant affine opens, and take invariant coordinate rings. The free quotient $Q_{K(N)}/\Delta$ represents the $K$-level sheaf and is therefore $Q_K$. It is quasi-projective. This proof also shows why the polarization and fixed endomorphism type matter; without boundedness the principal-level forgetful map need not be finite.

### 10.3 The representability theorem

**Theorem 10.1 (fine representability).** Let $\mathscr D$ be a quaternionic PEL realization, choose the integral data of Chapter 2, and impose either full prime-to-base level $N\geq3$ or a neat level detecting the center. Then the fppf sheaf

$$
S\longmapsto
\{\text{PEL objects over $S$}\}/\text{isomorphism}
$$

is represented by a quasi-projective $R$-scheme $Q_K$ of finite presentation. The scheme carries a universal abelian scheme with universal $\mathcal O$-action, polarization, determinant condition, and level structure.

**Proof.** The stack is algebraic of finite presentation by Theorem 9.1. The level kills inertia by Theorem 8.2 or Corollary 8.3, so it is an algebraic space. Section 10.2 makes that space a quasi-projective scheme. The universal object is obtained in Chapter 14 from the representing identity map. $\square$

The theorem does not assert that $Q_K$ is connected. It can contain several open-and-closed components corresponding to adelic lattice classes. Nor does it say the structural morphism is smooth at every integral prime. Both questions depend on information beyond abstract representability.

## 11. Infinitesimal deformation theory

### 11.1 The characteristic-zero Hodge chart

Representability tells us that the moduli space exists; its local geometry still has to be
identified. We use de Rham homology, the dual of first de Rham cohomology. For an abelian scheme
$A/S$ its Hodge sequence is

$$
0\longrightarrow\omega_{A^\vee}
\longrightarrow H_{1,\mathrm{dR}}(A/S)
\longrightarrow\operatorname{Lie}(A)
\longrightarrow0.                                                   \tag{11.1}
$$

Write $H=H_{1,\mathrm{dR}}(A/S)$ and $F=\omega_{A^\vee}$. Over $E$ the
polarization degree is invertible, so the polarization gives a perfect alternating form on $H$,
with its multiplier line understood. The order acts covariantly on homology, $F$ is
$\mathcal O$-stable and isotropic, and the quotient
$H/F=\operatorname{Lie}(A)$ is exactly where the determinant law belongs.

A full Grothendieck--Messing theorem over ramified integral bases would require crystalline
machinery not present in the dependency row of this book. It is also unnecessary for the generic
curve. The PEL-exact analytic algebraization already proved in Book 118 gives the following exact
characteristic-zero replacement.

**Theorem 11.1 (characteristic-zero Hodge chart).** Let $x$ be a geometric closed point of
$Q_{K,E}$, let $F_x\subset H_x$ be its Hodge subspace, and choose a
$D$-linear symplectic-similitude frame $H_x\simeq V\otimes_E\overline E$. Let
$M_{\mathscr D}$ be the flag scheme of $\mathcal O$-stable Lagrangian direct summands satisfying
the determinant law and the component condition selected by $h$. Then there is an isomorphism

$$
\widehat{\mathcal O}_{Q_{K,\overline E},x}
\simeq
\widehat{\mathcal O}_{M_{\mathscr D,\overline E},F_x}.           \tag{11.2}
$$

After extension to $\mathbf C$, it may be chosen from the locally flat marking of homology and
the period map. With that choice, the infinitesimal Hodge direction is the direction in which the
framed filtration moves. In particular, for a local Artinian $\overline E$-algebra $C$ with
residue field $\overline E$, continuous local maps from the rings in (11.2) to $C$ describe
$\mathcal O$-stable Lagrangian direct-summand lifts

$$
F_C\subset V\otimes_E C,
\qquad F_C\otimes_C\overline E=F_x,                               \tag{11.3}
$$

which satisfy the determinant and component conditions. The level has a unique lift. The action
on the tangent space of the abelian scheme is the action on
$(V\otimes_EC)/F_C$, in accordance with the homology convention.

**Proof strategy.** The substantive input is the two-sided PEL-exact uniformization of Book 118:
it proves both that every point of the analytic quotient gives the stated PEL abelian variety and
that every such PEL Hodge structure comes from the chosen quaternionic domain. Locally the period
domain is an open subset of its compact dual $M_{\mathscr D}(\mathbf C)$. We compare completed
local rings and then use the representing property.

**Proof.** Let $x_0$ be the closed point below $x$. Its residue field is a finite extension of
$E$. Choose an embedding of its algebraic closure into $\mathbf C$. Book 118 identifies the
analytification of the selected PEL component with

$$
\Gamma\backslash X^+,
$$

where $\Gamma$ is the relevant arithmetic group. The fine-level hypothesis makes the stabilizer
of the chosen point trivial. Proper discontinuity therefore gives a sufficiently small analytic
neighborhood $U\subset X^+$ which maps biholomorphically to a neighborhood of the induced
complex point in $Q_{K,E}(\mathbf C)$.

Under the PEL realization, a point of $X^+$ is exactly a $D$-stable polarized Hodge filtration
of the prescribed determinant type. Positivity is an open analytic condition in the compact
dual, so the period map identifies $X^+$ locally with an analytic open subset of
$M_{\mathscr D}(\mathbf C)$. Hence the analytic local rings of $Q_{K,E}(\mathbf C)$ at $x$ and
of $M_{\mathscr D}(\mathbf C)$ at $F_x$ have isomorphic completions.

We recall exactly what the analytic comparison implies algebraically. If a finite-type
$\mathbf C$-scheme is presented near a point by
$\mathbf C[z_1,\ldots,z_n]/I$, its analytic local ring is obtained from convergent power series,
while both the algebraic and analytic maximal-ideal completions are

$$
\mathbf C[[z_1,\ldots,z_n]]/I\mathbf C[[z_1,\ldots,z_n]].
$$

Thus analytification does not change the completed local ring. The analytic open immersion shows
that $Q_{K,\mathbf C}$ and $M_{\mathscr D,\mathbf C}$ are smooth of the same dimension at the
corresponding points. Smoothness and relative dimension descend through the faithfully flat
extension $\overline E\to\mathbf C$. Both completed local rings over $\overline E$ are therefore
power-series rings in the same number of variables, which proves (11.2). The period construction
over $\mathbf C$ identifies their tangent directions with the stated algebra, isotropy,
determinant, and component conditions. Finally, prime-to-characteristic level is finite etale,
and finite etale objects lift uniquely across nilpotent thickenings. $\square$

The direct-summand condition in (11.3) is essential: a fiberwise rank condition can leave torsion
in the quotient. The theorem is deliberately a characteristic-zero theorem about the generic
PEL scheme. It proves every infinitesimal assertion used below without claiming an integral
Hodge-lifting theorem at the excluded primes.

### 11.2 Linearizing the PEL conditions

Fix a geometric point $x=(A,\iota,\lambda,\eta)$ of $Q_{K,E}$ and write

$$
H=H_{1,\mathrm{dR}}(A/k),\qquad F=\omega_{A^\vee},\qquad
Q=H/F=\operatorname{Lie}(A).
$$

An unrestricted first-order lift of $F$ is the graph of a map

$$
u:F\longrightarrow Q.                                               \tag{11.4}
$$

Thus the tangent space of the Grassmannian is $\operatorname{Hom}(F,Q)$. The PEL structures impose three linear conditions.

First, $\mathcal O$-stability says

$$
u(bf)=b\,u(f),
$$

so $u\in\operatorname{Hom}_{\mathcal O}(F,Q)$. Second, differentiating isotropy gives

$$
\langle u(f_1),f_2\rangle+
\langle f_1,u(f_2)\rangle=0.                                       \tag{11.5}
$$

Depending on the chosen identification $Q\simeq F^\vee$, this is a symmetry condition on the corresponding bilinear form. Third, the derivative of (4.2) requires the trace of the induced variation on every universal algebra element to agree with the prescribed constant law. In the semisimple characteristic-zero situation, the determinant multiplicities have already selected the appropriate direct summands, so this last condition removes variations between different multiplicity blocks rather than adding hidden nilpotent equations.

Consequently the PEL tangent space is the kernel of an explicit map

$$
\operatorname{Hom}(F,Q)\longrightarrow
C_{\mathrm{act}}\oplus C_{\mathrm{iso}}\oplus C_{\det},           \tag{11.6}
$$

where the three targets measure failure of equivariance, isotropy, and determinant type. A dimension subtraction is valid only after this map is proved to have constant rank. The homogeneous-space argument of the next section proves exactly that.

### 11.3 The local-model diagram

Let $M_{\mathscr D}$ be the $E$-scheme whose points over an $E$-algebra $C$ are $\mathcal O$-stable locally direct-summand submodules

$$
F\subset V\otimes_{\mathbf Q}C
$$

which are Lagrangian, satisfy the determinant law on the corresponding quotient, and lie in the component selected by $h$. It is a closed and open subscheme of a closed subscheme of the Lagrangian Grassmannian.

Because $D\otimes E$ is semisimple, the determinant law fixes the multiplicities of all simple
constituents. The component condition then puts every geometric filtration under consideration
in the orbit of $F_h$. The PEL realizability hypothesis identifies the connected stabilizer of
the algebra and pairing with $G_{\mathscr D}$, so this is precisely the
$G_{\mathscr D,\overline E}$-orbit. The stabilizer of $F_h$ is the parabolic $P_\mu$ attached to
the Hodge cocharacter. Hence

$$
M_{\mathscr D,\overline E}\simeq
G_{\mathscr D,\overline E}/P_\mu.                                \tag{11.7}
$$

This proves that the generic local model is smooth and projective. It also proves that (11.6) has constant rank: its kernel is the tangent space of the orbit.

There is a geometric version of (11.7). Let $\widetilde Q_{K,E}$ classify a generic-fiber PEL
object together with a $D$-linear symplectic-similitude frame in the component selected above,

$$
\beta:H_{1,\mathrm{dR}}(A/S)\xrightarrow{\sim}V\otimes\mathcal O_S.
$$

Then the two maps

$$
Q_{K,E}\xleftarrow{\ \pi\ }\widetilde Q_{K,E}
\xrightarrow{\ \varphi\ }M_{\mathscr D}                         \tag{11.8}
$$

send a frame respectively to its underlying object and to the framed Hodge filtration. The map
$\pi$ is a torsor under the smooth group $G_{\mathscr D}$. To analyze $\varphi$, extend to
$\mathbf C$ and use the marked analytic neighborhood in the proof of Theorem 11.1. There the
diagram is locally the action map

$$
X^+\times G_{\mathscr D}(\mathbf C)
\longrightarrow M_{\mathscr D}(\mathbf C),
\qquad (F,g)\longmapsto gF.
$$

The inclusion $X^+\hookrightarrow M_{\mathscr D}(\mathbf C)$ is analytically open, so the
differential is surjective and the action map is smooth of relative dimension
$\dim G_{\mathscr D}$. Algebraic and analytic smoothness agree for finite-type complex schemes,
and smoothness with its relative dimension descends through $\mathbf C/E$. Hence $\varphi$ is
smooth of relative dimension $\dim G_{\mathscr D}$.

The two arrows in (11.8) therefore add the same number of formally smooth variables. In
particular, $Q_{K,E}$ and $M_{\mathscr D}$ have isomorphic completed local singularity types,
and

$$
\dim Q_{K,E}=\dim M_{\mathscr D}.                                 \tag{11.9}
$$

This is the local-model principle in the exact generic form needed here.

### 11.4 Cotangent complexes and obstruction groups

Whenever an integral determinant locus is locally a complete intersection and its linearized
constraints admit a two-term presentation, write that presentation as vector bundles

$$
\mathcal E\xrightarrow{\alpha}\mathcal F.
$$

The dual of the relative cotangent complex is represented in degrees $0,1$ by $[\mathcal E\to\mathcal F]$. Its zeroth cohomology is the tangent bundle and its first cohomology is the primary obstruction sheaf. Smoothness requires surjectivity of $\alpha$, not merely the expected fiber dimension.

This description is conditional: without the lci hypothesis, further negative-degree cotangent
homology may occur. On the generic fiber, (11.7), (11.8), and the smoothness criterion show that
$\alpha$ is locally split surjective. Therefore

$$
L_{Q_{K,E}/E}\simeq\Omega^1_{Q_{K,E}/E}[0]                        \tag{11.10}
$$

with $\Omega^1$ locally free, and every square-zero PEL deformation is unobstructed. The relative dimension is

$$
\dim Q_{K,E}/E=\dim M_{\mathscr D}
=\dim G_{\mathscr D,\overline E}/P_\mu.                          \tag{11.11}
$$

At a bad integral prime, failure of semisimplicity can make $H^1$ of the tangent complex nonzero; failure of a regular sequence can add cotangent homology below degree $-1$; failure of flatness can invalidate fiberwise base change. These are distinct failures. A determinant line records their Jacobian minors but does not by itself repair any of them.

## 12. The quaternionic curve calculation

### 12.1 The active real place

Assume now that the quaternion algebra $B/F$ is split at exactly one real embedding $\tau_0$ and that the chosen PEL realization has this quaternionic adjoint datum. The real symmetric domain has one noncompact factor. At $\tau_0$ the adjoint Hodge cocharacter is noncentral; at every other real place it is central in the adjoint quotient because that quotient is compact.

After extending scalars to $\mathbf C$, the derived group is a product of rank-one factors. The cocharacter is minuscule in the $\tau_0$ factor and central in all others. Therefore

$$
G_{\mathbf C}/P_\mu
\simeq \operatorname{PGL}_{2,\mathbf C}/P\simeq\mathbf P^1_{\mathbf C},
                                                                    \tag{12.1}
$$

where $P$ is a Borel stabilizing a line. Compact real factors contribute points to the flag variety, not extra projective lines, because their cocharacters are central. This is why the moduli dimension is one even when the universal abelian scheme has high dimension.

### 12.2 The rank-two local model

The tangent calculation can be seen without root notation. At the active factor, Morita equivalence writes the relevant piece of the framed de Rham module as

$$
W\otimes U,
$$

where $W$ is the fixed two-dimensional simple module for the matrix algebra and $U$ is a two-dimensional multiplicity space. A stable Hodge submodule with the prescribed determinant law is

$$
W\otimes L
$$

for a line $L\subset U$. Polarization makes the complementary quotient dual in the required way but imposes no further equation on a line in a two-dimensional symplectic space. Hence the local model is the line Grassmannian

$$
\operatorname{Gr}(1,U)=\mathbf P(U).
$$

Its tangent space at $L$ is

$$
\operatorname{Hom}(L,U/L),                                        \tag{12.2}
$$

which is one-dimensional. At every inactive factor the determinant and component conditions fix the filtration, so its tangent contribution is zero.

This computation also detects an incorrectly formulated moduli problem. If one uses an endomorphism algebra whose centralizer has an additional moving multiplicity space at an inactive factor, the local model acquires another projective line and the moduli space is not the desired curve. PEL realizability and the exact determinant law prevent that error.

### 12.3 Smoothness and dimension one

**Theorem 12.1.** The generic fiber $Q_{K,E}$ of the fine quaternionic PEL scheme is smooth of pure relative dimension one over $E$.

**Proof.** By (12.1), the geometric generic local model is $\mathbf P^1$ and is smooth of
dimension one. In the local-model diagram (11.8), $\pi$ is smooth surjective of relative
dimension $\dim G_{\mathscr D}$, and $\varphi$ is smooth of the same relative dimension by
Section 11.3. Smoothness descends through $\pi$, while the relative-dimension formula gives

$$
\dim Q_{K,E}=\dim M_{\mathscr D}=1.
$$

Equivalently, Theorem 11.1 identifies every infinitesimal deformation with the choice of the single line deformation (12.2), which always lifts across a square-zero ideal. $\square$

Pure dimension follows even if $Q_{K,E}$ is disconnected, because every component has the same local model. Smoothness implies regularity and normality. These properties will be used when comparing the moduli scheme with the previously constructed canonical model.

### 12.4 The cotangent and Hodge lines

Let $\mathcal L\subset\mathcal U$ be the universal active line on the local model. From (12.2),

$$
\Omega^1_{\mathbf P(\mathcal U)/E}
\simeq\mathcal L\otimes(\mathcal U/\mathcal L)^\vee.
$$

Since $\det\mathcal U=\mathcal L\otimes(\mathcal U/\mathcal L)$, this becomes

$$
\Omega^1\simeq
\mathcal L^{\otimes2}\otimes(\det\mathcal U)^{-1}.               \tag{12.3}
$$

On the frame torsor $\widetilde Q_{K,E}$, the differential of the period morphism in (11.8)
and the characteristic-zero Hodge chart identify the horizontal tangent direction with
$\operatorname{Hom}(\mathcal L,\mathcal U/\mathcal L)$. The identification is equivariant for
change of symplectic-similitude frame. Dualizing (12.2), using (12.3), and applying faithfully
flat descent along $\pi$ therefore gives an intrinsic line-bundle isomorphism on the fine curve.
The perfect active alternating form has values in the multiplier line $\mathcal M$, so exterior
product gives $\det\mathcal U\simeq\mathcal M$. Thus, with the homology convention used here,

$$
\Omega^1_{Q_{K,E}/E}
\simeq\mathcal L^{\otimes2}\otimes\mathcal M^{-1}.               \tag{12.4}
$$

Changing from homology to cohomology dualizes both named lines and leaves the intrinsic isomorphism unchanged. Formula (12.4) is the quaternionic Kodaira--Spencer identity. In terms of perfect complexes, it says

$$
\operatorname{Det}(L_{Q_{K,E}/E})
=\det\Omega^1_{Q_{K,E}/E}
\simeq\mathcal L^{\otimes2}\otimes\mathcal M^{-1}.
$$

The multiplier factor must not be silently discarded. It becomes trivial only after a symplectic rather than similitude normalization has actually trivialized it.

## 13. Fine covers and finite quotients

### 13.1 Cofinal principal levels

Let $K$ be any compact open preserving the integral datum. Choose a normal principal congruence subgroup

$$
K(N)\triangleleft K,
\qquad N\geq3,
$$

small enough to be neat and to detect the center. The scheme $Q_{K(N)}$ is a fine cover. Such subgroups are cofinal: intersect $K$ with a sufficiently deep congruence kernel in one faithful lattice representation.

The cover is finite because forgetting a full level structure has finite fibers represented by a finite etale isomorphism scheme. Over the generic fiber it is etale when both source and target levels are neat. If the target level has stabilizers, the map is instead an atlas for a quotient stack and can ramify on the coarse quotient.

### 13.2 Change of level

For $K'\subset K$, forgetting part of the level gives a finite morphism

$$
Q_{K'}\longrightarrow\mathscr Q_K.                                \tag{13.1}
$$

If both levels are neat, the target is the fine scheme $Q_K$. The underlying abelian scheme and all PEL tensors are unchanged; only the orbit of trivializations is enlarged. When $K'\triangleleft K$, the effective deck group is

$$
\Delta=(K/K')/Z_{\mathrm{triv}},                                  \tag{13.2}
$$

where $Z_{\mathrm{triv}}$ consists of rational central elements already identified by the left action. Keeping this quotient prevents an overcount of deck transformations.

If $K$ is neat, $\Delta$ acts freely. The quotient $Q_{K'}/\Delta$ exists as a finite scheme quotient and represents $\mathscr Q_K$. Thus fine representability is independent of the particular principal cover used to prove it.

### 13.3 Quotient stacks and coarse schemes

At arbitrary $K$, one has

$$
\mathscr Q_K\simeq[Q_{K(N)}/\Delta].                              \tag{13.3}
$$

The quotient stack remembers points fixed by subgroups of $\Delta$ as inertia. The finite categorical quotient

$$
Q_K^{\mathrm{coarse}}=Q_{K(N)}/\Delta                              \tag{13.4}
$$

is a normal quasi-projective scheme on the generic fiber. It records geometric orbits and can have finite quotient singularities.

The construction is independent of $K(N)$. Given two normal neat subgroups, their intersection dominates both. Taking the quotient in either order produces the same invariant function fields, and normalization gives the same finite quotient scheme. Likewise, (13.3) gives equivalent stacks because both present the same groupoid of $K$-level objects.

### 13.4 When a universal family descends

The universal abelian scheme on $Q_{K(N)}$ carries the natural equivariance needed to descend along a free level action. Therefore it descends to $Q_K$ when $K$ is neat. At non-neat level a fixed point $x$ has a stabilizer acting nontrivially on the fiber $A_x$. A family pulled back from the coarse quotient would have trivial stabilizer action on that fiber. Hence the universal family cannot descend.

This gives the exact rule:

- the stack $\mathscr Q_K$ always carries the universal PEL abelian scheme;
- a fine scheme $Q_K$ at neat level carries it;
- the coarse scheme $Q_K^{\mathrm{coarse}}$ carries it only if every stabilizer acts trivially on the entire PEL object, which is precisely the fine condition in this setting.

A power of a Hodge line can descend even when the family does not, because a finite stabilizer character can become trivial after taking a power. This does not contradict the obstruction for the abelian scheme itself.

## 14. The universal abelian family

### 14.1 Construction by Yoneda

Suppose $Q_K$ represents the fine moduli functor. The identity morphism

$$
1_{Q_K}\in\operatorname{Hom}_R(Q_K,Q_K)
$$

corresponds, by the representing bijection, to a PEL object

$$
(\mathcal A,\iota^{\mathrm{univ}},\lambda^{\mathrm{univ}},
\eta^{\mathrm{univ}})
$$

over $Q_K$. This is the universal family. For every $S\to Q_K$, its pullback is canonically the object classified by that morphism. Uniqueness is strict up to the unique isomorphism forced by the fine property.

The construction agrees with descent from the framed parameter space. On $H$, the universal Hilbert family has a $\operatorname{GL}_r$-equivariant structure. Pulling it to the free relation and applying effective fpqc descent produces $\mathcal A$. Yoneda identifies that descent with the object attached to $1_{Q_K}$.

### 14.2 Universal endomorphisms and polarization

Every $b\in\mathcal O$ gives a universal endomorphism

$$
\iota^{\mathrm{univ}}(b):\mathcal A\to\mathcal A.
$$

The full multiplication table holds as equality of morphisms. The universal polarization

$$
\lambda^{\mathrm{univ}}:\mathcal A\to\mathcal A^\vee
$$

has the fixed kernel type and satisfies the Rosati identity. Its associated torsion pairing makes the universal level structure a similitude as in (3.4). All these assertions can be checked on the framed cover, but descent of morphisms makes them genuine equalities over $Q_K$.

There is also a canonical relatively ample bundle

$$
\mathcal L_{\mathrm{univ}}
=(1,\lambda^{\mathrm{univ}})^*\mathcal P_{\mathcal A}
$$

inducing $2\lambda^{\mathrm{univ}}$. One should not replace it by an unspecified line bundle inducing $\lambda^{\mathrm{univ}}$: such a bundle may exist only after an fppf cover.

### 14.3 Hodge and determinant bundles

Let $p:\mathcal A\to Q_K$. The Hodge bundle is

$$
\omega_{\mathcal A}=p_*\Omega^1_{\mathcal A/Q_K}
=e^*\Omega^1_{\mathcal A/Q_K}.
$$

It is locally free of rank $g$, carries the universal $\mathcal O$-action, and satisfies (4.2). Semisimplicity over $E$ decomposes it into isotypic factors. The active rank-one multiplicity factor is the line $\mathcal L$ of Section 12.4.

The determinant line

$$
\det\omega_{\mathcal A}
$$

and all its isotypic determinant factors commute with base change. On the smooth curve, the cotangent determinant is the ordinary cotangent line and (12.4) identifies it with an automorphic Hodge expression. On an integral lci locus, the correct replacement is

$$
\operatorname{Det}(L_{Q_K/R}),
$$

not merely the top exterior power of possibly non-locally-free differentials. Exact triangles and flat base change then preserve the determinant bookkeeping.

### 14.4 Functoriality under base change

For every ring homomorphism $R\to R'$ compatible with the spread-out datum, there is a canonical
map

$$
Q_K\times_RR'\longrightarrow Q_{K,R'}.
$$

It is an isomorphism because both sides represent the same functor on $R'$-schemes: an abelian scheme, action, polarization, determinant equality, and level over an $R'$-scheme are exactly the base changes of the defining types, not necessarily of a single object over $R$. Yoneda supplies the isomorphism.

Under it, the universal family, action, polarization, level, Hodge bundle, and canonical ample bundle all pull back to their universal counterparts. Smoothness also base changes. The converse statement requires care: a singular special fiber does not become smooth merely because the generic fiber is smooth, and cohomology sheaves of a cotangent complex need not commute with nonflat base change even when the perfect complex itself does.

## 15. Generic fibers, properness, and the Shimura curve

### 15.1 Comparison with the canonical model

Let $S_K^{\mathscr D}/E$ be the canonical model constructed in Book 118 for the connected
PEL-exact datum $(G_{\mathscr D},X_{\mathscr D})$ at the level matching $K$. Its symplectic
algebraization uses exactly the endomorphism, adjoint, determinant, polarization, and level
tensors fixed here. At neat PEL level it therefore gives a morphism

$$
Q_{K,E}\longrightarrow S_K^{\mathscr D}.                           \tag{15.1}
$$

on the union of components belonging to the chosen lattice genus.

**Proposition 15.1.** On that union of components, (15.1) is an isomorphism.

**Proof.** Over $\mathbf C$, a PEL object gives the polarized weight-one Hodge structure of the
fixed datum, while the level identifies its rational homology with $V$ up to $K$. Conversely,
the two-sided PEL-exact algebraization theorem of Book 118 recovers from every point of the
selected analytic quotient an abelian variety with exactly the action, adjoint, determinant,
polarization, and level data imposed here. It follows that (15.1) identifies the analytic
uniformizations and induces the same function field on every selected component.

We still have to justify that no nonfinite modification is hidden in this comparison. Let
$\mathcal A$ be the fine Siegel moduli scheme used in Section 10.2. The forgetful map
$Q_{K,E}\to\mathcal A_E$ is finite by that section. Book 118's direct PEL algebraization gives
a compatible finite map $S_K^{\mathscr D}\to\mathcal A_E$. Since $\mathcal A_E$ is separated,
the graph map

$$
Q_{K,E}\longrightarrow Q_{K,E}\times_{\mathcal A_E}S_K^{\mathscr D}
$$

is a closed immersion; the projection of the fiber product to $S_K^{\mathscr D}$ is finite.
Hence (15.1) is finite. It is birational on each selected component by the uniformization
comparison. Both sides
are normal: the source is smooth by Theorem 12.1, and Book 118 constructs
$S_K^{\mathscr D}$ by normalization. A finite birational morphism to a normal scheme is an
isomorphism. $\square$

If the realization is direct, $G_{\mathscr D}=G$ and Proposition 15.1 identifies the fine PEL
scheme with the canonical model $S_K$ of the original datum. For a nontrivial central
modification, Book 118 instead supplies, after choosing compatible levels, a finite map

$$
S_{K^{\mathscr D}}^{\mathscr D}\longrightarrow S_K              \tag{15.2}
$$

obtained by the effective finite central quotient. It need not be an isomorphism: the center can
change the component set even though the adjoint domain is unchanged. Likewise, the universal
abelian family on the source of (15.2) descends only when the effective quotient action is free
on the full PEL object. This is exactly the distinction established in Sections 13.3--13.4.

### 15.2 Selecting the required components

The moduli functor can contain several open-and-closed pieces. Polarization type, the genus of the prime-to-bad lattice, the multiplier component, and orientation data are locally constant. Fixing their values selects an open-and-closed subscheme

$$
Q_K^{\mathrm{req}}\subset Q_K.                                    \tag{15.3}
$$

No connectedness assertion is hidden here. A single geometric connected component can require a finite abelian extension of the reflex field, while the union stable under reflex-field Galois action is defined over $E$. The canonical model at level $K$ is that stable union. Later component formulas identify the individual pieces adelically.

Here “the canonical model” means the model for $(G_{\mathscr D},X_{\mathscr D})$. In the direct
case it is the required model for $(G,X)$. In the central-modification case, the required model
for $(G,X)$ is the corresponding finite quotient (15.2) of the stable union.

The universal abelian scheme restricts to $Q_K^{\mathrm{req}}$. If a geometric component descends only after extending $E$, the restriction of the universal family descends over the same field because the fine moduli interpretation is preserved by the component idempotent.

### 15.3 Properness in the division case

Assume the quaternion algebra is a division algebra and split at exactly one real place. The adjoint arithmetic quotient has no cusps: a rational parabolic would give a proper right ideal in $B$, impossible in a division algebra. The complex analytic Shimura curve is therefore compact.

By Proposition 15.1, $Q_K^{\mathrm{req}}(\mathbf C)$ is the analytification of the corresponding
PEL canonical curve. A quasi-projective complex curve with compact analytification is proper:
embed it in a projective curve, and any missing boundary point would produce a noncompact
punctured analytic neighborhood. Hence the PEL canonical curve is projective over $E$ by descent
of properness. Its finite central quotient, when one is required, is projective as well.

**Corollary 15.2.** In the division, one-split-real-place case, every neat required PEL component
is a smooth projective curve over its field of definition and carries the universal quaternionic
PEL abelian scheme. The corresponding finite central quotient is a projective quaternionic curve;
it carries the descended universal family exactly when its effective action is free.

If $B=M_2(F)$, rational parabolics exist and cusps occur. The open PEL moduli scheme is then not proper; a compactification requires degenerating abelian objects and lies outside the present quaternionic division case.

### 15.4 The boundary with integral-model theory

The scheme $Q_K/R$ constructed here is a representable spread-out PEL functor. At primes excluded from $R$, or at primes where the order and lattice local model are ramified, it is not yet a good integral model. Even over a larger tentative base, the naive determinant locus may fail flatness.

The following claims have been proved here:

- algebraicity and finite presentation of the exact PEL stack;
- fine quasi-projective representability after rigid prime-to-base level;
- smoothness and dimension one of the generic quaternionic curve;
- existence and base-change compatibility of the universal abelian family;
- finite quotient descriptions at arbitrary level.

The following claims require additional local geometry and are not consequences of those results:

- extension over every bad prime;
- smoothness of a ramified integral determinant model;
- semistable reduction, component calculations, or monodromy;
- extension of Hecke correspondences over bad fibers.

Keeping this boundary explicit prevents generic deformation theory from being misapplied to a nonsemisimple residue algebra.

## 16. The representability package

### 16.1 Main theorem

We collect the construction in a form suitable for later use.

**Theorem 16.1 (quaternionic PEL representability package).** Let $(G,X)$ be a quaternionic Shimura datum that admits a quaternionic PEL realization

$$
\mathscr D=(D,*,V,\psi,h)
$$

in the sense of Definition 1.1. Fix a $*$-stable order, a compatible lattice, a polarization kernel type, the universal determinant law attached to $h$, and a prime-to-bad compact open level $K$. Then:

1. PEL objects form an fpqc algebraic stack $\mathscr Q_K$ of finite presentation with finite unramified separated diagonal.
2. A normal principal level $K(N)$ with $N\geq3$ kills all automorphisms. More generally, a neat level detecting the center does so.
3. At such a fine level, the moduli sheaf is represented by a quasi-projective scheme $Q_K$ carrying a universal abelian scheme with universal $\mathcal O$-action, polarization, determinant condition, and level.
4. The characteristic-zero local model is the $E$-flag scheme $M_{\mathscr D}$, whose geometric
   fiber is $G_{\mathscr D,\overline E}/P_\mu$. Hence $Q_{K,E}$ is smooth of dimension
   $\dim(G_{\mathscr D,\overline E}/P_\mu)$.
5. If the quaternion algebra is split at exactly one real place, that dimension is one and the active local model is $\mathbf P^1$.
6. If $K'\triangleleft K$ is fine, then

   $$
   \mathscr Q_K\simeq[Q_{K'}/\Delta]
   $$

   for the effective finite level group $\Delta$. Its finite quotient is the coarse scheme. The universal family descends to the quotient precisely when the target level has trivial inertia.
7. On the required component union, the generic fine PEL scheme is the canonical model of the
   PEL-exact datum $(G_{\mathscr D},X_{\mathscr D})$. In the direct case this is the canonical
   model of $(G,X)$; in the central-modification case the latter is its effective finite central
   quotient. In the division case the PEL curve and its finite quotient are projective.

**Proof.** Effective descent is Theorem 6.1. The diagonal is Theorem 7.2. Automorphism killing is
Theorem 8.2 and Corollary 8.3. The framed atlas and scheme representability are Theorems 9.1 and
10.1. The characteristic-zero Hodge chart and local-model diagram give statements 4 and 5.
Chapter 13 proves the quotient assertions, and Chapter 15 proves the comparison and properness
statements. $\square$

### 16.2 Hypothesis ledger

The theorem is safe to reuse only if its hypotheses travel with it.

| Assertion                                          | Required hypothesis                                                              | Failure without it                                                       |
| -------------------------------------------------- | -------------------------------------------------------------------------------- | ------------------------------------------------------------------------ |
| PEL moduli describes the chosen quaternionic datum | the centralizer of $(D,*,\psi)$ is the chosen central modification               | endomorphism and polarization equations define a larger variety          |
| polarization condition                             | actual positive polarization of fixed kernel type                                | a symmetric isogeny can lie outside the ample cone                       |
| perfect level pairing                              | $N$ invertible and prime to $\deg\lambda$                                        | $e_N^\lambda$ can be degenerate                                          |
| correct Hodge type                                 | equality of the universal determinant polynomial law, plus orientation if needed | generatorwise equations or dimension alone allow wrong multiplicities    |
| finite diagonal                                    | fixed polarization                                                               | unpolarized automorphism groups need not be finite                       |
| trivial inertia                                    | full $N\geq3$, or neat level detecting the center                                | $-1$ survives at level two; central torsion can survive adjoint neatness |
| scheme rather than stack                           | trivial inertia and the finite map to fine Siegel moduli                         | a finite-diagonal stack can still have stabilizers                       |
| generic smoothness                                 | characteristic zero, semisimple $D$, and the selected $G/P_\mu$ component        | the determinant local model can be nonflat or nonreduced                 |
| curve dimension                                    | exactly one noncentral rank-one Hodge factor                                     | abelian dimension does not determine moduli dimension                    |
| universal family on a level or central quotient    | free effective action on the full PEL object                                     | stabilizers obstruct descent to the coarse space                         |
| projectivity                                       | quaternion division datum, hence no rational parabolic                           | split data have cusps                                                    |

Three normalization checks are especially important. The action $\iota$ and the group controlling level lie on commuting sides. The Rosati equation reverses multiplication through $*$. The determinant polynomial is evaluated on the Lie quotient dictated by the fixed homology convention. Changing any one of these conventions requires changing all associated formulas, not merely renaming a symbol.

### 16.3 Conclusion

The quaternionic curve has now acquired an intrinsic moduli meaning. Starting from a genuine polarized weight-one PEL realization, the order action, positive polarization, determinant law, and prime-to-bad level form an fpqc stack. Polarization makes its diagonal finite; full level at least three or a neat center-detecting level removes its inertia. A canonical ample bundle places every object in a bounded Hilbert parameter space, and the finite forgetful map to Siegel moduli turns the resulting algebraic space into a quasi-projective scheme.

Its local geometry is governed by one transparent operation: lift the Hodge filtration. Endomorphisms demand equivariance, polarization demands isotropy, and the determinant law fixes multiplicities. In characteristic zero these conditions form the homogeneous local model $G/P_\mu$. For a quaternion algebra split at exactly one real place, only one rank-two line moves, so the local model is $\mathbf P^1$ and the fine moduli scheme is a smooth curve. Its cotangent line is the square of the active Hodge line corrected by the similitude multiplier.

The universal abelian scheme belongs to the fine PEL curve and, more generally, to the moduli
stack. Finite quotient stacks recover arbitrary level while retaining stabilizers; coarse schemes
forget them and therefore need not carry the family. On the required component union, the generic
fine scheme is the canonical model of its PEL-exact datum over the reflex field. It agrees with
the original quaternionic canonical model in the direct case and finitely covers it in the
central-modification case. Division of the quaternion algebra makes the PEL curve and its finite
quotient projective. The output is thus the exact geometric package promised at the outset:
correctly typed quaternionic PEL functors, determinant and polarization conditions, cofinal fine
covers, representability, smooth curve geometry, and universal abelian families on precisely the
fine spaces where inertia permits them, with the bad-prime integral questions left at their
proper boundary.
