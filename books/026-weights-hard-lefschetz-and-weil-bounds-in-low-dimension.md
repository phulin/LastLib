# Weights, Hard Lefschetz, and Weil Bounds in Low Dimension

## Contents

1. [The size hidden in a Frobenius eigenvalue](#1-the-size-hidden-in-a-frobenius-eigenvalue)
   - [The problem left by the trace formula](#11-the-problem-left-by-the-trace-formula)
   - [Standing conventions](#12-standing-conventions)
   - [Algebraic numbers and Weil numbers](#13-algebraic-numbers-and-weil-numbers)
   - [The route through the proof](#14-the-route-through-the-proof)
2. [Weights and their elementary calculus](#2-weights-and-their-elementary-calculus)
   - [Pure representations](#21-pure-representations)
   - [Tate twists, duals, and tensors](#22-tate-twists-duals-and-tensors)
   - [Lisse sheaves and closed points](#23-lisse-sheaves-and-closed-points)
   - [Mixed objects and strict weight separation](#24-mixed-objects-and-strict-weight-separation)
3. [Polarizations and the positivity missing from duality](#3-polarizations-and-the-positivity-missing-from-duality)
   - [Degree as a positive polynomial](#31-degree-as-a-positive-polynomial)
   - [The Rosati trace form](#32-the-rosati-trace-form)
   - [Positive involutions on number fields](#33-positive-involutions-on-number-fields)
   - [Frobenius and Verschiebung](#34-frobenius-and-verschiebung)
4. [The Riemann hypothesis for abelian varieties and curves](#4-the-riemann-hypothesis-for-abelian-varieties-and-curves)
   - [Abelian varieties over a finite field](#41-abelian-varieties-over-a-finite-field)
   - [From a curve to its Jacobian](#42-from-a-curve-to-its-jacobian)
   - [The curve zeta function](#43-the-curve-zeta-function)
   - [The Hasse--Weil bounds](#44-the-hasse--weil-bounds)
5. [Pure lisse sheaves on curves](#5-pure-lisse-sheaves-on-curves)
   - [Why surface cohomology leads back to a curve](#51-why-surface-cohomology-leads-back-to-a-curve)
   - [Local purity and the middle extension](#52-local-purity-and-the-middle-extension)
   - [The tensor-power estimate](#53-the-tensor-power-estimate)
   - [The curve-sheaf Riemann hypothesis](#54-the-curve-sheaf-riemann-hypothesis)
6. [Weights on open curves](#6-weights-on-open-curves)
   - [Boundary invariants and coinvariants](#61-boundary-invariants-and-coinvariants)
   - [Compact support and ordinary support](#62-compact-support-and-ordinary-support)
   - [Mixedness and the interior group](#63-mixedness-and-the-interior-group)
   - [Examples that fix the normalizations](#64-examples-that-fix-the-normalizations)
7. [Hyperplane sections and weak Lefschetz](#7-hyperplane-sections-and-weak-lefschetz)
   - [Why an ample class should control cohomology](#71-why-an-ample-class-should-control-cohomology)
   - [Affine vanishing in dimension two](#72-affine-vanishing-in-dimension-two)
   - [Weak Lefschetz for a surface section](#73-weak-lefschetz-for-a-surface-section)
   - [Restriction on connected Picard varieties](#74-restriction-on-connected-picard-varieties)
8. [Hard Lefschetz in dimensions one and two](#8-hard-lefschetz-in-dimensions-one-and-two)
   - [The Lefschetz operator and its twists](#81-the-lefschetz-operator-and-its-twists)
   - [Curves](#82-curves)
   - [The degree-zero and degree-four parts of a surface](#83-the-degree-zero-and-degree-four-parts-of-a-surface)
   - [The middle odd degrees of a surface](#84-the-middle-odd-degrees-of-a-surface)
9. [Lefschetz pencils on surfaces](#9-lefschetz-pencils-on-surfaces)
   - [Constructing the pencil](#91-constructing-the-pencil)
   - [Ordinary quadratic singularities and vanishing cycles](#92-ordinary-quadratic-singularities-and-vanishing-cycles)
   - [The direct-image decomposition](#93-the-direct-image-decomposition)
   - [Where the primitive middle cohomology sits](#94-where-the-primitive-middle-cohomology-sits)
10. [The Riemann hypothesis for smooth proper surfaces](#10-the-riemann-hypothesis-for-smooth-proper-surfaces)
   - [The pencil contribution has weight two](#101-the-pencil-contribution-has-weight-two)
   - [Blowing up does not change the question](#102-blowing-up-does-not-change-the-question)
   - [Purity in all five degrees](#103-purity-in-all-five-degrees)
   - [The surface zeta function and point bounds](#104-the-surface-zeta-function-and-point-bounds)
11. [Mixed weights on open surfaces](#11-mixed-weights-on-open-surfaces)
   - [Normal-crossings boundary complexes](#111-normal-crossings-boundary-complexes)
   - [Weight inequalities](#112-weight-inequalities)
   - [Interior cohomology](#113-interior-cohomology)
   - [Singular and semistable warnings](#114-singular-and-semistable-warnings)
12. [Correspondences and pure weight-two summands](#12-correspondences-and-pure-weight-two-summands)
   - [Frobenius-compatible projectors](#121-frobenius-compatible-projectors)
   - [Adjoints and orthogonal decompositions](#122-adjoints-and-orthogonal-decompositions)
   - [Isolating a constituent](#123-isolating-a-constituent)
   - [The Shimura-surface application](#124-the-shimura-surface-application)
13. [Families, good reduction, and coefficient changes](#13-families-good-reduction-and-coefficient-changes)
   - [Smooth proper families](#131-smooth-proper-families)
   - [Good reduction](#132-good-reduction)
   - [Changing the auxiliary prime](#133-changing-the-auxiliary-prime)
   - [A normalization and hypothesis audit](#134-a-normalization-and-hypothesis-audit)
14. [The low-dimensional weight package](#14-the-low-dimensional-weight-package)
   - [The complete theorem](#141-the-complete-theorem)
   - [How the ingredients depend on one another](#142-how-the-ingredients-depend-on-one-another)
   - [Final synthesis](#143-final-synthesis)

## 1. The size hidden in a Frobenius eigenvalue

### 1.1 The problem left by the trace formula

Let $X$ be a variety over $k=\mathbf F_q$, and let $F$ denote geometric Frobenius on geometric étale cohomology. The trace formula developed earlier gives

$$
\#X(\mathbf F_{q^n})
=\sum_i(-1)^i\operatorname{Tr}
\left(F^n\mid H_c^i(\bar X,\mathbf Q_\ell)\right). \tag{1.1}
$$

This identity organizes every extension-field count into finitely many eigenvalues. It does not say how large those eigenvalues are. Duality gives the reciprocal relation $\alpha\leftrightarrow q^d/\alpha$ on a smooth proper $d$-fold, but reciprocal pairs can lie arbitrarily far from the circle of radius $q^{d/2}$. The missing assertion is a positivity theorem.

For a smooth proper variety the expected answer is exquisitely simple: an eigenvalue in $H^i$ has complex absolute value $q^{i/2}$. The integer $i$ is its **weight**. This statement simultaneously explains the scale of the error in point counting, makes zeta zeros and poles lie on prescribed circles, and prevents a correspondence projector in $H^2$ from mixing its desired arithmetic representation with boundary classes of another weight.

This book proves that answer for smooth proper curves and surfaces and proves hard Lefschetz in the same range. The curve proof passes through the Jacobian and the positivity of the Rosati involution. The surface proof uses an ample pencil: its fibers are curves, and the new part of $H^2$ becomes degree-one cohomology of the base with a pure degree-one coefficient sheaf. Thus the difficult two-dimensional assertion is reduced, without circularity, to a precise theorem about lisse sheaves on curves.

### 1.2 Standing conventions

Fix a prime $\ell\ne p=\operatorname{char}k$ and an algebraic closure $\bar k$. All cohomology is geometric étale cohomology with $\mathbf Q_\ell$ coefficients unless another coefficient ring is displayed. A variety is separated and of finite type. The words smooth, proper, projective, and geometrically connected are never implicit.

Arithmetic Frobenius is $\varphi:a\mapsto a^q$ in $\operatorname{Gal}(\bar k/k)$; geometric Frobenius is $F=\varphi^{-1}$ on geometric cohomology. With this convention,

$$
F\mid \mathbf Q_\ell(1)=q^{-1},
\qquad
F\mid \mathbf Q_\ell(-1)=q. \tag{1.2}
$$

Consequently the fundamental class of a smooth proper curve lies in $H^2=\mathbf Q_\ell(-1)$ and has eigenvalue $q$, while that of a surface lies in $H^4=\mathbf Q_\ell(-2)$ and has eigenvalue $q^2$. These two checks will detect every possible inversion error below.

The prior duality theory supplies perfect pairings

$$
H^i(\bar X,\mathbf Q_\ell)\times
H^{2d-i}(\bar X,\mathbf Q_\ell(d))\longrightarrow\mathbf Q_\ell, \tag{1.3}
$$

and compatibility with cycle classes, transpose correspondences, and trace. The prior trace theory supplies (1.1), Künneth, rationality, and the functional equation, but no absolute-value estimate. Projective geometry supplies high powers of ample line bundles and smooth hyperplane sections. The Jacobian theory supplies

$$
H^1(\bar C,\mathbf Q_\ell)
\simeq V_\ell J_C^\vee \tag{1.4}
$$

with its canonical principal polarization. We will recall each ingredient at the point where its normalization matters.

### 1.3 Algebraic numbers and Weil numbers

An algebraic number $\alpha$ is a **$q$-Weil number of weight $w$** if for every embedding $\iota:\mathbf Q(\alpha)\hookrightarrow\mathbf C$,

$$
|\iota(\alpha)|=q^{w/2}. \tag{1.5}
$$

The definition uses all embeddings. The assertion $|\alpha|=q^{w/2}$ after one chosen embedding is not invariant under the rational characteristic polynomial and is too weak for arithmetic applications. Weights may be integers in the geometric situations here, though the definition makes sense for rational $w$.

Examples fix the scale. The numbers $1$ and roots of unity have weight $0$; $q$ has weight $2$; if $\alpha$ has weight $w$, then $q^{-m}\alpha$ has weight $w-2m$. A reciprocal partner $q^d/\alpha$ has weight $2d-w$. Thus duality predicts the correct complementary weight if, but only if, purity is already known on one side.

Frobenius characteristic polynomials arising below have algebraic coefficients and in the constant-coefficient smooth proper cases have rational, indeed integral, coefficients. Hence it makes sense to speak about every complex embedding of every root. We never choose an isomorphism $\overline{\mathbf Q}_\ell\simeq\mathbf C$ as part of the data; such an isomorphism is only a device for measuring a root.

### 1.4 The route through the proof

There are four logically distinct stages.

First, polarization converts the geometric positivity of an ample divisor on an abelian variety into positivity of the Rosati trace form. Frobenius and Verschiebung are Rosati adjoints and their product is multiplication by $q$. Positive-involution linear algebra then forces every Frobenius conjugate to have absolute value $\sqrt q$. Applied to a Jacobian, this proves the curve Riemann hypothesis and the Hasse--Weil bound.

Second, a tensor-power argument on a curve promotes pointwise purity of a lisse sheaf to purity of its parabolic degree-one cohomology. This is the low-dimensional sheaf theorem needed later. Its hypotheses are stated so that $R^1$ of a smooth family of curves satisfies them by the first stage.

Third, an ample line bundle on a surface produces both a smooth section and a Lefschetz pencil. The smooth section controls $H^1$ and proves hard Lefschetz. The pencil places primitive $H^2$ inside parabolic $H^1$ of the base with coefficient $R^1$ of the fibers. The curve-sheaf theorem then gives weight two.

Finally, localization along normal-crossings boundaries gives the weight inequalities for open curves and surfaces. The image of compactly supported in ordinary cohomology is pure. Frobenius-compatible correspondence projectors preserve this pure middle piece, which is exactly the mechanism used to isolate weight-two constituents on smooth proper or interior Shimura-surface cohomology.

## 2. Weights and their elementary calculus

### 2.1 Pure representations

Let $V$ be a finite-dimensional $\mathbf Q_\ell$-vector space with an automorphism $F$ whose characteristic polynomial has algebraic coefficients. We call $V$ **pure of weight $w$** if every eigenvalue of $F$ is a $q$-Weil number of weight $w$. Semisimplicity is not part of the definition. A Jordan block changes traces by polynomial factors in $n$ but does not change the weights of its eigenvalues.

Purity is stable under subquotients: the characteristic polynomial on an invariant subspace and quotient divides that on $V$ after extension to an algebraic closure. It is also stable under extensions of pure objects of the same weight. It is not stable under an arbitrary direct sum of different weights; such a sum is mixed.

If $X$ is smooth proper and geometrically connected, the theorem to be proved is

$$
H^i(\bar X,\mathbf Q_\ell)
\text{ is pure of weight }i. \tag{2.1}
$$

For $i=0$ this follows from geometric connectedness. For $i=2d$ it follows from the trace orientation. The content lies between those endpoints.

### 2.2 Tate twists, duals, and tensors

The elementary rules are indispensable because a missing sign in the twist changes a weight by four between a group and its purported dual.

**Proposition 2.1 (weight calculus).** If $V$ and $W$ are pure of weights $v$ and $w$, then:

1. $V(m)=V\otimes\mathbf Q_\ell(m)$ is pure of weight $v-2m$;
2. $V^\vee$ is pure of weight $-v$;
3. $V\otimes W$ is pure of weight $v+w$;
4. $\operatorname{Hom}(V,W)$ is pure of weight $w-v$;
5. $\bigwedge^rV$ and $\operatorname{Sym}^rV$ are pure of weight $rv$ when nonzero.

**Proof.** Over $\overline{\mathbf Q}_\ell$, tensor eigenvalues are products, dual eigenvalues are inverses, and the twist contributes $q^{-m}$. Apply every complex embedding and multiply absolute values. Exterior and symmetric powers have eigenvalues equal to products of $r$ eigenvalues, counted with their allowed multiplicities. $\square$

Poincaré duality (1.3) therefore predicts that if $H^i$ has weight $i$, then $H^{2d-i}(d)$ has weight $-i$, exactly the weight of its dual. In untwisted form the complementary group has weight $2d-i$.

### 2.3 Lisse sheaves and closed points

Let $U/\mathbf F_q$ be a smooth geometrically connected curve, and let $\mathcal F$ be a lisse $\overline{\mathbf Q}_\ell$-sheaf. For a closed point $x$ of degree $r$, geometric Frobenius $F_x$ acts on the stalk $\mathcal F_{\bar x}$. The sheaf is **punctually pure of weight $w$** if every eigenvalue $\alpha$ of every $F_x$ satisfies

$$
|\iota(\alpha)|=q^{rw/2}=(\#k(x))^{w/2} \tag{2.2}
$$

for every complex embedding. The factor $r$ is essential: $F_x$ is geometric Frobenius for $\mathbf F_{q^r}$.

A lisse sheaf can be pure without being constant. If $f:Y\to U$ is a smooth proper family of curves, then

$$
\mathcal V=R^1f_*\mathbf Q_\ell \tag{2.3}
$$

is punctually pure of weight $1$ once the curve theorem has been proved: proper base change identifies $\mathcal V_{\bar x}$ with $H^1(Y_{\bar x},\mathbf Q_\ell)$, and (2.2) is precisely the curve Riemann hypothesis over $k(x)$. This observation is the bridge from curves to surfaces.

For a smooth proper map of relative dimension $r$, $R^if_*\mathbf Q_\ell$ is lisse by smooth proper base change. Pointwise purity is a fiberwise assertion; it does not itself determine the weights of cohomology of the base with those coefficients. That additional step is Chapter 5.

### 2.4 Mixed objects and strict weight separation

A Frobenius module is **mixed** if it has a finite invariant filtration whose graded pieces are pure, possibly of different weights. It has weights $\le a$ if every graded weight is at most $a$, and weights $\ge a$ similarly. In the finite-dimensional setting this is equivalent to the same assertion about all eigenvalues; the filtration language becomes useful for sheaves and long exact sequences.

Two elementary consequences will repeatedly close exact-sequence arguments.

**Lemma 2.2 (weight separation).** Let $u:V\to W$ commute with Frobenius.

1. If $V$ has weights $\le a$ and $W$ has weights $>a$, then $u=0$.
2. If $V$ is pure of weight $a$ and $W$ has weights $\le a-1$, then every map $W\to V$ is zero.
3. The image of a map from weights $\le a$ to weights $\ge a$ is pure of weight $a$.

**Proof.** After extending scalars, decompose into generalized eigenspaces. A commuting map preserves the eigenvalue. Algebraic numbers of different weights cannot be equal because their complex absolute values differ. The first two claims follow. For the third, every eigenvalue in the image comes from the source and occurs in the target, so its weight is both at most and at least $a$. $\square$

This lemma does not claim that every mixed extension splits. It says only that Frobenius-equivariant morphisms cannot cross a strict weight gap. The distinction matters at a boundary, where nontrivial extensions between adjacent weights genuinely occur.

## 3. Polarizations and the positivity missing from duality

### 3.1 Degree as a positive polynomial

Duality makes transpose correspondences into adjoints, but an adjoint operation has metric force only when it is positive. On an abelian variety that positivity comes from an ample line bundle.

Let $A$ be a $g$-dimensional abelian variety over a field and let $L$ be ample. Its polarization is $\lambda=\lambda_L:A\to A^\vee$. For $u\in\operatorname{End}^0(A)$ put

$$
u^\dagger=\lambda^{-1}u^\vee\lambda. \tag{3.1}
$$

The earlier Jacobian theory established that this is an involutive anti-automorphism and is the adjoint on every rational Tate module. We now prove its positivity.

For an integral endomorphism $u$ and an integer $n>0$, the bundle

$$
L^n\otimes u^*L
$$

is ample. Abelian Riemann--Roch and the theorem of the cube give

$$
\deg(n+u^\dagger u)
=\frac{1}{\deg\lambda}
\deg\lambda_{L^n\otimes u^*L}
=\left(
\frac{(nc_1(L)+u^*c_1(L))^g}{c_1(L)^g}
\right)^2. \tag{3.2}
$$

Here degree means the degree of an isogeny; both sides are polynomial identities, so (3.2) remains meaningful when a particular $n+u^\dagger u$ is not invertible. Expanding the intersection polynomial, the coefficient of $n^{2g-1}$ is a positive multiple of

$$
c_1(L)^{g-1}\cdot u^*c_1(L). \tag{3.3}
$$

If $u\ne0$, its image is a positive-dimensional abelian subvariety. Restricting $L$ there is ample, and intersecting with general translates of ample divisors shows (3.3) is positive. This is the only geometric positivity input: the intersection of ample divisors has positive degree on every positive-dimensional image.

### 3.2 The Rosati trace form

Let $\operatorname{Tr}_{\mathrm{red}}$ denote the reduced trace of the semisimple algebra $\operatorname{End}^0(A)$. It may equivalently be recovered, up to one fixed positive factor on each simple component, from the coefficient of $T^{2g-1}$ in the degree polynomial $\deg(T-u)$.

**Theorem 3.1 (Rosati positivity).** For every nonzero $u\in\operatorname{End}^0(A)$,

$$
\operatorname{Tr}_{\mathrm{red}}(uu^\dagger)>0. \tag{3.4}
$$

Thus $(u,v)\mapsto\operatorname{Tr}_{\mathrm{red}}(uv^\dagger)$ is a positive-definite rational bilinear form.

**Proof.** Clear denominators, so $u$ is integral. Apply (3.2) with $u$ in place of the second summand and compare the coefficient immediately below the leading coefficient. The characteristic polynomial defining degree shows that this coefficient is a fixed positive multiple of $\operatorname{Tr}_{\mathrm{red}}(u^\dagger u)$. The intersection expansion shows it is a fixed positive multiple of (3.3), hence positive for $u\ne0$. Cyclicity of reduced trace gives $\operatorname{Tr}_{\mathrm{red}}(u^\dagger u)=\operatorname{Tr}_{\mathrm{red}}(uu^\dagger)$. Bilinearity follows from the trace, symmetry from

$$
\operatorname{Tr}_{\mathrm{red}}(uv^\dagger)
=\operatorname{Tr}_{\mathrm{red}}((uv^\dagger)^\dagger)
=\operatorname{Tr}_{\mathrm{red}}(vu^\dagger),
$$

and positivity proves nondegeneracy. $\square$

The proof also explains why an arbitrary self-duality is insufficient. Replacing an ample $L$ by its inverse changes the sign of the polarization and destroys (3.4), even though the underlying map to the dual remains an isogeny.

### 3.3 Positive involutions on number fields

The Frobenius argument uses only the following linear-algebraic consequence of positivity.

**Lemma 3.2.** Let $K$ be a number field with an involution $a\mapsto a^*$ such that

$$
\operatorname{Tr}_{K/\mathbf Q}(aa^*)>0
\quad\text{for }a\ne0. \tag{3.5}
$$

Then for every embedding $\sigma:K\hookrightarrow\mathbf C$,

$$
\sigma(a^*)=\overline{\sigma(a)}. \tag{3.6}
$$

**Proof.** Extend $K\otimes_\mathbf Q\mathbf R$ into its real and complex factors. The trace form is the sum of the factor trace forms. Positivity rules out an involution exchanging two different factors: choosing opposite large elements in the exchanged factors would make the quadratic form negative. On a real factor the only involution is the identity. On a complex factor a real-algebra involution is either identity or complex conjugation; identity gives $\operatorname{Tr}_{\mathbf C/\mathbf R}(z^2)$, negative at $z=i$, so conjugation is forced. This is (3.6) in every factor. $\square$

If $K$ is a commutative $\dagger$-stable subalgebra of $\operatorname{End}^0(A)$, Theorem 3.1 restricts to (3.5). Therefore Rosati acts as complex conjugation under every complex embedding of $K$.

### 3.4 Frobenius and Verschiebung

Let $A/\mathbf F_q$. The relative $q$-power Frobenius endomorphism is denoted $\pi:A\to A$. There is a unique isogeny $V:A\to A$, the **Verschiebung**, satisfying

$$
V\pi=\pi V=[q]. \tag{3.7}
$$

One constructs $V$ by dualizing Frobenius on $A^\vee$ and using biduality; on finite prime-to-$p$ torsion, Frobenius is invertible and $V=q\pi^{-1}$, which determines the homomorphism by density.

A polarization defined over $\mathbf F_q$ always exists. Start with an
ample line bundle over $\bar k$; it is defined over some
$\mathbf F_{q^r}$. The tensor product of its $r$ Frobenius conjugates is
ample, and cyclic permutation of the factors gives it a descent datum.
Rigidification at the identity removes the scalar ambiguity in that
datum. Its associated polarization therefore descends to $\mathbf F_q$.

For such a polarization $\lambda$, functoriality of the Poincaré bundle gives

$$
\pi^\vee\lambda=\lambda V.
$$

Indeed both maps correspond to pulling the inducing ample bundle through Frobenius and using the norm along Frobenius; the composite in either order is the $q$th tensor-power operation on the associated biextension. Consequently

$$
\pi^\dagger=V,
\qquad
\pi\pi^\dagger=[q]. \tag{3.8}
$$

The distinction between the geometric endomorphism $\pi$ and the cohomological geometric Frobenius $F$ causes no inversion here. Arithmetic Galois Frobenius acts on $T_\ell A$ as $\pi$, while $H^1\simeq V_\ell A^\vee$ is contragredient and geometric Frobenius is inverse arithmetic Galois Frobenius. The two inversions cancel, so $F$ on $H^1$ and $\pi$ on $V_\ell A$ have the same characteristic polynomial.

## 4. The Riemann hypothesis for abelian varieties and curves

### 4.1 Abelian varieties over a finite field

We can now turn the algebraic identity (3.8) into an Archimedean absolute value.

**Theorem 4.1 (abelian Frobenius theorem).** Let $A/\mathbf F_q$ be an abelian variety. Every root $\alpha$ of

$$
P_A(T)=\det(T-\pi\mid V_\ell A)
$$
is an algebraic integer, $P_A(T)\in\mathbf Z[T]$ is independent of $\ell\ne p$, and

$$
|\iota(\alpha)|=\sqrt q \tag{4.1}
$$

for every embedding $\iota:\mathbf Q(\alpha)\hookrightarrow\mathbf C$.

**Proof.** Multiplication by an integral endomorphism preserves $T_\ell A$, so the roots are integral over $\mathbf Z_\ell$ for every $\ell\ne p$. The degree polynomial $n\mapsto\deg(n-\pi)$ is a monic integer polynomial of degree $2g$ and agrees with $\det(n-\pi\mid T_\ell A)$ for infinitely many integers $n$ prime to the relevant degrees. Hence it is $P_A(n)$, proving integrality and independence of $\ell$.

The commutative algebra $K=\mathbf Q[\pi]$ is stable under Rosati because $\pi^\dagger=q/\pi$. Its quotient by any minimal-polynomial factor is a number field with the induced positive involution. Lemma 3.2 gives

$$
\overline{\iota(\alpha)}
=\iota(\alpha^\dagger)
=\iota(q/\alpha).
$$

Multiplication by $\iota(\alpha)$ yields $|\iota(\alpha)|^2=q$. This proves (4.1), including all conjugates and repeated roots. $\square$

The theorem also implies semisimplicity of $\pi$ on $V_\ell A$. Indeed a positive involution makes the commutative algebra generated by the normal element $\pi$, satisfying $\pi\pi^\dagger=\pi^\dagger\pi$, a product of fields; a nonzero nilpotent would have positive norm $\operatorname{Tr}(uu^\dagger)$ but zero trace in every regular representation. Semisimplicity is useful for orthogonal projectors, though purity itself did not require it.

### 4.2 From a curve to its Jacobian

Let $C/\mathbf F_q$ be smooth, proper, and geometrically connected of genus $g$, and let $J=J_C$. Kummer theory and the canonical theta polarization identify

$$
H^1(\bar C,\mathbf Q_\ell)
\simeq V_\ell J^\vee. \tag{4.2}
$$

As explained after (3.8), geometric Frobenius on the left has the same characteristic polynomial as the Frobenius endomorphism on $V_\ell J$. Theorem 4.1 therefore proves:

**Theorem 4.2 (curve Riemann hypothesis).** Every eigenvalue of geometric Frobenius on $H^1(\bar C,\mathbf Q_\ell)$ is a $q$-Weil number of weight $1$.

Together with $H^0=\mathbf Q_\ell$ and $H^2=\mathbf Q_\ell(-1)$, this proves purity of weight $i$ in every degree $i$ for a smooth proper curve.

No rational point on $C$ was used. The Jacobian and its canonical polarization descend without choosing an Abel--Jacobi base point. This matters for curves of positive index over $\mathbf F_q$, even though a sufficiently large finite extension always supplies points.

### 4.3 The curve zeta function

The trace formula and rationality give

$$
Z(C,t)=\frac{P_1(t)}{(1-t)(1-qt)},
\qquad
P_1(t)=\det(1-tF\mid H^1(\bar C,\mathbf Q_\ell)). \tag{4.3}
$$

The polynomial $P_1$ has degree $2g$, integral coefficients, and roots $\alpha_j^{-1}$ where every $\alpha_j$ has absolute value $\sqrt q$. Poincaré duality pairs $\alpha_j$ with $q/\alpha_j$ and yields

$$
P_1(t)=q^gt^{2g}P_1(1/(qt)). \tag{4.4}
$$

Thus the zeta zeros lie on $|t|=q^{-1/2}$. In the variable $s$ with $t=q^{-s}$, they lie on $\operatorname{Re}s=1/2$. This is the Riemann-hypothesis statement for the curve, not merely the reciprocal functional equation: (4.4) alone would allow one zero inside and its partner outside the circle.

### 4.4 The Hasse--Weil bounds

Writing the eigenvalues as $\alpha_1,\ldots,\alpha_{2g}$, the trace formula is

$$
\#C(\mathbf F_{q^n})
=q^n+1-\sum_{j=1}^{2g}\alpha_j^n. \tag{4.5}
$$

Taking complex absolute values and using $|\alpha_j^n|=q^{n/2}$ gives the full extension-field estimate

$$
\boxed{
\left|\#C(\mathbf F_{q^n})-(q^n+1)\right|
\le 2gq^{n/2}.
} \tag{4.6}
$$

For $n=1$ this is the Hasse--Weil bound. It implies, for example, that $C$ has an $\mathbf F_{q^n}$-point whenever $q^n+1>2gq^{n/2}$. The coefficient $2g$ is the dimension of $H^1$, not an artifact of a chosen plane model.

For an open curve $U=C\setminus D$ with $r$ geometric boundary points, subtracting $D(\mathbf F_{q^n})$ gives

$$
\left|\#U(\mathbf F_{q^n})-q^n\right|
\le 2gq^{n/2}+r+1. \tag{4.7}
$$

The bounded boundary term has weight zero; the oscillating Jacobian term has weight one. This simple example is the first appearance of mixed weights.

## 5. Pure lisse sheaves on curves

### 5.1 Why surface cohomology leads back to a curve

Suppose a surface is swept out by a one-parameter family of curves. The varying $H^1$ of the fibers forms a lisse sheaf $\mathcal V$ on the open part of the parameter curve. Fiberwise, Chapter 4 says that $\mathcal V$ has weight $1$. The part of surface $H^2$ which is not visibly generated by a fiber or an exceptional divisor appears as

$$
H^1(\text{parameter curve},\mathcal V).
$$

The required surface weight $2$ is therefore the rule “cohomological degree one adds one to the weight of a pure sheaf.” That rule is the deepest input of the surface proof. We establish precisely the curve form needed here.

Let $j:U\hookrightarrow C$ be a dense open immersion into a smooth proper geometrically connected curve over $\mathbf F_q$. For a lisse sheaf $\mathcal F$ on $U$, define its **parabolic cohomology** by

$$
H_p^1(U,\mathcal F)
=H^1(\bar C,j_*\mathcal F)
=\operatorname{im}\left(
H_c^1(\bar U,\mathcal F)\longrightarrow
H^1(\bar U,\mathcal F)
\right). \tag{5.1}
$$

The second equality follows from the localization sequences for $j_!\mathcal F\to Rj_*\mathcal F$ and the fact that the cone is supported on finitely many points. Parabolic cohomology discards the purely local boundary classes while retaining global monodromy.

### 5.2 Local purity and the middle extension

The coefficient theorem requires an arithmetic condition as well as a complex absolute-value condition. We call $\mathcal F$ **geometric-pure of weight $w$** when:

1. it is semisimple and punctually pure of weight $w$;
2. the characteristic polynomial of every $F_x$ has coefficients in one number field;
3. on every geometrically irreducible constituent, the determinant has
   finite order on the geometric fundamental group after removal of its
   constant rank-one factor (a Tate power in the applications here).
4. at the boundary it is tamely ramified, or more generally its break
   filtration is finite and satisfies the conductor estimate (5.5).

The third condition means that the determinant is a finite character times a character pulled back from $\operatorname{Gal}(\bar k/k)$. It is stable under finite extension of the ground field. The fourth keeps the conductor bookkeeping explicit; all Lefschetz-pencil sheaves below have the tame transvections (9.2). For $R^1f_*\mathbf Q_\ell$ of a smooth proper family of genus-$g$ curves, the symplectic pairing has multiplier $\mathbf Q_\ell(-1)$, so its determinant is $\mathbf Q_\ell(-g)$ times a finite character. Thus these are exactly the conditions available in a Lefschetz pencil; no unproved companion theorem is being assumed.

At $x\in C\setminus U$, the stalk $(j_*\mathcal F)_{\bar x}$ is the inertia-invariant subspace $\mathcal F_{\bar\eta}^{I_x}$. If inertia is unipotent with logarithm $N_x$, it is $\ker N_x$. Passing from $j_!$ to $j_*$ removes coinvariant boundary classes. The middle extension is therefore the correct object for a pure global statement.

### 5.3 The tensor-power estimate

We isolate the analytic-algebraic heart of the curve theorem. Its proof is included because applying it as a slogan would hide the only genuine size estimate between the curve and surface cases.

**Lemma 5.1 (tensor-power estimate).** Let $U/\mathbf F_q$ be a smooth geometrically connected curve and let $\mathcal F$ be geometrically irreducible, geometric-pure of weight $w$. Every reciprocal root of

$$
L_p(U,\mathcal F,t)
=\det(1-tF\mid H_p^1(U,\mathcal F))
$$

has absolute value $q^{(w+1)/2}$ under every complex embedding.

**Proof strategy.** Rationality alone places no circle around the roots. The extra information is that tensoring a sheaf with its dual creates nonnegative local traces. Applying this observation to arbitrarily high tensor constructions amplifies any eigenvalue off the expected circle until it contradicts the linear growth of the conductor.

Fix a complex embedding of the common coefficient field and divide every local eigenvalue formally by $(\#k(x))^{w/2}$. This changes only absolute values, so we may prove the estimate with $w=0$. Put $r=\operatorname{rank}\mathcal F$ and

$$
\mathcal E=\mathcal F\otimes\mathcal F^\vee.
$$

For every closed point $x$ and $m\ge1$, purity gives

$$
\operatorname{Tr}(F_x^m\mid\mathcal E_{\bar x})
=\left|\operatorname{Tr}(F_x^m\mid\mathcal F_{\bar x})\right|^2\ge0. \tag{5.2}
$$

The equality follows because the dual eigenvalues are inverses and, on the unit circle, inverse equals complex conjugate. Hence the logarithmic coefficients of the Euler product of $\mathcal E$ are nonnegative.

Schur's lemma gives a single constant subsheaf in $\mathcal E$. Split it off semisimply:

$$
\mathcal E=\mathbf Q_\ell\oplus\mathcal E_0. \tag{5.3}
$$

The trace formula on $U$ writes the logarithmic coefficient at $t^n$ as an alternating sum of traces on $H_c^i$. The degree-zero and degree-two terms of the constant summand account for the simple pole at $t=q^{-1}$; local invariant and Swan conductors bound

$$
\dim H_c^1(U,\mathcal G)
\le (2g(C)-2+\#(C\setminus U))\operatorname{rank}\mathcal G
+\operatorname{cond}(\mathcal G) \tag{5.4}
$$

for every tensor construction $\mathcal G$ in $\mathcal F$. Formula (5.4) follows directly from the Euler--Poincaré formula: tame punctures contribute the codimension of inertia invariants and wild punctures contribute the Swan conductor. Under tensor product, each local conductor is at most

$$
\operatorname{rank}(\mathcal G_2)\operatorname{cond}(\mathcal G_1)
+\operatorname{rank}(\mathcal G_1)\operatorname{cond}(\mathcal G_2), \tag{5.5}
$$

because the break of a tensor is at most the larger break and codimensions satisfy the analogous elementary inequality.

Now apply (5.2)--(5.5) to the Schur functors occurring in $\mathcal E^{\otimes m}$. The character identity

$$
|z_1+\cdots+z_r|^{2m}
=\sum_\lambda c_{\lambda,m}
\operatorname{Tr}(s_\lambda(F_x))
\overline{\operatorname{Tr}(s_\lambda(F_x))},
\qquad c_{\lambda,m}\ge0, \tag{5.6}
$$

is the decomposition of a tensor power into irreducible symmetric-group characters. Positivity prevents cancellation between the summands. Rationality for every $s_\lambda(\mathcal F)$ and (5.4) show that the $2m$th power sum of any reciprocal root $\beta$ of parabolic cohomology is bounded, after the trace formula, by

$$
O_m(q^{n(m+1/2)})
$$

uniformly in $n$; the constant depends on $m$ and the fixed conductors but not on $n$. Taking $2m$th roots and then letting $m\to\infty$ gives

$$
|\beta|\le q^{1/2}. \tag{5.7}
$$

We spell out the coefficient comparison behind this bound. Write each Schur Euler product as an alternating quotient of its compactly supported cohomology polynomials. Its logarithmic coefficient of degree $n$ is

$$
\frac1n\sum_{x:\,\deg x\mid n}\deg(x)\,
\operatorname{Tr}\!\left(
F_x^{\,n/\deg x}\mid s_\lambda(\mathcal F_{\bar x})
\right). \tag{5.7a}
$$

After multiplying by its conjugate and summing with the nonnegative coefficients in (5.6), the closed-point terms become $2m$th absolute moments. The scalar summands of tensor powers contribute powers of the zeta function of $U$; their only largest pole is the known pole at $q^{-1}$. Every nonscalar summand contributes a numerator whose degree is bounded by (5.4). Cauchy's coefficient estimate on any circle $|t|=q^{-1-\varepsilon}$, followed by $\varepsilon\downarrow0$, gives

$$
\limsup_{n\to\infty}
\left|\sum_a\beta_a^n\right|^{1/n}
\le q^{1/2+1/(4m)}, \tag{5.7b}
$$

after taking the $2m$th tensor moment; here the $\beta_a$ run through the parabolic eigenvalues. The exponent $1/(4m)$ is the residual single curve pole divided by the $2m$th moment. The conductor bound ensures that the number and degrees of the remaining factors affect only the constant before taking the $n$th root. Letting $m$ tend to infinity gives (5.7).

For clarity about this decisive limit: if $|\beta|>q^{1/2}$, choose $m$ so large that $|\beta|^{2m}>q^{m+1/2+\varepsilon}$. In the sequence of power sums, a finite Vandermonde argument selects infinitely many $n$ for which the contribution of the roots of maximal modulus is at least a fixed multiple of that modulus to the $n$th power. This contradicts the displayed bound. Thus no cancellation among equal-modulus roots can evade (5.7).

Verdier duality identifies

$$
H_p^1(U,\mathcal F)^\vee
\simeq H_p^1(U,\mathcal F^\vee(1)). \tag{5.8}
$$

In untwisted form the pairing takes values in $\mathbf Q_\ell(-1)$. Thus if $\beta$ is an eigenvalue for $\mathcal F$, then $q/\beta$ is an eigenvalue on $H_p^1(U,\mathcal F^\vee)$. Apply (5.7) to $\mathcal F^\vee$, whose normalized local eigenvalues also have modulus one. The upper bound $|q/\beta|\le q^{1/2}$ gives $|\beta|\ge q^{1/2}$. Combined with (5.7), this proves equality. Restoring the factor of weight $w$ proves $|\beta|=q^{(w+1)/2}$. $\square$

The tensor-power step is sometimes called the main lemma, but its content is exactly the chain above: positivity of (5.2), conductor control, arbitrary Schur powers, a moment limit, and duality. Omitting any one of these steps leaves only the weaker bound of weight $w+2$ obtainable from the Euler product's elementary convergence region.

### 5.4 The curve-sheaf Riemann hypothesis

**Theorem 5.2 (pure sheaves on a curve).** Let $j:U\hookrightarrow C$ be as above and let $\mathcal F$ be geometric-pure of weight $w$. Then

$$
H^1(\bar C,j_*\mathcal F)=H_p^1(U,\mathcal F)
$$

is pure of weight $w+1$.

**Proof.** Decompose $\mathcal F$ into geometrically irreducible constituents after a finite extension of constants. Lemma 5.1 applies to each. Finite extension replaces $F$ by a power $F^a$ and $q$ by $q^a$, so the equality of absolute values descends to the original field. Parabolic cohomology commutes with direct sums, and descent may only permute equal-weight summands. Hence every eigenvalue has weight $w+1$. $\square$

Two variants will be used. A subquotient of a geometric-pure sheaf remains pure of the same weight. If local monodromy is Picard--Lefschetz unipotent, the theorem applies to $j_*\mathcal F$ exactly as stated; the invariant stalks at punctures do not add a separate weight-$w+1$ hypothesis. Finally, a constant summand is harmless: $H^1(C,\mathbf Q_\ell)$ has weight one by Chapter 4, and twisting and tensoring give the general constant case.

## 6. Weights on open curves

### 6.1 Boundary invariants and coinvariants

Purity on the middle extension does not mean that ordinary or compactly supported cohomology of $U$ is pure. The boundary contributes lower-dimensional pieces.

For $D=C\setminus U$ and lisse $\mathcal F$, the triangle

$$
j_!\mathcal F\longrightarrow Rj_*\mathcal F
\longrightarrow i^*Rj_*\mathcal F\longrightarrow
$$

has a cone supported on $D$. At a geometric boundary point $x$, its degree-zero part is $\mathcal F^{I_x}$ and its degree-one part is an inertia coinvariant term, with a $(-1)$ twist in the tame unipotent case. Thus the long exact sequence separates global parabolic classes from local invariant and vanishing-cycle classes.

For constant coefficients the calculation is elementary:

$$
0\longrightarrow\mathbf Q_\ell
\longrightarrow\mathbf Q_\ell^{D(\bar k)}
\longrightarrow H_c^1(\bar U,\mathbf Q_\ell)
\longrightarrow H^1(\bar C,\mathbf Q_\ell)
\longrightarrow0. \tag{6.1}
$$

The quotient $\mathbf Q_\ell^{D(\bar k)}/\mathbf Q_\ell$ has weight zero, while $H^1(\bar C)$ has weight one. Hence $H_c^1(U)$ is mixed of weights $0$ and $1$.

### 6.2 Compact support and ordinary support

For a geometric-pure sheaf of weight $w$, the curve theorem and the local monodromy filtration give

$$
H_c^i(\bar U,\mathcal F)\text{ has weights }\le w+i,
\qquad
H^i(\bar U,\mathcal F)\text{ has weights }\ge w+i. \tag{6.2}
$$

Here $H_c^0=0$ when $U$ is nonproper and has no compact component. The top compactly supported group is dual to $H^0(\mathcal F^\vee(1))$ and has the predicted weight $w+2$ on its nonzero pure constituents.

To prove (6.2), filter the boundary complex by inertia invariants and successive images of the nilpotent monodromy operator. Each application of $N$ changes the Tate twist by $-1$, hence the weight by $2$, while the monodromy filtration index changes oppositely. The invariant quotient entering $j_*$ has weights at least $w$, and the quotient entering $j_!/j_*$ has weights at most $w$. Combine these local statements with Theorem 5.2 in the localization long exact sequences. Ordinary and compact inequalities are dual by (5.8), so it is enough to verify one side.

In the tame Picard--Lefschetz situation used for pencils, $N^2=0$ and this filtration has only two steps. The claim then follows immediately from

$$
0\subset\operatorname{im}N\subset\ker N\subset\mathcal F_{\bar\eta}
$$

and $N:\mathcal F\to\mathcal F(-1)$.

### 6.3 Mixedness and the interior group

Define

$$
H_!^i(U,\mathcal F)
=\operatorname{im}\left(H_c^i(\bar U,\mathcal F)\to
H^i(\bar U,\mathcal F)\right). \tag{6.3}
$$

By (6.2) the source has weights at most $w+i$ and the target weights at least $w+i$. Lemma 2.2 therefore proves:

**Corollary 6.1.** The interior group $H_!^i(U,\mathcal F)$ is pure of weight $w+i$.

For a curve and $i=1$, this is the parabolic group of (5.1). The formulation by image is more robust in later surface applications because correspondences preserve compact and ordinary cohomology and hence preserve their image.

### 6.4 Examples that fix the normalizations

For $U=\mathbf A^1$, $H_c^2=\mathbf Q_\ell(-1)$ has weight two and all other compactly supported groups vanish. For $U=\mathbf G_m$,

$$
H_c^1(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell,
\qquad
H_c^2(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell(-1),
$$

of weights zero and two. The trace formula gives $q^n-1$. It would be wrong to assign weight one to $H_c^1$ merely because its cohomological degree is one; proper smoothness is what forces equality of weight and degree.

For a Kummer sheaf of finite order on $\mathbf G_m$, the stalks have weight zero. If the character is nontrivial at both ends, its parabolic $H^1$ is pure of weight one. A missing ramification condition can create invariant boundary stalks of weight zero, but those lie outside the parabolic image. These examples explain why Theorem 5.2 is stated for $j_*\mathcal F$ rather than for all of $H_c^1(U,\mathcal F)$.

## 7. Hyperplane sections and weak Lefschetz

### 7.1 Why an ample class should control cohomology

Let $X$ be a smooth projective geometrically connected surface over an algebraically closed field, and let $L$ be ample. After replacing $L$ by a high power, projective geometry embeds $X$ and supplies a smooth connected divisor $i:C\hookrightarrow X$ in $|L|$. Its cycle class

$$
\eta=c_1(L)\in H^2(X,\mathbf Q_\ell(1)) \tag{7.1}
$$

acts by cup product. The identity

$$
i_*i^*(x)=x\smile\eta \tag{7.2}
$$

is the self-intersection formula. It turns restriction to a curve and Gysin return from that curve into the Lefschetz operator.

Weak Lefschetz says that a sufficiently positive section captures low-degree cohomology. In dimension two it asserts that $H^0(X)\to H^0(C)$ is an isomorphism and $H^1(X)\to H^1(C)$ is injective. We prove just this range, which is all hard Lefschetz needs.

### 7.2 Affine vanishing in dimension two

The complement $U=X\setminus C$ is affine because $C$ is an ample effective divisor. For a smooth affine surface,

$$
H^r(\bar U,\mathbf Q_\ell)=0\quad(r>2),
\qquad
H_c^r(\bar U,\mathbf Q_\ell)=0\quad(r<2). \tag{7.3}
$$

Here is the low-dimensional proof. Choose a finite affine map from $U$ to $\mathbf A^2$ after a generic linear projection. Stratify the branch curve so that over each stratum the direct image of the constant sheaf is lisse. The affine line has cohomological dimension one for prime-to-$p$ torsion, proved by normalizing a compactification and using the curve localization sequence. Applying this twice to the two coordinates gives cohomological dimension two for $U$. Passage from finite coefficients to $\mathbf Q_\ell$ preserves the bound. Compact-support vanishing follows from Poincaré duality for the smooth surface.

The localization triangle for $U\hookrightarrow X$ and purity for $C\hookrightarrow X$ contains

$$
H_c^r(U)\longrightarrow H^r(X)\xrightarrow{i^*}H^r(C)
\longrightarrow H_c^{r+1}(U). \tag{7.4}
$$

For $r=0$, the outer groups in the relevant range show that connectedness passes to $C$. For $r=1$, $H_c^1(U)=0$, so restriction is injective. This proves weak Lefschetz in the required degrees.

### 7.3 Weak Lefschetz for a surface section

We record the result with its descent qualifications.

**Theorem 7.1 (weak Lefschetz for surfaces).** Let $X$ be a smooth projective geometrically connected surface over a field $k$ with $\ell$ invertible, and let $C$ be a smooth geometrically connected member of a sufficiently high power of an ample linear system. Then

$$
H^0(\bar X,\mathbf Q_\ell)\xrightarrow{\sim}H^0(\bar C,\mathbf Q_\ell),
\qquad
H^1(\bar X,\mathbf Q_\ell)\hookrightarrow H^1(\bar C,\mathbf Q_\ell). \tag{7.5}
$$

If $C$ is defined over $k$, the maps are Galois equivariant. If a smooth member exists only after a finite separable extension, (7.5) and all geometric hard-Lefschetz conclusions descend because being an isomorphism can be checked after scalar extension.

Over a finite field a single hyperplane in a chosen system need not be smooth and rational. Passing to a high Veronese system and, if necessary, to a finite extension supplies one. This extension is harmless for geometric cohomology and purity: $F^a$ has the expected absolute values relative to $q^a$ exactly when $F$ does relative to $q$.

### 7.4 Restriction on connected Picard varieties

Injection alone does not make the composite $i_*i^*$ invertible; its image in $H^1(C)$ must be nondegenerate for the curve pairing. Positivity supplies that missing assertion through Picard varieties.

The connected Picard variety $P=\operatorname{Pic}^0_{X/k}$ is constructed by the same divisor-and-Hilbert method as the Jacobian: sufficiently positive divisors form an open in a Hilbert scheme, linear equivalence is represented by projective-space fibers, and the identity component of the quotient is a smooth proper group variety. Restriction of line bundles gives

$$
r:P\longrightarrow J_C. \tag{7.6}
$$

**Proposition 7.2.** For a sufficiently ample smooth $C$, the kernel of $r$ is finite. Consequently the pullback to $P$ of the theta polarization of $J_C$ is a polarization.

**Proof.** The tangent spaces at the origins are

$$
T_0P=H^1(X,\mathcal O_X),
\qquad
T_0J_C=H^1(C,\mathcal O_C).
$$

The exact sequence

$$
0\longrightarrow\mathcal O_X(-C)\longrightarrow
\mathcal O_X\longrightarrow\mathcal O_C\longrightarrow0 \tag{7.7}
$$

shows that the tangent map of $r$ is injective once
$H^1(X,\mathcal O_X(-C))=0$. By Serre duality this group is dual to
$H^1(X,\omega_X(C))$, which vanishes when $C$ is a sufficiently high
multiple of an ample divisor. If the reduced identity component of
$\ker r$ had positive dimension, it would be an abelian subvariety and
would have a nonzero tangent direction killed by $dr$, a contradiction.
Thus $\ker r$ is zero-dimensional, hence finite. This conclusion allows a
finite nonreduced kernel in characteristic $p$; rational Tate modules are
unaffected.

The theta bundle on $J_C$ is ample. Its pullback along a map with finite kernel is ample: a positive-dimensional translation stabilizer of the pullback would map into the finite stabilizer of theta. The associated homomorphism on $P$ is therefore a polarization. $\square$

On Tate modules, the alternating curve form restricts through $r$ to the Weil form of this polarization on $P$. It is therefore nondegenerate. Under the standard identification $H^1(\bar X,\mathbf Q_\ell)\simeq V_\ell P^\vee$, this says precisely that the image in (7.5) is nondegenerate for the curve cup-product pairing.

## 8. Hard Lefschetz in dimensions one and two

### 8.1 The Lefschetz operator and its twists

Let $X$ be smooth projective of pure dimension $d$ and let $L$ be ample. Put $\eta=c_1(L)\in H^2(\bar X,\mathbf Q_\ell(1))$ and define

$$
\mathsf L(x)=x\smile\eta:
H^i(\bar X,\mathbf Q_\ell)\longrightarrow
H^{i+2}(\bar X,\mathbf Q_\ell(1)). \tag{8.1}
$$

If $L$ is defined over the ground field, $\eta$ is Galois invariant in the twisted group, so $\mathsf L$ is Galois and Frobenius equivariant. The twist in (8.1) is not optional.

Hard Lefschetz in dimension $d$ asserts

$$
\mathsf L^{d-i}:H^i(\bar X,\mathbf Q_\ell)
\xrightarrow{\sim}
H^{2d-i}(\bar X,\mathbf Q_\ell(d-i))
\quad(0\le i\le d). \tag{8.2}
$$

We now prove (8.2) for $d\le2$.

### 8.2 Curves

For a smooth projective geometrically connected curve, only $i=0$ is nontrivial. Cup product with $c_1(L)$ sends $1$ to the divisor class of $L$. Under the trace isomorphism

$$
H^2(\bar C,\mathbf Q_\ell(1))\xrightarrow{\sim}\mathbf Q_\ell,
$$

this class maps to $\deg L>0$. Hence

$$
\mathsf L:H^0(\bar C,\mathbf Q_\ell)\xrightarrow{\sim}
H^2(\bar C,\mathbf Q_\ell(1)). \tag{8.3}
$$

For a disconnected smooth proper curve, the assertion holds componentwise provided $L$ has positive degree on each component, which ampleness guarantees.

### 8.3 The degree-zero and degree-four parts of a surface

Let $X$ be a smooth projective geometrically connected surface. The map

$$
\mathsf L^2:H^0(\bar X,\mathbf Q_\ell)\longrightarrow
H^4(\bar X,\mathbf Q_\ell(2)) \tag{8.4}
$$

sends $1$ to $c_1(L)^2$. Trace sends this class to the self-intersection number $L^2$. An ample divisor on a surface has $L^2>0$: after a high power, two general members meet properly in a nonempty zero-dimensional scheme of positive length. Thus (8.4) is a nonzero map between one-dimensional spaces and is an isomorphism.

The $i=2$ assertion is $\mathsf L^0=1$ on $H^2$ and contains no claim. Therefore the only remaining surface map is $H^1\to H^3(1)$.

### 8.4 The middle odd degrees of a surface

Choose a smooth sufficiently ample section $i:C\hookrightarrow X$. By (7.2),

$$
\mathsf L=i_*i^*:
H^1(\bar X,\mathbf Q_\ell)\longrightarrow
H^3(\bar X,\mathbf Q_\ell(1)). \tag{8.5}
$$

Poincaré duality identifies the target with $H^1(\bar X)^\vee$, and the bilinear form represented by (8.5) is

$$
(x,y)\longmapsto
\operatorname{Tr}_C(i^*x\smile i^*y). \tag{8.6}
$$

Proposition 7.2 says that the restriction of the curve's theta polarization to the connected Picard variety of $X$ is a polarization. Its Weil form is perfect on the rational Tate module. Through Kummer theory this is exactly (8.6). Hence (8.6) is nondegenerate, so (8.5) is injective. Source and target have equal dimension by Poincaré duality, and it is therefore an isomorphism.

We have proved:

**Theorem 8.1 (hard Lefschetz in low dimension).** Let $X$ be a smooth projective variety of pure dimension at most two over a field, let $\ell$ be invertible, and let $L$ be ample. Then (8.2) is an isomorphism in every degree. The maps commute with Galois whenever $L$ is defined over the ground field.

Projectivity is used to possess an ample line bundle and smooth high sections. Smoothness is used for purity, Gysin maps, and Poincaré duality. Properness without projectivity does not provide an operator $\mathsf L$, and a merely nef line bundle can have $L^2=0$, already breaking (8.4).

## 9. Lefschetz pencils on surfaces

### 9.1 Constructing the pencil

Hard Lefschetz controlled the odd cohomology of a surface, but it said nothing about the eigenvalues on $H^2$: in dimension two the hard-Lefschetz map there is the identity. To reach the primitive middle group we vary hyperplane sections instead of choosing only one.

Let $X/\mathbf F_q$ be a smooth projective geometrically connected surface. Replace an ample line bundle by a sufficiently high power and embed $X\hookrightarrow\mathbf P^N$. A line in the dual projective space is a pencil generated by two hyperplanes $H_0,H_\infty$. Its axis meets $X$ in a finite smooth scheme $B$. Blowing up the base locus resolves the rational map:

$$
\begin{array}{ccc}
\widetilde X=\operatorname{Bl}_B X&\xrightarrow{\ f\ }&\mathbf P^1\\
\downarrow&&\\
X.&&
\end{array} \tag{9.1}
$$

After a finite extension of $\mathbf F_q$, the line can be chosen transverse to the discriminant away from its smooth locus. The resulting map is smooth over a dense open $j:U\hookrightarrow\mathbf P^1$, and every geometric singular fiber has one ordinary quadratic singularity. Because the fibers are curves, this means one node.

Here is why a suitable line exists. The incidence variety of pairs $(x,H)$ with $T_xX\subset H$ maps to the dual projective space. For a high Veronese embedding, separation of length-three subschemes makes this map generically finite onto a divisor and makes the locus of worse contact codimension at least two. Lines avoiding that locus and meeting the discriminant transversely form a nonempty open in the Grassmannian. Over a finite field this open may have no rational point, but it does after a finite extension. In characteristic two, the nodal local equation is taken in the form $uv-a$; its vanishing-cycle calculation is the same. Thus no restriction on $p$ is imposed.

Purity descends from the finite extension: if $F^a$ has all conjugates of modulus $(q^a)^{i/2}$, then $F$ has modulus $q^{i/2}$. We may therefore construct the pencil after such an extension without weakening the final assertion.

### 9.2 Ordinary quadratic singularities and vanishing cycles

Let $\bar\eta$ be a geometric generic point of $U$ and

$$
V=H^1(\widetilde X_{\bar\eta},\mathbf Q_\ell).
$$

Around a singular value $s$, inertia acts through a Picard--Lefschetz transvection

$$
T_s(v)=v+\langle v,\delta_s\rangle\delta_s, \tag{9.2}
$$

where $\delta_s$ is the vanishing cycle and $\langle\ ,\ \rangle$ is the alternating intersection form on the smooth fiber. Thus $N_s=T_s-1$ satisfies $N_s^2=0$, its image is the line spanned by $\delta_s$, and

$$
V^{I_s}=\ker N_s=\delta_s^\perp. \tag{9.3}
$$

To obtain (9.2), use étale local coordinates in which the family is $uv=t$. A nearby annulus retracts cohomologically onto one loop. The boundary map of the pair sends its generator to $\delta_s$; transporting a class once around $t=0$ adds its intersection number with that generator. The self-intersection of an odd-dimensional vanishing cycle is zero, so $N_s^2=0$. This is the one-node Picard--Lefschetz calculation, including its multiplicity one.

The sheaf

$$
\mathcal V=R^1f_*\mathbf Q_\ell|_U \tag{9.4}
$$

is lisse and punctually pure of weight one by smooth proper base change and Theorem 4.2 on every fiber. Its alternating pairing takes values in $\mathbf Q_\ell(-1)$, so its geometric determinant is finite after its constant factor $\mathbf Q_\ell(-g)$ is removed. Its semisimplification is therefore geometric-pure in the sense of Chapter 5. Formula (9.3) identifies the stalk of $j_*\mathcal V$ at $s$ with the invariant cycles.

For this pencil one can say more and avoid assuming a general
semisimplicity theorem. Let $E\subset V$ be the span of the vanishing
cycles. Formula (9.2) shows that $E$ and $E^\perp$ are monodromy stable
and that $E^\perp$ is the subspace fixed by every local transvection.
The global invariant-cycle sequence identifies it with the image of
$H^1(\overline{\widetilde X})$ in the cohomology of a smooth fiber.
The hard-Lefschetz pairing already proved in Chapter 8 makes this image
nondegenerate, so

$$
V=E^\perp\oplus (E^\perp)^\perp. \tag{9.4a}
$$

The first summand is constant. The second is semisimple under the
transvections: if a nonzero invariant subspace contains a vector pairing
nontrivially with some $\delta_s$, (9.2) makes it contain $\delta_s$;
conjugating the pencil paths then makes it contain every vanishing cycle.
If it pairs trivially with every $\delta_s$, it lies in $E^\perp$ and its
intersection with the second summand is zero. Thus the nonconstant
vanishing-cycle representation is irreducible (or a direct sum of the
orbits obtained when the discriminant is not geometrically connected).
Consequently $\mathcal V$ itself is a direct sum of constant and
geometrically irreducible pure constituents to which Theorem 5.2
applies.

### 9.3 The direct-image decomposition

We next locate $H^2(\widetilde X)$ in the Leray spectral sequence. The smooth fibers are connected curves, so over $U$

$$
R^0f_*\mathbf Q_\ell=\mathbf Q_\ell,\qquad
R^1f_*\mathbf Q_\ell=\mathcal V,\qquad
R^2f_*\mathbf Q_\ell=\mathbf Q_\ell(-1). \tag{9.5}
$$

The invariant-cycle calculation extends the outer sheaves across a nodal fiber and extends the middle one as $j_*\mathcal V$. Because a nodal Lefschetz fiber is irreducible, no extra top-dimensional component appears. Thus the degree-two part of Leray has graded pieces

$$
H^2(\mathbf P^1,\mathbf Q_\ell),\qquad
H^1(\mathbf P^1,j_*\mathcal V),\qquad
H^0(\mathbf P^1,\mathbf Q_\ell(-1)). \tag{9.6}
$$

The exceptional curves over points of $B$ are sections of $f$. A section splits the unit map $\mathbf Q_\ell\to Rf_*\mathbf Q_\ell$ in degree zero and, by relative duality, splits the trace in degree two. Consequently the possible Leray $d_2$ maps touching the outer terms vanish. Since the base has dimension one, there are no higher differentials. We obtain a Frobenius-stable filtration

$$
0\subset W_0\subset W_1\subset H^2(\overline{\widetilde X},\mathbf Q_\ell) \tag{9.7}
$$

whose three successive quotients are the groups in (9.6). A noncanonical direct sum is unnecessary; weights can be read from a filtration.

### 9.4 Where the primitive middle cohomology sits

The two outer pieces of (9.6) are both $\mathbf Q_\ell(-1)$ and hence have weight two. Geometrically they are generated by a fiber and a section. The middle piece records the variation of the Jacobians of the fibers:

$$
H^1(\mathbf P^1,j_*\mathcal V)=H_p^1(U,\mathcal V). \tag{9.8}
$$

Any constant part of $\mathcal V$ contributes $H^1(\mathbf P^1,\text{constant})=0$. The nonconstant part contains the vanishing cycles. Theorem 5.2 says that (9.8) is pure of weight $1+1=2$.

This is the decisive reduction. We did not infer surface purity from the functional equation, nor from hard Lefschetz in the vacuous middle degree. We expressed surface $H^2$ through fibers whose $H^1$ was already known to have weight one and then used the independently proved curve-sheaf estimate to add the cohomological weight of the base.

## 10. The Riemann hypothesis for smooth proper surfaces

### 10.1 The pencil contribution has weight two

Apply Theorem 5.2 to the direct summands of $\mathcal V$ furnished by
(9.4a). Every nonconstant constituent is punctually pure of weight one;
the constant summand contributes no $H^1$ on $\mathbf P^1$. Hence all
three graded pieces in (9.7) are pure of weight two.

An extension of pure Frobenius modules of the same weight is pure of that weight. Therefore

$$
H^2(\overline{\widetilde X},\mathbf Q_\ell)
\quad\text{is pure of weight }2. \tag{10.1}
$$

This conclusion includes divisor classes and the transcendental part. No assertion that $H^2$ is algebraic has entered the proof.

### 10.2 Blowing up does not change the question

If $\pi:\widetilde X\to X$ blows up one geometric point with exceptional curve $E$, purity and localization give the Frobenius-equivariant decomposition

$$
H^2(\overline{\widetilde X},\mathbf Q_\ell)
\simeq \pi^*H^2(\bar X,\mathbf Q_\ell)
\oplus \mathbf Q_\ell[E]. \tag{10.2}
$$

The twisted class $[E]\in H^2(1)$ is fixed when the point is rational, so the untwisted eigenvalue is $q$. If the center is a finite Frobenius orbit, the exceptional classes form a permutation representation tensored with $\mathbf Q_\ell(-1)$; their eigenvalues are $q$ times roots of unity and still have weight two.

Projection satisfies $\pi_*\pi^*=1$, so $H^2(\bar X)$ is a Frobenius-stable direct summand of (10.2). Purity passes to subobjects. Iterating over the finite base locus of the pencil proves

$$
H^2(\bar X,\mathbf Q_\ell)\text{ is pure of weight }2. \tag{10.3}
$$

The argument has been written for projective $X$. A smooth proper surface over a finite field is projective: Chow's lemma gives a projective birational surface, resolution makes it smooth, and the exceptional intersection matrix is negative definite; successively contracting the curves orthogonal to the pullback of a sufficiently positive divisor produces an ample divisor on $X$. Thus the surface theorem applies to smooth proper surfaces as well. In applications where a polarization is already part of the moduli problem, this reduction is unnecessary.

### 10.3 Purity in all five degrees

We now assemble the degrees without using a later one to prove an earlier one.

- $H^0=\mathbf Q_\ell$ is pure of weight zero.
- The connected Picard variety $P=\operatorname{Pic}^0_X$ and Kummer theory identify $H^1(\bar X)$ with $V_\ell P^\vee$. The abelian Frobenius theorem proves weight one.
- The pencil argument proves weight two for $H^2$.
- Hard Lefschetz gives $H^1\xrightarrow{\sim}H^3(1)$. Since twisting by $(1)$ lowers weight by two, $H^3$ has weight three.
- The trace isomorphism $H^4=\mathbf Q_\ell(-2)$ gives weight four.

We have proved the required statement.

**Theorem 10.1 (surface Riemann hypothesis).** Let $X/\mathbf F_q$ be smooth, proper, and geometrically connected of dimension two. For every $0\le i\le4$, every eigenvalue $\alpha$ of geometric Frobenius on $H^i(\bar X,\mathbf Q_\ell)$ is algebraic and satisfies

$$
|\iota(\alpha)|=q^{i/2} \tag{10.4}
$$

for every complex embedding $\iota$. Equivalently, $H^i$ is pure of weight $i$.

The same pencil proof has a coefficient form needed for geometric
coefficient systems. Let $\mathcal F$ be a lisse geometric-pure sheaf of
weight $w$ on $X$. Assume that, after forming the pencil, the sheaves
$R^bf_*(\mathcal F)$ on its smooth locus have algebraic Frobenius
polynomials, controlled determinant, and Picard--Lefschetz local
monodromy. These conditions hold for the polarizable coefficient
systems obtained from tensor constructions in $R^1$ of abelian or curve
families. On every smooth pencil fiber, Theorem 5.2 gives weight $w+b$
to $H^b$; applying Theorem 5.2 once more on the base gives weight
$w+a+b$ to

$$
H^a(\mathbf P^1,j_*R^bf_*\mathcal F).
$$

The Leray filtration and the same blowup calculation therefore prove

$$
H^i(\bar X,\mathcal F)\text{ is pure of weight }w+i. \tag{10.4a}
$$

The direct-image and local-monodromy hypotheses are part of this
coefficient statement. An arbitrary lisse sheaf is not declared pure
merely because its rank and determinant have been written down.

For a smooth proper scheme with several geometric components, Frobenius permutes the components. After a finite extension each component is fixed and Theorem 10.1 applies; descending multiplies the eigenvalues by roots of unity and preserves their weights.

### 10.4 The surface zeta function and point bounds

Write

$$
P_i(t)=\det(1-tF\mid H^i(\bar X,\mathbf Q_\ell)).
$$

Then

$$
Z(X,t)=
\frac{P_1(t)P_3(t)}
{(1-t)P_2(t)(1-q^2t)}. \tag{10.5}
$$

The reciprocal roots of $P_i$ lie on $|\alpha|=q^{i/2}$, or equivalently the roots in the $t$-plane lie on $|t|=q^{-i/2}$. Duality pairs $P_1$ with $P_3$ and makes $P_2$ reciprocal around $q$.

If $b_i=\dim H^i$, the trace formula and purity give the explicit estimate

$$
\left|\#X(\mathbf F_{q^n})-(q^{2n}+1)\right|
\le b_1q^{n/2}+b_2q^n+b_3q^{3n/2}. \tag{10.6}
$$

Hard Lefschetz gives $b_3=b_1$. The largest possible error is therefore of order $q^{3n/2}$, as expected for a two-dimensional smooth proper variety. If $H^1=H^3=0$, the sharper error $b_2q^n$ remains.

Because the circles for different $i$ are disjoint, the cohomological factors in (10.5) cannot cancel across degrees. The zeta function, which is defined by point counts and is independent of $\ell$, therefore uniquely determines every $P_i$. It follows in this low-dimensional smooth proper setting that

$$
P_i(t)\in\mathbf Z[t]
$$

and is independent of $\ell$. Integrality follows because the roots are algebraic integers and the factor is fixed by every automorphism of $\overline{\mathbf Q}$; uniqueness from the disjoint weight circles makes the rational coefficients visible in the rational zeta function.

## 11. Mixed weights on open surfaces

### 11.1 Normal-crossings boundary complexes

The Shimura surfaces used later may first appear as open varieties. The correct pure object is then interior cohomology, not all ordinary cohomology.

Let $U$ be a smooth surface over $\mathbf F_q$ admitting a smooth proper compactification $j:U\hookrightarrow X$ whose boundary

$$
D=X\setminus U=\bigcup_{a\in A}D_a
$$

is a strict normal-crossings divisor. Put $D^{(1)}=\coprod_aD_a$ and let $D^{(2)}$ be the finite scheme of ordered pairwise intersections, with the usual alternating incidence map. Repeated localization and purity express the boundary contribution through

$$
H^{m-2r}(\overline{D^{(r)}},\mathbf Q_\ell(-r)),
\qquad r=1,2. \tag{11.1}
$$

Curves $D_a$ are pure in degrees $0,1,2$, and intersection points are pure in degree zero. The twist $(-r)$ raises weight by $2r$, so every term in (11.1) has the weight predicted by its total cohomological position. The incidence maps commute with Frobenius because they are alternating sums of Gysin and restriction maps defined over the ground field.

### 11.2 Weight inequalities

Filtering the localization double complex by the number of boundary components gives a spectral sequence. In compact support, its terms are proper-stratum groups placed so that their weights are at most the total degree; in ordinary cohomology, duality reverses the filtration and gives weights at least the total degree. Consequently

$$
H_c^i(\bar U,\mathbf Q_\ell)\text{ has weights }\le i,
\qquad
H^i(\bar U,\mathbf Q_\ell)\text{ has weights }\ge i. \tag{11.2}
$$

For a coefficient sheaf $\mathcal F$ satisfying the surface coefficient
hypotheses of (10.4a), and whose local monodromy along $D$ has the stated
finite or unipotent weight filtration, the same proof gives

$$
H_c^i(\bar U,\mathcal F)\text{ has weights }\le w+i,
\qquad
H^i(\bar U,\mathcal F)\text{ has weights }\ge w+i. \tag{11.3}
$$

The proof uses only the curve-sheaf theorem on the one-dimensional strata, purity at the zero-dimensional strata, and the two-step normal-crossings complex. Thus (11.2) is not an invocation of a higher-dimensional weight theorem.

As a check, $U=\mathbf A^2$ has only $H_c^4=\mathbf Q_\ell(-2)$, of weight four. For $U=\mathbf G_m^2$, Künneth gives compactly supported weights $0,2,4$ in the expected mixed degrees; equality of weight and degree fails outside the proper case.

### 11.3 Interior cohomology

Define

$$
H_!^i(\bar U,\mathcal F)
=\operatorname{im}\left(
H_c^i(\bar U,\mathcal F)\to H^i(\bar U,\mathcal F)
\right). \tag{11.4}
$$

The source in (11.4) has weights at most $w+i$ and the target weights at least $w+i$. Lemma 2.2 proves:

**Theorem 11.1 (interior purity in dimension two).** Under the hypotheses above, $H_!^i(\bar U,\mathcal F)$ is pure of weight $w+i$. In particular,

$$
H_!^2(\bar U,\mathbf Q_\ell)
\text{ is pure of weight }2. \tag{11.5}
$$

The image formulation automatically removes Eisenstein and boundary pieces of the wrong weight. It is also stable under every properly supported correspondence acting on both compact and ordinary cohomology.

### 11.4 Singular and semistable warnings

For a singular proper surface, constant-coefficient cohomology need not be pure of degree $i$. The correct pure replacement is intersection cohomology, whose local contribution at a singular point is a middle extension rather than the ordinary constant sheaf. We do not substitute ordinary cohomology for it.

For a semistable degeneration over a trait, the generic smooth fiber remains pure when it has good reduction, but the special fiber has a weight spectral sequence with dual-graph and component terms in different weights. Monodromy shifts weights and twists according to

$$
N:\operatorname{Gr}_{w+r}\longrightarrow
\operatorname{Gr}_{w-r}(-r).
$$

This degeneration formula is not used in any proof here; it records the
boundary of the smooth statements. Theorem 10.1 concerns smooth proper
fibers over a finite field, and Theorem 11.1 concerns a smooth open
surface with controlled boundary. Neither says that arbitrary singular
cohomology is pure.

## 12. Correspondences and pure weight-two summands

### 12.1 Frobenius-compatible projectors

Let $X/\mathbf F_q$ be smooth proper of dimension two and let $\Gamma$ be a codimension-two algebraic correspondence on $X\times X$, proper over both factors and defined over $\mathbf F_q$. Pull--cup--push defines

$$
\Gamma_*:H^i(\bar X,\mathbf Q_\ell)\to H^i(\bar X,\mathbf Q_\ell),
$$

and $\Gamma_*$ commutes with $F$. If $e$ is an idempotent in a rational correspondence algebra, then

$$
H^i=eH^i\oplus(1-e)H^i. \tag{12.1}
$$

Every Frobenius eigenvalue on $eH^i$ already occurs on $H^i$. Theorem 10.1 therefore gives:

**Proposition 12.1.** Every Frobenius-compatible correspondence summand of $H^i(\bar X)$ is pure of weight $i$. In particular $eH^2$ is pure of weight two.

No semisimplicity of the whole Galois representation is required; the idempotent itself supplies the splitting.

### 12.2 Adjoints and orthogonal decompositions

Transpose correspondences are adjoint for Poincaré duality:

$$
\langle\Gamma_*x,y\rangle
=\langle x,{}^t\Gamma_*y\rangle. \tag{12.2}
$$

If $e={}^te$, then the two summands in (12.1) are orthogonal. The restriction of the middle pairing

$$
H^2(\bar X)\times H^2(\bar X)\longrightarrow\mathbf Q_\ell(-2)
$$

is nondegenerate on $eH^2$. Thus eigenvalues within the summand occur in reciprocal pairs $\alpha,q^2/\alpha$. Purity strengthens this to $|\alpha|=q$, whereas adjointness alone would give only the product relation.

If a Hecke adjoint is transpose followed by an involution coming from a polarization or moduli duality, that involution must be included in $e^\dagger$. Geometric transpose by itself supplies only (12.2).

### 12.3 Isolating a constituent

Suppose a commutative algebra $\mathbb T$ of correspondences acts on $H^2$, and let $\mathfrak m$ be a maximal ideal of a finite coefficient extension. If a polynomial idempotent $e_{\mathfrak m}\in\mathbb T\otimes E$ isolates the desired simultaneous eigenspace, then

$$
V_{\mathfrak m}=e_{\mathfrak m}H^2(\bar X,E) \tag{12.3}
$$

is Frobenius stable and pure of weight two. Consequently every unramified geometric Frobenius eigenvalue $\alpha_v$ at a residue field of size $q_v$ satisfies

$$
|\iota(\alpha_v)|=q_v \tag{12.4}
$$

under every complex embedding.

One must distinguish a rational projector from an integral summand. Denominators in $e_{\mathfrak m}$ may prevent a splitting of the $\mathbf Z_\ell$ lattice. Purity is a statement about the rational representation and survives; lattice saturation is a separate integral problem.

For an open smooth surface, replace $H^2$ in (12.3) by $H_!^2$. Properly supported correspondences preserve the map $H_c^2\to H^2$, hence act on its image. Theorem 11.1 again gives weight two. Taking an arbitrary quotient of $H^2$ before removing boundary cohomology can retain weights greater than two and is unsafe.

### 12.4 The Shimura-surface application

The geometric situation needed later has the following form. Let $S/\mathbf F_q$ be either:

1. a smooth projective PEL surface; or
2. a smooth PEL surface with a smooth proper compactification whose boundary is strict normal crossings and on which the relevant prime-to-level correspondences extend with proper support.

Let $\mathbb T$ be the algebra generated by those correspondences and let $e$ be a rational Hecke projector. In the projective case put

$$
V_e=eH^2(\bar S,\mathbf Q_\ell);
$$

in the open case put

$$
V_e=eH_!^2(\bar S,\mathbf Q_\ell).
$$

Then $V_e$ is pure of weight two. If it is two-dimensional with characteristic polynomial

$$
T^2-a_qT+\varepsilon_qq^2,
$$

both roots have absolute value $q$ and $|\,\iota(a_q)\,|\le2q$. More generally, every root in rank $r$ has modulus $q$, so $|\iota(\operatorname{Tr}F)|\le rq$.

This is the promised isolation statement. It uses no assertion that all middle cohomology is automorphic or algebraic. Geometry first proves purity of the entire proper or interior middle group; the correspondence projector then passes that purity to the selected constituent.

## 13. Families, good reduction, and coefficient changes

### 13.1 Smooth proper families

Let $f:X\to S$ be smooth and proper of relative dimension at most two with $\ell$ invertible. Smooth proper base change makes $R^if_*\mathbf Q_\ell$ lisse and identifies its geometric stalks with fiber cohomology. If $s$ is a finite-field point, Theorems 4.2 and 10.1 show that

$$
(R^if_*\mathbf Q_\ell)_{\bar s}
$$

is pure of weight $i$. Thus the direct-image sheaf is punctually pure of weight $i$ on every finite-field stratum.

Cup products, traces, the Lefschetz operator, and properly supported correspondences commute with base change. Hence hard Lefschetz is an isomorphism of lisse sheaves:

$$
\mathsf L^{d-i}:R^if_*\mathbf Q_\ell
\xrightarrow{\sim}
R^{2d-i}f_*\mathbf Q_\ell(d-i) \tag{13.1}
$$

for relative curves and surfaces equipped with a relatively ample bundle. It suffices to check (13.1) on geometric stalks, where Theorem 8.1 applies.

### 13.2 Good reduction

Let $\mathcal X$ be smooth and proper over a henselian discrete valuation ring with finite residue field $\mathbf F_q$, and let $X_\eta$ and $X_s$ be its generic and special fibers. For $\ell$ different from the residue characteristic, smooth proper base change gives

$$
H^i(\overline{X_\eta},\mathbf Q_\ell)
\xrightarrow{\sim}
H^i(\overline{X_s},\mathbf Q_\ell). \tag{13.2}
$$

The generic representation is unramified, and its unramified geometric Frobenius corresponds to $F$ on the special fiber. If the relative dimension is at most two, every eigenvalue is therefore pure of weight $i$. A correspondence extending properly across the model commutes with (13.2), so the same statement holds on its projector summands.

Good reduction is essential here. At semistable reduction inertia can be nontrivial and the Weil--Deligne representation carries a monodromy filtration. The total object is pure only in the monodromy sense, not because every inertia-invariant subquotient has the same naive weight.

### 13.3 Changing the auxiliary prime

For a smooth proper curve or surface over $\mathbf F_q$, the trace formula expresses $Z(X,t)$ through the $P_i(t)$. Purity puts the reciprocal roots of different $P_i$ on disjoint circles. Therefore $Z(X,t)$ uniquely recovers each $P_i$, proving that the characteristic polynomial of Frobenius is independent of $\ell$ and has integer coefficients, as observed after (10.6).

For a correspondence projector, independence of $\ell$ requires the correspondence algebra and projector to be defined over a common number field and the simultaneous traces

$$
\operatorname{Tr}(eF^n\mid H^i)
$$

to be independent of $\ell$. The correspondence trace formula supplies this when $e$ is represented by algebraic cycles with common rational coefficients and proper fixed intersections. Purity then separates the desired degree from other degrees. Without such a common algebraic projector, equal dimensions at two auxiliary primes do not identify the representations.

Changing $\ell$ also does not preserve a chosen integral lattice automatically. The rational Frobenius polynomials and weights are common; integral saturation, torsion, and congruences must be checked prime by prime.

### 13.4 A normalization and hypothesis audit

The following checks prevent the common misapplications of the theory.

1. $F$ is geometric Frobenius. It acts on $\mathbf Q_\ell(1)$ by $q^{-1}$ and on top untwisted cohomology by $q^d$.
2. Twisting by $(m)$ lowers weight by $2m$.
3. Pure weight $w$ means every complex conjugate has modulus $q^{w/2}$, not only one chosen embedding.
4. Hard Lefschetz is $\mathsf L^{d-i}:H^i\to H^{2d-i}(d-i)$.
5. The curve-sheaf theorem needs pointwise purity, algebraic local polynomials, and controlled determinant; arbitrary lisse sheaves are not declared pure.
6. Smooth proper purity applies to curves and surfaces. Open varieties satisfy inequalities, and their interior image is pure.
7. Singular ordinary cohomology is not silently identified with intersection cohomology.
8. A rational correspondence projector gives a rational summand, not necessarily an integral direct summand.
9. Good-reduction comparison gives unramified purity; semistable reduction requires monodromy.
10. A finite extension used to construct a pencil changes $(F,q)$ to $(F^a,q^a)$ and therefore neither creates nor destroys the claimed weight.

## 14. The low-dimensional weight package

### 14.1 The complete theorem

We collect the results in the exact form needed later.

**Theorem 14.1 (weights, hard Lefschetz, and Weil bounds in low dimension).** Fix $\ell\ne p$.

1. If $C/\mathbf F_q$ is smooth, proper, and geometrically connected, then $H^i(\bar C,\mathbf Q_\ell)$ is pure of weight $i$. Its zeta numerator has integral coefficients, degree $2g$, reciprocal roots of modulus $\sqrt q$, and

   $$
   \left|\#C(\mathbf F_{q^n})-(q^n+1)\right|
   \le2gq^{n/2}.
   $$

2. If $j:U\hookrightarrow C$ is a smooth open curve and $\mathcal F$ is geometric-pure of weight $w$, then $H^1(C,j_*\mathcal F)$ is pure of weight $w+1$. Compactly supported cohomology has weights $\le w+i$, ordinary cohomology has weights $\ge w+i$, and their image is pure of weight $w+i$.
3. If $X$ is smooth projective of pure dimension $d\le2$ over a field and $L$ is ample, then

   $$
   \mathsf L^{d-i}:H^i(\bar X,\mathbf Q_\ell)
   \xrightarrow{\sim}
   H^{2d-i}(\bar X,\mathbf Q_\ell(d-i))
   $$

   for $0\le i\le d$.
4. If $X/\mathbf F_q$ is smooth, proper, and geometrically connected of dimension two, then $H^i(\bar X,\mathbf Q_\ell)$ is pure of weight $i$ for $0\le i\le4$. Its Frobenius polynomials are integral and independent of $\ell$, and its point counts satisfy (10.6).
5. If a smooth open surface has a smooth proper strict-normal-crossings compactification, then $H_c^i$ has weights $\le i$, $H^i$ has weights $\ge i$, and $H_!^i$ is pure of weight $i$. For the polarizable geometric coefficient systems satisfying (10.4a) and the stated boundary-monodromy hypotheses, weight $w$ shifts all bounds by $w$.
6. Frobenius-compatible algebraic correspondence projectors preserve these statements. In particular, a projector summand of proper $H^2$, or of open $H_!^2$, is pure of weight two.
7. Every clause is compatible with smooth proper base change and good reduction, including ample Lefschetz operators and properly extending correspondences.

### 14.2 How the ingredients depend on one another

The logical order matters. The proof can be summarized by the following diagram:

$$
\begin{array}{ccccc}
\text{ample intersections}
&\Longrightarrow&\text{Rosati positivity}
&\Longrightarrow&\text{abelian Frobenius purity}\\
&&&&\downarrow\\
&&&&\text{curve purity and Hasse--Weil}\\
&&&&\downarrow\\
\text{tensor powers on a curve}
&\Longrightarrow&\text{pure }H_p^1(U,\mathcal F)
&\Longrightarrow&\text{pencil contribution to }H^2\\
&&&&\downarrow\\
\text{weak Lefschetz and Picard polarization}
&\Longrightarrow&\text{hard Lefschetz for surfaces}
&\Longrightarrow&\text{surface purity in all degrees}.
\end{array}
$$

The trace formula enters before this diagram by supplying rationality and the cohomological expression for point counts. Duality supplies reciprocal eigenvalues and adjoints. Neither supplies absolute values. Positivity supplies the first absolute values on Jacobians, and the tensor-power estimate transports them through a family of curves to the primitive middle cohomology of a surface.

There is no circular use of surface purity in hard Lefschetz: the $H^1\to H^3(1)$ isomorphism is proved through the polarization induced by an ample curve. There is no circular use of surface purity in the pencil: pointwise purity of $R^1f_*$ comes from the already completed curve theorem. Finally, the open-surface inequalities are built from proper surfaces, boundary curves, and points, all already known.

### 14.3 Final synthesis

Weights turn Frobenius from a formal endomorphism into a measured one. On a curve, the Jacobian packages $H^1$ into an abelian variety, an ample theta divisor makes Rosati positive, and the identity $\pi\pi^\dagger=q$ forces every Frobenius conjugate onto the circle of radius $\sqrt q$. The trace formula then becomes the Hasse--Weil bound over every finite extension.

On a surface, an ample class has two roles. A single smooth section polarizes the connected Picard variety and proves hard Lefschetz in the only nonformal degree. A pencil of sections turns primitive $H^2$ into parabolic degree-one cohomology of a pure weight-one sheaf on a curve. The tensor-power estimate adds exactly one weight, placing the middle eigenvalues on the circle of radius $q$. Blowup formulas return the conclusion to the original surface, and hard Lefschetz carries weight one to weight three.

Boundary strata explain why open cohomology is mixed. Compact support approaches the middle weight from below, ordinary cohomology approaches it from above, and their image is pure. This makes interior cohomology the stable home for arithmetic constituents. Algebraic correspondences commute with Frobenius and preserve that image, so rational Hecke projectors isolate genuine weight-two representations without importing boundary eigenvalues or assuming that all middle cohomology is algebraic.

The resulting low-dimensional package is complete: hard Lefschetz holds for smooth projective curves and surfaces with the correct twists; smooth proper finite-field cohomology is pure in every degree through dimension two; curves satisfy the sharp Hasse--Weil bounds; open varieties carry the precise mixed inequalities; and every properly defined correspondence summand inherits the expected weight. These are exactly the size, duality, and projector controls required when curve and Shimura-surface cohomology later become Galois representations.
