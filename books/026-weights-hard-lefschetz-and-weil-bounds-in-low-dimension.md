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
   - [Normalization, determinant, and rationality](#52-normalization-determinant-and-rationality)
   - [Tensor invariants and the positive determinant lemma](#53-tensor-invariants-and-the-positive-determinant-lemma)
   - [The curve-sheaf Riemann hypothesis](#54-the-curve-sheaf-riemann-hypothesis)
   - [The symplectic monodromy criterion](#55-the-symplectic-monodromy-criterion)
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

This book proves that answer for smooth proper curves and surfaces and proves hard Lefschetz in the same range. An ample pencil reduces surface weight two to degree-one cohomology of a curve with a pure lisse coefficient sheaf. Chapter 5 closes the infinite-monodromy coefficient estimate: determinant rationality and tensor invariant projectors recover the global parabolic Frobenius algebra from polarized curve covers, and Rosati positivity forces its adjoint involution to be complex conjugation. The distinction from a local moment argument is explicit.

### 1.2 Standing conventions

Fix a prime $\ell\ne p=\operatorname{char}k$ and an algebraic closure $\bar k$. All cohomology is geometric étale cohomology with $\mathbf Q_\ell$ coefficients unless another coefficient ring is displayed. A variety is separated and of finite type. The words smooth, proper, projective, and geometrically connected are never implicit.

Arithmetic Frobenius is $\varphi:a\mapsto a^q$ in $\operatorname{Gal}(\bar k/k)$; geometric Frobenius is $F=\varphi^{-1}$ on geometric cohomology. With this convention,

$$
F\mid \mathbf Q_\ell(1)=q^{-1},
\qquad
F\mid \mathbf Q_\ell(-1)=q. \tag{1.2}
$$

Consequently the fundamental class of a smooth proper curve lies in $H^2=\mathbf Q_\ell(-1)$ and has eigenvalue $q$, while that of a surface lies in $H^4=\mathbf Q_\ell(-2)$ and has eigenvalue $q^2$. These two checks will detect every possible inversion error below.

The established duality theory supplies perfect pairings

$$
H^i(\bar X,\mathbf Q_\ell)\times
H^{2d-i}(\bar X,\mathbf Q_\ell(d))\longrightarrow\mathbf Q_\ell, \tag{1.3}
$$

and compatibility with cycle classes, transpose correspondences, and trace. The established trace theory supplies (1.1), Künneth, rationality, and the functional equation, but no absolute-value estimate. Projective geometry supplies high powers of ample line bundles and projective parameter spaces; the smooth-section and pencil arguments needed here are proved in Chapters 7 and 9. The theory of Jacobians supplies

$$
H^1(\bar C,\mathbf Q_\ell)
\simeq V_\ell J_C^\vee \tag{1.4}
$$

with its canonical principal polarization, where the superscript denotes the linear dual representation. Smooth proper base change is used only with its full smoothness, properness, and invertibility hypotheses. We will recall each ingredient at the point where its normalization matters.

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

Second, the coefficient theorem normalizes a pure sheaf to weight zero and separates its constant determinant. Rationality puts the parabolic Frobenius polynomial in one number field. Tensor invariant projectors are applied to global cochain complexes on congruence covers; curve Jacobians make the resulting adjoint trace form positive. Positive-involution linear algebra then places parabolic $H^1$ on the circle of weight one. This construction includes infinite connected monodromy and does not confuse local diagonal moments with global cross terms.

Third, an ample line bundle on a surface produces both a smooth section and a Lefschetz pencil. The smooth section controls $H^1$ and proves hard Lefschetz. The pencil places the new part of $H^2$ inside parabolic $H^1$ of the base with coefficient $R^1$ of the fibers. Picard--Lefschetz transvections give full symplectic monodromy on the nonconstant part, so the coefficient theorem gives weight two.

Finally, localization along normal-crossings boundaries gives the open-curve and open-surface inequalities. The image of compactly supported in ordinary cohomology is pure. Frobenius-compatible correspondence projectors preserve this interior image and hence isolate weight-two constituents without boundary contamination.

## 2. Weights and their elementary calculus

### 2.1 Pure representations

Let $V$ be a finite-dimensional $\mathbf Q_\ell$-vector space with an automorphism $F$ whose characteristic polynomial has algebraic coefficients. We call $V$ **pure of weight $w$** if every eigenvalue of $F$ is a $q$-Weil number of weight $w$. Semisimplicity is not part of the definition. A Jordan block changes traces by polynomial factors in $n$ but does not change the weights of its eigenvalues.

Purity is stable under subquotients: the characteristic polynomial on an invariant subspace and quotient divides that on $V$ after extension to an algebraic closure. It is also stable under extensions of pure objects of the same weight. It is not stable under an arbitrary direct sum of different weights; such a sum is mixed.

If $X$ is smooth proper and geometrically connected, the desired purity assertion is

$$
H^i(\bar X,\mathbf Q_\ell)
\text{ is pure of weight }i. \tag{2.1}
$$

For $i=0$ this follows from geometric connectedness. For $i=2d$ it follows from the trace orientation. Chapters 4, 5, 9, and 10 prove the assertion for curves and surfaces.

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

The established Jacobian theory shows that this is an involutive anti-automorphism and is the adjoint on every rational Tate module. We now prove its positivity.

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

**Lemma 3.2.** Let $K$ be a finite product of number fields with an involution $a\mapsto a^*$ such that

$$
\operatorname{Tr}_{K/\mathbf Q}(aa^*)>0
\quad\text{for }a\ne0. \tag{3.5}
$$

Then the involution preserves every field factor, and for every embedding $\sigma$ of a factor into $\mathbf C$,

$$
\sigma(a^*)=\overline{\sigma(a)}. \tag{3.6}
$$

**Proof.** Decompose $K\otimes_\mathbf Q\mathbf R$ into real and complex factors. If $*$ exchanged two factors, an element supported on only one of them would have $aa^*=0$ and hence zero trace, contradicting positive definiteness. Thus every factor is preserved. On a real factor the only involution is the identity. On a complex factor a real-algebra involution is either the identity or complex conjugation; the identity gives $\operatorname{Tr}_{\mathbf C/\mathbf R}(z^2)$, which is negative at $z=i$, so conjugation is forced. This proves (3.6) in every factor. $\square$

If $K$ is a commutative semisimple $\dagger$-stable subalgebra of $\operatorname{End}^0(A)$, Theorem 3.1 restricts to (3.5), with the reduced trace a positive multiple of the field trace on each factor. Therefore Rosati acts as complex conjugation under every complex embedding of every factor of $K$.

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

The element $\pi$ is normal for the positive involution because $\pi\pi^\dagger=\pi^\dagger\pi=q$. Consequently $K=\mathbf Q[\pi]$ has no nilpotents: after tensoring with $\mathbf R$, the positive involution represents $K$ by commuting normal operators, which are simultaneously diagonalizable over $\mathbf C$. Thus $K$ is a product of number fields and is stable under Rosati. Lemma 3.2, applied to this product rather than incorrectly to a possibly nonstable single factor, gives

$$
\overline{\iota(\alpha)}
=\iota(\alpha^\dagger)
=\iota(q/\alpha).
$$

Multiplication by $\iota(\alpha)$ yields $|\iota(\alpha)|^2=q$. This proves (4.1), including all conjugates and repeated roots. $\square$

The same normal-operator argument proves semisimplicity of $\pi$ on $V_\ell A$. Semisimplicity is useful for orthogonal projectors, though purity itself did not require it.

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

Suppose a surface is swept out by a one-parameter family of curves. The varying $H^1$ of the fibers forms a lisse sheaf $\mathcal V$ on the smooth part of the parameter curve. Fiberwise, Chapter 4 says that $\mathcal V$ has weight $1$. The part of surface $H^2$ not generated by a fiber or a section appears as

$$
H^1(\text{parameter curve},\mathcal V).
$$

The required surface weight $2$ is therefore the rule “degree-one cohomology of the base adds one to the weight of a pure coefficient sheaf.” This is not formal square-root cancellation. We now prove the coefficient theorem in the form needed by a Lefschetz pencil.

Let $j:U\hookrightarrow C$ be a dense open immersion into a smooth proper geometrically connected curve over $\mathbf F_q$. For a lisse sheaf $\mathcal F$ on $U$, put

$$
H_p^1(U,\mathcal F)
=H^1(\bar C,j_*\mathcal F)
=\operatorname{im}\left(
H_c^1(\bar U,\mathcal F)\longrightarrow
H^1(\bar U,\mathcal F)
\right). \tag{5.1}
$$

The equality follows by comparing the two localization sequences. The cone of $j_!\mathcal F\to Rj_*\mathcal F$ is supported on $C\setminus U$, and the image removes the classes which live only at the boundary. Verdier duality descends to a perfect pairing

$$
H_p^1(U,\mathcal F)\times
H_p^1(U,\mathcal F^\vee(1))
\longrightarrow\mathbf Q_\ell. \tag{5.2}
$$

Thus a self-dual weight-zero coefficient gives a $\mathbf Q_\ell(-1)$-valued form on its parabolic cohomology. Duality alone says only that $\beta$ is paired with $q/\beta$. The rest of this chapter proves that the adjoint involution is positive, which forces $q/\beta$ to be the complex conjugate of $\beta$.

### 5.2 Normalization, determinant, and rationality

We first state exactly which arithmetic hypotheses enter the proof. A geometrically semisimple lisse $E_\lambda$-sheaf $\mathcal F$ is called **determinant-normalized pure of weight $w$** when:

1. its closed-point Frobenius polynomials lie in a number field $E$ and are punctually pure of weight $w$ under every embedding $E\hookrightarrow\mathbf C$;
2. after a finite extension of constants, every geometrically irreducible constituent has determinant equal to a finite-order character times a constant character;
3. the local inertia representations have finite conductor, and the Frobenius polynomials on the invariant spaces $\mathcal F^{I_x}$ also lie in $E$;
4. the evaluation, coevaluation, and monodromy-presentation tensors used by the generated Tannakian category have a model over a fixed finite extension of $E$.

The last clause is a rationality condition on tensor projectors, not a purity assertion. It is automatic for the pencil: in a vanishing-cycle basis the Picard--Lefschetz matrices and their contractions are integral. The determinant condition is likewise not an extra weight theorem. It separates the scalar arithmetic character from geometric monodromy. For the pencil sheaf it follows directly from the alternating cup-product pairing: if the fibers have genus $g$, then

$$
\det R^1f_*\mathbf Q_\ell=\mathbf Q_\ell(-g)
$$

up to the finite character which records a possible permutation of connected constituents. On the vanishing summand the normalized determinant is $1$. No rank-one companion or class-field-theoretic determinant theorem is being imported.

Choose $c\in\overline E$ with $c^2=q$ and let $\mathcal L_c$ be the constant rank-one sheaf on which geometric Frobenius acts by $c^{-1}$. If $w$ is integral, then

$$
\mathcal F_0=\mathcal F\otimes\mathcal L_c^{\otimes w} \tag{5.3}
$$

is punctually pure of weight zero. Passing from $E$ to $E(c)$ is harmless. A closed point of degree $d$ contributes the scalar $c^{-wd}$, exactly canceling $q^{wd/2}$. After a further constant twist, clause 2 makes the determinant finite; after a finite extension of constants it is trivial. At the end, undoing (5.3) multiplies every parabolic eigenvalue by $c^w$ and restores weight $w+1$.

Rationality has to be established before any Archimedean argument. Apply the constructible-coefficient trace formula of Book 25 to $j_*\mathcal F$ on the proper curve $C$:

$$
L(C,j_*\mathcal F,t)
=\prod_i\det\left(1-tF\mid
H^i(\bar C,j_*\mathcal F)\right)^{(-1)^{i+1}}. \tag{5.4}
$$

Its logarithmic coefficients lie in $E$, because they are sums of the prescribed local traces, including the inertia-invariant traces at the boundary. A rational power series with coefficients in $E$ lies in $E(t)$: if $s$ is the degree of its minimal normalized denominator, its coefficients satisfy a unique order-$s$ recurrence, and minimality supplies a nonsingular finite linear system for that recurrence over $E$.

On a geometrically irreducible nonconstant constituent, $H^0$ vanishes. Parabolic duality makes $H^2$ dual to the corresponding $H^0$ of the dual middle extension, so it vanishes as well. Consequently

$$
L(C,j_*\mathcal F,t)
=P_{\mathcal F}(t),
\qquad
P_{\mathcal F}(t)
=\det(1-tF\mid H_p^1(U,\mathcal F))
\in E[t]. \tag{5.5}
$$

For a constant constituent the two end groups are explicit and Chapter 4 already proves the result. Direct sums and a finite extension of constants reduce the theorem to the nonconstant geometrically irreducible case in (5.5).

It is useful to retain the elementary estimate as a check. Pointwise purity and the trace formula give

$$
q^{w/2}\le |\iota(\beta)|
\le q^{(w+2)/2} \tag{5.6}
$$

for every root $\beta$ of $P_{\mathcal F}$ and every complex embedding $\iota$. Indeed, the stalk sum is $O(q^{n(w/2+1)})$; after removing $H^0$ and $H_c^2$, the power-sum Vandermonde lemma gives the upper bound. Pairing (5.2), applied to $\mathcal F^\vee(1)$, gives the lower bound. The two edges of (5.6) are exchanged by duality. The positive determinant argument below is what selects their geometric mean.

### 5.3 Tensor invariants and the positive determinant lemma

We isolate the hard step. Its proof is included because an argument using only the local moments

$$
\sum_{u\in U(\mathbf F_{q^n})}
|\operatorname{Tr}(F_{u,n}\mid\mathcal F_{\bar u})|^{2m}
$$

would be invalid: it omits the cross terms in the $2m$th power of the global stalk sum. The construction below applies tensor projectors to the entire parabolic cochain complex. It therefore approximates the global determinant (5.5), not merely the diagonal part of one Euler coefficient.

Explicitly, if $a_{u,n}=\operatorname{Tr}(F_{u,n}\mid\mathcal F_{\bar u})$ and $A_n=\sum_u a_{u,n}$, then

$$
|A_n|^{2m}
=\sum_{u_1,\ldots,u_m\atop v_1,\ldots,v_m}
a_{u_1,n}\cdots a_{u_m,n}
\overline{a_{v_1,n}\cdots a_{v_m,n}}, \tag{5.6a}
$$

whereas a tensor or Schur Euler factor at one point controls only

$$
\sum_u|a_{u,n}|^{2m}. \tag{5.6b}
$$

Newton identities do not turn (5.6b) into (5.6a).  The external parabolic
determinant (5.11) and the correspondence trace formula (5.11b) are instead
formed before contraction, so they retain every tuple in (5.6a).

**Lemma 5.1 (positive tensor-determinant lemma).** Let $\mathcal F$ be geometrically irreducible, determinant-normalized, and punctually pure of weight zero. Assume its geometric algebraic monodromy group $G$ is connected. Put

$$
B=H_p^1(U,\mathcal F),
\qquad
B'=H_p^1(U,\mathcal F^\vee).
$$

For every embedding $\iota:E\hookrightarrow\mathbf C$, the duality involution on the commutative Frobenius algebra generated on $B\oplus B'$ is positive. Equivalently, after passage to its semisimple quotient, if $a\ne0$, then

$$
\operatorname{Tr}_{\mathrm{red},\iota}(aa^\dagger)>0,
\qquad F^\dagger=qF^{-1}. \tag{5.7}
$$

Here $\dagger$ exchanges the $B$ and $B'$ factors through (5.2). If $\mathcal F\simeq\mathcal F^\vee$, it is the ordinary adjoint on $B$ for the resulting $\mathbf Q_\ell(-1)$-valued form. The notation $\operatorname{Tr}_{\mathrm{red},\iota}$ means the sum of ordinary matrix traces on all complex factors obtained after base change through $\iota$; thus (5.7) is a real inequality, not an ordering on an $\ell$-adic field.

**Proof.** We separate the finite-cover, invariant-theory, determinant, and positivity steps.

**Step 1: congruence covers and polarized finite approximants.** Wild
inertia has finite image: it is pro-$p$, while a pro-$p$ subgroup of an
$\ell$-adic analytic group with $p\ne\ell$ is finite. A finite cover
therefore kills the wild image, and induction back from that cover is dealt
with at the end. We may work with the finitely presented tame curve group.
Enlarge $E$ once by the fixed tensor field allowed in clause 4, and write
$\mathcal O$ for the valuation ring of $E_\lambda$ and $\lambda$ for its
maximal ideal.  These do not vary with the congruence level.  Choose a
lattice $M$ in a geometric stalk which is stable under the full arithmetic
monodromy group. Let $\Gamma$ be the geometric monodromy image and

$$
\Gamma_N=\ker\bigl(\Gamma\to
\operatorname{GL}(M/\lambda^NM)\bigr).
$$

The subgroup $\Gamma_N$ defines a connected finite étale cover $U_N\to U$; let $C_N$ be the normalization of $C$ in its function field. It is a smooth proper curve. Stability of $M$ makes every $\Gamma_N$ invariant under the arithmetic action, so descent supplies a Frobenius action on $C_N$. The deck group $G_N=\Gamma/\Gamma_N$ acts on $H^1(\bar C_N,E_\lambda)$, and the Frobenius-stable combinations used below commute with Frobenius. The group-algebra involution $g\mapsto g^{-1}$ is adjoint for the canonical polarization of $J_{C_N}$. Chapter 4 and Rosati positivity therefore give

$$
\operatorname{Tr}\left(uu^\dagger\mid
eH^1(\bar C_N,E_\lambda)\right)>0 \tag{5.8}
$$

whenever $e$ is a nonzero self-adjoint Frobenius-stable idempotent in the
deck-correspondence algebra and the induced endomorphism $u$ of $eH^1$ is
nonzero. Every Frobenius root in this summand occurs in $H^1(C_N)$ and
hence has absolute value $\sqrt q$ under every complex embedding. This
uses only the already proved curve theorem.

**Step 2: the invariant projectors.** Let $R$ be the faithful representation of $G$ furnished by $\mathcal F$. Since $G$ is the Zariski closure of $\Gamma$, a morphism between tensor words in $R\oplus R^\vee$ is $G$-equivariant exactly when it commutes with $\Gamma$. Reductivity follows from geometric semisimplicity: the unipotent radical would have nonzero fixed vectors in an irreducible constituent. Hence every irreducible $G$-module in the tensor category generated by $R$ is the image of an idempotent made from evaluation, coevaluation, permutations, and a Reynolds projector.

In the symplectic case used for the pencil this statement is completely explicit:

$$
(R^{\otimes 2m})^{\operatorname{Sp}(R)}
=\left\langle
\prod_{\{a,b\}\in\mathcal P}
\langle v_a,v_b\rangle:
\mathcal P\text{ a pairing of }\{1,\ldots,2m\}
\right\rangle, \tag{5.9}
$$

and the odd invariant spaces vanish. To prove (5.9), contract two entries with the alternating form and induct on $m$. If a tensor is killed by every contraction, evaluate it on a symplectic basis and use the diagonal torus to force equal positive and negative weights; a unipotent root subgroup then lowers a surviving pair and contradicts contraction-freeness. Thus complete contractions span. When $m$ exceeds the symplectic rank there are Pfaffian relations among the pairings, but the span and the image of the Reynolds projector are unchanged. In particular the projectors are defined over the coefficient field and commute with scalar extension.

We need the projectors on global cochains, not merely on stalks.  The
following determinant comparison is the precise bridge.  We give the
integral form because two tempting shortcuts are false: a module which is
constant modulo $\lambda^s$ on a cover need not lift to a
characteristic-zero representation of its deck group, and a lifted
differential cannot be replaced by $A^\dagger A$ without changing its
cohomology.

**Polarized determinant comparison.**  Let $\Pi$ be the tame geometric
fundamental group of the pair $(C,C\setminus U)$ and let $M$ be a stable
lattice in $R$.  There is a finite parabolic Poincaré complex
$K_\Pi$ of completed $\mathcal O[\Pi]$-modules, free in each term, such
that

$$
K_p(M)=K_\Pi\mathbin{\widehat\otimes}_{\mathcal O[\Pi]}M,
\qquad
H^1K_p(M)\otimes E_\lambda=B, \tag{5.10}
$$

and $K_\Pi^\vee\simeq K_\Pi[2](1)$.  The analogous complex with compact
support maps to it and its image in degree one is (5.10).  For every
balanced tensor word $T$ in $M\oplus M^\vee$, every polynomial $a(F)$,
and every $m\ge1$, the determinant functor applied to

$$
\left(K_p(M)\oplus K_p(M^\vee)\right)^{\boxtimes m}
\boxtimes
\left(K_p(M)\oplus K_p(M^\vee)\right)^{\vee\boxtimes m} \tag{5.11}
$$

Here $\boxtimes$ means that the coefficient complexes are first placed on
independent factors of $U^{2m}$ and only then are global parabolic cochains
taken; Künneth identifies the result with the indicated tensor product of
$K_p$-complexes.  Apply the determinant functor and then the complete
contractions of $T$.  After reduction modulo $\lambda^s$ the determinant
is a product and quotient of determinants on $H^1$-Künneth summands of
products of smooth proper curve covers; in the balanced contraction its
reduced trace is a finite sum of Rosati Gram terms.  Cancellation is
performed in the determinant category before reduction.  Consequently its residual determinant degree
is the dimension of the corresponding cohomology of (5.11), independent
of the degrees of the covers; its coefficients lie in the fixed field of
definition of the contraction tensors and have denominators in one fixed
finite set.

Here is the proof of the comparison.  The finite presentation of the tame
curve pair gives $K_\Pi$; imposing the local invariant and coinvariant maps
at the punctures gives its parabolic version.  Poincaré duality for the
pair identifies its transpose complex with the displayed twist.  For
$N\ge s$, reduction of the coefficient action factors through $G_N$, but
the cochains of the kernel must still be retained.  They are retained by
the Cartan--Leray identity

$$
K_p(T(M/\lambda^s))
\simeq
R\!\operatorname{Hom}_{(\mathcal O/\lambda^s)[G_N]}
\left(T(M/\lambda^s)^\vee,
K_p(C_N,\mathcal O/\lambda^s)\right). \tag{5.11a}
$$

Thus (5.11a), not the group cochain complex of $G_N$ alone, is the finite
level object.  Resolve the first argument and totalize before making any
truncation.  Book 20's cohomological-dimension and finiteness theorem makes
the total object a perfect $(\mathcal O/\lambda^s)$-complex of parabolic
amplitude $[0,2]$.  Replace it, *after totalization*, by a three-term finite
free complex.  This is not a claim that $T(M/\lambda^s)$ has a bounded
projective resolution over the modular group ring.  The cone of the
replacement is acyclic, and the determinant functor cancels it canonically:
for an elementary acyclic pair with differential $d$, the two factors are
$\det d$ and $(\det d)^{-1}$.

To compare this determinant with characteristic zero, apply determinant
Brauer induction to the matrix-coefficient laws of the regular terms in
(5.11a), rather than trying to lift the modular representation.  After
inverting $\lambda$ the group algebra is semisimple, so these laws split
into induced summands; equality is checked on cyclic subgroups, where it is
the determinant identity for a companion matrix.  Shapiro identifies an
induced summand with the corresponding intermediate curve cover.  Transfer
and restriction occur as transpose pairs, so their factors $[G_N:H]$
cancel before a determinant is taken.  In particular no division by
$|G_N|$ survives and the denominator set is independent of $N$.

Apply this construction simultaneously to the external tensor complex and
its dual.  Evaluation, coevaluation, permutations, and the Reynolds
idempotent commute with its differentials.  Complete contractions in
(5.9) turn every surviving pair of transpose induced summands into
$x^\dagger x$.  Conversely, the first fundamental theorem says that these
contractions exhaust the invariant determinant laws; hence no unrecorded
summand remains.  On a product $C_{H_1}\times\cdots\times C_{H_r}$ use the
curve Chow--Künneth projectors to select
$H^1(C_{H_1})\otimes\cdots\otimes H^1(C_{H_r})$.  The projectors are made
from a degree-one zero-cycle, a fiber, and the diagonal.  Such a zero-cycle
exists here without another theorem: the Hasse--Weil bound gives points
over $\mathbf F_{q^n}$ for every sufficiently large $n$; norms from two
consecutive extensions give zero-cycles of coprime degrees, and Bézout
gives a divisor of degree one.  Books 23
and 37 identify their transpose with the tensor product Rosati adjoint.
Thus the finite-level scalar is a sum of genuine Rosati squares, not an
alternating virtual trace.

Finally Book 25 applies to every deck correspondence and every product:

$$
\sum_i(-1)^i\operatorname{Tr}\left(F^r u\mid
H^i(\bar C_{H_1}\times\cdots\times\bar C_{H_t})\right)
=\sum_{z\in\operatorname{Fix}(F^r\circ u)}LT_z(u). \tag{5.11b}
$$

The Künneth expansion of (5.11b) is taken *before* contraction.  Its
fixed points therefore range over independent tuples of points and retain
all terms in (5.6a); restricting all entries to one diagonal would instead
give only (5.6b).  Equality of the first $D$ power traces, where $D$ is the
fixed residual degree, gives equality of determinant coefficients by
Newton identities.

There remains a descent issue which is often hidden in the phrase
``pass to the limit.''  The determinant laws just constructed are defined
over the fixed tensor field, not over the varying splitting fields of the
covers.  Their roots occur in tensor products of $H^1$ of proper curves, so
Chapter 4 and Künneth bound every coefficient under every embedding; in
degree $a$ the bound is

$$
\binom Da q^{ma}. \tag{5.11c}
$$

They are integral away from the fixed denominator set.  The coefficient
congruence modulo $\lambda^s$, common rationality, and the product formula
in that fixed field now force eventual equality: a nonzero difference
would have unbounded $\lambda$-adic valuation and uniformly bounded
valuation at every other place.  This proves the polarized determinant
comparison over every embedding.  Notice that neither a varying field norm
nor continuity from the $\lambda$-adic to the complex topology has been
used.

**Step 3: positivity and strictness.** Let $a$ be a polynomial in
Frobenius on $B\oplus B'$.  Apply the comparison to (5.11), insert $a$ in
one block and $a^\dagger$ in the other, and contract.  The finite-level
answer is a sum of Rosati squares of the form (5.8), hence is nonnegative
under every complex embedding.  Eventual determinant equality identifies
it exactly with

$$
\operatorname{Tr}_{\mathrm{red},\iota}
\bigl((aa^\dagger)^m\bigr). \tag{5.12}
$$

Taking $m=1$ gives nonnegativity in (5.7).  If equality held for $a\ne0$,
every complete contraction of a matrix coefficient of $a$ with its dual
would vanish.  Among these contractions are the ordinary evaluation
pairings between $B$ and $B'$ furnished by (5.2); their nondegeneracy says
that they separate endomorphisms of $B\oplus B'$.  Formula (5.9), or the
evaluation tensors for a general reductive $G$, is what ensures that all
of these separating contractions occur in the determinant comparison.
Thus $a$ would act as zero, contrary to its being nonzero in the reduced
Frobenius algebra.  The form is positive definite.

All four operations are now accounted for: tensor invariant theory
constructs the projector, the trace formula identifies its finite-cover
traces, determinant rationality passes from traces to one polynomial over
$E$, and Jacobian Rosati supplies positivity.  Pullback to either finite
cover used in Step 1 and induction back are adjoint under trace; the
averaging idempotent cuts the original parabolic complex from the induced
one, including its inertia-invariant boundary terms.  Positivity therefore
descends through those reductions.  At no point is a local diagonal moment
identified with a global moment. $\square$

### 5.4 The curve-sheaf Riemann hypothesis

We can now turn positivity into absolute values exactly as in the abelian argument of Chapter 4.

**Theorem 5.2 (curve-sheaf Riemann hypothesis).** Let $j:U\hookrightarrow C$ be as above and let $\mathcal F$ be determinant-normalized pure of weight $w$. Then

$$
H^1(\bar C,j_*\mathcal F)
\quad\text{is pure of weight }w+1. \tag{5.13}
$$

The conclusion includes geometrically irreducible sheaves with infinite geometric monodromy.

**Proof.** Normalize to weight zero by (5.3), extend constants so that the geometric constituents and their finite determinants are fixed, and treat one constituent at a time. A finite-monodromy constituent is a direct summand of the pushforward from a finite cover $C'\to C$. At a boundary point, inertia invariants in the regular representation are functions on inertia orbits, exactly the points of $C'$ above that boundary point; hence the direct-summand statement remains true after middle extension. Chapter 4 gives weight one to $H^1(C')$, so its parabolic summand has weight one.

Now suppose the geometric monodromy is infinite. Replace it by its connected component after a finite étale cover; induction from that cover and the finite component group returns the original constituent at the end. Lemma 5.1 supplies a positive involution on the semisimple Frobenius algebra

$$
A=E[F,F^{-1}]/\sqrt0,
\qquad F^\dagger=qF^{-1}. \tag{5.14}
$$

This quotient does not change the roots of the characteristic polynomial;
it only forgets possible Jordan nilpotents.  Being finite, commutative, and
reduced over the characteristic-zero field $E$, $A$ is a product of number
fields.  Apply Lemma 3.2 to every field factor and to the embedding under
consideration.  The positive involution acts as complex conjugation.  If
$\beta$ is an eigenvalue of $F$ on $B$, then

$$
\overline{\iota(\beta)}
=\iota(\beta^\dagger)
=\frac q{\iota(\beta)},
$$

so $|\iota(\beta)|^2=q$. This proves weight one for the normalized sheaf. Undoing (5.3) multiplies the radius by $q^{w/2}$ and gives $q^{(w+1)/2}$. A finite extension of constants replaces $(F,q)$ by $(F^a,q^a)$, so the result descends. $\square$

For later reference, the theorem is stable under direct sums, subquotients of a geometrically semisimple sheaf, finite pullback and induction, constant twists, and duals. These operations are already present in the tensor construction of Lemma 5.1 and preserve determinant normalization.

### 5.5 The symplectic monodromy criterion

The pencil application has a particularly transparent monodromy check.

**Lemma 5.3 (transvections give full symplectic monodromy).** Let $W$ be a symplectic vector space of characteristic zero, and let $\Gamma\subseteq\operatorname{Sp}(W)$ act irreducibly. Suppose $\Gamma$ is generated by transvections

$$
T_v(x)=x+\langle x,v\rangle v
$$

whose directions span $W$ and form one $\Gamma$-orbit. Then the Zariski closure of $\Gamma$ is $\operatorname{Sp}(W)$.

**Proof.** The powers $T_v^n=1+nN_v$ are Zariski dense in the one-parameter subgroup $1+tN_v$, where $N_v(x)=\langle x,v\rangle v$. Hence every $N_v$ lies in the Lie algebra $\mathfrak g$ of the Zariski closure. Under the standard identification

$$
\mathfrak{sp}(W)\simeq\operatorname{Sym}^2W,
\qquad v^2\longmapsto N_v, \tag{5.15}
$$

the commutator of $N_v$ and $N_w$ with $\langle v,w\rangle\ne0$ supplies the mixed tensor $vw$. The graph on the orbit directions, joining two directions when their pairing is nonzero, is connected. Indeed, a transvection from one component acts trivially on all other component spans and preserves its own. Since the transvections generate $\Gamma$, every component span would be $\Gamma$-stable if there were more than one, contradicting irreducibility. Mixed tensors along a path and polarization then span all of $\operatorname{Sym}^2W$. Thus $\mathfrak g=\mathfrak{sp}(W)$. The closure contains the connected group $\operatorname{Sp}(W)$ and was already contained in it, so equality follows. $\square$

For a weight-one symplectic sheaf $\mathcal V$ with pairing into $\mathbf Q_\ell(-1)$, tensoring by $\mathcal L_c$ makes it weight zero and changes the pairing into a scalar-valued symplectic form. Lemma 5.3 verifies connected monodromy when the Picard--Lefschetz directions span the nonconstant part, its determinant is one, and Theorem 5.2 gives

$$
H_p^1(U,\mathcal V\otimes\mathcal L_c)
\text{ of weight }1,
\qquad
H_p^1(U,\mathcal V)
\text{ of weight }2. \tag{5.16}
$$

This is the exact coefficient estimate required for a surface pencil.

## 6. Weights on open curves

### 6.1 Boundary invariants and coinvariants

Purity on the middle extension does not mean that ordinary or compactly supported cohomology of $U$ is pure. The boundary contributes lower-dimensional pieces.

For $D=C\setminus U$ and lisse $\mathcal F$, the triangle

$$
j_!\mathcal F\longrightarrow Rj_*\mathcal F
\longrightarrow i^*Rj_*\mathcal F\longrightarrow
$$

has a cone supported on $D$. At a geometric boundary point $x$, its degree-zero part is $\mathcal F^{I_x}$ and its degree-one part is an inertia coinvariant term, with a $(-1)$ twist in the tame unipotent case. Thus the long exact sequence separates global parabolic classes from local invariant and vanishing-cycle classes.

When $D$ is nonempty, the constant-coefficient calculation is elementary:

$$
0\longrightarrow\mathbf Q_\ell
\longrightarrow\mathbf Q_\ell^{D(\bar k)}
\longrightarrow H_c^1(\bar U,\mathbf Q_\ell)
\longrightarrow H^1(\bar C,\mathbf Q_\ell)
\longrightarrow0. \tag{6.1}
$$

The quotient $\mathbf Q_\ell^{D(\bar k)}/\mathbf Q_\ell$ has weight zero, while $H^1(\bar C)$ has weight one. Hence $H_c^1(U)$ is mixed of weights $0$ and $1$. If $D$ is empty, $U=C$ and the proper-curve calculation of Chapter 4 applies directly instead of (6.1).

### 6.2 Compact support and ordinary support

For constant coefficients, (6.1), the curve theorem, and duality give unconditionally

$$
H_c^i(\bar U,\mathbf Q_\ell)\text{ has weights }\le i,
\qquad
H^i(\bar U,\mathbf Q_\ell)\text{ has weights }\ge i. \tag{6.2}
$$

Indeed, $H_c^1$ is an extension of the weight-zero boundary quotient by the weight-one group $H^1(\bar C)$, while $H_c^2=\mathbf Q_\ell(-1)$ has weight two. The ordinary statement is the dual residue sequence. This proof uses no coefficient form of the weight theorem.

For a punctually pure lisse sheaf $\mathcal F$ of weight $w$, the shifted inequalities

$$
H_c^i(\bar U,\mathcal F)\text{ has weights }\le w+i,
\qquad
H^i(\bar U,\mathcal F)\text{ has weights }\ge w+i \tag{6.2a}
$$

follow by the same localization argument provided the corresponding weight bounds on the inertia-invariant and coinvariant boundary pieces are present. Theorem 5.2 supplies purity of the global middle-extension group, including in the infinite-monodromy case. A conductor bound alone controls only dimensions and cannot replace the local boundary-weight input.

In the tame Picard--Lefschetz situation used for pencils, $N^2=0$ and this filtration has only two steps. The required boundary check reduces to

$$
0\subset\operatorname{im}N\subset\ker N\subset\mathcal F_{\bar\eta}
$$

and $N:\mathcal F\to\mathcal F(-1)$, together with the normalization sequence of the nodal fiber that determines Frobenius on the two graded pieces.

### 6.3 Mixedness and the interior group

Define

$$
H_!^i(U,\mathcal F)
=\operatorname{im}\left(H_c^i(\bar U,\mathcal F)\to
H^i(\bar U,\mathcal F)\right). \tag{6.3}
$$

For constant coefficients, (6.2) and Lemma 2.2 prove unconditionally:

**Corollary 6.1.** The group $H_!^i(U,\mathbf Q_\ell)$ is pure of weight $i$.

For a determinant-normalized coefficient sheaf satisfying the boundary input stated after (6.2a), the same argument makes $H_!^i(U,\mathcal F)$ pure of weight $w+i$. This includes both finite-geometric-monodromy sheaves and the infinite-monodromy pencil sheaf with its explicit nodal boundary calculation. The formulation by image remains useful because correspondences preserve compact and ordinary cohomology and hence preserve their image.

### 6.4 Examples that fix the normalizations

For $U=\mathbf A^1$, $H_c^2=\mathbf Q_\ell(-1)$ has weight two and all other compactly supported groups vanish. For $U=\mathbf G_m$,

$$
H_c^1(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell,
\qquad
H_c^2(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell(-1),
$$

of weights zero and two. The trace formula gives $q^n-1$. It would be wrong to assign weight one to $H_c^1$ merely because its cohomological degree is one; proper smoothness is what forces equality of weight and degree.

For a Kummer sheaf of finite order on $\mathbf G_m$, the finite-monodromy part of Theorem 5.2 applies. If the character is nontrivial at both ends, its parabolic $H^1$ is pure of weight one. A missing ramification condition can create invariant boundary stalks of weight zero, but those lie outside the parabolic image. This example also shows why the middle extension, rather than all of $H_c^1$, is the natural pure object.

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

Let

$$
P=(\operatorname{Pic}^0_{X/k})_{\mathrm{red}}.
$$

This reduced identity component is an abelian variety. The qualification is essential in characteristic $p$: the full Picard scheme of a smooth surface can be nonreduced. The required representability is obtained from the divisor Hilbert schemes supplied by projective geometry. After choosing a sufficiently positive divisor, the open locus of effective divisors maps to the Picard sheaf; its fibers are projective spaces of sections, fpqc descent gives the quotient, and the component through the trivial bundle is proper. The reduced group component is smooth over the perfect ground field and hence is an abelian variety. Restriction of line bundles gives

$$
r:P\longrightarrow J_C. \tag{7.6}
$$

**Proposition 7.2.** For a sufficiently ample smooth $C$, the kernel of $r$ is finite. Consequently the pullback to $P$ of the theta polarization of $J_C$ is a polarization.

**Proof.** The tangent space of $P$ injects into the tangent space of the full Picard scheme, so

$$
T_0P\hookrightarrow H^1(X,\mathcal O_X),
\qquad
T_0J_C=H^1(C,\mathcal O_C).
$$

The exact sequence

$$
0\longrightarrow\mathcal O_X(-C)\longrightarrow
\mathcal O_X\longrightarrow\mathcal O_C\longrightarrow0 \tag{7.7}
$$

shows that $H^1(X,\mathcal O_X)\to H^1(C,\mathcal O_C)$, and hence the tangent map of $r$, is injective once
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

For completeness, that identification does not require a comparison theorem beyond Kummer theory. The Kummer sequence gives

$$
H^1(\bar X,\mu_{\ell^n})\simeq
\operatorname{Pic}(\bar X)[\ell^n]. \tag{7.8}
$$

The Néron--Severi theorem says that divisor classes modulo algebraic
equivalence form a finitely generated group. Its bounded
$\ell$-primary torsion contributes nothing to the inverse limit under
multiplication by $\ell$. The possible nonreduced quotient of the Picard
identity component is a finite connected group scheme of $p$-power order and
has no prime-to-$p$ Tate module. Taking inverse limits in (7.8) therefore
gives

$$
T_\ell P\simeq H^1(\bar X,\mathbf Z_\ell(1)),
\qquad
H^1(\bar X,\mathbf Q_\ell)\simeq V_\ell P^\vee. \tag{7.9}
$$

The second isomorphism uses Poincaré duality and the polarization just constructed; its Galois action and twist agree with (1.2). Under restriction to $C$, (7.9) is the Tate-module map induced by $r$, and the Weil-pairing/cup-product compatibility identifies its alternating form with (8.6). This proves the precise interface used below rather than assuming surface Picard theory by analogy with curves.

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

Poincaré duality identifies the target with $H^1(\bar X)^\vee(-1)$, and the $\mathbf Q_\ell(-1)$-valued bilinear form represented by (8.5) is

$$
(x,y)\longmapsto
\operatorname{Tr}_C(i^*x\smile i^*y). \tag{8.6}
$$

Here $\operatorname{Tr}_C:H^2(\bar C,\mathbf Q_\ell)\to\mathbf Q_\ell(-1)$ is the untwisted trace. Proposition 7.2 says that the restriction of the curve's theta polarization to the reduced connected Picard variety of $X$ is a polarization. Its Weil form is perfect on the rational Tate module. Through Kummer theory this is exactly (8.6), including its twist. Hence (8.6) is nondegenerate, so (8.5) is injective. Source and target have equal dimension by Poincaré duality, and it is therefore an isomorphism.

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

After a finite extension of $\mathbf F_q$, the line can be chosen transverse to the discriminant away from its singular locus. The resulting map is smooth over a dense open $j:U\hookrightarrow\mathbf P^1$, and every geometric singular fiber is geometrically irreducible and has one ordinary quadratic singularity. Because the fibers are curves, this means one node.

Here is why a suitable line exists. The incidence variety of pairs $(x,H)$ with $T_xX\subset H$ maps to the dual projective space. For a high Veronese embedding, separation of length-three subschemes makes this map generically finite onto a divisor and makes the locus of worse contact codimension at least two. Taking the power still higher makes the locus of reducible hyperplane sections codimension at least two: if a divisor splits, both effective summands have positive intersection with the fixed ample class, and the Hilbert-polynomial parameter spaces for such splittings have smaller dimension than the full linear system. Lines avoiding these two loci and meeting the smooth part of the discriminant transversely form a nonempty open in the Grassmannian. Over a finite field this open may have no rational point, but it does after a finite extension. In characteristic two, the nodal local equation is taken in the form $uv-a$; the curve vanishing-cycle calculation is unchanged because it uses the tame prime-to-$p$ annulus, not division by two. Thus no restriction on $p$ is imposed.

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

is lisse and punctually pure of weight one by smooth proper base change and Theorem 4.2 on every fiber. Its alternating pairing takes values in $\mathbf Q_\ell(-1)$, so its determinant is $\mathbf Q_\ell(-g)$ times a finite character. Formula (9.3) identifies the stalk of $j_*\mathcal V$ at $s$ with the invariant cycles. The normalization sequence of the irreducible one-node fiber identifies those invariants with an extension of the weight-one $H^1$ of its normalization by the weight-zero loop class. In particular the boundary Frobenius polynomials are rational and the conductor is finite, as required in Section 5.2.

For this pencil one can say more and avoid assuming a general semisimplicity theorem. Let $E\subset V$ be the span of the vanishing cycles. Formula (9.2) shows that $E$ and $E^\perp$ are monodromy stable and that $E^\perp$ is the subspace fixed by every local transvection. We justify the invariant-cycle identification used next. The Leray edge map restricts a class on $\widetilde X$ to a smooth fiber. Conversely, a class fixed by all local monodromies extends across each punctured strict henselian disc because (9.3) identifies invariants with the cohomology of the nodal fiber; the proper base-change classes glue to a section of $R^1f_*\mathbf Q_\ell$ on $\mathbf P^1$. An exceptional curve over a rational base point is a section of $f$ and splits the unit map, so the only possible Leray differential from this group to $H^2(\mathbf P^1,R^0f_*\mathbf Q_\ell)$ vanishes. The edge sequence therefore lifts the glued section to $H^1(\overline{\widetilde X})$. Hence $E^\perp$ is exactly the image of $H^1(\overline{\widetilde X})$.

We still have to prove that the alternating form is nondegenerate on this
image; hard Lefschetz for an ample class does not by itself do so, because a
fiber has self-intersection zero. Put
$Q=(\operatorname{Pic}^0_{\widetilde X})_{\mathrm{red}}$ and restrict
algebraically trivial line bundles to the geometric generic fiber. This gives
a homomorphism

$$
Q_{\bar\eta}\longrightarrow J_{\widetilde X_{\bar\eta}}. \tag{9.4b}
$$

Its kernel is finite. Indeed, a positive-dimensional connected kernel would
give a nonconstant family of algebraically trivial line bundles on
$\widetilde X$ that is trivial on the generic fiber. Separatedness of the
relative Picard functor makes it trivial on every fiber; the see-saw lemma
then makes it the pullback of a family in
$\operatorname{Pic}^0(\mathbf P^1)=0$, a contradiction. Pullback of the
theta polarization along (9.4b) is therefore a polarization of $Q$. Kummer
theory identifies its rational Tate module with the image of
$H^1(\overline{\widetilde X})$ in $V$, while compatibility of the Weil and
cup-product pairings identifies its alternating form with the restriction of
$\langle\ ,\ \rangle$. That restriction is consequently nondegenerate, so

$$
V=E^\perp\oplus (E^\perp)^\perp. \tag{9.4a}
$$

The first summand is constant. The second is irreducible under the geometric
monodromy. Indeed, the conormal incidence variety over the smooth locus of
the dual discriminant is geometrically irreducible: it is a dense open in a
projective-space bundle over $X$. Thus the vanishing cycles in the full
hyperplane family form one geometric conjugacy class.

We use the fundamental-group slicing assertion for a general line, in its
precise étale form:

$$
\pi_1(U_{\bar k})\longrightarrow
\pi_1(((\mathbf P^N)^\vee\setminus\Delta)_{\bar k})
\quad\text{is surjective}. \tag{9.4c}
$$

Here the codimension-two worse-contact locus has first been removed from
$\Delta$. To prove (9.4c), test it on a connected finite étale cover of the
right-hand complement, normalize $(\mathbf P^N)^\vee$ in that cover, and take
successive general hyperplane sections through the chosen line. Bertini
connectedness for the normalization says that the inverse image of each
section remains connected; purity of the branch locus says that removing
the codimension-two bad set does not disconnect it. The inverse image of
$U$ is therefore connected. This criterion for every finite quotient is
exactly surjectivity of geometric étale fundamental groups. The argument is
unchanged after the finite field extension used to choose the line.

Consequently all vanishing cycles in the pencil are conjugate. If a nonzero
invariant subspace contains a vector pairing nontrivially with some
$\delta_s$, subtracting its transform under (9.2) makes it contain
$\delta_s$, and conjugacy makes it contain every vanishing cycle, hence their
span $(E^\perp)^\perp$. If it pairs trivially with every $\delta_s$, it lies
in $E^\perp$ and has zero intersection with the second summand. Thus the
nonconstant summand is geometrically irreducible. It also has infinite
geometric monodromy: any nontrivial transvection $1+N_s$ has the distinct
powers $1+mN_s$ in characteristic zero. Its transvection directions span
the summand and form one orbit, so Lemma 5.3 identifies its geometric
algebraic monodromy group with the full symplectic group. Punctual purity,
the normalized determinant-one pairing, rational local and boundary
polynomials, and finite tame conductor now verify every hypothesis of
Theorem 5.2.

### 9.3 The direct-image decomposition

We next locate $H^2(\widetilde X)$ in the Leray spectral sequence. The smooth fibers are connected curves, so over $U$

$$
R^0f_*\mathbf Q_\ell=\mathbf Q_\ell,\qquad
R^1f_*\mathbf Q_\ell=\mathcal V,\qquad
R^2f_*\mathbf Q_\ell=\mathbf Q_\ell(-1). \tag{9.5}
$$

Proper base change and the normalization sequence extend the outer sheaves across a nodal fiber and identify the middle direct image with $j_*\mathcal V$. Geometric irreducibility of the chosen nodal fibers ensures that no extra top-dimensional component appears. Thus the degree-two part of Leray has graded pieces

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

Any constant part of $\mathcal V$ contributes $H^1(\mathbf P^1,\text{constant})=0$. For the nonconstant part, Theorem 5.2 gives

$$
|\iota(\beta)|=q
\quad
(\beta\text{ on }H_p^1(U,\mathcal V)) \tag{9.9}
$$

for every complex embedding $\iota$. Thus all three quotients of the
filtration (9.7) are pure of weight two. The global cross terms which were
absent from a local moment calculation have entered through the global
tensor determinant in Lemma 5.1.

For comparison, the elementary annulus alone would have yielded only the
coarser estimate

$$
\left|\#X(\mathbf F_{q^n})-(q^{2n}+1)\right|
\le b_1q^{n/2}+(b_2+b_3)q^{3n/2}. \tag{9.10}
$$

The theorem improves the middle contribution from the upper edge
$q^{3n/2}$ to its exact scale $q^n$ in Section 10.4.

## 10. The Riemann hypothesis for smooth proper surfaces

### 10.1 The pencil contribution has weight two

Apply Theorem 5.2 to the nonconstant direct summand of $\mathcal V$
furnished by (9.4a), whose hypotheses were checked in Section 9.2. The
constant summand contributes no $H^1$ on $\mathbf P^1$. Thus all three
graded pieces in (9.7) are pure of weight two.

An extension of pure Frobenius modules of the same weight is pure of that weight. Therefore

$$
H^2(\overline{\widetilde X},\mathbf Q_\ell)
\quad\text{is pure of weight }2. \tag{10.1}
$$

This includes both divisor classes and the transcendental part. The infinite-monodromy case of Theorem 5.2 is essential for the latter.

### 10.2 Blowing up does not change the question

If $\pi:\widetilde X\to X$ blows up one geometric point with exceptional curve $E$, purity and localization give the Frobenius-equivariant decomposition

$$
H^2(\overline{\widetilde X},\mathbf Q_\ell)
\simeq \pi^*H^2(\bar X,\mathbf Q_\ell)
\oplus \mathbf Q_\ell[E]. \tag{10.2}
$$

The twisted class $[E]\in H^2(1)$ is fixed when the point is rational, so the untwisted eigenvalue is $q$. If the center is a finite Frobenius orbit, the exceptional classes form a permutation representation tensored with $\mathbf Q_\ell(-1)$; their eigenvalues are $q$ times roots of unity and still have weight two.

Projection satisfies $\pi_*\pi^*=1$, so $H^2(\bar X)$ is a Frobenius-stable direct summand of (10.2). Purity passes to subobjects. Consequently, iteration over the finite base locus of the pencil proves

$$
H^2(\bar X,\mathbf Q_\ell)\text{ is pure of weight }2. \tag{10.3}
$$

The argument has been written for projective $X$. A smooth proper surface over a finite field is projective: Chow's lemma gives a projective birational surface, resolution makes it smooth, and the exceptional intersection matrix is negative definite; successively contracting the curves orthogonal to the pullback of a sufficiently positive divisor produces an ample divisor on $X$. Thus the reduction applies to smooth proper surfaces as well. In applications where a polarization is already part of the moduli problem, this reduction is unnecessary.

### 10.3 Purity in all five degrees

The degrees assemble without using a later one to prove an earlier one.

- $H^0=\mathbf Q_\ell$ is pure of weight zero.
- The reduced connected Picard variety $P=(\operatorname{Pic}^0_X)_{\mathrm{red}}$ and prime-to-$p$ Kummer theory identify $H^1(\bar X)$ with $V_\ell P^\vee$. The abelian Frobenius theorem proves weight one.
- The pencil argument and Theorem 5.2 give weight two for $H^2$.
- Hard Lefschetz gives $H^1\xrightarrow{\sim}H^3(1)$. Since twisting by $(1)$ lowers weight by two, $H^3$ has weight three.
- The trace isomorphism $H^4=\mathbf Q_\ell(-2)$ gives weight four.

**Theorem 10.1 (surface Riemann hypothesis).** Let $X/\mathbf F_q$ be smooth, proper, and geometrically connected of dimension two. For every $0\le i\le4$, every eigenvalue $\alpha$ of geometric Frobenius on $H^i(\bar X,\mathbf Q_\ell)$ is algebraic and satisfies

$$
|\iota(\alpha)|=q^{i/2} \tag{10.4}
$$

for every complex embedding $\iota$. Equivalently, $H^i$ is pure of weight $i$.

There is also a coefficient form with explicit hypotheses. Call a lisse
punctually pure sheaf $\mathcal F$ of weight $w$ on $X$
**pencil-admissible** if its restrictions to the smooth pencil fibers and
the lisse direct-image constituents on the base are geometrically
semisimple and determinant-normalized in the sense of Section 5.2, with the
stated rational boundary polynomials and finite conductors. Theorem 5.2 on
the fibers gives
weight $w+1$ in degree one; degrees zero and two follow from invariants and
curve duality. Thus $R^bf_*\mathcal F$ is punctually pure of weight $w+b$.
Apply Theorem 5.2 to its determinant-normalized constituents on the base.
This gives weight $w+a+b$ to

$$
H^a(\mathbf P^1,j_*R^bf_*\mathcal F).
$$

The coefficient blowup calculation is equally explicit.  For the finite
smooth base locus $B$ and $\pi:\widetilde X\to X$,

$$
H^i(\overline{\widetilde X},\pi^*\mathcal F)
\simeq H^i(\bar X,\mathcal F)
\oplus H^{i-2}(\bar B,\mathcal F|_{\bar B})(-1). \tag{10.4b}
$$

The exceptional term is nonzero only in the shifted point degree and has
weight $w+2$, exactly $w+i$ there.  Projection and pullback split the first
summand.  The Leray filtration and (10.4b) therefore prove

$$
H^i(\bar X,\mathcal F)\text{ is pure of weight }w+i. \tag{10.4a}
$$

Thus (10.4a) is a theorem for pencil-admissible coefficients. The adjective
records genuine checkable hypotheses; it is not shorthand for an assumed
weight theorem. Constant coefficients are pencil-admissible by Sections
9.2 and 5.5.

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

is a strict normal-crossings divisor. Put $D^{(1)}=\coprod_aD_a$ and let $D^{(2)}$ be the finite disjoint union of pairwise intersections indexed once after fixing an order on $A$, with the usual alternating incidence map. Repeated localization gives the residue spectral sequence

$$
E_1^{-r,n+r}
=H^{n-r}(\overline{D^{(r)}},\mathbf Q_\ell(-r))
\Longrightarrow H^n(\bar U,\mathbf Q_\ell),
\qquad r=0,1,2, \tag{11.1}
$$

where $D^{(0)}=X$ and terms outside the cohomological range vanish. Theorem 10.1 gives purity for the $r=0$ proper-surface term, the curves $D_a$ are pure in degrees $0,1,2$, and intersection points are pure in degree zero. The displayed term has weight $(n-r)+2r=n+r$, at least $n$. The incidence maps commute with Frobenius because they are alternating sums of Gysin and restriction maps defined over the ground field. The compactly supported sequence is the Verdier dual of (11.1).

### 11.2 Weight inequalities

The spectral sequence (11.1) gives a finite Frobenius-stable filtration on each ordinary cohomology group whose graded subquotients have weight at least the total degree. Poincaré duality for the smooth surface identifies $H_c^i(U)^\vee$ with $H^{4-i}(U)(2)$; applying the ordinary bound in degree $4-i$ and undoing the twist gives the compact bound. Consequently,

$$
H_c^i(\bar U,\mathbf Q_\ell)\text{ has weights }\le i,
\qquad
H^i(\bar U,\mathbf Q_\ell)\text{ has weights }\ge i. \tag{11.2}
$$

There is a clean coefficient version when no boundary extension theorem is
being hidden. Let $\mathcal F$ extend to a pencil-admissible lisse
punctually pure sheaf $\widetilde{\mathcal F}$ of weight $w$ on $X$, and
assume its restrictions to the curves $D_a$ are determinant-normalized in
the sense of Section 5.2. Apply (10.4a), Theorem 5.2 on the divisors, and
the residue spectral sequence with these coefficients. This gives

$$
H_c^i(\bar U,\mathcal F)\text{ has weights }\le w+i,
\qquad
H^i(\bar U,\mathcal F)\text{ has weights }\ge w+i. \tag{11.3}
$$

Indeed, the $r=0$ term has weight $w+n$ by (10.4a), the divisor terms have
weight $w+n+1$, and the double-intersection terms have weight $w+n+2$ in
the degrees in which they occur. Duality gives the compact inequality.

If $\mathcal F$ does not extend lisse across $D$, a logarithmic or
inertia-graded residue complex may replace this one, but then (11.3) is
valid only after **each** term in total degree $n$ has been proved to have
weight at least $w+n$. The phrases “finite monodromy” and “unipotent
monodromy” by themselves do not prove those termwise estimates. This book
therefore uses (11.3) only under the lisse-extension hypotheses just stated,
or under an explicitly supplied termwise residue-weight calculation.

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

**Theorem 11.1 (interior purity in dimension two).** Under the lisse-extension or explicit termwise residue-weight hypotheses above, $H_!^i(\bar U,\mathcal F)$ is pure of weight $w+i$. In particular,

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
fibers over a finite field, and Theorem 11.1 concerns a smooth open surface
with controlled boundary. Neither statement says that arbitrary singular
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

is Frobenius stable and pure of weight two. Every unramified geometric Frobenius eigenvalue $\alpha_v$ at a residue field of size $q_v$ therefore satisfies

$$
|\iota(\alpha_v)|=q_v \tag{12.4}
$$

under every complex embedding.

One must distinguish a rational projector from an integral summand. Denominators in $e_{\mathfrak m}$ may prevent a splitting of the $\mathbf Z_\ell$ lattice. Purity is a statement about the rational representation and survives; lattice saturation is a separate integral problem.

For an open smooth surface, replace $H^2$ in (12.3) by $H_!^2$. Properly supported correspondences preserve the map $H_c^2\to H^2$, hence act on its image. Theorem 11.1 gives weight two under its explicit lisse-extension or termwise residue-weight hypotheses. Taking an arbitrary quotient of $H^2$ before removing boundary cohomology can retain weights greater than two and is unsafe.

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

This isolation statement uses no assertion that all middle cohomology is automorphic or algebraic. Geometry proves proper or interior middle purity first; the projector then passes that purity to the selected constituent.

## 13. Families, good reduction, and coefficient changes

### 13.1 Smooth proper families

Let $f:X\to S$ be smooth and proper of relative dimension at most two with $\ell$ invertible. Smooth proper base change makes $R^if_*\mathbf Q_\ell$ lisse and identifies its geometric stalks with fiber cohomology. If $s$ is a finite-field point, Theorems 4.2 and 10.1 give

$$
(R^if_*\mathbf Q_\ell)_{\bar s}
$$

pure of weight $i$. Thus the direct-image sheaf is punctually pure of weight $i$ on every finite-field stratum.

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

The generic representation is unramified, and its unramified geometric Frobenius corresponds to $F$ on the special fiber. In relative dimension at most two every eigenvalue is therefore pure of weight $i$. A correspondence extending properly across the model commutes with (13.2), so the same statement holds on its projector summands.

More generally, if a lisse sheaf on $\mathcal X$ restricts to a
pencil-admissible punctually pure sheaf of weight $w$ on the special
surface, proper base change with coefficients identifies the two fiber
groups and (10.4a) gives weight $w+i$ on the generic unramified group.
The coefficient sheaf must extend lisse across the model; a representation
given only on the generic fiber is not covered by this assertion.

Good reduction is essential here. At semistable reduction inertia can be nontrivial and the Weil--Deligne representation carries a monodromy filtration. The total object is pure only in the monodromy sense, not because every inertia-invariant subquotient has the same naive weight.

### 13.3 Changing the auxiliary prime

For a smooth proper curve or surface over $\mathbf F_q$, the trace formula expresses $Z(X,t)$ through the $P_i(t)$, and purity puts their reciprocal roots on disjoint circles. Therefore $Z(X,t)$ uniquely recovers each $P_i$, proving that its Frobenius polynomial is independent of $\ell$ and integral, as observed after (10.6).

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
5. Theorem 5.2 uses the external global tensor determinant (5.11) and the
   correspondence trace formula (5.11b), not a local Schur moment. Common
   rationality, normalized determinant, finite conductor, tensor invariants,
   connected monodromy, and Rosati positivity all enter Lemma 5.1.
6. Smooth proper purity is proved for curves and surfaces. Open varieties satisfy the stated inequalities, and their interior image is pure under the explicit boundary hypotheses.
7. Singular ordinary cohomology is not silently identified with intersection cohomology.
8. A rational correspondence projector gives a rational summand, not necessarily an integral direct summand.
9. Good-reduction comparison transports purity for curves and surfaces; semistable reduction additionally requires monodromy.
10. A finite extension used to construct a pencil changes $(F,q)$ to $(F^a,q^a)$ and therefore neither creates nor destroys the claimed weight.

## 14. The low-dimensional weight package

### 14.1 The complete theorem

The proved package is the following.

**Theorem 14.1 (weights, hard Lefschetz, and Weil bounds in low dimension).** Fix $\ell\ne p$.

1. If $C/\mathbf F_q$ is smooth, proper, and geometrically connected, then $H^i(\bar C,\mathbf Q_\ell)$ is pure of weight $i$. Its zeta numerator has integral coefficients, degree $2g$, reciprocal roots of modulus $\sqrt q$, and

   $$
   \left|\#C(\mathbf F_{q^n})-(q^n+1)\right|
   \le2gq^{n/2}.
   $$

2. If $j:U\hookrightarrow C$ and $\mathcal F$ is determinant-normalized pure of weight $w$, including with infinite connected geometric monodromy, then $H^1(\bar C,j_*\mathcal F)$ is pure of weight $w+1$. With the stated local boundary-weight calculation, compact cohomology has weights at most $w+i$, ordinary cohomology has weights at least $w+i$, and their image is pure of weight $w+i$.
3. If $X$ is smooth projective of pure dimension $d\le2$ over a field and $L$ is ample, then

   $$
   \mathsf L^{d-i}:H^i(\bar X,\mathbf Q_\ell)
   \xrightarrow{\sim}
   H^{2d-i}(\bar X,\mathbf Q_\ell(d-i))
   $$

   for $0\le i\le d$.
4. If $X/\mathbf F_q$ is smooth, proper, and geometrically connected of dimension two, then $H^i(\bar X,\mathbf Q_\ell)$ is pure of weight $i$ for $0\le i\le4$. Its Frobenius polynomials are integral and independent of $\ell$, and its point counts satisfy (10.6).
5. If a smooth open surface has a smooth proper strict-normal-crossings compactification, then $H_c^i$ has weights $\le i$, $H^i$ has weights $\ge i$, and $H_!^i$ is pure of weight $i$. The coefficient version holds under the pencil-admissibility and lisse-extension or explicit termwise residue-weight hypotheses of Sections 10.3 and 11.2.
6. Frobenius-compatible algebraic correspondence projectors preserve these statements. In particular, a projector summand of proper $H^2$, or of open $H_!^2$, is pure of weight two.
7. Every clause is compatible with smooth proper base change and good reduction, including ample Lefschetz operators and properly extending correspondences.

### 14.2 How the ingredients depend on one another

The logical order is:

$$
\begin{array}{ccccc}
\text{ample intersections}
&\Longrightarrow&\text{Rosati positivity}
&\Longrightarrow&\text{curve purity and Hasse--Weil}\\
&&&&\downarrow\\
\text{rational global determinants and tensor invariants}
&\Longrightarrow&\text{positive adjoint on }H_p^1
&\Longrightarrow&\text{curve-sheaf RH}\\
&&&&\downarrow\\
\text{Lefschetz pencil}
&\Longrightarrow&\text{surface }H^2\text{ filtration}
&\Longrightarrow&\text{surface purity and its consequences}.
\end{array}
$$

Weak Lefschetz and the Picard polarization prove hard Lefschetz for surfaces independently of the weight argument. The coefficient step is also noncircular: pointwise purity of $R^1f_*$ comes from the already completed curve theorem, while Picard--Lefschetz transvections and Lemma 5.3 give full symplectic monodromy before Theorem 5.2 is applied.

The distinction between local and global tensor operations is decisive.
Local Schur moments see only repeated factors over one point.  The external
complex (5.11) is formed before contraction, and (5.11b) therefore retains
independent tuples and all global cross terms.  The Cartan--Leray complex
(5.11a) also retains the cochains of the congruence kernel; it does not
pretend that an infinite-monodromy characteristic-zero representation
factors through a finite deck group.  Bounded residual determinant degree
and Newton identities descend the result to the fixed number field; Rosati
positivity on the cover Jacobians then makes the adjoint involution positive.

### 14.3 Final synthesis

Weights turn Frobenius from a formal endomorphism into a measured one. On a curve, the Jacobian packages $H^1$ into an abelian variety, an ample theta divisor makes Rosati positive, and $\pi\pi^\dagger=q$ forces every Frobenius conjugate onto the circle of radius $\sqrt q$. The trace formula then gives the Hasse--Weil bound over every finite extension.

On a surface, an ample class has two roles. A smooth section polarizes the reduced connected Picard variety and proves hard Lefschetz in the only nonformal degree. A pencil identifies the new middle cohomology with parabolic cohomology of the weight-one sheaf $R^1f_*\mathbf Q_\ell$. Its nonconstant part has infinite transvection monodromy, full symplectic algebraic closure, controlled determinant, and rational local data. The curve-sheaf theorem therefore puts its global roots on $|\beta|=q$.

Blowup descent returns weight two to the original surface, hard Lefschetz carries weight one to weight three, and trace supplies weights zero and four. Boundary strata then give the open-surface inequalities and interior purity. Algebraic correspondences commute with Frobenius and preserve the interior image, so rational Hecke projectors isolate genuine weight-two representations without importing boundary eigenvalues or assuming that all middle cohomology is algebraic.

The resulting package is complete in the stated range: hard Lefschetz holds for smooth projective curves and surfaces with the correct twists; smooth proper finite-field cohomology is pure in every degree through dimension two; curves and surfaces satisfy the displayed Weil bounds; and properly defined correspondence summands inherit the expected weight.
