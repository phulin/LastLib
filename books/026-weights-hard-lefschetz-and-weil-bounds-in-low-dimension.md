# Weights and Weil Bounds for Curves and Abelian Varieties

## Contents

[1. The size hidden in a Frobenius eigenvalue](#1-the-size-hidden-in-a-frobenius-eigenvalue)
   - [1.1 The problem left by the trace formula](#11-the-problem-left-by-the-trace-formula)
   - [1.2 Standing conventions](#12-standing-conventions)
   - [1.3 Algebraic numbers and Weil numbers](#13-algebraic-numbers-and-weil-numbers)
   - [1.4 The route through the proof](#14-the-route-through-the-proof)
[2. Weights and their elementary calculus](#2-weights-and-their-elementary-calculus)
   - [2.1 Pure representations](#21-pure-representations)
   - [2.2 Tate twists, duals, and tensors](#22-tate-twists-duals-and-tensors)
   - [2.3 Lisse sheaves and closed points](#23-lisse-sheaves-and-closed-points)
   - [2.4 Mixed objects and strict weight separation](#24-mixed-objects-and-strict-weight-separation)
[3. Polarizations and the positivity missing from duality](#3-polarizations-and-the-positivity-missing-from-duality)
   - [3.1 Degree as a positive polynomial](#31-degree-as-a-positive-polynomial)
   - [3.2 The Rosati trace form](#32-the-rosati-trace-form)
   - [3.3 Positive involutions on number fields](#33-positive-involutions-on-number-fields)
   - [3.4 Frobenius and Verschiebung](#34-frobenius-and-verschiebung)
[4. The Riemann hypothesis for abelian varieties and curves](#4-the-riemann-hypothesis-for-abelian-varieties-and-curves)
   - [4.1 Abelian varieties over a finite field](#41-abelian-varieties-over-a-finite-field)
   - [4.2 From a curve to its Jacobian](#42-from-a-curve-to-its-jacobian)
   - [4.3 The curve zeta function](#43-the-curve-zeta-function)
   - [4.4 The Hasse--Weil bounds](#44-the-hasse--weil-bounds)
[5. Pure lisse sheaves on curves](#5-pure-lisse-sheaves-on-curves)
   - [5.1 Why coefficients on curves require a separate theorem](#51-why-coefficients-on-curves-require-a-separate-theorem)
   - [5.2 Normalization, determinant, and rationality](#52-normalization-determinant-and-rationality)
   - [5.3 Tensor invariants and the positive determinant lemma](#53-tensor-invariants-and-the-positive-determinant-lemma)
   - [5.4 The curve-sheaf Riemann hypothesis](#54-the-curve-sheaf-riemann-hypothesis)
   - [5.5 The symplectic monodromy criterion](#55-the-symplectic-monodromy-criterion)
[6. Weights on open curves](#6-weights-on-open-curves)
   - [6.1 Boundary invariants and coinvariants](#61-boundary-invariants-and-coinvariants)
   - [6.2 Compact support and ordinary support](#62-compact-support-and-ordinary-support)
   - [6.3 Mixedness and the interior group](#63-mixedness-and-the-interior-group)
   - [6.4 Examples that fix the normalizations](#64-examples-that-fix-the-normalizations)
[7. Correspondences and pure summands](#7-correspondences-and-pure-summands)
   - [7.1 Frobenius-compatible projectors](#71-frobenius-compatible-projectors)
   - [7.2 Transpose, adjoints, and reciprocal pairs](#72-transpose-adjoints-and-reciprocal-pairs)
   - [7.3 Coefficient sheaves and parabolic summands](#73-coefficient-sheaves-and-parabolic-summands)
[8. Families, good reduction, and coefficient changes](#8-families-good-reduction-and-coefficient-changes)
   - [8.1 Smooth proper curve and abelian families](#81-smooth-proper-curve-and-abelian-families)
   - [8.2 Good reduction](#82-good-reduction)
   - [8.3 Changing the auxiliary prime](#83-changing-the-auxiliary-prime)
   - [8.4 A normalization and hypothesis audit](#84-a-normalization-and-hypothesis-audit)
[9. The curve and abelian weight package](#9-the-curve-and-abelian-weight-package)
   - [9.1 The complete theorem](#91-the-complete-theorem)
   - [9.2 How the ingredients depend on one another](#92-how-the-ingredients-depend-on-one-another)
   - [9.3 Final synthesis](#93-final-synthesis)

## 1. The size hidden in a Frobenius eigenvalue

### 1.1 The problem left by the trace formula

Let $X$ be a variety over $k=\mathbf F_q$, and let $F$ denote geometric Frobenius on geometric étale cohomology. The trace formula developed earlier gives

$$
\#X(\mathbf F_{q^n})
=\sum_i(-1)^i\operatorname{Tr}
\left(F^n\mid H_c^i(\bar X,\mathbf Q_\ell)\right). \tag{1.1}
$$

This identity organizes every extension-field count into finitely many eigenvalues. It does not say how large those eigenvalues are. Duality gives the reciprocal relation $\alpha\leftrightarrow q^d/\alpha$ on a smooth proper $d$-fold, but reciprocal pairs can lie arbitrarily far from the circle of radius $q^{d/2}$. The missing assertion is a positivity theorem.

For a smooth proper variety the expected answer is exquisitely simple: an eigenvalue in $H^i$ has complex absolute value $q^{i/2}$. The integer $i$ is its **weight**. For curves and abelian varieties this statement explains the scale of the error in point counting, places zeta zeros and poles on prescribed circles, and ensures that a Frobenius-compatible correspondence projector inherits the weight of its ambient cohomological degree.

This book proves that answer for abelian varieties and smooth proper curves, proves the corresponding Weil bounds, and establishes the curve-sheaf Riemann hypothesis for pure lisse coefficients. Chapter 5 closes the infinite-monodromy coefficient estimate: determinant rationality and tensor invariant projectors recover the global parabolic Frobenius algebra from polarized curve covers, and Rosati positivity forces its adjoint involution to be complex conjugation. Frobenius-compatible correspondence summands then inherit purity without any semisimplicity assumption on the ambient representation.

### 1.2 Standing conventions

Fix a prime $\ell\ne p=\operatorname{char}k$ and an algebraic closure $\bar k$. All cohomology is geometric étale cohomology with $\mathbf Q_\ell$ coefficients unless another coefficient ring is displayed. A variety is separated and of finite type. The words smooth, proper, projective, and geometrically connected are never implicit.

Arithmetic Frobenius is $\varphi:a\mapsto a^q$ in $\operatorname{Gal}(\bar k/k)$; geometric Frobenius is $F=\varphi^{-1}$ on geometric cohomology. With this convention,

$$
F\mid \mathbf Q_\ell(1)=q^{-1},
\qquad
F\mid \mathbf Q_\ell(-1)=q. \tag{1.2}
$$

Consequently the fundamental class of a smooth proper curve lies in $H^2=\mathbf Q_\ell(-1)$ and has eigenvalue $q$. Together with the identity $\pi\pi^\dagger=[q]$ for an abelian variety, this checks the Frobenius normalization used below.

The established duality theory supplies perfect pairings

$$
H^i(\bar X,\mathbf Q_\ell)\times
H^{2d-i}(\bar X,\mathbf Q_\ell(d))\longrightarrow\mathbf Q_\ell, \tag{1.3}
$$

and compatibility with cycle classes, transpose correspondences, and trace. The established trace theory supplies (1.1), Künneth, rationality, and the functional equation, but no absolute-value estimate. Projective geometry supplies ample polarizations, while the theory of algebraic correspondences supplies the projectors used in Chapter 7. The theory of Jacobians supplies

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

Third, localization at the missing points of an open curve separates boundary invariants and coinvariants from parabolic cohomology. This gives the sharp weight inequalities and identifies the interior image as the pure part in the stated coefficient range.

Finally, algebraic correspondences commute with Frobenius. An idempotent therefore cuts a Frobenius-stable direct summand whose eigenvalues already occur in the ambient pure curve or abelian-variety cohomology. The same argument applies to parabolic cohomology with a pure coefficient sheaf.

## 2. Weights and their elementary calculus

### 2.1 Pure representations

Let $V$ be a finite-dimensional $\mathbf Q_\ell$-vector space with an automorphism $F$ whose characteristic polynomial has algebraic coefficients. We call $V$ **pure of weight $w$** if every eigenvalue of $F$ is a $q$-Weil number of weight $w$. Semisimplicity is not part of the definition. A Jordan block changes traces by polynomial factors in $n$ but does not change the weights of its eigenvalues.

Purity is stable under subquotients: the characteristic polynomial on an invariant subspace and quotient divides that on $V$ after extension to an algebraic closure. It is also stable under extensions of pure objects of the same weight. It is not stable under an arbitrary direct sum of different weights; such a sum is mixed.

If $X$ is smooth proper and geometrically connected, the desired purity assertion is

$$
H^i(\bar X,\mathbf Q_\ell)
\text{ is pure of weight }i. \tag{2.1}
$$

For $i=0$ this follows from geometric connectedness. For $i=2d$ it follows from the trace orientation. Chapter 4 proves the assertion for curves and abelian varieties, and Chapter 5 proves the coefficient form on curves.

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

is punctually pure of weight $1$ once the curve theorem has been proved: proper base change identifies $\mathcal V_{\bar x}$ with $H^1(Y_{\bar x},\mathbf Q_\ell)$, and (2.2) is precisely the curve Riemann hypothesis over $k(x)$. This observation is a basic source of punctually pure coefficient sheaves on curves.

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

### 5.1 Why coefficients on curves require a separate theorem

A pure lisse sheaf on a curve can have infinite geometric monodromy, so its global cohomology is not reduced to the constant-coefficient curve theorem by a finite cover. The missing assertion is that degree-one parabolic cohomology adds exactly one to the punctual weight. Proving it requires a global positivity argument: determinant rationality places all Frobenius eigenvalues in one number field, tensor invariants construct the relevant projectors on curve covers, and Rosati positivity identifies the adjoint involution with complex conjugation.

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

A common geometric source of infinite monodromy has a particularly transparent check.

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

This illustrates how Theorem 5.2 applies to a nonconstant symplectic coefficient sheaf on a curve.

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

In the tame nodal-monodromy situation, $N^2=0$ and this filtration has only two steps. The required boundary check reduces to

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

For a determinant-normalized coefficient sheaf satisfying the boundary input stated after (6.2a), the same argument makes $H_!^i(U,\mathcal F)$ pure of weight $w+i$. This includes both finite-geometric-monodromy sheaves and an infinite-monodromy symplectic sheaf with the stated nodal boundary calculation. The formulation by image remains useful because correspondences preserve compact and ordinary cohomology and hence preserve their image.

### 6.4 Examples that fix the normalizations

For $U=\mathbf A^1$, $H_c^2=\mathbf Q_\ell(-1)$ has weight two and all other compactly supported groups vanish. For $U=\mathbf G_m$,

$$
H_c^1(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell,
\qquad
H_c^2(\bar U,\mathbf Q_\ell)=\mathbf Q_\ell(-1),
$$

of weights zero and two. The trace formula gives $q^n-1$. It would be wrong to assign weight one to $H_c^1$ merely because its cohomological degree is one; proper smoothness is what forces equality of weight and degree.

For a Kummer sheaf of finite order on $\mathbf G_m$, the finite-monodromy part of Theorem 5.2 applies. If the character is nontrivial at both ends, its parabolic $H^1$ is pure of weight one. A missing ramification condition can create invariant boundary stalks of weight zero, but those lie outside the parabolic image. This example also shows why the middle extension, rather than all of $H_c^1$, is the natural pure object.

## 7. Correspondences and pure summands

### 7.1 Frobenius-compatible projectors

Let $C/\mathbf F_q$ be a smooth proper geometrically connected curve and let $\Gamma$ be a codimension-one algebraic correspondence on $C\times C$, proper over both factors and defined over $\mathbf F_q$. Pull--cup--push defines

$$
\Gamma_*:H^i(\bar C,\mathbf Q_\ell)\longrightarrow H^i(\bar C,\mathbf Q_\ell),
$$

and $\Gamma_*$ commutes with geometric Frobenius. If $e$ is an idempotent in a rational correspondence algebra, then

$$
H^i(\bar C,\mathbf Q_\ell)
=
eH^i(\bar C,\mathbf Q_\ell)
\oplus
(1-e)H^i(\bar C,\mathbf Q_\ell).
\tag{7.1}
$$

Every Frobenius eigenvalue on the first summand already occurs on the ambient cohomology. Theorem 4.2 therefore gives the following reusable result.

**Proposition 7.1 (purity of curve correspondence summands).** Every Frobenius-compatible correspondence summand of $H^i(\bar C,\mathbf Q_\ell)$ is pure of weight $i$. In particular, a projector summand of $H^1$ is pure of weight one.

No semisimplicity of the ambient Galois representation is required: the idempotent itself supplies the splitting. The same eigenvalue argument applies to an abelian variety $A/\mathbf F_q$. Theorem 4.1 makes $H^1(\bar A)$ pure of weight one, the exterior-algebra description
$H^i(\bar A)\simeq\bigwedge^iH^1(\bar A)$ makes $H^i$ pure of weight $i$, and every correspondence summand inherits that weight.

### 7.2 Transpose, adjoints, and reciprocal pairs

Transpose correspondences are adjoint for Poincaré duality:

$$
\langle\Gamma_*x,y\rangle
=
\langle x,{}^t\Gamma_*y\rangle.
\tag{7.2}
$$

If $e={}^te$, the two summands in (7.1) are orthogonal. On $H^1(\bar C)$ the alternating pairing has values in $\mathbf Q_\ell(-1)$, so its restriction to $eH^1$ is nondegenerate and the eigenvalues occur in pairs

$$
\alpha,\qquad q/\alpha.
\tag{7.3}
$$

Adjointness alone gives only the product relation. Curve purity strengthens it to
$|\iota(\alpha)|=\sqrt q$ for every complex embedding. If the arithmetic adjoint is transpose followed by a polarization or moduli involution, that extra involution must be included; geometric transpose by itself does not supply it.

A rational projector need not preserve a chosen $\mathbf Z_\ell$-lattice. Denominators in $e$ may prevent an integral splitting even though the rational summand is pure. Saturation and congruences are separate integral questions.

### 7.3 Coefficient sheaves and parabolic summands

Let $j:U\hookrightarrow C$ and let $\mathcal F$ be a determinant-normalized punctually pure lisse sheaf of weight $w$ satisfying the hypotheses of Theorem 5.2. A properly supported curve correspondence equipped with an identification between the two pulled-back coefficient sheaves acts on

$$
H_p^1(U,\mathcal F)
=
H^1(\bar C,j_*\mathcal F).
$$

The coefficient identification is part of the correspondence datum; the underlying geometric diagram alone does not define the operator. If a rational idempotent $e$ in this correspondence algebra commutes with Frobenius, then

$$
eH_p^1(U,\mathcal F)
$$

is pure of weight $w+1$. Indeed, Theorem 5.2 makes the entire parabolic group pure of that weight, and an invariant direct summand cannot introduce a new eigenvalue.

For an open curve, properly supported correspondences also preserve the map
$H_c^1\to H^1$ and hence its image. Boundary invariants must still be kept separate from the parabolic summand: taking an arbitrary quotient before applying the middle-extension theorem can retain a boundary eigenvalue of a different weight.

## 8. Families, good reduction, and coefficient changes

### 8.1 Smooth proper curve and abelian families

Let $f:X\to S$ be either a smooth proper relative curve or an abelian scheme over a base on which $\ell$ is invertible. Smooth proper base change makes $R^if_*\mathbf Q_\ell$ lisse and identifies its geometric stalks with fiber cohomology. At a finite-field point, Theorems 4.1 and 4.2, together with the exterior-algebra description for an abelian variety, make the stalk pure of weight $i$.

Cup products, traces, polarizations, and properly supported correspondences commute with base change. Consequently every rational idempotent correspondence defines a lisse direct summand whose fiber at a finite-field point is pure of the same weight. This is a fiberwise statement; it does not say that the cohomology of an arbitrary higher-dimensional base is pure.

For a smooth proper family of curves $g:Y\to U$, the lisse sheaf
$R^1g_*\mathbf Q_\ell$ is punctually pure of weight one. Theorem 5.2 applies to its parabolic cohomology when the determinant, rationality, conductor, and monodromy hypotheses stated there are verified.

### 8.2 Good reduction

Let $\mathcal X$ be a smooth proper curve or an abelian scheme over a henselian discrete valuation ring with finite residue field $\mathbf F_q$. For $\ell$ different from the residue characteristic, smooth proper base change gives

$$
H^i(\overline{X_\eta},\mathbf Q_\ell)
\xrightarrow{\sim}
H^i(\overline{X_s},\mathbf Q_\ell).
\tag{8.1}
$$

The generic representation is unramified, and its unramified geometric Frobenius corresponds to Frobenius on the special fiber. Every eigenvalue is therefore pure of weight $i$. A correspondence extending properly across the model commutes with (8.1), so the same statement holds on its projector summands.

With coefficients, the sheaf must extend lisse across the model and retain the hypotheses of Theorem 5.2 on the special curve. A representation supplied only on the generic fiber is not covered. At semistable reduction inertia can be nontrivial and the Weil--Deligne representation carries a monodromy filtration; naive good-reduction purity is then not a substitute for the monodromy-weight statement.

### 8.3 Changing the auxiliary prime

For a smooth proper curve, the trace formula expresses the zeta function through the three cohomological polynomials, and their weights lie on distinct circles. The intrinsic zeta function therefore recovers the middle Frobenius polynomial, proving its integrality and independence of $\ell$. For an abelian variety, Theorem 4.1 obtains the common integral polynomial directly from the degree polynomial of Frobenius.

For a correspondence projector, independence of $\ell$ requires the correspondence and projector to be defined over a common number field and the simultaneous traces

$$
\operatorname{Tr}(eF^n\mid H^i)
$$

to be independent of $\ell$. The correspondence trace formula supplies this when $e$ is represented by algebraic cycles with common rational coefficients and proper fixed intersections. Without a common algebraic projector, equal dimensions at two auxiliary primes do not identify the representations.

Changing $\ell$ does not preserve a chosen integral lattice automatically. Rational Frobenius polynomials and weights can be common while saturation, torsion, and congruences vary prime by prime.

### 8.4 A normalization and hypothesis audit

The following checks prevent the common misapplications of the theory.

1. $F$ is geometric Frobenius. It acts on $\mathbf Q_\ell(1)$ by $q^{-1}$ and on $H^2$ of a proper curve by $q$.
2. Twisting by $(m)$ lowers weight by $2m$.
3. Pure weight $w$ means every complex conjugate has modulus $q^{w/2}$, not only one chosen embedding.
4. Theorem 5.2 uses the external global tensor determinant and the correspondence trace formula, not a local Schur moment. Common rationality, normalized determinant, finite conductor, tensor invariants, connected monodromy, and Rosati positivity all enter its proof.
5. A rational correspondence projector gives a rational summand, not necessarily an integral direct summand.
6. Open-curve ordinary and compactly supported cohomology contain boundary pieces; the parabolic image is the pure object under the stated hypotheses.
7. Good-reduction comparison transports purity for curves and abelian varieties; semistable reduction additionally requires monodromy.
8. A finite extension of constants replaces $(F,q)$ by $(F^a,q^a)$ and therefore neither creates nor destroys the claimed weight.

## 9. The curve and abelian weight package

### 9.1 The complete theorem

**Theorem 9.1 (weights and Weil bounds for curves and abelian varieties).** Fix $\ell\ne p$.

1. If $A/\mathbf F_q$ is an abelian variety, the Frobenius polynomial on $H^1$ is integral and independent of $\ell$, and all its roots have modulus $\sqrt q$ under every complex embedding. Since
   $H^i(\bar A)\simeq\bigwedge^iH^1(\bar A)$, $H^i(\bar A)$ is pure of weight $i$.
2. If $C/\mathbf F_q$ is smooth, proper, and geometrically connected, then $H^i(\bar C,\mathbf Q_\ell)$ is pure of weight $i$. Its zeta numerator has integral coefficients, degree $2g$, reciprocal roots of modulus $\sqrt q$, and
   $$
   \left|\#C(\mathbf F_{q^n})-(q^n+1)\right|
   \le2gq^{n/2}.
   $$
3. If $j:U\hookrightarrow C$ and $\mathcal F$ is determinant-normalized pure of weight $w$, including the stated infinite-connected-monodromy cases, then
   $H^1(\bar C,j_*\mathcal F)$ is pure of weight $w+1$. With the stated local boundary calculation, compact cohomology has weights at most $w+i$, ordinary cohomology has weights at least $w+i$, and their image is pure of weight $w+i$.
4. Frobenius-compatible algebraic correspondence projectors preserve these purity statements on curve cohomology, abelian-variety cohomology, and parabolic cohomology with pure coefficients.
5. All preceding clauses are compatible with smooth proper base change and good reduction when the varieties, coefficient sheaves, and correspondences extend with the hypotheses stated in Chapter 8.
6. A rational projector or purity statement does not by itself produce a saturated integral lattice or an $\ell$-independent integral splitting.

### 9.2 How the ingredients depend on one another

The logical order is

$$
\text{ample intersections}
\Longrightarrow
\text{Rosati positivity}
\Longrightarrow
\text{abelian and curve purity}
\Longrightarrow
\text{Hasse--Weil bounds},
$$

and, independently after curve purity,

$$
\text{global tensor determinants and invariant projectors}
\Longrightarrow
\text{positive adjoint on }H_p^1
\Longrightarrow
\text{curve-sheaf purity}.
$$

Correspondence projectors come last: they inherit already proved purity because an idempotent summand has no new Frobenius eigenvalues. This order is noncircular. The external tensor complex is formed before contraction and retains global cross terms; the Cartan--Leray complex retains the cochains of an infinite-monodromy congruence kernel; and Rosati positivity on cover Jacobians supplies the Archimedean estimate.

### 9.3 Final synthesis

Weights turn Frobenius from a formal endomorphism into a measured one. On an abelian variety, an ample polarization makes Rosati positive and
$\pi\pi^\dagger=[q]$ forces every Frobenius conjugate onto the circle of radius $\sqrt q$. On a curve, the Jacobian transfers that result to $H^1$, and the trace formula gives the Hasse--Weil bound over every finite extension.

Pure lisse sheaves on curves require an additional global argument because infinite monodromy cannot be killed by one finite cover. Determinant rationality, tensor invariant projectors, and positivity on curve-cover Jacobians put parabolic $H^1$ on the circle of weight $w+1$. Boundary invariants remain visible in ordinary and compactly supported cohomology and are not confused with the parabolic image.

Algebraic correspondences commute with Frobenius, so rational projectors pass these weights to selected curve, abelian, and coefficient-sheaf summands. Good reduction transports the resulting polynomials to unramified generic fibers. The package therefore retains exactly the Weil-number calculus, pure curve and abelian cohomology, pure sheaves on curves, and correspondence summands required by the modular and quaternionic curve spine.
