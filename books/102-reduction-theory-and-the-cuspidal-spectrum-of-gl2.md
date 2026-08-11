# Reduction Theory and the Cuspidal Spectrum of $\mathrm{GL}_2$

## Contents

1. [The global quotient and its escaping direction](#1-the-global-quotient-and-its-escaping-direction)
   - [The problem of infinity](#11-the-problem-of-infinity)
   - [Standing number-field notation](#12-standing-number-field-notation)
   - [The group, its center, and its parabolic](#13-the-group-its-center-and-its-parabolic)
   - [What reduction theory must prove](#14-what-reduction-theory-must-prove)
2. [Measures, centers, and quotient conventions](#2-measures-centers-and-quotient-conventions)
   - [Local and adelic measures](#21-local-and-adelic-measures)
   - [Iwasawa measure](#22-iwasawa-measure)
   - [Quotient measure and covolume](#23-quotient-measure-and-covolume)
   - [Removing the split center](#24-removing-the-split-center)
   - [Fixed central character](#25-fixed-central-character)
3. [Iwasawa coordinates and adelic height](#3-iwasawa-coordinates-and-adelic-height)
   - [Local Iwasawa decomposition](#31-local-iwasawa-decomposition)
   - [The root coordinate](#32-the-root-coordinate)
   - [Compact reduction of the torus](#33-compact-reduction-of-the-torus)
   - [Balanced archimedean representatives](#34-balanced-archimedean-representatives)
   - [Lattices and short lines](#35-lattices-and-short-lines)
4. [The adelic reduction theorem](#4-the-adelic-reduction-theorem)
   - [The unipotent reduction step](#41-the-unipotent-reduction-step)
   - [Finding a rational short line](#42-finding-a-rational-short-line)
   - [Reduction into a Siegel region](#43-reduction-into-a-siegel-region)
   - [The adelic reduction theorem](#44-the-adelic-reduction-theorem)
   - [Why the hypotheses are exact](#45-why-the-hypotheses-are-exact)
5. [Siegel sets and fundamental-domain estimates](#5-siegel-sets-and-fundamental-domain-estimates)
   - [Definition of a Siegel set](#51-definition-of-a-siegel-set)
   - [The Siegel intersection property](#52-the-siegel-intersection-property)
   - [Proof by rational matrix entries](#53-proof-by-rational-matrix-entries)
   - [A measurable fundamental region](#54-a-measurable-fundamental-region)
   - [Finite volume and cusp-volume bounds](#55-finite-volume-and-cusp-volume-bounds)
   - [Counting and truncation estimates](#56-counting-and-truncation-estimates)
6. [Cusp coordinates and geometry](#6-cusp-coordinates-and-geometry)
   - [The high cusp as a quotient chart](#61-the-high-cusp-as-a-quotient-chart)
   - [Height and invariant derivatives](#62-height-and-invariant-derivatives)
   - [Several archimedean places](#63-several-archimedean-places)
   - [Finite level and the set of cusps](#64-finite-level-and-the-set-of-cusps)
   - [The rational and imaginary-quadratic models](#65-the-rational-and-imaginary-quadratic-models)
7. [Automorphic $L^2$ spaces](#7-automorphic-l2-spaces)
   - [The norm-one space](#71-the-norm-one-space)
   - [Central-character spaces](#72-central-character-spaces)
   - [Equivalence of the two realizations](#73-equivalence-of-the-two-realizations)
   - [The right regular representation](#74-the-right-regular-representation)
   - [Central and compact-type decompositions](#75-central-and-compact-type-decompositions)
8. [Constant terms and cusp forms](#8-constant-terms-and-cusp-forms)
   - [Why an average detects escape](#81-why-an-average-detects-escape)
   - [The global constant term](#82-the-global-constant-term)
   - [Covariance and invariance](#83-covariance-and-invariance)
   - [Smooth cusp forms](#84-smooth-cusp-forms)
   - [The $L^2$ cuspidal condition](#85-the-l2-cuspidal-condition)
   - [Examples and nonexamples](#86-examples-and-nonexamples)
9. [Closedness and cuspidal projection mechanisms](#9-closedness-and-cuspidal-projection-mechanisms)
   - [Local boundedness of fiber averaging](#91-local-boundedness-of-fiber-averaging)
   - [Closedness of the cuspidal space](#92-closedness-of-the-cuspidal-space)
   - [Invariance under translation and convolution](#93-invariance-under-translation-and-convolution)
   - [Density of smooth cuspidal vectors](#94-density-of-smooth-cuspidal-vectors)
   - [The exact role of all translates](#95-the-exact-role-of-all-translates)
10. [Cuspidal decay and compactness](#10-cuspidal-decay-and-compactness)
   - [The transverse Poincare inequality](#101-the-transverse-poincare-inequality)
   - [The cusp tail estimate](#102-the-cusp-tail-estimate)
   - [Higher decay and smooth vectors](#103-higher-decay-and-smooth-vectors)
   - [Rellich compactness on truncations](#104-rellich-compactness-on-truncations)
   - [The global compact embedding](#105-the-global-compact-embedding)
   - [Escape of mass without cuspidality](#106-escape-of-mass-without-cuspidality)
11. [Typewise elliptic spectrum](#11-typewise-elliptic-spectrum)
   - [The positive measuring operator](#111-the-positive-measuring-operator)
   - [Self-adjoint realization and compact resolvent](#112-self-adjoint-realization-and-compact-resolvent)
   - [Smoothness and rapid decrease of eigenvectors](#113-smoothness-and-rapid-decrease-of-eigenvectors)
   - [Finite spectral windows](#114-finite-spectral-windows)
   - [Why compactness is typewise](#115-why-compactness-is-typewise)
12. [The discrete cuspidal decomposition](#12-the-discrete-cuspidal-decomposition)
   - [Compact cuspidal convolution](#121-compact-cuspidal-convolution)
   - [The compact-operator decomposition](#122-the-compact-operator-decomposition)
   - [Finite multiplicity](#123-finite-multiplicity)
   - [The decomposition theorem](#124-the-decomposition-theorem)
   - [Consequences and boundaries](#125-consequences-and-boundaries)
13. [Synthesis of the reduction and spectral arguments](#13-synthesis-of-the-reduction-and-spectral-arguments)
   - [The complete implication chain](#131-the-complete-implication-chain)
   - [A normalization ledger](#132-a-normalization-ledger)
   - [Failure modes and their repairs](#133-failure-modes-and-their-repairs)
   - [Conclusion](#134-conclusion)

## 1. The global quotient and its escaping direction

### 1.1 The problem of infinity

An adelic quotient for $\mathrm{GL}_2$ is locally built from compact pieces at almost every finite place and from familiar real or complex manifolds at infinity. Its global geometry is nevertheless noncompact. A matrix can become more and more triangular: one diagonal entry expands while the other contracts, and the upper-right coordinate becomes negligible after quotienting by rational translations. This is the cusp.

There are two different noncompact directions, and only one is geometrically significant. Multiplying a matrix by a scalar moves along the center. The determinant module detects this motion, but it does not change the associated point of the projective group. The second direction is the ratio of the two diagonal entries. It measures the degeneration of a two-dimensional lattice toward a rational line. Reduction theory removes the first direction by a central quotient and confines the second to finitely many explicit cusp regions.

The main analytic difficulty is equally specific. Finite volume does not imply a discrete spectrum. A function may be nearly constant on every shrinking cross-section and move its mass farther into a cusp. Such functions create a half-line channel and hence continuous spectrum. Cuspidality removes precisely that constant transverse mode. The remaining oscillation becomes increasingly expensive because invariant transverse derivatives expand down the cusp. Compactness, and ultimately discreteness, come from this increasing cost.

This book proves that chain for $\mathrm{GL}_2$ over an arbitrary number field. The field is not assumed totally real. At complex places the real dimension and absolute-value normalization change, but the reduction and compactness mechanisms do not. The conclusions concern the cuspidal part only. The construction and analysis of the complementary Eisenstein spectrum require additional arguments and are not used here.

### 1.2 Standing number-field notation

Let $F$ be a number field of degree

$$
n=[F:\mathbf Q]=r_1+2r_2,
$$

with ring of integers $\mathcal O_F$, discriminant $d_F$, adele ring $\mathbf A=\mathbf A_F$, and idele group $\mathbf A^\times$. For a place $v$, write $F_v$ for the completion. At a finite place let $\mathcal O_v$ be its integer ring, $\mathfrak p_v$ its maximal ideal, and $q_v$ its residue cardinality.

Absolute values are normalized by

$$
|\varpi_v|_v=q_v^{-1}
$$

at finite places, by the usual absolute value at real places, and by the square of the usual modulus at complex places. Thus

$$
\prod_v|a|_v=1\qquad(a\in F^\times).
\tag{1.1}
$$

For $x\in\mathbf A^\times$, put

$$
|x|_{\mathbf A}=\prod_v|x_v|_v,
\qquad
\mathbf A^1=\ker|\cdot|_{\mathbf A}.
$$

The quotient $F^\times\backslash\mathbf A^1$ is compact. We use this compactness repeatedly to reduce every idele of prescribed module to a compact family of representatives.

The two compactness statements for $F$ are logically independent in the argument. Compactness of $F\backslash\mathbf A$ is additive and controls the upper-right matrix coordinate. Compactness of $F^\times\backslash\mathbf A^1$ is multiplicative and controls the relative sizes of diagonal entries after their total module is fixed. Neither statement replaces the other, and both are needed before a one-dimensional height ray emerges.

The additive quotient $F\backslash\mathbf A$ is also compact. With finite additive measures satisfying $\operatorname{vol}(\mathcal O_v)=1$, ordinary Lebesgue measure at real places, and ordinary planar measure at complex places, its volume is

$$
c_F=2^{-r_2}|d_F|^{1/2}.
\tag{1.2}
$$

We write

$$
[N]=F\backslash\mathbf A
$$

when the additive group is being viewed as the adelic points of the upper unipotent subgroup. The probability measure on $[N]$ is $d\bar x=c_F^{-1}dx$.

The complex normalization deserves emphasis. Ordinary planar measure scales by the square of ordinary complex modulus, exactly matching our normalized $|\cdot|_v$. Consequently multiplication by $a\in F_v$ scales additive measure by $|a|_v$ at every place. This uniform identity is what makes the modular character in (1.3) a single adelic product.

### 1.3 The group, its center, and its parabolic

Put

$$
G=\mathrm{GL}_2,
\qquad
Z=\left\{zI_2:z\in\mathbf G_m\right\}.
$$

Let $B=TN$ be the upper triangular subgroup, with

$$
N=\left\{n(x)=
\begin{pmatrix}1&x\\0&1\end{pmatrix}:x\in\mathbf G_a\right\}
$$

and diagonal torus $T$. For

$$
t=\operatorname{diag}(a,d)
$$

the positive root and the modular character are

$$
\alpha(t)=a/d,
\qquad
\delta_B(t)=|a/d|_{\mathbf A}.
\tag{1.3}
$$

The determinant-one-in-module subgroup is

$$
G(\mathbf A)^1
=\{g\in G(\mathbf A):|\det g|_{\mathbf A}=1\}.
\tag{1.4}
$$

By (1.1), $G(F)\subset G(\mathbf A)^1$. The center inside this group is

$$
Z(\mathbf A)^1
=Z(\mathbf A)\cap G(\mathbf A)^1
=\{zI_2:z\in\mathbf A^1\}.
\tag{1.5}
$$

The compact group $F^\times\backslash\mathbf A^1$ is therefore exactly the central quotient acting on the norm-one automorphic space.

Every proper parabolic subgroup of $G$ defined over $F$ is the stabilizer of an $F$-rational line in $F^2$, hence is conjugate under $G(F)$ to $B$. This rank-one fact has two consequences. There is only one rational parabolic direction to reduce, and vanishing of the standard constant term at every right translate is equivalent to vanishing along every proper rational parabolic.

### 1.4 What reduction theory must prove

A useful reduction theorem has more content than finite volume. It must supply all of the following.

1. A height $H$ on an upper triangular coordinate that is unchanged by $B(F)$ and by the center.
2. A compact set of unipotent, norm-one torus, and maximal-compact coordinates.
3. A lower height bound such that finitely many translates of the resulting Siegel set cover the quotient.
4. A high-cusp uniqueness statement: two sufficiently high reduced points can be rationally equivalent only through $B(F)$.
5. The exact measure density $dH/H^2$, which implies both finite volume and a $Y^{-1}$ tail bound.
6. Uniform geometric control of the cusp cross-sections, strong enough to apply transverse Poincare inequalities and compactness on truncations.

The covering statement alone would not control multiplicity of charts. The volume statement alone would not prevent mass from escaping. The height alone would be ambiguous if the center were not removed. The rest of the book proves these assertions in the order in which they become necessary.

Three principles organize the proof.

**Arithmetic confinement.** Additive compactness confines the unipotent coordinate, multiplicative norm-one compactness confines every torus direction orthogonal to the module, and a short-vector theorem selects a rational line. This is the arithmetic content of reduction.

**Geometric coercivity.** The root module is the only remaining unbounded coordinate. Its measure decays, while invariant derivatives tangent to the unipotent fiber expand. Vanishing of the fiber average converts that expansion into a quantitative lower bound for energy.

**Spectral localization.** Compactness is first proved after fixing finite level and archimedean compact type. A positive elliptic form then has finite-dimensional bounded windows. Only at the final stage are all levels and types allowed to vary, through the fact that every irreducible constituent is detected by at least one of them.

Each principle has a sharp counterexample if one of its hypotheses is removed. Keeping the split center destroys finite volume; keeping the transverse zero mode destroys compactness; and ignoring compact types destroys finite-dimensionality of central spectral eigenspaces. These failures will be proved alongside the positive results.

## 2. Measures, centers, and quotient conventions

### 2.1 Local and adelic measures

Every volume statement depends on choices. We now fix them once.

On $F_v$ use additive Haar measure $dx_v$ with $\operatorname{vol}(\mathcal O_v)=1$ at finite $v$, ordinary Lebesgue measure at real $v$, and ordinary planar measure at complex $v$. Their restricted product is $dx$ on $\mathbf A$, and (1.2) holds.

On $F_v^\times$ use $d^\times x_v$ with $\operatorname{vol}(\mathcal O_v^\times)=1$ at finite places. At a real place use $d^\times x=dx/|x|$. At a complex place write $z=re^{i\theta}$ and use

$$
d^\times z=\frac{dr}{r}\frac{d\theta}{2\pi}.
$$

These archimedean multiplicative measures are convenient rather than forced by the additive ones. The product measure $d^\times x$ on $\mathbf A^\times$ exists because the distinguished finite unit groups have volume one almost everywhere.

Choose maximal compact subgroups

$$
K_v=
\begin{cases}
\mathrm{GL}_2(\mathcal O_v),&v<\infty,\\
\mathrm O(2),&F_v=\mathbf R,\\
\mathrm U(2),&F_v=\mathbf C,
\end{cases}
$$

and give each probability Haar measure $dk_v$. Their product

$$
K=K_\infty K_f
=\prod_{v\mid\infty}K_v\times\prod_{v<\infty}K_v
$$

is compact and has volume one.

### 2.2 Iwasawa measure

Every local element has an Iwasawa decomposition

$$
g_v=n(x_v)\operatorname{diag}(a_v,d_v)k_v.
$$

We define $dg_v$ by the integration formula

$$
\int_{G(F_v)}f(g)\,dg_v
=\int_{F_v}\int_{F_v^\times}\int_{F_v^\times}\int_{K_v}
f\left(n(x)\operatorname{diag}(a,d)k\right)
\left|\frac ad\right|_v^{-1}
dk\,d^\times a\,d^\times d\,dx.
\tag{2.1}
$$

The coordinates are not unique. At a finite place the ambiguity contains $B(F_v)\cap K_v$; at an archimedean place signed diagonal elements give a finite ambiguity. Formula (2.1), rather than a choice of unique coordinates, is the definition: the compact-intersection measure is the one induced by the stated measures, and the displayed integral fixes the scalar of $dg_v$. In particular, at a finite unramified place $B(F_v)\cap K_v$ has volume one because $x\in\mathcal O_v$ and $a,d\in\mathcal O_v^\times$ each have volume one. The factor $|a/d|_v^{-1}$ is forced by

$$
\operatorname{diag}(a,d)n(x)\operatorname{diag}(a,d)^{-1}
=n((a/d)x).
$$

Indeed, left translation by the torus scales $dx$ by $|a/d|_v$, so the inverse factor makes (2.1) left invariant. Left translation by $n(u)$ merely translates $x$, while right translation by $K_v$ preserves $dk_v$. These transformations generate $G(F_v)$, so (2.1) is left Haar. Since $G(F_v)$ is reductive and hence unimodular, the measure is right Haar as well.

The restricted product $dg=\prod_vdg_v$ is Haar measure on $G(\mathbf A)$. At every finite unramified place, applying (2.1) to the characteristic function of $K_v$ gives $\operatorname{vol}(K_v)=1$: the contributing coordinates are exactly $x\in\mathcal O_v$ and $a,d\in\mathcal O_v^\times$. Thus the adelic product is a genuine restricted product, and only finitely many exceptional local factors enter a factorizable integral.

One global scalar will be useful. Disintegrate multiplicative measure on the idele class group along the module. With probability measure $du$ on the compact kernel $C_F^1$ and $dH/H$ on $\mathbf R_{>0}$, there is a unique $\kappa_F>0$ such that

$$
\int_{F^\times\backslash\mathbf A^\times}f(y)\,d^\times\bar y
=\kappa_F\int_0^\infty\int_{C_F^1}f(u\,s(H))\,du\,\frac{dH}{H}.
\tag{2.1a}
$$

The number $\kappa_F$ is determined by the multiplicative measures already fixed; it is not reset later. Replacing the section $s$ translates the probability measure on $C_F^1$ and leaves (2.1a) unchanged.

### 2.3 Quotient measure and covolume

The diagonal $G(F)$ is discrete in $G(\mathbf A)$. If $\mathcal F$ is a measurable fundamental region, defined up to null boundary, the quotient measure on

$$
G(F)\backslash G(\mathbf A)
$$

is characterized by

$$
\int_{G(F)\backslash G(\mathbf A)}
\sum_{\gamma\in G(F)}f(\gamma g)\,d\dot g
=\int_{G(\mathbf A)}f(g)\,dg
\tag{2.2}
$$

for every nonnegative measurable $f$. Equivalently, integration over the quotient is integration over $\mathcal F$. The definition is independent of $\mathcal F$ because distinct rational translates are almost disjoint and Haar measure is left invariant.

The same convention defines quotient measures for $N(F)\backslash N(\mathbf A)$, $Z(\mathbf A)G(F)\backslash G(\mathbf A)$, and the norm-one variants. Whenever a quotient is taken in stages, the measures are the unique ones satisfying the corresponding iterated integration formula. Explicitly, for closed unimodular subgroups $H_1\subset H_2\subset G(\mathbf A)$ and an absolutely integrable function,

$$
\int_{H_1\backslash G(\mathbf A)}F(g)\,d\dot g
=\int_{H_2\backslash G(\mathbf A)}
\int_{H_1\backslash H_2}F(hg)\,d\dot h\,d\ddot g.
\tag{2.2a}
$$

We use (2.2a) to define whichever quotient measure has not yet been fixed. Applied to $H_1=G(F)$ and $H_2=Z(\mathbf A)G(F)$, it records exactly which central measure is removed. Applied to $N(F)\subset N(\mathbf A)$, it says that the quotient induced by $dx$ has mass $c_F$, whereas the constant term uses the probability measure $d\bar x=c_F^{-1}dx$. The distinction affects norm constants, though not the condition that a constant term vanish.

This convention removes the otherwise harmless but confusing scalar ambiguity in later norm identities. In particular, every occurrence of $d\bar g$ on the central quotient and every occurrence of $d\dot g$ on the norm-one quotient refers to the measure produced from (2.1) by (2.2a), not to an independently rescaled finite-volume measure.

### 2.4 Removing the split center

The quotient $G(F)\backslash G(\mathbf A)$ has infinite volume for a simple reason: the map

$$
g\longmapsto|\det g|_{\mathbf A}
$$

descends and is onto $\mathbf R_{>0}$. Haar measure on this factor is $dr/r$, which has infinite mass.

There are two standard repairs.

The first is the norm-one quotient

$$
[G]^1=G(F)\backslash G(\mathbf A)^1.
\tag{2.3}
$$

It still contains the compact central action of $F^\times\backslash\mathbf A^1$.

The second is the central quotient

$$
[\overline G]
=Z(\mathbf A)G(F)\backslash G(\mathbf A).
\tag{2.4}
$$

It removes all scalar ideles. Both quotients have finite volume; this will be proved from the same Siegel-set calculation. They are not literally identical. The first remembers the compact norm-one idele class center, while the second has divided it out.

A third description often used at infinity divides only by a chosen split subgroup $A_G\simeq\mathbf R_{>0}$ mapping isomorphically to the determinant-module direction. That description is noncanonical because the splitting of the idele module is noncanonical. We will use only (2.3) and (2.4), whose definitions require no choice.

The relation between the two canonical quotients is exact. The inclusion $G(\mathbf A)^1\hookrightarrow G(\mathbf A)$ induces

$$
C_F^1\backslash [G]^1
\longrightarrow [\overline G].
\tag{2.4a}
$$

It is surjective: given $g\in G(\mathbf A)$, choose a scalar idele $z$ with $|z|_{\mathbf A}^2=|\det g|_{\mathbf A}^{-1}$; then $zg\in G(\mathbf A)^1$ and $g$ has the same image in the central quotient. It is injective: if $g_1,g_2\in G(\mathbf A)^1$ have the same image, then $g_2=\gamma zg_1$ for $\gamma\in G(F)$ and $z\in Z(\mathbf A)$. Taking determinant modules gives $|z|_{\mathbf A}^2=1$, hence $z\in\mathbf A^1$, so the two points differ by $C_F^1$ in $[G]^1$.

With probability measure on $C_F^1$, quotient integration identifies the measure on the left side of (2.4a) with $d\bar g$ on the right. Consequently

$$
\int_{[G]^1}F(g)\,d\dot g
=\int_{[\overline G]}
\int_{C_F^1}F(zg)\,dz\,d\bar g
\tag{2.4b}
$$

for nonnegative measurable $F$, after choosing any measurable lift of $g$. This formula will later turn Fourier decomposition on the compact central fiber into fixed-central-character spaces on $[\overline G]$.

The square in $|z|_{\mathbf A}^2$ is specific to $\mathrm{GL}_2$: the determinant of $zI_2$ is $z^2$. It is the reason the scalar used to normalize a determinant of module $r^2$ has module $r^{-1}$. The root height is unchanged throughout, because the scalar cancels in the ratio of diagonal entries.

### 2.5 Fixed central character

Let

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times
$$

be a unitary character. Define $L^2_\omega$ to be the measurable functions $\phi$ on $G(F)\backslash G(\mathbf A)$ satisfying

$$
\phi(zg)=\omega(z)\phi(g)
\qquad(z\in Z(\mathbf A))
\tag{2.5}
$$

and

$$
\|\phi\|_2^2
=\int_{Z(\mathbf A)G(F)\backslash G(\mathbf A)}
|\phi(g)|^2\,d\bar g<\infty.
\tag{2.6}
$$

Unitarity is essential: it makes $|\phi|^2$ descend to the central quotient. If $|\omega|$ were nontrivial, the integrand would depend on the central representative. Every continuous character is a real power of the idele module times a unitary character, so the unitary hypothesis removes exactly the growth direction that would invalidate (2.6).

Some authors put $\omega^{-1}$ in (2.5). Our convention makes right translation by a central element act with eigencharacter $\omega$:

$$
(R(z)\phi)(g)=\phi(gz)=\omega(z)\phi(g).
$$

All later central-isotypic statements use this choice.

## 3. Iwasawa coordinates and adelic height

### 3.1 Local Iwasawa decomposition

At a finite place, $G(F_v)$ acts transitively on the vertices and oriented apartments of its lattice tree. Elementary divisor theory gives

$$
G(F_v)=B(F_v)K_v.
$$

At a real or complex place, Gram--Schmidt orthogonalization gives the same equality with $K_v=\mathrm O(2)$ or $\mathrm U(2)$. Taking the restricted product yields

$$
G(\mathbf A)=B(\mathbf A)K=N(\mathbf A)T(\mathbf A)K.
\tag{3.1}
$$

Only finitely many local coordinates of an adelic element leave the standard integral pieces, so the local decompositions assemble without an infinite convergence problem.

Iwasawa coordinates are not unique. Multiplying the torus coordinate by $T(\mathbf A)\cap K$ and compensating in $K$ changes the decomposition. The positive root module, however, is unchanged because every compact idele has module one.

### 3.2 The root coordinate

If

$$
g=n(x)\operatorname{diag}(a,d)k,
$$

define the Iwasawa height

$$
H_B(g)=\left|\frac ad\right|_{\mathbf A}.
\tag{3.2}
$$

This is well defined despite the ambiguity just noted. It satisfies

$$
H_B(bg)=H_B(g)
$$

for $b\in B(F)$, because the root value of the rational diagonal part has adelic module one and the rational unipotent part does not change the torus. It also satisfies

$$
H_B(zg)=H_B(g)
$$

for $z\in Z(\mathbf A)$. Thus height belongs naturally to the central quotient of the rational Borel quotient.

It is not invariant under all of $G(F)$. That failure is desirable. Different rational translates correspond to different rational lines, and reduction theory chooses the line for which the resulting height is large.

For later change of variables, write $y=a/d$. The torus measure splits into a central coordinate and $d^\times y$. Formula (2.1) becomes, up to the already fixed quotient measure on the central factor,

$$
dg=H_B(g)^{-1}\,dx\,d^\times y\,dk\,d^\times z.
\tag{3.3}
$$

On the module coordinate $H=|y|_{\mathbf A}$, multiplicative measure is a constant multiple of $dH/H$. Hence the root contribution is

$$
H^{-1}\frac{dH}{H}=\frac{dH}{H^2}.
\tag{3.4}
$$

This elementary identity is the source of finite cusp volume.

The phrase “up to the central factor” in (3.3) can be made exact without choosing square roots in every local field. The homomorphism

$$
T(\mathbf A)\longrightarrow \mathbf A^\times,
\qquad \operatorname{diag}(a,d)\longmapsto a/d,
$$

has kernel $Z(\mathbf A)$. Give the quotient $Z(\mathbf A)\backslash T(\mathbf A)$ the measure obtained from (2.2a). Under the root map it is a fixed positive multiple of $d^\times y$; that multiple is already determined by (2.1). After quotienting further by $T(F)$, formula (2.1a) yields

$$
d\mu_{\mathrm{root}}
=\kappa'_F\,du\,\frac{dH}{H^2},
\tag{3.4a}
$$

where $du$ is probability measure on the compact norm-one idele class coordinate and $\kappa'_F>0$ is fixed. Thus later inequalities may absorb $\kappa'_F$ into their constants, but no height-dependent factor is being suppressed. This is the precise sense in which the cusp density is $dH/H^2$.

There is also a useful consistency check. Reversing the two diagonal entries replaces $H$ by $H^{-1}$. The modular factor then changes from $H^{-1}$ to $H$, exactly as it must for the opposite Borel. Reduction chooses the chamber $H\geq H_0$; using both chambers would count the same rational-line degeneration twice.

### 3.3 Compact reduction of the torus

Let $C_F=F^\times\backslash\mathbf A^\times$. The module gives an exact sequence

$$
1\longrightarrow C_F^1\longrightarrow C_F
\xrightarrow{|\cdot|_{\mathbf A}}\mathbf R_{>0}
\longrightarrow1,
\tag{3.5}
$$

with compact kernel $C_F^1$. Choose a compact set $\Omega_T\subset\mathbf A^\times$ mapping onto $C_F^1$. Then every $y\in\mathbf A^\times$ can be written

$$
y=q\,u\,s(H),
\qquad
q\in F^\times,\quad u\in\Omega_T,\quad H=|y|_{\mathbf A},
\tag{3.6}
$$

where $s:\mathbf R_{>0}\to\mathbf A^\times$ is any fixed continuous section of the module. Different sections change $u$ inside another compact set. The final theorems therefore do not depend on $s$.

Equation (3.6) is the multiplicative reduction step. The rational scalar $q$ belongs to $T(F)$ through $\operatorname{diag}(q,1)$, the norm-one coordinate $u$ stays compact modulo rational elements, and the sole remaining noncompact variable is $H$.

To prove (3.6), begin with $y\in\mathbf A^\times$ and set $H=|y|_{\mathbf A}$. Then $ys(H)^{-1}\in\mathbf A^1$. Its class in $F^\times\backslash\mathbf A^1$ has a representative $u$ in the fixed compact surjective set $\Omega_T$. Therefore $ys(H)^{-1}=qu$ for some $q\in F^\times$, which is the desired factorization. Conversely, every such factorization has module $H$ by the product formula. This proves existence and shows that the only ambiguity is multiplication of $q$ and $u$ by inverse rational factors.

The compact set $\Omega_T$ need not be a subgroup or a continuous global section. A compact surjective set is enough for covering and estimates. When measurable uniqueness is needed, choose a Borel fundamental set inside it and discard a null boundary. This distinction avoids assuming that the compact idele class group admits a globally continuous system of representatives.

The compactness in (3.5) is specific to number fields and uses ideal-class finiteness and the unit lattice. Without it, the root coordinate could have additional uncontrolled directions and a one-variable Siegel set would not cover.

One can see the two arithmetic ingredients separately. Finite valuations of an idele determine a fractional ideal. Multiplication by $F^\times$ reduces its ideal class to one of finitely many representatives. Once the finite ideal is fixed, the remaining archimedean logarithms have prescribed sum. Multiplication by units translates the sum-zero hyperplane by a full lattice. A compact parallelotope for that lattice completes the reduction. Ideal classes control the finite places; units control the relative archimedean sizes.

### 3.4 Balanced archimedean representatives

The section in (3.6) can be chosen so that its finite components are $1$ and its archimedean components expand at comparable rates. More precisely, there is a compact set $\Omega_\infty$ and constants $c_1,c_2>0$ such that every torus class of module $H\geq1$ has a representative $y$ with

$$
c_1H^{1/n}\leq |y_v|_{\mathrm{usual}}\leq c_2H^{1/n}
\qquad(v\mid\infty).
\tag{3.7}
$$

At a complex place the normalized absolute value is the square of the usual one, so the product of the normalized bounds has total exponent

$$
\frac{r_1+2r_2}{n}=1.
$$

**Proof strategy.** Use finite ideles to choose one of finitely many ideal classes, then apply the logarithms of global units to balance the archimedean coordinates.

**Proof.** After multiplication by $F^\times$, the finite valuation vector belongs to a finite list of ideal-class representatives. Absorb that list into a compact finite-idele set. The archimedean logarithmic vector

$$
(\log|y_v|_v)_{v\mid\infty}
$$

has coordinate sum $\log H$ up to a bounded correction from the finite representative. Subtract the ray

$$
\left(\frac{[F_v:\mathbf R]}n\log H\right)_{v\mid\infty}.
$$

The result lies in the hyperplane of coordinate sum zero. Logarithms of global units form a full lattice in that hyperplane, so multiplication by a unit moves the result into a fixed compact parallelotope. Returning from normalized logarithms to usual archimedean moduli gives (3.7). $\square$

The exponent $1/n$ will later be the weakest uniform transverse expansion rate when $t=\log H$ is used as cusp depth.

### 3.5 Lattices and short lines

There is a geometric interpretation of height. An element $g\in G(\mathbf A)$ carries the standard adelic lattice to a rank-two adelic lattice. A nonzero rational row vector $v\in F^2$ determines an adelic vector $vg$. Modulo scalar homothety, the size of $vg$ measures the line $Fv$ inside that lattice.

In an Iwasawa decomposition with $v=(0,1)$, the two successive one-dimensional covolumes differ by the root module $H_B(g)$. Large height means that one rational line is much shorter than the quotient line after determinant normalization. Reduction theory chooses a shortest rational line and moves it to $F(0,1)$.

This description explains why the cusp is indexed by rational lines and why $B(F)$ is its stabilizer. It also supplies the high-cusp uniqueness principle: a sufficiently degenerate lattice cannot have two distinct rational lines both serving as its unique shortest line.

## 4. The adelic reduction theorem

### 4.1 The unipotent reduction step

Because $F\backslash\mathbf A$ is compact, choose a compact measurable set $\Omega_N\subset\mathbf A$ whose image covers it. Every $x\in\mathbf A$ can be written

$$
x=q+u,
\qquad q\in F,\quad u\in\Omega_N.
\tag{4.1}
$$

Left multiplication by $n(-q)\in N(F)$ replaces $n(x)$ by $n(u)$. Thus the unipotent coordinate of every Iwasawa decomposition can be reduced to a fixed compact set.

The compactness statement, rather than a particular parallelotope, is the invariant content. At finite places it removes all principal parts simultaneously. At infinity it reduces the remaining algebraic-integer ambiguity to a Minkowski cell. Its measure is $c_F$ if boundary representatives are chosen with almost-everywhere uniqueness, and the normalized quotient measure $d\bar x$ makes its volume one.

Unipotent reduction interacts well with the torus. Since

$$
\operatorname{diag}(a,d)^{-1}n(x)\operatorname{diag}(a,d)
=n((d/a)x),
$$

a compact set of unreduced $x$ becomes even smaller in the expanding cusp $|a/d|\to\infty$. This contraction is why a fixed $\Omega_N$ suffices at every height.

### 4.2 Finding a rational short line

We need one geometry-of-numbers input in rank two.

**Lemma 4.1 (adelic short vector).** There is a constant $C_F>0$ with the following property. For every $g\in G(\mathbf A)$ there is $0\ne v\in F^2$ such that

$$
\prod_v\|vg_v\|_v\leq C_F|\det g|_{\mathbf A}^{1/2},
\tag{4.2}
$$

where at finite places the sup norm is used, at real places the Euclidean norm, and at complex places the square of the Euclidean norm. Any two choices of standard local norms change only $C_F$.

**Proof strategy.** Keep the finite body equal to the standard integral lattice and scale all ordinary archimedean radii by $R^{1/n}$. The product norm then grows by $R$, while the two-dimensional adelic volume grows by $R^2$.

**Proof.** The additive group $F^2$ is a discrete cocompact subgroup of $\mathbf A^2$. Let $D$ be a measurable fundamental region of volume $c_F^2$. For $R>0$, define $\mathcal B_R$ by

$$
w_v\in\mathcal O_v^2\quad(v<\infty),
\qquad
\|w_v\|_{\mathrm{usual}}\leq R^{1/n}\quad(v\mid\infty).
$$

At a real place the corresponding volume exponent is $2/n$, and at a complex place it is $4/n$. Hence

$$
\operatorname{vol}(\mathcal B_R)=c_\infty R^2,
$$

because $2r_1+4r_2=2n$. Every $w\in\mathcal B_R$ also satisfies

$$
\prod_v\|w_v\|_v\leq R:
$$

finite norms are at most one, each real place contributes at most $R^{1/n}$, and each complex place contributes at most $R^{2/n}$.

Right multiplication by $g^{-1}$ scales additive volume on $\mathbf A^2$ by $|\det g|_{\mathbf A}^{-1}$. Choose

$$
R=C|\det g|_{\mathbf A}^{1/2}
$$

with $C$ depending only on $F$. Shrink every archimedean radius by a fixed factor to obtain a concentric body $\mathcal C_R$ such that

$$
\mathcal C_R-\mathcal C_R\subset\mathcal B_{C_0R}
$$

for a fixed $C_0$, while

$$
\operatorname{vol}(\mathcal C_Rg^{-1})>c_F^2.
$$

The finite inclusion uses $\mathcal O_v^2-\mathcal O_v^2=\mathcal O_v^2$; at infinity it is the triangle inequality. Project $\mathcal C_Rg^{-1}$ to $\mathbf A^2/F^2$. Its volume exceeds that of the quotient, so the projection cannot be one-to-one almost everywhere. Two distinct points have the same image modulo $F^2$; their nonzero difference lies in

$$
F^2\cap\mathcal B_{C_0R}g^{-1}.
$$

Multiplying by $g$ gives (4.2), after replacing $C_0C$ by $C_F$. All constants are independent of $g$. $\square$

Equivalently, one may attach to $g_f$ the full $\mathcal O_F$-lattice

$$
L(g_f)=\{v\in F^2:v g_f\in\widehat{\mathcal O}_F^{\,2}\},
$$

whose archimedean covolume is the finite determinant factor times $c_F^2$, and then apply the ordinary convex-body theorem to $L(g_f)$ at infinity. The finitely many ideal classes make the comparison constants uniform. This second description is often convenient when one wants an explicit, though nonoptimal, value of $C_F$.

A primitive representative may be chosen for the line $Fv$: multiplying $v$ by $F^\times$ does not change the product of local sizes because of (1.1). Complete $v$ to an $F$-basis of $F^2$. The corresponding element of $G(F)$ moves $v$ to $(0,1)$.

The square-root exponent in (4.2) is forced. Replacing $g$ by the scalar matrix $zg$ multiplies the left side by $|z|_{\mathbf A}$ and $|\det g|_{\mathbf A}^{1/2}$ by the same quantity. Any different determinant exponent would violate central homogeneity. This check is important because reduction is ultimately performed only after the center is removed.

### 4.3 Reduction into a Siegel region

Let $g\in G(\mathbf A)$. Choose a rational short line by Lemma 4.1 and $\gamma\in G(F)$ carrying it to the second coordinate line. Write

$$
\gamma g=n(x)\operatorname{diag}(a,d)k.
$$

The second row has local size comparable, uniformly in $k\in K$, to $|d|_v$. The determinant has local size $|ad|_v$. Therefore (4.2) implies

$$
|d|_{\mathbf A}\leq C'_F|ad|_{\mathbf A}^{1/2},
$$

and hence

$$
H_B(\gamma g)=|a/d|_{\mathbf A}\geq (C'_F)^{-2}.
\tag{4.3}
$$

Now apply torus reduction (3.6) to $a/d$ and absorb its rational factor into $T(F)$. Apply unipotent reduction (4.1), remembering that torus conjugation merely replaces one compact unipotent set by another compact set because height is bounded below. The remaining center may be discarded in the central quotient or retained in the norm-one group as a compact norm-one idele class.

Thus all coordinates except $H_B$ lie in fixed compact sets and the height has a fixed positive lower bound. No compactness assertion about the full quotient has been made: $H_B$ is allowed to tend to infinity.

We record the bookkeeping behind this conclusion. It is the point at which several superficially similar scalar operations must be distinguished.

First, multiplication by $\gamma\in G(F)$ chooses a rational line. It does not alter $|\det g|_{\mathbf A}$, by the product formula. Second, multiplication by $\operatorname{diag}(q,1)$ with $q\in F^\times$ changes the representative of the root idele $a/d$ but does not change its module. Third, multiplication by $zI_2$ with $z\in Z(\mathbf A)$ changes the determinant module by $|z|_{\mathbf A}^2$ but leaves the root idele unchanged. These three operations respectively control the rational parabolic, the compact root class, and the split center.

To see compactness of the remaining finite coordinates, choose a fractional ideal $\mathfrak a$ representing each ideal class. The finite root idele may, after multiplication by $F^\times$, be arranged to generate one of these finitely many ideals and to have unit components elsewhere. At the exceptional places its unit part lies in a compact group. Thus the finite root coordinate belongs to a finite union of compact sets. The same representatives enter the completion of the short line to a basis, which is why the finite set of cusp representatives is controlled by ideal classes rather than by infinitely many denominators.

For the unipotent coordinate, write the already reduced torus representative as $t$. Left multiplication by $n(q)$ changes

$$
n(x)t=n(q)n(x-q)t.
$$

Choose $q\in F$ so that $x-q\in\Omega_N$. If the torus representative is subsequently altered within its fixed compact norm-one class, conjugation replaces $\Omega_N$ by the image of $\Omega_N$ under a compact family of additive automorphisms. The union of those images is still compact. This justifies the assertion in Section 4.1 without assuming a coordinate section invariant under every torus operation.

Finally, a representative in the norm-one group can be produced without a local square-root convention. Given a balanced root representative $y(H)$, choose any idele $z(H)$ of module $H^{-1/2}$ and put

$$
a^1(H)=z(H)I_2\operatorname{diag}(y(H),1).
$$

Its determinant has module one and its root has module $H$. Two choices of $z(H)$ differ by a norm-one idele, whose class belongs to the compact central coordinate already placed in $\Omega^1$.

### 4.4 The adelic reduction theorem

We state the result in the two forms used later.

**Theorem 4.2 (adelic reduction for $\mathrm{GL}_2$).** Let $F$ be a number field, with absolute values and measures as in Chapters 1 and 2.

1. There are a compact set $\Omega\subset G(\mathbf A)$, a number $H_0>0$, a balanced section $H\mapsto a(H)$ with $H_B(a(H))=H$, and a finite set $C\subset G(\mathbf A_f)$ such that

   $$
   G(\mathbf A)
   =G(F)Z(\mathbf A)\,\Omega\,
   \{a(H):H\geq H_0\}\,C.
   \tag{4.4}
   $$

   The finite components of $a(H)$ may be taken from a fixed compact set, and its archimedean root coordinates satisfy (3.7).

2. Intersecting with $G(\mathbf A)^1$, there is a compact $\Omega^1$ such that

   $$
   G(\mathbf A)^1
   =G(F)\,\Omega^1\{a^1(H):H\geq H_0\},
   \tag{4.5}
   $$

   where $a^1(H)\in G(\mathbf A)^1$ has height $H$, and a compact set of representatives for the compact center $F^\times\backslash\mathbf A^1$ is included in $\Omega^1$.

3. For every compact open $K_f'\subset G(\mathbf A_f)$, the quotient by right $K_f'$ is covered by finitely many cusp regions of this form.

**Proof.** We give the covering argument in five steps.

**Choice of a parabolic.** Apply Lemma 4.1 to the lattice represented by $g$. Complete the resulting short vector to an $F$-basis and left multiply by the corresponding rational matrix. In the resulting Iwasawa decomposition, the chosen line is the second coordinate line. Comparing its covolume with the determinant gives (4.3), so the root lies in the positive chamber $H\geq H_0$ for $H_0=(C'_F)^{-2}$.

**Reduction of the root class.** Apply (3.6) to $a/d$. The factor $q\in F^\times$ is absorbed by a rational diagonal matrix. The norm-one factor belongs to $\Omega_T$, while the module factor is represented by the balanced section. Changing the rational diagonal matrix may rescale the two basis vectors, but it preserves the chosen rational line and the lower bound on height.

**Reduction of the unipotent.** Translate the additive coordinate by $N(F)$ into $\Omega_N$. As explained above, the compact ambiguity in the torus enlarges $\Omega_N$ only to another compact set. The maximal compact coordinate already lies in $K$.

**The center.** In the central quotient, discard the scalar coordinate. In $G(\mathbf A)^1$, use $a^1(H)$ and retain the residual norm-one central idele class. Compactness of $F^\times\backslash\mathbf A^1$ supplies a compact representative set, which is absorbed into $\Omega^1$.

**Finite level.** At the standard full finite level, the finite root ideals lie in finitely many ideal classes. Replacing that level by $K_f'$ introduces only finitely many right cosets inside each of the finitely many relevant compact sets, because an open subgroup has finite index in a compact group. Choose representatives and call their union $C$. The preceding steps then give (4.4), (4.5), and the finite-level assertion. $\square$

The proof is quantitative in the following limited but useful sense. Once compact representatives have been fixed, $H_0$, the diameters of the compact coordinates, the overlap bound of Chapter 5, and all cusp-density comparison constants depend only on $F$ and the chosen level. No constant depends on the point being reduced or on its height. Uniformity in a varying level is neither asserted nor needed for the spectral conclusions.

The finite set $C$ can be hidden inside a larger compact set when no level is fixed. It is displayed because, at finite level, its double cosets become the familiar finite set of cusps.

### 4.5 Why the hypotheses are exact

The number-field hypothesis enters three times: $F\backslash\mathbf A$ is compact, $F^\times\backslash\mathbf A^1$ is compact, and $F^2$ is an adelic lattice. All three are used. A restricted product over arbitrary local fields need not satisfy any of them.

Invertibility of $g$ is also essential. A singular adelic matrix has no determinant with which to normalize covolume, and its rows may vanish at different places. Reduction belongs to the group, not to the full matrix algebra.

Finally, removing the scalar module is essential for finite volume. Imposing $|\det g|_{\mathbf A}=1$ or quotienting by $Z(\mathbf A)$ does this. Merely quotienting by $G(F)$ does not, because rational determinants have module one and cannot change the positive real determinant module.

## 5. Siegel sets and fundamental-domain estimates

### 5.1 Definition of a Siegel set

Fix compact sets $\Omega_N\subset N(\mathbf A)$ and $\Omega_T\subset T(\mathbf A)$ as above, and retain the probability compact group $K$. Use the balanced section from Theorem 4.2 and write

$$
A^+(H_0)=\{a(H):H\geq H_0\}.
$$

For $H_0>0$, define

$$
\mathfrak S(H_0)
=\Omega_N\Omega_TA^+(H_0)K,
\tag{5.1}
$$

viewed either inside $G(\mathbf A)^1$ with compact central coordinate included or inside the central quotient. This is a Siegel set.

The word “set” hides controlled ambiguity. The compact pieces may overlap and the balanced torus section is not unique. Every permitted choice produces a set contained in another permitted Siegel set after changing $H_0$ and enlarging compact factors. Consequently covering, finite-overlap, and tail estimates are independent of the choice.

For $Y\geq H_0$, its high part is

$$
\mathfrak S(Y)=\{g\in\mathfrak S(H_0):H_B(g)\geq Y\}.
\tag{5.2}
$$

Reduction says finitely many rational translates of $\mathfrak S(H_0)$ cover the relevant quotient.

### 5.2 The Siegel intersection property

Covering is not enough: an infinite number of rational translates might pass through one compact region. The required finiteness is the Siegel property.

**Theorem 5.1 (Siegel property).** Work in $Z(\mathbf A)\backslash G(\mathbf A)$ and choose the unipotent and torus factors of each Siegel region inside fixed measurable fundamental sets for their rational translations. For compact subsets $C_1,C_2$ of this central quotient and positive lower height bounds, the set

$$
\{[\gamma]\in Z(F)\backslash G(F):[\gamma] C_1\mathfrak S(H_1)
\cap C_2\mathfrak S(H_2)\ne\varnothing\}
$$

is finite. The quotient by $Z(F)$ is necessary: every rational scalar acts trivially after the adelic center has been removed.

There is a stronger high-cusp form. There exists $Y_0$ such that if

$$
\gamma\mathfrak S(Y_0)\cap\mathfrak S(Y_0)\ne\varnothing,
$$

then $\gamma\in B(F)$. Among reduced representatives, only finitely many classes in $Z(F)\backslash B(F)$ can produce an overlap, and their number is bounded independently of the height.

### 5.3 Proof by rational matrix entries

We prove the decisive high-cusp assertion. Write

$$
\gamma=\begin{pmatrix}p&q\\r&s\end{pmatrix}\in G(F)
$$

and suppose $g,g'\in\mathfrak S(Y)$ satisfy $\gamma g=g'$. The compact factors keep all unipotent and norm-one torus coordinates in bounded adelic sets. Conjugate the equality by the balanced expanding torus. The lower-left entry is multiplied, at each archimedean place, by a factor comparable to $H^{1/n}$, while the remaining compact factors are bounded. Consequently

$$
|r|_v\leq C_vY^{-1/n}
\qquad(v\mid\infty).
\tag{5.3}
$$

At every finite place, compactness of the finite factors bounds $r$ inside one fixed fractional ideal $\mathfrak a^{-1}$. Thus $r$ lies in a fixed fractional $\mathcal O_F$-lattice and all its archimedean conjugates tend uniformly to zero as $Y\to\infty$. A bounded archimedean region meets a fractional lattice in finitely many points; for sufficiently large $Y$, the only possibility is $r=0$.

Hence $\gamma$ is upper triangular, so $\gamma\in B(F)$. This proves the high-cusp assertion.

For the general finite-intersection statement, first consider $r\ne0$. The fixed fractional lattice containing $r$ has a positive lower bound for the maximum of its archimedean absolute values away from zero. The analogue of (5.3), with the two possibly different heights retained, therefore bounds both heights above. Once both heights lie in a compact interval, the matrix identity bounds $p,q,r,s$, after one fixed common denominator, in a compact archimedean region. A fractional lattice meets that region in finitely many points.

If $r=0$, then $\gamma\in B(F)$. The reduced unipotent coordinates imply that the rational translation parameter belongs to the intersection of a fixed fractional lattice with a compact adelic difference set; there are only finitely many such parameters. The reduced torus coordinates similarly leave only finitely many rational root classes. Modulo the rational scalar center, only finitely many upper triangular matrices remain. This proves the stated finiteness. Nonzero determinant excludes singular candidates. $\square$

The proof is a reusable arithmetic pattern: finite components bound denominators, archimedean components bound conjugates, and a fractional lattice meets a compact set finitely.

The high-cusp conclusion also admits a geometric proof that clarifies its meaning. Each point of a Siegel region has a distinguished short rational line. The ratio between the covolume of that line and the quotient line tends to zero as $H\to\infty$. Compactness of the transverse coordinates gives a uniform gap: past some height, every rational line distinct from the distinguished one is longer by a fixed factor. If $\gamma g=g'$ with both points high, $\gamma$ must carry the distinguished line of $g$ to that of $g'$. Both are the standard second coordinate line, so $\gamma$ stabilizes it and lies in $B(F)$. The matrix-entry proof is stronger for estimates because it exhibits the precise lower-left coordinate whose vanishing detects the parabolic.

One must not omit the word “reduced.” The unreduced set $N(\mathbf A)A^+(H_0)K$ is invariant under infinitely many translations from $N(F)$ and therefore has infinite overlap. Compact fundamental representatives for $F\backslash\mathbf A$ remove those translations. Similarly, rational scalars would remain invisible on the central quotient unless the intersection set were taken in $Z(F)\backslash G(F)$. These are not cosmetic qualifications; without them Theorem 5.1 is false.

### 5.4 A measurable fundamental region

Start with finitely many Siegel sets covering the quotient. Order their rational translates. Remove from each translate the points already covered by earlier ones, and choose measurable representatives on the remaining null boundaries. The Siegel property ensures local finiteness, so this subtraction is measurable and does not introduce an infinite accumulation of boundaries in a compact region.

The resulting set $\mathcal F$ has these properties:

$$
G(\mathbf A)^1=G(F)\mathcal F,
$$

distinct rational translates of $\mathcal F$ are disjoint outside a null set, and $\mathcal F$ is contained in a finite union of Siegel sets. It is a measurable fundamental region for $[G]^1$. The same construction after dividing by $Z(\mathbf A)$ gives one for $[\overline G]$.

This construction does not promise a connected polygon or a canonical boundary. Neither feature is needed for integration. What matters is almost-everywhere uniqueness and containment in finitely many regions with explicit measure.

More explicitly, enumerate $Z(F)\backslash G(F)$ and the finite list of cusp representatives. For the first reduced Siegel region keep every point. From the $j$-th region remove its intersections with all earlier rational translates. Local finiteness from Theorem 5.1 makes the union removed at each stage locally finite, hence measurable. On the residual boundary, choose the least representative in the enumeration. Boundaries of additive and logarithmic fundamental cells have Haar measure zero, as do the smooth height boundaries, so tie-breaking changes no integral.

The resulting region need not be closed. Nevertheless, for each finite $Y$ its part of height at most $Y$ has compact closure modulo a null boundary. It lies in a finite union of products of compact coordinate sets with the compact interval $[H_0,Y]$. This relative compactness, together with almost-everywhere uniqueness, is the exact property later used in truncation and local compactness arguments.

### 5.5 Finite volume and cusp-volume bounds

In the central quotient, all coordinates of a Siegel set except $H$ range over compact sets of finite measure. By (3.4),

$$
\operatorname{vol}(\mathfrak S(Y))
\leq C\int_Y^\infty\frac{dH}{H^2}
=\frac CY.
\tag{5.4}
$$

Since a finite union covers the quotient,

$$
\operatorname{vol}([\overline G])<\infty.
\tag{5.5}
$$

For $[G]^1$, the extra central quotient $F^\times\backslash\mathbf A^1$ is compact, so the same calculation proves

$$
\operatorname{vol}([G]^1)<\infty.
\tag{5.6}
$$

At sufficiently high height the cusp chart is injective modulo $B(F)$, and the compact coordinate sets may be replaced by smaller positive-measure subsets. Hence there are constants $c,C>0$ such that every nonempty cusp satisfies

$$
\frac cY\leq
\operatorname{vol}\{x\text{ in that cusp}:H(x)\geq Y\}
\leq\frac CY
\qquad(Y\geq Y_0).
\tag{5.7}
$$

Thus the exponent $1$ is exact. It is not a rough consequence of finite volume.

For completeness, the upper and lower estimates use different halves of reduction theory. For the upper bound, cover the cusp by finitely many coordinate products. On each product the quotient density is (3.4a) times a bounded positive Jacobian, so integration gives at most $C/Y$. Sum over the finite cover and use the uniform overlap bound.

For the lower bound, choose compact subsets $U_N\subset\Omega_N$, $U_T\subset\Omega_T$, and $U_K\subset K$ of positive measure whose closures avoid the boundaries of the chosen fundamental cells. High-cusp uniqueness says that, after increasing $Y_0$, the map from

$$
U_N\times U_T\times [Y,2Y]\times U_K
$$

to the chosen cusp is injective modulo a fixed finite stabilizer. The Jacobian is bounded below by a positive number. Hence the image has volume at least

$$
c_0\int_Y^{2Y}\frac{dH}{H^2}
=\frac{c_0}{2Y}.
$$

The first dyadic interval already gives the desired lower bound. The argument identifies a uniform positive-measure tube persisting at every height, rather than merely proving that the cusp is nonempty.

Finite volume now follows without circularity. The compact truncation has finite measure because finitely many compact coordinate products cover it. Each cusp tail has finite measure by the upper estimate. There are finitely many cusps at fixed level, and the unrestricted central quotient is covered by finitely many adelic Siegel regions. No prior finite-covolume assertion entered this proof.

The total volume is not claimed to equal a normalization-independent number. It changes if an archimedean Haar measure in Chapter 2 is rescaled. What is exact under our conventions is the quotient measure, the factor $\kappa'_F$, the $H^{-2}$ density, and the exponent of the tail.

The same calculation gives a useful family of integrability tests. For real $\sigma$ and an integer $m\geq0$,

$$
\int_{H\geq Y}H^\sigma(\log H)^m\,d\mu
\asymp
\int_Y^\infty H^{\sigma-2}(\log H)^m\,dH.
\tag{5.7a}
$$

The integral converges exactly when $\sigma<1$. At $\sigma=1$ it diverges for every $m\geq0$, and for $\sigma<1$ it is bounded by a constant times

$$
Y^{\sigma-1}(1+\log Y)^m.
$$

Both directions of the comparison use the positive-measure tube from the lower-bound proof. Thus the critical exponent is a geometric invariant of this height normalization, not merely an upper estimate. In particular, $\log H$ has moments of every fixed order on the finite-volume quotient, while $H$ itself is not integrable in a nonempty cusp.

If the height is replaced by $H'=c(u)H$ with $c(u)$ bounded above and below on the compact coordinates, then (5.7a) and its convergence threshold are unchanged. This explains why later Sobolev and tail statements are independent of the particular balanced section used to define $H$.

### 5.6 Counting and truncation estimates

Define the truncation

$$
[\overline G]_{\leq Y}
=\{x\in[\overline G]:H(x)\leq Y\},
\tag{5.8}
$$

with the compact core included and with one height in each of the finitely many level cusps. The reduction and high-cusp intersection theorems imply:

- $[\overline G]_{\leq Y}$ is compact after passing to the archimedean locally symmetric quotient at fixed finite level;
- its boundary is a finite union of compact cross-sections;
- the complement has volume at most $C/Y$;
- the number of reduced representatives of any point is bounded uniformly in $Y$;
- on a compact height interval $H_0\leq H\leq Y$, only finitely many rational translates of a fixed compact set can meet.

To justify the first item, take a sequence of reduced points with height bounded by $Y$. Compactness of the unipotent, norm-one torus, central, and maximal-compact coordinates gives a convergent subsequence in one of finitely many coordinate products. Its limit may lie on a boundary, but the quotient identifies that boundary point with a point in the closure of the truncation. Conversely, a sequence leaving every compact subset must eventually leave every bounded height region and therefore has $H\to\infty$ in one of the finitely many cusps. Height is a proper exhaustion function after finite level and central quotient.

This statement fails on $G(F)\backslash G(\mathbf A)$ before removal of the split center: a scalar sequence can leave compact sets while keeping $H_B=1$. It also fails if one keeps unreduced unit directions at infinity: units can move logarithmic coordinates unboundedly at fixed global height. Both failures explain why the center and the unit lattice were handled before truncations were introduced.

For a compactly supported function $f$ on $G(\mathbf A)$, properness modulo $G(F)$ gives pointwise finiteness of

$$
\sum_{\gamma\in G(F)}f(x^{-1}\gamma y).
$$

The Siegel property strengthens this on truncations to a uniform finite bound depending on the support of $f$ and on $Y$. Global integrability still needs cusp estimates; pointwise finiteness alone does not control a diagonal integral.

Smooth truncation is often preferable to a sharp boundary. Choose a smooth function $\chi$ on $\mathbf R$ with $\chi(s)=1$ for $s\leq0$ and $\chi(s)=0$ for $s\geq1$, and in each cusp put

$$
\chi_Y(g)=\chi(\log H(g)-\log Y).
$$

Extend it by one over the compact core. Finite overlap permits the cusp definitions to be patched into a global function satisfying

$$
0\leq\chi_Y\leq1,
\qquad
\chi_Y=1\text{ on }H\leq Y,
\qquad
\chi_Y=0\text{ on }H\geq eY.
\tag{5.8a}
$$

Every invariant derivative of fixed order is bounded independently of $Y$. Radial derivatives differentiate $\chi(\log H-\log Y)$, while transverse derivatives vanish on the pure height factor and only meet uniformly bounded patching functions. These cutoffs allow integration by parts and compact-support approximation without height-dependent derivative losses.

For $f\in L^2$, dominated convergence gives $\chi_Yf\to f$ in $L^2$. This individual approximation is not compactness: the height $Y$ may depend on $f$. For a bounded cuspidal Sobolev family, Chapter 10 proves a uniform estimate on $(1-\chi_Y)f$, which is the additional ingredient needed for total boundedness.

If $\widetilde\chi_Y$ is supported in one reduced Siegel region, then at every quotient point the sum

$$
\sum_{[\gamma]\in Z(F)\backslash G(F)}
\widetilde\chi_Y([\gamma]g)
$$

has at most a fixed number of nonzero terms. Its derivatives and $L^p$ norms are therefore bounded by the corresponding local quantities times the overlap constant. This is the mechanism for passing from one cusp calculation to a global quotient estimate.

## 6. Cusp coordinates and geometry

### 6.1 The high cusp as a quotient chart

For $Y\geq Y_0$, high-cusp uniqueness identifies a cusp with a quotient of

$$
[N]\times\Omega^1\times[Y,\infty)\times K
\tag{6.1}
$$

by compact stabilizers and, at fixed finite level, by a finite group. Here $[N]=F\backslash\mathbf A$ has probability measure $d\bar x$, $\Omega^1$ collects the compact norm-one torus and central data, and $H\in[Y,\infty)$ is height.

The measure has the form

$$
d\mu
=b(u,k,H)\,d\bar x\,du\,dk\,\frac{dH}{H^2},
\tag{6.2}
$$

where $b$ is smooth in the archimedean variables, locally constant at finite level, and bounded above and below by positive constants with all invariant derivatives bounded. With a carefully chosen product section, $b$ can be made independent of $H$; the bounded form (6.2) is invariant under changing sections and is all the analytic argument requires.

Put $t=\log H$. Then

$$
\frac{dH}{H^2}=e^{-t}\,dt.
\tag{6.3}
$$

Thus the rank-one density exponent in the notation of a standard cusp is $2\rho=1$.

Let us derive the chart rather than treating it as a picture. Fix a finite cusp representative $c$. A point sufficiently far out is represented by

$$
n(x)t_1a(H)kc,
$$

where $x\in\mathbf A$, $t_1$ belongs to a compact norm-one torus set, and $k$ belongs to a compact archimedean factor together with the fixed finite level. If two such points agree in the quotient, high-cusp uniqueness places the rational transition matrix in $B(F)$. Its unipotent part changes $x$ by $F$, its diagonal root part changes $t_1$ by $F^\times$, and its scalar part is removed by the center. Thus the remaining identifications are exactly those already built into $[N]$, the compact torus class, and a finite stabilizer. This proves (6.1).

The density follows by disintegrating (2.1) in the same order. The $[N]$ coordinate has mass one because we use $d\bar x$; replacing it by $dx$ would contribute the fixed factor $c_F$. The norm-one root class has probability measure, with its fixed factor $\kappa'_F$. The height contributes $H^{-1}dH/H$. A smooth change among compact sections multiplies the product density by the Radon--Nikodym factor $b$. Compactness of the parameter space and invertibility of the change give

$$
0<b_0\leq b(u,k,H)\leq b_1<\infty.
\tag{6.3a}
$$

The same argument applied to invariant derivatives gives bounded derivatives of $b$. Therefore all analytic constants can be chosen uniformly for $H\geq Y_0$ in a fixed cusp and, after taking a finite maximum, in every cusp at the fixed level.

### 6.2 Height and invariant derivatives

Conjugation by the torus gives

$$
a(H)n(x)a(H)^{-1}=n(y(H)x),
$$

where the archimedean components of $|y(H)|$ are comparable to $H^{1/n}$ by (3.7). Consequently a fixed invariant derivative in an archimedean unipotent direction has the coordinate form

$$
W_j=e^{\lambda_jt}V_j+\text{uniformly bounded lower-order terms},
\qquad \lambda_j\geq\frac1n.
\tag{6.4}
$$

The $V_j$ span the real tangent space of the compact archimedean part of $F\backslash\mathbf A$. Finite adelic directions are already compact and become finite-dimensional after fixing a compact open level. Compact torus and maximal-compact directions remain uniformly bounded.

The radial invariant derivative is uniformly equivalent to $\partial_t$. Therefore every fixed-level cusp satisfies the geometric hypotheses needed for invariant Sobolev estimates: compact cross-section, density $e^{-t}$ times a bounded factor, and transverse expansion at least $e^{t/n}$.

To check the exponent, write the balanced root at an archimedean place as $y_v(t)$. For $X_v$ in the real Lie algebra of $N(F_v)$,

$$
\operatorname{Ad}(\operatorname{diag}(y_v(t),1))X_v
=y_v(t)X_v.
$$

At a real place, (3.7) gives $|y_v(t)|\asymp e^{t/n}$. At a complex place, the normalized absolute value is $|y_v|_{\mathrm{usual}}^2$, and the same balanced formula again gives $|y_v(t)|_{\mathrm{usual}}\asymp e^{t/n}$. The complex unipotent direction has two real coordinates, both multiplied by this ordinary modulus. Hence every real transverse direction expands at the same lower rate $e^{t/n}$, even though its contribution to the global module was counted with local degree two.

Changing from a coordinate derivative to a right-invariant field introduces coefficients from the compact $t_1$ and $k$ variables. Those coefficients and their inverses remain bounded. Differentiating them yields the lower-order terms in (6.4). This proves both the principal expansion and the uniform control required when fields are commuted in higher Sobolev estimates.

Equivalently, after taking bounded linear combinations of a full invariant frame $X_1,\ldots,X_m$, the coordinate gradient along the unipotent fiber satisfies the pointwise estimate

$$
|\nabla_Yu|^2
\leq Ce^{-2t/n}\sum_{i=1}^m|X_i u|^2.
\tag{6.4b}
$$

This form allows the compact variables to mix the invariant directions and is the one used in the Poincare estimate. It asserts control by the full first-order invariant energy, not by a coordinate field that has been held fixed while the compact coordinates vary.

Fix a basis $X_1,\ldots,X_m$ of the archimedean Lie algebra modulo the scalar direction and let the same letters denote right-invariant fields. On a fixed level and compact type, define

$$
\|u\|_{H^r}^2
=\sum_{j\leq r}\ \sum_{i_1,\ldots,i_j}
\|X_{i_1}\cdots X_{i_j}u\|_2^2.
\tag{6.4a}
$$

Different bases give equivalent norms. On a compact truncation this is the ordinary Sobolev norm in finitely many charts. In the cusp, it is stronger in the transverse coordinate directions because $X_i$ contains the expanding factor $e^{\lambda_it}$. This is desirable: bounded invariant energy records the increasing geometric cost of a fixed amount of coordinate oscillation.

The scalar Lie direction has been omitted because it is absent on the central quotient; in a fixed central-character realization it acts by a fixed imaginary scalar and contributes only a bounded zeroth-order term. Compact-direction fields may be retained in (6.4a), or replaced on a fixed type by their finite scalar energy. These alternatives yield equivalent forms with constants depending on the type.

At finite places there are no derivatives in (6.4a). Fixing $K_f'$ turns the finite adelic variables into discrete finite-level data, while shrinking $K_f'$ enlarges the family of spaces being considered. The compactness theorem fixes the level first; it makes no assertion that one Sobolev ball remains compact while the finite level varies.

### 6.3 Several archimedean places

It is tempting to use one height $y_v$ at each archimedean place and thereby obtain a higher-dimensional positive cone. Before quotienting by units, that description is correct. The logarithms of global units form a lattice in the hyperplane of total logarithmic sum zero. Reduction modulo this lattice makes the orthogonal directions compact, leaving only the ray $t=\log H$.

This is why the adelic cusp remains rank one even when $F$ has many archimedean places. The field degree appears not as the number of unbounded variables but in the weakest transverse expansion exponent $1/n$.

Without reduction by units, a sequence could expand at one embedding and contract at another while keeping global height fixed. Such coordinates do not form a compact cross-section and are unsuitable for global estimates. The balanced representative theorem is precisely the correction.

### 6.4 Finite level and the set of cusps

Fix a compact open $K_f'\subset G(\mathbf A_f)$. The locally symmetric quotient is

$$
X(K_f')
=Z(\mathbf A)G(F)\backslash G(\mathbf A)/K_f'.
\tag{6.5}
$$

Its cusps are indexed by the finite double-coset set

$$
B(F)\backslash G(\mathbf A_f)/K_f'.
\tag{6.6}
$$

Finiteness follows directly from reduction: project the finite set $C$ in (4.4) to the double quotient. Conversely, each double coset supplies a cusp chart by translating the standard one.

The indexing has a direct rational-line interpretation. A cusp is a $G(F)$-orbit of a rational parabolic together with a finite-level structure. Since $G(F)$ is transitive on $F$-rational lines, move the parabolic to $B$; the remaining finite component is then defined up to left $B(F)$ and right $K_f'$, giving (6.6). Surjectivity follows from Iwasawa decomposition at infinity. Injectivity follows because a rational equivalence between two standard high-cusp ends must lie in $B(F)$ by Theorem 5.1.

At full level, these classes are controlled by the ideal class group. At a smaller level, the natural map from (6.6) to the full-level cusp set has finite fibers because $K_f'$ has finite index in a suitable compact open subgroup containing it. This proves finiteness without assuming a class-number-one field and explains why a single classical cusp picture is insufficient in general.

The quotient may have finite stabilizers. Choose a sufficiently small normal compact open subgroup $K_f''\subset K_f'$ for which the associated arithmetic groups are torsion-free. The map

$$
X(K_f'')\longrightarrow X(K_f')
$$

is a finite covering away from the harmless finite isotropy, and $L^2(X(K_f'))$ is the invariant subspace of the finite deck action on $L^2(X(K_f''))$. All Sobolev, compactness, and spectral conclusions descend to this closed invariant subspace. Thus no torsion-free hypothesis is silently imposed on the final theorems.

### 6.5 The rational and imaginary-quadratic models

For $F=\mathbf Q$ and full finite level, the archimedean quotient is the modular surface. With

$$
g=n(x)\begin{pmatrix}y^{1/2}&0\\0&y^{-1/2}\end{pmatrix}k,
$$

height is $H=y$, and the quotient measure is a constant multiple of

$$
\frac{dx\,dy}{y^2}.
$$

The cross-section is $\mathbf R/\mathbf Z$, and the invariant transverse derivative is $y\partial_x=e^t\partial_x$. Here $n=1$, so (6.4) is exact with exponent one.

For an imaginary quadratic field, the archimedean symmetric space is hyperbolic three-space. The unipotent cross-section is a two-dimensional torus coming from a lattice in $\mathbf C$, and balanced scaling has usual complex modulus $H^{1/2}$ because the normalized complex absolute value is its square. Thus $n=2$ and the weakest transverse expansion is $e^{t/2}$. The cusp-volume density is still $dH/H^2$, showing that measure decay and transverse metric scaling record different aspects of the field degree.

For a real quadratic field, two upper-half-plane factors appear before the unit quotient. If their usual heights are $y_1$ and $y_2$, global height is comparable to $y_1y_2$. A fundamental unit translates $(\log y_1,\log y_2)$ along the line of constant sum. Reducing by that translation confines $\log y_1-\log y_2$ to a bounded interval, so both $y_i$ are comparable to $H^{1/2}$. The remaining sum coordinate is $\log H$. This is the simplest example in which unit reduction genuinely turns a multidimensional positive cone into one cusp ray.

These models also expose a common false analogy. The exponent in the invariant transverse derivative is not always one, as it is for the modular surface. It is $1/n$ after a uniform balancing valid at every archimedean place. The weaker exponent gives a slower quantitative tail estimate but still tends to infinity and therefore still yields compactness.

## 7. Automorphic $L^2$ spaces

### 7.1 The norm-one space

Finite volume allows us to form

$$
\mathcal H^1=L^2([G]^1,d\dot g),
\qquad [G]^1=G(F)\backslash G(\mathbf A)^1.
\tag{7.1}
$$

Functions are equivalence classes modulo equality almost everywhere. The right regular action is

$$
(R(h)\phi)(g)=\phi(gh),
\qquad h\in G(\mathbf A)^1.
\tag{7.2}
$$

The quotient measure is right invariant because $G(\mathbf A)^1$ is unimodular. Hence

$$
\|R(h)\phi\|_2=\|\phi\|_2.
$$

Strong continuity follows first for compactly supported continuous functions by uniform continuity and then for all of $\mathcal H^1$ by density and unitarity.

The Hilbert space is separable. The quotient is second countable and has a $\sigma$-finite regular measure; compactly supported continuous functions on a countable exhaustion admit a countable dense family. This point later ensures that compact types, levels, spectral eigenspaces, and irreducible summands can all be indexed countably. It also permits the countable dense subgroup used in the closedness proof.

Finite volume is essential here only for the inclusion of bounded functions such as the constant function. The right regular action would still be unitary on an infinite-volume quotient, but the spectral conclusion would change because the split central $dr/r$ direction would supply another translation channel. Unitarity of the action and finiteness of the quotient are logically distinct.

The constant function belongs to $\mathcal H^1$ because the quotient has finite volume. This simple example shows that finite volume alone does not isolate the cusp spectrum.

### 7.2 Central-character spaces

The compact abelian group

$$
C_F^1=F^\times\backslash\mathbf A^1
\tag{7.3}
$$

acts centrally on $[G]^1$. Its unitary characters form a countable discrete group because $C_F^1$ is compact and second countable. For a character $\chi$ define

$$
\mathcal H^1_\chi
=\{\phi\in\mathcal H^1:R(z)\phi=\chi(z)\phi
\text{ for every }z\in C_F^1\}.
\tag{7.4}
$$

The orthogonal projection is

$$
P_\chi\phi(g)
=\int_{C_F^1}\overline{\chi(z)}\phi(gz)\,dz,
\tag{7.5}
$$

where $dz$ is probability Haar measure. Character orthogonality gives

$$
P_\chi^2=P_\chi=P_\chi^*,
\qquad
P_\chi P_{\chi'}=0\quad(\chi\ne\chi').
$$

Fourier completeness on the compact abelian group gives the Hilbert sum

$$
\mathcal H^1
=\widehat\bigoplus_{\chi\in\widehat{C_F^1}}
\mathcal H^1_\chi.
\tag{7.6}
$$

The hat means completion in the square-sum norm. It does not mean that an individual function has only finitely many central Fourier modes. Parseval's identity makes the decomposition quantitative:

$$
\|\phi\|_2^2
=\sum_{\chi\in\widehat{C_F^1}}\|P_\chi\phi\|_2^2.
\tag{7.6a}
$$

To prove it directly, disintegrate the quotient measure over $C_F^1$, apply Fourier theory on each compact central orbit, and integrate the fiberwise identity over the quotient by that orbit. Fubini applies to $|\phi|^2$. The same argument shows that the central decomposition commutes with right translation, because the central action commutes with all of $G(\mathbf A)^1$.

### 7.3 Equivalence of the two realizations

Let $\omega$ be a unitary character of $F^\times\backslash\mathbf A^\times$ and let $\chi=\omega|_{C_F^1}$. The space $L^2_\omega$ of (2.5)--(2.6) and $\mathcal H^1_\chi$ carry equivalent representations after restricting or extending across the determinant-module splitting.

To see this without hiding a measure factor, choose a measurable section $s:\mathbf R_{>0}\to\mathbf A^\times$ of the idele module and use the central scalar $s(r)I_2$ to move every $g\in G(\mathbf A)$ to $G(\mathbf A)^1$. If $|\det g|_{\mathbf A}=r^2$, set

$$
g^1=s(r)^{-1}g.
$$

Then $|\det g^1|_{\mathbf A}=1$. An $\omega$-equivariant function is determined by its restriction to $G(\mathbf A)^1$, and that restriction transforms under $C_F^1$ by $\chi$. Conversely, a $\chi$-equivariant function on the norm-one group extends by

$$
\phi(s(r)g^1)=\omega(s(r))\phi(g^1).
$$

Changing $s$ changes $s(r)$ by an element of $\mathbf A^1$, and the $\chi$ transformation law makes the extension independent of the choice. The quotient integration formulas show equality of norms. Thus the central quotient and norm-one descriptions encode the same fixed-unitary-central-character problem.

More explicitly, the map from the norm-one quotient to the central quotient has compact fiber $C_F^1$. On the $\chi$-isotypic subspace, the absolute value of a function is constant along that fiber. With probability measure on $C_F^1$, integrating over the fiber contributes exactly one. This is the norm equality; no hidden factor equal to the volume of the idele class group remains. Had we used the quotient measure inherited from $d^\times x$ without normalizing the compact fiber, the two norms would differ by its finite volume.

We use $L^2_\omega$ when the full group action and a central character are conceptually convenient, and $\mathcal H^1_\chi$ when the compact central Fourier decomposition is useful.

### 7.4 The right regular representation

On $L^2_\omega$, right translation by $G(\mathbf A)$ is unitary. Indeed, it preserves (2.5), and right invariance of the quotient measure gives

$$
\int_{[\overline G]}|\phi(gh)|^2\,d\bar g
=\int_{[\overline G]}|\phi(g)|^2\,d\bar g.
$$

For $f\in C_c(G(\mathbf A))$, define

$$
R(f)\phi(g)=\int_{G(\mathbf A)}f(h)\phi(gh)\,dh.
\tag{7.7}
$$

Then

$$
\|R(f)\|\leq\|f\|_{L^1(G(\mathbf A))}.
\tag{7.8}
$$

If $f^*(g)=\overline{f(g^{-1})}$, unimodularity gives $R(f)^*=R(f^*)$. At finite places, locally constant compactly supported functions provide the usual convolution operators; at infinity, smooth compactly supported functions produce smooth vectors.

### 7.5 Central and compact-type decompositions

Fix a compact open $K_f'\subset G(\mathbf A_f)$ and write

$$
\mathcal H_\omega(K_f')=L^2_\omega{}^{K_f'}.
\tag{7.9}
$$

Let $K_\infty=\prod_{v\mid\infty}K_v$. For an irreducible unitary representation $\tau$ of $K_\infty$, character averaging gives an orthogonal isotypic projection $P_\tau$. Thus

$$
\mathcal H_\omega(K_f')
=\widehat\bigoplus_{\tau\in\widehat K_\infty}
\mathcal H_\omega(K_f',\tau),
\qquad
\mathcal H_\omega(K_f',\tau)=P_\tau\mathcal H_\omega(K_f').
\tag{7.10}
$$

If $d_\tau=\dim\tau$ and $\chi_\tau$ is its character, the projection is

$$
P_\tau\phi
=d_\tau\int_{K_\infty}\overline{\chi_\tau(k)}R(k)\phi\,dk.
\tag{7.10a}
$$

Character orthogonality proves that these projections are mutually orthogonal and sum strongly to the identity. The finite-level projection is the probability average over $K_f'$. The finite and archimedean projections commute because the corresponding group factors commute, and both commute with the central-character projection. Hence every order of imposing center, level, and compact type gives the same closed subspace.

Both the level and the type matter. Fixing only $K_f'$ leaves infinitely many archimedean compact types. Fixing only $\tau$ leaves infinitely many finite levels. Compactness and finite spectral windows will be proved on each pair $(K_f',\tau)$.

As $K_f'$ shrinks through a countable cofinal family, the union of its fixed-vector spaces is dense in the smooth finite-adelic vectors. As $\tau$ varies, the finite sums of isotypic components are dense for the archimedean compact action. These statements later let typewise conclusions determine the whole cuspidal representation.

## 8. Constant terms and cusp forms

### 8.1 Why an average detects escape

On a high cusp, the compact cross-section contains the unipotent quotient $[N]=F\backslash\mathbf A$. The transverse zero mode is the average over this quotient. It can move outward without paying unipotent derivative energy. Every nonzero mode must oscillate on $[N]$, and torus conjugation magnifies that oscillation.

The correct definition of a cusp form therefore removes this average before any spectral claim is made. The definition is algebraic in appearance but geometric in effect.

### 8.2 The global constant term

Let $\phi$ be a measurable automorphic function for which the following integral is locally absolutely convergent. Its constant term along $N$ is

$$
\phi_N(g)
=\int_{F\backslash\mathbf A}
\phi(n(x)g)\,d\bar x.
\tag{8.1}
$$

The probability measure $d\bar x=c_F^{-1}dx$ fixes the normalization. Using unnormalized measure would multiply $\phi_N$ by $c_F$ and would not change vanishing, but it would change norm estimates.

The integrand is well defined on $F\backslash\mathbf A$ because for $q\in F$,

$$
\phi(n(q)n(x)g)=\phi(n(x)g)
$$

by left $G(F)$-invariance. Since $[N]$ is compact, every continuous automorphic function has a pointwise constant term. For an $L^2$ class, the integral exists for almost every remaining cusp coordinate by Fubini; Chapter 9 gives the precise local definition.

The Fourier interpretation is exact. Choose a nontrivial continuous additive character $\psi:F\backslash\mathbf A\to\mathbf C^\times$. The character group of the compact quotient $F\backslash\mathbf A$ is naturally $F$: the element $\xi\in F$ gives $x\mapsto\psi(\xi x)$. On every square-integrable unipotent fiber,

$$
\phi(n(x)g)\sim\sum_{\xi\in F}W_\xi(g)\psi(\xi x)
$$

in the fiberwise $L^2$ sense, where

$$
W_\xi(g)=\int_{F\backslash\mathbf A}
\phi(n(x)g)\overline{\psi(\xi x)}\,d\bar x.
\tag{8.1a}
$$

The coefficient $W_0$ is precisely $\phi_N$. Cuspidality removes one character, not all unipotent Fourier data. The nonzero characters are the oscillatory modes controlled by transverse derivatives. No choice of $\psi$ affects which coefficient is constant.

At finite level, the allowable characters form the dual lattice of the archimedean torus in Section 10.1. Its zero character is isolated, so the first nonzero frequency is bounded away from zero. This spectral gap is the Fourier version of the transverse Poincare inequality.

### 8.3 Covariance and invariance

The constant term obeys three identities.

First, it is left $N(\mathbf A)$-invariant:

$$
\phi_N(n(u)g)=\phi_N(g),
\tag{8.2}
$$

because translation by $u$ preserves probability measure on $F\backslash\mathbf A$.

Second, for $t=\operatorname{diag}(a,d)\in T(F)$,

$$
\phi_N(tg)=\phi_N(g).
\tag{8.3}
$$

Indeed, substitute $x\mapsto(a/d)x$. Multiplication by $a/d\in F^\times$ preserves the quotient and its Haar measure by the product formula.

Third, constant terms commute with right translation:

$$
(R(h)\phi)_N(g)=\phi_N(gh).
\tag{8.4}
$$

Consequently the property $\phi_N(g)=0$ for every $g$ is invariant under the whole right regular action.

For $b=n(u)t\in B(\mathbf A)$, a change of variables gives the more general covariance

$$
\phi_N(bg)
=\phi_N(tg),
$$

with the expected central character when $b$ has a scalar factor. No modular factor occurs in the normalized average itself; modular factors enter when constant terms are compared as functions on a quotient with its own measure.

There is deliberately no assertion that $\phi_N(tg)$ equals a scalar multiple of $\phi_N(g)$ for arbitrary $t\in T(\mathbf A)$. Such a formula would impose an eigencondition that a general automorphic function does not satisfy. The identities above use arbitrary adelic unipotents, rational diagonals, right translations, and central scalars; that is the full covariance available before a spectral parameter is introduced.

For a conjugate parabolic $P=\gamma B\gamma^{-1}$ with unipotent radical $N_P=\gamma N\gamma^{-1}$, transport probability measure from $[N]$. Left invariance by $\gamma$ and a change of variables identify

$$
\int_{N_P(F)\backslash N_P(\mathbf A)}\phi(ug)\,du
$$

with $\phi_N$ evaluated at a translated argument. Hence vanishing of (8.1) for every argument is exactly vanishing of every proper rational constant term. This equivalence uses the rank-one fact that all proper parabolics of $G$ are rationally conjugate.

### 8.4 Smooth cusp forms

A smooth automorphic function $\phi$ of fixed unitary central character is cuspidal if

$$
\phi_N(g)=0
\qquad\text{for every }g\in G(\mathbf A).
\tag{8.5}
$$

For $\mathrm{GL}_2$, this single condition covers all proper rational parabolics. If $P=\gamma B\gamma^{-1}$ with $\gamma\in G(F)$, then its unipotent radical is $\gamma N\gamma^{-1}$, and left invariance plus the substitution $n\mapsto\gamma n\gamma^{-1}$ converts its constant term to (8.1) at a right translate.

Requiring (8.5) only at $g=1$ would be far too weak. Right translates explore all heights, compact coordinates, and finite cusp classes. The quantifier “for every $g$” is what makes cuspidality a representation-invariant condition.

If a smooth cusp form is square-integrable, it belongs to the cuspidal $L^2$ space defined below. Conversely, a smooth vector in that $L^2$ space has pointwise vanishing constant term and rapid decay, so the two uses of “cuspidal” agree on smooth vectors.

### 8.5 The $L^2$ cuspidal condition

Choose a countable family of cusp-coordinate regions as follows. In the finite adelic variables take a countable exhaustion by compact open pieces; in the archimedean compact variables take a countable relatively compact atlas; and in height take bounded intervals with rational endpoints. Reduction theory says that these regions cover every standard-parabolic chart. On one such region $\mathcal U$, let

$$
\mathcal C_{\mathcal U}\phi(H,u,k)
=\int_{[N]}\phi(n(x)a(H)u k c)\,d\bar x
\tag{8.6}
$$

for almost every $(H,u,k)$. Define

$$
L^2_{\mathrm{cusp},\omega}
=\{\phi\in L^2_\omega:
\mathcal C_{\mathcal U}(R(h)\phi)=0\text{ almost everywhere}
\text{ for every }\mathcal U\text{ and }h\in G(\mathbf A)\}.
\tag{8.7}
$$

At a fixed compact open level, the regions regroup into the finitely many cusp charts of Section 6.4. For the unrestricted space they remain countable, which is essential: no finite level has been silently imposed on a general vector. It is enough to take $h$ in a countable dense subset and then use continuity of right translation together with local boundedness of averaging. This makes (8.7) a countable intersection of closed conditions and avoids a set-theoretic ambiguity about uncountably many null sets.

Equivalently, $\phi_N(g)=0$ for almost every $g$ in the local quotient on which the constant term is defined. The translated chart formulation is more convenient for proving closedness, while the global formulation is more invariant.

The central character causes no conflict with averaging. Since scalar matrices commute with $n(x)$,

$$
(\phi_N)(zg)=\omega(z)\phi_N(g).
$$

Thus the zero constant-term condition is defined within each central-character space. Level and compact-type projections also commute with it because they are averages of right translations. The cuspidal subspace can therefore be decomposed by center, finite level, and archimedean compact type without changing its definition.

### 8.6 Examples and nonexamples

The constant function on a finite-volume quotient has

$$
1_N=1,
$$

so it is not cuspidal.

For $F=\mathbf Q$, a classical Fourier expansion in the standard cusp has the form

$$
\phi(x+iy)=\sum_{m\in\mathbf Z}a_m(y)e^{2\pi imx}.
$$

The constant term is $a_0(y)$. Cuspidality is exactly $a_0(y)=0$ at every cusp. The adelic definition packages all cusp classes and all levels into the single integral (8.1).

A compactly supported smooth function on the quotient need not be cuspidal: averaging it over a unipotent fiber can be nonzero. Conversely, a cusp form need not be compactly supported. Its support may extend through every cusp, but its values decrease rapidly once smoothness and finite type are imposed.

The condition is also stronger than orthogonality to constants. A nonzero function of the height alone can have total integral zero and still have a nonzero unipotent constant term. Cuspidality removes the full height-dependent zero mode, not merely one global scalar.

There is a useful local model of a genuine cusp form. On a torus fiber $Y=\Lambda\backslash F_\infty$, take a nonzero character $e^{2\pi i\langle\xi,y\rangle}$ and multiply it by a smooth function of $t$ and the compact coordinates. Its fiber average vanishes. A finite sum of such terms is cuspidal within that chart, although extending it to a global automorphic function requires compatibility on overlaps. The invariant transverse derivative multiplies the $\xi$-term by a quantity comparable to $e^{t/n}|\xi|$, making the compactness mechanism visible term by term.

By contrast, a function supported in a cusp and constant on each unipotent fiber remains noncuspidal even if it changes sign in $t$, has total integral zero, and decays at infinity. Decay alone is not the definition: it may be too weak for uniform compactness on bounded families, while the zero-mode condition is stable under the group action and yields decay as a theorem.

Cuspidality is also sensitive to every cusp class. At a level with several cusps, a function can have zero constant term in the standard chart and a nonzero constant term in another. The adelic quantifier over all right translates, or the equivalent finite collection of translated charts at fixed level, rules out this partial condition.

## 9. Closedness and cuspidal projection mechanisms

### 9.1 Local boundedness of fiber averaging

Let $\mathcal U$ be a relatively compact set of the non-unipotent cusp coordinates, including a bounded height interval. On the corresponding chart define

$$
(A_{\mathcal U}\phi)(u)
=\int_{[N]}\phi(x,u)\,d\bar x.
$$

Jensen's inequality for the probability measure gives

$$
|A_{\mathcal U}\phi(u)|^2
\leq\int_{[N]}|\phi(x,u)|^2\,d\bar x.
$$

Integrating and using the bounded density factor in (6.2) yields

$$
\|A_{\mathcal U}\phi\|_{L^2(\mathcal U)}
\leq C_{\mathcal U}\|\phi\|_{L^2(\text{chart over }\mathcal U)}.
\tag{9.1}
$$

If the product coordinates are chosen with exact product measure, $C_{\mathcal U}=1$. The bounded-density formulation is stable under changing sections and is sufficient.

The dependence on $\mathcal U$ is harmless in the closedness argument because each region is relatively compact. It cannot simply be dropped on the whole cusp: changing from quotient measure to product measure may introduce a factor whose behavior at infinity must first be controlled. The high-cusp bounds (6.3a) provide such control at fixed level, but the local exhaustion works uniformly even before a level is imposed.

The same Jensen estimate applies to weak derivatives tangent to the non-unipotent variables. For an unipotent derivative, integration over the compact fiber gives zero. Consequently fiber averaging extends continuously from the local $H^1$ space to the $H^1$ space on the base of the chart. This observation is used when cuspidality is passed to Sobolev limits in Chapter 10.

Thus constant-term averaging is a bounded operator on every truncated chart. It need not be a bounded operator from the full automorphic $L^2$ space to one global unweighted $L^2$ space on $B(F)\backslash G(\mathbf A)$; the target measure has a different modular weight. Closedness must therefore be proved locally and then exhausted, not asserted from a nonexistent global contraction.

### 9.2 Closedness of the cuspidal space

**Theorem 9.1.** For every number field $F$ and every unitary idele class character $\omega$, the subspace $L^2_{\mathrm{cusp},\omega}$ is closed in $L^2_\omega$.

**Proof strategy.** Express cuspidality as the simultaneous vanishing of bounded fiber averages on a countable exhaustion of cusp charts and a countable dense set of right translates.

**Proof.** Use the countable family of finite-coordinate pieces, archimedean charts, and bounded height intervals from Section 8.5. On each resulting region, (9.1) gives a bounded averaging operator. At finite level this family collapses to finitely many cusps, but no level restriction is needed for the present argument.

Choose a countable dense subgroup $D\subset G(\mathbf A)$; second countability supplies one. For every region, cusp, and $h\in D$, the kernel of

$$
A_{\mathcal U}R(h)
$$

is closed. Their countable intersection is therefore closed.

Why can $D$ be chosen to be a subgroup rather than merely a dense set? Begin with a countable basis of neighborhoods and select one point from each nonempty basis element. The subgroup generated by those points is countable and dense. This makes inverses and products available while preserving countability.

If $\phi$ lies in this intersection and $h_j\to h$, then $R(h_j)\phi\to R(h)\phi$ in $L^2$. Local boundedness of $A_{\mathcal U}$ passes vanishing to $h$. Exhausting the cusp gives (8.7) for every $h$. Conversely, (8.7) plainly lies in every kernel. Thus the intersection is exactly $L^2_{\mathrm{cusp},\omega}$. $\square$

This proof also shows that the definition is independent of the chosen Siegel representatives: two systems of cusp charts have a common refinement on sufficiently high regions, while their compact remainders impose no additional parabolic condition.

There is an equivalent sequential formulation. If $\phi_j$ are cuspidal and $\phi_j\to\phi$ in $L^2_\omega$, then on every truncated chart

$$
A_{\mathcal U}R(h)\phi_j\longrightarrow
A_{\mathcal U}R(h)\phi
$$

in the local $L^2$ norm. The left side vanishes, so the right side does also. Exhaustion and density in $h$ give cuspidality of $\phi$. This formulation makes clear that no pointwise convergence of the automorphic functions is required.

### 9.3 Invariance under translation and convolution

Identity (8.4) gives

$$
R(h)L^2_{\mathrm{cusp},\omega}
\subseteq L^2_{\mathrm{cusp},\omega}.
$$

Since $R(h)$ is invertible, equality holds. Closedness then gives an orthogonal projection

$$
P_{\mathrm{cusp}}:L^2_\omega\longrightarrow
L^2_{\mathrm{cusp},\omega}.
\tag{9.2}
$$

The projection commutes with every $R(h)$: both the subspace and its orthogonal complement are invariant under a unitary action. It consequently commutes with every bounded convolution operator $R(f)$.

Ordinary convolution preserves cuspidal input but does not generally turn noncuspidal input into cuspidal input. The universal cuspidal projection is $P_{\mathrm{cusp}}$, whose existence rests on closedness rather than on an unproved cancellation property of a test function.

### 9.4 Density of smooth cuspidal vectors

Let $(\eta_j)$ be a smooth approximate identity on the archimedean group, combined with normalized characteristic functions of compact opens shrinking to the identity at the finite places. Then

$$
R(\eta_j)\phi\longrightarrow\phi
\quad\text{in }L^2_\omega.
\tag{9.4}
$$

If $\phi$ is cuspidal, every $R(\eta_j)\phi$ is cuspidal by Section 9.3. Archimedean convolution makes it a smooth vector, and the finite factor makes it fixed by a compact open subgroup. Projecting onto finitely many $K_\infty$-types and letting the finite set grow gives finite-type smooth cuspidal vectors converging to $\phi$.

The approximate identities may be chosen to respect the central character. Convolution already preserves it because the center commutes with right translation. If one works in the norm-one realization, apply the compact central projection $P_\chi$ after smoothing; it commutes with the smoothing operator. Similarly, the finite-level and compact-type projections are contractions, so inserting them does not spoil convergence.

Therefore

$$
L^2_{\mathrm{cusp},\omega}
=\overline{\{\text{smooth, finite-level, finite-type cusp forms in }L^2_\omega\}}.
\tag{9.5}
$$

This is the bridge between the constant-term definition for automorphic functions and the closed Hilbert subspace used in spectral theory.

### 9.5 The exact role of all translates

Suppose a function has zero average in one chosen high-cusp chart but not after a right translation. The right regular orbit then leaves the proposed space, so no representation decomposition could be carried out inside it. Requiring all translates prevents this failure.

For smooth automorphic functions, the global condition (8.5) automatically includes all translates because $g$ itself is arbitrary. For $L^2$ classes, local charts are defined only almost everywhere, so translated bounded operators supply the safe meaning. The two definitions coincide on the dense smooth subspace, and closedness extends the agreement to all of $L^2_{\mathrm{cusp},\omega}$.

## 10. Cuspidal decay and compactness

### 10.1 The transverse Poincare inequality

Fix a finite level and one cusp. The level condition gives invariance under an open compact additive subgroup $U_f\subset\mathbf A_f$. Strong additive approximation identifies

$$
F\backslash\mathbf A/U_f
\simeq \Lambda\backslash F_\infty
$$

for a full lattice $\Lambda\subset F_\infty$. Thus the effective unipotent fiber is a compact connected real torus $Y$, not an uncontrolled finite union. Only finitely many lattices $\Lambda$ occur among the reduced finite-coordinate pieces of one fixed level. For a function $v\in H^1(Y)$ with average zero,

$$
\|v\|_{L^2(Y)}
\leq C_Y\|\nabla_Yv\|_{L^2(Y)}.
\tag{10.1}
$$

**Proof.** If (10.1) failed, there would be mean-zero $v_j$ with $\|v_j\|_2=1$ and $\|\nabla v_j\|_2\to0$. Compactness of $H^1(Y)\hookrightarrow L^2(Y)$ gives a subsequence converging in $L^2$ to $v$. Its weak gradient is zero, so connectedness makes $v$ constant. Its mean is zero, hence $v=0$, contradicting $\|v\|_2=1$. $\square$

For a torus, one can see the constant explicitly. If $\Lambda^*$ is the dual lattice and

$$
v(y)=\sum_{\xi\in\Lambda^*\setminus\{0\}}
\widehat v(\xi)e^{2\pi i\langle\xi,y\rangle},
$$

then Parseval gives

$$
\|\nabla v\|_2^2
=4\pi^2\sum_{\xi\ne0}|\xi|^2|\widehat v(\xi)|^2
\geq4\pi^2\ell(\Lambda^*)^2\|v\|_2^2,
$$

where $\ell(\Lambda^*)$ is the length of the shortest nonzero dual vector. Thus one may take $C_Y=(2\pi\ell(\Lambda^*))^{-1}$. Finiteness of the possible level lattices gives the uniform constant used below.

Apply this on every unipotent fiber, with the other compact coordinates fixed. Cuspidality gives the mean-zero hypothesis. Estimate (6.4b) gives

$$
\|u(t,\cdot)\|_{L^2(Y)}^2
\leq Ce^{-2t/n}
\sum_i\|X_iu(t,\cdot)\|_{L^2(Y)}^2.
\tag{10.2}
$$

Finite stabilizers only change $C$. No finite-place differential operator is needed: the level has already converted the adelic fiber into the connected archimedean torus above. Taking the maximum over the finitely many possible lattices makes $C$ uniform throughout every cusp of the fixed-level quotient.

### 10.2 The cusp tail estimate

Multiply (10.2) by the bounded compact-coordinate density and by $e^{-t}dt$, then integrate over $t\geq T$. This gives

$$
\|u\|_{L^2(t\geq T)}^2
\leq Ce^{-2T/n}
\sum_j\|W_ju\|_{L^2(t\geq T)}^2.
\tag{10.3}
$$

Equivalently, in height coordinates,

$$
\|u\|_{L^2(H\geq Y)}
\leq CY^{-1/n}\|u\|_{H^1(H\geq Y)}.
\tag{10.4}
$$

The constant is uniform for $Y\geq Y_0$ and, after taking the maximum, uniform over the finite set of cusps at the fixed level.

Notice that the $L^2$ norm, not its square, decays by $Y^{-1/n}$. The cusp volume itself decays by $Y^{-1}$. These are different estimates: the first uses oscillation and derivative energy, while the second applies even to constants.

The tail estimate extends from smooth cusp forms to the $H^1$ closure. Fiber averaging is bounded in $H^1$ and commutes with weak limits, so the zero-average condition survives completion. Approximation by smooth cusp forms then passes (10.4) to every $u\in H^1_{\mathrm{cusp}}$.

Estimate (10.4) is a tightness statement. If a set $\mathcal B$ is bounded in the cuspidal $H^1$ norm, then

$$
\sup_{u\in\mathcal B}\|u\|_{L^2(H\geq Y)}
\longrightarrow0
\qquad(Y\to\infty).
\tag{10.4a}
$$

This uniform limit is stronger than saying that each individual $u$ has a small tail. Compactness needs one truncation working for the entire bounded set. Cuspidality supplies exactly this uniformity; finite cusp volume alone would only control uniformly bounded functions, not an arbitrary $H^1$-bounded family.

### 10.3 Higher decay and smooth vectors

Every invariant derivative of a smooth cusp form remains cuspidal. A unipotent derivative has integral zero on the compact fiber; the radial derivative commutes with fiber integration; compact-direction derivatives commute with the projection after resolving into finite types.

The higher-order estimate is not obtained merely by repeating the first-order inequality on the same function. Let $\Delta_Y$ be the positive Laplacian of the compact torus. On its mean-zero subspace the spectral theorem gives

$$
\|v\|_{L^2(Y)}
\leq \lambda_1(Y)^{-m/2}
\|\Delta_Y^{m/2}v\|_{L^2(Y)}
$$

for even $m$, with the corresponding gradient form for odd $m$. Expressing coordinate derivatives through the expanding invariant fields of (6.4), moving bounded lower-order terms to the right, and inducting on $m$ gives

$$
\|u\|_{L^2(H\geq Y)}
\leq C_mY^{-m/n}\|u\|_{H^m(H\geq Y)}.
\tag{10.5}
$$

Commutators among invariant fields produce lower-order derivatives, already included in the $H^m$ norm. Uniformity follows because only finitely many fiber lattices occur at fixed level and their first positive Laplace eigenvalues have a positive minimum.

If $u$ belongs to every invariant Sobolev space, Sobolev embedding on the fixed cylinder $[t-1,t+1]\times Y$ and (10.5) show that for every invariant differential operator $D$ and every $M>0$,

$$
|Du(g)|\leq C_{D,M}H(g)^{-M}
\tag{10.6}
$$

in every cusp. To obtain a prescribed $M$, take enough transverse derivatives that $m/n$ exceeds $M$ plus the finite loss from converting the weighted measure to a fixed cylinder measure.

Thus smooth finite-type cusp forms are rapidly decreasing. Rapid decrease is a theorem, not part of the definition of cuspidality.

### 10.4 Rellich compactness on truncations

Fix $Y$. After quotienting by $K_f'$ and resolving the finite-dimensional $K_\infty$-type, the truncation $X(K_f')_{\leq Y}$ is a compact manifold with boundary, or a finite quotient of one. The inclusion

$$
H^1(X(K_f')_{\leq Y})
\hookrightarrow L^2(X(K_f')_{\leq Y})
\tag{10.7}
$$

is compact.

No boundary condition is imposed in (10.7). The boundary at height $Y$ is an artificial cut used only for restriction. Boundary conditions become relevant only when an operator is independently realized on the truncation.

For completeness, compactness follows by a finite atlas and Euclidean averaging. On a cube of side $\delta$, replace a function by its average. The Poincare inequality bounds the $L^2$ error by $C\delta\|u\|_{H^1}$. The averaging map has finite-dimensional range. A finite partition of unity gives a uniform finite-rank approximation to the $H^1$ unit ball, proving total boundedness in $L^2$.

If the quotient has finite isotropy, perform this construction on a finite smooth cover. Average the finite-rank approximating map over the deck group. It then preserves the invariant subspace, has finite-dimensional range, and retains the same error bound up to a fixed constant. This proves compactness on the original quotient without pretending that all level quotients are manifolds.

### 10.5 The global compact embedding

Let

$$
H^1_{\mathrm{cusp},\omega}(K_f',\tau)
$$

be the fixed-level, fixed-$K_\infty$-type cuspidal Sobolev space. Its norm includes every invariant derivative of order at most one needed on the central quotient.

The argument is an instance of a general compactness criterion. Let $X=X_{\leq Y}\cup X_{>Y}$ be exhausted by relatively compact truncations. Suppose a Hilbert space $V$ embeds continuously into $L^2(X)$, the restriction $V\to L^2(X_{\leq Y})$ is compact for every $Y$, and

$$
\sup_{\|u\|_V\leq1}\|u\|_{L^2(X_{>Y})}\longrightarrow0.
\tag{10.7a}
$$

Then $V\hookrightarrow L^2(X)$ is compact. To prove this, choose $Y$ making the tail smaller than $\varepsilon$, approximate the restricted unit ball on $X_{\leq Y}$ by finitely many $\varepsilon$-balls, and extend those centers by zero. The global unit ball is then covered by finitely many $3\varepsilon$-balls. Total boundedness proves compactness. In our situation, local Rellich gives the first hypothesis and (10.4a) gives the second.

This formulation isolates the roles of geometry and cuspidality. Reduction theory constructs the exhaustion and proves local compactness; the vanishing constant term proves uniform tightness. Neither half alone establishes (10.8).

**Theorem 10.1 (cuspidal compactness).** The inclusion

$$
H^1_{\mathrm{cusp},\omega}(K_f',\tau)
\hookrightarrow
L^2_{\mathrm{cusp},\omega}(K_f',\tau)
\tag{10.8}
$$

is compact.

**Proof strategy.** Use Rellich compactness on a truncation and the cuspidal tail estimate uniformly on the complement.

**Proof.** Let $(u_j)$ be bounded in the left side. Given $\varepsilon>0$, choose $Y$ so large that (10.4), summed over the finitely many cusps, gives

$$
\|u_j\|_{L^2(H\geq Y)}<\varepsilon
$$

for every $j$. On the compact truncation, (10.7) gives a subsequence converging in $L^2$. Two sufficiently late terms differ by less than $\varepsilon$ on the truncation and by less than $2\varepsilon$ on the cusp tails. A diagonal subsequence for $\varepsilon=2^{-m}$ is Cauchy in the global $L^2$ norm and therefore converges. $\square$

The proof works on a torsion-free finite cover and descends to the invariant subspace for the finite deck group, so it applies to every compact open level.

The fixed-type hypothesis enters through the Sobolev norm on compact directions. On one $K_\infty$-type, compact-direction derivatives are bounded by a constant depending on $\tau$, and the remaining first derivatives control an ordinary local $H^1$ norm. Without fixing type, a bounded norm built only from the noncompact central quadratic operator need not control oscillation along $K_\infty$. The form used in Chapter 11 includes that missing compact energy.

### 10.6 Escape of mass without cuspidality

The full embedding $H^1\hookrightarrow L^2$ is not compact. In one cusp choose a smooth function $\psi$ supported in $(0,1)$ and define

$$
u_j(t,y)=c_j e^{t/2}\psi(t-j),
\tag{10.9}
$$

independent of the unipotent coordinate $y$, where $c_j>0$ is chosen so that $\|u_j\|_2=1$. Since the measure is comparable to $e^{-t}dt\,dy$, the factor $e^{t/2}$ makes the unnormalized masses bounded above and below independently of $j$; hence both $c_j$ and $c_j^{-1}$ are uniformly bounded. Radial derivatives remain uniformly bounded, and transverse derivatives vanish. For a spaced subsequence the supports are disjoint, so

$$
\|u_j-u_k\|_2=\sqrt2
\qquad(j\ne k).
$$

This sequence is bounded in $H^1$ and has no convergent $L^2$ subsequence. Its constant term is itself. The example proves that cuspidality, not finite volume, supplies tightness.

To verify the derivative bound, write $s=t-j$ on the support. Then

$$
\partial_tu_j
=c_j e^{t/2}\bigl(\psi'(s)+\tfrac12\psi(s)\bigr).
$$

Multiplication by the density $e^{-t}dt$ cancels $e^t$ in both the function and its radial derivative. All compact derivatives vanish, so the full first-order norm is independent of $j$ up to the fixed bounded cusp Jacobian. This makes the counterexample robust under every coordinate choice allowed in (6.2).

Subtracting the global integral of $u_j$ would make it orthogonal to constants but would not repair compactness: its fiberwise constant term would remain nonzero. The obstruction is therefore the entire height-dependent zero mode, not merely the one-dimensional space of constant functions.

## 11. Typewise elliptic spectrum

### 11.1 The positive measuring operator

Let $G_\infty=\prod_{v\mid\infty}G(F_v)$ and choose an $\operatorname{Ad}(K_\infty)$-invariant inner product on its Lie algebra modulo the scalar direction already removed. Let $\Omega_G$ be the central Casimir, with the convention that $-\Omega_G$ is positive on the noncompact directions, and let $\Omega_K$ be the nonnegative compact-direction operator. The elliptic combination is

$$
\Lambda=1-\Omega_G+2\Omega_K,
\tag{11.1}
$$

with signs chosen so that its quadratic form is positive. Its principal symbol is positive definite on the full tangent space. On a fixed irreducible $K_\infty$-type $\tau$, the compact quadratic operator $\Omega_K$ acts by a scalar, while $\Omega_G$ remains central for the infinitesimal group action.

Equivalently, one may take the positive invariant sum of squares from a global frame. The two choices have equivalent Sobolev forms on a fixed type. The form point of view avoids any dependence of the final spectrum on a particular basis.

On smooth cuspidal vectors of level $K_f'$ and type $\tau$, define

$$
q_\tau(u)=\langle\Lambda u,u\rangle.
$$

After adding a harmless positive constant, there are $c,C>0$ such that

$$
c\|u\|_{H^1}^2
\leq q_\tau(u)
\leq C\|u\|_{H^1}^2.
\tag{11.2}
$$

The constants may depend on $F$, $K_f'$, and $\tau$. No uniformity over all types is asserted here.

The lower estimate is local ellipticity plus a partition of unity. On a compact truncation it is the usual comparison between an elliptic quadratic form and the first Sobolev norm. In a cusp, write invariant fields in the coordinates of Section 6.2. The principal coefficients control $\partial_t$ and every transverse derivative; compact coefficients remain bounded, and lower-order terms are absorbed after adding the positive constant. The upper estimate follows from the reverse coefficient bounds. Uniformity in height is precisely why invariant, rather than coordinate, derivatives were used.

The form is symmetric on smooth finite-level cusp forms. Integration by parts creates no boundary term at infinity: first prove the identity for compactly supported truncations, insert cutoffs whose derivatives are supported in $Y\leq H\leq2Y$, and use (10.4) for the function and its first derivatives to let $Y\to\infty$. On the compact-type space, integration in compact directions has no boundary. Thus the analytic realization below agrees with the invariant differential expression.

### 11.2 Self-adjoint realization and compact resolvent

Close $q_\tau$ on

$$
H^1_{\mathrm{cusp},\omega}(K_f',\tau).
$$

The form is densely defined, closed, and bounded below. It therefore determines a unique self-adjoint operator $A_\tau\geq1$ characterized by

$$
q_\tau(u,v)=\langle A_\tau u,v\rangle
$$

for $u$ in the operator domain and $v$ in the form domain.

The compact embedding (10.8) implies that $(A_\tau+1)^{-1}$ is compact: the weak solution map is bounded from $L^2$ to the form domain, and the inclusion of that domain into $L^2$ is compact. Hence $A_\tau$ has compact resolvent.

Here is the functional argument. Given $f\in L^2$, the coercive form

$$
(u,v)\longmapsto q_\tau(u,v)+\langle u,v\rangle
$$

has a unique weak solution $u$ to

$$
q_\tau(u,v)+\langle u,v\rangle=\langle f,v\rangle
$$

for every form-domain vector $v$, and $\|u\|_{H^1}\leq C\|f\|_2$. This solution is $(A_\tau+1)^{-1}f$. Hence the resolvent factors as a bounded map from $L^2$ to the form domain followed by the compact inclusion (10.8). A compact self-adjoint resolvent has nonzero eigenvalues of finite multiplicity tending to zero, which is equivalent to (11.3).

It follows that

$$
L^2_{\mathrm{cusp},\omega}(K_f',\tau)
=\widehat\bigoplus_{\lambda}
E(K_f',\tau,\lambda),
\qquad
E(K_f',\tau,\lambda)=\ker(A_\tau-\lambda),
\tag{11.3}
$$

where every eigenspace is finite-dimensional and the eigenvalues, repeated with multiplicity, tend to infinity.

The eigenvalues have the min--max description

$$
\lambda_j
=\inf_{\substack{V\subset H^1_{\mathrm{cusp},\omega}(K_f',\tau)\\
\dim V=j}}
\ \sup_{0\ne u\in V}\frac{q_\tau(u)}{\|u\|_2^2}.
\tag{11.3a}
$$

Compactness of the embedding guarantees that this infimum is achieved by the span of the first $j$ eigenvectors. The formula shows directly that enlarging the form raises the eigenvalues and that passing to a closed invariant subspace cannot increase the counting function. It also gives another proof that every bounded form-energy subspace is finite-dimensional: otherwise its unit sphere would contain an orthonormal sequence contradicting compactness.

### 11.3 Smoothness and rapid decrease of eigenvectors

A weak eigenvector satisfies

$$
A_\tau u=\lambda u.
$$

Elliptic regularity gains two derivatives. Iteration gives $u\in H^m$ for every $m$, with estimates

$$
\|u\|_{H^{2m}}
\leq C_m(1+\lambda)^m\|u\|_2.
\tag{11.4}
$$

Thus $u$ is a smooth vector. Since it is cuspidal, (10.6) gives rapid decrease with all invariant derivatives.

The regularity estimate is global because the cusp geometry is uniform. On compact truncations use finitely many ordinary elliptic charts. In a high cusp, conjugate the expanding frame back to a fixed compact cylinder; the coefficients and all invariant derivatives are bounded by Section 6.2. A partition in the $t$ direction with uniformly bounded overlap gives an estimate independent of the cylinder. The cuspidal tail estimate then sums the local gains without losing integrability at infinity.

This order of reasoning matters. Compact resolvent produces an $L^2$ eigenvector. Ellipticity makes it smooth. Cuspidality then makes it rapidly decreasing. None of the later properties should be assumed while proving the earlier one.

### 11.4 Finite spectral windows

For $L>0$, the spectral subspace

$$
E_{\leq L}(K_f',\tau)
=\mathbf1_{[1,L]}(A_\tau)
L^2_{\mathrm{cusp},\omega}(K_f',\tau)
\tag{11.5}
$$

is finite-dimensional. Every bounded operator commuting with the level projection, the $K_\infty$ action, and $A_\tau$ preserves this space. A commuting family of normal convolution operators can therefore be simultaneously diagonalized on it.

There is also a polynomial bound

$$
\dim E_{\leq L}(K_f',\tau)
\leq C(1+L)^D.
\tag{11.6}
$$

To prove it, (11.2) bounds the $H^1$ norm on the spectral window by $CL^{1/2}\|u\|_2$. Choose height $Y\asymp L^{n/2}$, equivalently logarithmic depth $T=\log Y\asymp\log L$, so that (10.4) makes the tail smaller than one quarter of the norm. On the truncation, average over coordinate cubes of side $cL^{-1/2}$. If all cube averages vanish, the local Poincare estimate bounds the truncated norm by another quarter of the global norm when $c$ is small. Together with the tail bound this forces $u=0$. Hence the finite-rank averaging map is injective on the spectral window.

The number of cubes grows polynomially in $L$. The cube scale contributes a fixed power of $L^{1/2}$ determined by the real dimension. The truncation has depth $O(\log L)$ and, in the original invariant metric, at most exponential coordinate distortion in that depth; this is another fixed power of $L$. Thus the rank of the averaging map is at most $C(1+L)^D$, proving (11.6). No optimal exponent is claimed.

Finite windows have two immediate analytic consequences. After increasing $D$ if necessary, $(1+A_\tau)^{-s}$ is trace class for every $s>D$, because the polynomial counting bound makes the eigenvalue sum converge. Also $e^{-tA_\tau}$ is trace class for every $t>0$. These assertions remain typewise: their traces need not be summable over all compact types or finite levels.

The window bound can be stated variationally. If $V$ is a subspace on which $q_\tau(u)\leq L\|u\|_2^2$, then $\dim V\leq C(1+L)^D$. This is also the form that bounds the contribution of the irreducible summands found in Chapter 12: every nonzero contribution to one window consumes at least one dimension.

### 11.5 Why compactness is typewise

It would be false to claim that $A_\tau$ has compact resolvent before fixing $\tau$. A central quadratic operator acts by one scalar on an entire infinite-dimensional irreducible representation, giving an infinite-dimensional eigenspace. Adding the compact-direction operator repairs ellipticity, but its eigenvalues grow with the compact type. The correct object is therefore the restriction to one type.

It would also be false to sum blindly over all finite levels. Repeating one bounded spectral window at infinitely many levels destroys compactness. The spectral theorem needed for discreteness fixes level and type first. Summation over them occurs only after each irreducible summand has been identified.

## 12. The discrete cuspidal decomposition

### 12.1 Compact cuspidal convolution

Write $\mathcal H=L^2_{\mathrm{cusp},\omega}$. Let $\mathcal D$ be the convolution algebra of finite sums of functions

$$
f=f_\infty\otimes f_f,
$$

where $f_\infty\in C_c^\infty(G_\infty)$ is finite under left and right translation by $K_\infty$, and $f_f$ is compactly supported, locally constant, and bi-invariant under some compact open subgroup of $G(\mathbf A_f)$. The involution preserves $\mathcal D$.

**Lemma 12.1.** For every $f\in\mathcal D$, the operator $R(f)$ on $\mathcal H$ is compact.

**Proof.** It is enough to treat one tensor. Left invariance of $f_f$ under a compact open $K_f'$ makes the image of $R(f)$ fixed by $K_f'$. Finite-dimensionality of the left $K_\infty$-orbit of $f_\infty$ makes the image lie in a finite sum $\Theta$ of $K_\infty$-types. These assertions follow directly from changing variables in (7.7).

Archimedean differentiation of $R(f)u$ differentiates a left translate of $f_\infty$. Hence, for every invariant differential monomial $D$,

$$
\|D R(f)u\|_2
\leq \|D_Lf_\infty\|_1\,\|f_f\|_1\,\|u\|_2,
\tag{12.1}
$$

with the evident finite sum for a general $f$. Convolution preserves cuspidality by Section 9.3. Thus $R(f)$ factors as a bounded map

$$
\mathcal H\longrightarrow
H^1_{\mathrm{cusp},\omega}(K_f',\Theta)
$$

followed by inclusion into $\mathcal H$. The latter inclusion is compact because $\Theta$ is finite and Theorem 10.1 applies to each of its types. Therefore $R(f)$ is compact. $\square$

This lemma packages the entire geometric argument into a representation-theoretic statement: every smooth, finite-level, finite-type convolution operator is compact on the whole cuspidal space, even though no unrestricted Sobolev embedding is compact.

The algebra $\mathcal D$ is dense in $L^1(G(\mathbf A))$. At the finite places, locally constant compactly supported functions are dense. At infinity, smooth compactly supported functions are dense, and convolution on the left and right by finite Peter--Weyl sums on $K_\infty$ approximates them in $L^1$. These approximations may be chosen inside a fixed compact enlargement of the original support. In particular, $\mathcal D$ contains an $L^1$ approximate identity $(\eta_j)$ for which

$$
R(\eta_j)u\longrightarrow u
\qquad(u\in\mathcal H).
\tag{12.2}
$$

### 12.2 The compact-operator decomposition

Let

$$
\mathfrak A
=\overline{R(\mathcal D)}^{\|\cdot\|}
\subset B(\mathcal H).
$$

Lemma 12.1 and norm-closedness of the compact operators give

$$
\mathfrak A\subset\mathcal K(\mathcal H).
\tag{12.3}
$$

The action is nondegenerate by (12.2), and $\mathfrak A$ is separable because the group is second countable. We use the following elementary compact-operator structure lemma.

**Lemma 12.2.** Let $A$ be a separable $C^*$-algebra acting nondegenerately on a separable Hilbert space $H$. If $A\subset\mathcal K(H)$, then there are countably many pairwise inequivalent irreducible nondegenerate representations $\pi$ and finite-dimensional multiplicity spaces $M_\pi$ such that

$$
H\simeq\widehat\bigoplus_\pi M_\pi\otimes H_\pi,
\qquad
A\text{ acts as }
\widehat\bigoplus_\pi I_{M_\pi}\otimes\pi(A).
\tag{12.4}
$$

**Proof.** If $0\ne a\in A$ is positive, compactness gives an isolated nonzero part of its spectrum. Continuous functional calculus with a function vanishing at zero produces a nonzero finite-rank projection in $A$. A minimal projection exists in the resulting finite-dimensional corner. Group mutually equivalent minimal projections and use the partial isometries between them as matrix units. Their closed spans are mutually orthogonal elementary ideals, each isomorphic to the compact operators on one irreducible module. A maximal family has zero annihilator; otherwise the same construction in the annihilator would produce another minimal projection. Nondegeneracy therefore makes the corresponding modules span $H$.

Separability makes the family countable. In a representation of one elementary ideal, the action has the form $I_M\otimes\mathcal K(H_0)$. If $M$ were infinite-dimensional, $I_M\otimes b$ would fail to be compact for every nonzero finite-rank $b$. Hence each multiplicity space is finite-dimensional. Finally, compactness of every element forces the norms of its components to tend to zero, giving the Hilbert direct sum in (12.4). $\square$

Apply Lemma 12.2 to $\mathfrak A$. Since $\mathcal D$ is $L^1$-dense, $\mathfrak A$ is also the norm closure of the integrated right action of $L^1(G(\mathbf A))$. A closed subspace is invariant under $\mathfrak A$ if and only if it is invariant under $G(\mathbf A)$. One direction follows by integration. For the other, if $V$ is $\mathfrak A$-invariant and $v\in V$, then a left translate of the approximate identity gives

$$
R(L_g\eta_j)v\longrightarrow R(g)v;
$$

every vector on the left belongs to $V$, so $R(g)v\in V$. Thus irreducibility and equivalence for the $\mathfrak A$-modules are exactly irreducibility and equivalence for the corresponding unitary group representations.

Every summand has central character $\omega$, because the center already acts by that scalar on $\mathcal H$. Consequently (12.4) becomes

$$
L^2_{\mathrm{cusp},\omega}
\simeq
\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
M_\pi\otimes\mathcal H_\pi,
\tag{12.5}
$$

where the index set is countable, every $\mathcal H_\pi$ is irreducible and unitary, and $1\leq\dim M_\pi<\infty$. This proves discreteness and finite multiplicity without assuming a direct-integral theorem, a type-I theorem for the adelic group, or a restricted-tensor-product classification.

### 12.3 Finite multiplicity

The compact-operator lemma already proves finite multiplicity. The elliptic windows give an independent bound and explain how multiplicity is detected geometrically.

Let $\pi$ be a summand in (12.5). Strong continuity at the finite places and compact Fourier completeness at infinity give $K_f'$ and $\tau$ such that

$$
V_{\pi,K_f',\tau}
=\mathcal H_\pi^{K_f'}(\tau)\ne0.
$$

The spectral projections of the central archimedean quadratic operator commute with the group action. Irreducibility and the spectral form of Schur's lemma therefore make that operator scalar on $\mathcal H_\pi$; the compact quadratic operator is scalar on the $\tau$-isotypic component. Their sum has one value $\lambda$ on $V_{\pi,K_f',\tau}$. Hence

$$
M_\pi\otimes V_{\pi,K_f',\tau}
\subset E(K_f',\tau,\lambda).
$$

By (11.3), the space on the right is finite-dimensional. It follows simultaneously that $V_{\pi,K_f',\tau}$ and $M_\pi$ are finite-dimensional, and

$$
\dim M_\pi
\leq\frac{\dim E(K_f',\tau,\lambda)}
{\dim V_{\pi,K_f',\tau}}
<\infty.
\tag{12.6}
$$

This is finite automorphic multiplicity. It does not say that $\mathcal H_\pi$ is finite-dimensional; archimedean irreducible representations are usually infinite-dimensional.

The same argument rules out an infinite-dimensional multiplicity even though the irreducible representation itself can be infinite-dimensional. Every vector in $M_\pi$ tensored with one fixed nonzero type vector lies in the same global eigenspace. The dimension of that eigenspace controls multiplicity.

Conversely, finite-dimensional type spaces alone would not prove finite automorphic multiplicity. One could tensor a fixed irreducible representation with an infinite multiplicity space and retain finite-dimensional intrinsic type spaces. The global compact-resolvent theorem excludes exactly this possibility by bounding the entire automorphic eigenspace.

More generally, every bounded spectral projection of $A_\tau$ preserves the orthogonal sum (12.5), and

$$
E_I(K_f',\tau)
=\widehat\bigoplus_\pi
M_\pi\otimes V_{\pi,K_f',\tau,I}
$$

for a bounded interval $I$. Since the left side is finite-dimensional, only finitely many summands on the right are nonzero, and

$$
\dim E_I(K_f',\tau)
=\sum_\pi
\dim M_\pi\,\dim V_{\pi,K_f',\tau,I}.
$$

This proves the counted finite-window assertion in Theorem 12.1. It also completes the regularity interface: a finite-level, finite-type vector in one irreducible summand lies in the scalar eigenspace described above, so Section 11.3 makes it smooth and Section 10.3 makes it rapidly decreasing.

### 12.4 The decomposition theorem

**Theorem 12.1 (discrete cuspidal spectrum of $\mathrm{GL}_2$).** Let $F$ be a number field and let $\omega:F^\times\backslash\mathbf A_F^\times\to\mathbf C^\times$ be unitary. Give $Z(\mathbf A_F)G(F)\backslash G(\mathbf A_F)$ the quotient measure determined by the local choices of Chapter 2. Then:

1. $L^2_{\mathrm{cusp},\omega}$ is a closed $G(\mathbf A_F)$-invariant subspace of $L^2_\omega$.
2. It decomposes as

   $$
   L^2_{\mathrm{cusp},\omega}
   \simeq
   \widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
   m(\pi)\mathcal H_\pi,
   \tag{12.7}
   $$

   where the index set is countable, every $\mathcal H_\pi$ is irreducible and unitary with central character $\omega$, and

   $$
   1\leq m(\pi)<\infty.
   $$

3. For every compact open $K_f'$, every $K_\infty$-type $\tau$, and every bounded elliptic spectral interval, only finitely many summands contribute, counted with the dimensions of their type spaces and their multiplicities.
4. Every finite-level, finite-type vector in a summand is smooth and rapidly decreasing in every cusp.

**Proof.** Closedness and invariance are Theorem 9.1 and Section 9.3. Compactness of finite-type convolution and Lemma 12.2 give the direct sum with finite multiplicities. Typewise compact resolvent and finite spectral windows are Chapter 11, while elliptic regularity plus cuspidal decay gives the last assertion. $\square$

Orthogonality in (12.7) is Hilbert-space orthogonality. Distinct irreducible equivalence classes occupy orthogonal isotypic summands, and the $m(\pi)$ copies inside one isotypic summand are encoded by an orthonormal basis of $M_\pi$. The sum is complete because the nondegenerate compact-operator algebra acts on the whole closed cuspidal subspace.

The theorem is stable under changing among the two central realizations. On $[G]^1$, first apply (7.6). Each character subspace corresponds to a unitary idele class character after a choice of extension across the module direction, and the extension affects only the removed scalar action. The geometric height, cuspidality, compact embedding, and multiplicities are unchanged.

The same theorem on $[G]^1$ decomposes first by the compact center as in (7.6) and then applies (12.7) to each central character.

### 12.5 Consequences and boundaries

The theorem supplies the exact spectral input needed for later automorphic representation theory: a genuine discrete Hilbert sum, finite multiplicities, finite-dimensional typewise spectral windows, and rapidly decreasing smooth vectors.

It does not prove multiplicity one. Finite multiplicity is an analytic compactness conclusion; multiplicity one needs global uniqueness arguments of a different kind.

It does not classify the orthogonal complement of the cuspidal space. The constant-term channel exhibited in Section 10.6 can support continuous spectrum, and residues can create additional discrete noncuspidal terms. Their construction and classification require the theory of Eisenstein series.

It also does not assert global compact resolvent on the unrestricted cuspidal representation. The correct compactness is the fixed-level, fixed-type statement used in the proof.

Several finiteness conclusions should be distinguished.

1. At fixed level, there are finitely many cusps. This is arithmetic reduction at the finite places.
2. At fixed level, type, and bounded elliptic window, the spectral space is finite-dimensional. This is analytic compactness.
3. In the whole fixed-central-character cuspidal space, the set of irreducible summands is countable. This follows by exhausting with countably many levels, types, and windows.
4. For each fixed irreducible summand, its multiplicity space is finite-dimensional. This follows by placing one of its nonzero type vectors inside a finite global eigenspace.

None of these statements gives a uniform bound as level, type, field, or central character varies. Such uniformity would require additional arithmetic estimates. The theorem instead gives the exact qualitative finiteness needed for a discrete spectral expansion at each fixed datum.

The reduction and spectral halves also have different dependence on the central character. The geometry of the quotient, the height, and the cusp-volume constants do not depend on $\omega$. Unitarity of $\omega$ ensures that absolute values descend and that the right action is unitary. Once this is imposed, the compactness proof is identical in every central-character space; only the eventual list of irreducible summands changes.

## 13. Synthesis of the reduction and spectral arguments

### 13.1 The complete implication chain

The proof can now be read as one sequence in which every arrow has a distinct source:

$$
\begin{aligned}
&F\backslash\mathbf A\text{ compact}
+F^\times\backslash\mathbf A^1\text{ compact}
+\text{adelic short vectors}\\
&\hspace{25mm}\Longrightarrow
\text{Siegel covering and high-cusp uniqueness},\\[2mm]
&\text{Iwasawa Jacobian }H^{-1}
+d^\times H=\frac{dH}{H}\\
&\hspace{25mm}\Longrightarrow
\text{cusp measure }\frac{dH}{H^2}
\Longrightarrow\text{finite volume},\\[2mm]
&\text{zero unipotent average}
+\text{transverse expansion }H^{1/n}\\
&\hspace{25mm}\Longrightarrow
\text{uniform cusp tails},\\[2mm]
&\text{uniform tails}
+\text{Rellich compactness on truncations}\\
&\hspace{25mm}\Longrightarrow
\text{compact cuspidal Sobolev embedding},\\[2mm]
&\text{compact embedding}
+\text{ellipticity}\\
&\hspace{25mm}\Longrightarrow
\text{typewise compact resolvent and finite windows},\\[2mm]
&\text{compact finite-type convolution}
+\text{compact-operator structure}\\
&\hspace{25mm}\Longrightarrow
\text{discrete cuspidal spectrum with finite multiplicities}.
\end{aligned}
\tag{13.1}
$$

No arrow can be replaced by the conclusion of the preceding line alone. Finite volume does not give uniform tails; uniform tails do not give regularity; ellipticity does not prevent escape; and compact convolution is obtained only after smoothing has been confined to finitely many levels and compact types.

### 13.2 A normalization ledger

| Feature | Convention |
|---|---|
| Finite absolute value | $|\varpi_v|_v=q_v^{-1}$ |
| Complex absolute value | Square of the usual modulus |
| Additive finite measure | $\operatorname{vol}(\mathcal O_v)=1$ |
| Additive adelic covolume | $\operatorname{vol}(F\backslash\mathbf A)=2^{-r_2}|d_F|^{1/2}$ |
| Unipotent quotient measure | Probability measure $d\bar x=c_F^{-1}dx$ |
| Finite multiplicative measure | $\operatorname{vol}(\mathcal O_v^\times)=1$ |
| Maximal compact measure | Probability Haar measure |
| Borel modular character | $\delta_B(\operatorname{diag}(a,d))=|a/d|_{\mathbf A}$ |
| Height | $H_B=|a/d|_{\mathbf A}$ |
| Cusp measure | Bounded compact factor times $dH/H^2$ |
| Central transformation | $\phi(zg)=\omega(z)\phi(g)$ |
| Constant term | Probability average over $F\backslash\mathbf A$ |
| Cuspidality | Constant term zero at every right translate |
| Compactness claim | Fixed finite level and fixed $K_\infty$-type |

Changing one Haar normalization rescales quotient volumes and constant-term norms but does not change zero constant terms or the abstract representation. Every numerical volume statement in this book refers to the ledger above.

### 13.3 Failure modes and their repairs

Several plausible shortcuts are false.

**Keeping the full determinant module.** Then $G(F)\backslash G(\mathbf A)$ maps onto $\mathbf R_{>0}$ with measure $dr/r$, so its volume is infinite. Passing to $G(\mathbf A)^1$ or quotienting by $Z(\mathbf A)$ repairs the problem.

**Using finite volume as compactness.** Constant-mode bumps (10.9) escape with bounded energy. Vanishing constant terms supplies the missing tail estimate.

**Defining the $L^2$ constant term as one global bounded map.** Its natural target has a different modular measure. Bounded averaging on a countable exhaustion of cusp charts gives the correct closedness proof.

**Checking one cusp point only.** The resulting condition is not stable under right translation. Requiring every $g$, or equivalently every translated local average, makes the cuspidal space invariant.

**Claiming unrestricted compact resolvent.** One irreducible representation can be infinite-dimensional at one central eigenvalue. Fixing compact type and adding compact-direction energy produces finite-dimensional windows.

**Confusing finite multiplicity with finite dimension.** The multiplicity space $M_\pi$ is finite; the irreducible factor $\mathcal H_\pi$ generally is not.

**Inferring multiplicity one from compactness.** Compactness proves $m(\pi)<\infty$, not $m(\pi)=1$.

These counterexamples are not peripheral. Each identifies the exact hypothesis used by the correct theorem.

### 13.4 Conclusion

Reduction theory turns an adelic quotient from an abstract double coset into a space with one measurable direction of escape. The additive quotient confines the unipotent coordinate, the norm-one idele class group confines the torus directions orthogonal to height, and an adelic short vector chooses a rational line. What remains is a one-dimensional height ray. Its Iwasawa Jacobian is $dH/H^2$, yielding finite volume and exact cusp-tail volume.

Cuspidality responds to the same geometry. The constant term is the transverse zero mode along the rational line selected by the cusp. Removing it forces oscillation on a compact unipotent quotient. Balanced torus expansion magnifies that oscillation by at least $H^{1/[F:\mathbf Q]}$, so bounded Sobolev energy cannot move indefinitely outward. Compactness on truncations and uniform smallness of the tails then give a compact embedding on every finite level and compact type.

The final spectral conclusion is consequently geometric before it is representation-theoretic. Compact embedding makes every smooth finite-type convolution operator compact; the resulting compact-operator algebra gives a discrete irreducible sum with finite multiplicities. Typewise compact resolvent supplies finite spectral windows and regularity. Every smooth finite-type cuspidal vector is automatically rapidly decreasing. The cuspidal spectrum of $\mathrm{GL}_2$ is therefore a discrete countable collection of irreducible unitary representations, each repeated only finitely many times, while the omitted constant-term channel remains available for the noncuspidal spectrum that lies beyond this book.
