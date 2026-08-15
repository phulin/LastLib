# Global Constant Terms and Eisenstein Contributions for $\mathrm{GL}_2$

## Contents

1. [The missing half of the automorphic quotient](#1-the-missing-half-of-the-automorphic-quotient)
   - [Why constant terms require their own theory](#11-why-constant-terms-require-their-own-theory)
   - [Standing notation](#12-standing-notation)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [The range and the boundary of the book](#14-the-range-and-the-boundary-of-the-book)
2. [Global parabolic constant terms](#2-global-parabolic-constant-terms)
   - [Averaging over the unipotent quotient](#21-averaging-over-the-unipotent-quotient)
   - [Covariance under the Borel subgroup](#22-covariance-under-the-borel-subgroup)
   - [Constant terms and right convolution](#23-constant-terms-and-right-convolution)
   - [Examples, nonexamples, and the rank-one simplification](#24-examples-nonexamples-and-the-rank-one-simplification)
3. [Normalized inducing data](#3-normalized-inducing-data)
   - [Why the half-density is indispensable](#31-why-the-half-density-is-indispensable)
   - [Global sections and the compact picture](#32-global-sections-and-the-compact-picture)
   - [Local sections and restricted tensor products](#33-local-sections-and-restricted-tensor-products)
   - [The unitary axis and contragredient pairing](#34-the-unitary-axis-and-contragredient-pairing)
4. [Rank-one Eisenstein series in the convergence chamber](#4-rank-one-eisenstein-series-in-the-convergence-chamber)
   - [Definition and the geometric meaning of the sum](#41-definition-and-the-geometric-meaning-of-the-sum)
   - [Absolute convergence](#42-absolute-convergence)
   - [Uniform convergence and differentiation](#43-uniform-convergence-and-differentiation)
   - [A rational example and the sharp boundary](#44-a-rational-example-and-the-sharp-boundary)
5. [Unfolding the constant term](#5-unfolding-the-constant-term)
   - [The two Bruhat cells](#51-the-two-bruhat-cells)
   - [The global intertwining integral](#52-the-global-intertwining-integral)
   - [The constant-term formula](#53-the-constant-term-formula)
   - [Why there are exactly two exponents](#54-why-there-are-exactly-two-exponents)
6. [Local intertwining operators](#6-local-intertwining-operators)
   - [Definition and convergence](#61-definition-and-convergence)
   - [Covariance and the reflected induced representation](#62-covariance-and-the-reflected-induced-representation)
   - [The nonarchimedean spherical calculation](#63-the-nonarchimedean-spherical-calculation)
   - [Ramified and archimedean sections](#64-ramified-and-archimedean-sections)
7. [The global operator as a product of local operators](#7-the-global-operator-as-a-product-of-local-operators)
   - [Factorization in the convergence chamber](#71-factorization-in-the-convergence-chamber)
   - [The completed scalar and the finite correction](#72-the-completed-scalar-and-the-finite-correction)
   - [Normalization of the operator](#73-normalization-of-the-operator)
   - [A normalization audit](#74-a-normalization-audit)
8. [Continuation in the required strip](#8-continuation-in-the-required-strip)
   - [Truncation isolates the constant term](#81-truncation-isolates-the-constant-term)
   - [Meromorphic continuation to the closed right half-plane](#82-meromorphic-continuation-to-the-closed-right-half-plane)
   - [The functional equation](#83-the-functional-equation)
   - [Regularity and unitarity on the imaginary axis](#84-regularity-and-unitarity-on-the-imaginary-axis)
9. [Poles and residues](#9-poles-and-residues)
   - [The character-theoretic pole criterion](#91-the-character-theoretic-pole-criterion)
   - [The residue is one-dimensional](#92-the-residue-is-one-dimensional)
   - [Square integrability of the residue](#93-square-integrability-of-the-residue)
   - [What does not produce a residual term](#94-what-does-not-produce-a-residual-term)
10. [Pseudo-Eisenstein series and wave packets](#10-pseudo-eisenstein-series-and-wave-packets)

- [Incomplete data on the Borel quotient](#101-incomplete-data-on-the-borel-quotient)
- [Mellin inversion along height](#102-mellin-inversion-along-height)
- [Moving the contour](#103-moving-the-contour)
- [The elementary Maass--Selberg identity](#104-the-elementary-maass--selberg-identity)

11. [Classification of the noncuspidal contributions](#11-classification-of-the-noncuspidal-contributions)

- [The constant-term channel](#111-the-constant-term-channel)
- [Continuous and residual terms](#112-continuous-and-residual-terms)
- [The classification theorem in the required range](#113-the-classification-theorem-in-the-required-range)
- [Why no general spectral measure is needed](#114-why-no-general-spectral-measure-is-needed)

12. [Cuspidal local test functions](#12-cuspidal-local-test-functions)

- [The operator-level vanishing condition](#121-the-operator-level-vanishing-condition)
- [Nonarchimedean supercuspidal coefficients](#122-nonarchimedean-supercuspidal-coefficients)
- [Archimedean discrete-series coefficients](#123-archimedean-discrete-series-coefficients)
- [The weaker trace-level condition](#124-the-weaker-trace-level-condition)

13. [Annihilation of every noncuspidal contribution](#13-annihilation-of-every-noncuspidal-contribution)

- [Factorizable global tests](#131-factorizable-global-tests)
- [Vanishing on Eisenstein series and wave packets](#132-vanishing-on-eisenstein-series-and-wave-packets)
- [Vanishing on residues](#133-vanishing-on-residues)
- [The cuspidal-test theorem](#134-the-cuspidal-test-theorem)

14. [Consequences, failure modes, and final synthesis](#14-consequences-failure-modes-and-final-synthesis)

- [Consequences for later trace arguments](#141-consequences-for-later-trace-arguments)
- [Failure modes and their corrections](#142-failure-modes-and-their-corrections)
- [The complete implication chain](#143-the-complete-implication-chain)
- [Conclusion](#144-conclusion)

## 1. The missing half of the automorphic quotient

### 1.1 Why constant terms require their own theory

Reduction theory reveals a single direction in which the central quotient of the global $\mathrm{GL}_2$ quotient can escape. Cuspidality removes the average along the compact unipotent cross-section and thereby closes that escape channel. The cuspidal subspace consequently has a discrete spectral theory. The complementary channel is not an error term. It carries coherent families of automorphic functions parametrized by one complex variable, and isolated poles of those families can leave square-integrable residues.

This book studies that complementary channel at exactly the depth required later. The central construction is the rank-one Eisenstein series. Its constant term has two pieces: the inducing section and its image under a global intertwining operator. The operator itself factors into local integrals, and its unramified factors are ratios of completed Hecke functions. Those ratios control convergence, continuation, the functional equation, and every residue in the half-plane that will be crossed.

There is a second goal. Later trace arguments use test functions chosen to be cuspidal at one place. Such a choice should remove the entire noncuspidal contribution, not merely the constant function. We prove this directly. A suitable local factor acts by zero on every relevant induced representation; factorization then kills Eisenstein series, their wave packets, and their residues. This argument is stronger and cleaner than constructing a general spectral decomposition of the full automorphic space.

The rank-one setting is unusually transparent. The rational Bruhat decomposition has two cells, so an Eisenstein constant term has two summands. There is one complex parameter, one reflection $s\mapsto-s$, and one possible residual mechanism. Every decisive step can therefore be proved by direct summation, integration, Mellin inversion, and the analytic theory of one-dimensional Hecke functions.

### 1.2 Standing notation

Let $F$ be a number field, $\mathbf A=\mathbf A_F$, and

$$
G=\mathrm{GL}_2,
\qquad
B=TN,
\qquad
N=\left\{n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}\right\}.
$$

Write

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

For $t=\operatorname{diag}(a,d)$ put

$$
\alpha(t)=a/d,
\qquad
\delta_B(t)=|a/d|_{\mathbf A}.
$$

The center is $Z$. We work at a fixed unitary central character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
$$

Automorphic functions satisfy $\phi(zg)=\omega(z)\phi(g)$. Their square norm is taken on

$$
Z(\mathbf A)G(F)\backslash G(\mathbf A).
$$

At a finite place $v$, the normalized absolute value satisfies $|\varpi_v|_v=q_v^{-1}$. At a complex place it is the square of the ordinary modulus. All idele class characters called unitary have absolute value one.

Choose two unitary idele class characters $\chi_1,\chi_2$ with

$$
\chi_1\chi_2=\omega,
\qquad
\mu=\chi_1\chi_2^{-1}.
\tag{1.1}
$$

The ordered pair $\chi=(\chi_1,\chi_2)$ is an inducing datum. Its reflection is

$$
w\chi=(\chi_2,\chi_1).
$$

The parameter $s$ will always be normalized so that the unitary axis is $\operatorname{Re}(s)=0$ and the initial convergence chamber is $\operatorname{Re}(s)>1/2$.

### 1.3 The normalization ledger

The additive character is the standard trace character

$$
\psi_F(x)=\psi_{\mathbf Q}(\operatorname{Tr}_{F/\mathbf Q}^{\mathbf A}x),
$$

with positive Fourier phase. Let $dx_v$ be self-dual for $\psi_v$, and put $dx=\prod_vdx_v$. Then

$$
\operatorname{vol}_{dx}(F\backslash\mathbf A)=1.
\tag{1.2}
$$

This is also the probability measure used for the global unipotent quotient in reduction theory. Indeed, the earlier finite-place measures of integer-ring volume one, together with ordinary archimedean measures, give covolume $2^{-r_2}|d_F|^{1/2}$. Passing to self-dual finite measures and doubling ordinary area at each complex place rescales the product by its reciprocal. Thus the two descriptions give the same probability measure on $F\backslash\mathbf A$.

This identity has an important consequence. The global intertwining integral uses the literal restricted product $dx=\prod_vdx_v$, while the automorphic constant term uses probability measure on $F\backslash\mathbf A$; no additional discriminant or covolume scalar separates them.

Give every maximal compact subgroup $K_v$ probability measure and write $K=\prod_vK_v$. Haar measure on $G(F_v)$ is normalized by Iwasawa integration:

$$
dg_v=\delta_B(t)^{-1}\,dn_v\,d^\times a_v\,d^\times d_v\,dk_v
$$

when $g_v=n(x_v)\operatorname{diag}(a_v,d_v)k_v$. The multiplicative measure has $\operatorname{vol}(\mathcal O_v^\times)=1$ at finite places. Quotient measures are always the ones induced by iterated integration.

Disintegrate the measure on $F^\times\backslash\mathbf A^\times$ as

$$
d^\times\bar y=\kappa_F\,du\,\frac{dH}{H},
\qquad H=|y|_{\mathbf A},
\tag{1.3}
$$

where $du$ is probability measure on $C_F^1=F^\times\backslash\mathbf A^1$. The positive constant $\kappa_F$ is fixed by the preceding local measures. Whenever a compact cross-section pairing occurs below, it includes this factor; it is never silently reset to one.

For a unitary idele class character $\nu$, write

$$
\Lambda(s,\nu)=\prod_vL_v(s,\nu_v)
\tag{1.4}
$$

for the completed Hecke function with the local factors and archimedean gamma factors fixed by the preceding harmonic analysis. It is entire unless $\nu$ is a pure module character; in that exceptional case it is a translate of the completed Dedekind zeta function and has two simple poles. Its functional equation and vertical-strip bounds are available with the same additive characters and self-dual measures.

### 1.4 The range and the boundary of the book

We prove absolute convergence for $\operatorname{Re}(s)>1/2$, continuation across the closed strip $0\leq\operatorname{Re}(s)\leq1/2$, the reflection equation, regularity on the imaginary axis, and the residues crossed in moving from the convergence chamber to that axis. This is the required range for classifying the continuous and residual terms entering later cuspidal trace kernels.

We do not construct a general spectral measure for the full automorphic quotient. We also do not seek optimal bounds in arbitrary vertical strips, a many-parabolic truncation theory, or higher-rank residual classifications. None of those is needed for the rank-one annihilation theorem.

The proof inputs are equally bounded. The preceding adelic harmonic analysis supplies
self-dual Fourier transform, Poisson summation, Tate integrals, completed Hecke functions, and
their functional equations. Reduction theory supplies finite-volume central quotients, reduced
cusp charts, high-cusp uniqueness, constant-term averaging, and the closed discrete cuspidal
subspace. The local coefficient examples in Chapter 12 use only the already established
rank-one facts that supercuspidals have compact-mod-center coefficients and zero Jacquet module,
and that real discrete-series coefficients are square-integrable with their explicit radial
exponents. Continuation, residue classification, pseudo-Eisenstein exhaustion, and global
noncuspidal annihilation are proved here; no later trace formula or global Plancherel theorem is
used.

The main conclusions will be these:

1. every noncuspidal family in the required range is a rank-one Eisenstein family induced from two idele class characters;
2. its only square-integrable residue is a one-dimensional character $g\mapsto\eta(\det g)$;
3. a factorizable global test with one strongly cuspidal local factor acts by zero on all continuous and residual terms.

The hypotheses in the third assertion matter. Mere compact support, total integral zero, or orthogonality to constants is insufficient. The local factor must remove the entire parabolic channel.

## 2. Global parabolic constant terms

### 2.1 Averaging over the unipotent quotient

The global quotient becomes noncompact when a rational line becomes short. The group stabilizing that line is a Borel subgroup, and the compact cross-section normal to the height direction is $N(F)\backslash N(\mathbf A)$. Averaging over that cross-section extracts the mode that can travel to infinity without transverse oscillation.

For a continuous automorphic function $\phi$ define

$$
\phi_N(g)
=\int_{F\backslash\mathbf A}\phi(n(x)g)\,dx.
\tag{2.1}
$$

The quotient is compact and has mass one, so the integral is defined whenever $\phi$ is continuous. For an automorphic $L^2$ class it is defined almost everywhere on every truncated cusp chart by Fubini. All pointwise arguments below are first made for smooth functions of moderate growth and then extended where needed by local $L^2$ continuity.

The definition solves two problems at once. It descends because $n(q)$ with $q\in F$ acts trivially on the left, and it is normalized without an arbitrary scalar. If one used $\mathbf A$ rather than $F\backslash\mathbf A$, the integral would diverge even for a constant function. If one integrated over a local unipotent subgroup only, the result would not detect the global cusp.

Fourier expansion on the compact additive quotient gives

$$
\phi(n(x)g)\sim\sum_{\xi\in F}W_\xi(g)\psi_F(\xi x),
$$

where

$$
W_\xi(g)=\int_{F\backslash\mathbf A}
\phi(n(x)g)\overline{\psi_F(\xi x)}\,dx.
$$

The constant term is $W_0$. Thus cuspidality removes one Fourier mode on every unipotent fiber, not every Fourier coefficient.

### 2.2 Covariance under the Borel subgroup

The constant term is left invariant under $N(\mathbf A)$:

$$
\phi_N(n(u)g)=\phi_N(g).
\tag{2.2}
$$

It is also invariant under $T(F)$. If $t=\operatorname{diag}(a,d)\in T(F)$, conjugation sends $n(x)$ to $n((a/d)x)$. Multiplication by $a/d\in F^\times$ preserves $F\backslash\mathbf A$ and its probability measure, by the product formula. Hence

$$
\phi_N(tg)=\phi_N(g).
\tag{2.3}
$$

For an adelic diagonal element $t=\operatorname{diag}(a,d)$ there is no corresponding invariance. A change of variables gives

$$
\phi_N(tg)
=\int_{F\backslash\mathbf A}
\phi(n(x)tg)\,dx,
$$

and the dependence on $t$ contains the spectral data. Pretending that (2.3) holds adelically would erase the very height variable that Eisenstein series describe.

The center behaves as expected:

$$
\phi_N(zg)=\omega(z)\phi_N(g).
\tag{2.4}
$$

Finally, constant terms commute with right translation:

$$
(R(h)\phi)_N(g)=\phi_N(gh).
\tag{2.5}
$$

This identity explains why cuspidality must mean vanishing at every argument. Checking only $\phi_N(1)$ would not produce an invariant subspace.

### 2.3 Constant terms and right convolution

Let $f$ be an integrable test function on $G(\mathbf A)$, compactly supported modulo the center and transforming under the center so that right convolution preserves central character $\omega$. Put

$$
R(f)\phi(g)=\int_{Z(\mathbf A)\backslash G(\mathbf A)}
f(h)\phi(gh)\,dh.
\tag{2.6}
$$

Whenever absolute convergence permits Fubini,

$$
(R(f)\phi)_N(g)
=\int f(h)\phi_N(gh)\,dh
=R(f)(\phi_N)(g).
\tag{2.7}
$$

For smooth compactly supported $f$, the identity extends to $L^2$ by local boundedness of unipotent averaging and boundedness of convolution. Thus right convolution preserves cusp forms, but it does not generally make a noncuspidal function cuspidal.

There is a different constant term attached to a local test function, introduced in Chapter 12. It controls the action of $f$ on induced representations. Confusing the automorphic constant term (2.1) with the parabolic transform of a test function is a frequent source of incomplete vanishing arguments. The former diagnoses an automorphic vector; the latter diagnoses an operator.

### 2.4 Examples, nonexamples, and the rank-one simplification

The constant function has constant term one. A function of height alone has the same function as its constant term, even if its total integral is zero. Compact support on the quotient also does not imply cuspidality: a compactly supported function can have a nonzero average on every unipotent fiber it meets.

For the classical upper half-plane, a Fourier expansion

$$
\phi(x+iy)=\sum_{m\in\mathbf Z}a_m(y)e^{2\pi imx}
$$

has constant term $a_0(y)$. At a level with several cusps, vanishing in the standard cusp alone is insufficient. The adelic condition $\phi_N(g)=0$ for every $g$ includes every cusp class automatically.

Every proper parabolic subgroup of $G$ defined over $F$ stabilizes an $F$-rational line, and all such lines are conjugate under $G(F)$. Hence every proper parabolic is rationally conjugate to $B$. Vanishing of (2.1) at every right translate is therefore equivalent to vanishing along every proper rational parabolic. This is the decisive rank-one simplification: there is one constant-term channel, though it appears at finitely many cusp classes after a finite level is fixed.

## 3. Normalized inducing data

### 3.1 Why the half-density is indispensable

A function on $B(F)\backslash G(\mathbf A)$ becomes an automorphic function after summing its rational translates. To organize such functions by characters, one prescribes their transformation under $T(\mathbf A)$. The modular character must enter with exponent $1/2$. This half-density makes the reflection $s\mapsto-s$ symmetric and places unitary induction on the imaginary axis.

For $s\in\mathbf C$, define $I(\chi,s)$ to be the space of smooth functions $f_s:G(\mathbf A)\to\mathbf C$ satisfying

$$
f_s\!\left(n(x)\begin{pmatrix}a&0\\0&d\end{pmatrix}g\right)
=\chi_1(a)\chi_2(d)
\left|\frac ad\right|_{\mathbf A}^{s+1/2}f_s(g).
\tag{3.1}
$$

The characters are trivial on $F^\times$, so $f_s$ is left $B(F)$-invariant. Its central character is $\chi_1\chi_2=\omega$.

Had we omitted $1/2$, the unitary axis would be shifted, the standard intertwining operator would reflect $s$ about $1/2$, and the unramified factor would acquire displaced arguments. The normalization (3.1) makes all three structures agree.

### 3.2 Global sections and the compact picture

Iwasawa decomposition gives $G(\mathbf A)=B(\mathbf A)K$. Thus a section is determined by its restriction to $K$, subject to the compact intersection relation. A standard section is a family $s\mapsto f_s$ whose restriction to $K$ is independent of $s$. If $g=bk$, define

$$
f_s(g)=\chi_1(a)\chi_2(d)|a/d|^{s+1/2}f(k)
$$

for $b=n(x)\operatorname{diag}(a,d)$. Compatibility with $B(\mathbf A)\cap K$ is the only condition on $f$.

The compact picture is useful because holomorphy in $s$ is explicit: the parameter appears only through $|a/d|^s$. Derivatives introduce powers of $\log|a/d|$, which reduction-theoretic estimates can absorb on compact vertical strips.

We use finite sums of factorizable standard sections. This class is stable under right translation, differentiation at archimedean places, and the local intertwining operations below. It is large enough for every wave packet and test-function argument in this book.

### 3.3 Local sections and restricted tensor products

For each place $v$, let $I_v(\chi_v,s)$ be the corresponding normalized local induced representation:

$$
f_{v,s}\!\left(n(x)\begin{pmatrix}a&0\\0&d\end{pmatrix}g\right)
=\chi_{1,v}(a)\chi_{2,v}(d)
|a/d|_v^{s+1/2}f_{v,s}(g).
\tag{3.2}
$$

At almost every finite place, both characters are unramified. There is then a unique $K_v$-fixed section $f_{v,s}^0$ with

$$
f_{v,s}^0(1)=1.
\tag{3.3}
$$

A factorizable global section has the form

$$
f_s=\bigotimes_v f_{v,s},
\qquad
f_{v,s}=f_{v,s}^0
\text{ for almost every }v.
\tag{3.4}
$$

The restricted tensor product is essential. Without the normalized spherical vector at almost every place, neither the global section nor the product of local intertwining integrals would have a canonical tail.

### 3.4 The unitary axis and contragredient pairing

For $s=it$, the character multiplying the first diagonal entry is $\chi_1|\cdot|^{it}$ and that multiplying the second is $\chi_2|\cdot|^{-it}$. Both are unitary. The compact-picture norm

$$
\|f_{it}\|^2=\int_K|f_{it}(k)|^2\,dk
\tag{3.5}
$$

is therefore invariant under the local or global group action. This is why $\operatorname{Re}(s)=0$ is the continuous spectral axis.

There are two operations here, and they should not be conflated. The Hermitian dual of
$I(\chi,s)$ is obtained by conjugating the characters and the parameter. The Weyl operator,
on the other hand, maps $I(\chi,s)$ to $I(w\chi,-s)$. On the unitary axis both source and
target carry their own compact-picture inner products

$$
\langle f,h\rangle_K=\int_K f(k)\overline{h(k)}\,dk.
\tag{3.6}
$$

Thus an adjoint of the Weyl operator is a map in the reverse direction
$I(w\chi,-it)\to I(\chi,it)$; it is not an identification of the reflected datum with the
contragredient datum. This typing distinction is what makes the later formula
$M(\chi,it)^*=M(w\chi,-it)$ meaningful.

## 4. Rank-one Eisenstein series in the convergence chamber

### 4.1 Definition and the geometric meaning of the sum

For $f_s\in I(\chi,s)$ define

$$
E(g,f_s)
=\sum_{\gamma\in B(F)\backslash G(F)}f_s(\gamma g).
\tag{4.1}
$$

The coset space is the set of $F$-rational lines in $F^2$. Thus the sum assigns one term to every possible rational degeneration. Left $G(F)$-invariance follows by permuting the cosets, and central transformation follows from that of the section.

The sum is not taken over $G(F)$ itself. Summing over all rational matrices would repeat each rational line infinitely often through $B(F)$. Nor may one quotient by $N(F)$ alone, since rational diagonal rescaling would still repeat the same line.

For a standard section bounded on $K$, (3.1) gives

$$
|f_s(g)|\leq C_f H_B(g)^{\operatorname{Re}(s)+1/2}
\tag{4.2}
$$

in an Iwasawa decomposition. Convergence therefore reduces to counting rational lines by height.

### 4.2 Absolute convergence

**Theorem 4.1.** Let $f_s$ be a finite sum of factorizable standard sections whose compact-picture restrictions are smooth at the archimedean places and fixed by a compact open subgroup at the finite places. Then (4.1) converges absolutely and locally uniformly in $(g,s)$ for

$$
\operatorname{Re}(s)>\frac12.
\tag{4.3}
$$

On compact subsets of that half-plane it defines a smooth automorphic function of moderate growth and depends holomorphically on $s$.

**Proof strategy.** Reduce $g$ to a compact set, parametrize rational lines by primitive pairs, and compare the height contribution with a rank-two lattice sum. The exponent $1/2$ in normalized induction turns the classical convergence condition into (4.3).

**Proof.** Fix a compact set $C\subset G(\mathbf A)$. Right multiplication by $C$ changes all local norms of a rational row vector by bounded factors. A coset in $B(F)\backslash G(F)$ may be represented by a primitive rational row $(c,d)$, modulo multiplication by $F^\times$. Choose one representative in each ideal class and balance its archimedean embeddings by units. The finite denominators then lie in a fixed finite collection of fractional ideals, while the archimedean coordinates form full lattices.

In the Iwasawa decomposition of $\gamma g$, the inverse height is comparable to the square of the normalized size of the bottom row $(c,d)g$, after determinant normalization. Consequently, for $\sigma=\operatorname{Re}(s)$,

$$
|f_s(\gamma g)|
\leq C_C\|(c,d)\|^{-2\sigma-1}
\tag{4.4}
$$

in each of finitely many Minkowski lattices, with the complex embeddings counted twice. The number of lattice points of norm at most $R$ is $O(R^{2[F:\mathbf Q]})$ in ordinary real dimension, while the normalized radial power in (4.4) has the corresponding field-norm scaling. Equivalently, dyadic shells for the rank-two adelic height contain $O(R)$ rational lines and each contributes $O(R^{-\sigma-1/2})$ after the projective scaling has been removed. The resulting geometric series converges precisely for $\sigma>1/2$.

For clarity, the last comparison can be made without an asymptotic formula. Partition primitive pairs by dyadic values $2^m\leq H_B(\gamma g)^{-1}<2^{m+1}$. The adelic lattice-point estimate gives at most $C2^m$ projective classes in the $m$th shell. Formula (4.2), applied after reversing height, bounds one term by $C2^{-m(\sigma+1/2)}$. Thus the shell is $O(2^{-m(\sigma-1/2)})$, summable when $\sigma>1/2$.

The constants are uniform for $g\in C$ and $s$ in a compact subset of (4.3). This proves absolute and local uniform convergence. Differentiating a standard section inserts at worst a fixed power of the logarithmic height and bounded derivatives on $K$; the same geometric series still converges after slightly decreasing the positive distance from $\sigma$ to $1/2$. Holomorphy follows from locally uniform convergence of the differentiated series. $\square$

The proof uses exact hypotheses. Finite level prevents infinitely many unrelated finite denominators, smooth compact type controls archimedean derivatives, and standard dependence on $s$ controls logarithmic factors. An arbitrary pointwise family of sections need not satisfy a uniform convergence statement.

### 4.3 Uniform convergence and differentiation

Let $D$ be a right-invariant differential operator at infinity and let $C$ be compact in $G(\mathbf A)$. For every compact parameter set

$$
\Omega\subset\{s:\operatorname{Re}(s)>1/2\}
$$

there are constants $A,N$ such that

$$
\sum_{\gamma\in B(F)\backslash G(F)}
|D f_s(\gamma g)|
\leq A(1+H_B(g)+H_B(g)^{-1})^N
\tag{4.5}
$$

for $s\in\Omega$. On compact $g$-sets the right side is bounded. This estimate justifies termwise differentiation, right translation, and integration over compact unipotent quotients.

Moderate growth is the correct conclusion. Eisenstein series are not rapidly decreasing: their constant terms contain powers $H^{s+1/2}$ and $H^{-s+1/2}$. At the unitary axis both have absolute size $H^{1/2}$ before the quotient density $H^{-2}dH$ is applied. Wave packets gain decay by Fourier cancellation in $s$, but an individual unitary Eisenstein series is not square-integrable.

### 4.4 A rational example and the sharp boundary

For $F=\mathbf Q$, trivial characters, full finite level, and the spherical section, the quotient sum becomes the classical nonholomorphic Eisenstein series. If its traditional parameter is $u$, then

$$
u=s+\frac12.
$$

The classical convergence condition $\operatorname{Re}(u)>1$ is exactly $\operatorname{Re}(s)>1/2$.

At $s=1/2$ the shell estimate becomes harmonic rather than summable. This does not prove divergence for every section—cancellation or vanishing can improve a special case—but it shows that absolute convergence cannot be asserted uniformly at the boundary. Continuation past that line must come from the constant-term identity and Hecke-function continuation, not from rearranging a conditionally convergent rational-line sum.

## 5. Unfolding the constant term

### 5.1 The two Bruhat cells

The constant term of $E(g,f_s)$ is

$$
E_N(g,f_s)
=\int_{F\backslash\mathbf A}
\sum_{\gamma\in B(F)\backslash G(F)}
f_s(\gamma n(x)g)\,dx.
\tag{5.1}
$$

For $\operatorname{Re}(s)>1/2$, absolute convergence permits interchange of sum and integral. The rational Bruhat decomposition is

$$
G(F)=B(F)\sqcup B(F)wN(F).
\tag{5.2}
$$

Thus $B(F)\backslash G(F)$ has one closed cell represented by $1$ and one open cell represented by $wn(q)$ with $q\in F$.

The closed cell contributes

$$
\int_{F\backslash\mathbf A}f_s(n(x)g)\,dx=f_s(g),
$$

because $f_s$ is left $N(\mathbf A)$-invariant and the quotient has mass one.

For the open cell, summing $q\in F$ and integrating $x\in F\backslash\mathbf A$ unfolds to integration over $\mathbf A$:

$$
\sum_{q\in F}\int_{F\backslash\mathbf A}
f_s(wn(q+x)g)\,dx
=\int_{\mathbf A}f_s(wn(x)g)\,dx.
\tag{5.3}
$$

This is the multiplicative analogue of unfolding a periodized function. It uses the probability quotient measure induced by the same $dx$ on $\mathbf A$; otherwise a covolume factor would remain.

### 5.2 The global intertwining integral

For $\operatorname{Re}(s)>1/2$, define

$$
(M(\chi,s)f_s)(g)
=\int_{\mathbf A}f_s(wn(x)g)\,dx.
\tag{5.4}
$$

To see convergence, split $\mathbf A$ into a compact set and shells of large module. Locally, $wn(x)$ has Iwasawa root size comparable to $|x|^{-2}$ when $|x|>1$. Formula (3.1) then gives decay comparable to

$$
|x|_{\mathbf A}^{-2\operatorname{Re}(s)-1}.
$$

Additive measure contributes one power of $|x|$, leaving a geometric exponent $-2\operatorname{Re}(s)$. The product over places converges globally in the same chamber as the Eisenstein series. A precise proof follows from factorization and the local calculation in Chapters 6 and 7.

The integral is called an intertwining operator because it exchanges the two diagonal characters and reflects the parameter. This will be checked directly rather than inferred from its name.

### 5.3 The constant-term formula

**Theorem 5.1.** For $\operatorname{Re}(s)>1/2$,

$$
\boxed{
E_N(g,f_s)=f_s(g)+M(\chi,s)f_s(g).
}
\tag{5.5}
$$

**Proof.** Insert the two-cell decomposition (5.2) into (5.1). The closed cell gives $f_s(g)$. Parametrize the open cell by $N(F)$, then apply (5.3). The resulting adelic integral is (5.4). Every interchange is justified by Theorem 4.1. $\square$

This formula is the structural center of the book. The entire meromorphic behavior visible in the cusp is carried by $M(\chi,s)$. The first term is holomorphic because the standard section is. Any pole of the Eisenstein series must therefore appear in the intertwining term of its constant term, once the rapidly decaying remainder has been controlled.

### 5.4 Why there are exactly two exponents

On a diagonal element $t=\operatorname{diag}(a,d)$, the first term transforms by

$$
\chi_1(a)\chi_2(d)|a/d|^{s+1/2}.
$$

The second transforms by

$$
\chi_2(a)\chi_1(d)|a/d|^{-s+1/2}.
$$

Thus the two exponents are $s+1/2$ and $-s+1/2$. They correspond exactly to the two rational Bruhat cells. In higher rank there is one term for each Weyl element and poles can interact across several hyperplanes. Here the reflection group has two elements, so no third asymptotic exponent can occur.

A function with only the first exponent is not generally automorphic: the reflection term is what repairs its behavior under the second Bruhat cell. Conversely, adding an arbitrary second power is not enough; its coefficient must be the intertwining operator forced by unfolding.

## 6. Local intertwining operators

### 6.1 Definition and convergence

Let $v$ be a place of $F$. For $f_{v,s}\in I_v(\chi_v,s)$ define initially for $\operatorname{Re}(s)>0$

$$
(M_v(\chi_v,s)f_{v,s})(g)
=\int_{F_v}f_{v,s}(wn(x)g)\,dx_v.
\tag{6.1}
$$

The local convergence chamber is larger than the global one. On a compact set of $x$ there is no problem. For large $|x|_v$, an elementary matrix identity and Iwasawa decomposition give a diagonal factor with root absolute value $|x|_v^{-2}$. Hence the integrand is

$$
O(|x|_v^{-2\operatorname{Re}(s)-1}),
$$

and additive shells have measure comparable to $|x|_v$. Their product is summable when $\operatorname{Re}(s)>0$. At an archimedean place the same estimate is an ordinary radial integral.

The distinction between local and global convergence is instructive. Every local integral converges for $\operatorname{Re}(s)>0$, but the infinite product of its unramified values need not. The Euler product forces the global boundary to $\operatorname{Re}(s)>1/2$.

### 6.2 Covariance and the reflected induced representation

**Proposition 6.1.** In its convergence chamber,

$$
M_v(\chi_v,s):I_v(\chi_v,s)
\longrightarrow I_v(w\chi_v,-s).
\tag{6.2}
$$

**Proof strategy.** Check invariance under $N_v$ and transformation under $T_v$ by changes of variable in (6.1).

**Proof.** Right translation is built into the definition. For $u\in F_v$, left multiplication by $n(u)$ may be absorbed by translating $x$, so the output is left $N_v$-invariant. Let $t=\operatorname{diag}(a,d)$. Using

$$
t^{-1}n(x)t=n((d/a)x)
$$

and changing variables gives a factor $|a/d|_v$ from $dx$. The inducing transformation contributes

$$
\chi_{1,v}(d)\chi_{2,v}(a)|d/a|_v^{s+1/2}.
$$

After multiplying by the Jacobian, this becomes

$$
\chi_{2,v}(a)\chi_{1,v}(d)|a/d|_v^{-s+1/2},
$$

which is precisely the transformation law of $I_v(w\chi_v,-s)$. $\square$

The Jacobian is the reason the exponent $1/2$ is reflected cleanly. Without it, an unwanted full power of the modular character would remain.

### 6.3 The nonarchimedean spherical calculation

Assume $v$ is finite, $\chi_{1,v}$ and $\chi_{2,v}$ are unramified, and $f_{v,s}^0(1)=1$. Put

$$
z_v=\mu_v(\varpi_v)q_v^{-2s},
\qquad
\mu_v=\chi_{1,v}\chi_{2,v}^{-1}.
$$

Since the output is spherical, it is a scalar multiple of the normalized spherical section in $I_v(w\chi_v,-s)$. Its scalar is its value at $1$.

**Proposition 6.2.** With self-dual additive measure,

$$
M_v(\chi_v,s)f_{v,s}^0
=q_v^{-d_v/2}
\frac{1-q_v^{-1}z_v}{1-z_v}
f_{v,-s}^{0,w},
\tag{6.3}
$$

where $\mathfrak D_v=\mathfrak p_v^{d_v}$. At almost every place $d_v=0$, so

$$
M_v(\chi_v,s)f_{v,s}^0
=\frac{L_v(2s,\mu_v)}{L_v(2s+1,\mu_v)}
f_{v,-s}^{0,w}.
\tag{6.4}
$$

**Proof.** First suppose $\operatorname{vol}(\mathcal O_v)=1$. On $x\in\mathcal O_v$, $wn(x)\in K_v$, so the integral contributes $1$. For $|x|_v=q_v^m$, $m\geq1$, the Iwasawa decomposition gives

$$
f_{v,s}^0(wn(x))
=\mu_v^{-1}(x)|x|_v^{-2s-1}.
$$

The shell has measure $(1-q_v^{-1})q_v^m$. Writing $x=\varpi_v^{-m}u$ and using unramifiedness gives the shell contribution

$$
(1-q_v^{-1})z_v^m.
$$

Therefore

$$
1+(1-q_v^{-1})\sum_{m\geq1}z_v^m
=\frac{1-q_v^{-1}z_v}{1-z_v}.
$$

The self-dual measure is $q_v^{-d_v/2}$ times the integer-volume-one measure, which gives (6.3). Away from the different, $d_v=0$, and the last quotient is exactly the ratio in (6.4). $\square$

The discriminant factors at the finitely many places with $d_v>0$ must not be inserted into the unramified Euler tail twice. They belong to the finite correction when self-dual measures are used.

### 6.4 Ramified and archimedean sections

At a ramified finite place, choose a compact open subgroup fixing the section. Decompose $F_v$ into finitely many compact shells plus a tail on which the Iwasawa formula is monomial. The local integral becomes a rational function of $q_v^{-s}$. More precisely, after multiplication by the inverse of the appropriate local ratio

$$
\frac{L_v(2s,\mu_v)}{L_v(2s+1,\mu_v)},
$$

its matrix entries on every fixed-vector space are Laurent polynomials in $q_v^{-s}$. This follows from the same finite shell calculation used for local zeta integrals. It gives meromorphic continuation without an infinite-dimensional argument.

At a real or complex place, use the compact picture. Matrix coefficients between fixed compact types reduce to Mellin integrals of smooth functions with controlled behavior at zero and infinity. Subtracting a finite Taylor expansion continues those integrals meromorphically. Dividing by

$$
\frac{L_v(2s,\mu_v)}{L_v(2s+1,\mu_v)}
$$

removes the scalar gamma singularities in the closed strip needed below. Repeated integration by parts gives polynomial control on compact vertical strips.

The spherical archimedean calculations provide exact checks. At a real place with $\mu_v=1$ and $f_{v,s}^0|_{\mathrm O(2)}=1$,

$$
M_v(s)f_{v,s}^0(1)
=\int_{\mathbf R}(1+x^2)^{-s-1/2}\,dx
=\sqrt\pi\frac{\Gamma(s)}{\Gamma(s+1/2)}
=\frac{\Gamma_{\mathbf R}(2s)}{\Gamma_{\mathbf R}(2s+1)}.
\tag{6.5}
$$

At a complex place, normalized absolute value is $|z|_{\mathbf C}=|z|_{\mathrm{usual}}^2$ and self-dual measure is $2\,dx\,dy$. Hence

$$
\begin{aligned}
M_v(s)f_{v,s}^0(1)
&=2\int_{\mathbf C}(1+|z|^2)^{-2s-1}\,dx\,dy\\
&=4\pi\int_0^\infty r(1+r^2)^{-2s-1}\,dr
=\frac\pi s
=\frac{\Gamma_{\mathbf C}(2s)}{\Gamma_{\mathbf C}(2s+1)}.
\end{aligned}
\tag{6.6}
$$

These formulas show independently why the real exponent is $s+1/2$, why the normalized complex absolute value is squared, and why the complex self-dual measure carries a factor two. For nontrivial spherical $\mu_v$, the same beta integral with the radial character gives $L_v(2s,\mu_v)/L_v(2s+1,\mu_v)$.

We record the exact finite-dimensional statement used later.

**Proposition 6.3.** Fix a place $v$, a compact open fixed-vector space if $v$ is finite, or finitely many compact types if $v$ is archimedean. Then $M_v(\chi_v,s)$ extends meromorphically through the strip $0\leq\operatorname{Re}(s)\leq1/2$. After removal of the scalar local Hecke ratio, its matrix is holomorphic at every point contributing to a global pole except possibly where

$$
\mu_v|\cdot|_v^{2s}=|\cdot|_v.
$$

At that exceptional point the relevant quotient is one-dimensional. On the imaginary axis the normalized form is bounded on the fixed finite-dimensional space. Other local reducibility points may change the kernel or image of a regular operator, but do not by themselves create a global pole.

**Proof.** The finite-place assertion is the shell calculation just described. At infinity, Taylor subtraction gives continuation, and the local functional equation for the underlying Mellin integrals identifies every possible scalar singularity with the displayed gamma ratio. The remaining integral has a smooth kernel on the compact picture and is holomorphic by dominated differentiation. Under the displayed character identity, the reflected inducing transformation is $t\mapsto\eta(\det t)$ for a local character $\eta$, so its invariant quotient is one-dimensional. Regular reducibility points require no exception to holomorphy and leave no residue in the global contour shift. $\square$

The proposition deliberately claims only the half-plane and finite types required here. A uniform theory over all compact types is unnecessary for the global annihilation argument.

## 7. The global operator as a product of local operators

### 7.1 Factorization in the convergence chamber

Let $f_s=\otimes_vf_{v,s}$ be factorizable. For $\operatorname{Re}(s)>1/2$, absolute convergence gives

$$
M(\chi,s)f_s
=\bigotimes_vM_v(\chi_v,s)f_{v,s}.
\tag{7.1}
$$

**Proof strategy.** First integrate over a finite product of local fields and the integer rings outside it; then expand the remaining valuation shells and use absolute convergence of the Euler product.

**Proof.** Choose a finite set $S$ containing all archimedean places, all places where the characters or sections are ramified, and all places dividing the different. On

$$
\mathbf A_S\times\prod_{v\notin S}\mathcal O_v
$$

ordinary finite-product Fubini applies. Outside this compact subset, decompose each nonzero coordinate by its negative valuation. The absolute values of the resulting terms are bounded by the Euler product

$$
\prod_{v\notin S}
\frac{1-q_v^{-2\sigma-1}}{1-q_v^{-2\sigma}},
\qquad \sigma=\operatorname{Re}(s),
$$

which converges for $2\sigma>1$. Tonelli therefore permits the shell sums and finite-product integrals to be interchanged. Passing through increasing finite sets proves (7.1). $\square$

The proof explains why a product of locally convergent integrals may fail globally when $0<\operatorname{Re}(s)\leq1/2$: the denominator has the convergence behavior of a Hecke Euler product at $2s$.

### 7.2 The completed scalar and the finite correction

Define

$$
r(\chi,s)=\frac{\Lambda(2s,\mu)}{\Lambda(2s+1,\mu)}.
\tag{7.2}
$$

For a factorizable standard section there is a finite meromorphic operator $A_S(\chi,s)$, a tensor product over the places in $S$, such that

$$
M(\chi,s)f_s
=r(\chi,s)A_S(\chi,s)f_s.
\tag{7.3}
$$

At an unramified place outside $S$, $A_v$ fixes the normalized spherical vector. At places in $S$, it includes the ramified-section correction, the archimedean compact-type operator, and the factor $q_v^{-d_v/2}$ arising from self-dual measure. Thus (7.3) is exact under the normalization ledger.

The possible poles in the required strip are now visible. The finite correction is holomorphic there apart from a possible local reducibility point. The completed scalar can have a pole only when $\Lambda(2s,\mu)$ does, unless a zero of the denominator cancels it. The one-dimensional Hecke theory classifies precisely when that happens.

### 7.3 Normalization of the operator

Put

$$
\mathcal A(\mu)=N\mathfrak f(\mu)|d_F|,
\qquad
\Xi(u,\mu)=\mathcal A(\mu)^{u/2}\Lambda(u,\mu).
\tag{7.4}
$$

The functional equation of $\Xi$ has constant root number:

$$
\Xi(u,\mu)=W(\mu)\Xi(1-u,\mu^{-1}).
$$

Define the symmetric normalizing scalar and normalized operator by

$$
\rho(\chi,s)
=\frac{\Xi(2s,\mu)}{\Xi(2s+1,\mu)}
=\mathcal A(\mu)^{-1/2}r(\chi,s),
\qquad
R(\chi,s)=\rho(\chi,s)^{-1}M(\chi,s).
\tag{7.5}
$$

The fixed factor $\mathcal A(\mu)^{-1/2}$ is absorbed into the finite correction in (7.3). On every fixed finite-level, finite-type space, $R(\chi,s)$ is meromorphic in the required half-plane and holomorphic on the imaginary axis. The rank-one composition identity for the global, self-dually measured operator is

$$
M(w\chi,-s)M(\chi,s)=\operatorname{id}
\tag{7.6}
$$

where both sides are regular, and hence everywhere by meromorphic continuation. Equivalently,

$$
R(w\chi,-s)R(\chi,s)=\operatorname{id},
\tag{7.7}
$$

because the constant-root-number functional equation gives

$$
\rho(w\chi,-s)\rho(\chi,s)=1.
\tag{7.8}
$$

This identity uses the same local normalization at every place.

The word _global_ is essential. A raw local intertwining integral generally composes to a
nontrivial scalar. In the global product, the different, conductor, and ramified local
corrections combine with the functional equation of $\Lambda$; under the self-dual measure
ledger their product is exactly the scalar needed for (7.6). A clean proof in the present
range uses the Eisenstein functional equation proved in Chapter 8: compare the two constant
terms of the same continued Eisenstein series and use independence of the two height exponents
away from $s=0$. Meromorphic continuation then fills the exceptional point.

### 7.4 A normalization audit

Four independent checks now agree.

1. Normalized induction uses $s+1/2$, so the local operator reflects $s$ to $-s$.
2. The spherical shell variable is $z_v=\mu_v(\varpi_v)q_v^{-2s}$, so the Euler ratio is $L_v(2s,\mu_v)/L_v(2s+1,\mu_v)$.
3. Self-dual measure introduces $q_v^{-d_v/2}$ only at the finite set dividing the different; it is placed in $A_S$, not the Euler tail.
4. Symmetric conductor completion makes the Hecke functional equation have constant root number and makes the two normalizing scalars in (7.8) exact inverses.

Changing the Fourier phase, the complex absolute value, or the local additive measure would alter at least one of these checks. A consistent alternative normalization is possible, but formulas from two systems cannot be mixed.

## 8. Continuation in the required strip

### 8.1 Truncation isolates the constant term

The rational-line sum cannot be continued by termwise estimates at $\operatorname{Re}(s)=1/2$. The obstruction is concentrated in the constant term. Once its two explicit powers are removed above a fixed height, the remaining function decreases rapidly enough to be integrated on the quotient.

Fix $Y>1$. In each high cusp, let $H(g)$ be the reduced height and define rank-one truncation by

$$
(\Lambda^YE)(g)
=E(g)-\sum_{\gamma\in B(F)\backslash G(F)}
\mathbf 1_{\{H(\gamma g)>Y\}}E_N(\gamma g).
\tag{8.1}
$$

Only finitely many summands are nonzero at each $g$, and high-cusp uniqueness makes the sum a single term sufficiently far out. A smooth cutoff may replace the characteristic function; the meromorphic conclusions are independent of that choice.

For $\operatorname{Re}(s)>1/2$, insert (5.5). The growing part of $E$ is cancelled in every cusp, while nonconstant unipotent Fourier modes retain oscillation. For every $A>0$, repeated integration by parts on the compact unipotent quotient, together with the balanced cusp expansion, gives

$$
|D\Lambda^YE(g,f_s)|
\leq C_{D,A,Y,\Omega}H(g)^{-A}
\tag{8.2}
$$

when $\Omega$ is a compact subset of the convergence chamber. Here is the estimate rather than
an analogy: after finite level is fixed, the unipotent fiber is a real torus with a fixed dual
lattice. Its zero Fourier coefficient is exactly the term subtracted in (8.1). Applying a
transverse invariant derivative $m$ times multiplies the coefficient of a nonzero dual-lattice
point by a quantity bounded below by $cH^{m/[F:\mathbf Q]}$. Uniform bounds for the same
derivatives of the absolutely convergent series therefore give $H^{-m/[F:\mathbf Q]}$ decay.
Choose $m>A[F:\mathbf Q]$; compactness of the remaining cusp coordinates gives (8.2).

Consequently $\Lambda^YE(g,f_s)$ is square-integrable and holomorphic in the convergence
chamber. After the direct continuation below has been constructed, the same argument on compact
parameter sets avoiding its poles extends (8.2) there. The untruncated series is recovered by
adding back two explicitly meromorphic height powers. This order avoids using continuation to
prove itself.

There is a direct construction that proves this assertion without circularity and also identifies the poles. For $\Phi\in\mathcal S(\mathbf A^2)$ put

$$
f_{\Phi,s}(g)
=\chi_1(\det g)|\det g|^{s+1/2}
\int_{\mathbf A^\times}
\Phi((0,t)g)\mu(t)|t|^{2s+1}\,d^\times t.
\tag{8.3}
$$

A change of variable verifies (3.1). Summing over rational lines and grouping nonzero vectors on each line gives

$$
E(g,f_{\Phi,s})
=\chi_1(\det g)|\det g|^{s+1/2}
\int_{F^\times\backslash\mathbf A^\times}
\sum_{0\ne v\in F^2}\Phi(tv g)
\mu(t)|t|^{2s+1}\,d^\times t.
\tag{8.4}
$$

The sum is a two-dimensional theta series without its zero vector. Splitting the module at one and applying Poisson summation on $\mathbf A^2$ continues (8.4), exactly as in the one-dimensional Hecke integral. Scaling in two dimensions contributes $|t|^{-2}$, so the reflected exponent is

$$
(2s+1)\longmapsto2-(2s+1)=1-2s,
$$

which is $s\mapsto-s$.

We now justify that these sections suffice. Fix a parameter $s_*$ and a finite-dimensional
compact-picture space. Locally, the map

$$
(t,k)\longmapsto (0,t)k
$$

parametrizes the nonzero row-vector orbit, modulo the compact stabilizer already present in the
compact picture. Choose a compactly supported radial function whose Mellin transform is nonzero
near $s_*$, and multiply it by a prescribed compact-picture vector pulled back along this map.
Averaging over the compact stabilizer makes the definition independent of the chosen
representative. Compact-open partitions at finite places and a compact-type partition of unity
at infinity show that finitely many such functions span the chosen compact-picture space. Their
Mellin transforms form a holomorphic matrix invertible after shrinking the neighborhood of
$s_*$. Its holomorphic inverse expresses every flat section there as a finite holomorphic linear
combination of sections (8.3).

Taking restricted tensor products leaves the spherical tail unchanged, and expanding the
finitely many exceptional factors gives the global statement. Since $s_*$ was arbitrary, these
local continuations glue by uniqueness on the original convergence chamber. Thus the theta
argument continues every finite-level, finite-type standard section used in this book; no
unproved global surjectivity of a single Schwartz function is being assumed.

### 8.2 Meromorphic continuation to the closed right half-plane

**Theorem 8.1.** Let $f_s$ satisfy the hypotheses of Theorem 4.1. Then $E(g,f_s)$ and $M(\chi,s)f_s$ continue meromorphically from $\operatorname{Re}(s)>1/2$ to a neighborhood of

$$
\{s:\operatorname{Re}(s)\geq0\}.
$$

On every fixed finite-level, finite-type space, the only possible pole in this region is simple and arises when

$$
\mu|\cdot|^{2s_0}=|\cdot|.
\tag{8.5}
$$

Away from that point the continued Eisenstein series is smooth in $g$, meromorphic in $s$, and of moderate growth locally uniformly on compact parameter sets.

**Proof.** For sections (8.3), split the module integral in (8.4) at one. The large-module theta integral is entire because the test function decreases rapidly. Apply two-dimensional Poisson summation to the small-module integral and substitute $t\mapsto t^{-1}$. The transformed nonzero-vector term is another entire large-module integral. The omitted zero vector and its transformed counterpart give elementary Mellin integrals on $C_F^1\times(0,1]$.

Those elementary terms vanish unless $\mu$ is trivial on $C_F^1$, equivalently unless $\mu=|\cdot|^{i\tau}$ for some real $\tau$. In that case they have simple denominators

$$
2s+1+i\tau
\qquad\text{and}\qquad
2s-1+i\tau.
$$

The first pole lies at real part $-1/2$; the second lies at

$$
s_0=\frac{1-i\tau}{2}
$$

and is the only one in the required region. This is exactly (8.5). Finite sums give the theorem for every required section. The same calculation applied to the open-cell term, or comparison of constant terms through (5.5), gives the continuation of $M(\chi,s)$. Uniform Schwartz estimates justify differentiation in $g$ and $s$. $\square$

The theorem asserts actual poles only when the relevant zero-orbit functional on the section is nonzero. A special section can have zero residue. The pole belongs to the meromorphic family of operators, not necessarily to every vector in it.

### 8.3 The functional equation

Poisson summation in (8.4) exchanges $\Phi$ with its two-dimensional Fourier transform and $s$ with $-s$. Translating this statement from Schwartz sections to their compact-picture span gives

$$
\boxed{
E(g,f_s)=E(g,M(\chi,s)f_s)
}
\tag{8.6}
$$

where the right side is the Eisenstein series for the reflected datum $I(w\chi,-s)$. Both sides are meromorphic.

There is also a proof using constant terms. The difference between the two sides has zero constant term by (5.5) and the composition identity. In the initial chamber where both expressions may be compared after truncation, it is a rapidly decreasing automorphic function orthogonal to every compactly supported pseudo-Eisenstein series by unfolding. It is therefore both cuspidal and in the constant-term-generated subspace, hence zero. Meromorphic continuation completes the identity.

Applying (8.6) twice gives

$$
M(w\chi,-s)M(\chi,s)=1.
$$

Thus the composition identity used earlier is now proved without evaluating a divergent double integral.

### 8.4 Regularity and unitarity on the imaginary axis

The pole criterion (8.5) has real part $1/2$, so no pole lies on $s=it$. The normalized operator is therefore regular on the imaginary axis.

For standard sections $f_{it}$ and $h_{it}$, changes of variables in the local integrals, first in a convergence region and then by continuation, give the adjoint relation

$$
R(\chi,it)^*=R(w\chi,-it)=R(\chi,it)^{-1}.
\tag{8.7}
$$

Together with (7.7), this yields

$$
R(\chi,it)^*R(\chi,it)=1.
\tag{8.8}
$$

Hence the normalized global intertwining operator is unitary on every fixed finite-level, finite-type compact-picture space.

For unitary $\mu$, complex conjugation and the symmetric functional equation give

$$
|\Xi(2it,\mu)|=|\Xi(1+2it,\mu)|,
$$

so $|\rho(\chi,it)|=1$. Consequently the global unnormalized operator is unitary as well:

$$
M(\chi,it)^*=M(w\chi,-it)=M(\chi,it)^{-1}.
\tag{8.9}
$$

This is a global statement. Individual raw local intertwining integrals need not be unitary;
their normalizing scalars and the finite global correction are indispensable. The earlier
claim is therefore not that normalization creates global unitarity, but that it makes the Weyl
composition and the local-to-global scalar bookkeeping transparent.

## 9. Poles and residues

### 9.1 The character-theoretic pole criterion

Suppose a pole $s_0$ occurs in $\operatorname{Re}(s)\geq0$. By Theorem 8.1 there is a real $\tau$ such that

$$
\mu=|\cdot|^{i\tau},
\qquad
s_0=\frac{1-i\tau}{2}.
\tag{9.1}
$$

Define

$$
\eta=\chi_1|\cdot|^{-i\tau/2}
=\chi_2|\cdot|^{i\tau/2}.
\tag{9.2}
$$

Then $\eta$ is unitary and

$$
\eta^2=\chi_1\chi_2=\omega.
\tag{9.3}
$$

Conversely, every unitary idele class character $\eta$ with $\eta^2=\omega$ can arise from such a pole after choosing a unitary parametrization of the inducing pair. Thus the residual data are indexed by square roots of the central character, not by arbitrary pairs of characters.

The pole is simple because the completed Hecke function has a simple pole and the denominator $\Lambda(2s_0+1,\mu)$ is finite and nonzero in the convergence half-plane. The finite correction is regular on the one-dimensional quotient that survives.

### 9.2 The residue is one-dimensional

Let

$$
\mathcal R_{f}(g)
=\operatorname*{Res}_{s=s_0}E(g,f_s).
\tag{9.4}
$$

The first term in the constant-term formula is holomorphic, so

$$
(\mathcal R_f)_N(g)
=\operatorname*{Res}_{s=s_0}M(\chi,s)f_s(g).
\tag{9.5}
$$

The residue on the right belongs to the reflected induced representation $I(w\chi,-s_0)$. Its diagonal transformation is

$$
\chi_2(a)\chi_1(d)|a/d|^{i\tau/2}
=\eta(a)\eta(d)
=\eta(ad).
\tag{9.6}
$$

The determinant character

$$
g\longmapsto\eta(\det g).
\tag{9.7}
$$

has exactly this covariance, but covariance alone does **not** prove one-dimensionality:
$I(w\chi,-s_0)$ is a reducible induced representation containing many sections with the same
left $N$-invariance. The decisive input is the theta continuation. In (8.4), every
nonzero-vector integral is holomorphic at $s_0$ after the small-module term has been transformed.
The entire residue comes from the transformed zero vector, which is independent of the
projective direction and equals a scalar multiple of (9.7). Therefore no vector in the other
constituent can occur in the residue.

**Theorem 9.1.** Every nonzero residue in the required half-plane has the form

$$
\operatorname*{Res}_{s=s_0}E(g,f_s)
=c(f)\eta(\det g),
\tag{9.8}
$$

where $\eta$ is unitary and $\eta^2=\omega$. The scalar $c(f)$ is the zero-orbit functional of the associated Schwartz section, equivalently the residue of $M(\chi,s)f_s$ at the identity.

For trivial inducing characters and the spherical section, this recovers the constant function. For a nontrivial square root $\eta$, the residual function is not constant but remains one-dimensional under right translation.

### 9.3 Square integrability of the residue

Because $\eta$ is unitary,

$$
|\eta(\det g)|=1.
$$

Because $\eta^2=\omega$, the function has the prescribed central character:

$$
\eta(\det(zg))=\eta(z^2)\eta(\det g)=\omega(z)\eta(\det g).
$$

The central automorphic quotient has finite volume. Consequently (9.7) is square-integrable and

$$
\|\eta\circ\det\|_2^2
=\operatorname{vol}\bigl(Z(\mathbf A)G(F)\backslash G(\mathbf A)\bigr)
\tag{9.9}
$$

under the fixed quotient measure.

This is the residual contribution: a pole of a non-square-integrable family leaves a square-integrable one-dimensional representation. The square integrability is not inferred merely from the word “residue”; it follows from unitarity, central equivariance, and finite volume.

### 9.4 What does not produce a residual term

If $\mu$ is nontrivial on $C_F^1$, the zero-orbit integrals vanish by character orthogonality, so the Eisenstein family is holomorphic in the required strip. Ramification of $\mu$ by itself does not create a pole. Nor does a local reducibility point create a global residual term unless the global character criterion (8.5) holds.

At $s=0$, the two exponents in the constant term coincide in absolute size, but the family is regular. The normalized intertwining operator may have eigenvalues $1$ and $-1$ there; this affects the parametrization of the continuous family, not the appearance of a residue.

A zero of the numerator or denominator of an isolated local factor is also insufficient. Global poles are determined by the completed product together with its finite correction. Treating one Euler factor as if it classified a global residue would ignore cancellation and the global character condition.

## 10. Pseudo-Eisenstein series and wave packets

### 10.1 Incomplete data on the Borel quotient

Eisenstein series begin with a pure exponential in height. A compactly supported function of height is often more convenient because its rational translate sum is immediately integrable. Let $\varphi$ be a smooth left $B(F)N(\mathbf A)$-invariant function on $G(\mathbf A)$ satisfying

$$
\varphi(zg)=\omega(z)\varphi(g).
$$

Assume that it has compact support in the height direction modulo the center, finite level, and finite compact type. Define

$$
\Theta_\varphi(g)
=\sum_{\gamma\in B(F)\backslash G(F)}\varphi(\gamma g).
\tag{10.1}
$$

The sum is locally finite by the Siegel intersection property. Such a function is called a pseudo-Eisenstein series. It need not be cuspidal; its purpose is to generate the constant-term channel with compactly supported input.

For a smooth automorphic function $h$ for which the pairing converges, unfolding gives

$$
\langle h,\Theta_\varphi\rangle
=\langle h_N,\varphi\rangle_{B\text{-quotient}}.
\tag{10.2}
$$

The proof is direct: insert (10.1), integrate over a fundamental region, and let the rational translates fill $B(F)\backslash G(\mathbf A)$. Then integrate over $N(F)\backslash N(\mathbf A)$ to obtain $h_N$.

Equation (10.2) has a decisive consequence. If an $L^2$ automorphic function is orthogonal to every right translate of every pseudo-Eisenstein series, its constant term vanishes in every cusp chart; hence it is cuspidal. Conversely every cusp form is orthogonal to all pseudo-Eisenstein series. Therefore

$$
\bigl(L^2_{\mathrm{cusp},\omega}\bigr)^{\perp}
=\overline{\operatorname{span}\{R(g)\Theta_\varphi\}}.
\tag{10.3}
$$

This is an elementary orthogonal-complement statement, not a decomposition of the right regular representation into a general spectral measure.

### 10.2 Mellin inversion along height

The compact norm-one idele class direction is Fourier-expanded into unitary characters. Along the remaining height variable $H=e^t$, ordinary Fourier inversion in $t$ gives

$$
\varphi(g)
=\frac1{2\pi i}
\sum_{\chi}
\int_{\operatorname{Re}(s)=c}
f_{\chi,s}(g)\,ds,
\tag{10.4}
$$

where $c>1/2$, the sum runs over the discrete unitary characters compatible with the fixed level, and its coefficients decrease rapidly in the compact-class character lattice. The Mellin transforms $f_{\chi,s}|_K$ also decrease faster than every power of $|\operatorname{Im}(s)|$. Thus the character sum and the integral converge locally absolutely. The two characters in $\chi=(\chi_1,\chi_2)$ multiply to $\omega$.

Absolute convergence permits summation over rational lines, giving

$$
\Theta_\varphi(g)
=\frac1{2\pi i}
\sum_\chi\int_{\operatorname{Re}(s)=c}
E(g,f_{\chi,s})\,ds.
\tag{10.5}
$$

This identity explains why Eisenstein series are the spectral exponentials of the constant-term channel. The compactly supported height profile is reconstructed by a Mellin superposition of pure powers.

### 10.3 Moving the contour

Move the contour in (10.5) from $\operatorname{Re}(s)=c$ to $\operatorname{Re}(s)=0$. The rapid decrease of the Mellin transform and polynomial vertical-strip bounds for the finite-type intertwining operator make the horizontal integrals tend to zero. Cauchy's theorem gives

$$
\Theta_\varphi(g)
=\frac1{2\pi}\sum_\chi
\int_{\mathbf R}E(g,f_{\chi,it})\,dt
+\sum_{\eta^2=\omega}c_{\eta}(\varphi)\eta(\det g).
\tag{10.6}
$$

Only characters compatible with the fixed compact data occur, with rapidly decreasing coefficients. The residue sum is finite because fixed finite level bounds the conductors of the quadratic quotients of two square roots of $\omega$. The second sum consists precisely of residues crossed at the points (9.1).

The equality is first obtained after truncation, where every integral is absolutely convergent in $L^2$ on a compact region. Estimate (8.2), rapid Mellin decay, and the finite cusp-volume bound then pass to the global $L^2$ limit. Thus (10.6) is not a pointwise assertion about an unintegrated continuum at every cusp; it is a wave-packet identity.

### 10.4 The elementary Maass--Selberg identity

Truncation also gives the norm relation that controls the unitary axis. Let $f_s$ and $h_{s'}$ have the same central character and compatible inducing data. Write $\langle\ ,\ \rangle_{\mathrm{cpt}}$ for the exact pairing on the compact part of the Borel quotient: it uses probability measure on $C_F^1$ and $K$, together with the factor $\kappa_F$ in (1.3). Away from vanishing denominators,

$$
\begin{aligned}
\langle\Lambda^YE(f_s),\Lambda^YE(h_{s'})\rangle
={}&\frac{Y^{s+\bar s'}}{s+\bar s'}\langle f_s,h_{s'}\rangle_{\mathrm{cpt}}
+\frac{Y^{s-\bar s'}}{s-\bar s'}
  \langle f_s,M(s')h_{s'}\rangle_{\mathrm{cpt}}\\
&+\frac{Y^{-s+\bar s'}}{-s+\bar s'}
  \langle M(s)f_s,h_{s'}\rangle_{\mathrm{cpt}}
+\frac{Y^{-s-\bar s'}}{-s-\bar s'}
  \langle M(s)f_s,M(s')h_{s'}\rangle_{\mathrm{cpt}}.
\end{aligned}
\tag{10.7}
$$

If a denominator vanishes, the corresponding quotient is interpreted by its limit. The definition of $\langle\ ,\ \rangle_{\mathrm{cpt}}$ is what makes (10.7) exact for the measure ledger of Chapter 1.

**Proof strategy.** Unfold one Eisenstein sum in the inner product of truncated series and
split the remaining rational terms into the two Bruhat cells. On the portion below height $Y$
the two closed-cell contributions are the original sections; on the portion above $Y$ the
subtractions in (8.1) replace them by their reflected terms. The open-cell integral is exactly
$M(s)$, so the four surviving pairings are the four displayed in (10.7). The compact core
appears twice with opposite signs and cancels. The nonconstant Fourier modes are absolutely
integrable by (8.2); translating their unfolded domains pairs each such term with the identical
term carrying the opposite truncation sign. Thus no unrecorded boundary integral remains.

The quotient density is $H^{-2}dH$, while each pair of normalized inducing exponents contributes
one factor $H$. The radial integrals are therefore

$$
\int^Y H^{a}\frac{dH}{H}=\frac{Y^a}{a},
$$

which gives (10.7). This proves the identity in a joint convergence region. Both sides are
meromorphic finite-type pairings, so continuation proves it everywhere both sides are defined.

On the imaginary axis, take $s'=s$ after first keeping the parameters distinct. The apparent
singular quotients combine into their derivatives, and the coefficient of $\log Y$ is the sum
of the compact-picture norm and the norm after scattering. Positivity together with (7.7)
forces preservation of the compact-picture norm, giving an independent proof of (8.8). It also
shows why individual Eisenstein series are not in $L^2$: their truncated norm grows linearly in
$\log Y$.

For later use, apply (10.7) to two rapidly decreasing packets, integrate in both spectral
parameters, and let $Y\to\infty$. Fourier inversion makes the terms with distinct parameters
orthogonal; the two terms related by $t\leftrightarrow-t$ combine through the unitary operator
$R(\chi,it)$. If the packet coefficients are written in the Weyl-symmetric form

$$
a_{w\chi}(-t)=R(\chi,it)a_\chi(t),
\tag{10.8}
$$

the resulting norm is a positive integral of compact-picture norms, with only the harmless
factor two coming from the Weyl redundancy. Pairing the contour identity (10.6) with a residual
character and unfolding shows that its value is exactly the residue term already displayed in
(10.6); hence the remaining unitary-axis packet is orthogonal to that character. This proves,
without invoking a general Plancherel theorem, both continuous--residual orthogonality and the
orthogonality of disjoint unitary spectral packets used in Chapter 11.

## 11. Classification of the noncuspidal contributions

### 11.1 The constant-term channel

The orthogonal-complement identity (10.3) reduces classification to pseudo-Eisenstein series. Mellin inversion and contour motion then reduce every pseudo-Eisenstein series to two explicitly described kinds of term. Nothing else can occur in the required range because every pole crossed by the contour has already been classified.

This reasoning is both global and economical. Reduction theory says there is one parabolic escape direction. Unfolding says that its compactly supported functions are generated by pseudo-Eisenstein sums. One-variable Mellin inversion says that pure powers span those height profiles. The two-cell constant term and one-dimensional Hecke continuation determine the reflection and poles.

### 11.2 Continuous and residual terms

The continuous terms are wave packets

$$
\frac1{2\pi}\int_{\mathbf R}E(g,f_{it})\,dt
\tag{11.1}
$$

for unitary inducing data, with the redundancy

$$
(\chi_1,\chi_2,it)
\sim(\chi_2,\chi_1,-it)
$$

implemented by $M(\chi,it)$. A single Eisenstein series is a generalized eigenfunction; only a sufficiently decreasing packet is an $L^2$ automorphic function.

The residual terms are

$$
g\longmapsto\eta(\det g),
\qquad
\eta^2=\omega.
\tag{11.2}
$$

Each spans a one-dimensional invariant subspace. Distinct $\eta$ are orthogonal: their quotient is a nontrivial unitary character on the determinant image, and integration over the corresponding compact class direction gives zero.

There is no third type. In particular, no complementary-series interval appears as a separate automorphic contribution in this contour shift. Nonunitary parameters occur while the contour moves, but only their poles leave terms after the contour reaches the unitary axis.

### 11.3 The classification theorem in the required range

**Theorem 11.1.** Fix a number field $F$, a unitary central character $\omega$, a finite level, and finitely many archimedean compact types. In the closed span generated by smooth compactly supported pseudo-Eisenstein series of these data, every contribution obtained by continuation from $\operatorname{Re}(s)>1/2$ to $\operatorname{Re}(s)=0$ is one of the following:

1. a wave packet of unitary rank-one Eisenstein series induced from unitary pairs $(\chi_1,\chi_2)$ with $\chi_1\chi_2=\omega$;
2. a one-dimensional residual character $\eta\circ\det$ with $\eta^2=\omega$.

The two classes are mutually orthogonal after wave-packet integration, and their closed span is $\bigl(L^2_{\mathrm{cusp},\omega}\bigr)^{\perp}$ within the fixed data.

**Proof.** Equation (10.3) identifies the noncuspidal closed subspace with the closure of pseudo-Eisenstein series. Equation (10.5) writes each generator as a Mellin integral in the convergence chamber. Theorem 8.1 permits contour motion to the unitary axis. Theorem 9.1 identifies every crossed residue with (11.2), yielding (10.6). Unitarity of normalized intertwining and the Maass--Selberg identity give orthogonality of disjoint unitary parameter packets; character orthogonality separates distinct residues. Taking closures proves the assertion. $\square$

The theorem is deliberately typewise and levelwise. This is exactly the setting of a factorizable trace kernel, and it avoids unsupported uniform summation over all levels and compact types.

### 11.4 Why no general spectral measure is needed

The proof never decomposes an arbitrary unitary representation of $G(\mathbf A)$ outside the already established cuspidal subspace. It uses only:

- the orthogonal complement characterized by constant terms;
- compactly supported pseudo-Eisenstein generators;
- Fourier series on a compact abelian class group;
- one-variable Mellin inversion;
- continuation and residues of rank-one Eisenstein series.

This is enough for later trace arguments because their noncuspidal kernels are tested on finite-level, finite-type wave packets. A universal measure formula, multiplicity statement for every induced datum, or higher-rank scattering matrix would add machinery without strengthening the annihilation conclusion.

## 12. Cuspidal local test functions

### 12.1 The operator-level vanishing condition

Let $k$ be a local field of characteristic zero, $G_k=\mathrm{GL}_2(k)$, and $B_k=T_kN_k$. Fix the local central character $\omega_k$. A smooth function $f:G_k\to\mathbf C$ satisfying

$$
f(zg)=\omega_k(z)^{-1}f(g)
$$

is an admissible test function if it is compactly supported modulo $Z_k$ when $k$ is
nonarchimedean, or belongs to the invariant Harish--Chandra Schwartz space modulo $Z_k$ when
$k$ is archimedean. It is called strongly cuspidal if

$$
\int_{N_k}f(x^{-1}tny)\,dn=0
\tag{12.1}
$$

for every $x,y\in G_k$ and $t\in T_k$. Absolute convergence is part of the condition at infinity.

This two-sided formulation is tailored to operators. Let $I_k(\xi)$ be normalized induction
from a quasicharacter $\xi$ of $T_k$, with central character $\omega_k$, at a parameter where
convolution by $f$ is defined. In the compact picture, Iwasawa integration in the order $tnk$
gives the kernel between compact-picture points $x$ and $y$:

$$
K_f(x,y)
=\int_{Z_k\backslash T_k}\xi(t)\delta_B(t)^{1/2}
\left(\int_{N_k}f(x^{-1}tny)\,dn\right)dt.
\tag{12.2}
$$

The quotient by $Z_k$ is necessary: the two central transformation laws make the integrand
descend, whereas an integral over all of $T_k$ would contain an infinite central factor. The
power $\delta_B^{1/2}$ is also exact. In the coordinates $tnk$, the Jacobian from moving $t$
past $n$ cancels the $\delta_B^{-1}$ in the usual $ntk$ Iwasawa formula, leaving the
half-density of normalized induction.

Thus (12.1) implies

$$
I_k(\xi)(f)=0
\tag{12.3}
$$

whenever the convolution operator is defined. If $f$ is compactly supported modulo the center,
fixed compact-type matrix entries are entire Laurent or Mellin transforms of compactly
supported data, so (12.3) holds for every quasicharacter. For an archimedean Schwartz function,
the assertion needed here is on the unitary principal axis, where the Schwartz algebra acts
continuously on tempered induction and Fubini is valid. One must not identify that honest
tempered operator with a regularized operator on every nonunitary principal series: at a
reducibility point the latter can contain the very discrete series from which $f$ was formed.
This distinction will matter in Chapter 13.

### 12.2 Nonarchimedean supercuspidal coefficients

Let $k$ be nonarchimedean and let $\sigma$ be an irreducible unitary supercuspidal representation with central character $\omega_k^{-1}$. Choose smooth vectors $u$ and $\lambda$ and form a matrix coefficient

$$
c(g)=\lambda(\sigma(g)u).
\tag{12.4}
$$

It is compactly supported modulo the center. Its unipotent averages vanish. Indeed, for fixed
$x,y,t$, integration is over a compact subset of $N_k$. Put
$u'=\sigma(y)u$ and $\lambda'=\lambda\circ\sigma(x^{-1}t)$. The integral becomes

$$
\int_{N_k}\lambda'(\sigma(n)u')\,dn.
$$

It is invariant under replacing $u'$ by $\sigma(n_0)u'$ and therefore factors through the $N_k$-coinvariants
of $\sigma$. The local rank-one theory proves that a supercuspidal representation has zero
Jacquet quotient. Hence the functional is zero. Left and right translates of a coefficient are
again coefficients, proving (12.1) with all its quantifiers.

After adjusting by the central character and taking a finite linear combination of coefficients, one obtains a nonzero strongly cuspidal test function with any desired sufficiently small compact-open invariance carried by $\sigma$. Such functions are the most robust finite-place choice: they kill the induced representation itself, not just its character distribution.

The hypothesis “supercuspidal” cannot be weakened to “irreducible.” A principal-series coefficient has a nonzero Jacquet quotient and generally a nonzero unipotent average.

### 12.3 Archimedean discrete-series coefficients

Let $k=\mathbf R$ and let $D$ be a discrete-series representation of
$\mathrm{GL}_2(\mathbf R)$ with central character $\omega_k^{-1}$. Its compact-finite matrix
coefficients are square-integrable modulo the center and belong to the invariant
Harish--Chandra Schwartz space. They are strongly cuspidal.

Here is the rank-one proof of the last assertion. For a compact-finite coefficient $c$, the
integral

$$
c_N(g)=\int_{N_k}c(n g)\,dn
$$

converges absolutely by the explicit discrete-series coefficient estimates. Compact finiteness
and the Casimir equation make $c_N(a(r)k)$ a finite sum of exponential-polynomial functions of
$\log r$; these are obtained by inserting the two compact-weight ladders into the rank-one
radial differential equation. A nonzero term has one of the boundary exponents of the
principal series with the same infinitesimal character. Multiplied by the Iwasawa density, its
square has a nonintegrable tail. Since $c$ is square-integrable modulo the center, Fubini and
Cauchy--Schwarz on finite truncations force every such coefficient to vanish. Thus $c_N=0$.

The same estimate applies to all invariant derivatives. Approximate arbitrary smooth vectors
by compact-finite vectors in the smooth topology; the uniform Schwartz bounds pass the
unipotent integral to the limit. Left and right translates of a matrix coefficient are smooth
coefficients of the same representation, so applying the result to
$n\mapsto c(x^{-1}tny)$ proves (12.1).

The same argument applies to a finite linear combination of such coefficients. In particular,
after multiplication by the formal degree, a conjugate diagonal coefficient is the usual
rank-one projector on $D$ and is still strongly cuspidal. This does not contradict its nonzero
action on $D$: the vanishing statement (12.3) is being used on unitary principal series, while
$D$ occurs inside a principal series only at a nonunitary reducibility parameter where
convolution by this noncompact Schwartz coefficient is not the same operation as formal
meromorphic regularization.

At a complex place $\mathrm{GL}_2(\mathbf C)$ has no discrete series modulo center, so this
construction is unavailable. One then uses a nonarchimedean supercuspidal coefficient if a
strongly cuspidal place is required.

Limits of discrete series require care: their coefficients lie at the square-integrability boundary and need not satisfy the same integrable constant-term statement without an additional cancellation. They are not silently included.

### 12.4 The weaker trace-level condition

For some applications it is enough that induced traces vanish. Define the local parabolic transform

$$
f^{B}(t)
=\delta_B(t)^{1/2}
\int_{K_k}\int_{N_k}f(k^{-1}tnk)\,dn\,dk.
\tag{12.5}
$$

The product $\xi(t)f^B(t)$ descends to $Z_k\backslash T_k$ for inducing data of central
character $\omega_k$. Iwasawa integration and the compact-picture trace give

$$
\operatorname{tr}I_k(\xi)(f)
=\int_{Z_k\backslash T_k}\xi(t)f^B(t)\,dt.
\tag{12.6}
$$

Hence $f^B=0$ kills the trace of every induced representation for which the operator is
defined. It also kills every one-dimensional character trace. Indeed, average
$g\mapsto f(g)\eta(\det g)$ over conjugation by $K_k$, apply Iwasawa integration in $tnk$
coordinates, and obtain the Mellin integral of $f^B$ against $t\mapsto\eta(\det t)$.

Strong cuspidality implies $f^B=0$, but the converse need not hold: averaging over $K_k$ can
cancel a nonzero operator kernel. Formula (12.5) is sufficient for an ordinary induced-character
trace or a one-dimensional residual trace. It is not sufficient for a regularized expression
with a scattering operator beside $I_k(\xi)(f)$. The theorem in Chapter 13 uses the stronger
condition and therefore proves actual operator vanishing on the noncuspidal span.

## 13. Annihilation of every noncuspidal contribution

### 13.1 Factorizable global tests

Let

$$
f=\bigotimes_vf_v
\tag{13.1}
$$

be a smooth factorizable test function on $Z(\mathbf A)\backslash G(\mathbf A)$ with the inverse central transformation needed to act on $L^2_\omega$. Assume that at one place $v_0$, the factor $f_{v_0}$ is strongly cuspidal. At almost every finite place take the normalized maximal-compact idempotent.
Here “idempotent” means the central-character extension supported on $Z_vK_v$, normalized to
act as the identity on the unramified $K_v$-fixed line; the ordinary characteristic function of
$K_v$ alone would not have the required central transformation.

For a factorizable induced representation,

$$
I(\chi,s)(f)
=\bigotimes_v I_v(\chi_v,s)(f_v).
\tag{13.2}
$$

On the unitary axis the $v_0$ factor is zero by (12.3), so

$$
I(\chi,s)(f)=0
\tag{13.3}
$$

for every unitary inducing datum and $s=it$. If $f_{v_0}$ is compactly supported modulo the
center, the same identity holds as a meromorphic finite-type operator family for every $s$.
For an archimedean Schwartz coefficient we make no such off-axis identification; the unitary
axis is exactly what the continuous automorphic spectrum requires.

This factorization is why one cuspidal place suffices. No compatibility among the other local factors is needed beyond the ordinary restricted-product and central-character conditions.

### 13.2 Vanishing on Eisenstein series and wave packets

Suppose first that the strongly cuspidal factor is compactly supported modulo the center. Right
convolution then commutes with the rational-line sum in the convergence chamber:

$$
R(f)E(g,f_s)
=E(g,I(\chi,s)(f)f_s).
\tag{13.4}
$$

Absolute convergence justifies moving the convolution integral through the sum. By (13.3), the right side is zero. Both sides continue meromorphically, so

$$
R(f)E(g,f_s)=0
\tag{13.5}
$$

throughout the required strip.

For an archimedean Schwartz coefficient, begin instead on the unitary axis after truncation.
The Harish--Chandra Schwartz estimates, the polynomial vertical bounds of Chapter 8, and the
rapid decrease of the packet coefficient justify convolution with a wave packet and Fubini.
Applying the factored unitary operator (13.3) inside the packet gives zero. This route does not
claim a pointwise convolution of the non-square-integrable family in the absolute-convergence
chamber.

Let $W(g)=\int_{\mathbf R}E(g,f_{it})a(t)\,dt$ be a wave packet with rapidly decreasing $a$.
Polynomial vertical bounds permit Fubini, and either of the preceding arguments gives

$$
R(f)W=0.
\tag{13.6}
$$

Thus every continuous contribution in Theorem 11.1 is annihilated as a vector, not merely assigned trace zero.

### 13.3 Vanishing on residues

When the strongly cuspidal factor is compactly supported modulo the center, take residues in
(13.5): bounded convolution commutes with the finite Laurent coefficient, giving

$$
R(f)\operatorname*{Res}_{s=s_0}E(g,f_s)=0.
\tag{13.7}
$$

There is a proof valid for both finite and archimedean strongly cuspidal factors. On the residual
line, convolution is multiplication by

$$
\prod_v\int_{Z_v\backslash G_v}f_v(g_v)\eta_v(\det g_v)\,dg_v.
\tag{13.8}
$$

At a compact-mod-center place these are ordinary quotient integrals. For an archimedean
Harish--Chandra Schwartz coefficient, (13.8) means the compact-picture Schwartz-algebra action:
average over $K_{v_0}$ and $N_{v_0}$ first and then take the outer torus Mellin integral. This
order is essential at the lowest discrete-series weight, where the absolute group integral of a
matrix coefficient need not converge. The inner average is $f_{v_0}^B=0$, so the local scalar
is zero before any outer integration. Thus the residual operator itself is zero. This direct
proof is necessary for an archimedean Schwartz coefficient, because it does not pass through a
regularized nonunitary principal-series operator.

If only the weaker condition $f_{v_0}^B=0$ is assumed, (13.8) still shows that every residual
line is annihilated: on a one-dimensional representation trace zero and operator zero are the
same assertion. What is lost is operator vanishing on the continuous induced representations.

### 13.4 The cuspidal-test theorem

**Theorem 13.1.** Let $F$ be a number field and $\omega$ a unitary idele class character. Let $f=\otimes_vf_v$ be a factorizable smooth test function of the compatible central character. Suppose one local factor is strongly cuspidal in the sense of (12.1). Then:

1. $R(f)$ acts by zero on every unitary rank-one induced representation with central character
   $\omega$;
2. $R(f)$ annihilates every unitary Eisenstein wave packet;
3. $R(f)$ annihilates every residual character $\eta\circ\det$ with $\eta^2=\omega$;
4. consequently $R(f)$ vanishes on the full noncuspidal closed subspace generated by the
   pseudo-Eisenstein series of Theorem 11.1.

If the strongly cuspidal factor is compactly supported modulo the center, $R(f)$ additionally
annihilates every Eisenstein series in the entire required meromorphic family.

**Proof.** Local kernel formula (12.2) on the unitary axis proves the first assertion. Restricted
tensor factorization gives (13.3), and integration inside genuine $L^2$ wave packets gives the
second. Formula (13.8) gives the third, and the closed-span classification gives the fourth.
For a compact-mod-center factor, convolution through the Eisenstein sum and meromorphic
continuation give the final additional assertion. $\square$

**Corollary 13.2.** Under the weaker hypothesis $f_{v_0}^B=0$, the ordinary character trace of
every unitary induced representation and the operator on every residual character vanish.

This weaker statement must not be substituted into a regularized continuous trace containing a
scattering operator next to $I(\chi,it)(f)$: trace zero for the last factor does not force the
trace of its product with another operator to vanish. Strong cuspidality is preferable because
it makes the induced operator itself zero.

## 14. Consequences, failure modes, and final synthesis

### 14.1 Consequences for later trace arguments

A global kernel built from a factorizable test with one strongly cuspidal local factor has no noncuspidal spectral contribution. What remains is the already established discrete cuspidal sum. The conclusion does not depend on calculating scattering determinants, continuous multiplicities, or a universal measure on the unitary dual.

At a finite place, a supercuspidal coefficient supplies the required factor. At a real place, a discrete-series coefficient can do the same. The other local factors may impose level, Hecke, or matching conditions independently. This flexibility is the practical value of the one-place principle.

The residual classification also prevents a common oversight. Killing the continuous integral is not enough unless residues are checked. Here residues are explicit one-dimensional determinant characters, and strong cuspidality kills them automatically.

### 14.2 Failure modes and their corrections

Several plausible shortcuts fail.

**Using unnormalized induction.** Then the reflection is displaced and the convergence boundary is mislabelled. The half-density in (3.1) places the unitary axis at $\operatorname{Re}(s)=0$.

**Multiplying local integrals in the local chamber.** Local convergence for $\operatorname{Re}(s)>0$ does not imply global convergence. The unramified Euler product requires $\operatorname{Re}(s)>1/2$.

**Forgetting the different.** Self-dual finite measures have integer-ring volume $q_v^{-d_v/2}$. Those finitely many factors belong in the finite correction.

**Using the direct completion in a symmetric composition formula.** Its functional equation contains a conductor–discriminant power. The symmetric completion $\Xi$ is what makes (7.8) exact.

**Inferring global poles from local reducibility.** A global residue occurs only under the character identity $\mu|\cdot|^{2s_0}=|\cdot|$.

**Calling every residue cuspidal.** The residue (9.8) has nonzero constant term. It is square-integrable but noncuspidal.

**Using total integral zero as a cuspidal test.** This removes at most one character. Strong cuspidality removes the entire induced channel.

**Checking only induced traces when operator vanishing is needed.** The averaged transform (12.5) controls traces; the two-sided condition (12.1) controls operators.

**Regularizing an archimedean coefficient off the unitary axis.** A discrete-series coefficient
acts honestly on tempered principal series, but at a nonunitary reducibility point a formal
continuation need not agree with convolution on a discrete constituent. The continuous spectrum
is killed on the unitary axis, and determinant residues are killed directly by (13.8).

**Invoking finite volume to justify unitary Eisenstein integrals.** Individual unitary Eisenstein series are not square-integrable. Rapidly decreasing wave packets and truncation provide the correct objects.

### 14.3 The complete implication chain

The argument can be summarized without suppressing any essential step:

$$
\begin{aligned}
&\text{compact unipotent quotient}
+\text{rank-one Bruhat decomposition}\\
&\qquad\Longrightarrow
E_N=f_s+M(s)f_s,\\
&\text{self-dual product measure}
+\text{restricted tensor sections}\\
&\qquad\Longrightarrow
M(s)=\bigotimes_vM_v(s),\\
&\text{unramified shell calculation}
+\text{one-dimensional Hecke theory}\\
&\qquad\Longrightarrow
\text{continuation, reflection, and the pole criterion},\\
&\text{two-dimensional Poisson summation}
+\text{zero-orbit analysis}\\
&\qquad\Longrightarrow
\operatorname*{Res}E=c\,\eta\circ\det,\\
&\text{pseudo-Eisenstein unfolding}
+\text{Mellin inversion}\\
&\qquad\Longrightarrow
\text{continuous wave packets plus determinant residues},\\
&\text{one strongly cuspidal local factor}
+\text{tensor factorization}\\
&\qquad\Longrightarrow
\text{annihilation of every noncuspidal contribution}.
\end{aligned}
\tag{14.1}
$$

Every arrow has a distinct hypothesis. Bruhat decomposition determines the number of constant-term exponents; measure normalization makes factorization exact; Poisson summation supplies continuation; zero orbits supply residues; Mellin inversion classifies packets; local cuspidality supplies annihilation.

### 14.4 Conclusion

The noncompact direction of the global $\mathrm{GL}_2$ quotient is governed by a compact unipotent average and a single height variable. Normalized induction turns pure height powers into a unitary family, while rational-line summation makes them automorphic. The two rational Bruhat cells force a two-term constant term, and the open cell produces the global intertwining operator.

Self-dual adelic measure makes that operator a genuine product of local integrals. The spherical local calculation identifies its Euler tail as a ratio of Hecke factors; the finite exceptional places carry exactly the ramification, archimedean, and different corrections. Poisson summation on two-dimensional adelic space continues the family, reflects $s$ to $-s$, and shows that the only pole crossed on the way to the unitary axis comes from a zero orbit. Its residue is the determinant character $\eta\circ\det$ with $\eta^2=\omega$.

Pseudo-Eisenstein series then give the precise noncuspidal classification needed here. Mellin inversion expresses their compact height profiles as unitary Eisenstein wave packets, and contour motion adds only the one-dimensional residues. This is the whole constant-term channel in rank one.

Finally, a strongly cuspidal local test function has zero kernel on every unitary parabolically
induced representation. One such factor in a global tensor product therefore kills every
unitary Eisenstein wave packet, while its parabolic transform kills every determinant residue.
If the factor is compactly supported modulo the center, the same zero continues through the
whole required meromorphic family. The continuous and residual terms disappear for a local
reason whose global force comes from factorization. What remains is the discrete cuspidal
contribution, isolated without constructing a general spectral decomposition of the full
automorphic quotient.
