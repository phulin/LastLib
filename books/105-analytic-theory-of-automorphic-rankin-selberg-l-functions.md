# Analytic Theory of Automorphic Rankin–Selberg L-functions

## Contents

1. [The analytic problem](#1-the-analytic-problem)
   - [What remains after unfolding](#11-what-remains-after-unfolding)
   - [Standing hypotheses](#12-standing-hypotheses)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [The main theorem](#14-the-main-theorem)
2. [Canonical local factors](#2-canonical-local-factors)
   - [The zeta ideal at a finite place](#21-the-zeta-ideal-at-a-finite-place)
   - [The unramified calculation](#22-the-unramified-calculation)
   - [Compatibility with Weil–Deligne factors](#23-compatibility-with-weildeligne-factors)
   - [Archimedean factors](#24-archimedean-factors)
   - [Duality, additive characters, and conductors](#25-duality-additive-characters-and-conductors)
3. [The global Euler product](#3-the-global-euler-product)
   - [Complete and incomplete products](#31-complete-and-incomplete-products)
   - [Absolute convergence in the initial half-plane](#32-absolute-convergence-in-the-initial-half-plane)
   - [Independence from test data](#33-independence-from-test-data)
   - [Twists and contragredients](#34-twists-and-contragredients)
4. [Continuation and the polar divisor](#4-continuation-and-the-polar-divisor)
   - [The Eisenstein pairing](#41-the-eisenstein-pairing)
   - [Continuation of the canonical function](#42-continuation-of-the-canonical-function)
   - [Residues as invariant pairings](#43-residues-as-invariant-pairings)
   - [The exact pole criterion](#44-the-exact-pole-criterion)
   - [Removing the poles](#45-removing-the-poles)
5. [The functional equation](#5-the-functional-equation)
   - [Local gamma factors](#51-local-gamma-factors)
   - [The global product formula](#52-the-global-product-formula)
   - [Conductor and root number](#53-conductor-and-root-number)
   - [The completed equation](#54-the-completed-equation)
   - [Consistency checks](#55-consistency-checks)
6. [Finite order and Mellin control](#6-finite-order-and-mellin-control)
   - [Why continuation is not yet a bound](#61-why-continuation-is-not-yet-a-bound)
   - [A Mellin-transform lemma](#62-a-mellin-transform-lemma)
   - [Finite order](#63-finite-order)
   - [Uniformity on compact strips](#64-uniformity-on-compact-strips)
7. [Vertical bounds](#7-vertical-bounds)
   - [Rapid decay of completed integrals](#71-rapid-decay-of-completed-integrals)
   - [Eliminating local correction factors](#72-eliminating-local-correction-factors)
   - [Polynomial bounds for the finite part](#73-polynomial-bounds-for-the-finite-part)
   - [A fixed-data convexity bound](#74-a-fixed-data-convexity-bound)
8. [Positivity of the self-convolution](#8-positivity-of-the-self-convolution)
   - [Local Schur positivity](#81-local-schur-positivity)
   - [Global nonnegative coefficients](#82-global-nonnegative-coefficients)
   - [A positive residue](#83-a-positive-residue)
   - [Consequences without a Tauberian theorem](#84-consequences-without-a-tauberian-theorem)
9. [Logarithmic derivatives and the boundary line](#9-logarithmic-derivatives-and-the-boundary-line)
   - [Prime-power coefficients](#91-prime-power-coefficients)
   - [The singularity at one](#92-the-singularity-at-one)
   - [Cross-term domination](#93-cross-term-domination)
   - [Landau's positivity lemma](#94-landaus-positivity-lemma)
10. [Deleting local factors](#10-deleting-local-factors)
    - [Local regularity at one](#101-local-regularity-at-one)
    - [Stability of pole order](#102-stability-of-pole-order)
    - [What can fail without unitarity](#103-what-can-fail-without-unitarity)
11. [The analytic multiplicity criterion](#11-the-analytic-multiplicity-criterion)
    - [Order of the incomplete product](#111-order-of-the-incomplete-product)
    - [The pole-comparison principle](#112-the-pole-comparison-principle)
    - [Hecke data and the analytic handoff](#113-hecke-data-and-the-analytic-handoff)
    - [Sparse exceptional sets](#114-sparse-exceptional-sets)
12. [Examples and normalization audits](#12-examples-and-normalization-audits)
    - [Unramified representations](#121-unramified-representations)
    - [A special local component](#122-a-special-local-component)
    - [Unitary twists](#123-unitary-twists)
    - [A failed diagonal integral](#124-a-failed-diagonal-integral)
13. [The analytic package](#13-the-analytic-package)
    - [Dependency closure](#131-dependency-closure)
    - [The reusable criterion](#132-the-reusable-criterion)
    - [Conclusion](#133-conclusion)

## 1. The analytic problem

### 1.1 What remains after unfolding

Book 104 constructed the global Whittaker model for cuspidal representations of
$\mathrm{GL}_2$, unfolded the three-variable Rankin–Selberg integral, calculated its
unramified factor, and related its possible residues to invariant pairings. Those results
produce a meromorphic family of integrals. They do not, by themselves, settle every analytic
question about the canonical $L$-function.

There are four remaining transitions. First, a particular global integral depends on local
Whittaker vectors and on a Schwartz function, whereas the $L$-function should depend only on
the representations. One must remove all correction factors without accidentally dividing by
a function that vanishes. Second, a functional equation for factorizable integrals must be
converted into an intrinsic equation whose local epsilon factors use one convention at every
place. Third, meromorphic continuation must be strengthened to finite order and to bounds in
vertical strips. Finally, positivity must be formulated at the level of Dirichlet coefficients,
where it can control a boundary singularity and distinguish a representation from every
nondual partner.

These transitions are the subject of this book. The guiding principle is that an Euler product
has three simultaneous realizations:

$$
\begin{array}{c}
\text{local zeta ideals}\\
\downarrow\\
\text{global Euler product}
\end{array}
\qquad =\qquad
\begin{array}{c}
\text{unfolded Whittaker integral}\\
\downarrow\\
\text{Eisenstein pairing}
\end{array}
\qquad =\qquad
\begin{array}{c}
\text{Mellin transform}\\
\downarrow\\
\text{vertical estimates}.
\end{array}
$$

The first realization fixes the local factors, the second supplies continuation and residues,
and the third supplies growth. None may be silently replaced by another outside the region in
which their equality has been proved.

### 1.2 Standing hypotheses

Let $F$ be a number field, $\mathbf A=\mathbf A_F$, and $G=\mathrm{GL}_2$. Let
$\pi$ and $\pi'$ be irreducible cuspidal automorphic representations of $G(\mathbf A)$ with
unitary central characters $\omega$ and $\omega'$. Their contragredients are
$\widetilde\pi$ and $\widetilde\pi'$. We write $[G]$ for

$$
Z(\mathbf A)G(F)\backslash G(\mathbf A)
$$

whenever the integrand is central invariant. All cusp forms used below are smooth, finite at
infinity under a maximal compact subgroup, and fixed by a compact open subgroup at the finite
places. Book 104 proves the rapid decrease and Whittaker factorization required for all
unfoldings in this volume.

Fix the global additive character $\psi:F\backslash\mathbf A\to\mathbf C^\times$ and the
product of its local self-dual measures. At a finite place $v$, write $q_v$ for the residue
cardinality and choose geometric Frobenius $\Phi_v$. Thus

$$
|\varpi_v|_v=q_v^{-1},\qquad |\Phi_v|=q_v^{-1},
$$

and local reciprocity sends $\varpi_v$ to $\Phi_v$. These are exactly the conventions of
Book 80. They force an unramified eigenvalue $\alpha$ to contribute
$(1-\alpha q_v^{-s})^{-1}$.

At almost every finite $v$, both representations are unramified. Write their Satake parameters
as

$$
A_v=\{\alpha_{1,v},\alpha_{2,v}\},\qquad
B_v=\{\beta_{1,v},\beta_{2,v}\}.
$$

The unordered sets, rather than an ordering, are intrinsic. Their products are the values of
the central characters at $\varpi_v$.

### 1.3 The normalization ledger

The entire book uses the following choices.

$$
\begin{array}{c|c}
\text{object}&\text{normalization}\\ \hline
\text{finite Frobenius}&\text{geometric}\\
\text{local reciprocity}&\operatorname{rec}_v(\varpi_v)=\Phi_v\\
\text{absolute value}&|\varpi_v|_v=q_v^{-1}\\
\text{Fourier transform}&\widehat f(y)=\int f(x)\psi_v(xy)\,dx\\
\text{additive Haar measure}&\text{self-dual for }\psi_v\\
\text{Whittaker signs}&\psi_v\text{ for }\pi_v,\ \psi_v^{-1}\text{ for }\pi'_v\\
\text{Rankin--Selberg weight}&|\det g|_v^s\\
\text{functional-equation center}&s=\tfrac12.
\end{array}
$$

The opposite Whittaker signs make their product descend to $N(F_v)\backslash G(F_v)$. The
power $|\det g|^s$ then produces the four unramified factors

$$
\prod_{i,j=1}^2(1-\alpha_{i,v}\beta_{j,v}q_v^{-s})^{-1}.
$$

On a Weil–Deligne parameter $D=(r,N)$, Book 80 defines

$$
L(s,D)=\det\left(1-q_v^{-s}r(\Phi_v)\mid(\ker N)^{I_v}\right)^{-1}
$$

and

$$
\gamma(s,D,\psi_v)=\epsilon(s,D,\psi_v)
\frac{L(1-s,D^\vee)}{L(s,D)}.
$$

Our representation-theoretic local factors will be compared with these formulas, not with a
second Frobenius or reciprocity convention.

### 1.4 The main theorem

Here is the analytic package to be proved. The notation $\Lambda$ includes all finite and
archimedean local $L$-factors in the normalization just fixed.

**Theorem 1.1 (analytic Rankin–Selberg theorem).** Let $\pi,\pi'$ be unitary cuspidal
automorphic representations of $\mathrm{GL}_2(\mathbf A_F)$.

1. The Euler product $L_f(s,\pi\times\pi')$ converges absolutely for
   $\operatorname{Re}(s)>1$, and the completed function
   $\Lambda(s,\pi\times\pi')$ continues meromorphically to $\mathbf C$.
2. There is a root number $W(\pi\times\pi')$ of absolute value one and a positive conductor
   $Q(\pi\times\pi')$ such that

   $$
   \Lambda(s,\pi\times\pi')
   =W(\pi\times\pi')Q(\pi\times\pi')^{1/2-s}
   \Lambda(1-s,\widetilde\pi\times\widetilde\pi').
   $$

3. The completed function is entire unless, for some $u\in\mathbf R$,

   $$
   \pi'\simeq\widetilde\pi\otimes|\det|^{iu}.
   $$

   In that exceptional case its only poles are simple and occur at $s=-iu$ and $s=1-iu$.
4. After these possible poles are removed, the completed function has finite order and is
   rapidly decreasing in every closed vertical strip. The finite part has polynomial vertical
   growth there.
5. For a finite set $S$ containing all ramified and archimedean places,

   $$
   L^S(s,\pi\times\widetilde\pi)
   =\sum_{\mathfrak a}b_\pi^S(\mathfrak a)(N\mathfrak a)^{-s}
   $$

   has $b_\pi^S(\mathfrak a)\geq0$ and a simple pole at $s=1$.
6. For unitary cuspidal $\rho$, the polar order at $s=1$ satisfies

   $$
   \operatorname{pord}_{s=1}L^S(s,\rho\times\widetilde\pi)
   =\begin{cases}1,&\rho\simeq\pi,\\0,&\rho\not\simeq\pi,
   \end{cases}
   $$

   where $\operatorname{pord}_{s_0}f=\max\{0,-\operatorname{ord}_{s_0}f\}$. This is the
   analytic criterion used in the next volume's multiplicity-one argument. No nonvanishing
   claim is made for a holomorphic cross product at $s=1$.

The proof occupies the remainder of the book. The important point is not merely that each
assertion is true, but that all six use the same local factors.

There are several tempting shortcuts that the proof must avoid. Continuation of one integral
does not continue the normalized generator of every local zeta ideal if the chosen correction
factor has zeros. A formal product of local functional equations is meaningless until all but
finitely many gamma factors are shown to equal one and the remaining product is tied to a
global Fourier identity. A pole visible in an Eisenstein series can disappear after pairing
with cusp forms, so its residue must be calculated rather than merely located. Finally,
positivity of the Petersson norm does not automatically imply coefficientwise positivity of an
Euler product; the latter requires a separate local identity.

The proof is organized to close these four gaps in order. Chapter 2 makes the local factor
canonical and compares its normalization with tensor parameters. Chapter 3 uses a finite
Bézout family to pass between local generators and global integrals. Chapters 4 and 5 extract
the polar divisor and functional equation from Eisenstein residues and Fourier transform.
Chapters 6 and 7 revisit the integral as a Mellin transform, because growth cannot be deduced
from continuation alone. Chapters 8 and 9 prove two forms of positivity. Chapter 10 justifies
deleting finitely many local factors, and Chapter 11 packages the result as the analytic
separation criterion. The examples in Chapter 12 are normalization tests: each would fail in a
detectable way if Frobenius, monodromy, the central Schwartz variable, or the center of the
functional equation had been chosen inconsistently.

## 2. Canonical local factors

### 2.1 The zeta ideal at a finite place

Let $K=F_v$ be nonarchimedean. For generic irreducible admissible representations
$\pi_v,\pi'_v$, Whittaker functions

$$
W\in\mathcal W(\pi_v,\psi_v),\qquad
W'\in\mathcal W(\pi'_v,\psi_v^{-1}),
$$

and $\Phi\in\mathcal S(K^2)$, Book 104 defines

$$
\Psi_v(s,W,W',\Phi)
=\int_{N(K)\backslash G(K)}
W(g)W'(g)\Phi((0,1)g)|\det g|^s\,dg.
\tag{2.1}
$$

The integrals are rational functions of $X=q_v^{-s}$. As the data vary they form a nonzero
fractional ideal

$$
\mathcal Z(\pi_v,\pi'_v)
\subset \mathbf C[X,X^{-1}].
$$

Because this Laurent polynomial ring is a principal ideal domain, there is a unique generator
of the form $P(X)^{-1}$ with $P(0)=1$. We define

$$
L_v(s,\pi_v\times\pi'_v)=P(q_v^{-s})^{-1}.
\tag{2.2}
$$

The normalization $P(0)=1$ matters: multiplication by $cX^m$ does not change a fractional
ideal, so without it the generator would be ambiguous.

Two consequences will be used repeatedly.

**Proposition 2.1.** Every local integral has the form

$$
\Psi_v(s,W,W',\Phi)
=L_v(s,\pi_v\times\pi'_v)P_{W,W',\Phi}(q_v^{-s})
\tag{2.3}
$$

with $P_{W,W',\Phi}$ a Laurent polynomial. Moreover, finitely many triples of data may be
chosen so that their correction polynomials generate the unit ideal.

**Proof.** The first assertion is the definition of the generated fractional ideal. For the
second, the ideal generated by all correction polynomials is the whole Laurent polynomial
ring; otherwise their common nonunit divisor would enlarge the normalized denominator in
(2.2). An ideal is, by definition, generated by finite sums of its elements. Hence finitely
many correction polynomials $P_1,\ldots,P_m$ and Laurent polynomials $A_1,\ldots,A_m$ satisfy

$$
A_1P_1+\cdots+A_mP_m=1.
\tag{2.4}
$$

This finite Bézout identity is the device that later removes test-vector zeros. $\square$

One should not replace Proposition 2.1 by the assertion that one favorite integral always
equals the local factor. At ramified places a natural-looking vector can give zero. The family,
not a single member, is canonical.

### 2.2 The unramified calculation

Suppose both representations are unramified. Let $W^\circ,W'^\circ$ be the normalized spherical
Whittaker functions and $\Phi^\circ=\mathbf1_{\mathcal O_K^2}$. Book 104 calculates

$$
W^\circ(a(\varpi^m))=q^{-m/2}h_m(\alpha_1,\alpha_2),
$$

with the value zero for $m<0$, and similarly for $W'^\circ$. The root-coordinate sum is

$$
\sum_{m\geq0}h_m(\alpha_1,\alpha_2)
h_m(\beta_1,\beta_2)X^m
=\frac{1-\alpha_1\alpha_2\beta_1\beta_2X^2}
{\prod_{i,j}(1-\alpha_i\beta_jX)}.
\tag{2.5}
$$

The scalar-coordinate integral is

$$
(1-\alpha_1\alpha_2\beta_1\beta_2X^2)^{-1}.
\tag{2.6}
$$

Multiplying (2.5) and (2.6) proves

$$
\boxed{
L_v(s,\pi_v\times\pi'_v)
=\prod_{i,j=1}^2(1-\alpha_i\beta_jq^{-s})^{-1}.}
\tag{2.7}
$$

This calculation simultaneously fixes the half-power, the geometric Frobenius convention,
and the central Schwartz variable. The diagonal Whittaker integral without that variable has
the numerator in (2.5) and is not the degree-four $L$-factor.

### 2.3 Compatibility with Weil–Deligne factors

Whenever a local representation is described by its Frobenius-semisimple Weil–Deligne
parameter $D(\pi_v)$, define

$$
D_v=D(\pi_v)\otimes D(\pi'_v),
$$

where the tensor monodromy is $N\otimes1+1\otimes N'$. Compatibility means

$$
L_v(s,\pi_v\times\pi'_v)=L(s,D_v)
\tag{2.8}
$$

and the analogous equality for epsilon and gamma factors.

The point of (2.8) is not to import continuation from a parameter: it is to prove that the
analytic factor and the local-constant factor use the same normalization. The verification
reduces to the local building blocks.

For two unramified parameters, inertia and monodromy are trivial and Frobenius on the tensor
product has eigenvalues $\alpha_i\beta_j$. Book 80's determinant definition gives (2.7).

For a special block $\operatorname{Sp}_m(\rho)$, Book 80 gives

$$
L(s,\operatorname{Sp}_m(\rho))
=L\left(s+\frac{m-1}{2},\rho\right).
\tag{2.9}
$$

The same shift occurs in the Whittaker calculation because the normalized special
representation has diagonal exponents differing by $|\cdot|$ and its Whittaker function begins
with the $q^{-m/2}$ factor dictated by normalized induction. Thus passage from a reducible
principal series to its generic special constituent deletes precisely the factor removed by
$\ker N$ in Book 80's definition.

For a representation induced from a character of the Weil group of a finite extension,
Book 80 proves

$$
L_K(s,\operatorname{Ind}_{W_L}^{W_K}U)=L_L(s,U)
\tag{2.10}
$$

and the epsilon induction formula with its lambda constant. The local Whittaker integral obeys
the same induction identity: after the open-cell change of variables, the additive character
becomes $\psi_K\circ\operatorname{Tr}_{L/K}$ and the discrepancy for the trivial character is
exactly the same lambda constant. Rank-one Fourier uniqueness then identifies the two gamma
factors. Direct sums, twists, and special blocks exhaust the parameter calculations needed in
the present Rankin–Selberg theory; multiplicativity gives (2.8).

This argument also explains the hypotheses. One cannot compare to a parameter that has not
been attached to the representation. The analytic definition (2.2) remains valid for every
generic local representation, independently of such a description.

It is useful to make the block comparison explicit. If

$$
D(\pi_v)=\chi_1\oplus\chi_2,\qquad
D(\pi'_v)=\mu_1\oplus\mu_2
$$

have zero monodromy, then

$$
L(s,D_v)=\prod_{i,j=1}^2L(s,\chi_i\mu_j).
\tag{2.10a}
$$

Ramified character products simply contribute the factor one, exactly as unit orthogonality
removes their Mellin integrals. Thus (2.10a) includes ramified principal series, not only the
spherical calculation.

If $D(\pi_v)=\operatorname{Sp}_2(\chi)$ and
$D(\pi'_v)=\mu_1\oplus\mu_2$, then

$$
D_v=\operatorname{Sp}_2(\chi\mu_1)
\oplus\operatorname{Sp}_2(\chi\mu_2),
$$

so

$$
L(s,D_v)=L(s+1/2,\chi\mu_1)L(s+1/2,\chi\mu_2).
\tag{2.10b}
$$

When both parameters are special, the tensor product of the two length-two monodromy strings
has one string of length three and one of length one:

$$
\operatorname{Sp}_2(\chi)\otimes\operatorname{Sp}_2(\mu)
\simeq\operatorname{Sp}_3(\chi\mu)\oplus\operatorname{Sp}_1(\chi\mu).
\tag{2.10c}
$$

To prove this, take bases $e_0,e_1$ and $f_0,f_1$. Tensor monodromy sends
$e_i\otimes f_j$ to $e_{i-1}\otimes f_j+e_i\otimes f_{j-1}$, with negative indices
interpreted as zero. The vector $e_1\otimes f_1$ generates a length-three string, while
$e_1\otimes f_0-e_0\otimes f_1$ spans a complementary kernel line. Centered Frobenius
weights identify the two strings as displayed. Hence

$$
L(s,D_v)=L(s+1,\chi\mu)L(s,\chi\mu).
\tag{2.10d}
$$

For a dihedral parameter $D(\pi_v)=\operatorname{Ind}_{W_L}^{W_K}\theta$, multiplication in
the induced function model proves

$$
(\operatorname{Ind}_{W_L}^{W_K}\theta)\otimes U
\simeq\operatorname{Ind}_{W_L}^{W_K}(\theta\otimes U|_{W_L}).
\tag{2.10e}
$$

Combining (2.10e) with (2.10) reduces its tensor $L$-factor to rank one or to a direct sum over
$W_L$. The same reduction carries the epsilon factor, with Book 80's lambda constant on both
the parameter and zeta-integral sides. These formulas make concrete how monodromy and induction
alter the number, position, and phase of the local factors.

### 2.4 Archimedean factors

At an archimedean place, the local zeta integrals are Mellin transforms of smooth Whittaker
functions. Repeated use of the differential equations for a fixed infinitesimal character
reduces them to products of the two basic gamma functions

$$
\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2),
\qquad
\Gamma_{\mathbf C}(s)=2(2\pi)^{-s}\Gamma(s).
\tag{2.11}
$$

Thus there are shifts $\mu_{v,1},\ldots,\mu_{v,d_v}$, with $d_v=4$ over $\mathbf R$ when
counted in $\Gamma_{\mathbf R}$-degree and $d_v=4$ over $\mathbf C$ when counted in
$\Gamma_{\mathbf C}$-degree, such that

$$
L_v(s,\pi_v\times\pi'_v)
=\prod_{k=1}^{d_v}\Gamma_{F_v}(s+\mu_{v,k}).
\tag{2.12}
$$

Here repetitions are allowed, and a complex gamma factor may be replaced by the corresponding
pair of real gamma factors. The intrinsic normalization is the one for which the local
functional equation reflects $s$ to $1-s$.

For completeness, the Mellin reduction uses only integration by parts. If a radial Whittaker
component $f(y)$ satisfies an equation

$$
P(y\,d/dy)f(y)=y^rQ(y\,d/dy)f(y),
$$

then its Mellin transform $M_f(s)=\int_0^\infty f(y)y^s\,d^\times y$ satisfies a recurrence

$$
P(-s)M_f(s)=Q(-s-r)M_f(s+r).
$$

Rapid decrease at infinity and the finite exponent expansion at zero determine $M_f$ up to an
entire factor; the recurrence extracts exactly the gamma functions in (2.12). Varying the
$K_v$-finite vector makes the remaining entire factors generate the unit ideal in the ring of
polynomials in $s$. This is the archimedean analogue of Proposition 2.1.

For example, a real quasicharacter

$$
\chi_{\varepsilon,t}(x)=\operatorname{sgn}(x)^\varepsilon|x|^{it},
\qquad \varepsilon\in\{0,1\},
$$

has factor $\Gamma_{\mathbf R}(s+it+\varepsilon)$. If two real principal-series parameters
split as $\chi_1\oplus\chi_2$ and $\mu_1\oplus\mu_2$, their Rankin–Selberg factor is the
product of the four gamma functions attached to $\chi_i\mu_j$. This is the archimedean
counterpart of (2.10a).

A discrete-series parameter is a two-dimensional representation induced from a character of
$\mathbf C^\times$ to the real Weil group. Restricting a tensor product to
$\mathbf C^\times$ produces character products in conjugate pairs; induction back to the real
Weil group groups each pair into one $\Gamma_{\mathbf C}$ factor. This gives (2.12) without a
new convention. In every case tensoring by $|\cdot|^{iu}$ translates all four shifts by $iu$,
which confirms the global translation formula (3.10) at infinity.

### 2.5 Duality, additive characters, and conductors

The local functional equation of Book 104 defines

$$
\gamma_v(s,\pi_v\times\pi'_v,\psi_v)
=\epsilon_v(s,\pi_v\times\pi'_v,\psi_v)
\frac{L_v(1-s,\widetilde\pi_v\times\widetilde\pi'_v)}
{L_v(s,\pi_v\times\pi'_v)}.
\tag{2.13}
$$

At a finite place, compatibility with Book 80 gives

$$
\epsilon_v(s,\pi_v\times\pi'_v,\psi_v)
=W_vq_v^{-[a_v+n(\psi_v)4](s-1/2)},
\tag{2.14}
$$

where $a_v$ is the conductor exponent of the four-dimensional tensor parameter. For unitary
data, $|W_v|=1$.

If $\psi_{v,c}(x)=\psi_v(cx)$, the determinant-scaling rule of Book 80 gives

$$
\epsilon_v(s,\pi_v\times\pi'_v,\psi_{v,c})
=(\omega_v(c))^2(\omega'_v(c))^2
|c|_v^{4(s-1/2)}
\epsilon_v(s,\pi_v\times\pi'_v,\psi_v).
\tag{2.15}
$$

Indeed, the determinant of a tensor product $V\otimes V'$ is
$(\det V)^{\dim V'}(\det V')^{\dim V}$, which gives the two squares. Formula (2.15) is a
sensitive check: using arithmetic Frobenius or the inverse reciprocity convention would invert
the central-character factor.

Local duality gives

$$
\gamma_v(s,\pi_v\times\pi'_v,\psi_v)
\gamma_v(1-s,\widetilde\pi_v\times\widetilde\pi'_v,\psi_v^{-1})=1.
\tag{2.16}
$$

With the same additive character in both factors, the right side becomes the determinant at
$-1$. The distinction will disappear globally because $-1\in F^\times$ and the product of the
local determinant values is one.

## 3. The global Euler product

### 3.1 Complete and incomplete products

Define

$$
L_f(s,\pi\times\pi')=\prod_{v<\infty}L_v(s,\pi_v\times\pi'_v)
\tag{3.1}
$$

in a right half-plane, and

$$
L_\infty(s,\pi\times\pi')
=\prod_{v\mid\infty}L_v(s,\pi_v\times\pi'_v).
\tag{3.2}
$$

The completed function is

$$
\Lambda(s,\pi\times\pi')
=L_\infty(s,\pi\times\pi')L_f(s,\pi\times\pi').
\tag{3.3}
$$

If $S$ is a finite set of places containing the archimedean ones, put

$$
L^S(s,\pi\times\pi')
=\prod_{v\notin S}L_v(s,\pi_v\times\pi'_v).
\tag{3.4}
$$

The distinction is structural. Continuation and the functional equation naturally concern
$\Lambda$; comparison of almost all local components naturally concerns $L^S$.

### 3.2 Absolute convergence in the initial half-plane

We prove absolute convergence without assuming a pointwise bound for each Satake parameter.
For the self-pair $\pi\times\widetilde\pi$, choose conjugate Whittaker data. The unfolded
coefficients are nonnegative; their precise form is proved in Chapter 8. In the half-plane
$\sigma>1$, the defining Eisenstein series and the global pairing converge absolutely, so the
resulting nonnegative Dirichlet series converges.

For a cross pair, the unramified diagonal coefficient satisfies

$$
|h_m(A_v)h_m(B_v)|
\leq\frac12\bigl(|h_m(A_v)|^2+|h_m(B_v)|^2\bigr).
\tag{3.5}
$$

The scalar Euler factor is absolutely convergent at $2\sigma>2$. Applying Cauchy–Schwarz to
the ideal coefficients, and then the convergent self-pair series for $\pi$ and $\pi'$, proves
absolute convergence of the cross Dirichlet series for $\sigma>1$.

To pass from the Dirichlet series to the Euler product, expand the logarithm in a sufficiently
far right half-plane and dominate the prime-power traces by the two self-pairs. Monotone
convergence then carries the bound down to every $\sigma>1$. Finitely many ramified factors are
rational functions with constant term one and do not affect convergence away from their finite
set of poles. We have proved:

Here is the coefficient-level passage in more detail. At an unramified place the Cauchy identity
used later in (8.2) writes the degree-$m$ coefficient of the cross factor as

$$
c_v(m)=\sum_{\substack{\lambda\vdash m\\\ell(\lambda)\leq2}}
s_\lambda(A_v)s_\lambda(B_v).
$$

Therefore

$$
|c_v(m)|^2\leq
\left(\sum_{\lambda\vdash m}|s_\lambda(A_v)|^2\right)
\left(\sum_{\lambda\vdash m}|s_\lambda(B_v)|^2\right).
\tag{3.5a}
$$

For an ideal $\mathfrak a=\prod_v\mathfrak p_v^{m_v}$, multiply (3.5a) over $v$.
The two products on the right are exactly the self-pair coefficients
$b_\pi(\mathfrak a)$ and $b_{\pi'}(\mathfrak a)$. Thus

$$
|a_{\pi,\pi'}(\mathfrak a)|
\leq b_\pi(\mathfrak a)^{1/2}b_{\pi'}(\mathfrak a)^{1/2}.
\tag{3.5b}
$$

Summing with weight $(N\mathfrak a)^{-\sigma}$ and applying Cauchy–Schwarz proves convergence
of the cross Dirichlet series directly from the two self series. For logarithms, the analogous
inequality is applied to
$\operatorname{tr}(A_v^r)\operatorname{tr}(B_v^r)$ at every prime power. This avoids any
unproved individual estimate for $\alpha_{i,v}$ or $\beta_{j,v}$.

**Proposition 3.1.** Both $L_f(s,\pi\times\pi')$ and its Dirichlet series converge absolutely
and locally uniformly on $\operatorname{Re}(s)>1$.

Local uniformity implies holomorphy there. It also permits termwise logarithmic differentiation
on every smaller half-plane $\sigma\geq1+\delta$.

### 3.3 Independence from test data

Choose pure tensors $\phi\in\pi$, $\phi'\in\pi'$, and
$\Phi\in\mathcal S(\mathbf A^2)$. Book 104 proves, initially for $\sigma>1$,

$$
\mathcal I(s,\phi,\phi',\Phi)
=\prod_v\Psi_v(s,W_v,W'_v,\Phi_v).
\tag{3.6}
$$

At almost every place the local integral is the canonical local factor. Hence

$$
\mathcal I(s,\phi,\phi',\Phi)
=\Lambda(s,\pi\times\pi')C_{\phi,\phi',\Phi}(s),
\tag{3.7}
$$

where $C$ is a finite product of local correction functions.

Equation (3.7) does not authorize division by one chosen $C$. Instead choose finitely many
local data at each exceptional finite place as in Proposition 2.1 and finitely many
archimedean data as in Section 2.4. Tensoring the finite choices produces global integrals
$\mathcal I_1,\ldots,\mathcal I_M$ and holomorphic coefficient functions
$A_1,\ldots,A_M$ such that

$$
\boxed{
\Lambda(s,\pi\times\pi')
=\sum_{j=1}^MA_j(s)\mathcal I_j(s).}
\tag{3.8}
$$

In the initial half-plane this is just the product of the local Bézout identities. Both sides
then continue together. Thus the canonical function is recovered from a finite family of
integrals with no division and no artificial poles.

Conversely, (3.7) says every global integral is the canonical function times an entire local
correction. Together the two statements prove that continuation and poles found from the
family of integrals belong to $\Lambda$ itself.

### 3.4 Twists and contragredients

For a unitary Hecke character $\chi$, local diagonal covariance gives

$$
L(s,(\pi\otimes\chi)\times\pi')
=L(s,\pi\times(\pi'\otimes\chi)).
\tag{3.9}
$$

For a real number $u$,

$$
L(s,(\pi\otimes|\det|^{iu})\times\pi')
=L(s+iu,\pi\times\pi').
\tag{3.10}
$$

The identity follows place by place because every tensor Frobenius eigenvalue is multiplied by
$q_v^{-iu}$, while the same translation holds for archimedean Mellin transforms.

Duality sends the local factor to the reciprocal parameters:

$$
L_v(s,\widetilde\pi_v\times\widetilde\pi'_v)
=L_v(s,D_v^\vee).
\tag{3.11}
$$

No complex conjugation appears in (3.11) as an algebraic identity. For unitary
representations, however, $\widetilde\pi_v$ is the complex-conjugate unitary representation,
so the Satake multiset of the contragredient is the complex conjugate multiset. This is the
source of positivity in Chapter 8.

## 4. Continuation and the polar divisor

### 4.1 The Eisenstein pairing

Let $\eta=\omega\omega'$. Book 104 constructs the Eisenstein series
$E(g,\Phi,\eta,s)$ and proves

$$
\mathcal I(s,\phi,\phi',\Phi)
=\int_{[G]}\phi(g)\phi'(g)E(g,\Phi,\eta,s)\,dg.
\tag{4.1}
$$

The rapid decrease of the cusp forms makes the pairing continuous against every
moderate-growth coefficient of the Eisenstein series. The Eisenstein family is entire unless
$\eta$ is trivial on the norm-one idele class group. In the exceptional case there is a unique
$u\in\mathbf R$ with

$$
\eta=|\cdot|^{2iu},
\tag{4.2}
$$

and the only possible poles are simple poles at $s=-iu$ and $s=1-iu$.

This proves continuation of each $\mathcal I$, but the canonical continuation uses (3.8).

### 4.2 Continuation of the canonical function

**Theorem 4.1.** The completed function $\Lambda(s,\pi\times\pi')$ has meromorphic
continuation to $\mathbf C$. Its only possible poles are those in (4.2), and each is at most
simple.

**Proof.** Every integral on the right of (3.8) has the continuation and possible pole set just
described. Its coefficient $A_j(s)$ is entire. Hence their finite sum continues meromorphically
with no other poles and no larger pole order. In $\sigma>1$ the sum equals the canonical Euler
product, so uniqueness of meromorphic continuation proves the assertion. $\square$

The proof is deliberately family-valued. Dividing a single integral by a correction factor
could create a false pole at any zero of that factor.

### 4.3 Residues as invariant pairings

At the upper possible pole, the Eisenstein residue is

$$
\operatorname*{Res}_{s=1-iu}E(g,\Phi,\eta,s)
=c_F\widehat\Phi(0)|\det g|^{-iu},
\tag{4.3}
$$

with $c_F>0$. Therefore

$$
\operatorname*{Res}_{s=1-iu}\mathcal I(s,\phi,\phi',\Phi)
=c_F\widehat\Phi(0)
\int_{[G]}\phi(g)\phi'(g)|\det g|^{-iu}\,dg.
\tag{4.4}
$$

The last expression is a $G(\mathbf A)$-invariant bilinear pairing between
$\pi$ and $\pi'\otimes|\det|^{-iu}$. Indeed, right translation by $h$ in both variables and
then $g\mapsto gh^{-1}$ leaves the measure fixed; the determinant twist exactly compensates
the twist in the second representation.

An invariant bilinear pairing defines an intertwining map

$$
\pi'\otimes|\det|^{-iu}\longrightarrow\widetilde\pi.
\tag{4.5}
$$

If it is nonzero, irreducibility makes its kernel zero and its image nonzero, hence the map is
an isomorphism on every admissible compact type and therefore on the smooth representation.
Consequently (4.4) can be nonzero only if

$$
\pi'\simeq\widetilde\pi\otimes|\det|^{iu}.
\tag{4.6}
$$

Conversely, if (4.6) holds, the unitary inner product on $\pi$ supplies a nonzero pairing.
Choose paired nonzero vectors and choose $\Phi$ with $\widehat\Phi(0)>0$; then (4.4) is nonzero.

### 4.4 The exact pole criterion

**Theorem 4.2 (pole criterion).** The canonical completed function is entire unless (4.6)
holds for some real $u$. If (4.6) holds, it has simple poles at

$$
s=1-iu\qquad\text{and}\qquad s=-iu.
\tag{4.7}
$$

In particular,

$$
\Lambda(s,\pi\times\pi')\text{ has a pole at }s=1
\quad\Longleftrightarrow\quad
\pi'\simeq\widetilde\pi.
\tag{4.8}
$$

**Proof.** Theorem 4.1 gives the possible locations and simplicity. Section 4.3 proves that all
upper residues vanish unless (4.6), and produces data with a nonzero upper residue when (4.6)
holds. If the canonical function were regular there, every integral, being it times an entire
correction, would be regular, a contradiction. Thus the upper pole is genuine. The functional
equation proved in Chapter 5 reflects it to the lower point. Alternatively the lower
Eisenstein residue gives the same conclusion directly. $\square$

The use of a test function with nonzero residue does not make the pole test-data dependent. It
only detects a pole already belonging to the canonical function.

The simplicity assertion deserves emphasis. The Eisenstein constant term has only two Weyl
cells. After Poisson summation their zero-vector contributions are
$c/(s+iu)$ and $c'/(s-1+iu)$; every nonzero Fourier coefficient is entire. Pairing with two
cusp forms is a continuous linear operation on each vertical strip, so it cannot raise either
pole order. The finite Bézout sum (3.8) also cannot raise it. Thus no hidden double pole can
arise from multiplying local factors, even if several local Euler denominators happen to have
the same root.

When (4.6) holds, let $R_+$ and $R_-$ denote the residues at $1-iu$ and $-iu$. Taking residues
in the functional equation relates them by the nonzero scalar

$$
R_-=-W(\pi\times\pi')Q^{1/2+iu}
R_+(\widetilde\pi\times\widetilde\pi'),
$$

with the minus sign coming from the change of variable $1-s$. Hence one residue is nonzero if
and only if the other is. This gives a second proof that the lower possible pole cannot be
removed by cancellation.

### 4.5 Removing the poles

Define the polar polynomial

$$
p_{\pi,\pi'}(s)=
\begin{cases}
1,&\pi'\not\simeq\widetilde\pi\otimes|\det|^{iu}\text{ for all }u,\\
(s+iu)(s-1+iu),&\pi'\simeq\widetilde\pi\otimes|\det|^{iu}.
\end{cases}
\tag{4.9}
$$

The real number $u$ is unique. Indeed, two such values would give a nontrivial unitary
self-twist $|\det|^{i(u-u')}$; comparing central characters gives
$|\cdot|^{2i(u-u')}=1$, which on the positive idele module forces $u=u'$.

By Theorem 4.2,

$$
\Lambda^*(s,\pi\times\pi')
=p_{\pi,\pi'}(s)\Lambda(s,\pi\times\pi')
\tag{4.10}
$$

is entire. This is the function whose order and vertical behavior will be studied.

## 5. The functional equation

### 5.1 Local gamma factors

The local functional equation is

$$
\Psi_v(1-s,\widetilde W_v,\widetilde W'_v,\widehat\Phi_v)
=\gamma_v(s,\pi_v\times\pi'_v,\psi_v)
\Psi_v(s,W_v,W'_v,\Phi_v).
\tag{5.1}
$$

At a finite place rationality and local Whittaker uniqueness show that the proportionality
factor is independent of the data. At an archimedean place the same follows from uniqueness of
the continuous equivariant trilinear functional after meromorphic continuation.

Separating the canonical local $L$-factors defines $\epsilon_v$ by (2.13). At almost every
finite place all data are unramified, $n(\psi_v)=0$, $a_v=0$, and

$$
\epsilon_v(s,\pi_v\times\pi'_v,\psi_v)=1.
\tag{5.2}
$$

Thus the global product of local epsilon factors is finite.

### 5.2 The global product formula

The Eisenstein functional equation and the change
$g\mapsto{}^tg^{-1}$ give

$$
\mathcal I(s,\phi,\phi',\Phi)
=\mathcal I(1-s,\widetilde\phi,\widetilde\phi',\widehat\Phi).
\tag{5.3}
$$

For pure tensors, apply (5.1) at every place in the common convergence region. The two sides
of (5.3) differ by $\prod_v\gamma_v(s)$. Choose local data with nonzero integrals there. Hence

$$
\boxed{\prod_v\gamma_v(s,\pi_v\times\pi'_v,\psi_v)=1.}
\tag{5.4}
$$

Meromorphic continuation makes (5.4) an identity for all $s$.

The product is independent of the global additive character. Replacing $\psi$ by $\psi_c$
with $c\in F^\times$ multiplies the local factors by (2.15). Their product is one because the
central characters are trivial on $F^\times$ and $\prod_v|c|_v=1$.

### 5.3 Conductor and root number

At a finite place write (2.14). Multiplying over finite places gives a positive integer ideal
conductor

$$
\mathfrak q(\pi\times\pi')=\prod_{v<\infty}\mathfrak p_v^{a_v}
\tag{5.5}
$$

and its absolute norm

$$
Q_f=N_{F/\mathbf Q}\mathfrak q(\pi\times\pi').
\tag{5.6}
$$

The additive-conductor exponents cancel globally against the discriminant factors already
built into the self-dual archimedean normalization. This is the global form of Book 80's trace
formula $n(\psi\circ\operatorname{Tr})=en(\psi)+d$.

After fixing the gamma factors as in (2.12), the product of all monomial powers has the form

$$
\epsilon(s,\pi\times\pi')
=W(\pi\times\pi')Q(\pi\times\pi')^{1/2-s},
\tag{5.7}
$$

where $Q>0$. With conductor powers placed wholly in the finite epsilon factors, $Q=Q_f$ times
the fixed discriminant normalization determined by $F$ and the chosen $\Gamma_{\mathbf R}$ and
$\Gamma_{\mathbf C}$ conventions.

The conductor in (5.5) is the conductor of the tensor parameter, not the product of the two
individual conductor ideals. There is no degree-only formula for it, because equal wild breaks
can cancel in a tensor product. The definition remains exact:

$$
a_v=a\bigl(D(\pi_v)\otimes D(\pi'_v)\bigr),
\tag{5.8}
$$

with the monodromy correction included. For instance, two unramified parameters give $a_v=0$.
If $D(\pi_v)=\operatorname{Sp}_2(\chi)$ with $\chi$ unramified and $D(\pi'_v)=\mu$ is an
unramified character, then the tensor remains a length-two special block and $a_v=1$. If both
are unramified length-two special blocks, (2.10c) gives

$$
a_v=a(\operatorname{Sp}_3(\chi\mu))+a(\chi\mu)=2.
$$

If $\chi\mu$ is ramified, Book 80's block formula instead gives

$$
a(\operatorname{Sp}_m(\chi\mu))=m\,a(\chi\mu),
$$

so the special-special tensor has exponent $4a(\chi\mu)$. These examples show why the
monodromy operator must be retained until after tensoring.

The global conductor is independent of the additive character even though each displayed local
epsilon factor is not. Replacing $\psi_v$ by a scaled character changes the exponent through
$n(\psi_v)$ and changes the phase through the determinant. For a global scaling, the product
formula and triviality of automorphic central characters on $F^\times$ cancel both changes.
Trace-compatible local characters account for the different of $F_v/\mathbf Q_p$; collecting
those differents is exactly the fixed discriminant term mentioned after (5.7).

Local duality and unitarity imply $|W_v|=1$ at every place. Only finitely many finite factors
are nontrivial, so

$$
|W(\pi\times\pi')|=1.
\tag{5.8a}
$$

### 5.4 The completed equation

Substitute (2.13) into (5.4), separate the products of $L$-factors, and use (5.7). This proves

**Theorem 5.1 (functional equation).**

$$
\boxed{
\Lambda(s,\pi\times\pi')
=W(\pi\times\pi')Q(\pi\times\pi')^{1/2-s}
\Lambda(1-s,\widetilde\pi\times\widetilde\pi').}
\tag{5.9}
$$

Applying (5.9) twice yields

$$
W(\pi\times\pi')
W(\widetilde\pi\times\widetilde\pi')=1
\tag{5.10}
$$

and equality of the two conductors. If the pair is self-dual, the root number is real and hence
$\pm1$, provided the self-duality has determinant one in the same-character normalization. In
general it is a complex number on the unit circle and should not be called a sign.

### 5.5 Consistency checks

Several computations detect every likely inversion error.

At an unramified finite place, (2.7) and $\epsilon_v=1$ give the local reflection with the four
reciprocal tensor roots. For a special block, the monodromy correction contributes the missing
power of $q_v^{1/2-s}$, so the conductor exponent agrees with Book 80. Scaling $\psi_v$ gives
the two squares of the central characters in (2.15), exactly the determinant of a
$2\times2$ tensor product. Finally, multiplying those scaling laws for $c\in F^\times$ gives
one, which is necessary for (5.4).

There is also a pole check. If $\pi'=\widetilde\pi\otimes|\det|^{iu}$, reflection in (5.9)
sends $1-iu$ to $iu$ for the dual twisted pair; after translating the dual pair back by
(3.10), this is the lower pole $-iu$ of the original function. Thus the polar set (4.7) is
stable under the functional equation.

## 6. Finite order and Mellin control

### 6.1 Why continuation is not yet a bound

A meromorphic function may grow arbitrarily fast on a vertical line. The functional equation
does not prevent this: one can multiply both sides by a symmetric entire function of very large
order. To extract arithmetic information from a pole, and later to apply the
Phragmén–Lindelöf principle, one must return to the integral that produced the continuation.

The useful variable is the idele module. Write

$$
\mathbf A^\times=\mathbf A^1\times\mathbf R_{>0}
$$

after choosing a continuous splitting of the norm map. The quotient
$F^\times\backslash\mathbf A^1$ is compact. Once all norm-one and compact variables in an
unfolded integral have been integrated out, the remaining dependence on $s$ is a Mellin
transform

$$
\int_0^\infty H(y)y^s\,d^\times y.
\tag{6.1}
$$

Cuspidal decay controls $H(y)$ as $y\to\infty$. Poisson summation expresses the behavior at
zero as a finite sum of explicit powers plus another rapidly decreasing function. This is the
analytic content behind continuation and growth.

### 6.2 A Mellin-transform lemma

We isolate the required one-variable statement.

**Lemma 6.1 (regularized Mellin transform).** Let $H$ be smooth on $\mathbf R_{>0}$. Suppose
that for every $A,j\geq0$,

$$
(y\,d/dy)^jH(y)=O_{A,j}(y^{-A})\qquad(y\to\infty),
\tag{6.2}
$$

and that, for $0<y\leq1$,

$$
H(y)=\sum_{k=1}^mc_ky^{\lambda_k}+H_0(y),
\tag{6.3}
$$

where $H_0$ and all its logarithmic derivatives are $O_A(y^A)$ for every $A$. Then

$$
M_H(s)=\int_0^\infty H(y)y^s\,d^\times y
\tag{6.4}
$$

continues meromorphically to $\mathbf C$, with at most simple poles at $s=-\lambda_k$ and
principal parts $c_k/(s+\lambda_k)$. After those principal parts are subtracted, the result is
rapidly decreasing on every closed vertical strip.

**Proof.** Split (6.4) at one. The integral over $[1,\infty)$ is entire. Repeated integration
by parts with $D=y\,d/dy$ gives

$$
s^r\int_1^\infty H(y)y^s\,d^\times y
=(-1)^r\int_1^\infty D^rH(y)y^s\,d^\times y
+\text{boundary terms at }1.
\tag{6.5}
$$

On a fixed strip the integral on the right is bounded, and the boundary terms are polynomials
of degree at most $r-1$ in $s$ divided by $s^r$. After the matching contribution from the
interval $(0,1]$ is included, the boundary terms cancel.

On $(0,1]$, integrate the explicit terms directly:

$$
\int_0^1c_ky^{s+\lambda_k}\,d^\times y=\frac{c_k}{s+\lambda_k}
\tag{6.6}
$$

in their initial half-planes. The Mellin transform of $H_0$ is entire because $H_0$ vanishes
to every order at zero, and the same integration-by-parts argument applies. Taking $r$ as large
as desired proves decay faster than every power of $|\operatorname{Im}(s)|$ on a closed strip
after the principal parts are removed. $\square$

Logarithmic powers $y^\lambda(\log y)^r$ would produce poles of order $r+1$. In the present
rank-one Eisenstein family, the relevant residual exponents are distinct and no logarithmic
terms occur, which is another explanation for the simplicity of the poles.

### 6.3 Finite order

Apply Lemma 6.1 to the norm-coordinate form of every global integral in (3.8). The two powers
in (6.3) are precisely the zero-vector terms in the Poisson summation used to continue the
Eisenstein series. They yield the possible poles at $-iu$ and $1-iu$. All other terms are
rapid at both ends because the cusp forms are rapidly decreasing and the Schwartz function is
Schwartz.

For finite order one needs more than stripwise rapid decrease, because the constants in a strip
estimate could grow too quickly as the strip moves. Finite type at infinity provides the
missing control. Each archimedean Whittaker component satisfies a regular-singular differential
equation with polynomial coefficients and decays exponentially in the positive chamber. After
Poisson summation, the small-height part of the **global** kernel is the Weyl reflection of a
positive-height kernel plus the explicit residual powers. Thus the regularized global
norm-coordinate function, rather than an individual local Whittaker function, satisfies an
estimate of the form

$$
|D^jH_{\mathrm{reg}}(y)|\leq C_j(y^C+y^{-C})e^{-c(y^\eta+y^{-\eta})}
\tag{6.7}
$$

for suitable $c,C,\eta>0$. At several archimedean places the estimate is applied in each
radial coordinate before the compact norm-one variables are integrated out. Finite coordinates
contribute only finite geometric series or rational functions in $q_v^{-s}$.

Estimate (6.7) reduces the global growth problem to gamma-type integrals such as

$$
\int_0^\infty e^{-cy}y^{s+C}\,d^\times y=c^{-s-C}\Gamma(s+C)
$$

and their reflected versions. Stirling's formula, followed by the functional equation in the
far left half-plane, gives

$$
|\mathcal I^*(s)|\leq \exp(C|s|\log(2+|s|)).
\tag{6.8}
$$

The coefficient functions in (3.8) are finite products of Laurent polynomials in $q_v^{-s}$
and polynomials in $s$, so they satisfy the same type of bound. Consequently

$$
|\Lambda^*(s,\pi\times\pi')|
\leq \exp(C'|s|\log(2+|s|)).
\tag{6.9}
$$

Thus $\Lambda^*$ is entire of finite order, in fact of order at most one in the standard
extended sense allowing the factor $\log |s|$. This is exactly the amount of growth control
needed for Phragmén–Lindelöf arguments. No assertion of boundedness follows merely from
entireness.

### 6.4 Uniformity on compact strips

Let $a\leq\operatorname{Re}(s)\leq b$. The proof of Lemma 6.1 bounds every logarithmic
derivative uniformly in this strip. The norm-one variables range over a compact quotient, and
the cusp-form estimates are uniform on compact families of translates. Therefore, for every
$N\geq0$,

$$
\Lambda^*(\sigma+it,\pi\times\pi')
\ll_{a,b,N,\pi,\pi'}(1+|t|)^{-N}.
\tag{6.10}
$$

The implied constant is fixed-data: it depends on the representations, on $F$, and on the
chosen normalization. Uniformity as conductors or archimedean parameters vary is a different
problem and is not claimed here.

The same argument permits invariant derivatives of the cusp forms and derivatives in $s$.
Each $s$-derivative inserts a power of $\log y$, which is still dominated by rapid decrease at
both ends. Cauchy's formula then gives (6.10) for all derivatives of $\Lambda^*$ as well.

## 7. Vertical bounds

### 7.1 Rapid decay of completed integrals

It is worth distinguishing two conclusions. The regularized global integrals are rapidly
decreasing because they are Fourier transforms in the logarithmic norm variable. The finite
Euler product is not rapidly decreasing; removing the archimedean gamma factors exposes
polynomial growth. Both statements are called vertical bounds, but they have different proofs.

For one integral, put $y=e^x$. Then the polar-cleared expression is the Fourier transform of a
smooth function $h_\sigma(x)$ whose derivatives are integrable uniformly for $\sigma$ in a
compact interval:

$$
\mathcal I^*(\sigma+it)
=\int_{\mathbf R}h_\sigma(x)e^{itx}\,dx.
\tag{7.1}
$$

Integrating $N$ times by parts gives

$$
|\mathcal I^*(\sigma+it)|
\leq |t|^{-N}\|h_\sigma^{(N)}\|_{L^1}.
\tag{7.2}
$$

This proves rapid vertical decay without complex analysis. It also reveals why smoothness and
rapid cusp decay were essential in Book 104.

### 7.2 Eliminating local correction factors

A single identity

$$
\mathcal I(s)=\Lambda(s)C(s)
$$

does not transfer a bound to $\Lambda$ near the zeros of $C$. The finite family identity
(3.8) does. At a finite exceptional place, the Bézout coefficients are Laurent polynomials in
$q_v^{-s}$ and are bounded on each vertical strip. At infinity they may be taken to be
polynomials in $s$. Hence (7.2), summed over the finite family, gives (6.10) for the canonical
completed function.

This argument proves more than pointwise avoidance of zeros. It gives one bound uniformly on
the whole vertical line, including points where every initially preferred local integral might
vanish.

### 7.3 Polynomial bounds for the finite part

Let

$$
d=4[F:\mathbf Q]
\tag{7.3}
$$

be the archimedean degree of the Rankin–Selberg product, counted in real gamma factors. Fix
$\delta>0$. Absolute convergence gives

$$
L_f(1+\delta+it,\pi\times\pi')\ll_{\delta,\pi,\pi'}1.
\tag{7.4}
$$

On the line $\operatorname{Re}(s)=-\delta$, use the functional equation to express the finite
part through the dual finite part on $1+\delta-it$. Stirling's formula, uniformly away from the
finitely many gamma poles, says

$$
\frac{L_\infty(1-s,\widetilde\pi\times\widetilde\pi')}
{L_\infty(s,\pi\times\pi')}
\ll (1+|t|)^{d(1/2+\delta)}.
\tag{7.5}
$$

The exponential factors in the numerator and denominator cancel; this cancellation is why the
finite part has polynomial rather than exponential growth. The conductor factor is constant
for fixed data. Thus

$$
L_f(-\delta+it,\pi\times\pi')
\ll (1+|t|)^{d(1/2+\delta)}
\tag{7.6}
$$

away from the possible poles.

We recall the precise complex-analytic step. If $f$ is holomorphic of finite order in
$a\leq\operatorname{Re}(s)\leq b$ and has polynomial bounds on the two boundary lines, then it
has a polynomial bound throughout the strip. To prove this, divide $f(s)$ by
$(R+s)^M$ with $R$ outside the strip and $M$ larger than both boundary exponents. Multiply the
quotient by $\exp(\varepsilon(s-a)(s-b))$. On the horizontal edges of a rectangle of height
$T$, the real part of $(s-a)(s-b)$ is $-T^2+O(T)$, so the exponential dominates the finite-order
growth bound (6.9). The maximum-modulus principle bounds the rectangle by its vertical edges.
First let $T\to\infty$, then
$\varepsilon\to0^+$. Restoring the polynomial factor proves the claim. Linear interpolation of
the logarithms of the two boundary majorants gives the three-lines exponent.

Finite order from Chapter 6 therefore interpolates between (7.4) and (7.6). Small semicircular
indentations remove a pole on a boundary; equivalently, apply the principle to $\Lambda^*$ and
then divide by the polar polynomial away from its zeros. We obtain:

**Theorem 7.1 (vertical-strip bound).** On every closed vertical strip and outside fixed small
discs around the possible poles,

$$
L_f(\sigma+it,\pi\times\pi')\ll(1+|t|)^A
\tag{7.7}
$$

for some $A$ depending only on the strip and the fixed representations.

### 7.4 A fixed-data convexity bound

Keeping the exponents in the interpolation gives a familiar sharper form. For
$-\delta\leq\sigma\leq1+\delta$ and every $\varepsilon>0$,

$$
L_f(\sigma+it,\pi\times\pi')
\ll_{\delta,\varepsilon,\pi,\pi'}
\bigl(Q(1+|t|)^d\bigr)^{(1+\delta-\sigma)/2+\varepsilon},
\tag{7.8}
$$

again away from the possible poles. The $Q$-power is harmless for fixed data but records the
correct symmetry. To prove (7.8), multiply by a harmless factor
$(R+s)^{-M}$ large enough to make the horizontal edges vanish, apply the three-lines theorem
to the resulting holomorphic function, and let $R$ tend to infinity. The boundary exponents
are zero on $1+\delta$ and $d(1/2+\delta)$ on $-\delta$; linear interpolation gives
$d(1+\delta-\sigma)/2$. The factor $\varepsilon$ absorbs logarithms from Stirling's formula and
the polar-clearing polynomial.

This is a convexity bound in the vertical aspect for fixed automorphic data. It is not a
subconvex estimate, nor is its implied constant uniform in the conductor.

On the central line, take $\delta$ arbitrarily small in (7.8). For every $\varepsilon>0$ this
gives the fixed-data estimate

$$
L_f(1/2+it,\pi\times\pi')
\ll_{\varepsilon,\pi,\pi'}
\bigl(Q(1+|t|)^d\bigr)^{1/4+\varepsilon}.
\tag{7.9}
$$

The exponent $1/4$ is the convexity exponent because the functional equation has degree $d$
and width one between absolute convergence and its reflected line. The formula is often
written as a bound by the one-quarter power of the analytic conductor

$$
\mathcal C(t)=Q\prod_{v\mid\infty}\prod_k
(1+|t+\operatorname{Im}\mu_{v,k}|).
$$

Here each $\Gamma_{\mathbf C}$ factor is first expanded into its two
$\Gamma_{\mathbf R}$ factors, so the number of factors is $d=4[F:\mathbf Q]$. For fixed
archimedean shifts this is equivalent to (7.9). Keeping the individual shifts would
be necessary for uniform families, which lie beyond the fixed-data assertion here.

Bounds for derivatives follow without a new functional equation. Apply (7.8) on a circle of
fixed small radius around $s$ and use Cauchy's integral formula. If the circle approaches one
of the two possible poles, apply the argument to the polar-cleared function and restore the
explicit polar polynomial afterward.

## 8. Positivity of the self-convolution

### 8.1 Local Schur positivity

Let $v$ be unramified and let $A=\{\alpha_1,\alpha_2\}$ be the Satake multiset of a unitary
representation $\pi_v$. The contragredient multiset is
$\{\alpha_1^{-1},\alpha_2^{-1}\}$; unitarity identifies it, as an unordered multiset, with
$\{\overline\alpha_1,\overline\alpha_2\}$. Therefore

$$
L_v(s,\pi_v\times\widetilde\pi_v)
=\prod_{i,j}(1-\alpha_i\overline\alpha_jX)^{-1},
\qquad X=q_v^{-s}.
\tag{8.1}
$$

The two-variable Cauchy identity gives

$$
\prod_{i,j}(1-x_i y_jX)^{-1}
=\sum_{\lambda}s_\lambda(x_1,x_2)s_\lambda(y_1,y_2)X^{|\lambda|},
\tag{8.2}
$$

where $\lambda=(m-r,r)$ ranges over partitions of length at most two. Substituting
$y_j=\overline x_j$ yields

$$
L_v(s,\pi_v\times\widetilde\pi_v)
=\sum_{m\geq0}\left(
\sum_{r=0}^{\lfloor m/2\rfloor}
|s_{(m-r,r)}(\alpha_1,\alpha_2)|^2
\right)X^m.
\tag{8.3}
$$

Every coefficient is nonnegative.

For two variables the Cauchy identity can be proved without symmetric-function theory. Expand
each factor in (8.1) as a geometric series and group monomials according to the common total
degree and the smaller row sum. The resulting determinant quotient is

$$
s_{(a,b)}(x_1,x_2)
=(x_1x_2)^b\frac{x_1^{a-b+1}-x_2^{a-b+1}}{x_1-x_2},
$$

with the evident limiting value when $x_1=x_2$. Pairing it with its complex conjugate proves
(8.3) directly.

### 8.2 Global nonnegative coefficients

Let $S$ contain every archimedean and ramified place. Multiplying (8.3) over $v\notin S$ gives
an absolutely convergent Dirichlet series for $\sigma>1$:

$$
L^S(s,\pi\times\widetilde\pi)
=\sum_{\mathfrak a}b_\pi^S(\mathfrak a)(N\mathfrak a)^{-s}.
\tag{8.4}
$$

Unique factorization of ideals shows that
$b_\pi^S$ is multiplicative and that each value is a product of local coefficients from
(8.3). Hence

$$
\boxed{b_\pi^S(\mathfrak a)\geq0.}
\tag{8.5}
$$

No temperedness assertion is used. Individual Satake parameters may have modulus different
from one; unitarity of the representation is enough to identify the contragredient multiset
with the conjugate multiset.

Positivity is safest for the incomplete product. At a ramified place a parameter may have
monodromy and the coefficient formula need not visibly be a sum of squares in a chosen
presentation. Removing finitely many such places loses no information about the pole at one,
as Chapter 10 will prove.

### 8.3 A positive residue

Take $\pi'=\widetilde\pi$, choose $\phi'(g)=\overline{\phi(g)}$ in the unitary automorphic
realization, and choose $\widehat\Phi(0)>0$. Formula (4.4) with $u=0$ becomes

$$
\operatorname*{Res}_{s=1}\mathcal I(s,\phi,\overline\phi,\Phi)
=c_F\widehat\Phi(0)\|\phi\|_2^2>0.
\tag{8.6}
$$

Thus the pole of the self-convolution is not the result of cancellation among local terms. Its
residue is detected by a positive global norm.

Since the exceptional local correction factors can be chosen nonzero at $s=1$, the canonical
residue differs from (8.6) by a nonzero explicit local scalar. With the standard positive
unramified normalizations and paired ramified data, that scalar is positive. The sign of a
residue for arbitrarily rescaled test vectors is irrelevant; positivity belongs to the
canonical self-pairing normalization.

### 8.4 Consequences without a Tauberian theorem

Positivity and the simple pole already give useful coefficient bounds. For $X\geq2$ and
$\sigma>1$,

$$
\sum_{N\mathfrak a\leq X}b_\pi^S(\mathfrak a)
\leq X^\sigma L^S(\sigma,\pi\times\widetilde\pi).
\tag{8.7}
$$

Near one, meromorphy and the simple pole give
$L^S(\sigma)=O((\sigma-1)^{-1})$. Taking
$\sigma=1+1/\log X$ yields

$$
\sum_{N\mathfrak a\leq X}b_\pi^S(\mathfrak a)
\ll_{\pi,S}X\log X.
\tag{8.8}
$$

This is not the asymptotic one would obtain from a Tauberian theorem, but it is sufficient for
absolute domination of the Whittaker sums used in subsequent spectral arguments. It uses no
cancellation and is therefore robust under deletion of finitely many nonnegative factors.

For cross coefficients $a_{\pi,\pi'}^S(\mathfrak a)$, local Cauchy–Schwarz and then global
Cauchy–Schwarz give

$$
\sum_{N\mathfrak a\leq X}|a_{\pi,\pi'}^S(\mathfrak a)|
\leq
\left(\sum_{N\mathfrak a\leq X}b_\pi^S(\mathfrak a)\right)^{1/2}
\left(\sum_{N\mathfrak a\leq X}b_{\pi'}^S(\mathfrak a)\right)^{1/2},
\tag{8.9}
$$

and hence the same $O(X\log X)$ fixed-data bound.

## 9. Logarithmic derivatives and the boundary line

### 9.1 Prime-power coefficients

In $\sigma>1$, absolute convergence permits logarithmic differentiation. At an unramified
place,

$$
-\frac{L_v'}{L_v}(s,\pi_v\times\pi'_v)
=\sum_{r\geq1}
\left(\sum_{i,j}(\alpha_{i,v}\beta_{j,v})^r\right)
(\log q_v)q_v^{-rs}.
\tag{9.1}
$$

For the self-pair this coefficient is

$$
\sum_{i,j}\alpha_{i,v}^r\overline\alpha_{j,v}^r
=|\alpha_{1,v}^r+\alpha_{2,v}^r|^2\geq0.
\tag{9.2}
$$

Consequently

$$
-\frac{(L^S)'}{L^S}(s,\pi\times\widetilde\pi)
=\sum_{v\notin S}\sum_{r\geq1}
|\alpha_{1,v}^r+\alpha_{2,v}^r|^2
(\log q_v)q_v^{-rs}.
\tag{9.3}
$$

This second positivity is different from coefficient positivity: (8.5) concerns the Euler
product itself, while (9.3) concerns its logarithm.

### 9.2 The singularity at one

If a meromorphic function has a simple pole at one and is otherwise holomorphic nearby, then

$$
L^S(s)=\frac{c}{s-1}+h(s),\qquad c\ne0,
$$

and therefore

$$
-\frac{(L^S)'}{L^S}(s)=\frac1{s-1}+O(1)
\qquad(s\to1^+).
\tag{9.4}
$$

For the self-pair, (9.3) realizes the left side as a nonnegative prime-power series. Thus the
unit residue of its logarithmic singularity measures the total mass of the local traces near
the boundary. No assertion that the Euler product itself converges at $s=1$ is being made.

### 9.3 Cross-term domination

For two local trace sums

$$
A_{v,r}=\alpha_{1,v}^r+\alpha_{2,v}^r,qquad
B_{v,r}=\beta_{1,v}^r+\beta_{2,v}^r,
$$

the cross logarithmic coefficient is $A_{v,r}B_{v,r}$. The elementary inequality

$$
|A_{v,r}B_{v,r}|
\leq\frac12\bigl(|A_{v,r}|^2+|B_{v,r}|^2\bigr)
\tag{9.5}
$$

dominates it by the two self logarithmic derivatives. This justifies absolute logarithmic
differentiation for $\sigma>1$ and shows that cross products cannot have a worse right-edge
singularity than the two self-products.

The inequality does not prove that a cross product is holomorphic at one. That conclusion
comes from the invariant-pairing pole criterion. Boundary holomorphy cannot be read from an
Euler product whose absolute convergence stops at that boundary.

### 9.4 Landau's positivity lemma

The following elementary result explains why positivity places the first singularity on the
real axis.

**Lemma 9.1 (Landau).** Let

$$
D(s)=\sum_{n\geq1}a_nn^{-s},\qquad a_n\geq0,
$$

have finite abscissa of convergence $\sigma_c$. Then $D$ cannot be holomorphic in a
neighborhood of the real point $\sigma_c$.

**Proof.** Suppose $D$ were holomorphic in the disc
$|s-\sigma_0|<R$ with $\sigma_0>\sigma_c$ and
$R>\sigma_0-\sigma_c$. Its Taylor derivatives at the real point $\sigma_0$ are

$$
(-1)^kD^{(k)}(\sigma_0)
=\sum_na_n(\log n)^kn^{-\sigma_0}\geq0.
\tag{9.6}
$$

Cauchy's estimates bound these derivatives by $Mk!R^{-k}$ on any slightly smaller disc.
For $0<r<R$, positivity permits the order of summation to be exchanged:

$$
\sum_{k\geq0}\frac{(-1)^kD^{(k)}(\sigma_0)}{k!}r^k
=\sum_na_nn^{-\sigma_0}e^{r\log n}
=\sum_na_nn^{-(\sigma_0-r)}.
\tag{9.7}
$$

The left series converges for $r<R$, so the Dirichlet series converges at
$\sigma_0-r$. Choose $r>\sigma_0-\sigma_c$, contradicting the definition of $\sigma_c$.
$\square$

If $D$ were holomorphic merely in a neighborhood of $\sigma_c$, the disc used in the proof is
still available: choose $\sigma_0$ just to the right of $\sigma_c$. A disc centered at
$\sigma_0$ and extending slightly to the left of $\sigma_c$ lies in the union of that
neighborhood and the half-plane of convergence. Its radius is greater than
$\sigma_0-\sigma_c$, exactly as required.

For the self Rankin–Selberg series, the simple pole at one and absolute convergence to its
right identify one as the natural real boundary. Landau's lemma prevents an argument from
removing that pole by a formal cancellation among nonnegative coefficients.

## 10. Deleting local factors

### 10.1 Local regularity at one

To compare incomplete products, one must know that an omitted finite local factor is finite
and nonzero at $s=1$. This is where unitarity enters.

An irreducible generic unitary representation of $\mathrm{GL}_2(K)$ is either tempered or a
complementary principal series whose two real inducing exponents lie strictly between
$-1/2$ and $1/2$. Therefore every Frobenius root $\rho$ that can occur in a standard local
factor has

$$
|\rho|<q^{1/2}
$$

after the unitary central twist is removed. A tensor root $\rho\rho'$ consequently satisfies

$$
|\rho\rho'|<q.
\tag{10.1}
$$

Tempered and special endpoints satisfy an even stronger nonvanishing statement; monodromy can
only remove denominator factors. Thus

$$
1-\rho\rho'q^{-1}\ne0,
$$

and

$$
0<|L_v(1,\pi_v\times\pi'_v)|<\infty.
\tag{10.2}
$$

The strict complementary-series inequality is essential. Equality would place a reciprocal
root exactly at $q$ and could create a local pole at one.

Let us justify that no local class has been missed. For a tempered principal series, the
unramified absolute values of the inducing characters are one, so every surviving tensor root
has modulus one. For a complementary series the inducing characters have the form
$\xi|\cdot|^r$ and $\xi'|\cdot|^{-r}$ with $|r|<1/2$; pairing with a second complementary
series of exponent $r'$ gives real exponents among $\pm r\pm r'$, all strictly between $-1$
and $1$. A special representation has a centered length-two parameter; its only Euler root is
shifted inward by $q^{-1/2}$, while monodromy deletes the other root. A unitary supercuspidal
parameter has no inertia-fixed vector unless an interaction in the tensor product creates one.
Any such invariant summand is an unramified unitary character and contributes a root of modulus
one. These cases prove (10.1) for every generic unitary local component.

Nonvanishing is as important as finiteness. Each local factor is the reciprocal of a polynomial
with constant term one. The preceding root bound shows that none of its linear factors vanishes
at $X=q^{-1}$. Since a reciprocal polynomial has no numerator, it cannot vanish there either.
At infinity, the unitary shifts in (2.12) avoid the nonpositive integers when $s=1$, so the
gamma functions are likewise finite and nonzero. This completes the local input to the
deletion argument.

### 10.2 Stability of pole order

Let $S$ be any finite set containing the archimedean places. In a right half-plane,

$$
\Lambda(s,\pi\times\pi')
=L_\infty(s)\left(\prod_{v\in S,\ v<\infty}L_v(s)\right)L^S(s).
\tag{10.3}
$$

Every factor outside $L^S$ is meromorphic. At $s=1$, the archimedean gamma factors are finite
and nonzero for unitary cuspidal data, and (10.2) handles the finite factors. Hence

$$
\operatorname{ord}_{s=1}L^S(s,\pi\times\pi')
=\operatorname{ord}_{s=1}\Lambda(s,\pi\times\pi').
\tag{10.4}
$$

This proves:

**Proposition 10.1.** Deleting or restoring finitely many local factors does not change the
order at $s=1$ for a pair of unitary cuspidal representations.

In particular, $L^S(s,\pi\times\widetilde\pi)$ has a simple pole at one, while
$L^S(s,\rho\times\widetilde\pi)$ is holomorphic there if $\rho\not\simeq\pi$.

### 10.3 What can fail without unitarity

If arbitrary nonunitary twists are allowed, a local inducing exponent can cross the boundary
$1/2$. Then a tensor root can equal $q$, so the local factor itself has a pole at $s=1$.
Deleting that place changes the global order. Similarly, an archimedean gamma shift can place a
gamma pole at one.

There are two legitimate remedies: retain every suspect local factor, or first twist the global
representations to a unitary normalization and translate the spectral variable accordingly.
This book uses the second viewpoint from the outset. Statements about incomplete products at
$s=1$ always include unitarity.

## 11. The analytic multiplicity criterion

### 11.1 Order of the incomplete product

Combining Theorem 4.2 with Proposition 10.1 gives the central result of this volume.

**Theorem 11.1 (analytic separation at one).** Let $\pi$ and $\rho$ be irreducible unitary
cuspidal automorphic representations of $\mathrm{GL}_2(\mathbf A_F)$, and let $S$ be any finite
set containing the archimedean places. Then

$$
\boxed{
\operatorname{pord}_{s=1}L^S(s,\rho\times\widetilde\pi)
=\dim\operatorname{Hom}_{G(\mathbf A)}(\rho,\pi).}
\tag{11.1}
$$

Here $\operatorname{pord}_{s_0}f=\max\{0,-\operatorname{ord}_{s_0}f\}$ records only pole
order. Since the representations are irreducible, the dimension on the right is zero or one.

**Proof.** The pole criterion says that the completed function has a simple pole at one exactly
when $\widetilde\pi\simeq\widetilde\rho$, equivalently $\rho\simeq\pi$; otherwise it is
holomorphic there. It may vanish there, which does not affect its polar order. Irreducibility
and Schur's lemma identify the polar alternative with the dimension of the Hom space.
Proposition 10.1 transfers the polar order to the incomplete product.
$\square$

Equation (11.1) is more precise than the slogan “the self-product has a pole.” It identifies
the pole order with an invariant multiplicity and states exactly which factors may be omitted.

### 11.2 The pole-comparison principle

Suppose two incomplete Euler products satisfy

$$
L^S(s,\pi\times\widetilde\pi)
=L^S(s,\rho\times\widetilde\pi)
\tag{11.2}
$$

as functions in $\sigma>1$. By analytic continuation they agree wherever either side is
defined. The left side has a simple pole at one. The right side has no pole there unless
$\rho\simeq\pi$; it may be nonzero or may vanish. Thus equality (11.2) is analytically
incompatible with a zero Hom space.

This is the **pole-comparison principle**. Its inputs are:

$$
\begin{array}{c}
\text{equality of an unramified Euler tail}\\
+\ \text{unitary local regularity at the deleted places}\\
+\ \text{the invariant-pairing pole criterion}
\end{array}
\quad\Longrightarrow\quad
\operatorname{Hom}_{G(\mathbf A)}(\rho,\pi)\ne0.
\tag{11.3}
$$

The next volume converts equality of almost all Hecke data into (11.2) and combines this
criterion with the representation-theoretic newform theory. Here the analytic implication is
the endpoint.

### 11.3 Hecke data and the analytic handoff

At an unramified place, the factor

$$
L_v(s,\rho_v\times\widetilde\pi_v)
$$

is determined by the unordered Satake pairs of $\rho_v$ and $\pi_v$. Equality of local
representations certainly gives equality of these factors. Equality merely of traces is not
enough unless the central characters also agree, because trace and determinant together
recover the Satake polynomial

$$
1-(\alpha_{1,v}+\alpha_{2,v})X
+\alpha_{1,v}\alpha_{2,v}X^2.
\tag{11.4}
$$

Once the two unordered pairs agree outside $S$, the local tensor factors agree there and hence
(11.2) follows. The analytic work of this book then detects the global Hom space. No comparison
of the omitted factors is needed beyond their regularity and nonvanishing at one.

### 11.4 Sparse exceptional sets

Finite exceptional sets are not the only possible application. Assume now that $\pi$ and
$\rho$ are tempered at every unramified place under consideration, so all Satake parameters
have modulus one. Suppose their local data differ only on a set $T$ satisfying

$$
\sum_{v\in T}q_v^{-1}<\infty.
\tag{11.5}
$$

For $s\to1^+$, the total difference of the logarithms contributed by $T$ is bounded by

$$
C\sum_{v\in T}\sum_{r\geq1}q_v^{-rs}
\leq C'\sum_{v\in T}q_v^{-1}<\infty.
\tag{11.6}
$$

It cannot create or remove the $-\log(s-1)$ singularity associated with a simple pole.
Therefore the pole-comparison principle remains valid under (11.5).

The convergence condition is stronger than density zero. Better density thresholds require
uniform bounds toward temperedness and finer prime sums; they do not follow from the fixed-data
vertical estimates proved here.

## 12. Examples and normalization audits

### 12.1 Unramified representations

Let $v$ be finite and let

$$
A=\{\alpha,\beta\},\qquad B=\{\gamma,\delta\}.
$$

Then

$$
L_v(s,\pi_v\times\pi'_v)
=\frac1{(1-\alpha\gamma X)(1-\alpha\delta X)
(1-\beta\gamma X)(1-\beta\delta X)},
\qquad X=q_v^{-s}.
\tag{12.1}
$$

The line break in the denominator denotes ordinary multiplication of all four factors, so
equivalently

$$
L_v(s)=\prod_{u\in A,\ z\in B}(1-uzX)^{-1}.
\tag{12.2}
$$

If both pairs are $\{1,1\}$, then $L_v(s)=(1-X)^{-4}$. The diagonal Whittaker sum alone is

$$
\sum_{m\geq0}(m+1)^2X^m
=\frac{1-X^2}{(1-X)^4}.
$$

The scalar Schwartz integral contributes $(1-X^2)^{-1}$. This is the quickest audit of the
three-variable integral.

For the self-pair, the coefficient of $X$ is

$$
|\alpha+\beta|^2,
$$

and the coefficient of $X^2$ is

$$
|\alpha^2+\alpha\beta+\beta^2|^2+|\alpha\beta|^2.
$$

Both are visibly nonnegative, illustrating (8.3).

### 12.2 A special local component

Let $D=\operatorname{Sp}_2(\chi)$ with $\chi$ unramified and
$\chi(\Phi)=\alpha$. Book 80 gives

$$
L(s,D)=(1-\alpha q^{-s-1/2})^{-1},
\qquad a(D)=1.
\tag{12.3}
$$

The underlying Weil representation has two unramified lines, but monodromy leaves only one
line in $(\ker N)^I$. Treating the parameter as a semisimple direct sum would introduce one
extra Euler factor and would give conductor zero. The local Whittaker zeta ideal removes that
same extra factor at the reducibility point of normalized induction.

For conductor-zero $\psi_v$, the epsilon factor is

$$
\epsilon(s,D,\psi_v)=-\alpha q^{-(s-1/2)}.
\tag{12.4}
$$

Thus the $q$-degree of epsilon is the monodromy conductor. This checks simultaneously the
center $1/2$ and the sign in the determinant correction.

### 12.3 Unitary twists

Suppose

$$
\pi'=\widetilde\pi\otimes|\det|^{iu}.
$$

By translation of the spectral variable,

$$
\Lambda(s,\pi\times\pi')
=\Lambda(s+iu,\pi\times\widetilde\pi).
\tag{12.5}
$$

Since the untwisted self-pair has poles at zero and one, (12.5) has poles at $-iu$ and
$1-iu$. Its central-character product is $|\cdot|^{2iu}$, agreeing with the Eisenstein pole
locations. Three independent calculations—twisting, the Eisenstein constant term, and the
functional equation—therefore give the same answer.

### 12.4 A failed diagonal integral

It is instructive to see exactly how an almost-correct construction fails. Consider only

$$
\int_{K^\times}W(a(y))W'(a(y))|y|^{s-1}\,d^\times y.
\tag{12.6}
$$

At an unramified place it gives (2.5), not (2.7). If one nevertheless declared (12.6) to be the
local $L$-factor, then its numerator would vary with the product central character. The alleged
factor would fail to match the determinant definition for the tensor Weil–Deligne parameter,
and its functional equation would acquire an unexplained extra Tate factor.

The two-dimensional Schwartz variable repairs both failures at once. Its central Mellin
integral is the missing Tate factor, and its Fourier transform is what makes the global
Eisenstein functional equation available. The larger integral is forced by compatibility, not
chosen for aesthetic symmetry.

## 13. The analytic package

### 13.1 Dependency closure

The substantial inputs from Book 104 are now visible and limited: global Whittaker
factorization, the three-variable unfolding, rationality of finite local zeta integrals, local
functional equations, continuation and residues of the rank-one Eisenstein family, and rapid
cuspidal decay. This book did not assume the desired canonical continuation or vertical bounds;
it obtained them from a finite family of those integrals.

Book 80 supplies the nonarchimedean normalization ledger: geometric Frobenius, tensor
monodromy, $(\ker N)^I$, conductor exponents, self-dual measures, additive-character scaling,
duality, and induction constants. Section 2.3 verified that the zeta-integral factors agree
with those parameter factors on the local building blocks used here. Ordinary complex analysis
supplied Mellin continuation, Stirling's formula, Cauchy's estimates, and the
Phragmén–Lindelöf principle; their required forms were proved or explicitly reduced in
Chapters 6, 7, and 9.

No result about global newvectors or strong multiplicity one was used. The analytic criterion
has therefore been reached without borrowing the theorem it is meant to support.

### 13.2 The reusable criterion

For later use, the whole volume can be compressed into the following statement without losing
its hypotheses.

**Theorem 13.1 (Rankin–Selberg criterion).** Let $\pi$ and $\rho$ be irreducible unitary
cuspidal automorphic representations of $\mathrm{GL}_2(\mathbf A_F)$, and let $S$ be finite and
contain all archimedean places. Then:

1. $L^S(s,\pi\times\widetilde\pi)$ has nonnegative Dirichlet coefficients and a simple pole at
   $s=1$;
2. $L^S(s,\rho\times\widetilde\pi)$ is holomorphic at $s=1$ unless $\rho\simeq\pi$;
3. finite local factors omitted in forming $L^S$ are finite and nonzero at $s=1$;
4. consequently, equality of these two incomplete Euler products forces
   $\operatorname{Hom}_{G(\mathbf A)}(\rho,\pi)\ne0$.

**Proof.** Positivity is (8.5). The exact pole alternative is Theorem 4.2. Stability after
deleting $S$ is Proposition 10.1. The last assertion follows by comparing orders at one, as in
Section 11.2. $\square$

The theorem is intentionally phrased in terms of incomplete products. It is ready to receive
almost-everywhere local information without requiring any prior identification at the
exceptional places.

### 13.3 Conclusion

The Rankin–Selberg $L$-function is now independent of every auxiliary choice used to construct
it. Its finite factors are the normalized generators of local zeta ideals; at unramified
places they are the four tensor Frobenius factors, and where Weil–Deligne parameters are used
they agree with the $(\ker N)^I$ definition and its conductor and epsilon conventions.
Archimedean Mellin transforms complete the product around the center $s=1/2$.

The global Eisenstein pairing gives meromorphic continuation, but the passage from one integral
to the canonical function requires the finite Bézout family. Its residue is an invariant
pairing, so the polar divisor is exact: a dual unitary twist produces two simple poles and no
other pair produces any. Poisson summation and cuspidal decay turn the regularized integrals
into Fourier transforms in the logarithmic norm variable. This gives finite order, rapid decay
of the completion, and—after the functional equation and Stirling's formula—polynomial and
convexity bounds for the finite part.

Finally, the self-convolution is positive in two compatible senses: its Euler coefficients are
sums of squares of Schur polynomials, and its logarithmic derivative has nonnegative
prime-power coefficients. Its pole at one is the positive Petersson norm. Deleting finitely
many unitary local factors preserves that pole. A cross product has no pole unless it encodes
the invariant pairing with the original representation. The resulting difference between one
simple pole and holomorphy is the analytic separation principle on which multiplicity one
rests.
