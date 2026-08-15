# Local Jacquet--Langlands for Special and Dihedral Packets

## Contents

1. [The local comparison problem](#1-the-local-comparison-problem)
   - [Two groups and one elliptic geometry](#11-two-groups-and-one-elliptic-geometry)
   - [Standing arithmetic conventions](#12-standing-arithmetic-conventions)
   - [The selected domain](#13-the-selected-domain)
   - [The theorem in advance](#14-the-theorem-in-advance)
2. [Matching regular elliptic classes](#2-matching-regular-elliptic-classes)
   - [Characteristic polynomials as transfer coordinates](#21-characteristic-polynomials-as-transfer-coordinates)
   - [Centralizers and rational conjugacy](#22-centralizers-and-rational-conjugacy)
   - [The common Weyl discriminant](#23-the-common-weyl-discriminant)
   - [Why split regular classes do not transfer](#24-why-split-regular-classes-do-not-transfer)
3. [Measures and orbital normalization](#3-measures-and-orbital-normalization)
   - [A compatible measure ledger](#31-a-compatible-measure-ledger)
   - [Ordinary and normalized orbital integrals](#32-ordinary-and-normalized-orbital-integrals)
   - [Geometric and signed transfer conventions](#33-geometric-and-signed-transfer-conventions)
   - [Characters as functions and as distributions](#34-characters-as-functions-and-as-distributions)
4. [The special correspondence](#4-the-special-correspondence)
   - [The two representations](#41-the-two-representations)
   - [The elliptic Steinberg character](#42-the-elliptic-steinberg-character)
   - [The transfer sign](#43-the-transfer-sign)
   - [Twists, centers, and conductors](#44-twists-centers-and-conductors)
   - [Special local factors](#45-special-local-factors)
5. [Quadratic data and the rectifier](#5-quadratic-data-and-the-rectifier)
   - [Admissible pairs](#51-admissible-pairs)
   - [Direct and induction normalizations](#52-direct-and-induction-normalizations)
   - [The two representations attached to a pair](#53-the-two-representations-attached-to-a-pair)
   - [Equivalence, twists, and minimality](#54-equivalence-twists-and-minimality)
6. [Depth-zero character matching](#6-depth-zero-character-matching)
   - [The finite elliptic calculation](#61-the-finite-elliptic-calculation)
   - [Lifting from the residue field](#62-lifting-from-the-residue-field)
   - [Central and irregular counterexamples](#63-central-and-irregular-counterexamples)
   - [The depth-zero theorem](#64-the-depth-zero-theorem)
7. [Positive-depth tame matching](#7-positive-depth-tame-matching)
   - [A common simple character](#71-a-common-simple-character)
   - [The finite Fourier comparison](#72-the-finite-fourier-comparison)
   - [The type-regular range](#73-the-type-regular-range)
   - [Near-central correction terms](#74-near-central-correction-terms)
   - [Completion of the character identity](#75-completion-of-the-character-identity)
8. [Consequences of character matching](#8-consequences-of-character-matching)
   - [Central characters and contragredients](#81-central-characters-and-contragredients)
   - [Exact twisting laws](#82-exact-twisting-laws)
   - [Conductors and depth patterns](#83-conductors-and-depth-patterns)
   - [Why numerical invariants do not determine transfer](#84-why-numerical-invariants-do-not-determine-transfer)
9. [Local parameters and local factors](#9-local-parameters-and-local-factors)
   - [The common parameter assignment](#91-the-common-parameter-assignment)
   - [Determinants and conductors](#92-determinants-and-conductors)
   - [Euler and epsilon factors](#93-euler-and-epsilon-factors)
   - [Dependence on additive characters and measures](#94-dependence-on-additive-characters-and-measures)
10. [Types, newvectors, and level](#10-types-newvectors-and-level)
    - [What can and cannot correspond](#101-what-can-and-cannot-correspond)
    - [Special type lines](#102-special-type-lines)
    - [Dihedral type multiplicity spaces](#103-dihedral-type-multiplicity-spaces)
    - [Oldvectors and the anisotropic contrast](#104-oldvectors-and-the-anisotropic-contrast)
11. [Integral compatibility](#11-integral-compatibility)
    - [Coefficient rings and unit-valued data](#111-coefficient-rings-and-unit-valued-data)
    - [Integral special lines](#112-integral-special-lines)
    - [Integral dihedral types](#113-integral-dihedral-types)
    - [Perfect pairings and reduction](#114-perfect-pairings-and-reduction)
    - [The nonbanal boundary](#115-the-nonbanal-boundary)
12. [Bijection and uniqueness in the selected range](#12-bijection-and-uniqueness-in-the-selected-range)
    - [The selected sets](#121-the-selected-sets)
    - [Existence and injectivity](#122-existence-and-injectivity)
    - [Character-theoretic uniqueness](#123-character-theoretic-uniqueness)
    - [The complete selected theorem](#124-the-complete-selected-theorem)
13. [Worked packets and diagnostic failures](#13-worked-packets-and-diagnostic-failures)
    - [An unramified special twist](#131-an-unramified-special-twist)
    - [A ramified special twist](#132-a-ramified-special-twist)
    - [An unramified depth-zero pair](#133-an-unramified-depth-zero-pair)
    - [A tame ramified pair](#134-a-tame-ramified-pair)
    - [Five false shortcuts](#135-five-false-shortcuts)
14. [The transfer package](#14-the-transfer-package)
    - [A normalization audit](#141-a-normalization-audit)
    - [A reusable comparison table](#142-a-reusable-comparison-table)
    - [Boundary of the theorem](#143-boundary-of-the-theorem)
    - [Conclusion](#144-conclusion)

## 1. The local comparison problem

### 1.1 Two groups and one elliptic geometry

Let $F$ be a nonarchimedean local field of characteristic zero and let $D$ be the quaternion division algebra over $F$. We compare

$$
G=\operatorname{GL}_2(F)
\qquad\text{and}\qquad
G'=D^\times.
$$

These groups are inner forms: after extending scalars to a separable closure, $D$ becomes the algebra of two-by-two matrices. Over $F$, however, their representation theories look strikingly different. The group $G$ has a Borel subgroup, principal series, infinite-dimensional discrete series, and a large split regular set. The quotient $G'/F^\times$ is compact, every irreducible smooth representation of $G'$ is finite-dimensional, and every noncentral element of $G'$ is elliptic.

The point of local Jacquet--Langlands is that the discrete part of the split theory is nevertheless encoded by the anisotropic group. The encoding cannot be an isomorphism of representation spaces, nor can it compare fixed vectors under identical compact subgroups. It is detected by characters on the geometric region shared by the two groups: regular elliptic conjugacy classes. In degree two this region is unusually concrete. A class is described by one irreducible quadratic polynomial, and the same polynomial produces one class in each group.

This book proves the comparison for exactly the packets needed later: twists of the Steinberg representation and the supercuspidals arising from tame admissible quadratic pairs. The construction of these representations, their individual character formulas, their levels, and their integral types are already available. Our task is the genuinely two-sided step: identify matching classes and measures, compare every character contribution including those near the center, locate the sign, and prove that the result is a bijection uniquely characterized by the comparison.

### 1.2 Standing arithmetic conventions

Write

$$
\mathcal O=\mathcal O_F,
\qquad \mathfrak p=(\varpi),
\qquad |\mathcal O/\mathfrak p|=q,
\qquad |\varpi|=q^{-1}.
$$

Reduced trace and reduced norm on $D$ are $\operatorname{Trd}$ and $\operatorname{Nrd}$. The center of both groups is identified with $F^\times$: on $G$ by $z\mapsto zI_2$ and on $G'$ by scalar inclusion. Notice that

$$
\det(zI_2)=z^2=\operatorname{Nrd}(z).
\tag{1.1}
$$

This square is responsible for the fact that twisting by a character of $F^\times$ multiplies a central character by its square.

For local parameters, $\Phi$ denotes geometric Frobenius and reciprocity is normalized by

$$
\operatorname{rec}_F(\varpi)=\Phi.
\tag{1.2}
$$

Thus $|\Phi|=q^{-1}$. Additive characters use the convention that $n(\psi)=0$ means $\psi$ is trivial on $\mathcal O$ but not on $\varpi^{-1}\mathcal O$. Whenever an epsilon factor is written without an additive Haar measure, the measure is the self-dual measure for the displayed additive character.

Representations are complex when characters are compared analytically. Integral statements use a finite extension $L/\mathbf Q_\ell$, its valuation ring $R$, and $\ell$ different from the residue characteristic $p$ of $F$. The distinction between the two coefficient settings will always be explicit.

### 1.3 The selected domain

There are two families on each side.

The special family is

$$
\operatorname{St}\otimes(\mu\circ\det)
\quad\longleftrightarrow\quad
\mu\circ\operatorname{Nrd},
\tag{1.3}
$$

where $\mu$ is any smooth character of $F^\times$.

The dihedral family starts with a separable quadratic extension $E/F$ and a smooth character $\theta:E^\times\to\mathbf C^\times$. We require the pair $(E,\theta)$ to be tame admissible: $\theta\ne\theta^\sigma$, and if $\theta/\theta^\sigma$ is trivial on $1+\mathfrak p_E$, then $E/F$ is unramified. Here $\sigma$ is the nontrivial $F$-automorphism of $E$. This includes every quadratic extension when $p\ne2$ and the unramified quadratic extension in every residue characteristic. It excludes ramified dyadic pairs from the positive-depth construction.

Primitive wild supercuspidals and primitive wild representations of $D^\times$ are not in the theorem. The exclusion is structural, not cosmetic: their leading strata are not obtained from the tame quadratic data used in the character calculation, and the finite Fourier comparison below does not construct their extension operators.

### 1.4 The theorem in advance

For each selected representation $\pi$ of $G$ there is a unique selected representation $\pi'$ of $G'$ such that, whenever $g\in G$ and $d\in G'$ have the same irreducible characteristic polynomial,

$$
\boxed{\Theta_\pi(g)=-\Theta_{\pi'}(d).}
\tag{1.4}
$$

The assignment is the one in (1.3) for special twists and attaches to the same rectified quadratic pair in the dihedral case. It is a bijection in the selected range. It preserves central characters, twisting, contragredients, conductor exponents, and the common two-dimensional local parameter. Consequently it preserves local $L$-, epsilon, and gamma factors with all arithmetic, Frobenius, additive-character, and self-dual-measure conventions fixed.

The minus sign is not a convention that may be silently removed. It is the degree-two inner-form sign. One may move it from the character identity into the definition of transferred test functions, but it must appear exactly once. Chapter 3 makes this distinction precise.

## 2. Matching regular elliptic classes

### 2.1 Characteristic polynomials as transfer coordinates

For $g\in G$, write

$$
P_g(X)=X^2-t(g)X+n(g),
\qquad t(g)=\operatorname{tr}(g),\quad n(g)=\det(g).
$$

For $d\in G'$, write

$$
P_d(X)=X^2-t(d)X+n(d),
\qquad t(d)=\operatorname{Trd}(d),\quad n(d)=\operatorname{Nrd}(d).
$$

A regular element $g$ is elliptic exactly when $P_g$ is irreducible over $F$. Every noncentral $d$ is regular elliptic, because a root of $P_d$ in $F$ would make $d-a$ a nonzero zero divisor in the division algebra.

We say that $g$ and $d$ **match**, and write $g\leftrightarrow d$, when

$$
t(g)=t(d),\qquad n(g)=n(d).
\tag{2.1}
$$

Equivalently, $P_g=P_d$. This definition immediately gives symmetry under inversion and central scaling. Indeed

$$
P_{zg}(X)=X^2-zt(g)X+z^2n(g),
$$

and the identical formula holds for $zd$. Likewise, the roots of the inverse polynomial are the inverse roots of the original polynomial. These elementary compatibilities are what character twists and contragredients later require.

### 2.2 Centralizers and rational conjugacy

Suppose $g\leftrightarrow d$ and put $E=F[X]/(P_g)$. Then

$$
C_G(g)\simeq E^\times\simeq C_{G'}(d).
\tag{2.2}
$$

The first isomorphism sends the class of $X$ to $g$; the second sends it to $d$. A common abstract torus therefore centralizes both matching elements.

There is exactly one rational conjugacy class on each side for a fixed irreducible quadratic polynomial. On the split side, two matrices with the same irreducible characteristic polynomial are conjugate because each turns $F^2$ into a free rank-one module over $E$. On the division side, the two generated quadratic fields are identified by sending one generator to the other, and conjugacy of quadratic embeddings in a central simple algebra carries that identification to inner conjugacy.

It follows that (2.1) is a bijection between regular elliptic conjugacy classes of $G$ and regular conjugacy classes of $G'$. There is no hidden multiplicity of rational classes in degree two. This fact is special to the present setting and is why no separate stable-conjugacy sum is needed.

It is useful to see this bijection without choosing a matrix. Given an irreducible polynomial

$$
P(X)=X^2-tX+n,
$$

let $E=F[X]/(P)$ and let $u$ be the class of $X$. Multiplication by $u$ on the two-dimensional $F$-space $E$ gives the split element. Any embedding $E\hookrightarrow D$ gives the division element. Changing an $F$-basis of $E$ conjugates the first element; changing the embedding conjugates the second. Thus the pair of classes depends only on $P$. Conversely, trace and norm recover $P$. This construction also shows that every abstract centralizer identification in (2.2) may be chosen to carry $g$ and $d$ to the same element $u$.

The word “regular” matters. If $P=(X-z)^2$, then the scalar $z$ and a nontrivial Jordan block have the same polynomial on the split side, while only the scalar exists in $D$. Separability of $P$ is what turns polynomial data into conjugacy data.

### 2.3 The common Weyl discriminant

Set

$$
\Delta(x)=t(x)^2-4n(x).
$$

For either group define the degree-two Weyl discriminant by

$$
D(x)=\left|\frac{\Delta(x)}{n(x)}\right|.
\tag{2.3}
$$

If the eigenvalues in a separable closure are $\alpha$ and $\beta$, then

$$
D(x)=|(1-\alpha/\beta)(1-\beta/\alpha)|.
$$

Thus $D(x)$ is the absolute determinant of $1-\operatorname{Ad}(x)$ on the quotient of the Lie algebra by the centralizer. Matching elements have the same trace and norm, hence

$$
D(g)=D(d).
\tag{2.4}
$$

This equality is what permits ordinary orbital integrals to be compared to ordinary orbital integrals, or normalized ones to normalized ones, without an extra discriminant factor.

### 2.4 Why split regular classes do not transfer

A split regular matrix has two distinct eigenvalues in $F$. Its characteristic polynomial factors over $F$. No element of $D\setminus F$ can have that polynomial, because it would generate a split quadratic algebra containing zero divisors. Hence split regular classes have no partner in $G'$.

This gives a useful counterexample to the idea that local transfer should compare all character values. A Steinberg character is nonzero on many split regular elements, while its division-side companion has no corresponding class there. The correspondence is determined on the common elliptic locus. It is not an equality of class functions after pretending that the two groups have the same conjugacy space.

## 3. Measures and orbital normalization

### 3.1 A compatible measure ledger

Pointwise characters require no Haar measure, but trace distributions and orbital integrals do. We fix measures in an order that prevents incompatible quotient normalizations:

$$
\operatorname{vol}(\operatorname{GL}_2(\mathcal O),dg)=1,
\qquad
\operatorname{vol}(\mathcal O_D^\times,dd)=1,
\tag{3.1}
$$

$$
\operatorname{vol}(\mathcal O^\times,dz)=1,
\qquad
\operatorname{vol}(\mathcal O_E^\times,de)=1
\tag{3.2}
$$

for every quadratic $E/F$. When $E^\times$ is the centralizer of matching elements, the same measure $de$ is used on both sides. Every quotient measure is then defined by Weil's formula. For example,

$$
\int_G f(x)\,dx
=\int_{E^\times\backslash G}
\int_{E^\times}f(ex)\,de\,d\dot x.
\tag{3.3}
$$

One must not additionally demand that every compact quotient visible in (3.3) have volume one. Those volumes have already been determined by (3.1), (3.2), and the quotient formula.

### 3.2 Ordinary and normalized orbital integrals

For a regular element $x$ with centralizer $E^\times$, define

$$
O_x(f)=\int_{E^\times\backslash H}f(y^{-1}xy)\,d\dot y,
\tag{3.4}
$$

where $H$ is the group containing $x$. The normalized orbital integral is

$$
I_x(f)=D(x)^{1/2}O_x(f).
\tag{3.5}
$$

Because of (2.4), the relation $O_g(f)=O_d(f')$ is equivalent to $I_g(f)=I_d(f')$ for matching elements. If one side of a proposed identity uses $O$ and the other uses $I$, an unwanted factor $D(g)^{1/2}$ appears. It is rarely constant on a packet and cannot be absorbed into the transfer sign.

### 3.3 Geometric and signed transfer conventions

There are two coherent ways to place the inner-form sign.

In **geometric transfer**, test functions $f$ on $G$ and $f'$ on $G'$ match when

$$
O_g(f)=O_d(f')
\tag{3.6}
$$

for every $g\leftrightarrow d$; in the elliptic transfer situation the split regular orbital integrals of $f$ also vanish, since split classes have no division-side partners. The character relation (1.4) then gives, for elliptic-supported functions after Weyl integration,

$$
\operatorname{tr}\pi(f)=-\operatorname{tr}\pi'(f').
\tag{3.7}
$$

In **signed spectral transfer**, one instead requires

$$
O_g(f)=-O_d(f').
\tag{3.8}
$$

and the corresponding traces are equal. Both usages occur naturally. The error is to use (3.8) and also insert another minus sign in the character identity. Throughout this book, “matching functions” means the geometric convention (3.6), while the pointwise identity always has the minus sign in (1.4).

Here is the passage from pointwise characters to (3.7). On the elliptic regular set, the Weyl integration formula decomposes a conjugation-invariant integral into integrals over quadratic tori. For a fixed $E/F$, choose representatives $u$ modulo the Weyl action $u\mapsto u^\sigma$. The contribution of that torus has the shape

$$
\frac1{2}\int_{E^\times_{\mathrm{reg}}}
\Theta_\pi(u)D(u)O_u(f)\,du,
$$

where the factor $1/2$ divides out the action of $\sigma$. The expression has the same torus measure, the same Weyl order two, and the same discriminant on each inner form. If one works from the outset modulo the common center, the integral is correspondingly written over regular classes in $E^\times/F^\times$. Substitute $\Theta_\pi(u)=-\Theta_{\pi'}(u)$ and (3.6). Every geometric factor cancels term by term, leaving exactly one minus sign. Compact support away from the singular center justifies the formula directly; general elliptic-supported functions follow by cutting off shrinking neighborhoods of the center and using local integrability.

This argument also shows why compatible torus measures are logically part of the distributional theorem. If the two copies of $E^\times$ were independently rescaled, a torus-dependent scalar would survive the cancellation and no single spectral sign could repair it.

### 3.4 Characters as functions and as distributions

For an admissible representation $\rho$ of either group,

$$
\rho(f)=\int_H f(h)\rho(h)\,dh,
\qquad
\operatorname{tr}\rho(f)=\int_H f(h)\Theta_\rho(h)\,dh
\tag{3.9}
$$

whenever the second expression is represented by the locally integrable character. Rescaling $dh$ does not change the ordinary matrix trace $\Theta_\rho(h)$. It does change the operator $\rho(f)$ and therefore changes the representing integral in tandem.

On $D^\times$, the representations under consideration are finite-dimensional, and subdivision by a sufficiently small compact open subgroup reduces (3.9) to a finite sum. The compact-induction character formula is itself a finite trace and contains no volume factor. This observation will be important in Chapters 6 and 7: the character sign comes from a finite Fourier comparison, not from a quotient-measure convention.

## 4. The special correspondence

### 4.1 The two representations

Let $\mu:F^\times\to\mathbf C^\times$ be smooth. On the split side put

$$
\pi_\mu=\operatorname{St}\otimes(\mu\circ\det).
$$

On the division side put

$$
\pi'_\mu=\mu\circ\operatorname{Nrd}.
$$

The first is infinite-dimensional and essentially square-integrable; the second is one-dimensional. Their dimensions plainly do not match. What does match is the central character and the elliptic trace after the inner-form sign.

### 4.2 The elliptic Steinberg character

We first calculate the untwisted character. The Steinberg representation is the nontrivial constituent of normalized induction at the exceptional ratio. Equivalently, it is the quotient of locally constant functions on $\mathbf P^1(F)$ by the constant functions. For a regular elliptic $g$, there is no fixed point on $\mathbf P^1(F)$, because a fixed point would be an $F$-eigenline.

The fixed-point observation must be interpreted distributionally: $C^\infty(\mathbf P^1(F))$ is infinite dimensional, so it has no ordinary operator trace. Take a sufficiently small regular neighborhood $U$ of $g$ on which every element remains elliptic. The kernel representing the character distribution of the projective-line permutation representation is supported on pairs $(x,h)$ with $hx=x$. There are no such pairs over $U$, so the induced character distribution restricts to zero on $U$. The exact sequence

$$
0\longrightarrow\mathbf1\longrightarrow
C^\infty(\mathbf P^1(F))\longrightarrow\operatorname{St}\longrightarrow0
$$

then shows, by additivity of distribution characters, that

$$
\Theta_{\operatorname{St}}(g)=-1
\tag{4.1}
$$

for regular elliptic $g$. This argument also explains why the answer changes on split regular classes: there the projective action has two fixed eigenlines.

Twisting multiplies a character value by the twisting character evaluated at the determinant. Hence

$$
\Theta_{\pi_\mu}(g)=-\mu(\det g).
\tag{4.2}
$$

### 4.3 The transfer sign

The division-side trace is immediate:

$$
\Theta_{\pi'_\mu}(d)=\mu(\operatorname{Nrd}d).
\tag{4.3}
$$

For matching elements, $\det g=\operatorname{Nrd}d$. Combining (4.2) and (4.3) proves

$$
\Theta_{\pi_\mu}(g)=-\Theta_{\pi'_\mu}(d).
\tag{4.4}
$$

This calculation anchors the sign for the entire correspondence. It also rules out redefining the division companion as its negative: a negative of a character is not the character of a representation, and the one-dimensional norm character has already fixed the only possible companion.

### 4.4 Twists, centers, and conductors

At a central element $z$, both representations act by $\mu(z^2)$, so

$$
\omega_{\pi_\mu}(z)=\mu(z)^2=\omega_{\pi'_\mu}(z).
\tag{4.5}
$$

If $\chi$ is another character of $F^\times$, then

$$
\pi_\mu\otimes(\chi\circ\det)=\pi_{\mu\chi},
\qquad
\pi'_\mu\otimes(\chi\circ\operatorname{Nrd})=\pi'_{\mu\chi}.
\tag{4.6}
$$

On $G'$ the symbol $a(\rho')$ denotes the transfer-facing conductor established by the division-side type theory, not the first principal-unit subgroup acting trivially. It is $1$ for an unramified norm character, $2a_F(\mu)$ for a ramified norm character, and $\ell_D(\rho')+2$ for a higher-dimensional type of normalized division level $\ell_D$. Chapter 9 identifies this integer with the exponent of the analytic epsilon factor.

The conductor formula is exceptional at the unramified boundary:

$$
a(\pi_\mu)=a(\pi'_\mu)=
\begin{cases}
1,&a_F(\mu)=0,\\
2a_F(\mu),&a_F(\mu)>0.
\end{cases}
\tag{4.7}
$$

On the split side, the unramified Steinberg twist has an Iwahori line but no hyperspecial line. On the division side, an unramified norm character is trivial on $\mathcal O_D^\times$ yet receives conductor one under the comparison normalization. For ramified $\mu$, the identity

$$
\operatorname{Nrd}(U_D^{2m-1})=\operatorname{Nrd}(U_D^{2m})=U_F^m
$$

shows that the division character first becomes trivial on $U_D^{2m-1}$. The transfer-facing conductor is the shifted exponent $2m$, in agreement with the split newvector level. Thus the same apparently irregular formula arises from two different group geometries.

### 4.5 Special local factors

The common parameter is the centered special block

$$
\operatorname{Sp}_2(\mu).
\tag{4.8}
$$

Its monodromy is nonzero, its determinant is $\mu^2$, and

$$
L(s,\pi_\mu)=L(s,\pi'_\mu)
=L\left(s+\frac12,\mu\right).
\tag{4.9}
$$

If $\mu$ is unramified and $\alpha=\mu(\Phi)=\mu(\varpi)$, this is

$$
\left(1-\alpha q^{-s-1/2}\right)^{-1}.
$$

For $n(\psi)=0$ and self-dual measure,

$$
\epsilon(s,\pi_\mu,\psi)
=\epsilon(s,\pi'_\mu,\psi)
=\epsilon(s,\operatorname{Sp}_2(\mu),\psi).
\tag{4.10}
$$

When $\mu$ is unramified this equals

$$
-\alpha q^{-(s-1/2)}.
\tag{4.11}
$$

For ramified $\mu$, the general monodromy formula, rather than (4.11), must be used. In particular, replacing every ramified twist by an unramified scalar produces the wrong Gauss phase.

The two cases can be derived directly from the centered block. Its underlying Weil representation is

$$
\mu|\cdot|^{1/2}\oplus\mu|\cdot|^{-1/2}.
$$

If $\mu$ is unramified, both lines are inertia invariant, but only the first lies in the kernel of monodromy. The Euler determinant therefore retains one line and the epsilon determinant contributes the missing line, yielding (4.9), (4.11). If $\mu$ is ramified, neither line is inertia invariant. The Euler factor is one and the monodromy correction has no invariant quotient on which to act. Thus

$$
\epsilon(s,\operatorname{Sp}_2(\mu),\psi)
=\epsilon(s+1/2,\mu,\psi)
\epsilon(s-1/2,\mu,\psi).
\tag{4.12}
$$

Each rank-one factor contributes conductor $a(\mu)$, explaining the second line of (4.7). Formula (4.12) is also useful when the twist is nonunitary: no appeal to an absolute-value-one root number is then appropriate.

## 5. Quadratic data and the rectifier

### 5.1 Admissible pairs

Let $E/F$ be separable quadratic and let $\sigma$ be its nontrivial automorphism. A character $\theta$ is regular when $\theta\ne\theta^\sigma$. Equivalently, it does not descend through the norm. Regularity is necessary for irreducibility of the induced two-dimensional parameter and for irreducibility of both representation constructions.

The extra admissibility condition says that if $\theta/\theta^\sigma$ is trivial on $U_E^1$, then $E/F$ must be unramified. In the ramified case, asymmetry confined to residue or valuation data has too much normalizer intertwining; induction from the naive torus ceases to produce the desired irreducible type. This is a useful warning: $\theta\ne\theta^\sigma$ alone is not the correct positive-depth hypothesis.

Pairs are equivalent when an $F$-isomorphism carries one character to the other. For fixed $E$, the equivalence class is the unordered orbit

$$
\{\theta,\theta^\sigma\}.
\tag{5.1}
$$

### 5.2 Direct and induction normalizations

The direct torus character has central restriction $\theta|_{F^\times}$. The determinant of the induced two-dimensional datum has an additional quadratic character. To make these agree, introduce the character-dependent tame rectifier $\Delta_{E/F,\theta}$ and set

$$
\theta^\natural=\theta\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F},
\tag{5.2}
$$

where $\omega_{E/F}$ has kernel $N_{E/F}(E^\times)$. In the unramified case the rectifier is the fixed unramified character taking a common uniformizer to $-1$. In the tamely ramified case it can depend on $\theta$; its normalized quadratic Gauss sum fixes the extension phase. Suppressing this dependence would make duality and some ramified epsilon phases false. The identities

$$
\Delta_{E/F,\theta^\sigma}=\Delta_{E/F,\theta}^\sigma,
\qquad
\Delta_{E/F,\theta(\chi\circ N_{E/F})}=\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta^{-1}}=\Delta_{E/F,\theta}^{-1}
\tag{5.2a}
$$

make conjugation, twisting, and contragredience compatible with this normalization. The rectifier is unramified when $E/F$ is unramified and has conductor at most one when $E/F$ is tamely ramified. Since a ramified admissible character has conductor at least two, it does not alter the conductor in the selected range. All dihedral representations below use the induction normalization $\theta^\natural$.

This small-looking correction prevents three simultaneous errors. Without it, the central character would omit $\omega_{E/F}$, the finite Gauss traces on the two inner forms would differ by a torus phase rather than a constant sign, and the proposed parameter determinant would not match the representation center.

### 5.3 The two representations attached to a pair

The tame construction on $G$ gives an irreducible supercuspidal representation

$$
\pi(E,\theta).
$$

The quadratic type construction on $G'$ gives

$$
\pi'(E,\theta)
=\operatorname{Ind}_{J'}^{G'}\Lambda'_{\theta^\natural},
\tag{5.3}
$$

where $J'=E^\times J'^1$ and $J'^1=U_D^1$ at depth zero. At positive depth, $J'^1$ carries the simple character and its finite Heisenberg enlargement. On the split side there is an analogous compact-mod-center group $J=E^\times J^1$ and a type $\Lambda_{\theta^\natural}$ whose compact induction is $\pi(E,\theta)$.

The bare torus is generally insufficient on both sides. At positive depth, its last nontrivial unit character must be extended across a noncommutative congruence quotient. The simple character and Heisenberg representation record precisely the missing commutator data.

### 5.4 Equivalence, twists, and minimality

Both constructions depend only on (5.1), and each is injective on equivalence classes in the selected family. If $\chi$ is a character of $F^\times$, then

$$
\pi(E,\theta)\otimes(\chi\circ\det)
\simeq\pi(E,\theta(\chi\circ N_{E/F})),
\tag{5.4}
$$

$$
\pi'(E,\theta)\otimes(\chi\circ\operatorname{Nrd})
\simeq\pi'(E,\theta(\chi\circ N_{E/F})).
\tag{5.5}
$$

A positive-depth pair is minimal when no such norm twist lowers $a_E(\theta)$. Every tame pair is a norm twist of a minimal one. The proof repeatedly cancels a norm-derived final unit layer; the conductor strictly decreases, so the process terminates. It is therefore enough to compare minimal types and then apply (5.4), (5.5). This reduction is essential near the center, where a nonminimal presentation can hide cancellation.

## 6. Depth-zero character matching

### 6.1 The finite elliptic calculation

Assume $E/F$ is unramified and $a_E(\theta)=1$. Let $k_2/k$ be the quadratic residue extension and let $\bar\theta:k_2^\times\to\mathbf C^\times$ be regular. The depth-zero split type contains the cuspidal representation of $\operatorname{GL}_2(k)$ attached to $\bar\theta$; the division type is the index-two induction from $E^\times U_D^1$.

The unramified rectifier is trivial on $\mathcal O_E^\times$, so $\theta$ and $\theta^\natural$ have the same residue character $\bar\theta$. Their values on a uniformizer can differ, and the rectified character must be retained once valuation is visible.

For $x\in k_2^\times\setminus k^\times$, the division trace is the permutation-induction sum

$$
\bar\theta(x)+\bar\theta(x^q).
\tag{6.1}
$$

The split finite cuspidal trace at the elliptic class with eigenvalues $x,x^q$ is

$$
-\bar\theta(x)-\bar\theta(x^q).
\tag{6.2}
$$

Here is a proof that also locates the sign. Realize the finite cuspidal representation through functions on the nonsplit torus with the regular character prescribed, and apply the finite Fourier transform on the one-dimensional quotient complementary to the torus. The identity term gives no invariant vector because $\bar\theta$ is regular. The two torus embeddings contribute the two terms in (6.1). The Fourier transform on the complementary line contributes the sign of the rank-one alternating orientation, namely $-1$. This yields (6.2).

We spell out the trace step. Let $V=k_2$ as a two-dimensional $k$-space and let $T=k_2^\times$ act by multiplication. The endomorphism algebra generated by translations on $V$ and multiplication by $T$ contains the idempotent

$$
e_{\bar\theta}
=\frac1{|T|}\sum_{t\in T}\bar\theta(t)^{-1}[t].
$$

Regularity makes the $\bar\theta$- and $\bar\theta^q$-summands distinct. The finite Fourier transform with respect to

$$
(u,v)\longmapsto
\psi_k\bigl(\operatorname{Tr}_{k_2/k}(uv^q)\bigr)
$$

interchanges the two Bruhat cells. For an elliptic multiplication operator $x$, all off-diagonal translation terms occur in nontrivial additive-character orbits and sum to zero. The two stationary terms are $x$ and $x^q$. Passing from the ambient two-cell space to its cuspidal quotient subtracts rather than adds the second cell, so the trace is

$$
-\bar\theta(x)-\bar\theta(x^q).
$$

No division by $q-1$ remains: the idempotent denominator is canceled by the size of each free $T$-orbit. This direct finite calculation proves both the value and its independence of a choice of basis for $k_2/k$.

### 6.2 Lifting from the residue field

Let $g\leftrightarrow d$ be depth-zero type-regular elements. After central scaling, both lie in their maximal compact groups and have regular elliptic reductions. Their common characteristic polynomial identifies the reductions with the same element $x\in k_2^\times\setminus k^\times$. Inflation of the finite types and the induced-character formula give

$$
\Theta_{\pi(E,\theta)}(g)
=-\bigl(\theta^\natural(e)+(\theta^\natural)(e^\sigma)\bigr),
$$

$$
\Theta_{\pi'(E,\theta)}(d)
=(\theta^\natural)(e)+(\theta^\natural)(e^\sigma),
\tag{6.3}
$$

with $e$ the common torus coordinate. Central valuation factors agree because both central characters are

$$
\theta|_{F^\times}\omega_{E/F}.
$$

Thus the finite identity lifts without a new scalar.

### 6.3 Central and irregular counterexamples

At a central element $z$, the division character has value

$$
\dim\pi'(E,\theta)\,\omega(z),
$$

not a sum of two distinct regular torus contributions. Central elements are singular and are not part of (1.4). Extending the regular identity to them would equate representations of different dimensions and is impossible.

If $\bar\theta=\bar\theta^q$, the index-two induction splits, while the finite cuspidal construction degenerates. Formula (6.1) still makes sense as a number, but it no longer identifies a pair of irreducible representations. This shows why regularity belongs in the theorem rather than being inferred after a character calculation.

### 6.4 The depth-zero theorem

Central scaling reduces the valuation to one of two parities, but it does **not** always give regular elliptic reduction: an elliptic element arbitrarily close to a scalar has scalar reduction. We must account for these missing annuli rather than infer them from (6.3).

Use the exact compact-induction character formula on the split side and the index-two formula on the division side. The split fixed cosets are vertices, or oriented terminal edges, in the finite subtree fixed by the elliptic element at the level through which the depth-zero type factors. Filter this tree inward from its outer boundary. At a nonterminal scalar-reduction vertex, there are $q-1$ transverse directions with nontrivial unipotent reduction. The scalar term contributes

$$
(q-1)\overline\theta^\natural(z),
$$

while the sum of the $q-1$ transverse finite-cuspidal terms is

$$
-(q-1)\overline\theta^\natural(z).
$$

Finite additive-character orthogonality gives the second equality: the nontrivial unipotent parameters run through $k^\times$, and their complete sum is the negative of the missing zero parameter. Thus deleting an outer shell changes neither the total split trace nor its proposed negative division trace.

The fixed subtree is finite for a regular elliptic element. Repeating the shell deletion reaches its terminal vertex or edge. The two terminal orientations are precisely the two valuation cosets in the division induced model. At that terminal piece the calculation is the regular-reduction identity (6.2), with the two embeddings $e,e^\sigma$. Consequently the telescoped split trace is the negative of the full division trace. This proves

$$
\Theta_{\pi(E,\theta)}(g)
=-\Theta_{\pi'(E,\theta)}(d)
\tag{6.4}
$$

for every matching regular pair in the depth-zero packet, including the scalar-reduction annuli near the center. The proof also shows why local constancy alone was insufficient: the regular neighborhoods shrink as the singular center is approached, while the finite shell cancellation supplies the missing uniform comparison.

## 7. Positive-depth tame matching

### 7.1 A common simple character

Now let $(E,\theta)$ be a positive-depth minimal tame admissible pair. On its last visible unit layer, $\theta$ has the form

$$
\theta(1+x)=\psi_E(\beta x)
\tag{7.1}
$$

for a suitable $\beta\in E$ determined modulo a deeper trace-dual lattice. Under embeddings $E\hookrightarrow M_2(F)$ and $E\hookrightarrow D$, the two ambient simple characters are

$$
1+X\longmapsto\psi(\operatorname{tr}(\beta X)),
\qquad
1+Y\longmapsto\psi(\operatorname{Trd}(\beta Y)).
\tag{7.2}
$$

Their restrictions to $E$ are the same character (7.1). The centralizer of the leading class of $\beta$ is exactly $E$. Minimality ensures that it is noncentral and that no larger intertwining group appears.

The comparison is therefore concentrated in the complementary directions to $E$. Those directions differ between the split algebra and the division algebra, while their trace pairings have opposite discriminant orientation. This is the local source of the sign.

### 7.2 The finite Fourier comparison

Let $V$ and $V'$ be the finite additive quotients on which the split and division Heisenberg extensions are built. Their commutator forms are

$$
\langle X,Y\rangle_\beta
=\psi(\operatorname{tr}(\beta[X,Y])),
$$

and the analogous reduced-trace formula. Tameness makes these alternating forms nondegenerate after quotienting by their radicals.

Choose maximal isotropic subspaces and realize each Heisenberg representation by finite induction. For a torus element $e$ normalizing the data, its trace is a normalized finite sum

$$
\gamma_\beta(e)
=\frac1{|L|}\sum_{x\in L}\vartheta_\beta([e,x]).
\tag{7.3}
$$

The value does not depend on the chosen polarization. The split and division sums have the same absolute magnitude and the same dependence on $e$. Their quotient is the product of two one-dimensional quadratic Fourier indices: the common torus direction cancels, and the complementary trace forms differ by the unique nonsplit quaternion class. Consequently

$$
\gamma^{G}_\beta(e)=-\gamma^{G'}_\beta(e)
\tag{7.4}
$$

after inserting the rectifier attached to the datum.

The finite statement used here may be isolated as follows.

**Lemma 7.1 (opposite complementary Fourier indices).** Let $A$ be either $M_2(F)$ or $D$, let $E\subset A$ be the same tame quadratic field, and let $\beta\in E$ have centralizer $E$. Form the last nontrivial quotient of the lattice complementary to $E$ and endow it with the commutator pairing induced by

$$
(X,Y)\longmapsto\psi(\operatorname{Tr}_{A/F}(\beta[X,Y])).
$$

After quotienting by the common radical, the normalized Fourier traces for $M_2(F)$ and $D$ differ by $-1$ once the tame rectifier is included.

**Proof.** Choose $j$ with $jz=\sigma(z)j$ for $z\in E$. The complementary line is $Ej$. In the split algebra one may choose $j^2=c$ with $c$ in the norm class that makes the cyclic algebra split; in $D$, $j^2=c'$ lies in the other class of $F^\times/N_{E/F}(E^\times)$. On the graded quotient, the commutator form is the trace of a scalar multiple of

$$
(u,v)\longmapsto u\sigma(v)-v\sigma(u).
$$

All common torus and radical directions cancel, so the relative index is already visible on the first two-dimensional quotient complementary to the graded centralizer. After multiplying both forms by the same nonzero scalar, the split quadratic phase is the hyperbolic form $(u,v)\mapsto uv$ on $k^2$, while the division phase is the anisotropic norm $z\mapsto N_{k_2/k}(z)$ on $k_2$. For every nontrivial additive character $\overline\psi$ of $k$,

$$
q^{-1}\sum_{u,v\in k}\overline\psi(uv)=1,
\qquad
q^{-1}\sum_{z\in k_2}\overline\psi(N_{k_2/k}(z))=-1.
\tag{7.4a}
$$

The first equality follows by summing in $v$: only $u=0$ survives. For the second, zero has one preimage under the norm and each element of $k^\times$ has $q+1$ preimages, so the sum is

$$
q^{-1}\left(1+(q+1)\sum_{a\in k^\times}\overline\psi(a)\right)
=q^{-1}(1-(q+1))=-1.
$$

This is the concrete form of $\omega_{E/F}(c'/c)=-1$. A change of $j$, additive coordinate, or polarization multiplies both indices by the same norm-class factor. The direct torus extensions contribute a further one-dimensional phase; the normalized Gauss-sum definition of $\Delta_{E/F,\theta}$ cancels that common labeling discrepancy. The relative trace is therefore exactly $-1$. $\square$

The lemma is valid at every tame positive depth because successive lattice quotients are trace-dual and the same cyclic-algebra class controls each complementary form. Wild ramification would destroy this uniform reduction: the trace-dual jumps and extension operators can contain additional data. This pinpoints the scope of the argument.

Formula (7.4a) also shows directly that no unrecorded root of unity remains. The rectifier cancels the one-dimensional torus Gauss factor, while the normalized hyperbolic and anisotropic sums contribute exactly $1$ and $-1$.

### 7.3 The type-regular range

Suppose the conjugacy class of $e\in E^\times$ meets each inducing group only through the two normalizer embeddings. The induced-character formulas are then

$$
\Theta_{\pi(E,\theta)}(g)
=\operatorname{tr}\Lambda_{\theta^\natural}(e)
+\operatorname{tr}\Lambda_{\theta^\natural}(e^\sigma),
$$

$$
\Theta_{\pi'(E,\theta)}(d)
=\operatorname{tr}\Lambda'_{\theta^\natural}(e)
+\operatorname{tr}\Lambda'_{\theta^\natural}(e^\sigma).
\tag{7.5}
$$

Equations (7.3), (7.4) apply separately to the two summands. Hence (1.4) holds throughout the type-regular range.

This proof also explains why comparing only the bare torus characters is insufficient. The factors $\gamma_\beta(e)$ carry the effect of the noncommutative congruence quotient. Ignoring them can accidentally give the right answer at depth zero and the wrong phase at positive depth.

### 7.4 Near-central correction terms

When $e$ approaches $F^\times$, additional conjugates of the inducing subgroup can contain it. The two-term formula (7.5) must then be replaced by

$$
\Theta_\pi(x)
=\sum_{y\in J\backslash H\atop yxy^{-1}\in J}
\operatorname{tr}\Lambda(yxy^{-1}),
\tag{7.6}
$$

with $(H,J,\Lambda)=(G,J,\Lambda)$ or $(G',J',\Lambda')$. Formula (7.6) is finite after quotienting by the center in the compact-induction model relevant to the trace.

The remaining task is to pair the extra summands. Filter them by the smallest integer $r$ for which the conjugate embedding agrees with the fixed embedding modulo the $r$th congruence layer. Matching characteristic polynomials identify the resulting embedding sets on the two sides. On each graded fiber, conjugation gives an affine space over $k$ and the trace contribution is a finite Fourier sum governed by the same form as in Section 7.2. Nonstationary fibers sum to zero. Stationary fibers occur in paired split and division copies, and (7.4) gives a minus sign on each pair.

At the final, closest-to-central layer, the radical grows. Quotient first by the common radical, which is the torus direction, and apply the nondegenerate comparison on the quotient. The radical contributes the identical cardinality on both sides, so it does not alter the sign. This completes the correction calculation.

More explicitly, let $\mathcal X_r$ and $\mathcal X'_r$ denote the embeddings agreeing with the fixed torus embedding through depth $r$ but not $r+1$. Conjugation by the next unit quotient acts transitively on each nonempty fiber, and the stabilizer is the radical of the commutator form. Matching trace and norm identify the affine parameters of $\mathcal X_r$ and $\mathcal X'_r$. Summing (7.6) over one orbit gives

$$
|\operatorname{rad}_r|
\sum_{v\in V_r/\operatorname{rad}_r}
\psi(q_r(v)),
$$

where $q_r$ is the quadratic phase obtained from the commutator. Lemma 7.1 compares the two nondegenerate sums. The radical sizes agree because the common $E$-lattice has the same trace-dual length. Hence the entire $r$th shells differ by $-1$. Summing over $r$ proves the correction identity without assuming the two-normalizer formula.

There is no convergence issue in this shell calculation. Smoothness makes all sufficiently deep conjugations act trivially, and regularity keeps the shell range finite before the scalar locus is reached.

The filtration argument is the decisive reason the type-regular identity extends to every regular elliptic element. Local constancy alone would not suffice: its neighborhoods shrink near the singular center, and equality on a dense-looking subset need not cross those shrinking annuli without the explicit graded pairing.

### 7.5 Completion of the character identity

For a minimal positive-depth tame pair, Sections 7.3 and 7.4 prove

$$
\Theta_{\pi(E,\theta)}(g)
=-\Theta_{\pi'(E,\theta)}(d)
\tag{7.7}
$$

for every matching regular pair. For a nonminimal pair, write

$$
\theta=\theta_0(\chi\circ N_{E/F})
$$

with $\theta_0$ minimal. Matching gives $\det g=\operatorname{Nrd}d$, so twisting both sides of the identity for $\theta_0$ by $\chi$ proves (7.7) for $\theta$. Together with Chapter 6, this establishes character matching for all selected tame dihedral packets.

## 8. Consequences of character matching

### 8.1 Central characters and contragredients

For a quadratic pair, both central characters are

$$
\boxed{\omega(z)=\theta(z)\omega_{E/F}(z).}
\tag{8.1}
$$

The formula is also the determinant of $\operatorname{Ind}_{W_E}^{W_F}\theta$. One can recover equality of central characters directly from the regular identity: replace a fixed matching pair $(g,d)$ by $(zg,zd)$ and divide by the original nonzero character value on a sufficiently small regular neighborhood. The minus signs cancel and yield equality on $z$.

Inversion preserves matching. The distribution character of a smooth contragredient satisfies

$$
\Theta_{\rho^\vee}(x)=\Theta_\rho(x^{-1})
$$

on the regular set: transpose does not change the trace of the finite-rank convolution operator, and inversion changes the test function by the modular factor, which is one for both groups. Hence the correspondence commutes with contragredients. On labels this sends $\theta$ to $\theta^{-1}$ and $\mu$ to $\mu^{-1}$.

### 8.2 Exact twisting laws

Equations (4.6), (5.4), and (5.5) show

$$
\operatorname{JL}(\pi\otimes(\chi\circ\det))
=\operatorname{JL}(\pi)\otimes(\chi\circ\operatorname{Nrd})
\tag{8.2}
$$

in the selected range. This is also forced by characters, because matching elements have equal determinant and reduced norm.

Conductor behavior under twisting must be stated through the actual twisted label. For a dihedral pair,

$$
a\bigl(\pi(E,\theta)\otimes\chi\bigr)
=a\bigl(\pi'(E,\theta)\otimes\chi\bigr)
$$

$$
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E\bigl(\theta(\chi\circ N_{E/F})\bigr).
\tag{8.3}
$$

A maximum formula is false when the final unit layers cancel.

### 8.3 Conductors and depth patterns

For every tame admissible pair,

$$
\boxed{
a(\pi(E,\theta))=a(\pi'(E,\theta))
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).}
\tag{8.4}
$$

If $E/F$ is unramified, this becomes $2a_E(\theta)$; depth-zero gives conductor two. If $E/F$ is tamely ramified quadratic, it becomes $a_E(\theta)+1$, and admissibility forces $a_E(\theta)\ge2$. These parity patterns are useful diagnostics for minimal pairs, but twisting can disguise them.

The proof of equality is not merely a consequence of character matching. On the split side it comes from the newvector filtration, and on the division side from reduced-trace duality and the comparison shift in the definition of $a_{G'}$. Formula (8.4) shows that both measurements are expressions of the Artin conductor of the same quadratic induction.

### 8.4 Why numerical invariants do not determine transfer

Central character and conductor do not characterize a dihedral representation. Distinct regular residue characters of $k_2^\times$ can have the same restriction to $k^\times$ and the same conductor. Their depth-zero packets are separated by the sums

$$
\bar\theta(x)+\bar\theta(x^q)
$$

on elliptic elements. Likewise, an unramified and a ramified quadratic pair can acquire the same central character and total conductor after twisting while retaining different centralizer fields.

Local factors alone need not separate them either: every irreducible two-dimensional induced parameter has Euler factor one. The epsilon phase contains more information, but even conductor plus epsilon is not a complete character table. The regular elliptic identity is therefore the defining strength of the correspondence; the numerical compatibilities are consequences and consistency tests.

## 9. Local parameters and local factors

### 9.1 The common parameter assignment

We attach the following two-dimensional Frobenius-semisimple Weil--Deligne data:

$$
\pi_\mu,\ \pi'_\mu
\longmapsto \operatorname{Sp}_2(\mu),
\tag{9.1}
$$

$$
\pi(E,\theta),\ \pi'(E,\theta)
\longmapsto
\operatorname{Ind}_{W_E}^{W_F}\theta,
\qquad N=0.
\tag{9.2}
$$

Characters of multiplicative groups are read as Weil characters through (1.2). Regularity makes (9.2) irreducible. These assignments are determined by the selected labels, so their equality across transfer is a theorem about the constructions rather than an appeal to a broader classification.

### 9.2 Determinants and conductors

For (9.1), the centered block has determinant $\mu^2$ and conductor (4.7). For (9.2), the determinant formula is

$$
\det\operatorname{Ind}_{W_E}^{W_F}\theta
=\theta|_{F^\times}\omega_{E/F},
\tag{9.3}
$$

and induction of Artin conductors gives

$$
a_F\left(\operatorname{Ind}_{W_E}^{W_F}\theta\right)
=v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta).
\tag{9.4}
$$

Equations (9.3), (9.4) reproduce (8.1), (8.4). They also check the residue-degree factor: omitting $f(E/F)$ would give the wrong even conductor for an unramified quadratic pair.

### 9.3 Euler and epsilon factors

The common parameter predicts the answer, but preservation would be empty if the division-side factors were merely defined to equal the parameter factors. We therefore compare the independently constructed analytic factors. On $G$, they come from Whittaker zeta integrals. On $G'$, for a matrix coefficient $c$ and $\Phi_D\in C_c^\infty(D)$, they come from

$$
Z_D(s,\Phi_D,c)
=\int_{D^\times}\Phi_D(x)c(x)
|\operatorname{Nrd}(x)|^{s+1/2}\,d^\times x.
$$

The division functional equation uses the self-dual additive measure for $(x,y)\mapsto\psi(\operatorname{Trd}(xy))$ and the signed Fourier transform

$$
\mathcal F_D\Phi_D(y)
=-\int_D\Phi_D(x)\psi(\operatorname{Trd}(xy))\,dx.
$$

The sign is the anisotropic degree-two Hasse sign.

**Proposition 9.1 (division functional equation in the selected range).** For a selected irreducible $\pi'$ and its contragredient, the integrals $Z_D(s,\Phi_D,c)$ span a principal fractional ideal in $\mathbf C[q^s,q^{-s}]$; write its normalized generator as $L_D(s,\pi')$. If $\check c(x)=c(x^{-1})$, there is a scalar rational function $\gamma_D(s,\pi',\psi)$, independent of $\Phi_D$ and $c$, such that

$$
Z_D(1-s,\mathcal F_D\Phi_D,\check c)
=\gamma_D(s,\pi',\psi)Z_D(s,\Phi_D,c).
$$

The division epsilon factor is determined by

$$
\gamma_D(s,\pi',\psi)
=\epsilon_D(s,\pi',\psi)
\frac{L_D(1-s,(\pi')^\vee)}{L_D(s,\pi')}.
$$

**Proof.** Smoothness and finite dimensionality give $r$ such that $U_D^r$ acts trivially on $\pi'$. Subdivide $D^\times$ into cosets of $U_D^r$ and reduced-norm valuation shells. On each compact valuation interval the zeta integral is a finite matrix sum. Multiplication by a division prime translates the tail by one shell and its square is central, so the tail satisfies a recurrence of degree at most two; hence the integral is rational in $q^{-s}$.

For the reduced-trace pairing one has

$$
(\mathfrak P_D^m)^\perp=\mathfrak P_D^{-m-1}.
$$

The signed Fourier transform therefore exchanges characteristic functions of lattice cosets with explicit character multiples of their annihilator cosets. On the intervening finite quotients its square is reflection; multiplying the Fourier transform by $-1$ does not alter this inversion law, but inserts the degree-two anisotropic sign in the one-step functional-equation scalar. Pairing this finite operator with matrix coefficients of $\pi'$ and $(\pi')^\vee$, Schur orthogonality makes the proportionality operator scalar on the irreducible isotypic block and independent of the coefficient. Passage through deeper quotients gives the functional equation for every test function. Removing the shell recurrences gives the Euler generators; the remaining scalar is a monomial times a finite Gauss sum, hence the epsilon factor. $\square$

With this functional-equation normalization, the independently constructed division Euler and epsilon factors satisfy

$$
L(s,\pi)=L(s,\operatorname{JL}(\pi)),
\qquad
\epsilon(s,\pi,\psi)=\epsilon(s,\operatorname{JL}(\pi),\psi).
\tag{9.5}
$$

Therefore, with

$$
\gamma(s,\pi,\psi)
=\epsilon(s,\pi,\psi)
\frac{L(1-s,\pi^\vee)}{L(s,\pi)},
$$

one also has

$$
\gamma(s,\pi,\psi)
=\gamma(s,\operatorname{JL}(\pi),\psi).
\tag{9.5a}
$$

Here is the calculation. For $\mu\circ\operatorname{Nrd}$, decompose $D^\times$ into reduced-norm valuation shells. Unit averaging kills the Euler tail when $\mu$ is ramified. When $\mu$ is unramified, the shell sum is the geometric series with root $\mu(\varpi)q^{-s-1/2}$, giving (4.9). Fourier reversal leaves one endpoint; the displayed minus sign makes it $-\mu(\varpi)q^{-(s-1/2)}$. In the ramified case the two boundary unit sums are the rank-one factors for $\mu|\cdot|^{1/2}$ and $\mu|\cdot|^{-1/2}$. This proves (4.10)--(4.12) from the division coefficient integral as well as from the special parameter.

For a dihedral type, choose a matrix coefficient supported on the inducing subgroup $J'$. Frobenius reciprocity reduces the coefficient integral to $J'$. On the simple-character subgroup, additive Fourier transform is the finite Heisenberg transform of Chapter 7. A maximal isotropic polarization cancels the variables complementary to $E$ in pairs; the remaining integral is the rank-one Tate integral over $E$ for $\theta$ and $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$. The anisotropic Fourier sign and the complementary index (7.4a) cancel, while comparison of self-dual measures contributes exactly $\lambda(E/F,\psi)$. Regularity makes the unit average zero, so no Euler denominator remains. Thus the independently constructed division factors equal the parameter factors, proving (9.5).

Equivalently, for dihedral packets irreducibility of (9.2) implies that the inertia-invariant space is zero unless the representation were unramified and therefore reducible. Hence

$$
L(s,\pi(E,\theta))=L(s,\pi'(E,\theta))=1.
\tag{9.6}
$$

Let $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$. The induction formula gives

$$
\epsilon_F\left(s,\operatorname{Ind}_{W_E}^{W_F}\theta,\psi\right)
=\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E).
\tag{9.7}
$$

The lambda factor cannot generally be omitted, especially for ramified $E/F$. Formula (9.7) displays the finite Gauss phase that is invisible to conductor equality.

The equality of Euler factors in the induction formula can be seen without a character table. Inertia acts on the two cosets of $W_E$ in $W_F$. If $E/F$ is unramified, inertia fixes the cosets and the invariant space would require both $\theta|_{I_E}$ and $\theta^\sigma|_{I_E}$ to be trivial. Then $\theta$ would be unramified and fixed by $\sigma$, contradicting regularity. If $E/F$ is ramified, inertia acts transitively on the cosets; an invariant vector would give an unramified subrepresentation of the irreducible induction. Such a two-dimensional irreducible unramified representation cannot exist because the unramified Weil quotient is cyclic. Thus the invariant space is zero in both cases, proving (9.6).

The monomial exponent of (9.7) provides another conductor check. With self-dual measures it is

$$
q^{-\left[v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta)
+2n(\psi)\right](s-1/2)}.
$$

The trace character $\psi_E$ has conductor shifted by the inverse different. Converting its exponent from $q_E=q^{f(E/F)}$ back to $q$ supplies exactly the discriminant term above. The remaining constant is the product of the normalized Gauss sum of $\theta$ and $\lambda(E/F,\psi)$.

### 9.4 Dependence on additive characters and measures

For $a\in F^\times$ and $\psi_a(x)=\psi(ax)$, both members transform by the same rule

$$
\epsilon(s,\pi,\psi_a)
=\omega_\pi(a)|a|^{2(s-1/2)}\epsilon(s,\pi,\psi).
\tag{9.8}
$$

If the additive Haar measure on the base field $F$ used to normalize rank-one factors is multiplied by $b>0$ while $\psi$ is fixed, a two-dimensional epsilon factor is multiplied by $b^2$. The additive measure on the four-dimensional space $D$ in the coefficient integral is then chosen compatibly with the reduced-trace pairing; it is not independently rescaled. Thus equality in (9.5) survives a common coherent change, but a formula stated with a self-dual measure on one side and an unrelated volume-one measure on the other is not meaningful.

For an unramified twist $\chi$ with $\chi(\Phi)=\beta$,

$$
\epsilon(s,\pi\otimes\chi,\psi)
=\beta^{a(\pi)+2n(\psi)}\epsilon(s,\pi,\psi),
\tag{9.9}
$$

on both sides. This is a stringent joint check of the Frobenius, reciprocity, conductor, and additive-character conventions.

## 10. Types, newvectors, and level

### 10.1 What can and cannot correspond

The split representation is usually infinite-dimensional and has a one-dimensional newvector line at its conductor level. The division representation is finite-dimensional, and its normal principal-unit subgroups fix either the whole representation or nothing. Therefore there is no natural isomorphism between full fixed-vector spaces at equal-looking subgroups.

The correct comparison is between the split newvector line and the distinguished multiplicity line of the division type, together with equality of conductor exponents. This formulation retains the arithmetic information without asserting a false equality of dimensions.

### 10.2 Special type lines

For unramified $\mu$, $\pi_\mu$ has a one-dimensional Iwahori-fixed line on which the finite Iwahori quotient acts through the sign character. The companion $\pi'_\mu$ is trivial on $\mathcal O_D^\times$. These are the minimal type lines selected by conductor one.

For ramified $\mu$ of conductor $m$, the split newvector occurs at $\mathcal K_1(\mathfrak p^{2m})$. The division character becomes trivial on the corresponding reduced-norm layer, and (4.7) again selects conductor $2m$. A generator on either side is only defined up to a scalar; transfer does not canonically identify those scalars.

The minimality assertion can be checked in the exceptional induced model of Steinberg. The ambient normalized principal series has inducing characters $\mu|\cdot|^{1/2}$ and $\mu|\cdot|^{-1/2}$. When $m>0$, both have conductor $m$, so the first possible $\mathcal K_1$-level is $2m$. The one-dimensional exceptional constituent has no such fixed vector, forcing the line into the Steinberg constituent. When $m=0$, the spherical line lies in the one-dimensional constituent and disappears from Steinberg; the next Iwahori line survives. This recovers both cases of (4.7) at the level of actual vectors.

### 10.3 Dihedral type multiplicity spaces

Let $\Lambda$ and $\Lambda'$ be the split and division types attached to $(E,\theta)$. Their defining property is multiplicity one:

$$
\dim\operatorname{Hom}_{J}(\Lambda,\pi(E,\theta))=1,
$$

$$
\dim\operatorname{Hom}_{J'}(\Lambda',\pi'(E,\theta))=1.
\tag{10.1}
$$

The common simple-character restriction and the finite Fourier comparison canonically identify the labels of these lines. After choosing primitive torus vectors, the comparison is unique up to a unit in the coefficient ring. This is the local type compatibility needed for level change.

On the split side, the unique newvector at level (8.4) is obtained from the type line by the standard compact averaging compatible with its central character. On the division side, the corresponding object remains the type multiplicity line; averaging over a normal unit subgroup would instead produce the entire representation.

To see why the averaging gives only one split line, decompose the compact induction over

$$
J\backslash G/\mathcal K_1(\mathfrak p^{a(\pi)}).
$$

The conductor calculation says that exactly one double coset has a stabilizer on which the type and the required lower-right character agree. Frobenius reciprocity identifies its contribution with the one-dimensional space in (10.1); all other cosets vanish by the last nontrivial simple-character layer. At a higher level, successive diagonal translates create the oldvectors counted by (10.2).

For $D^\times$, the analogous Mackey calculation selects the prescribed occurrence of $\Lambda'$ inside restriction. The unit groups are normal, so their fixed spaces cannot isolate that occurrence; the torus character inside $\Lambda'$ does. This is why the phrase “division newvector” always means a multiplicity or toric line here, never an arbitrary principal-unit fixed vector.

### 10.4 Oldvectors and the anisotropic contrast

For $r\ge a(\pi)$, the split oldspace satisfies

$$
\dim\pi^{\mathcal K_1(\mathfrak p^r)}=r-a(\pi)+1.
\tag{10.2}
$$

No analogous linear growth holds on $D^\times$. Once a normal $U_D^r$ lies in the kernel, all vectors are fixed, so the dimension jumps to $\dim\pi'$. This is not a failure of the correspondence. The conductor and the distinguished type line are preserved; the surrounding oldform geometries belong to different groups.

## 11. Integral compatibility

### 11.1 Coefficient rings and unit-valued data

Let $L/\mathbf Q_\ell$ be finite with valuation ring $R$, and assume $\ell\ne p$. A selected datum is integral when its character values lie in $L^\times$ and are units of $R$. This condition includes finite-order tame data after enlarging $L$, and includes an unramified scalar only when that scalar is an $\ell$-adic unit.

The unit condition is necessary. If an unramified character sends $\varpi$ to a nonunit, no nonzero finite $R$-lattice can be stable under both $\varpi$ and $\varpi^{-1}$. Thus integral compatibility cannot be asserted for arbitrary complex labels after an unspecified change of coefficients.

### 11.2 Integral special lines

For unit-valued $\mu$, the division companion has the rank-one stable lattice

$$
R(\mu\circ\operatorname{Nrd}).
$$

The split Steinberg twist has its standard lattice of locally constant $R$-valued functions on $\mathbf P^1(F)$ modulo constants, twisted by $\mu$. Its minimal type line is a free rank-one direct summand. The exact sequence used in the distributional calculation of (4.1) is defined over $R$, so the character sign and type-line comparison survive scalar extension.

### 11.3 Integral dihedral types

At depth zero, the inducing characters preserve rank-one lattices. At positive depth, the simple character takes values in roots of unity of $p$-power order, which are units because $\ell\ne p$. The Heisenberg model is finite induction from a maximal isotropic subgroup; hence it admits a finite free stable lattice. To extend across the tame normalizer, begin with any full lattice in the characteristic-zero extension space and take the sum of its translates under the finite quotient through which the normalized extension acts. This orbit sum is full, finite, torsion free, and stable, hence finite free over the DVR $R$. It proves existence without assuming that one rescaling simultaneously integralizes an entire projective action.

Write $\Lambda_R$ and $\Lambda'_R$ for the resulting type lattices. The full division lattice

$$
\pi'_R=\operatorname{Ind}_{J'}^{G'}\Lambda'_R
$$

is finite free because $J'\backslash G'$ is finite modulo the common central action. On the split side, the full compact induction is not finite as an $R$-module, but every compact-open fixed module relevant to the newvector construction is finite free. In particular, the newvector line is a rank-one lattice.

The finite Fourier operators in Chapter 7 are defined over the common cyclotomic coefficient field. Their trace comparison canonically identifies the labels of the two type occurrences, but it does not manufacture an isomorphism between representations of different groups. The relevant Hom spaces are both one dimensional. Intersect each with its integral fixed module and saturate. Choosing an $L$-linear identification that carries one saturated rank-one lattice onto the other gives the integral comparison; it is unique up to $R^\times$ and remains compatible with finite extension of $R$.

The saturated intersection is a rank-one direct summand because its quotient is torsion free over a DVR. Multiplying any nonzero $L$-linear identification by one element of $L^\times$ makes the image primitive. Any two primitive normalizations differ by $R^\times$, exactly the unavoidable ambiguity in choosing generators of the two lines.

The character identity itself is integral on type-regular elements: both sides are traces of finite free operators and Lemma 7.1 is an equality in the cyclotomic coefficient ring. Near the center, every shell sum is again finite over $R$. Thus no analytic limiting process introduces denominators into the lattice comparison.

### 11.4 Perfect pairings and reduction

Dual type lattices use

$$
\Lambda_R^\#=\operatorname{Hom}_R(\Lambda_R,R).
$$

On the division side the coset-sum formula

$$
\langle f,f^\#\rangle
=\sum_{x\in J'\backslash G'}
\langle f(x),f^\#(x)\rangle
\tag{11.1}
$$

is perfect and invariant. No division by the coset number occurs. The split newvector lattice pairs perfectly with the contragredient newvector lattice after primitive normalization. Under transfer, inversion of the admissible pair identifies these dual lines.

Reduction modulo the maximal ideal always produces stable objects and reductions of the chosen primitive lines. Their intrinsic characterization as unique type lines, and preservation of irreducibility, require more.

### 11.5 The nonbanal boundary

Assume $\ell$ does not divide the orders of the finite quotients controlling the types, their stabilizers, and the relevant coset permutations. Then averaging idempotents remain defined after reduction, the two type multiplicities remain one, the perfect pairing remains nondegenerate, and the integral comparison descends.

If, for example, $\ell$ divides $q+1$, two distinct regular characters of $k_2^\times$ may become congruent to their Frobenius conjugates. The reduced index-two induction can split or acquire additional endomorphisms. This does not contradict characteristic-zero transfer; it shows that irreducible reduction is stronger than existence of stable lattices.

There is a second source of nonbanality. At positive depth the Heisenberg quotient is a $p$-group, so its order is automatically an $R$-unit when $\ell\ne p$. But the tame extension from the Heisenberg subgroup to its normalizer can involve factors dividing $q-1$ or $q+1$. If $\ell$ divides those factors, the stable lattice still exists while the projector onto a prescribed tame eigenspace may cease to be exact. Separating the $p$-primary construction from the tame normalizer is therefore necessary even when all character values are units.

Accordingly, integral compatibility has two layers. Stable lattices, contragredient pairings, and primitive selected lines hold for unit-valued data with $\ell\ne p$. Irreducibility and multiplicity preservation after reduction require the stated banal hypotheses.

Precisely, the transfer-facing integral datum is

$$
(a(\pi),\mathcal L_R,\mathcal L_R^\#)
\quad\longleftrightarrow\quad
(a(\pi'),\mathcal L'_R,(\mathcal L'_R)^\#),
\tag{11.4}
$$

where the conductor exponents agree, $\mathcal L_R$ is the saturated rank-one split newvector/type line, $\mathcal L'_R$ is the saturated rank-one division type-multiplicity line, and the displayed lines pair perfectly with their contragredient lines. The comparison is unique up to $R^\times$. It does not identify the ambient representation lattices or full fixed-vector spaces. Under the banal hypotheses, the reduced lines retain multiplicity one.

## 12. Bijection and uniqueness in the selected range

### 12.1 The selected sets

Let $\mathcal D_G$ consist of isomorphism classes of

$$
\operatorname{St}\otimes(\mu\circ\det)
$$

and $\pi(E,\theta)$ for tame admissible quadratic pairs, with pair equivalence as in (5.1). Let $\mathcal D_{G'}$ consist of the norm characters $\mu\circ\operatorname{Nrd}$ and the corresponding $\pi'(E,\theta)$.

The constructions on each side already show that labels within a family are unique: special labels are recovered from the representation, and dihedral labels are recovered up to equivalence. A special object cannot be isomorphic to a dihedral object because the former is one-dimensional on $G'$ and the latter has a regular noncentral type; on $G$, the former has nonzero monodromy shape while the latter is supercuspidal.

### 12.2 Existence and injectivity

Define

$$
\operatorname{JL}_{\mathrm{sel}}(\pi_\mu)=\pi'_\mu,
\qquad
\operatorname{JL}_{\mathrm{sel}}(\pi(E,\theta))=\pi'(E,\theta).
\tag{12.1}
$$

Chapters 4, 6, and 7 prove the character identity for every object in the domain, so existence is established.

If two split objects have the same image, division-side classification recovers the same family and label. Thus the split objects are isomorphic. Conversely, every object in $\mathcal D_{G'}$ occurs on the right side of (12.1). Hence (12.1) is a bijection.

### 12.3 Character-theoretic uniqueness

Suppose $\rho'\in\mathcal D_{G'}$ satisfies

$$
\Theta_\pi(g)=-\Theta_{\rho'}(d)
$$

on every matching regular pair. The already constructed companion $\pi'$ satisfies the same identity, so

$$
\Theta_{\rho'}(d)=\Theta_{\pi'}(d)
$$

for every regular $d\in D^\times$. Because $F$ has characteristic zero, every noncentral element of $D$ generates a separable quadratic field and is regular. The regular set is therefore $D^\times\setminus F^\times$, which is dense: the one-dimensional center has empty interior in the four-dimensional $F$-space $D$.

Both representations are finite dimensional and smooth, so their ordinary trace functions are locally constant on all of $D^\times$. Equality on the dense regular set consequently extends to the center, including the identity. The two representations now have equal dimensions and equal central characters. Divide out that common scalar central action. Each representation factors through a common finite central extension of a finite quotient of the compact group $D^\times/F^\times$. Its characteristic-zero twisted group algebra is semisimple, and irreducible characters in a semisimple finite-dimensional algebra are linearly independent. Equal trace functions therefore imply

$$
\rho'\simeq\pi'.
$$

This proves uniqueness from elliptic characters alone within the selected codomain without trying to reconstruct a ramified character from a symmetric sum on a subset where its Gauss trace might vanish. It makes no assertion about whether an omitted primitive wild representation can share a few numerical invariants; the theorem's selected codomain remains essential.

### 12.4 The complete selected theorem

**Theorem 12.1 (local Jacquet--Langlands in the selected range).** There is a unique bijection

$$
\operatorname{JL}_{\mathrm{sel}}:\mathcal D_G\xrightarrow{\sim}\mathcal D_{G'}
$$

characterized by

$$
\Theta_\pi(g)=-\Theta_{\operatorname{JL}_{\mathrm{sel}}(\pi)}(d)
$$

for matching regular elliptic elements. It is given by (12.1), commutes with twists and contragredients, and preserves central characters, conductor exponents, common local parameters, and local $L$-, epsilon, and gamma factors. For unit-valued data over $R$ with $\ell\ne p$, it preserves the precise integral package (11.4): a saturated rank-one split newvector/type line, a saturated rank-one division type-multiplicity line, and their perfect contragredient pairings, with comparison unique up to $R^\times$. Under the banal finite-quotient hypotheses, these multiplicity statements survive reduction.

**Proof.** Character matching is (4.4), (6.4), and (7.7). The label classifications prove bijectivity, while Section 12.3 proves character-theoretic uniqueness. Chapters 8 and 9 establish the invariant compatibilities. Chapters 10 and 11 establish type-line and lattice compatibility. $\square$

## 13. Worked packets and diagnostic failures

### 13.1 An unramified special twist

Let $\mu$ be unramified and write $A=\mu(\varpi)$. The split packet is $\operatorname{St}\otimes\mu$ and the division packet is $\mu\circ\operatorname{Nrd}$. Both have central character $\mu^2$ and conductor one. For $g\leftrightarrow d$,

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\mu(\det g)
=-\mu(\operatorname{Nrd}d).
$$

With conductor-zero $\psi$,

$$
L(s)=\frac1{1-Aq^{-s-1/2}},
\qquad
\epsilon(s)=-Aq^{-(s-1/2)}.
$$

The conductor is not $2a(\mu)=0$; monodromy supplies the missing one.

### 13.2 A ramified special twist

Suppose $a_F(\mu)=m>0$. Both conductors are $2m$, and both Euler factors are one. The epsilon factor is computed from $\operatorname{Sp}_2(\mu)$, including the rank-one Gauss sum of $\mu$ and the monodromy correction. Two characters of conductor $m$ can have different epsilon phases, so equality of conductors does not make their packets indistinguishable.

### 13.3 An unramified depth-zero pair

Let $E/F$ be unramified quadratic and choose a residue character $\bar\theta$ with $\bar\theta^q\ne\bar\theta$. Inflate it to a character of $E^\times$ of conductor one and choose its value on a uniformizer. Then both packet members have conductor two and central character $\theta|_{F^\times}\omega_{E/F}$. At a matching elliptic unit with residue $x\in k_2^\times\setminus k^\times$,

$$
\Theta_G=-\bar\theta(x)-\bar\theta(x^q),
\qquad
\Theta_{G'}=\bar\theta(x)+\bar\theta(x^q).
$$

The Euler factor is one, while

$$
\epsilon_F(s)=\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E).
$$

Changing the value of $\theta$ on a uniformizer can change this epsilon factor without changing the residue character formula on units.

### 13.4 A tame ramified pair

Assume $p\ne2$, let $E/F$ be ramified quadratic, and choose an admissible $\theta$ with $a_E(\theta)=r\ge2$. Then

$$
a(\pi)=a(\pi')=r+1.
$$

On the last unit layer, choose $\beta$ as in (7.1). The split and division characters on the type-regular torus are sums of two finite Gauss traces, and corresponding traces differ by $-1$. Near the center extra embedding cosets occur, but filtering those cosets by congruence depth pairs their Fourier sums with the same sign. This example is precisely where the two-term formula alone is inadequate.

### 13.5 Five false shortcuts

First, matching only trace and forgetting determinant is insufficient: many nonconjugate regular elements share a trace, and twists would no longer take equal values.

Second, declaring $\operatorname{vol}(E^\times\backslash G)=\operatorname{vol}(E^\times\backslash G')=1$ independently can conflict with the fixed group and torus measures. Pointwise characters survive this mistake, but orbital transfer does not.

Third, defining a dihedral packet solely by central character and conductor identifies many inequivalent regular characters. The elliptic character values, or equivalently the full admissible orbit, are indispensable.

A fourth shortcut is to infer integral compatibility from equality of complex characters. Equality of traces says nothing by itself about which stable lattices are saturated or whether reduction preserves an eigenspace. The primitive line construction of Chapter 11 and the banal hypotheses supply precisely that missing information.

A fifth is to use the type-regular two-term formula arbitrarily close to the center. At positive depth, extra embedding cosets enter the exact induced trace. The shell calculation of Section 7.4 is not a technical embellishment: without it one obtains a class function that fails local constancy on the final regular annuli.

## 14. The transfer package

### 14.1 A normalization audit

The comparison rests on the following linked choices:

$$
\begin{array}{c|c}
\text{datum}&\text{normalization}\\ \hline
\text{absolute value}&|\varpi|=q^{-1}\\
\text{Frobenius}&\text{geometric}\\
\text{reciprocity}&\operatorname{rec}_F(\varpi)=\Phi\\
\text{special block}&\text{centered }\operatorname{Sp}_2\\
\text{quadratic label}&\theta^\natural=\theta\Delta_{E/F,\theta}\\
\text{additive conductor}&n(\psi)=0\text{ when }\mathcal O\text{ is the largest trivial fractional ideal}\\
\text{epsilon measure}&\text{self-dual for }\psi\\
\text{centralizer measure}&\operatorname{vol}(\mathcal O_E^\times)=1\\
\text{geometric orbital transfer}&O_g(f)=O_d(f')\\
\text{pointwise sign}&\Theta_G=-\Theta_{G'}
\end{array}
$$

Changing one row is allowed only if every dependent formula changes with it. Arithmetic Frobenius reciprocates unramified eigenvalues. An uncentered special block shifts Euler factors. Direct quadratic normalization removes the rectifier from the label but forces its contribution to reappear in central characters and Gauss sums. Signed test-function transfer moves, but does not erase, the final minus sign.

### 14.2 A reusable comparison table

| invariant          | special label $\mu$                                 | dihedral label $(E,\theta)$                                       |
| ------------------ | --------------------------------------------------- | ----------------------------------------------------------------- |
| split member       | $\operatorname{St}\otimes(\mu\circ\det)$            | $\pi(E,\theta)$                                                   |
| division member    | $\mu\circ\operatorname{Nrd}$                        | $\pi'(E,\theta)$                                                  |
| central character  | $\mu^2$                                             | $\theta                                                           |
| parameter          | $\operatorname{Sp}_2(\mu)$                          | $\operatorname{Ind}_{W_E}^{W_F}\theta$                            |
| conductor          | $1$ if $a(\mu)=0$, else $2a(\mu)$                   | $v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta)$                        |
| Euler factor       | $L(s+1/2,\mu)$                                      | $1$                                                               |
| epsilon factor     | that of $\operatorname{Sp}_2(\mu)$                  | $\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E)$                    |
| gamma factor       | derived from the displayed $L$- and epsilon factors | derived from the displayed $L$- and epsilon factors               |
| elliptic character | negative of division value                          | negative of division value                                        |
| integral object    | saturated split new/type and division special lines | saturated split new/type line and division type-multiplicity line |

Every row is compatible with twisting. In the dihedral column, replace $\theta$ by $\theta(\chi\circ N_{E/F})$; in the special column, replace $\mu$ by $\mu\chi$.

### 14.3 Boundary of the theorem

The theorem includes special twists with arbitrary smooth $\mu$, unramified quadratic depth-zero and tame positive-depth pairs, and ramified tame quadratic pairs. It includes nonminimal pairs through exact norm twisting. It includes residue characteristic two only where the quadratic construction remains tame, in particular for the unramified quadratic extension.

It does not include ramified dyadic positive-depth pairs or primitive wild packets. It does not claim a correspondence for principal series, because those are not discrete series and have no irreducible companion on the quaternion division group. It does not identify full representation lattices across groups of different geometry, and it does not claim irreducibility after reduction outside the banal range.

These limits protect the theorem's uniqueness. Within the selected sets, every object is constructed, every regular elliptic character contribution is compared, and every label is recoverable. Beyond them, additional wild strata and extension data require a different analysis.

### 14.4 Conclusion

The local correspondence in degree two is governed by a simple geometric fact and a delicate arithmetic calculation. The simple fact is that an irreducible quadratic polynomial describes one regular elliptic class in each inner form. The delicate calculation is that the finite Fourier models transverse to their common quadratic torus have opposite orientation. That opposition produces the single transfer sign.

For Steinberg twists, the sign is already visible in the projective-line model: an elliptic element has no fixed line, so removing constants leaves trace $-1$. For tame dihedral packets, the same sign passes through residue-field cuspidal characters, positive-depth Heisenberg traces, and the extra congruence embeddings near the center. The rectifier makes the remaining torus phases agree.

The result is a genuine bijection, not merely a matching of a few invariants. The character calculation determines the companion, while separate type, conductor, parameter, coefficient-integral, and lattice calculations prove compatibility of centers, twists, conductors, local parameters, Euler and epsilon factors, type lines, newvectors, and integral pairings. Compatible Haar measures turn the pointwise theorem into the exact orbital statement needed for trace comparison, while the explicit boundary prevents tame arguments from making claims about primitive wild packets. Special and selected dihedral discrete series now have their unique quaternionic companions with all normalizations visible and mutually checked.
