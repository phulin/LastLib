# Global Jacquet--Langlands

## Contents

1. [The global comparison problem](#1-the-global-comparison-problem)
   - [One representation seen through two inner forms](#11-one-representation-seen-through-two-inner-forms)
   - [Standing notation and the scope of the theorem](#12-standing-notation-and-the-scope-of-the-theorem)
   - [A normalization ledger](#13-a-normalization-ledger)
   - [Why a place-by-place recipe is not yet a theorem](#14-why-a-place-by-place-recipe-is-not-yet-a-theorem)
2. [Global matching data](#2-global-matching-data)
   - [Split and ramified places](#21-split-and-ramified-places)
   - [Semisimple classes and characteristic polynomials](#22-semisimple-classes-and-characteristic-polynomials)
   - [The embedding criterion behind global matching](#23-the-embedding-criterion-behind-global-matching)
   - [Products of local matching functions](#24-products-of-local-matching-functions)
3. [Measures, centers, and central characters](#3-measures-centers-and-central-characters)
   - [Why measures are part of transfer](#31-why-measures-are-part-of-transfer)
   - [Tamagawa and Hecke normalizations](#32-tamagawa-and-hecke-normalizations)
   - [Fixed central character quotients](#33-fixed-central-character-quotients)
   - [The global sign](#34-the-global-sign)
4. [The compact quaternionic trace formula](#4-the-compact-quaternionic-trace-formula)
   - [The kernel](#41-the-kernel)
   - [The spectral expansion](#42-the-spectral-expansion)
   - [The geometric expansion](#43-the-geometric-expansion)
   - [Central and regular terms](#44-central-and-regular-terms)
5. [The simple trace formula on the split group](#5-the-simple-trace-formula-on-the-split-group)
   - [What noncompactness adds](#51-what-noncompactness-adds)
   - [Cuspidal local test functions](#52-cuspidal-local-test-functions)
   - [The simple trace identity](#53-the-simple-trace-identity)
   - [Why unwanted terms vanish](#54-why-unwanted-terms-vanish)
6. [Local transfer and the fundamental matching principle](#6-local-transfer-and-the-fundamental-matching-principle)
   - [Orbital integrals at ramified places](#61-orbital-integrals-at-ramified-places)
   - [Split places and spherical units](#62-split-places-and-spherical-units)
   - [The rank-one fundamental function](#63-the-rank-one-fundamental-function)
   - [Product compatibility](#64-product-compatibility)
7. [Comparison of geometric expansions](#7-comparison-of-geometric-expansions)
   - [Matching rational elliptic classes](#71-matching-rational-elliptic-classes)
   - [Classes that do not come from the quaternion algebra](#72-classes-that-do-not-come-from-the-quaternion-algebra)
   - [Equality term by term](#73-equality-term-by-term)
   - [The global trace identity](#74-the-global-trace-identity)
8. [Spectral comparison and extraction](#8-spectral-comparison-and-extraction)
   - [Factorized spectral traces](#81-factorized-spectral-traces)
   - [Isolating one quaternionic constituent](#82-isolating-one-quaternionic-constituent)
   - [Recovering every local component](#83-recovering-every-local-component)
   - [Strong multiplicity one and uniqueness](#84-strong-multiplicity-one-and-uniqueness)
9. [The global correspondence](#9-the-global-correspondence)
   - [Precise statement](#91-precise-statement)
   - [Existence and injectivity](#92-existence-and-injectivity)
   - [Surjectivity onto the stated image](#93-surjectivity-onto-the-stated-image)
   - [Multiplicity preservation](#94-multiplicity-preservation)
10. [Norm characters and the exceptional spectrum](#10-norm-characters-and-the-exceptional-spectrum)
    - [Why global characters must be separated](#101-why-global-characters-must-be-separated)
    - [Their local Steinberg transfers](#102-their-local-steinberg-transfers)
    - [How the trace comparison accounts for them](#103-how-the-trace-comparison-accounts-for-them)
    - [A counterexample to naive globalization](#104-a-counterexample-to-naive-globalization)
11. [Structural compatibilities](#11-structural-compatibilities)
    - [Central characters, twists, and contragredients](#111-central-characters-twists-and-contragredients)
    - [Conductors and exact local shifts](#112-conductors-and-exact-local-shifts)
    - [Local and global factors and formal degrees](#113-local-and-global-factors-and-formal-degrees)
    - [Root numbers and additive characters](#114-root-numbers-and-additive-characters)
12. [Unramified Hecke data](#12-unramified-hecke-data)
    - [Spherical operators and Satake parameters](#121-spherical-operators-and-satake-parameters)
    - [Equality of Hecke polynomials](#122-equality-of-hecke-polynomials)
    - [Good-place eigensystems determine the transfer](#123-good-place-eigensystems-determine-the-transfer)
    - [What good-place data do not determine](#124-what-good-place-data-do-not-determine)
13. [Archimedean weights and algebraic structures](#13-archimedean-weights-and-algebraic-structures)
    - [Real ramification turns weight into discrete series](#131-real-ramification-turns-weight-into-discrete-series)
    - [Highest weights and lowest weights](#132-highest-weights-and-lowest-weights)
    - [Cohomological transfer](#133-cohomological-transfer)
    - [Parity and the global center](#134-parity-and-the-global-center)
14. [Finite level, newforms, and exact level change](#14-finite-level-newforms-and-exact-level-change)
    - [From quaternionic fixed vectors to split newvectors](#141-from-quaternionic-fixed-vectors-to-split-newvectors)
    - [Maximal level and the discriminant factor](#142-maximal-level-and-the-discriminant-factor)
    - [Deeper division levels](#143-deeper-division-levels)
    - [Hecke modules and eigensystems](#144-hecke-modules-and-eigensystems)
15. [Rationality and conjugation](#15-rationality-and-conjugation)
    - [What character identities prove](#151-what-character-identities-prove)
    - [Fields of coefficients](#152-fields-of-coefficients)
    - [Galois conjugation](#153-galois-conjugation)
    - [Limits of the rationality statement](#154-limits-of-the-rationality-statement)
16. [Examples over the rationals](#16-examples-over-the-rationals)
    - [Definite discriminant eleven and weight two](#161-definite-discriminant-eleven-and-weight-two)
    - [The Hurwitz algebra and an empty cuspidal image](#162-the-hurwitz-algebra-and-an-empty-cuspidal-image)
    - [The image condition is real](#163-the-image-condition-is-real)
    - [A local level calculation](#164-a-local-level-calculation)
17. [Trace formulas and Brandt matrices](#17-trace-formulas-and-brandt-matrices)
    - [The finite geometric shadow](#171-the-finite-geometric-shadow)
    - [A worked spectral reading of a Brandt operator](#172-a-worked-spectral-reading-of-a-brandt-operator)
    - [What the finite picture proves and what it does not](#173-what-the-finite-picture-proves-and-what-it-does-not)
18. [The transfer dictionary](#18-the-transfer-dictionary)
    - [The place-by-place table](#181-the-place-by-place-table)
    - [A reusable global theorem](#182-a-reusable-global-theorem)
    - [Inputs for later applications](#183-inputs-for-later-applications)
    - [Conclusion](#184-conclusion)

## 1. The global comparison problem

### 1.1 One representation seen through two inner forms

Let $F$ be a number field and let $D$ be a quaternion algebra over $F$. At every place $v$, the algebra $D_v=D\otimes_FF_v$ is either $M_2(F_v)$ or a quaternion division algebra. Thus the adelic group $D^\times(\mathbf A_F)$ agrees locally with $\mathrm{GL}_2(F_v)$ at almost every place, but it may differ at a prescribed finite set. Global Jacquet--Langlands answers the natural question: when can an automorphic representation on the quaternionic group be transported to the matrix group without losing its local identity?

The answer is subtler than replacing each local factor independently. At a ramified place, Book 41 gives a bijection from irreducible representations of $D_v^\times$ to the discrete series of $\mathrm{GL}_2(F_v)$. At a split place there is nothing to transfer. One can therefore write down a formal tensor

$$
\bigotimes_v'\operatorname{JL}_v(\Pi_v).
$$

But a restricted tensor of admissible local representations need not occur automorphically. Automorphy is a global condition, and cuspidality is even more global: it is expressed by an integral over $F\backslash\mathbf A_F$, not by a condition on each component. The main work of this book is to prove that the formal tensor is indeed a cuspidal automorphic representation in exactly the noncharacter cases, and that every cusp form with the required discrete local behavior arises this way.

The proof compares two trace formulas. On $D^\times$, compactness modulo the center makes the kernel and its trace completely discrete. On $\mathrm{GL}_2$, the quotient has cusps, so continuous and parabolic terms ordinarily appear. A local test function supported in the elliptic theory kills the continuous terms, leaving cuspidal representations together with the one-dimensional residual boundary. Matching orbital integrals makes the two geometric expansions identical. After the character terms are identified and subtracted, equality of spectral traces forces the desired cuspidal representation to exist.

This route explains more than existence. It shows why the image condition is discrete series at every ramified place, why the local minus signs disappear globally, why Hecke eigenvalues are unchanged at good places, and why the quaternionic character subspace must be removed before claiming a cuspidal bijection.

### 1.2 Standing notation and the scope of the theorem

Write

$$
G=D^\times,\qquad G^*=\mathrm{GL}_{2/F},\qquad Z=\mathbf G_m,
$$

and abbreviate $\mathbf A_F$ to $\mathbf A$. Let

$$
R=\operatorname{Ram}(D),\qquad R_f=\{v<\infty:v\in R\},
$$

so $R$ contains finite and real places and no complex places. At $v\notin R$, fix an $F_v$-algebra isomorphism

$$
\iota_v:D_v\xrightarrow{\sim}M_2(F_v).
$$

Changing $\iota_v$ conjugates it and hence changes neither local representation classes nor orbital integrals. At $v\in R$, write $\operatorname{JL}_v$ for the local correspondence of Book 41, with the analogous archimedean correspondence at a ramified real place.

We assume first that $D$ is a division algebra over $F$, equivalently $R\ne\varnothing$. Then

$$
[G]=Z(\mathbf A)G(F)\backslash G(\mathbf A)
$$

is compact. The split case $D=M_2(F)$ has $R=\varnothing$ and the correspondence is the identity; it contains no trace-formula comparison and will be understood as the degenerate boundary case.

An automorphic representation of $G(\mathbf A)$ factors as $\Pi=\bigotimes_v'\Pi_v$. We call it a **norm character** if it is one dimensional. To state this spectrum without hiding a sign condition, put

$$
\mathbf A_D^\times=\operatorname{Nrd}(D^\times(\mathbf A)),
\qquad
F_D^\times=\operatorname{Nrd}(D^\times(F)).
$$

The local reduced norm is onto at every finite or split archimedean place and has image $\mathbf R_{>0}$ at a ramified real place. The global norm theorem gives

$$
F_D^\times=F^\times\cap\mathbf A_D^\times.
$$

Weak approximation realizes every required pattern of real signs, so

$$
F_D^\times\backslash\mathbf A_D^\times
\xrightarrow{\sim}
F^\times\backslash\mathbf A^\times.
$$

Consequently every character of the intrinsic norm quotient extends uniquely to a Hecke character $\chi$, and every norm character has the familiar form

$$
\Pi=\chi\circ\operatorname{Nrd}.
$$

All other irreducible automorphic representations will be called **noncharacters**. The theorem will give a bijection between noncharacters on $G$ and cuspidal representations on $G^*$ satisfying the discrete-series condition at every $v\in R$. Norm characters are genuinely exceptional and will be treated in Chapter 10.

We use $\Pi$ for a quaternionic representation and $\pi$ for a representation of $G^*(\mathbf A)$. Their local components are $\Pi_v$ and $\pi_v$. At a split place, the assertion $\pi_v\cong\Pi_v$ always means that $\Pi_v$ has been transported through $\iota_v$.

### 1.3 A normalization ledger

Transfer is unusually sensitive to conventions because three unrelated normalizations coexist.

First, matching conjugacy classes is oriented by equality of reduced characteristic polynomials:

$$
X^2-\operatorname{Trd}(d)X+\operatorname{Nrd}(d)
=X^2-\operatorname{tr}(g)X+\det(g).
$$

There is no inversion or negation in this rule.

Second, local matching functions have equal orbital integrals. The geometric transfer factor is $+1$. At a ramified place the spectral character identity is instead

$$
\Theta_{\operatorname{JL}_v(\rho)}(g)=-\Theta_\rho(d).
$$

The minus sign is spectral, not geometric.

Third, Hecke operators will normally be unnormalized characteristic-double-coset operators with hyperspecial volume one. At an unramified split place their polynomial is

$$
P_v(X)=1-T_vX+q_vS_vX^2.
$$

Normalized Satake parameters differ by $q_v^{1/2}$ from the raw roots used in this polynomial. We never move between these normalizations silently.

Hilbert-space arguments use unitary central characters. Algebraic representations are reduced to that case by a common real norm twist and restored afterward. Contragredients are algebraic smooth duals; complex conjugation enters only after choosing a unitary realization.

### 1.4 Why a place-by-place recipe is not yet a theorem

Suppose one defines candidate local factors by

$$
\pi_v^{\mathrm{cand}}=
\begin{cases}
\Pi_v,&v\notin R,\\
\operatorname{JL}_v(\Pi_v),&v\in R.
\end{cases}
$$

At almost every place this factor is spherical, so the restricted tensor product exists as an abstract representation. Four questions remain.

1. Does it occur in the automorphic spectrum of $G^*$?
2. Is it cuspidal?
3. Could a second automorphic representation have the same prescribed factors?
4. Does every cuspidal representation with discrete factors on $R$ arise this way?

Strong multiplicity one answers the third question only after existence and cuspidality are known. It cannot create an automorphic representation from a tensor product. Local Jacquet--Langlands answers none of the global questions. The trace formula supplies existence and surjectivity; local character independence recovers the ramified components; strong multiplicity one then makes the result canonical.

A useful counterexample is the formal tensor obtained from a global norm character. At almost every split place it is the one-dimensional representation $\chi_v\circ\det$, while at a finite ramified place local transfer asks for $\operatorname{St}_v\otimes\chi_v$ and at a ramified real place it asks for the corresponding lowest discrete-series representation. There is no cuspidal global representation with those almost-everywhere one-dimensional components. Thus even perfect local compatibility does not guarantee globalization without a global spectral argument.

## 2. Global matching data

### 2.1 Split and ramified places

The ramification set $R$ is finite and has even cardinality. This parity counts real places together with finite places. It is the global reciprocity constraint on quaternion algebras and will later cancel the product of local spectral signs.

At $v\notin R$, both groups are $\mathrm{GL}_2(F_v)$ after $\iota_v$. We match elements, functions, and representations identically. At $v\in R$, regular semisimple elements of $D_v^\times$ correspond exactly to elliptic regular elements of $\mathrm{GL}_2(F_v)$ by characteristic polynomial. A split regular matrix has no division-side partner.

The distinction between global and local ellipticity matters. If $E/F$ is a quadratic field, an element generating $E$ gives a regular elliptic matrix over $F$, but at a place where $E$ splits its local image is split regular. To come from $D^\times(F)$, the field $E$ must remain a field at every ramified place of $D$.

### 2.2 Semisimple classes and characteristic polynomials

For $\gamma\in G(F)$ put

$$
P_\gamma(X)=X^2-\operatorname{Trd}(\gamma)X+\operatorname{Nrd}(\gamma).
$$

For $\gamma^*\in G^*(F)$ put

$$
P_{\gamma^*}(X)=X^2-\operatorname{tr}(\gamma^*)X+\det(\gamma^*).
$$

Noncentral regular semisimple classes on either side are determined by this polynomial. We say that $\gamma$ and $\gamma^*$ match if $P_\gamma=P_{\gamma^*}$. The common algebra

$$
E=F[X]/(P_\gamma)
$$

is then a quadratic field whenever $\gamma$ lies in a division quaternion algebra. Their centralizers are the same torus:

$$
G_\gamma\cong\operatorname{Res}_{E/F}\mathbf G_m
\cong G^*_{\gamma^*}.
$$

The equality of centralizers is the reason the global volume coefficient can match. Equality merely of traces and norms without compatible torus measures would not suffice.

Scalar classes require separate language. After quotienting by the full adelic center, all rational scalar elements represent the identity class. Their contribution is the volume of the projective automorphic quotient times the test function's central germ. Regular orbital integrals do not determine the value of a function at a scalar, so the singular part of local transfer must also be normalized. The rank-one transfer of Book 41 includes exactly this central germ.

### 2.3 The embedding criterion behind global matching

The following elementary proposition organizes the geometric comparison.

**Proposition 2.1.** Let $P\in F[X]$ be separable irreducible quadratic and let $E=F[X]/(P)$. The following are equivalent:

1. $P$ is the reduced characteristic polynomial of an element of $D^\times(F)$;
2. $E$ embeds in $D$;
3. no place in $R$ splits in $E$;
4. at every $v\in R$, a matrix with polynomial $P$ is elliptic regular in $\mathrm{GL}_2(F_v)$.

**Proof strategy.** An element with polynomial $P$ generates $E$. A quadratic field embeds in a degree-two central simple algebra precisely when it splits that algebra. Local invariants translate splitting of $D$ by $E$ into the condition that $E_v$ have degree two at every ramified place.

**Proof.** The equivalence of (1) and (2) follows by sending the residue class of $X$ to the element. If $E$ embeds, it is a maximal subfield and splits $D$ after scalar extension. At $v\in R$, the invariant $1/2$ is killed precisely when every factor of $E\otimes_FF_v$ has even local degree. Since $E/F$ is quadratic, this means that $E_v$ is a field, not $F_v\times F_v$. This proves (2)$\Leftrightarrow$(3). A matrix with irreducible quadratic polynomial over $F_v$ is elliptic, proving (3)$\Leftrightarrow$(4). $\square$

Consequently the quaternionic rational regular classes are exactly the split-group rational elliptic classes that remain locally elliptic at all ramified places. This is the global selection rule the test functions will enforce.

**Worked example.** Let $F=\mathbf Q$ and let $D$ ramify at $p$ and $\infty$. An imaginary quadratic field $E$ embeds in $D$ exactly when $p$ is inert or ramified in $E$. A polynomial defining an imaginary quadratic field in which $p$ splits gives an elliptic real matrix, but its $p$-adic matrix is split regular. It therefore contributes to an unrestricted elliptic trace formula on $\mathrm{GL}_2$ but not to the quaternionic trace formula.

### 2.4 Products of local matching functions

Fix a unitary Hecke character $\omega$ that will be the common central character. A global test function on either group is a finite linear combination of restricted pure tensors

$$
f=\bigotimes_v f_v,\qquad f'=\bigotimes_v f'_v,
$$

with inverse central covariance $\omega_v^{-1}$. We place primes on quaternionic functions and leave split-group functions unprimed.

The pair $(f,f')$ is **globally matching** when:

- at $v\notin R$, transport through $\iota_v$ identifies $f_v$ with $f'_v$;
- at $v\in R$, the functions match in the local sense: elliptic orbital integrals agree, split regular orbital integrals of $f_v$ vanish, and central germs use the fixed singular normalization;
- almost everywhere both are the unit of the same hyperspecial Hecke algebra.

For matching rational regular elements, product measures give

$$
O_{\gamma^*}(f)=\prod_vO_{\gamma_v^*}(f_v)
=\prod_vO_{\gamma_v}(f_v')=O_\gamma(f').
$$

This factorization is valid because the centralizer is the same global torus and almost every local orbital integral of the unit function equals one in the unramified integral model. If local quotient measures were chosen independently, an uncontrolled product of constants would appear.

## 3. Measures, centers, and central characters

### 3.1 Why measures are part of transfer

An orbital integral is an integral over $T(F_v)\backslash G(F_v)$, so it depends on measures on both $T(F_v)$ and $G(F_v)$. A geometric coefficient in the global trace formula is a volume of

$$
Z(\mathbf A)T(F)\backslash T(\mathbf A),
$$

and depends on the quotient convention. Rescaling a local group measure without changing the torus measure rescales the orbital integral; rescaling both sides inconsistently destroys comparison.

The clean solution begins globally. Choose invariant differential forms over $F$ on the two inner forms and on every torus centralizer. Their adelic absolute values define product measures. Quotient measures are always obtained from Weil's formula. Because matching centralizers are the same $F$-torus, their measures agree automatically. Local transfer is then stated with respect to the induced local quotient measures.

At finitely many places one may rescale the group measures for convenient Hecke normalization. The matching function at that place must be rescaled inversely so that its orbital integrals remain unchanged. This bookkeeping is harmless when explicit and dangerous when hidden.

### 3.2 Tamagawa and Hecke normalizations

On the projective groups

$$
PG=G/Z,\qquad PG^*=G^*/Z,
$$

the compatible Tamagawa measures satisfy

$$
\operatorname{vol}\bigl(PG(F)\backslash PG(\mathbf A)\bigr)=2
$$

for the anisotropic inner form, and the corresponding finite-volume statement on $PG^*$. Equality of these Tamagawa numbers is the central-term normalization in the comparison. One could divide both global measures by two; every term on both sides would change together.

For finite-level calculations we instead require

$$
\operatorname{vol}(K_v)=1
$$

at almost every split finite place and, when used, $\operatorname{vol}(\mathcal O_{D_v}^\times)=1$ at a division place. These local choices determine the coefficients in characteristic-double-coset operators. A finite product of conversion factors relates them to Tamagawa measure. The trace formula remains unchanged only when the kernel, orbital integrals, and spectral convolution all use the same converted measure.

This distinction explains why a Brandt matrix has integral entries while a Tamagawa orbital coefficient may be rational. The matrix uses counting with compact-open volume one; the global trace formula packages the stabilizer denominators into quotient volumes.

### 3.3 Fixed central character quotients

Let

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times
$$

be unitary. On either group consider functions satisfying

$$
\phi(zg)=\omega(z)\phi(g).
$$

A convolution kernel must transform oppositely:

$$
f(zg)=\omega(z)^{-1}f(g).
$$

Then convolution is taken over $Z(\mathbf A)\backslash G(\mathbf A)$ and is independent of representatives. The same is true on $G^*$.

For a local compactly supported function $h_v$ without central covariance, one may form its central average

$$
h_v^\omega(g)=\int_{F_v^\times}h_v(zg)\omega_v(z)\,dz.
$$

Provided the support is compact modulo the center, this creates the required transformation law. At a finite level it recovers the ordinary double-coset action on the $\omega$-isotypic space. Thus fixing a central character is not a cosmetic restriction; it is what makes the center quotient and trace kernel well defined.

The central characters of matching local representations agree. Hence a global transfer, if it exists, must satisfy

$$
\omega_\pi=\omega_\Pi.
$$

This equality includes archimedean signs and norm powers, not merely the finite nebentype.

### 3.4 The global sign

At every $v\in R$, local character transfer contributes one minus sign:

$$
\operatorname{tr}\operatorname{JL}_v(\Pi_v)(f_v)
=-\operatorname{tr}\Pi_v(f'_v).
$$

At split places there is no sign. Therefore a factorized spectral trace acquires

$$
(-1)^{|R|}.
$$

Hilbert reciprocity says $|R|$ is even. Consequently

$$
\boxed{(-1)^{|R|}=+1.}
$$

This elementary parity is essential. Counting only finite ramified places can give the wrong sign. For a definite quaternion algebra over $\mathbf Q$ ramified at $p$ and $\infty$, there are two local minus signs, not one. The finite sign $-1$ and the archimedean sign $-1$ multiply to $+1$.

Geometric orbital transfer has sign $+1$ at every place, so its global product is already $+1$. The parity theorem is exactly what makes the spectral product agree with the geometric product.

## 4. The compact quaternionic trace formula

### 4.1 The kernel

Assume $D$ is division. For a smooth test function $f'$ on $G(\mathbf A)$, compactly supported modulo $Z(\mathbf A)$ and transforming by $\omega^{-1}$, define

$$
K_{f'}(x,y)=
\sum_{\gamma\in Z(F)\backslash G(F)}
f'(x^{-1}\gamma y).
$$

The sum is locally finite because $G(F)$ is discrete and $f'$ has compact support modulo the center. It descends in both variables to $[G]$. Right convolution is

$$
(R(f')\phi)(x)=
\int_{Z(\mathbf A)\backslash G(\mathbf A)}
f'(g)\phi(xg)\,dg,
$$

and the kernel identity gives

$$
(R(f')\phi)(x)=\int_{[G]}K_{f'}(x,y)\phi(y)\,dy.
$$

Compactness of $[G]$ makes $R(f')$ trace class. There is no truncation and no convergence correction. This is the analytic advantage of the inner form.

### 4.2 The spectral expansion

The right regular spectrum is discrete:

$$
L^2(G,\omega)=\widehat\bigoplus_\Pi m_D(\Pi)\Pi.
$$

Consequently

$$
I_D(f'):=\operatorname{tr}R(f')
=\sum_\Pi m_D(\Pi)\operatorname{tr}\Pi(f').
$$

At any fixed finite level and archimedean type only finitely many summands contribute. Book 43 proves $m_D(\Pi)=1$, but it is useful to retain the multiplicity symbol during comparison: doing so shows exactly where multiplicity preservation enters.

If $f'=\bigotimes_vf'_v$ and $\Pi=\bigotimes_v'\Pi_v$, then

$$
\operatorname{tr}\Pi(f')=\prod_v\operatorname{tr}\Pi_v(f'_v)
$$

whenever all but finitely many factors are normalized spherical projectors. This product is the spectral counterpart of factorized orbital integrals.

Norm characters occur in this sum. Compactness does not remove them, because the absence of rational parabolics makes the usual cuspidality condition vacuous. Their later separation is a spectral operation, not a convergence device.

### 4.3 The geometric expansion

Integrating the diagonal gives

$$
I_D(f')=
\int_{[G]}K_{f'}(x,x)\,dx.
$$

Group the rational elements by conjugacy class. One obtains

$$
I_D(f')=
\sum_{[\gamma]}
a_D(\gamma)O_\gamma(f'),
$$

where

$$
a_D(\gamma)=
\operatorname{vol}\bigl(
Z(\mathbf A)G_\gamma(F)\backslash G_\gamma(\mathbf A)
\bigr)
$$

and

$$
O_\gamma(f')=
\int_{G_\gamma(\mathbf A)\backslash G(\mathbf A)}
f'(x^{-1}\gamma x)\,dx.
$$

The same centralizer measure occurs in both expressions. For regular noncentral $\gamma$, the centralizer is $E^\times$ for the quadratic field $E=F(\gamma)$. For the central class it is all of $G$.

**Proof strategy.** Absolute convergence allows the sum and integral to be interchanged. Each orbit of $G(F)$ is unfolded against its stabilizer. Weil's quotient formula then separates the volume of the rational centralizer quotient from the adelic orbital integral.

**Proof.** Insert the kernel on the diagonal and integrate. Compact support and compactness of $[G]$ give absolute convergence. For a fixed $\gamma$, sum over $G_\gamma(F)\backslash G(F)$ and change variables. The quotient by $G_\gamma(F)$ unfolds to $G_\gamma(F)\backslash G(\mathbf A)$; applying Weil's formula along $G_\gamma(\mathbf A)$ gives the coefficient and orbital integral displayed above. Summing over conjugacy classes proves the formula. $\square$

The argument is elementary once compactness is known. Its importance lies in exposing exactly the geometric data that local transfer can compare.

### 4.4 Central and regular terms

Modulo $Z(F)$ there is one central class. With the projective Tamagawa normalization its contribution is

$$
I_{D,\mathrm{cent}}(f')=
\operatorname{vol}([G])f'(1),
$$

where $f'(1)$ means the central germ determined by the chosen covariance. Every remaining semisimple class is regular and generates a quadratic field. A division algebra has no nontrivial unipotents and no split quadratic étale subalgebra, so there are no unipotent or split regular terms.

This small geometric expansion is the model the split trace formula must be forced to imitate:

$$
\text{quaternionic geometry}
=\text{central}+\text{quadratic-field classes}.
$$

The absence of other terms is structural. It is not achieved by cancellation after summing.

## 5. The simple trace formula on the split group

### 5.1 What noncompactness adds

For $G^*=\mathrm{GL}_2$, the quotient by the center has finite volume but is not compact. The naive kernel has a cuspidal part, a continuous Eisenstein part, and residual contributions. Geometrically there are central, unipotent, split regular, and elliptic regular classes. Integrating the diagonal without modification does not justify exchanging sums and integrals near the cusp.

The full invariant trace formula controls these terms by truncation. Global Jacquet--Langlands needs a much smaller piece. If one local factor of the test function is cuspidal in the sense that all its constant terms vanish, every continuous and weighted induced **trace distribution** acquires a zero local factor. The truncated formula then collapses to a simple trace formula whose spectral side is discrete—cuspidal plus one-dimensional residual—and whose geometric side is central plus elliptic. This is a statement about the invariant trace distributions; it need not mean that the local convolution operator is zero on every induced representation.

The ramification of $D$ supplies exactly such a place. A local elliptic lift of a division-side function has zero orbital integrals on split regular elements and zero parabolic constant term. Thus the comparison itself creates the hypothesis that simplifies the split trace formula.

### 5.2 Cuspidal local test functions

For a local field $K$, let $B=TN$ be the upper Borel of $\mathrm{GL}_2(K)$ and let $h\in C_c^\infty(\mathrm{GL}_2(K))$ modulo the center. Its normalized constant term is

$$
h_B(t)=\delta_B(t)^{1/2}
\int_{N(K)}h(tn)\,dn.
$$

For the trace formula one uses the stronger conjugation-stable condition that

$$
\int_{N(K)}h(x^{-1}tnx)\,dn=0
$$

for every $x\in\mathrm{GL}_2(K)$ and $t\in T(K)$, with the evident archimedean smooth analogue. We call such an $h$ **cuspidal**. Equivalently, its trace on every normalized representation induced from $B$ is zero. The opposite-Borel condition follows by conjugating with the Weyl element. In rank one this is also reflected geometrically by vanishing split regular orbital integrals, together with the appropriate singular germ condition.

An elliptic lift of a function on $D_v^\times$ can be chosen cuspidal. The Euler--Poincare functions used later are canonical examples. Their traces isolate discrete series and vanish on principal series.

The converse warning matters: support on matrices whose characteristic polynomial happens to be irreducible does not by itself imply vanishing constant term. Cuspidality is a distributional statement stable under conjugation and passage through the singular boundary.

### 5.3 The simple trace identity

Let $f=\bigotimes_vf_v$ be a global test function on $G^*(\mathbf A)$ with fixed central character, and suppose $f_{v_0}$ is cuspidal at one place. Then the simple trace formula is

$$
I_{G^*}(f)
:=\sum_{\pi\ \mathrm{discrete}}
m_{G^*}(\pi)\operatorname{tr}\pi(f)
=I_{\mathrm{cent}}(f)+I_{\mathrm{ell}}(f).
$$

Here the discrete sum consists of cuspidal representations and the one-dimensional automorphic characters occurring as residues of Eisenstein series. For $\mathrm{GL}_2$, each has multiplicity one, but again we retain the multiplicity until the comparison has been interpreted.

**Proof strategy.** Insert Arthur--Selberg truncation at height $T$. The difference between the truncated kernel and the cuspidal kernel is assembled from constant terms. Since one local factor has zero constant term, every factorizable parabolic distribution contains a zero local factor. The truncation parameter therefore disappears. On the geometric side the same local vanishing kills unipotent and split-torus contributions.

**Proof.** Start with compact-mod-center, finite-under-the-maximal-compact test functions at the archimedean places and locally constant compact-mod-center functions at the finite places. The spectral expansion of the truncated kernel consists of cuspidal terms, one-dimensional residual terms, and integrals of traces of induced representations. The global operator factors locally. Every representation in the continuous integral has a local component induced from the Borel at $v_0$, and $f_{v_0}$ has trace zero on it. The same zero factor occurs in the normalized intertwining distributions and their derivatives, so the continuous integrals and weighted corrections vanish. A one-dimensional residue is an irreducible constituent at a reducibility point; it need not have zero trace on $f_{v_0}$ and must remain in the discrete sum.

Geometrically, a split regular rational element is split at $v_0$, so its orbital integral is zero. The unipotent and weighted parabolic terms factor through the local constant term of $f_{v_0}$ and vanish. Only central and elliptic regular terms remain. The invariant trace formula supplies absolute convergence before these zero factors are inserted; after their insertion, its estimates give an absolutely convergent central-plus-elliptic expansion independent of the truncation parameter. Thus no interchange of an untruncated kernel near the cusp is being assumed. $\square$

The surviving one-dimensional terms are precisely where the exceptional spectrum enters. A local Euler--Poincare trace distinguishes Steinberg from the character constituent, while additivity on the reducible principal series relates their traces with opposite sign. They will be paired with quaternionic norm characters and subtracted before the cuspidal correspondence is extracted.

### 5.4 Why unwanted terms vanish

It is useful to separate three mechanisms that are often compressed into the word “cuspidal.”

- Split regular classes vanish because their local orbital integral is zero at a transfer place.
- Unipotent and weighted parabolic terms vanish because the local constant term is zero.
- Continuous induced spectral terms vanish because the local trace on induced representations is zero; one-dimensional residual constituents remain and are handled separately.

These are compatible consequences of the same rank-one Euler--Poincare construction, but they occur on different sides of the trace formula.

**Counterexample.** If every local factor is the hyperspecial unit, no factor is cuspidal. The identity operator on the spherical spectrum has a nonzero Eisenstein trace, split semisimple classes contribute, and the quotient has an uncancelled cusp. Equating that trace with a compact quaternionic trace would be false even though the two groups agree at almost every place.

## 6. Local transfer and the fundamental matching principle

### 6.1 Orbital integrals at ramified places

Fix $v\in R$. For regular $d\in D_v^\times$ and elliptic regular $g\in\mathrm{GL}_2(F_v)$ with the same characteristic polynomial, their centralizers are the same quadratic torus $T$. With compatible measures define

$$
O_d(f_v')=
\int_{T(F_v)\backslash D_v^\times}f_v'(x^{-1}dx)\,dx
$$

and

$$
O_g(f_v)=
\int_{T(F_v)\backslash\mathrm{GL}_2(F_v)}f_v(x^{-1}gx)\,dx.
$$

The functions match when

$$
O_g(f_v)=O_d(f_v')
$$

on matching elliptic classes and $O_g(f_v)=0$ on split regular classes. No sign appears. The Weyl discriminant

$$
\left|\frac{\operatorname{tr}(g)^2-4\det(g)}{\det(g)}\right|_v
$$

is equal on matching classes, so the statement is unchanged if normalized orbital integrals are used consistently.

Book 41 proves smooth transfer in both directions. The assertion includes neighborhoods of the singular set through matching central germs. It is stronger than matching on a collection of conveniently regular compact sets and weaker than pointwise equality of functions, which would not be canonical.

The corresponding trace relation is

$$
\operatorname{tr}\operatorname{JL}_v(\rho)(f_v)
=-\operatorname{tr}\rho(f_v').
$$

This relation holds for every irreducible $\rho$, including wild representations and norm characters. It is the only local representation-theoretic input used in the global trace comparison.

### 6.2 Split places and spherical units

At $v\notin R$, transfer is identity through $\iota_v$. If $v$ is finite and all data are unramified, choose compatible maximal orders so that

$$
\iota_v(\mathcal O_{D_v}^\times)=\mathrm{GL}_2(\mathcal O_v).
$$

With both compact subgroups of volume one, the unit functions correspond:

$$
\mathbf1_{\mathcal O_{D_v}^\times}
\longleftrightarrow
\mathbf1_{\mathrm{GL}_2(\mathcal O_v)}.
$$

The same is true for every spherical double coset. In particular the quaternionic operators $T_v,S_v$ become the identically normalized split operators. This tautological matching at almost all places is the fundamental lemma in its unramified split form.

The chosen algebra isomorphism does not affect the conclusion. Any two splittings differ by inner conjugacy, and spherical double cosets, traces, and orbital integrals are conjugation invariant.

### 6.3 The rank-one fundamental function

At a finite division place the maximal-compact unit cannot match the hyperspecial unit on $\mathrm{GL}_2$. The latter has nonzero split orbital integrals and sees unramified principal series, while the division group has no split classes. The correct partner is an Euler--Poincare function $f_v^{\mathrm{EP}}$ in the elliptic cocenter of $\mathrm{GL}_2(F_v)$.

With the compatible local measures, the rank-one fundamental matching statement is

$$
\mathbf1_{\mathcal O_{D_v}^\times}^{\omega_v}
\longleftrightarrow f_v^{\mathrm{EP},\omega_v},
$$

where the superscript denotes central-character averaging. The split function is a normalized vertex-minus-edge combination on the Bruhat--Tits tree. Its decisive properties are:

$$
O_g(f_v^{\mathrm{EP}})=
\begin{cases}
O_d(\mathbf1_{\mathcal O_{D_v}^\times}),&g\leftrightarrow d,\\
0,&g\text{ split regular},
\end{cases}
$$

and

$$
\operatorname{tr}\pi_v(f_v^{\mathrm{EP}})=0
$$

for every principal series $\pi_v$. Its value on a transferred discrete series is the negative of the division trace. Exact coefficients in the vertex-minus-edge expression depend on the measures of the maximal compact and Iwahori; the orbital and trace identities, not an unrecorded coefficient formula, are the invariant statement.

This is why maximal level changes under transfer. The division unit fixes an unramified norm character. Its split transfer is an unramified Steinberg twist, which has an Iwahori line but no hyperspecial line. Fundamental matching relates trace projectors; it does not assert equality of maximal-compact fixed spaces.

### 6.4 Product compatibility

Choose matching local pairs at every $v\in R$, identical pairs elsewhere, and units almost everywhere. The restricted tensors exist because all but finitely many factors are integral units. For a global matching class, Fubini's theorem and the restricted-product normalization give equality of global orbital integrals.

On the spectral side let $\Pi=\bigotimes_v'\Pi_v$ and define its candidate transfer locally. Then

$$
\prod_v\operatorname{tr}\pi_v(f_v)
=(-1)^{|R|}
\prod_v\operatorname{tr}\Pi_v(f_v')
=\prod_v\operatorname{tr}\Pi_v(f_v').
$$

The last equality uses the evenness of $R$. Product compatibility therefore holds simultaneously on the geometric and spectral sides.

One must include every ramified archimedean factor in this product. Treating the infinity type merely as a passive weight and multiplying signs only over $R_f$ breaks the trace identity for definite quaternion algebras of odd finite discriminant parity.

## 7. Comparison of geometric expansions

### 7.1 Matching rational elliptic classes

Let $\gamma\in D^\times(F)$ be regular. Its polynomial defines a quadratic field $E=F(\gamma)$ embedded in $D$. The companion matrix of that polynomial defines a unique $G^*(F)$-conjugacy class $\gamma^*$. At every place the two elements match, and their centralizers are the adelic points of the same torus $\operatorname{Res}_{E/F}\mathbf G_m$.

Conversely, let $\gamma^*\in G^*(F)$ have irreducible characteristic polynomial and suppose it is elliptic at every $v\in R$. Proposition 2.1 gives an embedding $E=F(\gamma^*)\hookrightarrow D$, and the image of the generating element defines a unique quaternionic rational conjugacy class. Hence

$$
\left\{\begin{array}{c}
\text{regular classes in }D^\times(F)
\end{array}\right\}
\longleftrightarrow
\left\{\begin{array}{c}
\text{regular classes in }\mathrm{GL}_2(F)\\
\text{elliptic at every }v\in R
\end{array}\right\}.
$$

This is an honest rational-class bijection in degree two. There is no additional sum over rational classes inside a stable class because characteristic polynomial already determines conjugacy for regular elements in both algebras.

### 7.2 Classes that do not come from the quaternion algebra

The split geometric expansion contains more rational semisimple classes than the quaternionic expansion. Each extra class vanishes for a visible local reason.

If the polynomial splits over $F$, it splits over every $F_v$. At any chosen $v\in R$, the local orbital integral of the elliptic transfer function is zero. Thus every global split regular term vanishes.

If the polynomial defines a quadratic field $E/F$ that does not embed in $D$, the embedding criterion gives a ramified place $v\in R$ that splits in $E$. The local matrix is split regular there, and again its orbital integral is zero.

Unipotent terms have no division-side counterpart. They factor through a parabolic constant term and vanish because the local transfer function at a ramified place is cuspidal. Weighted split-torus terms vanish for the same reason.

This reasoning is stronger than saying that “only elliptic terms survive.” A globally elliptic class may still be locally split at a ramified finite place and must be removed. The exact survivor condition is ellipticity at **every** ramified place.

### 7.3 Equality term by term

For matching regular classes $\gamma\leftrightarrow\gamma^*$, local transfer gives

$$
O_{\gamma^*}(f)=O_\gamma(f').
$$

Their volume coefficients are equal because their rational and adelic centralizers are the same torus with the same measure:

$$
a_{G^*}(\gamma^*)
=\operatorname{vol}\bigl(Z(\mathbf A)E^\times\backslash\mathbf A_E^\times\bigr)
=a_D(\gamma).
$$

The displayed quotient suppresses the standard identification of $E^\times$ with $G_\gamma(F)$ and the central embedding of $\mathbf A^\times$. Its finite volume is a torus Tamagawa volume.

For the central class, compatible projective Tamagawa numbers and matching central germs give equality. Thus central terms match central terms and every regular quaternionic term matches exactly one split term.

**Theorem 7.1 (geometric comparison).** For globally matching functions $(f,f')$ with a cuspidal local factor at a ramified place,

$$
I_{G^*,\mathrm{geom}}(f)=I_{D,\mathrm{geom}}(f').
$$

**Proof strategy.** Pair the central classes, pair the regular classes through their common polynomial, and prove that all unmatched split terms have a zero local factor.

**Proof.** The central equality follows from the chosen measures and singular transfer. Proposition 2.1 pairs the regular classes that can contribute. Equality of their centralizer volumes and products of local orbital integrals gives equality term by term. Section 7.2 kills every remaining split semisimple, unipotent, and parabolic term. Absolute convergence of the two simple expansions permits the resulting reindexing. $\square$

### 7.4 The global trace identity

Combining the compact trace formula, the simple split trace formula, and Theorem 7.1 gives

$$
\boxed{
\sum_{\pi\ \mathrm{discrete}}
m_{G^*}(\pi)\operatorname{tr}\pi(f)
=
\sum_{\Pi\ \mathrm{automorphic}}
m_D(\Pi)\operatorname{tr}\Pi(f').}
$$

Both sides at this stage include one-dimensional characters. If $\Xi=\chi\circ\operatorname{Nrd}$ and $\xi=\chi\circ\det$, then at a finite ramified place additivity in

$$
0\longrightarrow\chi_v\circ\det\longrightarrow I_v
\longrightarrow\operatorname{St}_v\otimes\chi_v\longrightarrow0
$$

and vanishing of $\operatorname{tr}I_v(f_v)$ give

$$
\operatorname{tr}\xi_v(f_v)
=-\operatorname{tr}(\operatorname{St}_v\otimes\chi_v)(f_v)
=\operatorname{tr}\Xi_v(f_v').
$$

At a ramified real place, the Euler--Poincare identity for the reducible real principal series gives the same equality between the split character trace and the compact norm-character trace; its discrete-series constituent is the real local transfer. At split places the traces agree tautologically. Moreover $\Xi$ and $\xi$ both have central character $\chi^2$, so this pairing respects the fixed $\omega$-block. Hence the global one-dimensional traces agree and may be subtracted. Using the multiplicity-one theorems of Books 42 and 43, the resulting identity is

$$
\boxed{
\sum_{\pi\ \mathrm{cuspidal}}
\operatorname{tr}\pi(f)
=
\sum_{\Pi\ \mathrm{noncharacter}}
\operatorname{tr}\Pi(f').}
$$

Section 1.2 identifies the intrinsic norm quotient with the idele class group, so every quaternionic norm character supplies one and only one split automorphic character in this subtraction. This is a distribution identity, not yet a termwise bijection. Extracting irreducible terms requires varying the local functions.

There is no uncancelled global sign. If one rewrites each ramified local trace through local Jacquet--Langlands, the sign product is $(-1)^{|R|}=1$. This agrees with the sign-free geometric comparison.

## 8. Spectral comparison and extraction

### 8.1 Factorized spectral traces

Fix a finite set $S$ containing $R$, every archimedean place, and every finite place where the central character or chosen representation is ramified. Outside $S$, use spherical unit functions except at finitely many auxiliary places where arbitrary spherical Hecke operators may be inserted. Inside $S$, use functions supported in selected Bernstein or compact-type blocks, with a cuspidal transfer factor at one ramified place.

For a constituent $\Pi$, its contribution factors as

$$
m_D(\Pi)
\prod_{v\in S}\operatorname{tr}\Pi_v(f_v')
\prod_{v\notin S}\lambda_{\Pi_v}(f_v'),
$$

where $\lambda_{\Pi_v}$ is the spherical Hecke character. The split contribution has the analogous form. Since fixed-type spaces are finite dimensional, only finitely many representations survive any such choice.

This finiteness turns the distribution identity into finite-dimensional character theory. Varying one local factor while holding the others fixed separates inequivalent local representations. Varying good-place Hecke operators separates different global cuspidal representations by strong multiplicity one.

### 8.2 Isolating one quaternionic constituent

Let $\Pi$ be a noncharacter automorphic representation of $G(\mathbf A)$. We show how the trace identity forces a corresponding cusp form.

**Proof strategy.** At a finite set of places choose local matrix-coefficient projectors that have nonzero trace on $\Pi_v$ and zero trace on the other local types occurring in the fixed-level space. At a ramified place use a transferred elliptic projector. Outside the set vary spherical Hecke operators. The quaternionic spectral side then has a nonzero $\Pi$ contribution. Equality of traces forces at least one cuspidal split constituent with the same good-place Hecke character.

Choose a level and archimedean type detecting $\Pi$. The resulting automorphic space is finite dimensional. Book 43's strong determination theorem, proved there from the intrinsic quaternionic kernel and not from global transfer, says that the complete spherical Hecke character away from a finite set singles out $\Pi$ among noncharacters. On any fixed finite-dimensional block, finitely many good-place Hecke operators already separate the finitely many characters that occur. Polynomial interpolation in those commuting operators therefore produces a projector onto the $\Pi$-isotypic summand without invoking the correspondence being proved.

At a chosen $v_0\in R$, local character independence supplies a function with nonzero trace on $\Pi_{v_0}$; smooth transfer supplies a cuspidal matching function on the split side. At the remaining places in a finite set, character independence separates the finitely many local types in the chosen block. Expanding the resulting projector as a finite linear combination of factorizable functions preserves the hypothesis that every summand has a cuspidal factor at $v_0$.

The quaternionic trace of this finite combination on $\Pi$ is nonzero and its trace on every other noncharacter constituent in the block is zero. Apply the character-subtracted identity of Section 7.4. If the split cuspidal side were empty, that identity would give zero, a contradiction. Therefore some cuspidal $\pi$ occurs. Varying the finitely many auxiliary spherical operators and using linear independence of their characters shows that it has the same spherical Hecke character as $\Pi$ at almost every split place. Hence

$$
\pi_v\cong\Pi_v.
$$

The noncharacter hypothesis is essential in the isolation step. The projector must be taken in the orthogonal complement of the global character spectrum; otherwise the elliptic relation at reducible principal series can move trace between a norm character and a special constituent without producing the desired global tensor.

### 8.3 Recovering every local component

Agreement at almost all places is not the full theorem. Let $w$ be any place.

If $w\notin R$, vary $f_w=f_w'$ through the full local Hecke algebra while keeping isolating functions elsewhere. Equality of the resulting trace distributions gives equality of the characters of $\pi_w$ and $\Pi_w$, hence

$$
\pi_w\cong\Pi_w.
$$

If $w\in R$, vary $f_w'$ arbitrarily and choose matching $f_w$. After the other factors isolate the global pair, the trace identity becomes

$$
\operatorname{tr}\pi_w(f_w)
=-\operatorname{tr}\Pi_w(f_w').
$$

The minus sign here is not inserted by hand. The fixed transfer functions at the other $|R|-1$ ramified places contribute $(-1)^{|R|-1}=-1$, while the complete global sign is $+1$. Local Jacquet--Langlands uniqueness gives

$$
\pi_w\cong\operatorname{JL}_w(\Pi_w).
$$

This argument handles every ramified place separately, including real places. It does not infer a bad local component from conductor or from almost-all Hecke data. Those coarser invariants are consequences after the actual local representation has been identified.

### 8.4 Strong multiplicity one and uniqueness

The extraction may initially produce several cuspidal $\pi$ with the same almost-all spherical data. Strong multiplicity one for $\mathrm{GL}_2$ says that any two are isomorphic. Thus the transfer of $\Pi$ is unique and may be denoted

$$
\operatorname{JL}_D(\Pi).
$$

The logical order is important:

$$
\text{trace comparison}
\Longrightarrow\text{existence and good-place agreement}
\Longrightarrow\text{strong multiplicity one}
\Longrightarrow\text{global uniqueness}.
$$

Strong multiplicity one alone cannot prove existence. Nor is local multiplicity one enough: it says that a local generic model is unique, not that the global tensor occurs automorphically.

## 9. The global correspondence

### 9.1 Precise statement

We can now state the theorem with its exceptional clause visible.

**Theorem 9.1 (global Jacquet--Langlands for quaternion algebras).** Let $D$ be a quaternion division algebra over a number field $F$, with ramification set $R$. There is a unique bijection

$$
\operatorname{JL}_D:
\left\{\begin{array}{c}
\text{irreducible noncharacter automorphic}\\
\text{representations }\Pi\text{ of }D^\times(\mathbf A_F)
\end{array}\right\}
\xrightarrow{\sim}
\left\{\begin{array}{c}
\text{irreducible cuspidal automorphic representations }\pi\\
\text{of }\mathrm{GL}_2(\mathbf A_F)\text{ such that }\pi_v\\
\text{is discrete series for every }v\in R
\end{array}\right\}.
$$

It is characterized by

$$
\operatorname{JL}_D(\Pi)_v\cong
\begin{cases}
\Pi_v,&v\notin R,\\
\operatorname{JL}_v(\Pi_v),&v\in R.
\end{cases}
$$

At a ramified real place, “discrete series” means the archimedean discrete representation paired with the finite-dimensional representation of $\mathbf H^\times$; the appropriate holomorphic and antiholomorphic realization is determined by the chosen infinity type. Each representation occurs with the same automorphic multiplicity. In the present groups both multiplicities are one.

If $D=M_2(F)$, no inner-form comparison is needed: global Jacquet--Langlands is, by definition, the identity on the cuspidal spectrum of $\mathrm{GL}_2(\mathbf A_F)$. This split boundary case is stated separately because the phrase “noncharacter automorphic representation of $D^\times$” would otherwise also admit noncuspidal induced representations, which are not in the source of the displayed bijection.

### 9.2 Existence and injectivity

Existence for every noncharacter $\Pi$ was proved by spectral extraction. The local formulas determine every component of $\pi$.

For injectivity, suppose

$$
\operatorname{JL}_D(\Pi_1)\cong
\operatorname{JL}_D(\Pi_2).
$$

At split places the local components of $\Pi_1$ and $\Pi_2$ agree. At ramified places local Jacquet--Langlands is injective, so their local components agree there as well. Hence the two restricted tensor products are isomorphic. Equivalently, strong determination on the quaternionic spectrum already identifies them from almost all split places. Thus $\Pi_1\cong\Pi_2$.

This proof uses local injectivity only after global existence. It avoids the invalid inference that two abstract restricted tensors with equal factors must both be automorphic.

### 9.3 Surjectivity onto the stated image

Let $\pi$ be cuspidal on $\mathrm{GL}_2(\mathbf A)$ and assume $\pi_v$ is discrete series for every $v\in R$. Define candidate quaternionic factors by

$$
\Pi_v^{\mathrm{cand}}=
\begin{cases}
\pi_v,&v\notin R,\\
\operatorname{JL}_v^{-1}(\pi_v),&v\in R.
\end{cases}
$$

Use local pseudo-coefficients of $\pi_v$ at ramified places and transfer them to $D_v^\times$. At the other places use identical functions. The reverse geometric comparison is the same term-by-term identity. Isolate $\pi$ using a finite type and good-place Hecke operators, and apply the character-subtracted identity of Section 7.4 rather than the full discrete identity. The split cuspidal trace is nonzero, so the quaternionic **noncharacter** trace contains a constituent $\Pi$. Local character independence identifies every $\Pi_v$ with $\Pi_v^{\mathrm{cand}}$.

This use of the subtracted identity is essential when some $\pi_v$ is Steinberg: a local pseudo-coefficient can have nonzero trace on the one-dimensional constituent at the same reducibility point. In the full trace formula that residual contribution pairs with a quaternionic norm character and would not by itself prove a noncharacter preimage. As a consistency check, a norm-character preimage would also make $\pi_v$ one dimensional at almost every split place, contradicting the local genericity of a cuspidal representation.

The hypothesis at **every** ramified place is necessary. If $\pi_v$ is principal series at even one $v\in R$, there is no local inverse transfer and the corresponding split orbital data have no division representation to carry them.

### 9.4 Multiplicity preservation

Before inserting known multiplicity-one theorems, isolate a corresponding pair $(\Pi,\pi)$ on both sides and normalize the local projectors to have trace one. The global trace identity reduces to

$$
m_{G^*}(\pi)=m_D(\Pi).
$$

Thus trace comparison preserves automorphic multiplicity. Book 43 gives $m_D(\Pi)=1$, while global Whittaker uniqueness gives $m_{G^*}(\pi)=1$. The equality is therefore

$$
m_D(\Pi)=m_{G^*}(\operatorname{JL}_D(\Pi))=1.
$$

This statement concerns occurrences in the automorphic spectrum. It does not say that $\dim\Pi_f^U$ equals $\dim\pi_f^K$. Fixed-vector dimensions can differ dramatically at ramified places: a division newlevel block may have dimension $\dim\Pi_v$, while the split newvector space is a line.

## 10. Norm characters and the exceptional spectrum

### 10.1 Why global characters must be separated

The projective quaternionic quotient is compact, so its one-dimensional characters occur discretely and with multiplicity one. By Section 1.2, a character of the reduced-norm quotient corresponds to a unique Hecke character $\chi$, and the resulting automorphic representation is

$$
\Pi=\chi\circ\operatorname{Nrd}.
$$

At every split place,

$$
\Pi_v=\chi_v\circ\det.
$$

This local representation is one dimensional and not discrete series. At every ramified finite place, however, local Jacquet--Langlands gives a Steinberg twist. The formal local recipe therefore changes type only at the finite set $R$.

No cuspidal representation can have one-dimensional components at almost every place. Global genericity already excludes it, and the Rankin--Selberg pole criterion gives another proof. Hence global norm characters do not belong to the domain of the cuspidal bijection.

Although the reduced-norm image is smaller at ramified real places, Section 1.2 shows that passage to the rational quotient removes the apparent sign ambiguity. The intrinsic character is presented by a unique Hecke character $\chi$. The exception is therefore exactly the one-dimensional automorphic spectrum, with no multiplicity caused by choices of extension.

### 10.2 Their local Steinberg transfers

At a finite $v\in R$,

$$
\operatorname{JL}_v(\chi_v\circ\operatorname{Nrd})
=\operatorname{St}_v\otimes(\chi_v\circ\det).
$$

If $\chi_v$ is unramified, the division character is fixed by $\mathcal O_{D_v}^\times$ and has prepared conductor zero, whereas its Steinberg transfer has conductor exponent one. If $a(\chi_v)>0$, both prepared and split exponents equal $2a(\chi_v)$.

At a ramified real place, the trivial representation of $\mathbf H^\times$ transfers to the lowest member of the real discrete-series family, of weight two in the algebraic convention. More general norm powers and signs preserve the common central character. Thus the slogan “a norm character transfers to Steinberg” includes the real discrete-series analogue.

These local statements remain correct even though their restricted tensor does not globalize cuspidally. Local transfer is a theorem about one place; global automorphy imposes an additional compatibility.

### 10.3 How the trace comparison accounts for them

At a finite ramified place the reducible normalized principal series has, in the Grothendieck group, a character constituent and a Steinberg constituent whose elliptic characters are negatives. The Euler--Poincare test function annihilates the full induced representation, so the trace of the character constituent is the negative of the Steinberg trace. Since local Jacquet--Langlands makes the Steinberg trace the negative of the division norm-character trace, the two negatives cancel:

$$
\operatorname{tr}(\chi_v\circ\det)(f_v)
=\operatorname{tr}(\chi_v\circ\operatorname{Nrd})(f_v').
$$

At a ramified real place the analogous Euler--Poincare identity relates the one-dimensional split constituent, the lowest discrete-series constituent, and the compact norm character in the same way. Thus the full simple trace formula pairs a quaternionic norm character with the corresponding one-dimensional automorphic representation $\chi\circ\det$ on the split group. This exceptional pairing does **not** satisfy local Jacquet--Langlands at ramified places. Subtracting these equal character traces leaves the noncharacter quaternionic trace and the cuspidal split trace.

On the quaternionic side it is often convenient to define

$$
L^2_0(G,\omega)
=L^2(G,\omega)\ominus
\bigoplus_{\Xi\ \mathrm{one\ dimensional}}\Xi.
$$

The noncharacter trace formula is the restriction of the compact trace to this orthogonal complement. The global theorem compares this trace with the cuspidal trace of $\mathrm{GL}_2$. Removing characters is therefore not an arbitrary repair made after the proof; it is the spectral operation matching removal of the Eisenstein boundary.

For finite algebraic quaternionic spaces, the same operation is the complement of the norm-character subspace in characteristic zero. Over an integral ring the complement need not split, so the safe object is the quotient by the saturated character submodule.

### 10.4 A counterexample to naive globalization

Take the trivial automorphic representation $\mathbf1$ of a definite quaternion algebra over $\mathbf Q$ ramified at $p$ and $\infty$. The naive local tensor would have

$$
\pi_\ell=\mathbf1\circ\det\quad(\ell\ne p),
$$

while

$$
\pi_p=\operatorname{St}_p,\qquad
\pi_\infty=D_2.
$$

If this tensor were cuspidal, its unramified component at almost every prime would be one dimensional. That contradicts local genericity of cuspidal representations. It also predicts good-prime Hecke eigenvalues of the constant quaternionic function, namely the degree $\ell+1$, which belong to the Eisenstein pattern rather than a weight-two cusp form.

The example simultaneously shows why the local Steinberg statement is correct and why it cannot be promoted to a global cuspidal transfer for characters.

## 11. Structural compatibilities

### 11.1 Central characters, twists, and contragredients

Let $\pi=\operatorname{JL}_D(\Pi)$. At split places the central characters agree tautologically; at ramified places local transfer preserves them. Therefore

$$
\boxed{\omega_\pi=\omega_\Pi.}
$$

The equality is global because both products are trivial on $F^\times$ and have equal local factors everywhere.

Let $\chi$ be a Hecke character. On the quaternionic side twist by $\chi\circ\operatorname{Nrd}$; on the split side twist by $\chi\circ\det$. Local twisting compatibility gives the same candidate factors at every place. Global uniqueness then gives

$$
\boxed{
\operatorname{JL}_D\bigl(\Pi\otimes(\chi\circ\operatorname{Nrd})\bigr)
\cong
\operatorname{JL}_D(\Pi)\otimes(\chi\circ\det),}
$$

provided the quaternionic twist remains a noncharacter. Its central character is $\omega_\Pi\chi^2$, since both norm maps send a scalar $z$ to $z^2$.

Inversion preserves matching characteristic polynomials in the form $g^{-1}\leftrightarrow d^{-1}$. Thus local transfer commutes with smooth duals, and global uniqueness yields

$$
\boxed{
\operatorname{JL}_D(\Pi^\vee)
\cong\operatorname{JL}_D(\Pi)^\vee.}
$$

No complex conjugation is part of this algebraic identity. In a unitary realization one may identify the contragredient with the complex conjugate representation.

Twisting can turn a noncharacter into another noncharacter but cannot make a higher-dimensional local component one dimensional. Globally, a noncharacter representation remains noncharacter under a one-dimensional twist.

### 11.2 Conductors and exact local shifts

At a split finite place $v\notin R$, the local representation is unchanged, so

$$
a(\pi_v)=a(\Pi_v).
$$

At a division place let

$$
c_D(\Pi_v)=\min\{m\ge0:U_{D_v}^m\text{ acts trivially on }\Pi_v\}.
$$

The exact comparison is:

$$
a(\pi_v)=
\begin{cases}
c_D(\Pi_v)+1,&\dim\Pi_v>1,\\
1,&\Pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)=0,\\
2a(\mu_v),&\Pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)>0.
\end{cases}
$$

Book 41's prepared division exponent is

$$
a_D(\Pi_v)=
\begin{cases}
c_D(\Pi_v)+1,&\dim\Pi_v>1,\\
2a(\mu_v),&\Pi_v=\mu_v\circ\operatorname{Nrd}.
\end{cases}
$$

Thus $a(\pi_v)=a_D(\Pi_v)$ except for an unramified norm character, where $0$ becomes $1$. Globally define

$$
\mathfrak f_D(\Pi)=
\prod_{v<\infty}\mathfrak p_v^{a_D(\Pi_v)}
$$

using the usual split exponent off $R_f$, and put

$$
R_0(\Pi)=
\{v\in R_f:\Pi_v\text{ is an unramified norm character}\}.
$$

Then

$$
\boxed{
\mathfrak f(\operatorname{JL}_D(\Pi))
=\mathfrak f_D(\Pi)
\prod_{v\in R_0(\Pi)}\mathfrak p_v.}
$$

This is the exact level change. Replacing the correction product by the full discriminant is valid only when every ramified finite component is an unramified norm character, as happens for maximal division level.

**Worked cancellation.** Suppose $\Pi_v=\mu_v\circ\operatorname{Nrd}$ with $\mu_v$ nontrivial tame quadratic. Both sides have conductor exponent two. Twisting by the same $\mu_v$ produces the trivial division character and unramified Steinberg; the exponents become zero and one. A maximum-of-conductors rule would incorrectly leave exponent two.

### 11.3 Local and global factors and formal degrees

For a finite place $v\in R$, local transfer preserves the standard factors constructed from zeta integrals on the two degree-two algebras:

$$
L(s,\pi_v)=L(s,\Pi_v),
$$

$$
\epsilon(s,\pi_v,\psi_v)
=\epsilon(s,\Pi_v,\psi_v).
$$

At split places the equality is tautological. Therefore the finite Euler products agree:

$$
L^S(s,\operatorname{JL}_D(\Pi))
=L^S(s,\Pi)
$$

for every finite set $S$ containing the archimedean and ramified data. After the archimedean factors are included in the same normalization, the completed standard $L$-functions agree.

For a norm character at a ramified finite place,

$$
L(s,\mu_v\circ\operatorname{Nrd})
=L(s+1/2,\mu_v)
=L(s,\operatorname{St}_v\otimes\mu_v).
$$

For a higher-dimensional division representation and its supercuspidal transfer, the standard local factor is $1$. These formulas illustrate why factor compatibility cannot be inferred merely from conductor equality.

Twists satisfy the same identity after replacing $\Pi$ by $\Pi\otimes\chi$. At a ramified place the local factor may change by cancellation, and the equality remains true because it is representation-theoretic, not a formula in the old conductor alone.

The formal-degree comparison is equally local but has a different normalization requirement. At a finite division place, give the projective groups the compatible measures

$$
\operatorname{vol}(\mathrm{PGL}_2(\mathcal O_v))=1,
\qquad
\operatorname{vol}(D_v^\times/F_v^\times)=\frac{2}{q_v-1}.
$$

For a unitary $\Pi_v$, Book 41 then gives

$$
\boxed{
d_{\mathrm{GL}_2(F_v)}(\operatorname{JL}_v(\Pi_v))
=d_{D_v^\times}(\Pi_v)
=\frac{q_v-1}{2}\dim\Pi_v.}
$$

This identity is not invariant under independent rescaling of the two Haar measures. It is compatible with the product measures used in the trace formula only after the finite conversion factors of Section 3.2 have been included. Formal degree is a local Plancherel invariant; it does not multiply into an additional global multiplicity, and it should not be confused with the dimensions of level-fixed spaces.

### 11.4 Root numbers and additive characters

Choose a nontrivial global additive character

$$
\psi:F\backslash\mathbf A\longrightarrow\mathbf C^\times
$$

and write $\psi=\prod_v\psi_v$. The global epsilon factor is

$$
\epsilon(s,\Pi,\psi)=\prod_v\epsilon(s,\Pi_v,\psi_v),
$$

with the analogous definition for $\pi$. Local compatibility gives

$$
\boxed{
\epsilon(s,\operatorname{JL}_D(\Pi),\psi)
=\epsilon(s,\Pi,\psi).}
$$

At $s=1/2$ this is equality of global root numbers. The product is independent of replacing $\psi$ by $\psi_a(x)=\psi(ax)$ for $a\in F^\times$, because the local scaling factors multiply to one by the product formula and global central-character triviality on $F^\times$.

Changing only one local additive character does change the local epsilon factor. Thus a table of local root numbers must record the conductor of $\psi_v$; global invariance does not justify suppressing local normalizations.

## 12. Unramified Hecke data

### 12.1 Spherical operators and Satake parameters

Let $v$ be finite, split for $D$, and unramified for $\Pi$, its central character, and the level. With $K_v=\mathrm{GL}_2(\mathcal O_v)$ of volume one, let

$$
T_v=\mathbf1_{K_v\operatorname{diag}(\varpi_v,1)K_v},
\qquad
S_v=\mathbf1_{K_v\operatorname{diag}(\varpi_v,\varpi_v)K_v}.
$$

On the spherical line of $\Pi_v$ write

$$
T_v\mapsto t_v,\qquad S_v\mapsto s_v.
$$

The raw integral Hecke polynomial is

$$
P_v(X)=1-t_vX+q_vs_vX^2.
$$

If $\alpha_v,\beta_v$ are unitary normalized Satake parameters, then

$$
t_v=q_v^{1/2}(\alpha_v+\beta_v),
\qquad
s_v=\alpha_v\beta_v.
$$

If $A_v,B_v$ are the raw reciprocal roots, then $A_v=q_v^{1/2}\alpha_v$, $B_v=q_v^{1/2}\beta_v$, and $A_vB_v=q_vs_v$.

### 12.2 Equality of Hecke polynomials

At $v\notin R$, global transfer gives an isomorphism $\pi_v\cong\Pi_v$. Hence their spherical Hecke characters agree exactly:

$$
t_v(\pi)=t_v(\Pi),
\qquad
s_v(\pi)=s_v(\Pi),
$$

and

$$
\boxed{P_v(X,\pi)=P_v(X,\Pi).}
$$

No sign appears at a good place. The local minus sign belongs only to character transfer at a division place; it is not a sign change in good Hecke eigenvalues.

For a twist by an unramified character $\chi_v$,

$$
t_v\longmapsto\chi_v(\varpi_v)t_v,
\qquad
s_v\longmapsto\chi_v(\varpi_v)^2s_v.
$$

Both raw roots acquire $\chi_v(\varpi_v)$, and equality of polynomials remains true after twisting.

### 12.3 Good-place eigensystems determine the transfer

Suppose $\pi$ and $\pi'$ are cuspidal and have the same $T_v$ and $S_v$ eigenvalues for all but finitely many places. The two symmetric functions recover the unordered Satake pair, so $\pi_v\cong\pi_v'$ almost everywhere. Strong multiplicity one gives $\pi\cong\pi'$.

Consequently the away-from-$S$ quaternionic eigensystem determines the transferred cuspidal representation, once the character spectrum has been removed. This is the practical form used in arithmetic applications: one often computes only Brandt or double-coset eigenvalues away from the discriminant and level, yet obtains a unique split automorphic representation.

The central operator $S_v$ can be omitted from the recorded data only after the global central character has been fixed. Otherwise two different determinant parameters can share the same trace parameter.

### 12.4 What good-place data do not determine

Almost-all Hecke data determine the global isomorphism class of a cusp representation, but they do not by themselves prove that a proposed local tensor is automorphic. That was the role of the trace formula. Nor do they recover a chosen vector at nonminimal level: oldvectors in one representation have the same good-place eigenvalues.

They also do not replace the image condition. A cuspidal representation may have the same kind of spherical data away from $R$ while being principal series at one ramified place. Such a representation is perfectly legitimate on $\mathrm{GL}_2$ but has no quaternionic preimage for that $D$.

Finally, equality of $T_v$ alone is insufficient when the central character is not fixed. Both coefficients of the Hecke polynomial are part of the unramified local representation.

## 13. Archimedean weights and algebraic structures

### 13.1 Real ramification turns weight into discrete series

Let $\tau:F\hookrightarrow\mathbf R$ be a real place ramified in $D$. Then

$$
D_\tau^\times\cong\mathbf H^\times,
$$

which is compact modulo its center. An irreducible representation $\Pi_\tau$ is finite dimensional. Local Jacquet--Langlands sends it to a discrete-series representation of $\mathrm{GL}_2(\mathbf R)$ with the same central character.

This is the archimedean source of holomorphic weight. A finite-dimensional highest weight on the compact inner form becomes a lowest or highest $K$-type in an infinite-dimensional discrete series on the split form. Dimension is not preserved; infinitesimal character, central character, and elliptic character are.

At a real split place, no transfer occurs and $\pi_\tau=\Pi_\tau$. At a complex place every quaternion algebra splits, so again there is no inner-form change.

The real local correspondence can be seen directly from the Weyl character formulas. Restrict a finite-dimensional representation of $\mathbf H^\times$ to the norm-one group $\mathrm{SU}_2$. If its highest weight is $n$, its character on an elliptic element with eigenvalues $e^{i\theta},e^{-i\theta}$ is

$$
\frac{\sin((n+1)\theta)}{\sin\theta}.
$$

The stable elliptic character of the corresponding discrete series on $\mathrm{GL}_2(\mathbf R)$ is its negative after the common central character is inserted. The two Weyl denominators are the same and the rank difference supplies the minus sign. Orthogonality on the compact torus shows uniqueness, while the explicit discrete-series construction gives existence. Thus the archimedean factor obeys the same geometric sign convention as the nonarchimedean factors.

This calculation also explains the weight shift. The compact character with highest exponent $n$ has $n+1$ weights, whereas the split discrete series begins at compact weight $n+2$; the missing boundary weight is the archimedean analogue of the Steinberg phenomenon.

### 13.2 Highest weights and lowest weights

Write the algebraic representation at a ramified real place, after complexification, in the form

$$
W_\tau=\operatorname{Sym}^{n_\tau}(\mathbf C^2)
\otimes\operatorname{Nrd}^{m_\tau},
\qquad n_\tau\ge0.
$$

Its scalar central action is $z^{n_\tau+2m_\tau}$. With the right-translation convention of quaternionic forms, the automorphic local factor is $W_\tau^\vee$. Its transfer has minimal compact weight

$$
k_\tau=n_\tau+2
$$

and the same scalar central character as $W_\tau^\vee$. This pair of requirements fixes the determinant or norm twist without requiring a potentially ambiguous analytic half-power formula.

For $n_\tau=0$, the trivial compact type transfers to weight two discrete series. For $n_\tau=2$, the minimal weight is four. The shift by two is the familiar difference between an algebraic coefficient degree and a holomorphic modular weight.

One must respect the dual forced by the action convention. If finite quaternionic forms transform on the left through $W$, their generated automorphic representation contains $W^\vee$ at infinity. Forgetting this dual reverses determinant exponents and central characters.

### 13.3 Cohomological transfer

Suppose $F$ is totally real and $D$ is totally definite. Let the coefficient system be described by pairs $(a_\tau,b_\tau)$ with

$$
W_\tau=\operatorname{Sym}^{a_\tau-b_\tau}(\mathbf C^2)
\otimes\det^{b_\tau}.
$$

Then the transferred Hilbert modular weight is

$$
k_\tau=a_\tau-b_\tau+2.
$$

If $a_\tau+b_\tau=w$ is independent of $\tau$, the coefficient system has a global algebraic central weight and the split transfer is cohomological. The algebraic and unitary normalizations differ by a common norm power; all Hecke and $L$-factor formulas must be shifted together when moving between them.

The theorem does not claim algebraicity for arbitrary Maass-type archimedean parameters. Algebraic and cohomological conclusions require an algebraic coefficient system on the quaternionic side.

### 13.4 Parity and the global center

At a real place, the lowest weight $k_\tau$ determines the action of $-1$ by $(-1)^{k_\tau}$, modified by the prescribed sign of the central character. Because a global Hecke character is trivial on the principal element $-1\in F^\times$, the product of local signs must be one.

Thus locally available weights cannot be assembled arbitrarily. For example, over a totally real field with two real places, weights $2$ and $3$ with trivial finite central character violate the global parity condition. Each local discrete series exists, but their tensor cannot be an automorphic infinity type with trivial center.

Global Jacquet--Langlands preserves rather than repairs this condition: the quaternionic coefficient system and the split discrete series have the same scalar actions at each place, so either both global central characters descend or neither does.

## 14. Finite level, newforms, and exact level change

### 14.1 From quaternionic fixed vectors to split newvectors

Let $U=\prod_{v<\infty}U_v\subset D^\times(\mathbf A_f)$ be a compact open and let $W$ be an archimedean algebraic weight. The finite quaternionic space decomposes in characteristic zero as

$$
S_D(U,W,\omega)
\cong
\bigoplus_\Pi
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\Pi_\infty)
\otimes\Pi_f^U,
$$

with multiplicity one and with a separate norm-character block.

For a noncharacter constituent, transfer identifies the global representation but not the fixed-vector space. At split places $U_v$ is transported unchanged and the invariant spaces agree. At division places the local level must be translated through conductor and type theory.

If $\dim\Pi_v>1$ and $c=c_D(\Pi_v)$, then

$$
\Pi_v^{U_D^{c-1}}=0,
\qquad
\Pi_v^{U_D^c}=\Pi_v,
$$

while the transfer has

$$
\pi_v^{K_1(\mathfrak p_v^c)}=0,
\qquad
\dim\pi_v^{K_1(\mathfrak p_v^{c+1})}=1.
$$

Thus an entire division representation block first appears one step before a single split newvector line in the respective filtrations.

### 14.2 Maximal level and the discriminant factor

Suppose $U_v=\mathcal O_{D_v}^\times$ at every $v\in R_f$. A local irreducible with $U_v$-fixed vectors must be an unramified norm character. Its split transfer is an unramified Steinberg twist of conductor exponent one. Therefore every ramified finite prime occurs exactly once in the split conductor.

At split places suppose the chosen level is minimal for $\Pi_v$, with conductor ideal $\mathfrak n$ prime to the reduced discriminant

$$
\mathfrak d(D)=\prod_{v\in R_f}\mathfrak p_v.
$$

Then

$$
\boxed{
\mathfrak f(\operatorname{JL}_D(\Pi))
=\mathfrak d(D)\mathfrak n.}
$$

Moreover the transferred representation is new at every prime dividing $\mathfrak d(D)$. This is the classical “discriminant times Eichler level” formula. It is exact under the maximal-level and coprimality hypotheses just stated.

**Counterexample to unrestricted multiplication.** If $\Pi_v$ is higher dimensional at a ramified place and has $c_D(\Pi_v)=3$, its transfer has exponent four, not one. Multiplying a split-side level by the squarefree discriminant would record exponent one and miss three units of depth.

### 14.3 Deeper division levels

For the normal principal congruence tower $U_D^m=1+\mathfrak P_D^m$, a higher-dimensional $\Pi_v$ first appears when $m=c_D(\Pi_v)$ and transfers to split conductor exponent $m+1$. At deeper $U_D^{m+r}$ the invariant space remains the whole $\Pi_v$; it does not grow with $r$. On the split side, however,

$$
\dim\pi_v^{K_1(\mathfrak p_v^{m+1+r})}=r+1.
$$

There is therefore no level-by-level vector-space isomorphism along these two towers.

For a ramified norm character $\mu_v\circ\operatorname{Nrd}$ of character conductor $r>0$, the split exponent is $2r$. For an unramified norm character it is one. For a nonnormal toral or Eichler-type subgroup $H_v\subset D_v^\times$, fixed vectors are governed by the Mackey sum

$$
\dim\Pi_v^{H_v}
=\sum_{x\in J\backslash D_v^\times/H_v}
\dim\operatorname{Hom}_{J\cap xH_vx^{-1}}(\Lambda,\mathbf1)
$$

when $\Pi_v$ is compactly induced from $(J,\Lambda)$. Conductor alone does not determine this dimension or the corresponding split type.

The safe finite-level statement is thus representation by representation: transfer the constituent, compute its exact local conductor, and then choose the split newvector or desired type. A numerical ideal by itself cannot encode every compact-open condition.

### 14.4 Hecke modules and eigensystems

Let $\Sigma$ contain $R_f$, the split level primes, and the ramification of the central character. Away from $\Sigma$, the same abstract spherical Hecke algebra

$$
\mathbb T^\Sigma
=\mathbf Z[T_v,S_v,S_v^{-1}:v\notin\Sigma]
$$

acts on both quaternionic and split spaces with the same unnormalized conventions. Global transfer gives an equality of characters of this algebra on corresponding constituents.

In characteristic zero, after removing the norm-character block, the quaternionic module and the appropriate $\mathrm{GL}_2$ newform module have the same simple away-from-$\Sigma$ Hecke eigensystems, with the same multiplicities as representations. At minimal standard level each split constituent contributes its one-dimensional newvector line; on the quaternionic side a ramified local factor may contribute a higher-dimensional newlevel block. Thus equality of eigensystems need not be an equality of total vector-space dimensions unless the local type multiplicities are included.

For maximal division level in the totally definite case, the relevant local factors at $R_f$ are unramified norm characters and their split transfers have one-dimensional Iwahori newlines. Then the noncharacter quaternionic eigensystems agree exactly with the new eigensystems of split level $\mathfrak d(D)\mathfrak n$, new at every prime of $\mathfrak d(D)$ and with the matching nebentype. Oldforms at auxiliary split primes must be removed or counted through their degeneracy multiplicities.

Operators at primes in the discriminant are not identified with good spherical operators. The division valuation operator and the split $U_v$ or Atkin--Lehner action require their own local normalization. The robust common algebra is the spherical algebra away from $\Sigma$; refined bad-place compatibility is expressed through the identified local representations and types.

## 15. Rationality and conjugation

### 15.1 What character identities prove

The global correspondence is characterized by local character identities at ramified places and equality of local representations at split places. Both statements are algebraic after the representations and test functions have been placed over a number field. If $\sigma\in\operatorname{Aut}(\mathbf C)$, applying $\sigma$ to the identities gives

$$
\Theta_{\pi_v^\sigma}(g)
=-\Theta_{\Pi_v^\sigma}(d)
$$

on matching ramified classes and equality of spherical Hecke characters at split places. Local uniqueness and global strong multiplicity one therefore imply

$$
\boxed{
\operatorname{JL}_D(\Pi^\sigma)
\cong\operatorname{JL}_D(\Pi)^\sigma}
$$

whenever the infinity types are transported through their algebraic coefficient systems.

This proof does not apply an automorphism to analytic square roots $q_v^{1/2}$ or to arbitrary transcendental matrix coefficients. It applies $\sigma$ to algebraically normalized character and Hecke identities.

### 15.2 Fields of coefficients

For a cohomological quaternionic eigensystem, define its Hecke field by

$$
E(\Pi)=
\mathbf Q\bigl(t_v(\Pi),s_v(\Pi):v\notin\Sigma\bigr),
$$

with the values of the central character included when they are not already fixed. The finite algebraic quaternionic space has a number-field model, so this is a number field. Equality of good-place Hecke polynomials gives

$$
E(\Pi)=E(\operatorname{JL}_D(\Pi))
$$

for the finite eigensystems in the same algebraic normalization.

Bad-place eigenvalues may enlarge the field needed to realize a chosen local type, even though they do not enlarge the field of rationality of the global finite representation when strong multiplicity one already fixes it. Likewise a particular basis of a division newlevel block can require a larger splitting field than its central Hecke character.

### 15.3 Galois conjugation

Let $f_D$ be a quaternionic eigenform in an algebraic weight and let $f$ be the transferred Hilbert or classical newform, normalized in their one-dimensional eigenlines. For every good $v$,

$$
t_v(f^\sigma)=\sigma(t_v(f))
=\sigma(t_v(f_D))=t_v(f_D^\sigma),
$$

and similarly for $S_v$. Strong multiplicity one identifies the representation generated by $f^\sigma$ with the transfer of the representation generated by $f_D^\sigma$.

At infinity the weight labels remain integers. What changes under $\sigma$ is the embedding of the coefficient field, not the analytic choice of a holomorphic coordinate. If a coefficient system has several conjugate embeddings, $\sigma$ permutes those algebraic realizations in the usual way.

### 15.4 Limits of the rationality statement

Character and Hecke identities prove equality of fields of rationality and compatibility of algebraic conjugation. They do not automatically prove that the entire infinite-dimensional representation has a model over exactly that field. A Schur index or a ramified type can obstruct descent.

Nor do they prove algebraicity for an arbitrary unitary Maass representation. Finite-dimensionality over $\mathbf C$ alone gives characteristic polynomials with complex coefficients, not number-field coefficients. The rationality conclusions in this chapter require the algebraic or cohomological structures already constructed on the two sides.

Periods are also outside the conclusion. A quaternionic algebraic eigenvector and a normalized split newform can have the same Hecke field while their natural inner products differ by transcendental period factors. Global Jacquet--Langlands as proved here compares representations and Hecke characters, not canonical period normalizations.

## 16. Examples over the rationals

### 16.1 Definite discriminant eleven and weight two

Let $D/\mathbf Q$ be ramified exactly at $11$ and $\infty$, and let $\mathcal O$ be a maximal order. At finite level $\widehat{\mathcal O}^{\times}$ and trivial algebraic weight, the quaternionic space is the space of functions on the finite right-ideal class set. That set has two classes. Hence the space is two dimensional.

One line consists of constants. It generates the trivial norm character and is excluded from the cuspidal correspondence. Its orthogonal complement for the mass pairing is one dimensional and noncharacter. Let $\Pi$ be its automorphic constituent.

At every prime $\ell\ne11$, the algebra is split and $\Pi_\ell$ is spherical. At $11$, maximal compact invariance forces $\Pi_{11}$ to be an unramified norm character. Therefore

$$
\operatorname{JL}_{11}(\Pi_{11})
=\operatorname{St}_{11}\otimes\mu_{11}
$$

with $\mu_{11}$ unramified, and the split conductor exponent is one. At infinity the trivial compact weight transfers to discrete-series weight two. Global transfer therefore produces a weight-two cuspidal newform of level $11$.

The space $S_2(\Gamma_0(11))$ is one dimensional, so this is its normalized newform. If $B_2$ denotes the unnormalized Brandt operator at $2$, the constant line has eigenvalue $2+1=3$. The cuspidal line has the modular eigenvalue $a_2=-2$. Thus

$$
\det(X-B_2)=(X-3)(X+2).
$$

This calculation is a complete finite shadow of the transfer: the Eisenstein-shaped constant eigenline is removed, and the remaining Brandt eigenvalue is the good-prime Hecke eigenvalue of the level-$11$ newform.

### 16.2 The Hurwitz algebra and an empty cuspidal image

Let $D/\mathbf Q$ be ramified at $2$ and $\infty$, and use the Hurwitz maximal order. Its ideal class set has one element. In trivial weight and maximal level, the quaternionic space is one dimensional and consists entirely of constants.

There is therefore no noncharacter constituent to transfer. On the split side this predicts no weight-two cusp form of level $2$, exactly as the newform dimension shows. A naive statement transferring every quaternionic automorphic representation would incorrectly turn the constant function into a cusp form. The norm-character exception prevents that error.

At the local level the trivial representation of $D_2^\times$ still transfers to $\operatorname{St}_2$, and the trivial compact real type still transfers to weight two discrete series. The failure is purely global: their formal tensor, with trivial one-dimensional components at every odd prime, is not cuspidal automorphic.

### 16.3 The image condition is real

Keep the algebra ramified at $11$ and $\infty$. Consider the discriminant modular form

$$
\Delta(q)=q\prod_{n\ge1}(1-q^n)^{24},
$$

viewed through its cuspidal automorphic representation of level one and weight twelve. Its component at $11$ is unramified spherical, hence an unramified principal-series representation. It is not discrete series.

Therefore $\Delta$ is not in the image of global transfer from this $D$, even though:

- its real component is discrete series and so has an archimedean quaternionic partner;
- its Hecke operators away from $11$ make sense on both kinds of spaces;
- its central character is compatible with the trivial character.

The single local failure at $11$ is decisive. There is no representation of the division group $D_{11}^\times$ whose local transfer is an unramified principal series. Good-place eigenvalues and archimedean weight cannot compensate for a missing ramified local preimage.

### 16.4 A local level calculation

Let $D/\mathbf Q$ be definite and ramified at a finite prime $p$. Suppose a noncharacter automorphic representation $\Pi$ has a higher-dimensional local factor at $p$ with

$$
c_{D_p}(\Pi_p)=2.
$$

Then $\Pi_p$ is fixed by $U_{D_p}^2$ and not by $U_{D_p}^1$. Its transfer is supercuspidal of conductor exponent

$$
a(\pi_p)=3.
$$

At its new level, $\pi_p^{K_1(p^3)}$ is one dimensional. If the other finite components are unramified, the global split conductor is $p^3$, not $p$ and not $p^2$.

At the deeper split level $p^5$, the same representation contributes

$$
5-3+1=3
$$

oldvectors. On the division side every $U_{D_p}^m$ with $m\ge2$ fixes the entire $\Pi_p$, so deeper normal level does not create an analogous linear growth. This example shows why equality of automorphic multiplicity and equality of Hecke eigensystems do not imply equality of fixed-space dimensions.

## 17. Trace formulas and Brandt matrices

### 17.1 The finite geometric shadow

Assume $F$ is totally real and $D$ totally definite. At compact open level $U$ the finite double-coset set

$$
X_U=D^\times(F)\backslash D^\times(\mathbf A_f)/U
$$

has representatives $g_1,\ldots,g_h$. A Hecke double coset $UaU=\coprod_ra_rU$ acts by the finite correspondence

$$
g_ia_r=\gamma_{i,r}g_{j(i,r)}u_{i,r}.
$$

The resulting block matrix is a Brandt matrix. Its trace counts fixed transitions, weighted by coefficient traces and stabilizer masses.

The compact automorphic kernel gives the same count in invariant language. A fixed transition supplies a rational element $\gamma_{i,r}$ conjugate into the support of the test function. Grouping fixed transitions by the rational conjugacy class of $\gamma_{i,r}$ produces the geometric expansion. Thus

$$
\text{Brandt fixed points}
\longleftrightarrow
\text{rational conjugacy classes}
\longleftrightarrow
\text{orbital integrals}.
$$

This is not an analogy. It is the same trace evaluated before and after grouping a finite sum.

### 17.2 A worked spectral reading of a Brandt operator

Return to the discriminant-$11$ two-class space. Let $B_\ell$ be the Brandt operator for a prime $\ell\ne11$. The row degree is $\ell+1$, so the constant vector has eigenvalue $\ell+1$. The mass pairing makes the nonconstant line its orthogonal complement. Write its eigenvalue as $a_\ell$.

Spectrally,

$$
\operatorname{tr}(B_\ell)=(\ell+1)+a_\ell.
$$

Geometrically, the same trace is a weighted count of elements of norm $\ell$ that carry an ideal class to itself. Transfer identifies the nonconstant eigenvalue with the $T_\ell$ eigenvalue of the level-$11$ newform. For $\ell=2$ the eigenvalues are $3$ and $-2$; hence the geometric fixed-point count, after stabilizer weighting, has trace $1$.

The calculation illustrates the roles of the two spectral pieces. The degree eigenvalue belongs to the norm-character block and has Eisenstein growth. The other eigenvalue belongs to the noncharacter block and transfers cuspidally. Removing the constant line is the finite matrix version of restricting the compact trace formula to $L^2_0$.

### 17.3 What the finite picture proves and what it does not

Brandt matrices give explicit Hecke traces, integral lattices, and computable eigensystems. Their simultaneous eigenspaces reconstruct quaternionic automorphic constituents, and global Jacquet--Langlands transports the noncharacter systems to split cusp forms.

The finite matrices alone do not prove the global correspondence. Their entries do not display the continuous spectrum that must be removed on $\mathrm{GL}_2$, nor do they prove that a formal list of good-prime eigenvalues occurs cuspidally. The trace-formula comparison supplies that existence theorem.

Conversely, the abstract correspondence does not replace the finite picture. Brandt matrices record integral structures, congruences, and stabilizer denominators that are invisible in an isomorphism class over $\mathbf C$. Later arithmetic arguments use the two viewpoints together: finite quaternionic modules for calculation and control, split automorphic representations for global operations.

No representation of a Galois group is needed for this bridge. The characteristic polynomials in this chapter are Hecke and conjugacy polynomials; their interpretation through arithmetic geometry belongs later.

## 18. The transfer dictionary

### 18.1 The place-by-place table

For a noncharacter automorphic $\Pi$ and $\pi=\operatorname{JL}_D(\Pi)$, the usable local dictionary is:

| place and quaternionic component | split component | level or weight effect |
|---|---|---|
| $v\notin R$, spherical | the same spherical representation | identical $T_v,S_v$ and Satake polynomial |
| $v\notin R$, ramified | the same local representation | identical conductor and local type |
| $v\in R_f$, unramified norm character $\mu_v\circ\operatorname{Nrd}$ | $\operatorname{St}_v\otimes\mu_v$ | exponent $0\mapsto1$ |
| $v\in R_f$, ramified norm character | ramified Steinberg twist | exponent $2a(\mu_v)$ on both prepared scales |
| $v\in R_f$, higher dimensional | supercuspidal local transfer | exponent $c_D(\Pi_v)+1$ |
| real $v\in R$, compact highest degree $n_v$ | real discrete series | minimal weight $n_v+2$, same center |
| real or complex $v\notin R$ | the same representation | no change |

In every row, central characters, contragredients, determinant/norm twists, and local $L$- and epsilon factors are compatible. At finite ramified places formal degrees agree for the compatible quotient measures of Section 11.3. At ramified places the character identity has sign $-1$; over all ramified places the product sign is $+1$.

### 18.2 A reusable global theorem

The correspondence can be applied through the following checklist.

1. Verify that the quaternionic constituent is not one dimensional.
2. Record the full ramification set $R$, including infinity.
3. At $v\notin R$, retain the local component unchanged.
4. At every $v\in R$, apply local Jacquet--Langlands; the output must be discrete series.
5. Form the global conductor using the exact local exponent, inserting the $0\mapsto1$ correction for unramified norm components.
6. Transfer the archimedean compact highest weight to discrete-series lowest weight with the action-convention dual included.
7. Retain the same global central character and good-place Hecke polynomials.
8. Use strong multiplicity one to identify the resulting cusp representation from almost-all Hecke data.

In the reverse direction, begin with a cuspidal $\pi$ and check discreteness at **every** place of $R$. Only then apply the local inverse correspondence. The trace formula guarantees that the resulting tensor is an automorphic noncharacter representation of $D^\times(\mathbf A)$.

### 18.3 Inputs for later applications

The output needed downstream is now precise.

- A quaternionic Hecke eigensystem away from the bad set determines one cuspidal $\mathrm{GL}_2$ representation after the character block is removed.
- Its local components at ramified places are known, not guessed from conductor: norm characters become Steinberg twists and higher-dimensional components become supercuspidals.
- The finite conductor, bad-place newness, central character, twists, dual, local factors, and compatibly normalized formal degrees obey the exact local dictionary, with the explicit $0\mapsto1$ conductor shift at an unramified norm component.
- Algebraic compact weights become cohomological discrete-series weights, and algebraic Galois conjugation of coefficients commutes with transfer.
- Multiplicity is one on both sides, while fixed-level vector multiplicities remain governed by their different local towers.

These facts are exactly what is needed before one performs operations on the split representation or inserts the result into a modularity-lifting argument. This book does not construct automorphic induction or base change; those are separate global transfers with their own image and descent conditions. It also does not attach Galois representations to the Hecke system. Here the endpoint is the automorphic representation and its complete local dictionary.

### 18.4 Conclusion

Global Jacquet--Langlands begins with a local geometric coincidence. A regular quaternion generates a quadratic field, and the same polynomial generates an elliptic matrix class. At every ramified place the division algebra retains exactly the elliptic classes and discards the split ones. Matching orbital integrals with transfer factor $+1$ turns this coincidence into a product of local identities.

The global trace formula supplies what local correspondence cannot. Compactness makes the quaternionic trace a sum over a discrete spectrum and quadratic-field conjugacy classes. A cuspidal transfer function makes the split trace equally simple: induced spectrum, unipotent terms, split tori, and quadratic fields that fail to embed all acquire a zero local factor. The surviving centralizers are literally the same tori with the same Tamagawa measures. Geometric traces therefore agree term by term.

On the spectral side every ramified local transfer contributes a minus sign. Global reciprocity makes the number of ramified places even, so the signs multiply to one. Varying test functions then isolates representations, proves existence, recovers every local component, and preserves multiplicity. Strong multiplicity one turns agreement away from finitely many places into global uniqueness and makes the transfer detectable by good Hecke eigenvalues.

The exceptional character spectrum reveals the boundary of the theorem. A norm character has legitimate local Steinberg transfers at division places, but its almost-everywhere one-dimensional tensor cannot be cuspidal. Removing that spectrum on the compact side is the counterpart of removing the Eisenstein boundary on the split side. Once this distinction is respected, the result is exact: noncharacter quaternionic automorphic representations correspond bijectively to cusp representations that are discrete series at every ramified place.

The resulting dictionary is both analytic and arithmetic. It preserves central characters, twists, contragredients, local factors, root numbers, compatibly normalized formal degrees, good Hecke polynomials, coefficient fields, and algebraic conjugation. It changes levels by explicit local conductor rules and turns compact archimedean weights into discrete-series weights shifted by two. Finite Brandt matrices and the adelic trace formula are two resolutions of the same operator, so a computable quaternionic eigensystem becomes a unique split cuspidal representation without invoking any later arithmetic realization. That is the durable content of global Jacquet--Langlands.
