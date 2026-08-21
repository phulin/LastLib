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
   - [The compact one-split theorem](#95-the-compact-one-split-theorem)
   - [Construction, uniqueness, and exact image](#96-construction-uniqueness-and-exact-image)
10. [Norm characters and the exceptional spectrum](#10-norm-characters-and-the-exceptional-spectrum)
    - [Why global characters must be separated](#101-why-global-characters-must-be-separated)
    - [Their local Steinberg transfers](#102-their-local-steinberg-transfers)
    - [How the trace comparison accounts for them](#103-how-the-trace-comparison-accounts-for-them)
    - [A counterexample to naive globalization](#104-a-counterexample-to-naive-globalization)
11. [Structural compatibilities](#11-structural-compatibilities)
    - [Central characters, twists, and contragredients](#111-central-characters-twists-and-contragredients)
    - [Conductors and exact local shifts](#112-conductors-and-exact-local-shifts)
    - [Local and global factors](#113-local-and-global-factors)
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

The answer is subtler than replacing each local factor independently. At a ramified finite place, Book 80 gives the correspondence in the range needed here: norm characters, hence special representations on the split side, and the selected depth-zero or tame positive-depth dihedral representations. Primitive wild packets and ramified dyadic positive-depth packets are not in that local theorem and are not smuggled into the global statement. At a split place there is nothing to transfer. For a packet in this selected range one can therefore write down a formal tensor

$$
\bigotimes_v'\operatorname{JL}_v(\Pi_v).
$$

But a restricted tensor of admissible local representations need not occur automorphically. Automorphy is a global condition, and cuspidality is even more global: it is expressed by an integral over $F\backslash\mathbf A_F$, not by a condition on each component. The main work of this book is to prove automorphy and exactness in two named compact ranges. The first is the totally definite selected weight-two range. The second is the one-split curve range needed by the FLT route: $F$ has degree at least two, the quaternion algebra is split at exactly one real place, and its finite ramification set has the parity complementary to $[F:\mathbf Q]-1$ and consists of places where the split packet is special or selected tame dihedral. Thus the finite set is odd and nonempty in even degree, while in odd degree it is even and may be empty. In that second range the theorem constructs the inverse quaternionic packet from the split cusp form.

The proof compares two trace formulas. On $D^\times$, compactness modulo the center makes the kernel and its trace completely discrete. On $\mathrm{GL}_2$, the quotient has cusps, so continuous and parabolic terms ordinarily appear. Books 100--101 prove a one-place simple formula when a strongly cuspidal real factor also satisfies their global kernel-admissibility estimate. Their theorem does not automatically include a low-weight matrix-coefficient pseudo-coefficient merely because it is valid locally; the compact-mod-center Euler--Poincare projector used in Book 103, Chapter 12 is a separate admissible choice. For parallel weight two, the comparison used here is Book 96's character-clean two-place identity: two ramified transfer factors have zero induced trace and zero split regular orbital integrals, so differentiated continuous and boundary terms cancel place by place. One factor is the cuspidal archimedean weight-two projector. On the compact side the same identity removes the norm-character trace. Book 103's singular-germ calculation and Book 96's finite interpolation then normalize the scalar distribution. After that correction, matching regular orbital integrals forces the desired cuspidal representation to exist.

This route explains more than existence. It shows why the image condition is discrete series at every ramified place, why the local minus signs disappear globally, why Hecke eigenvalues are unchanged at good places, and why the quaternionic character subspace must be removed before claiming a cuspidal bijection. The one-split proof uses only compact automorphic traces, local transfer, and the split trace formula. It does not use the cohomology of a Shimura curve, and it therefore supplies rather than assumes the automorphic packet later used on that curve.

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

Changing $\iota_v$ conjugates it and hence changes neither local representation classes nor orbital integrals. At finite $v\in R$, write $\operatorname{JL}_v$ for the selected local correspondence of Book 80, with the archimedean correspondence constructed from the real discrete-series character formula at a ramified real place.

The trace-formula argument will be used only in the following two ranges.

1. **Totally definite range.** The field $F$ is totally real, $D$ is ramified at every real place, and every finite component at a place of $R_f$ lies in the selected local range.
2. **Compact one-split range.** The degree $d=[F:\mathbf Q]$ is at least two, a real place $\tau _0$ is fixed, $D$ is split at $\tau _0$, ramified at every other real place, and

   $$
   R_f=W
   $$

   is a finite set satisfying

   $$
   (d-1)+|W|\equiv0\pmod2.
   $$

   At every $w\in W$ the local component lies in the selected special or tame-dihedral range. When $d$ is even, $W$ is necessarily odd and nonempty. When $d$ is odd, $W$ is even and may be empty.

In the first range the full ramification set is nonempty and even, hence has at least two members. In the second range

$$
|R|=(d-1)+|W|
$$

is even and at least two. If $d=2$, one ramified real place and one member of $W$ are distinct; if $d\ge3$, two ramified real places are distinct. In both ranges $D$ is not the split matrix algebra, so a quaternion algebra of degree two is a division algebra. Book 96 then gives

$$
[G]=Z(\mathbf A)G(F)\backslash G(\mathbf A)
$$

as a compact quotient. These common facts, rather than total definiteness by itself, are what the comparison uses: two ramified trace-cuspidal factors, at least one of them a real weight-two projector, and a discrete compact quaternionic spectrum. No other mixed archimedean signature is claimed. The split case $D=M_2(F)$ has $R=\varnothing$ and the correspondence is the identity; it contains no trace-formula comparison and will be understood as the degenerate boundary case.

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

All other irreducible automorphic representations will be called **noncharacters**. A noncharacter is **selected** if, at every finite $v\in R$, its local factor is a norm character or one of the depth-zero or tame positive-depth dihedral factors covered by Book 80. The theorem will give a bijection between selected noncharacters on $G$ and cuspidal representations on $G^*$ whose ramified finite factors are the corresponding selected special or dihedral discrete series and whose ramified real factors have the prescribed algebraic discrete-series type. Parallel weight two is obtained from the trivial compact type at every ramified real place and, in the one-split range, from the unchanged minimal weight-two discrete series at $\tau _0$. Norm characters are genuinely exceptional and will be treated in Chapter 10.

We use $\Pi$ for a quaternionic representation and $\pi$ for a representation of $G^*(\mathbf A)$. Their local components are $\Pi_v$ and $\pi_v$. At a split place, the assertion $\pi_v\cong\Pi_v$ always means that $\Pi_v$ has been transported through $\iota_v$.

Trace comparison is carried out one central character and one infinity type at a time. Fix a unitary Hecke character $\omega$. At a ramified real place $v$, fix an irreducible algebraic automorphic type $\tau_v$ of $D_v^\times$ whose scalar action is $\omega_v$, and write $\tau_v^*=\operatorname{JL}_v(\tau_v)$ for the corresponding full-group discrete series. In parallel weight two, $\tau_v$ is trivial on the norm-one subgroup; a common norm twist accounts for the scalar action. In the compact one-split range, put

$$
\tau_{\tau _0}=\tau_{\tau _0}^*=D_{2,\omega_{\tau _0}},
$$

the full-group minimal weight-two discrete series under the fixed splitting $D_{\tau _0}^\times\simeq\mathrm{GL}_2(\mathbf R)$. Thus local transfer is the identity at the active real place and is the compact-to-discrete correspondence at every other real place. The algebraic, possibly nonunitary normalization is recovered after the Hilbert-space argument by undoing the common real norm twist.

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

Ordinary noncentral regular semisimple conjugacy classes on either side are determined by this polynomial. We say that $\gamma$ and $\gamma^*$ match if $P_\gamma=P_{\gamma^*}$. Multiplying both representatives by $z\in F^\times$ preserves matching and passes to the projective rational classes that occur in the fixed-central-character kernels. The common algebra

$$
E=F[X]/(P_\gamma)
$$

is then a quadratic field whenever $\gamma$ lies in a division quaternion algebra. Their centralizers are the same torus:

$$
G_\gamma\cong\operatorname{Res}_{E/F}\mathbf G_m
\cong G^*_{\gamma^*}.
$$

The equality of connected centralizers is the reason the global volume coefficient can match. Equality merely of traces and norms without compatible torus measures would not suffice.

Projective orbit unfolding has one additional finite coefficient. Let $\overline G=G/Z$, and for a regular $\gamma$ define its rational projective stabilizer by

$$
C_\gamma(F)=
\{\bar x\in\overline G(F):x^{-1}\gamma x\in F^\times\gamma\}.
$$

The connected subgroup is $\overline G_\gamma(F)=G_\gamma(F)/Z(F)$. If $\operatorname{Trd}(\gamma)\ne0$, taking traces in $x^{-1}\gamma x=z\gamma$ forces $z=1$. If $\operatorname{Trd}(\gamma)=0$, determinants force $z=\pm1$, and Skolem--Noether supplies an element which realizes the nontrivial automorphism of $F[\gamma]$ and sends $\gamma$ to $-\gamma$. Therefore

$$\kappa(\gamma):=[C_\gamma(F):\overline G_\gamma(F)]^{-1}=

\begin{cases}
\frac12,&\operatorname{Trd}(\gamma)=0,\\
1,&\operatorname{Trd}(\gamma)\ne0.
\end{cases}
\tag{2.1}
$$

The identical proof on $G^*$ uses the same trace. Hence matching classes have the same $\kappa$. This factor belongs to rational projective orbit unfolding, not to the local orbital integral.

Scalar classes require separate language. After quotienting by the full adelic center, all rational scalar elements represent the identity class. Their contribution is the volume of the projective automorphic quotient times the test function's central germ. Regular orbital integrals do not determine the value of a function at a scalar, so the singular part of local transfer must also be normalized. Book 103 separates the zero and regular-nilpotent germs and supplies the triangular correction used in Section 7.3.

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
\operatorname{vol}\bigl(PG(F)\backslash PG(\mathbf A)\bigr)
=\operatorname{vol}\bigl(PG^*(F)\backslash PG^*(\mathbf A)\bigr)
=2
$$

for the compatible Tamagawa measures. Equality of these Tamagawa numbers identifies the volume factor in the two central terms. It does not identify the local point values of transferred functions; that separate singular-germ normalization is carried out in Section 7.3. One could divide both global measures by two; every volume coefficient on both sides would change together.

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

Assume $D$ is division. Let $f'$ be locally constant and compactly supported modulo the center at the finite places, smooth and compact-finite at infinity, and transforming by $\omega^{-1}$. At a split archimedean place require either compact support modulo the center or the rapid-decay/smoothing class of Book 96, Proposition 7.2: after the common smoothing multiplier, the function and every required derivative decrease faster than every prescribed power of a projective norm. In the totally definite range the projective archimedean factors are compact, so this condition is automatic. Define

$$
K_{f'}(x,y)=
\sum_{\gamma\in Z(F)\backslash G(F)}
f'(x^{-1}\gamma y).
$$

For compactly supported archimedean factors the sum is locally finite. For factors in the second class it is absolutely and locally uniformly convergent, with all required derivatives, by the lattice count and rapid-decay estimate in Book 96, Proposition 7.2. It descends in both variables to $[G]$. Right convolution is

$$
(R(f')\phi)(x)=
\int_{Z(\mathbf A)\backslash G(\mathbf A)}
f'(g)\phi(xg)\,dg,
$$

and the kernel identity gives

$$
(R(f')\phi)(x)=\int_{[G]}K_{f'}(x,y)\phi(y)\,dy.
$$

The resulting smooth kernel on the compact quotient makes $R(f')$ trace class. There is no truncation and no continuous spectrum. Compactness alone does not make an arbitrary nonsmoothing operator trace class; the stated local smoothness and decay are part of the test-function hypothesis. This is the analytic advantage of the inner form.

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

At fixed finite level, fixed archimedean compact types, and bounded infinitesimal character, only finitely many summands contribute. In the theorem ranges the local projectors select the required weight-two factors inside such a window. Book 96 proves $m_D(\Pi)=1$, but it is useful to retain the multiplicity symbol during comparison: doing so shows exactly where multiplicity preservation enters.

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

Group the rational elements by conjugacy class in $Z(F)\backslash G(F)$. One obtains

$$
I_D(f')=
\sum_{[\gamma]}
\kappa(\gamma)a_D(\gamma)O_\gamma(f'),
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

The same connected-centralizer measure occurs in both expressions. For regular noncentral $\gamma$, the centralizer is $E^\times$ for the quadratic field $E=F(\gamma)$. For the central class it is all of $G$. We put $\kappa=1$ on that class.

**Proof strategy.** Absolute convergence allows the sum and integral to be interchanged. Each projective orbit is unfolded against its full rational projective stabilizer. Passing to the connected centralizer contributes $\kappa(\gamma)$, and Weil's quotient formula then separates its adelic volume from the orbital integral.

**Proof.** Insert the kernel on the diagonal and integrate. Local finiteness in the compact-support case, and the lattice-count and rapid-decay estimate just cited in the smoothed case, give absolute convergence uniformly on the compact quotient $[G]$. For a fixed projective class, the rational orbit is $C_\gamma(F)\backslash\overline G(F)$. The summand descends to this quotient because replacing $\gamma$ by $z\gamma$ for $z\in F^\times$ multiplies it by $\omega(z)^{-1}=1$. Replacing $C_\gamma(F)$ by its connected subgroup $\overline G_\gamma(F)$ is a cover of degree $\kappa(\gamma)^{-1}$. Weil's formula along $\overline G_\gamma(\mathbf A)$ then gives $\kappa(\gamma)a_D(\gamma)O_\gamma(f')$. Summing over projective conjugacy classes proves the formula. $\square$

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

Books 100--101 prove a smaller formula under a precise hypothesis: one real local factor is **strongly cuspidal**, meaning that its two-sided parabolic transform vanishes, and it belongs to their kernel-admissible global test class. Its convolution operator is then zero on every representation induced from the Borel. This kills the continuous channel, while the zero parabolic transform kills residual characters directly. The geometric formula consequently retains only the central and elliptic distributions.

The local discrete-series projector transferred from a compact real factor is strongly cuspidal and isolates the required infinity type. Book 100's matrix-coefficient construction has a separate global analytic condition: its fixed kernel estimate is automatic only in sufficiently high lowest weight and must otherwise be checked independently. The compact-mod-center Euler--Poincare projector used in Book 103, Chapter 12 does satisfy the test class of Book 101, so no failure of the one-place formula at weight two is asserted. The proof here uses instead the comparison already packaged in Book 96, Proposition 7.2, because it simultaneously supplies the two-place boundary cancellation, norm-character removal, and scalar-germ interpolation. It starts from two ramified factors whose traces on normalized principal series and whose split regular orbital integrals vanish. In each of the two named ranges of Section 1.2, $|R|\ge2$ and at least one member of $R$ is real. Hence one factor can be the archimedean weight-two projector and another ramified place supplies the second zero. In the compact one-split range take the second place in $W$ when $d=2$, and take a second ramified real place when $d\ge3$ and $W$ is empty.

### 5.2 Cuspidal local test functions

For a local field $K$, let $B=TN$ be the upper Borel of $\mathrm{GL}_2(K)$ and let $h\in C_c^\infty(\mathrm{GL}_2(K))$ modulo the center. Its normalized constant term is

$$
h_B(t)=\delta_B(t)^{1/2}
\int_{N(K)}h(tn)\,dn.
$$

For the one-place trace formula one uses the stronger conjugation-stable condition that

$$
\int_{N(K)}h(x^{-1}tnx)\,dn=0
$$

for every $x\in\mathrm{GL}_2(K)$ and $t\in T(K)$, with the evident archimedean smooth analogue, and require the opposite-Borel transform to vanish as well. We call such an $h$ **strongly cuspidal**. It acts by zero on every normalized representation induced from $B$; mere vanishing of trace is weaker and cannot kill a logarithmic derivative at the same place. In rank one this is also reflected geometrically by vanishing split regular orbital integrals together with the appropriate singular-germ condition.

The real discrete-series pseudo-coefficients used here are canonical local examples. They isolate the selected discrete series and act by zero on principal series and their one-dimensional quotients. At finite division places the Euler--Poincare functions of Book 103 provide regular orbital matching and trace zero on full normalized principal series. In the two-place formula, trace-level vanishing is enough: each differentiated global term has its derivative at at most one place, so the undifferentiated zero trace at the other selected place kills it.

The converse warning matters: support on matrices whose characteristic polynomial happens to be irreducible does not by itself imply vanishing constant term. Cuspidality is a distributional statement stable under conjugation and passage through the singular boundary.

### 5.3 The simple trace identity

There are two proved forms of the simple identity, and their hypotheses must not be conflated. Let $f=\bigotimes_vf_v$ be a global test function on $G^*(\mathbf A)$ with fixed central character. If $f_{v_0}$ is strongly cuspidal at a real place and satisfies the kernel-admissibility estimate of Books 100--101, their one-place formula is

$$
I_{G^*}(f)
:=\sum_{\pi\ \mathrm{cuspidal}}
m_{G^*}(\pi)\operatorname{tr}\pi(f)
=I_{\mathrm{cent}}(f)+I_{\mathrm{ell}}(f).
$$

**Proof strategy.** Insert the truncation used in Book 101. Its parabolic main term factors through the two-sided constant term, while the continuous channel factors through the induced local operator. Strong cuspidality kills both, and the zero parabolic transform kills residual characters. The remaining elliptic series is handled by Book 101's absolute-convergence estimates.

**Proof.** The kernel theorem gives a trace-class operator and an absolutely convergent cuspidal spectral trace. At $v_0$, the induced operator is zero. Tensor factorization therefore kills every Eisenstein wave packet, and direct integration of a residual determinant character through the parabolic transform gives zero. On the geometric side, stable-line unfolding expresses split regular, unipotent, and weighted terms through the same two-sided parabolic transform; they vanish. The central class remains, and elliptic orbit unfolding gives the absolutely convergent sum $I_{\mathrm{ell}}(f)$. This proves the identity. $\square$

For the weight-two theorem, choose two distinct ramified places $a,b\in R$. At each, use a transfer with zero split regular orbital integrals and trace zero on every full normalized principal series. Book 96, Proposition 7.2 proves that, after residual characters are displayed separately, the same identity holds. That proposition uses the signed orbital convention; multiplying the split function by $-1$ at every place of $R$ gives the signless convention of Chapter 6 and changes the global tensor by $(-1)^{|R|}=1$. Each logarithmically differentiated continuous term differentiates an intertwiner at only one place. If that place is $a$, the undifferentiated trace at $b$ is zero; if it is $b$, the trace at $a$ is zero; and if it is elsewhere, both vanish. The split, unipotent, and weighted geometric boundary terms have the identical two-place cancellation. The convergence estimates proved there justify removal of truncation. This is the form used from Chapter 7 onward.

Notice the asymmetry with the compact inner form: norm characters occur in its discrete trace. In the one-place formula the split residual characters have already vanished. In the two-place formula residual determinant characters and quaternionic norm characters first have equal traces, after multiplication of all ramified local signs, and the character-clean condition then kills both. Either way, a cuspidal correspondence is obtained only after the character spectrum has been removed.

### 5.4 Why unwanted terms vanish

It is useful to separate three mechanisms that are often compressed into the word “cuspidal.”

- In the one-place formula, split regular classes, unipotent and weighted terms, and the continuous spectrum vanish through the strongly cuspidal factor; residual characters vanish through its zero parabolic transform.
- In the weight-two two-place formula, each split or unipotent boundary term and each differentiated continuous term has an undifferentiated zero orbital or trace factor at one of the two selected places.
- Residual determinant characters are retained long enough to be matched with norm characters, then both are annihilated by character-clean interpolation.

These mechanisms lead to the same simple distribution, but they use different hypotheses and occur on different sides of the trace formula.

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

Book 103 uses the signed convention $O_g=-O_d$. In this book we multiply every split transfer at a division place by $-1$ and use the equivalent signless convention

$$
O_g(f_v)=O_d(f_v')
$$

on matching elliptic classes and $O_g(f_v)=0$ on split regular classes. No sign appears. The Weyl discriminant

$$
\left|\frac{\operatorname{tr}(g)^2-4\det(g)}{\det(g)}\right|_v
$$

is equal on matching classes, so the statement is unchanged if normalized orbital integrals are used consistently.

Book 103 constructs these functions for the unit, Iwahori, selected congruence, special, and tame dihedral types and treats the singular germs separately. The assertion is stronger than matching on a collection of conveniently regular compact sets and weaker than pointwise equality of functions, which would not be canonical. Central point values are not determined by regular orbital transfer and will be normalized in Chapter 7.

The corresponding trace relation is

$$
\operatorname{tr}\operatorname{JL}_v(\rho)(f_v)
=-\operatorname{tr}\rho(f_v').
$$

This relation holds for every $\rho$ in Book 80's selected special or dihedral range, including division norm characters. No assertion is made here for primitive wild or excluded dyadic packets. It is the local representation-theoretic input used in the global trace comparison.

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

This is an honest ordinary rational-class bijection in degree two, compatible with simultaneous scalar multiplication and hence with the projective classes in the kernels. There is no additional sum over ordinary rational classes inside a stable class because characteristic polynomial already determines conjugacy for regular elements in both algebras. On the trace-zero projective fiber the orbit has the extra order-two stabilizer of (2.1), with the same reciprocal factor on both sides.

### 7.2 Classes that do not come from the quaternion algebra

The split geometric expansion contains more rational semisimple classes than the quaternionic expansion. Each extra class vanishes for a visible local reason.

If the polynomial splits over $F$, it splits over every $F_v$. At any chosen $v\in R$, the local orbital integral of the elliptic transfer function is zero. Thus every global split regular term vanishes.

If the polynomial defines a quadratic field $E/F$ that does not embed in $D$, the embedding criterion gives a ramified place $v\in R$ that splits in $E$. The local matrix is split regular there, and again its orbital integral is zero.

Unipotent terms have no division-side counterpart. In the one-place formula they factor through the strongly cuspidal parabolic transform. In the weight-two formula the two-place cancellation of Section 5.3 kills them, as well as the weighted split-torus terms. Zero regular orbital integrals at one place alone would not justify this conclusion.

This reasoning is stronger than saying that “only elliptic terms survive.” A globally elliptic class may still be locally split at a ramified finite place and must be removed. The exact survivor condition is ellipticity at **every** ramified place.

### 7.3 Equality term by term

For matching regular classes $\gamma\leftrightarrow\gamma^*$, local transfer gives

$$
O_{\gamma^*}(f)=O_\gamma(f').
$$

Their volume and projective-stabilizer coefficients are equal because their rational and adelic connected centralizers are the same torus with the same measure and their traces agree:

$$
a_{G^*}(\gamma^*)
=\operatorname{vol}\bigl(Z(\mathbf A)E^\times\backslash\mathbf A_E^\times\bigr)
=a_D(\gamma).
$$

Moreover $\kappa(\gamma^*)=\kappa(\gamma)$ by (2.1). Thus the complete coefficients $\kappa a$ agree, including the trace-zero fiber; omitting $\kappa=1/2$ there would double both individual trace-formula terms.

The displayed quotient suppresses the standard identification of $E^\times$ with $G_\gamma(F)$ and the central embedding of $\mathbf A^\times$. Its finite volume is a torus Tamagawa volume.

The central class is different. Book 103 proves explicitly that regular transfer does not determine the central value: for its signed finite Euler function, the split value at $1$ is $q-1$ while the division unit has value $1$. After the sign change of Section 6.1 the split value is $1-q$; in either convention it is not forced to equal the division value. Book 103 also proves an important restriction: one cannot change a single function's central value while keeping all its regular orbital integrals fixed. A matching bump changes the division and split functions together near the scalar, preserving equality of their regular orbital integrals rather than preserving their former numerical values. The two rank-two germs form a triangular system, so this paired change controls the scalar distribution without creating a regular-nilpotent mismatch.

At fixed central character, level, infinity type, and spectral window, only finitely many norm characters occur. Book 96, Proposition 7.2 proves the required interpolation statement before global Jacquet--Langlands: local character distributions are linearly independent, the scalar point mass is independent of their locally integrable distributions, and regular slice functions together with one matching central bump solve the resulting finite triangular system. Consequently one may prescribe finitely many noncharacter trace coordinates, make every norm-character coordinate zero, and normalize the scalar distribution while retaining regular matching. We call such a test **character-clean**. This is not circular: the proposition uses compactness, local orbital transfer, and the split trace formula, but assumes no representation correspondence.

Transfer each tensor summand locally. The interpolation theorem just cited, using Book 103's matching bump, adjusts the split and division functions simultaneously near the singular fiber, retains their cross-inner-form regular and selected trace matching, and permits the scalar terms to be normalized by

$$
I_{G^*,\mathrm{cent}}(f)=I_{D,\mathrm{cent}}(f')
\tag{7.1}
$$

without changing the selected regular transfer identities. In the one-place version this removes the compact norm characters left after residual split characters vanish. In the weight-two two-place version, the residual determinant trace equals the corresponding norm-character trace before subtraction, and the character-clean condition kills both.

**Theorem 7.1 (character-clean geometric comparison).** For selected globally matching functions $(f,f')$ with either a kernel-admissible strongly cuspidal real factor or the two trace-cuspidal ramified factors of Section 5.3, a character-clean quaternionic test, and central normalization (7.1),

$$
I_{G^*,\mathrm{geom}}(f)
=I_{D,\mathrm{geom}}(f').
$$

**Proof strategy.** Pair the regular classes through their common polynomial, kill every unmatched split class locally, and then use (7.1) for the only distribution not determined by regular transfer.

**Proof.** Proposition 2.1 pairs the regular classes that can contribute. Equality of their centralizer volumes and products of local orbital integrals gives equality term by term. Section 7.2 kills every remaining split semisimple, unipotent, and parabolic term. The singular-germ calculation of Book 103 shows that no regular nilpotent distribution remains. Equation (7.1) compares the scalar terms. Absolute convergence of the compact expansion and of the applicable split elliptic expansion permits the reindexing. $\square$

### 7.4 The global trace identity

Combining the compact trace formula, the cuspidal split trace formula, and Theorem 7.1 gives directly

$$\boxed{\sum_{\pi\ \mathrm{cuspidal}}m_{G^*}(\pi)\operatorname{tr}\pi(f)=

\sum_{\Pi\ \mathrm{noncharacter}}
m_D(\Pi)\operatorname{tr}\Pi(f').}
$$

The multiplicities have deliberately been retained. The right sum may be written over noncharacters because the character-clean test has zero trace on every norm character in the block. There is no residual character on the left. This is a distribution identity on a separating family of tests, not yet a termwise bijection; extracting irreducible terms requires varying the local functions.

There is no uncancelled global sign. If one rewrites each ramified local trace through local Jacquet--Langlands, the sign product is $(-1)^{|R|}=1$. This agrees with the sign-free geometric comparison.

## 8. Spectral comparison and extraction

### 8.1 Factorized spectral traces

Fix a finite set $S$ containing $R$, every archimedean place, and every finite place where the central character or chosen representation is ramified. Outside $S$, use spherical unit functions except at finitely many auxiliary places where arbitrary spherical Hecke operators may be inserted. Inside $S$, use functions supported in selected Bernstein or compact-type blocks. For the weight-two comparison retain trace-cuspidal transfer factors at two ramified places, one of them archimedean.

For a constituent $\Pi$, its contribution factors as

$$
m_D(\Pi)
\prod_{v\in S}\operatorname{tr}\Pi_v(f_v')
\prod_{v\notin S}\lambda_{\Pi_v}(f_v'),
$$

where $\lambda_{\Pi_v}$ is the spherical Hecke character. The split contribution has the analogous form. Since fixed-type spaces are finite dimensional, only finitely many representations survive any such choice.

This finiteness turns the distribution identity into finite-dimensional character theory. Varying one local factor while holding the others fixed separates inequivalent local representations. Varying good-place Hecke operators separates different global cuspidal representations by strong multiplicity one.

### 8.2 Isolating one quaternionic constituent

Let $\Pi$ be a selected noncharacter automorphic representation of $G(\mathbf A)$. We show how the trace identity forces a corresponding cusp form.

**Proof strategy.** At a finite set of places choose local matrix-coefficient projectors that have nonzero trace on $\Pi_v$ and zero trace on the other local types occurring in the fixed-level space. At a ramified place use a transferred elliptic projector. Outside the set vary spherical Hecke operators. The quaternionic spectral side then has a nonzero $\Pi$ contribution. Equality of traces forces at least one cuspidal split constituent with the same good-place Hecke character.

Choose a level and archimedean type detecting $\Pi$. The resulting automorphic space is finite dimensional. Book 96, Theorem 7.3 proves, independently of global Jacquet--Langlands, that a complete good-place quaternionic Hecke character determines one global constituent. For the finite separation used here, one may equivalently list the constituents in the chosen block. If $\Pi'\not\cong\Pi$, uniqueness of restricted tensor factorization gives a place $v(\Pi')$ with $\Pi_{v(\Pi')}'\not\cong\Pi_{v(\Pi')}$. The local convolution characters of two inequivalent admissible irreducibles are distinct, so a local test function separates them. Taking the union of these finitely many places and using the interpolation clause of Book 96, Proposition 7.2 produces a finite linear combination of pure tensors whose trace is one on $\Pi$, zero on every other noncharacter constituent in the block, and zero on every norm character. At ramified finite places only selected type functions are used, so Book 103 transfers every tensor in the combination.

At a ramified real place $v_0$, use the transferred algebraic discrete-series projector. It is locally strongly cuspidal. Retain a second ramified trace-cuspidal factor in every tensor summand, as required by the proved low-weight simple identity. At the remaining separating places use local character independence, and at finite ramified places use the selected special or dihedral functions.

The quaternionic trace of this finite combination on $\Pi$ is nonzero and its trace on every other noncharacter constituent in the block is zero. Apply the character-clean identity of Section 7.4. If the split cuspidal side were empty, that identity would give zero, a contradiction. Therefore some cuspidal $\pi$ occurs. Varying the finitely many auxiliary spherical operators and using linear independence of their characters shows that it has the same spherical Hecke character as $\Pi$ at almost every split place. Hence

$$
\pi_v\cong\Pi_v.
$$

The noncharacter hypothesis is essential in the isolation step. The projector must be taken in the orthogonal complement of the global character spectrum; otherwise the elliptic relation at reducible principal series can move trace between a norm character and a special constituent without producing the desired global tensor.

### 8.3 Recovering every local component

Agreement at almost all places is not the full theorem. Let $w$ be any place.

The character-clean constraint does not prevent this variation. Hold fixed the two trace-cuspidal factors and all isolating coordinates away from $w$, and invoke the interpolation clause of Book 96, Proposition 7.2 again. If $w\in R$ is itself one of the two places, every regular transfer used while varying $f_w'$ still has zero split regular orbital integrals and trace zero on full normalized principal series, so the other selected place supplies the second zero factor. The proposition explicitly permits prescribed noncharacter local tensor coordinates while annihilating the finite norm-character list and solving the scalar equation. Thus no unproved assertion about a quotient of the local cocenter is needed.

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

The extraction may initially produce several cuspidal $\pi$ with the same almost-all spherical data. The strong multiplicity-one theorem of Book 95 says that any two are isomorphic. Thus the transfer of $\Pi$ is unique and may be denoted

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

**Theorem 9.1 (totally definite selected global Jacquet--Langlands).** Let $F$ be totally real and let $D/F$ be totally definite, with ramification set $R$. Fix $\omega$ and the compatible parallel-weight-two types $\tau_v,\tau_v^*$ as in Section 1.2. There is a unique bijection

$$
\operatorname{JL}_D:
\left\{\begin{array}{c}
\text{irreducible selected noncharacter automorphic}\\
\text{representations }\Pi\text{ of }D^\times(\mathbf A_F)\\
\text{with central character }\omega\text{ and }\Pi_v\cong\tau_v\ (v\mid\infty)
\end{array}\right\}
\xrightarrow{\sim}
\left\{\begin{array}{c}
\text{irreducible cuspidal automorphic representations }\pi\\
\text{of }\mathrm{GL}_2(\mathbf A_F)\text{ such that at finite }v\in R\\
\pi_v\text{ is selected special or dihedral, }\omega_\pi=\omega,\\
\text{and }\pi_v\cong\tau_v^*\text{ at every real }v
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

At a ramified real place, the representation of the full group $\mathrm{GL}_2(\mathbf R)$ is the discrete-series representation determined by the algebraic infinity type. Its restriction to the positive-determinant component contains the holomorphic and antiholomorphic orientations exchanged by an element of negative determinant; they are not two choices of the full local representation. For parallel weight two the quaternionic type is trivial and the split factor has minimal compact weight two. Each representation occurs with the same automorphic multiplicity. In the present groups both multiplicities are one.

If $D=M_2(F)$, no inner-form comparison is needed: global Jacquet--Langlands is, by definition, the identity on the cuspidal spectrum of $\mathrm{GL}_2(\mathbf A_F)$. This split boundary case is stated separately because the phrase “noncharacter automorphic representation of $D^\times$” would otherwise also admit noncuspidal induced representations, which are not in the source of the displayed bijection.

### 9.2 Existence and injectivity

The definite range has two edge cases worth auditing before invoking the common proof. If $[F:\mathbf Q]=1$, total definiteness contributes one ramified real place; reciprocity forces an odd nonempty finite ramification set, so a finite place supplies the second trace-cuspidal factor. If $[F:\mathbf Q]\ge2$, the real ramification set already contains two places unless the degree is one, and any additional finite ramification only enlarges the choice. Thus the assertion $|R|\ge2$ used in Chapters 5 and 8 is valid in every totally definite case covered by Theorem 9.1. The algebra is division and its quotient modulo center is compact by Book 96; no finite-class-set formula, high-weight kernel estimate, or unproved weight-two extension is being substituted for these facts.

Existence for every selected noncharacter $\Pi$ was proved by spectral extraction. The local formulas determine every component of $\pi$.

For injectivity, suppose

$$
\operatorname{JL}_D(\Pi_1)\cong
\operatorname{JL}_D(\Pi_2).
$$

At split places the local components of $\Pi_1$ and $\Pi_2$ agree. At ramified places local Jacquet--Langlands is injective, so their local components agree there as well. Hence the two restricted tensor products are isomorphic. Equivalently, strong determination on the quaternionic spectrum already identifies them from almost all split places. Thus $\Pi_1\cong\Pi_2$.

This proof uses local injectivity only after global existence. It avoids the invalid inference that two abstract restricted tensors with equal factors must both be automorphic.

### 9.3 Surjectivity onto the stated image

Let $\pi$ be cuspidal on $\mathrm{GL}_2(\mathbf A)$ and assume that at every finite $v\in R$ its factor is selected special or dihedral and that at every real $v$ it has the prescribed algebraic discrete-series type. Define candidate quaternionic factors by

$$
\Pi_v^{\mathrm{cand}}=
\begin{cases}
\pi_v,&v\notin R,\\
\operatorname{JL}_v^{-1}(\pi_v),&v\in R.
\end{cases}
$$

Use local pseudo-coefficients of $\pi_v$ at ramified places and transfer them to $D_v^\times$. At the other places use identical functions. The reverse geometric comparison is the same term-by-term identity. Isolate $\pi$ using a finite type and good-place Hecke operators. Since a cuspidal representation is not one dimensional at almost every split place, finite interpolation at split places can be chosen to retain its trace while annihilating every norm character in the fixed quaternionic block. Apply the character-clean identity of Section 7.4. The split cuspidal trace is nonzero, so the quaternionic **noncharacter** trace contains a constituent $\Pi$. Local character independence identifies every $\Pi_v$ with $\Pi_v^{\mathrm{cand}}$.

This use of the subtracted identity is essential when some $\pi_v$ is Steinberg. Its local division partner is a norm character, but the assembled global preimage must not be allowed to fall into the global norm-character spectrum. The right side has already removed that spectrum, so its nonzero trace produces a noncharacter constituent. As a consistency check, a norm-character preimage would be one dimensional at almost every split place, contradicting the local genericity of a cuspidal representation.

The hypothesis at **every** ramified place is necessary. If $\pi_v$ is principal series at even one $v\in R$, there is no local inverse transfer. Within the present dependency closure, a primitive wild or excluded ramified dyadic packet is likewise outside the theorem: it may belong to the full classical correspondence, but Book 80 and Book 103 do not construct the local character and test-function identities needed here.

### 9.4 Multiplicity preservation

Before inserting known multiplicity-one theorems, isolate a corresponding pair $(\Pi,\pi)$ on both sides and normalize the local projectors to have trace one. The global trace identity reduces to

$$
m_{G^*}(\pi)=m_D(\Pi).
$$

Thus trace comparison preserves automorphic multiplicity. Book 96 gives $m_D(\Pi)=1$, while Book 95 derives $m_{G^*}(\pi)=1$ from global Whittaker uniqueness. The equality is therefore

$$
m_D(\Pi)=m_{G^*}(\operatorname{JL}_D(\Pi))=1.
$$

This statement concerns occurrences in the automorphic spectrum. It does not say that $\dim\Pi_f^U$ equals $\dim\pi_f^K$. Fixed-vector dimensions can differ dramatically at ramified places: a division newlevel block may have dimension $\dim\Pi_v$, while the split newvector space is a line.

### 9.5 The compact one-split theorem

We now state the inverse theorem which is needed to move a split Hilbert packet onto a compact Shimura-curve inner form. Its hypotheses deliberately describe only one archimedean signature.

**Theorem 9.2 (compact one-split inverse Jacquet--Langlands).** Let $F$ be totally real of degree $d\ge2$, fix a real place $\tau _0$, and let $W$ be a finite set of finite places such that $(d-1)+|W|$ is even. Let $B/F$ be the quaternion algebra ramified exactly at

$$
R(B)=\{\tau:\tau\mid\infty,\ \tau\ne\tau _0\}\sqcup W.
\tag{9.1}
$$

Fix a compatible unitary central character $\omega$. Let $\pi$ be a cuspidal automorphic representation of $\mathrm{GL}_2(\mathbf A_F)$ with central character $\omega$, with full-group parallel-weight-two component $D_{2,\omega_\tau}$ at every real place, and such that, for every $w\in W$, $\pi_w$ is either selected special or selected depth-zero or tame positive-depth dihedral in the range of Books 80 and 103. Then there is a unique noncharacter automorphic representation

$$
\Pi_B=\operatorname{JL}_B^{-1}(\pi)
\quad\text{of}\quad B^\times(\mathbf A_F)
\tag{9.2}
$$

whose local factors are

$$
(\Pi_B)_v\cong
\begin{cases}
\pi_v,&v\notin R(B),\\
\operatorname{JL}_v^{-1}(\pi_v),&v\in R(B).
\end{cases}
\tag{9.3}
$$

At $\tau _0$ the first line uses the fixed splitting $B_{\tau _0}^\times\simeq\mathrm{GL}_2(\mathbf R)$; at the other real places the second line is the compact type trivial on the norm-one group, with the scalar action imposed by $\omega$. The assignment is inverse to global transfer and is a bijection between these split cusp forms and the selected noncharacter parallel-weight-two automorphic representations of $B^\times$ with the stated infinity type. This is its exact image.

Both automorphic multiplicities equal one. The central character of $\Pi_B$ is $\omega$. At every finite $v\notin W$, the local representation, conductor, compact type, and right-convolution Hecke action are unchanged. At $w\in W$ the exact prepared exponent is

$$
a_B((\Pi_B)_w)=a(\pi_w)=
\begin{cases}
1,&\pi_w=\operatorname{St}\otimes(\mu_w\circ\det),\ a(\mu_w)=0,\\
2a(\mu_w),&\pi_w=\operatorname{St}\otimes(\mu_w\circ\det),\ a(\mu_w)>0,\\
v_w(\mathfrak d_{E/F_w})+f(E/F_w)a_E(\theta),
&\pi_w=\pi(E,\theta).
\end{cases}
\tag{9.4}
$$

In the first line $(\Pi_B)_w=\mu_w\circ\operatorname{Nrd}$ has maximal-order fixed vectors although its prepared exponent is one; in the remaining lines the selected minimal division type is the one constructed from the displayed local label. Put $Z_w=F_w^\times$. If $(J_w',\lambda_w')$ is that division type, its normalized trace function is

$$
p_{\lambda_w'}(j)
=\operatorname{vol}(J_w'/Z_w)^{-1}
\operatorname{tr}\lambda_w'(j^{-1}),
$$

extended by zero with inverse central covariance. Right convolution by this function has trace

$$
\operatorname{tr}(\Pi_B)_w(p_{\lambda_w'})
=\dim\operatorname{Hom}_{J_w'}(\lambda_w',(\Pi_B)_w),
$$

which is one for the defining selected type. No equality of the full fixed-vector towers, or identification with an independently chosen raw split type idempotent, is asserted.

In particular, if every $\pi_w$ is an unramified Steinberg twist and the conductor away from $W$ is an ideal $\mathfrak n$ prime to $W$, then $(\Pi_B)_w$ is fixed by $\mathcal O_{B_w}^\times$ for every $w\in W$. The raw quaternionic level is maximal at $W$, while the prepared conductor and the split conductor are both

$$
\mathfrak n\prod_{w\in W}\mathfrak p_w.
$$

With $\operatorname{vol}(K_v)=1$ and

$$
K_vaK_v=\coprod_i a_iK_v,
$$

the common unnormalized action at a split finite place is

$$
R(\mathbf 1_{K_vaK_v})\phi(x)=\sum_i\phi(xa_i),
\tag{9.5}
$$

with right cosets, no inverse, and no averaging by the degree. Consequently the good eigenvalues $t_v,s_v$, the reciprocal polynomial $1-t_vX+q_vs_vX^2$, and the Frobenius-shaped polynomial $X^2-t_vX+q_vs_v$ agree exactly for $\pi$ and $\Pi_B$. If, in addition, the fixed common norm twist puts $\pi$ in Book 97's conjugation-compatible algebraic parallel-weight-two packet, then their good Hecke fields and their fields of rationality are equal, and algebraic coefficient conjugation commutes with (9.2). The existence, image, local, and multiplicity assertions do not require this additional rationality hypothesis.

### 9.6 Construction, uniqueness, and exact image

**Proof strategy.** Parity first constructs the algebra and division proves compactness. We then form the only possible local inverse tensor. Two distinct ramified places, at least one real, supply the two zeros in the character-clean trace identity, which forces a noncharacter compact constituent. Varying one local function at a time identifies the entire tensor; the same comparison in the forward direction proves exactness. Local uniqueness, the two multiplicity-one theorems, and the normalization ledger then prove the remaining assertions.

**Proof.** The ramification set (9.1) has

$$
(d-1)+|W|
$$

members, an even number. The local invariant reciprocity law therefore gives a unique isomorphism class of quaternion algebra with the stated ramification set. Since it is ramified at every real place except $\tau _0$ and $d\ge2$, it is not $M_2(F)$; a quaternion algebra is consequently division. Book 96, Theorem 2.1 then proves that

$$
Z(\mathbf A)B^\times(F)\backslash B^\times(\mathbf A)
$$

is compact. The split real factor does not create a cusp: compactness is an adelic consequence of division over $F$, not compactness of every local factor.

Define the candidate factors by (9.3). They exist locally: transfer is the identity away from $R(B)$, Book 80 supplies the inverse selected special or tame-dihedral factor at every $w\in W$, and real local Jacquet--Langlands supplies the compact inverse at every ramified real place. Their central characters are the local factors of $\omega$, so the restricted tensor has the correct global central character. What remains is automorphy.

Choose a ramified real place $a\ne\tau _0$. If $d=2$, parity makes $W$ odd and nonempty; choose $b\in W$. If $d\ge3$, choose a second ramified real place $b\ne a,\tau _0$ (one may instead use a member of $W$). At a real selected place use the weight-two compact projector and its split discrete-series transfer; at a finite selected place use the prepared type function and its transfer. In either case both split functions have zero split regular orbital integrals and trace zero on every full normalized principal series. Hence they are the two distinct zero factors required by Book 96, Proposition 7.2. At the active split real place $\tau _0$, use on both groups the same compact-mod-center Euler--Poincare pseudo-coefficient for $D_{2,\omega_{\tau _0}}$ used in Book 103, Chapter 12. Its trace is one on the chosen full-group weight-two discrete series and zero on the other tempered types, normalized principal series, and their one-dimensional quotients; its compact support puts it directly in the kernel class of Chapter 4. It plays no role in the ramification sign and requires neither a weight-two extension of the one-place formula nor a geometric realization of the packet.

Fix a finite level and infinity type containing $\pi$. Only finitely many cuspidal representations occur in that block. Begin with trace-nonzero local functions on the formal inverse factors of (9.3); at ramified places their transferred traces on the selected factors are fixed by the local character identities, and at split places transfer is the identity. Book 96's interpolation clause changes these tensors so that all quaternionic norm-character traces vanish and the scalar germs match, without changing the prescribed selected noncharacter trace coordinates. Strong multiplicity one separates the remaining finite split list, so interpolation in finitely many good spherical Hecke operators normalizes the split trace to one on $\pi$ and zero on every other cusp form in the block. Apply the reverse character-clean comparison of Theorem 7.1. The split side is nonzero, so the compact side contains a noncharacter constituent $\Pi_B$. Independently, its weight-two discrete-series factor at $\tau _0$ already rules out a global norm character; this remains true even when one or more finite inverse factors are local norm characters.

We next identify it rather than merely its good eigenvalues. The fixed pseudo-coefficient at $\tau _0$ already forces $(\Pi_B)_{\tau _0}\cong\pi_{\tau _0}$. At any other place $v$, hold the two selected factors fixed and vary a local function; if $v$ is one of those two places, keep the other as an undifferentiated zero factor. Every transferred function at such a ramified $v$ still has zero principal-series trace and zero split regular orbital integrals. The interpolation clause of Book 96 permits this variation while continuing to annihilate the finite norm-character list and normalize the scalar term. At a finite split place, equality of local character distributions gives $(\Pi_B)_v\cong\pi_v$. At a ramified place, the remaining $|R(B)|-1$ local signs leave the single local character identity, which gives $(\Pi_B)_v\cong\operatorname{JL}_v^{-1}(\pi_v)$. Thus every factor is the factor prescribed in (9.3).

If two compact automorphic representations had these factors, they would agree at every place and their restricted tensor products would be isomorphic. Equivalently, Book 96's strong determination identifies them already from their good split Hecke characters. This proves uniqueness. Conversely, starting with a selected noncharacter $B^\times$ representation, the forward extraction of Chapter 8 produces a cusp form with precisely the local factors in the theorem. The inverse construction just proved returns the original representation. Hence the image is exactly, and not merely contained in, the displayed selected split set.

Isolating a corresponding pair with local trace-one functions reduces the comparison to equality of automorphic multiplicities. Book 96 gives multiplicity one on the compact division side and Book 95 gives multiplicity one on the split cuspidal side, proving the multiplicity assertion.

Local transfer preserves central characters, which proves the global central-character assertion. Book 80 proves (9.4) and identifies the selected minimal types; identity transfer outside $W$ preserves the local conductor and type. Formula (9.5) follows directly from right convolution and the right-coset decomposition, so the good operators have exactly the same eigenvalues on the identical local representations.

Finally, assume the additional Book 97 hypothesis in the statement. The good eigenvalues of $\pi$ are algebraic and generate a number field by the rationality theorem of Book 97. They are the same numbers on $\Pi_B$, so the two good Hecke fields coincide. Algebraic conjugation preserves selected special labels, selected admissible tame pairs, the conjugated central character, and the parallel-weight-two algebraic coefficient system. Applying the construction to $\pi^\sigma$ and using local uniqueness gives

$$
\operatorname{JL}_B^{-1}(\pi^\sigma)
\cong
\operatorname{JL}_B^{-1}(\pi)^\sigma.
\tag{9.6}
$$

Thus an automorphism fixes $\pi$ if and only if it fixes $\Pi_B$: one implication uses inverse uniqueness, and the other uses injectivity of forward transfer. Their stabilizers in $\operatorname{Aut}(\mathbf C)$, hence their fields of rationality, are equal. This argument transports rationality through the trace-theoretic bijection; it uses no curve cohomology and claims no model over a field smaller than the field of rationality. $\square$

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

If $\chi_v$ is unramified, the division character is fixed by $\mathcal O_{D_v}^\times$ and has raw maximal-order level zero, whereas its Steinberg transfer has conductor exponent one. On the transfer-facing prepared scale both exponents are one. If $a(\chi_v)>0$, both prepared and split exponents equal $2a(\chi_v)$.

At a ramified real place, the trivial representation of $\mathbf H^\times$ transfers to the lowest member of the real discrete-series family, of weight two in the algebraic convention. More general norm powers and signs preserve the common central character. Thus the slogan “a norm character transfers to Steinberg” includes the real discrete-series analogue.

These local statements remain correct even though their restricted tensor does not globalize cuspidally. Local transfer is a theorem about one place; global automorphy imposes an additional compatibility.

### 10.3 How the trace comparison accounts for them

Locally, the reducible normalized principal series still explains the character identity: its character constituent and Steinberg constituent have opposite elliptic traces, and the division norm character is paired with the Steinberg constituent. In the one-place formula of Books 100--101, the strongly cuspidal real factor kills the continuous induced operator and its zero parabolic transform kills the residual determinant character. There is then no split one-dimensional term to pair with a quaternionic norm character.

In the low-weight two-place formula used here, residual determinant characters are first matched with norm characters: their local trace signs multiply to $+1$ because $|R|$ is even. Character-clean interpolation then annihilates both spectra. On every fixed block this projection is realized by Section 7.3. Geometrically, regular transfer does not determine central values, and Book 103's two-germ calculation together with Book 96's interpolation permits the central correction (7.1). For these separating tests the resulting identity is

$$
I_{G^*,\mathrm{cusp}}(f)
=I_D(f'),
$$

because every norm-character trace on $f'$ is zero. Equivalently, as an abstract spectral distribution, the right side is the restriction of $I_D$ to the orthogonal complement of the character spectrum. Thus the exceptional spectrum is accounted for exactly once. In the one-place formula it remains only on the compact side before subtraction; in the two-place formula the matched residual and norm-character terms are subtracted together.

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

Let $\pi=\operatorname{JL}_D(\Pi)$ in either Theorem 9.1 or Theorem 9.2. At split places the central characters agree tautologically; at ramified places local transfer preserves them. Therefore

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

At a division place the raw first principal-unit depth is not a conductor on the same scale: division invariants jump from zero to the entire finite-dimensional representation, whereas split newvectors first appear on a line. Book 80 therefore defines the transfer-facing exponent from the selected packet label:

$$
a_D(\Pi_v)=
\begin{cases}
1,&\Pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)=0,\\
2a(\mu_v),&\Pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)>0,\\
v(\mathfrak d_{E/F_v})+f(E/F_v)a_E(\theta),
&\Pi_v=\pi'(E,\theta).
\end{cases}
$$

The selected local theorem proves exactly

$$
\boxed{a(\pi_v)=a_D(\Pi_v).}
$$

The first line records the monodromy boundary: an unramified division norm character is maximal-compact fixed, but its Steinberg transfer has conductor one. The third line covers both depth-zero and tame positive-depth dihedral packets. Under twisting, one must replace $\mu$ or $\theta$ by the actually twisted label before evaluating the formula; conductors can cancel.

Globally define

$$
\mathfrak f_D(\Pi)=
\prod_{v<\infty}\mathfrak p_v^{a_D(\Pi_v)}
$$

using the usual split exponent off $R_f$. Then

$$
\boxed{
\mathfrak f(\operatorname{JL}_D(\Pi))
=\mathfrak f_D(\Pi).}
$$

If one instead records the raw maximal-order level on the division side, every unramified norm component contributes exponent zero there and exponent one after transfer. This is the source of the familiar discriminant factor. Replacing the prepared conductor by a raw division depth without recording this correction would be false.

**Worked cancellation.** Suppose $\Pi_v=\mu_v\circ\operatorname{Nrd}$ with $\mu_v$ nontrivial tame quadratic. The prepared division exponent and the split exponent are both two. Twisting by the same $\mu_v$ produces the trivial division character and unramified Steinberg; both prepared exponents become one, although the raw maximal-order depth on the division side is zero. A maximum-of-conductors rule would incorrectly leave exponent two.

### 11.3 Local and global factors

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

Formal degrees are deliberately not inserted into these global identities. They depend on a local Plancherel normalization and are not automorphic multiplicities. The trace comparison uses type functions normalized by their actual convolution measures; no unproved numerical formal-degree formula is needed.

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

If $K_vaK_v=\coprod_i a_iK_v$ is a right-coset decomposition, the convention is

$$
R(\mathbf1_{K_vaK_v})\phi(x)=\sum_i\phi(xa_i).
\tag{12.1}
$$

There is no $a_i^{-1}$, no division by the number of cosets, and no hidden degree factor. The raw reciprocal Hecke polynomial is

$$
P_v(X)=1-t_vX+q_vs_vX^2.
$$

The same coefficients give the Frobenius-shaped polynomial

$$
P_v^{\mathrm{Fr}}(X)=X^2-t_vX+q_vs_v.
\tag{12.2}
$$

The first polynomial is convenient for Euler factors; the second is the characteristic-polynomial orientation used by right-convolution Hecke correspondences on curves. Neither notation changes the operators $T_v,S_v$.

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

In the compact one-split range of Theorem 9.2, the active factor at $\tau _0$ is already the full-group weight-two discrete series and is left unchanged. At every other real place the trivial compact adjoint type transfers to the same weight-two discrete series. Hence the inverse packet has the intrinsic parallel-weight-two infinity type: weight two at the split factor and trivial compact adjoint type at the ramified factors. This is a local archimedean calculation inside the trace-formula proof; no Shimura-curve cohomology is used to establish the global packet.

### 13.4 Parity and the global center

At a real place, the lowest weight $k_\tau$ determines the action of $-1$ by $(-1)^{k_\tau}$, modified by the prescribed sign of the central character. Because a global Hecke character is trivial on the principal element $-1\in F^\times$, the product of local signs must be one.

Thus locally available weights cannot be assembled arbitrarily. For example, over a totally real field with two real places, weights $2$ and $3$ with trivial finite central character violate the global parity condition. Each local discrete series exists, but their tensor cannot be an automorphic infinity type with trivial center.

Global Jacquet--Langlands preserves rather than repairs this condition: the quaternionic coefficient system and the split discrete series have the same scalar actions at each place, so either both global central characters descend or neither does.

## 14. Finite level, newforms, and exact level change

### 14.1 From quaternionic fixed vectors to split newvectors

The finite algebraic-space formula in this paragraph belongs to the totally definite range. For the compact one-split range, the same local conductor and type assertions apply representation by representation, as stated in Theorem 9.2, but no finite double-coset model is substituted for the split real factor.

Let $U=\prod_{v<\infty}U_v\subset D^\times(\mathbf A_f)$ be a compact open and let $\mathcal W$ be an archimedean algebraic weight. The finite quaternionic space decomposes in characteristic zero as

$$
S_D(U,\mathcal W,\omega)
\cong
\bigoplus_\Pi
\operatorname{Hom}_{G(F_\infty)}(\mathcal W^\vee,\Pi_\infty)
\otimes\Pi_f^U,
$$

with multiplicity one and with a separate norm-character block.

For a noncharacter constituent, transfer identifies the global representation but not the fixed-vector space. At split places $U_v$ is transported unchanged and the invariant spaces agree. At division places the local level must be translated through conductor and type theory.

For a selected special or dihedral factor, Book 80 constructs a minimal division type $(J_v',\lambda_v')$ and the corresponding split type $(J_v,\lambda_v)$. Book 103 transfers their normalized type functions, and their trace on the selected representation is the same. On the split side the newform theorem recalled in Book 95 gives a one-dimensional $K_1(\mathfrak p_v^{a_D(\Pi_v)})$ newvector line. On the division side a normal principal-unit subgroup fixes either zero or the whole irreducible representation. Thus the theorem matches the representation and its prepared minimal type, not the ambient fixed-vector spaces term by term.

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

**Counterexample to unrestricted multiplication.** If $\Pi_v=\pi'(E,\theta)$ is a selected dihedral factor, then its transfer has exponent

$$
v(\mathfrak d_{E/F_v})+f(E/F_v)a_E(\theta),
$$

which can be greater than one. Multiplying a raw division level merely by the squarefree discriminant would record exponent one and lose the type depth.

### 14.3 Deeper division levels

For the normal principal congruence tower $U_D^m=1+\mathfrak P_D^m$, irreducibility and normality imply that $\Pi_v^{U_D^m}$ is either zero or all of $\Pi_v$. Once it appears, deeper normal level does not create a growing flag. On the split side the newvector theorem gives a line at exponent $a_D(\Pi_v)$ and an oldvector tower above it. There is therefore no level-by-level vector-space isomorphism along these towers, even though the prepared conductor and minimal types correspond.

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

Every comparison in this chapter is over characteristic zero. Book 97 constructs integral packet lattices when a Hecke-stable integral module is supplied; the finite quaternionic class module provides such a source, while its split-side statements retain their stated lattice hypothesis. The rational correspondence does not identify the two lattices, prove saturation of a level-change map, or compute a congruence index. Even the quotient by the norm-character submodule need not split integrally. Those assertions belong to the later theory of integral level change; using them here would exceed both the theorem and its dependencies.

## 15. Rationality and conjugation

### 15.1 What character identities prove

In either theorem range, the global correspondence is characterized by local character identities at ramified places and equality of local representations at split places. Both statements are algebraic after the representations and test functions have been placed over a number field. If $\sigma\in\operatorname{Aut}(\mathbf C)$, applying $\sigma$ to the identities gives

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

For an algebraic packet in either theorem range, define its good Hecke field by

$$
E(\Pi)=
\mathbf Q\bigl(t_v(\Pi),s_v(\Pi):v\notin\Sigma\bigr),
$$

with the values of the central character included when they are not already fixed. On the split side Book 97 supplies algebraicity and a number-field model for these eigenvalues. Equality of good-place Hecke polynomials then gives

$$
E(\Pi)=E(\operatorname{JL}_D(\Pi))
$$

for the eigensystems in the same algebraic normalization, and proves at once that the quaternionic field is a number field. In the totally definite range the finite algebraic quaternionic class module gives an independent rational model. In the one-split range the equality is transported from the split packet; no finite class-set model and no geometric cohomology realization are being asserted.

This is also equality of fields of rationality. Indeed, let $\sigma\in\operatorname{Aut}(\mathbf C)$. If $\sigma$ fixes the good Hecke field of $\pi=\operatorname{JL}_D(\Pi)$ and the central character, then $\pi^\sigma$ and $\pi$ agree at almost every place, so strong multiplicity one gives $\pi^\sigma\cong\pi$. Conversely an isomorphism fixes all good Hecke eigenvalues. By conjugation compatibility and injectivity of global transfer,

$$
\Pi^\sigma\cong\Pi
\quad\Longleftrightarrow\quad
\pi^\sigma\cong\pi.
$$

Their stabilizers in $\operatorname{Aut}(\mathbf C)$ are equal, hence so are their fixed fields. Thus both the good Hecke field and the representation-theoretic rationality field are preserved.

Bad-place eigenvalues may enlarge the field needed to realize a chosen local type. Likewise a particular basis of a division newlevel block can require a larger splitting field than its central Hecke character. These are fields of definition, not fields of rationality; Book 97 warns that a Schur index can keep them distinct.

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

One line consists of constants. It generates the trivial norm character and is excluded from the cuspidal correspondence. There is no second norm character at this level and weight: its Hecke character would be unramified at every finite prime, trivial on $\mathbf R_{>0}$, and trivial on $\mathbf Q^\times$; the class-number-one idele decomposition of $\mathbf Q$ makes such a character trivial. Hence the orthogonal complement for the mass pairing is one dimensional and noncharacter. Let $\Pi$ be its automorphic constituent.

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

Let $D/\mathbf Q$ be definite and ramified at a finite prime $p$, and suppose $\Pi_p=\pi'(E,\theta)$ is a selected depth-zero dihedral factor, with $E/\mathbf Q_p$ unramified and $\theta$ regular on the residue torus. Book 80 gives

$$
a(\operatorname{JL}_p(\Pi_p))
=v_p(\mathfrak d_{E/\mathbf Q_p})+2a_E(\theta)=2.
$$

Thus the split transfer is supercuspidal of conductor $p^2$ and has a one-dimensional $K_1(p^2)$ newvector line. At split level $p^4$ it contributes

$$
4-2+1=3
$$

oldvectors. On the division side the depth-zero type is already trivial on $U_{D_p}^1$, so every deeper normal principal-unit group fixes the entire finite-dimensional $\Pi_p$; no analogous three-step oldvector flag appears. This example shows why equality of automorphic multiplicity and equality of Hecke eigensystems do not imply equality of fixed-space dimensions.

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

For a selected noncharacter automorphic $\Pi$ and $\pi=\operatorname{JL}_D(\Pi)$, the usable local dictionary is:

| place and quaternionic component                                     | split component                              | level or weight effect                                |
| -------------------------------------------------------------------- | -------------------------------------------- | ----------------------------------------------------- |
| $v\notin R$, spherical                                               | the same spherical representation            | identical $T_v,S_v$ and Satake polynomial             |
| $v\notin R$, ramified                                                | the same local representation                | identical conductor and local type                    |
| $v\in R_f$, unramified norm character $\mu_v\circ\operatorname{Nrd}$ | $\operatorname{St}_v\otimes\mu_v$            | exponent $0\mapsto1$                                  |
| $v\in R_f$, ramified norm character                                  | ramified Steinberg twist                     | exponent $2a(\mu_v)$ on both prepared scales          |
| $v\in R_f$, selected dihedral $\pi'(E,\theta)$                       | selected dihedral supercuspidal              | exponent $v(\mathfrak d_{E/F_v})+f(E/F_v)a_E(\theta)$ |
| real $v\in R$, compact highest degree $n_v$                          | real discrete series                         | minimal weight $n_v+2$, same center                   |
| the unique real $\tau _0\notin R$ in Theorem 9.2                     | the same full-group $D_{2,\omega_{\tau _0}}$ | active weight two is unchanged                        |
| real or complex $v\notin R$                                          | the same representation                      | no change                                             |

In every row, central characters, contragredients, determinant/norm twists, and local $L$- and epsilon factors are compatible. At ramified places the character identity has sign $-1$; over all ramified places the product sign is $+1$.

### 18.2 A reusable global theorem

The totally definite theorem can be applied through the following checklist.

1. Verify that the quaternionic constituent is not one dimensional and lies in the selected range at every finite division place.
2. Verify the totally real, totally definite, algebraic infinity-type hypotheses and record the full ramification set $R$, including infinity.
3. At $v\notin R$, retain the local component unchanged.
4. At finite $v\in R$, apply selected local Jacquet--Langlands; at real $v$, apply the algebraic discrete-series correspondence.
5. Form the global conductor using the exact local exponent, inserting the $0\mapsto1$ correction for unramified norm components.
6. Transfer the archimedean compact highest weight to discrete-series lowest weight with the action-convention dual included.
7. Retain the same global central character and good-place Hecke polynomials.
8. Use strong multiplicity one to identify the resulting cusp representation from almost-all Hecke data.

In the reverse direction, begin with a cuspidal $\pi$, check the selected special-or-dihedral condition at every finite place of $R$, and check the prescribed algebraic discrete-series type at infinity. Only then apply the local inverse correspondence. The trace formula guarantees that the resulting tensor is an automorphic noncharacter representation of $D^\times(\mathbf A)$.

For the compact one-split theorem, use a separate checklist.

1. Verify that $d=[F:\mathbf Q]\ge2$, choose the active real place $\tau _0$, and choose a finite set $W$ with $(d-1)+|W|$ even. Thus $W$ is odd and nonempty when $d$ is even, and is even, possibly empty, when $d$ is odd.
2. Form the quaternion algebra ramified at every real place except $\tau _0$ and at exactly the places of $W$; the parity count makes it exist and its real ramification makes it division.
3. Begin with a cuspidal full-group parallel-weight-two $\pi$ and verify at every $w\in W$ that $\pi_w$ is selected special or selected tame dihedral. A principal series or excluded wild packet at one member of $W$ stops the construction.
4. Retain $\pi_v$ at every split place, including $\tau _0$, and take the proved local inverse at every place of $R(B)$.
5. Use Theorem 9.2 to globalize that tensor uniquely as a noncharacter $\Pi_B$. Its central character and good right-convolution eigenvalues are those of $\pi$; under Book 97's additional algebraicity hypothesis, its coefficient field and field of rationality are as well.
6. At $W$, record the prepared conductor and selected minimal division type by (9.4). In particular, an unramified Steinberg twist corresponds to a maximal-order-fixed norm character but retains prepared exponent one.

This second procedure is exactly the one-split inverse theorem, not an assertion for quaternion algebras with any other real signature.

### 18.3 Inputs for later applications

The output needed downstream is now precise.

- A quaternionic Hecke eigensystem away from the bad set determines one cuspidal $\mathrm{GL}_2$ representation after the character block is removed.
- Its local components at ramified places are known, not guessed from conductor: norm characters become Steinberg twists and higher-dimensional components become supercuspidals.
- The finite conductor, bad-place newness, central character, twists, dual, and local factors obey the exact selected local dictionary, with the explicit $0\mapsto1$ shift when raw maximal division level is compared with an unramified Steinberg component.
- Algebraic compact weights become cohomological discrete-series weights, and algebraic Galois conjugation of coefficients commutes with transfer.
- Multiplicity is one on both sides, while fixed-level vector multiplicities remain governed by their different local towers.
- If $F$ has degree at least two and a parity-compatible set $W$ of selected special or tame-dihedral places is chosen, Theorem 9.2 constructs the unique one-split compact quaternionic packet with those inverse local factors. In even degree $W$ is odd and nonempty; in odd degree it is even and may be empty. This closes the automorphic arrow from a split parallel-weight-two packet to the compact curve inner form without using the curve's cohomology.

These facts are the complete automorphic output of the book. The book does not construct automorphic induction or base change; those are separate global transfers with their own image and descent conditions. It also does not attach Galois representations to the Hecke system. Here the endpoint is the automorphic representation and its complete local dictionary.

### 18.4 Conclusion

Global Jacquet--Langlands begins with a local geometric coincidence. A regular quaternion generates a quadratic field, and the same polynomial generates an elliptic matrix class. At every ramified place the division algebra retains exactly the elliptic classes and discards the split ones. Matching orbital integrals with transfer factor $+1$ turns this coincidence into a product of local identities.

The global trace formula supplies what local correspondence cannot. Compactness makes the quaternionic trace a sum over a discrete spectrum and quadratic-field conjugacy classes. At sufficiently admissible weights, one strongly cuspidal real transfer function makes the split trace equally simple. In the weight-two theorem proved here, two ramified trace-cuspidal transfers instead kill differentiated continuous and boundary terms by leaving an undifferentiated zero factor. Split tori and quadratic fields that fail to embed also acquire a zero local orbital factor. The surviving regular centralizers are literally the same tori with the same Tamagawa measures. Character-clean interpolation removes the matched residual and quaternionic character terms, and a paired singular bump normalizes the scalar distribution.

On the spectral side every ramified local transfer contributes a minus sign. Global reciprocity makes the number of ramified places even, so the signs multiply to one. Varying test functions then isolates representations, proves existence, recovers every local component, and preserves multiplicity. Strong multiplicity one turns agreement away from finitely many places into global uniqueness and makes the transfer detectable by good Hecke eigenvalues.

The exceptional character spectrum reveals one boundary of the theorem. A norm character has legitimate local Steinberg transfers at division places, but its almost-everywhere one-dimensional tensor cannot be cuspidal. Character-clean subtraction removes it together with the corresponding residual determinant trace. The other boundary is local: the proved bijection covers exactly the selected special and tame-dihedral finite packets with the prescribed algebraic infinity type, not primitive wild packets.

For algebraic packets, the resulting rational dictionary preserves multiplicity, central characters, twists, contragredients, local factors, root numbers, good Hecke polynomials, rationality fields, and algebraic conjugation. The analytic correspondence and its local identities do not depend on this rationality qualification. It changes raw maximal division level by the explicit discriminant factor and turns compact archimedean weights into discrete-series weights shifted by two. It does not identify integral lattices or congruence indices. In the totally definite selected range, a quaternionic eigensystem becomes a unique split cuspidal representation. In the compact one-split range, a split cusp form satisfying the exact local image condition becomes a unique noncharacter quaternionic representation. These are the two, and only the two, global ranges established here.
