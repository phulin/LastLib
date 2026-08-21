# Automorphic Representations of $\mathrm{GL}_2$

## Contents

1. [The global representation problem](#1-the-global-representation-problem)
   - [From arithmetic functions to one global representation](#11-from-arithmetic-functions-to-one-global-representation)
   - [Standing notation and conventions](#12-standing-notation-and-conventions)
   - [What will and will not be constructed](#13-what-will-and-will-not-be-constructed)
2. [The adelic group and its quotients](#2-the-adelic-group-and-its-quotients)
   - [Restricted products and rational points](#21-restricted-products-and-rational-points)
   - [The center and the determinant direction](#22-the-center-and-the-determinant-direction)
   - [Haar measures and quotient integration](#23-haar-measures-and-quotient-integration)
   - [Reduction theory and finite volume](#24-reduction-theory-and-finite-volume)
   - [A lattice model for the cusp](#25-a-lattice-model-for-the-cusp)
3. [Automorphic forms and central characters](#3-automorphic-forms-and-central-characters)
   - [Why analytic and finiteness conditions coexist](#31-why-analytic-and-finiteness-conditions-coexist)
   - [Fixed central character](#32-fixed-central-character)
   - [Smooth automorphic representations](#33-smooth-automorphic-representations)
   - [Examples and failures](#34-examples-and-failures)
   - [Analytic vectors and algebraic normalizations](#35-analytic-vectors-and-algebraic-normalizations)
   - [A convention and hypothesis ledger](#36-a-convention-and-hypothesis-ledger)
4. [Constant terms and cuspidality](#4-constant-terms-and-cuspidality)
   - [Fourier analysis along the unipotent quotient](#41-fourier-analysis-along-the-unipotent-quotient)
   - [What cuspidality removes](#42-what-cuspidality-removes)
   - [A Fourier counterexample](#43-a-fourier-counterexample)
   - [Orthogonality to induced behavior](#44-orthogonality-to-induced-behavior)
   - [Poincaré series as a source of cusp forms](#45-poincaré-series-as-a-source-of-cusp-forms)
   - [Equivalent forms of the cusp condition](#46-equivalent-forms-of-the-cusp-condition)
5. [The cuspidal spectrum](#5-the-cuspidal-spectrum)
   - [The Hilbert space with central character](#51-the-hilbert-space-with-central-character)
   - [Why the cuspidal spectrum is discrete](#52-why-the-cuspidal-spectrum-is-discrete)
   - [Admissibility of global constituents](#53-admissibility-of-global-constituents)
   - [The residual boundary](#54-the-residual-boundary)
   - [Compact-open projectors](#55-compact-open-projectors)
   - [Atomicity and finite multiplicity in detail](#56-atomicity-and-finite-multiplicity-in-detail)
6. [Restricted tensor products and local components](#6-restricted-tensor-products-and-local-components)
   - [Why a global irreducible representation should factor](#61-why-a-global-irreducible-representation-should-factor)
   - [Factorization theorem](#62-factorization-theorem)
   - [Finite and archimedean local components](#63-finite-and-archimedean-local-components)
   - [Almost-everywhere spherical vectors](#64-almost-everywhere-spherical-vectors)
   - [Central characters and reference vectors](#65-central-characters-and-reference-vectors)
   - [Invariant spaces and restricted tensor products](#66-invariant-spaces-and-restricted-tensor-products)
   - [The local families inside a global representation](#67-the-local-families-inside-a-global-representation)
7. [Unramified Hecke data](#7-unramified-hecke-data)
   - [Convolution and the fixed-level viewpoint](#71-convolution-and-the-fixed-level-viewpoint)
   - [Satake parameters and the raw operator](#72-satake-parameters-and-the-raw-operator)
   - [The local polynomial and standard factor](#73-the-local-polynomial-and-standard-factor)
   - [Twists and a worked unramified example](#74-twists-and-a-worked-unramified-example)
   - [Radial recurrences](#75-radial-recurrences)
   - [Proof of the rank-two Satake calculation](#76-proof-of-the-rank-two-satake-calculation)
8. [Global Whittaker expansions](#8-global-whittaker-expansions)
   - [Why the nonconstant coefficient should determine the form](#81-why-the-nonconstant-coefficient-should-determine-the-form)
   - [Fourier expansion and injectivity](#82-fourier-expansion-and-injectivity)
   - [Global and local uniqueness](#83-global-and-local-uniqueness)
   - [The spherical Whittaker function](#84-the-spherical-whittaker-function)
   - [Standard zeta integrals](#85-standard-zeta-integrals)
   - [Global genericity and Euler products](#86-global-genericity-and-euler-products)
9. [Multiplicity one](#9-multiplicity-one)
   - [Two logically distinct assertions](#91-two-logically-distinct-assertions)
   - [Global multiplicity one from Whittaker expansion](#92-global-multiplicity-one-from-whittaker-expansion)
   - [The Rankin--Selberg integral](#93-the-rankin--selberg-integral)
   - [Strong multiplicity one](#94-strong-multiplicity-one)
   - [Why the pole comparison is logically complete](#95-why-the-pole-comparison-is-logically-complete)
   - [Recognition limits and counterexamples](#96-recognition-limits-and-counterexamples)
10. [Contragredients, twists, and central characters](#10-contragredients-twists-and-central-characters)
    - [The contragredient in the automorphic realization](#101-the-contragredient-in-the-automorphic-realization)
    - [Twisting by a Hecke character](#102-twisting-by-a-hecke-character)
    - [Finite-order and algebraic characters](#103-finite-order-and-algebraic-characters)
    - [Self-twists and a warning](#104-self-twists-and-a-warning)
    - [Local factors under duality](#105-local-factors-under-duality)
11. [Conductors and compact-open invariants](#11-conductors-and-compact-open-invariants)
    - [The local exponent and global ideal](#111-the-local-exponent-and-global-ideal)
    - [Global level groups and existence of invariants](#112-global-level-groups-and-existence-of-invariants)
    - [$K_0$ and the central-character correction](#113-k_0-and-the-central-character-correction)
    - [Conductors of local families](#114-conductors-of-local-families)
    - [Worked conductor profiles](#115-worked-conductor-profiles)
12. [Newforms and oldforms](#12-newforms-and-oldforms)
    - [Why minimal level singles out an eigenform](#121-why-minimal-level-singles-out-an-eigenform)
    - [Degeneracy maps and level raising](#122-degeneracy-maps-and-level-raising)
    - [The new subspace](#123-the-new-subspace)
    - [A counterexample to “new means ramified everywhere”](#124-a-counterexample-to-new-means-ramified-everywhere)
    - [Recovering new dimensions](#125-recovering-new-dimensions)
    - [The complete newform theorem](#126-the-complete-newform-theorem)
13. [Classical modular forms over $\mathbf Q$](#13-classical-modular-forms-over-mathbf-q)
    - [The adelization problem](#131-the-adelization-problem)
    - [Weight, level, and central character](#132-weight-level-and-central-character)
    - [Cuspidality and Fourier expansions](#133-cuspidality-and-fourier-expansions)
    - [Hecke eigenvalues and the unitary shift](#134-hecke-eigenvalues-and-the-unitary-shift)
    - [Primes dividing the level](#135-primes-dividing-the-level)
    - [The classical correspondence](#136-the-classical-correspondence)
    - [Proof of the two-way classical dictionary](#137-proof-of-the-two-way-classical-dictionary)
    - [A complete level-one example](#138-a-complete-level-one-example)
14. [Hilbert modular representations](#14-hilbert-modular-representations)
    - [Several real places, one adelic object](#141-several-real-places-one-adelic-object)
    - [Algebraic and cohomological weights](#142-algebraic-and-cohomological-weights)
    - [Parity from the center](#143-parity-from-the-center)
    - [Hilbert Hecke data and conductor](#144-hilbert-hecke-data-and-conductor)
    - [The Hilbert correspondence](#145-the-hilbert-correspondence)
    - [Components, ideals, and the proof of descent](#146-components-ideals-and-the-proof-of-descent)
    - [Parallel weight two as a global test case](#147-parallel-weight-two-as-a-global-test-case)
15. [Algebraicity and rationality](#15-algebraicity-and-rationality)
    - [What finite-dimensionality proves](#151-what-finite-dimensionality-proves)
    - [Field of rationality versus field of definition](#152-field-of-rationality-versus-field-of-definition)
    - [Galois conjugation of eigenforms](#153-galois-conjugation-of-eigenforms)
    - [The boundary of the algebraicity assertion](#154-the-boundary-of-the-algebraicity-assertion)
16. [Hecke algebras on fixed-level spaces](#16-hecke-algebras-on-fixed-level-spaces)
    - [The restricted tensor algebra](#161-the-restricted-tensor-algebra)
    - [Spectral decomposition of the action](#162-spectral-decomposition-of-the-action)
    - [Eigenvalue multiplicity versus representation multiplicity](#163-eigenvalue-multiplicity-versus-representation-multiplicity)
    - [Central operators and fixed character](#164-central-operators-and-fixed-character)
17. [The global dictionary](#17-the-global-dictionary)
    - [From eigenform data to local representations](#171-from-eigenform-data-to-local-representations)
    - [Normalization dictionary](#172-normalization-dictionary)
    - [Reading local types from global data](#173-reading-local-types-from-global-data)
    - [Twists through the dictionary](#174-twists-through-the-dictionary)
    - [Reconstruction and its limits](#175-reconstruction-and-its-limits)
    - [The automorphic representation package](#176-the-automorphic-representation-package)
18. [Conclusion: one form across all places](#18-conclusion-one-form-across-all-places)

## 1. The global representation problem

### 1.1 From arithmetic functions to one global representation

A classical modular eigenform appears at first as a holomorphic function on the upper half-plane. Its Fourier coefficients, congruence level, nebentype, and weight seem to be different kinds of data. The adelic viewpoint makes them shadows of one object. The finite primes record smooth representations and their distinguished vectors; the real places record analytic representations and their lowest weights; the Fourier expansion becomes a Whittaker expansion; and all Hecke operators arise from convolution in one group.

This book develops that viewpoint for

$$
G=\mathrm{GL}_{2/F},
$$

where $F$ is a number field. Its endpoint is a dictionary, not merely a change of notation. A cuspidal eigenform determines an irreducible representation

$$
\pi\cong\bigotimes_v'\pi_v
$$

of $G(\mathbf A_F)$, and the local factors recover level, Hecke eigenvalues, central character, and archimedean weight. Conversely, an automorphic representation with the appropriate archimedean and finite vectors produces a classical or Hilbert modular eigenform.

Two distinctions govern the narrative. First, an automorphic **form** is a function satisfying analytic and finiteness conditions, whereas an automorphic **representation** is an irreducible constituent of a space of such functions. Second, local cuspidality and global cuspidality are not the same statement. A global cuspidal representation may have principal-series components at almost every finite place. Global cuspidality is the vanishing of a global constant term; it forces the representation into the discrete spectrum.

### 1.2 Standing notation and conventions

Write

$$
\mathbf A=\mathbf A_F=F_\infty\times\mathbf A_{F,f},
\qquad G_v=\mathrm{GL}_2(F_v),
\qquad G(\mathbf A)=\prod_v'G_v.
$$

At a finite place $v$, let $\mathcal O_v$ be the integers, $\mathfrak p_v=(\varpi_v)$, $q_v=|\mathcal O_v/\mathfrak p_v|$, and $K_v=\mathrm{GL}_2(\mathcal O_v)$. The restricted product is taken relative to the $K_v$. Put

$$
K_f=\prod_{v<\infty}K_v,
$$

and choose a maximal compact subgroup $K_\infty\subset G(F_\infty)$. The center and the standard Borel are

$$
Z=\left\{\begin{pmatrix}z&0\\0&z\end{pmatrix}\right\},\qquad
B=TN,\qquad
N=\left\{n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}\right\}.
$$

All actions on functions are on the right:

$$
(R(g)\phi)(x)=\phi(xg).
$$

Thus $R(g_1)R(g_2)=R(g_1g_2)$. Left multiplication by $G(F)$ expresses automorphy and commutes with this right action.

We use normalized absolute values, so $|\varpi_v|_v=q_v^{-1}$ and $\prod_v|a|_v=1$ for $a\in F^\times$. A Hecke character is a continuous character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
$$

It is called unitary when $|\omega|=1$. Unless explicitly stated otherwise, Hilbert-space assertions use unitary central characters. Smooth representations at finite places are complex and admissible; archimedean representations are understood through their smooth, $K_v$-finite vectors and their Hilbert completions when unitarity is relevant.

### 1.3 What will and will not be constructed

The theory here is intrinsic to split rank two. We will construct the cuspidal spectrum, its local factorization, Whittaker models, Hecke data, conductors, and newforms, and then connect them with classical and Hilbert modular forms. One-dimensional and residual representations will be described only far enough to locate the boundary of cuspidality.

Representations of multiplicative groups of quaternion algebras, their global transfer, automorphic induction, base change, and representations attached to Galois groups require additional ideas and belong later. Keeping that boundary sharp is mathematically useful: none of the factorization, multiplicity-one, or newform arguments below depends on those constructions.

This order is logically necessary. Before one can compare a split representation with another
group or another field, one must know what the split representation is, how its local factors are
normalized, and which global data determine it. The present book supplies exactly that invariant
package. Later comparison theorems may use it as an input, but no comparison theorem is used to
prove the package itself.

## 2. The adelic group and its quotients

### 2.1 Restricted products and rational points

The adelic group must allow independent motion at finitely many places while retaining an integral tail. Explicitly,

$$
G(\mathbf A_f)=\left\{(g_v)_{v<\infty}:g_v\in K_v
\text{ for almost every }v\right\}.
$$

A basic open set specifies open subsets at finitely many places and uses $K_v$ elsewhere. This makes $G(\mathbf A_f)$ totally disconnected and locally compact; $G(\mathbf A)$ is locally compact after adjoining the finitely many archimedean factors. The diagonal subgroup $G(F)$ is discrete. Indeed, matrix entries and the inverse determinant reduce the assertion to discreteness of $F$ in $\mathbf A$.

The left quotient

$$
[G]=G(F)\backslash G(\mathbf A)
$$

therefore carries the quotient topology of a properly discontinuous action. It is locally compact and Hausdorff. A compact open $U\subset G(\mathbf A_f)$ cuts it into finitely many arithmetic quotients at infinity:

$$
G(F)\backslash G(\mathbf A)/(UK_\infty)
$$

has finitely many connected pieces, although each piece can be noncompact. This finite decomposition is the topological reason that finite level converts adelic analysis into analysis on finitely many locally symmetric spaces.

### 2.2 The center and the determinant direction

The center satisfies $Z(\mathbf A)\cong\mathbf A^\times$ and $Z(F)\cong F^\times$. It is not harmless. The quotient $[G]$ has an obvious noncompact direction measured by

$$
g\longmapsto |\det g|_{\mathbf A}.
$$

Scalar multiplication by $zI_2$ changes this value by $|z|_{\mathbf A}^2$. For fixed central character, the natural geometric quotient is therefore

$$
X_G=Z(\mathbf A)G(F)\backslash G(\mathbf A).
$$

Equivalently one may choose the subgroup

$$
G(\mathbf A)^1=\{g:|\det g|_{\mathbf A}=1\}
$$

and work modulo $Z(\mathbf A)^1G(F)$. The two descriptions differ only by choosing a positive scalar section. Neither quotient is compact: removing the scalar determinant direction does not remove the cusp produced by matrices whose two diagonal entries have very different sizes.

A useful counterexample is the sequence

$$
a(t)=\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}
$$

at one archimedean place, with all other components $1$. Its determinant has module $1$, so passage to $G(\mathbf A)^1$ does not control it. Reduction by $G(F)$ and the center still leaves representatives with height tending to infinity. Thus finite volume must not be confused with compactness.

### 2.3 Haar measures and quotient integration

Choose additive Haar measure $dx_v$ on each $F_v$, with $\operatorname{vol}(\mathcal O_v)=1$ for almost every finite $v$. The product measure on $\mathbf A$ is then well defined. We normalize the measure on $N(F)\backslash N(\mathbf A)\cong F\backslash\mathbf A$ to have volume $1$. Fix local Haar measures $dg_v$ on $G_v$ with

$$
\operatorname{vol}(K_v)=1
$$

for almost every finite $v$. Their restricted product gives $dg$ on $G(\mathbf A)$. Since $\mathrm{GL}_2$ is unimodular, left and right Haar measures agree.

Quotient measures are specified by Weil's integration formula. For example, once measures on $Z(\mathbf A)$, $G(F)\backslash G(\mathbf A)$, and $X_G$ are compatibly chosen,

$$
\int_{G(F)\backslash G(\mathbf A)}f(g)\,dg
=\int_{X_G}\int_{Z(F)\backslash Z(\mathbf A)}f(zg)\,dz\,d\dot g
$$

whenever the integrals converge. Scaling all measures changes inner products by a positive scalar but does not change representations or orthogonality. Local Hecke eigenvalues do depend on the convention $\operatorname{vol}(K_v)=1$, so that convention will always be visible.

### 2.4 Reduction theory and finite volume

Reduction theory supplies a coarse fundamental set. In rank two, every point of $X_G$ can be represented, up to a compact set, by an element of the positive diagonal chamber

$$
a(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix},
\qquad |y|_{\mathbf A}\ge c,
$$

together with bounded unipotent and compact factors. The quotient has finite invariant volume because the modular character of $B$ makes the tail integrable. It is not compact because $|y|_{\mathbf A}$ has no upper bound.

This is the geometric source of growth on the quotient by the center. On $X_G$, an automorphic function only needs control in finitely many cusp regions, and on each region the dangerous variable is a rational height comparable to

$$
\operatorname{ht}_X(g)=\max\{|y|_{\mathbf A},|y|_{\mathbf A}^{-1}\}
$$

after reduction. This height deliberately omits the scalar determinant direction because that direction has been divided out in $X_G$. On $G(F)\backslash G(\mathbf A)$ one must also control the center. For example, one may use the adelic matrix height

$$
\|g\|_G=
\prod_v\max\left\{1,|g_{ij}|_v,|(g^{-1})_{ij}|_v:
1\le i,j\le2\right\}.
$$

The product is finite because almost every local matrix is integral with integral inverse. After reduction, $\|g\|_G$ is polynomially comparable to a product of a height in the scalar determinant direction and $\operatorname{ht}_X(g)$. Different standard choices are polynomially comparable, so moderate growth does not depend on this particular formula.

### 2.5 A lattice model for the cusp

Over $F=\mathbf Q$, the quotient can be visualized through lattices. A matrix in $G(\mathbf A)$ determines, after rational change of basis and scalar homothety, an adelic rank-two lattice. In the real component, the class of

$$
\begin{pmatrix}y^{1/2}&xy^{-1/2}\\0&y^{-1/2}\end{pmatrix}
$$

has one increasingly short direction as $y\to\infty$. The unipotent coordinate $x$ is periodic, while $y$ escapes every compact subset.

For a general number field, ideal classes give finitely many lattice genera and units identify logarithmic directions, but a ratio of successive minima can still become arbitrarily large. A bounded-determinant subset of $X_G$ is relatively compact when the corresponding lattices have a uniform lower bound on their shortest nonzero vector at all embeddings. The cusp is precisely the failure of that bound.

This model also explains the constant term geometrically. Averaging over $N(F)\backslash N(\mathbf A)$ forgets the position of the long basis vector relative to the short one and retains the asymptotic contribution of the degenerating lattice shape.

## 3. Automorphic forms and central characters

### 3.1 Why analytic and finiteness conditions coexist

Left invariance under $G(F)$ alone permits far too many functions. One could prescribe arbitrary data on a fundamental set, with no local regularity and no manageable representation generated by translations. The definition of an automorphic form combines analytic control at infinity with algebraic finiteness under compact groups and infinitesimal operators. Each clause solves a separate problem.

Let $\mathfrak g_\infty$ be the complexified Lie algebra of $G(F_\infty)$ and $\mathcal Z(\mathfrak g_\infty)$ the center of its enveloping algebra. A complex-valued function $\phi$ on $G(\mathbf A)$ is an **automorphic form** if:

1. $\phi(\gamma g)=\phi(g)$ for every $\gamma\in G(F)$;
2. $\phi$ is smooth in the archimedean variables and locally constant in the finite variables;
3. some compact open $U\subset G(\mathbf A_f)$ fixes $\phi$ on the right;
4. the span of $R(K_\infty)\phi$ is finite dimensional;
5. the span of $\mathcal Z(\mathfrak g_\infty)\phi$ is finite dimensional;
6. $\phi$ and every right-invariant differential derivative $D\phi$ have moderate growth: for each $D$ there are constants $C_D,N_D$ such that

$$
|D\phi(g)|\le C_D\|g\|_G^{N_D}
$$

on a reduction-theoretic fundamental set for $G(F)\backslash G(\mathbf A)$. If a central quasi-character has been fixed, its prescribed growth in the scalar direction may instead be removed by a norm twist; for a unitary central character the remaining estimate is exactly a polynomial estimate in $\operatorname{ht}_X$ on $X_G$.

The derivative form of moderate growth is often called uniform moderate growth. It is the stable condition under right translation and differential operators. Merely bounding $\phi$ itself would not control the representation it generates.

Conditions 3 and 4 are not smoothness. At a finite place, local constancy of one function already gives an open stabilizer, but a common compact-open stabilizer across the restricted product is the finite-level condition. At infinity, smoothness does not imply $K_\infty$-finiteness: a generic smooth function on a circle has infinitely many Fourier modes. The $K_\infty$-finite and $\mathcal Z(\mathfrak g_\infty)$-finite conditions select the representation-theoretic vectors inside the analytic space.

### 3.2 Fixed central character

Let $\omega:F^\times\backslash\mathbf A^\times\to\mathbf C^\times$ be a Hecke character. An automorphic form has **central character $\omega$** if

$$
\phi(zg)=\omega(z)\phi(g)
\qquad(z\in Z(\mathbf A)).
$$

The triviality of $\omega$ on $F^\times$ is forced: a scalar rational matrix belongs both to $G(F)$ and to $Z(\mathbf A)$. If these two transformation laws are imposed with a character not trivial on $F^\times$, the only form is zero.

Every continuous Hecke character admits a unique expression

$$
\omega=\omega_0|\cdot|_{\mathbf A}^{t}
$$

with $\omega_0$ unitary and $t\in\mathbf R$ when the absolute value of $\omega$ is positive real; in general one separates the real part of its exponent. Twisting a form by $|\det|_{\mathbf A}^{-t/2}$ reduces many analytic questions to unitary central character. The factor $1/2$ occurs because $\det(zI_2)=z^2$.

For unitary $\omega$, the norm

$$
\|\phi\|^2=\int_{X_G}|\phi(g)|^2\,dg
$$

is well defined: $|\phi(zg)|=|\phi(g)|$. For a nonunitary central character this expression does not descend to $X_G$, which is why unitarity is not an aesthetic restriction in spectral theory.

### 3.3 Smooth automorphic representations

Right translation preserves all six conditions and the central character. The resulting space $\mathcal A(G,\omega)$ is a module for

$$
G(\mathbf A_f)\times(\mathfrak g_\infty,K_\infty).
$$

An **automorphic representation** is an irreducible subquotient of this module. A **cuspidal automorphic representation** will mean an irreducible subrepresentation of its cuspidal part; in the cuspidal spectrum subquotient and subrepresentation cause no ambiguity because the Hilbert decomposition is discrete.

This definition deliberately keeps the smooth vectors visible. The full right regular representation on an $L^2$ space is a unitary Hilbert representation. Its smooth, $K_\infty$-finite, finite-level vectors are the automorphic forms that support Hecke operators and Fourier expansions. Moving between these two categories is legitimate but never silent.

### 3.4 Examples and failures

The constant function is an automorphic form of trivial central character. It is smooth, finite at every level, and of moderate growth. It is not cuspidal, as its constant term will equal itself.

If $\chi$ is a Hecke character, then

$$
g\longmapsto\chi(\det g)
$$

is one dimensional and has central character $\chi^2$. It again fails cuspidality. This example explains why central character alone does not determine an automorphic representation: many nonisomorphic $\chi$ can have the same square.

At the opposite extreme, take an arbitrary measurable function on a fundamental domain and extend it by left invariance. It may lie in $L^2$, but it need not be smooth, finite-level, or generate an admissible module. Spectral theory begins on the Hilbert space, while automorphic representation theory extracts its smooth finite vectors.

### 3.5 Analytic vectors and algebraic normalizations

Three spaces attached to one cuspidal constituent should be distinguished. The Hilbert representation contains all square-integrable vectors in the closed irreducible summand. Its smooth vectors have smooth archimedean orbit maps and locally constant finite-adelic orbit maps. Its automorphic-form vectors are additionally $K_\infty$-finite, finite-level, and finite under the infinitesimal center.

The last space is dense in the Hilbert representation. At finite places, convolve with normalized characteristic functions of shrinking compact opens. At infinity, convolve with smooth approximate identities and project to finitely many $K_\infty$-types. These operations converge strongly to the identity, commute with left $G(F)$-invariance, and preserve cuspidality because constant term commutes with right convolution.

An algebraic normalization is different again. It twists the group action by a real norm power; it does not merely select a dense subspace. Consequently a holomorphic eigenform can have algebraically normalized Hecke eigenvalues while its unitary realization has those eigenvalues divided by explicit powers of $q_v$.

### 3.6 A convention and hypothesis ledger

Before using the definition, it is helpful to record what depends on which hypothesis.

| assertion                                                  | required input                                                                                              |
| ---------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| right translation preserves the space of forms             | uniform moderate growth and finite generation under the indicated operators                                 |
| the $L^2$ norm descends through the center                 | unitary central character                                                                                   |
| finite-level vectors have a common compact-open stabilizer | the finite-level clause, not local constancy alone                                                          |
| archimedean type spaces are finite dimensional             | $K_\infty$-finiteness and admissibility                                                                     |
| cusp forms are rapidly decreasing                          | automorphy, uniform moderate growth, finiteness, and vanishing constant terms                               |
| the cuspidal spectrum is discrete                          | unitary realization, reduction theory, and cuspidal compactness                                             |
| algebraic Hecke eigenvalues                                | an independently defined arithmetic rational structure, not spectral finite dimensionality over $\mathbf C$ |

The coefficient field in the analytic theory is $\mathbf C$. Local smooth representations at
finite places are algebraic complex vector spaces; at infinity one works with admissible
$(\mathfrak g_v,K_v)$-modules and their smooth or unitary globalizations. The phrase
$\pi=\otimes_v'\pi_v$ therefore combines different local categories. It means that the
$K_\infty$-finite, finite-adelic-smooth vectors form the algebraic restricted tensor product and
that, in the unitary case, its Hilbert completion is the global irreducible summand.

All absolute values use the product-formula normalization. At a complex place,

$$
|z|_v=|z|_{\rm usual}^2.
$$

At a finite place, $|\varpi_v|_v=q_v^{-1}$. These choices make
$|\det g|_{\mathbf A}$ trivial on $G(F)$ and make conjugation by
$\operatorname{diag}(a,d)$ scale additive Haar measure on $N(\mathbf A)$ by
$|a/d|_{\mathbf A}$. The same normalization later produces the half-modulus
$|a/d|_v^{1/2}$ in normalized induction. Product formula, parabolic modulus, and Satake
half-powers are therefore parts of one convention, not three unrelated choices.

The action convention is equally important:

$$
(R(h)\phi)(g)=\phi(gh).
$$

With it, convolution acts by

$$
R(f)\phi(g)=\int_{G(\mathbf A)}f(h)\phi(gh)\,dh.
$$

If a classical slash operator is written using $g^{-1}$, its nebentype on $K_0$ appears inverted
relative to this right action. The representation and the classical function are unchanged; only
the bookkeeping of the character changes. Sections 11.3 and 13.1 consistently use the right-action
convention.

Finally, “automorphic representation” can mean an irreducible subquotient of all automorphic
forms, while “cuspidal automorphic representation” here means an irreducible summand of the
cuspidal Hilbert space. The latter is automatically unitary in the normalization presently used,
occurs discretely, and admits a faithful Whittaker model. A nonunitary algebraic normalization is
a norm twist of this unitary object. Keeping the unitary object primary prevents a field-valued
Hecke normalization from being inserted into an $L^2$ statement where its central character
would no longer have modulus one.

## 4. Constant terms and cuspidality

### 4.1 Fourier analysis along the unipotent quotient

The noncompact cusp is controlled by the unipotent radical $N$. Because

$$
N(F)\backslash N(\mathbf A)\cong F\backslash\mathbf A
$$

is compact, one can Fourier expand any sufficiently regular automorphic form along it. The zeroth Fourier coefficient is the **constant term**

$$
\phi_N(g)=\int_{F\backslash\mathbf A}\phi(n(x)g)\,dx.
$$

The integral converges because its domain is compact. It is invariant under left $N(\mathbf A)$ and encodes the part of $\phi$ that can persist far into the diagonal cusp.

An automorphic form is **cuspidal** if

$$
\phi_N(g)=0\qquad\text{for every }g\in G(\mathbf A).
$$

For $\mathrm{GL}_2$, the standard Borel is the only proper parabolic up to conjugacy, so this single condition is the full cuspidality condition. Requiring only $\phi_N(1)=0$ would be inadequate: right translation gives $(R(g)\phi)_N(1)=\phi_N(g)$, and the cuspidal space must be stable under the global group.

### 4.2 What cuspidality removes

Reduction theory shows that the leading asymptotic term of an automorphic form in a cusp is its constant term. When this term vanishes, the remaining nontrivial Fourier modes oscillate along the compact quotient $F\backslash\mathbf A$. Repeated integration by parts at infinity and finite Fourier orthogonality then force rapid decay in the height variable.

**Theorem 4.1 (rapid decay of cusp forms modulo the center).** Let $\phi$ be a cuspidal automorphic form with unitary central character. On every Siegel set in $X_G$ and for every integer $M\ge0$ and right-invariant differential operator $D$, there is a constant $C_{D,M}$ such that

$$
|D\phi(g)|\le C_{D,M}\operatorname{ht}_X(g)^{-M}.
$$

For a nonunitary central quasi-character, first remove its real norm power as in Section 3.2; the same estimate then holds for the normalized form, while the original form retains the prescribed scalar norm factor. Thus rapid decay concerns escape toward the parabolic cusp, not arbitrary escape along the center.

**Proof strategy.** At fixed finite level, the adelic unipotent fiber becomes a compact real torus. Cuspidality removes its zero mode. The diagonal height expands every invariant transverse derivative, so the torus Poincaré inequality gives an arbitrarily small cuspidal tail after enough derivatives. Sobolev embedding on fixed-height cylinders converts those tail estimates into pointwise rapid decay.

**Proof.** Fix a finite level for $\phi$ and one of the finitely many cusp charts supplied by
reduction theory. If $n=[F:\mathbf Q]$ and $H\ge H_0$ is the cusp height, the finite level turns
the adelic unipotent fiber into a compact real torus

$$
\mathcal Y=\Lambda\backslash F_\infty
$$

for one of finitely many lattices $\Lambda$. Cuspidality says that the zero Fourier coefficient
on every such fiber vanishes.

Reduction by the norm-one torus keeps the remaining diagonal directions in a compact set. As a
result, when the invariant transverse fields $X_1,\ldots,X_n$ are written in fixed torus
coordinates, every nonzero Fourier character has frequency at least $cH^{1/n}$ in one of those
fields. The constant $c>0$ is uniform because only finitely many cusp lattices occur. Fourier
inversion and integration by parts therefore give, for every $r$ and every ordinary torus
derivative $D_0$,

$$
\sup_{x\in\mathcal Y}|D_0\phi(n(x)g)|
\le C_{r,D_0}H^{-r/n}
\max_{|I|\le r+s}\sup_{x\in\mathcal Y}|X^I\phi(n(x)g)|,
\tag{4.1}
$$

where $s>n/2$ is a fixed Sobolev loss. Indeed each nonzero coefficient gains the inverse $r$th
power of its frequency, and the remaining series is summable after the extra $s$ derivatives.

There is one analytic point needed to use (4.1). The definition gives moderate growth derivative
by derivative, but $K_\infty$-finiteness and finiteness under the infinitesimal center upgrade it
to one common polynomial exponent on a fixed automorphic representation. To see this, cover each
logarithmic-height cylinder by uniformly bounded invariant charts. The finite set of
$K_\infty$-types and a positive elliptic combination of the infinitesimal-center operators give
an interior elliptic estimate that bounds every higher derivative on the middle cylinder by the
supremum of finitely many generating derivatives on a slightly larger cylinder. Those finitely
many derivatives have a common moderate-growth exponent $N$. Hence

$$
\sup_{x\in\mathcal Y}|X^I\phi(n(x)g)|\le C_IH^N
$$

for every $I$, with $N$ independent of $I$. Insert this in (4.1) and choose
$r>n(M+N)$. The result is

$$
|D\phi(g)|\ll_{D,M}H(g)^{-M}.
$$

The compact part of a Siegel set is harmless, and there are finitely many cusp charts. No
$L^2$ estimate has been used, so the rapid-decay theorem now implies square-integrability rather
than assuming it. $\square$

Consequently every cusp form of unitary central character is square integrable on $X_G$. Cuspidality does not make the quotient compact; it makes the function decay as if the missing boundary were infinitely far away.

### 4.3 A Fourier counterexample

Vanishing average in one chosen cusp coordinate is not enough without automorphy. The function $e^{2\pi ix}$ on a strip has zero average in $x$ but may grow exponentially in the height. Automorphy and the differential finiteness conditions link the variables tightly enough for zero constant term to imply rapid decay. This shows why cuspidality is powerful only inside the automorphic category.

For the constant function, $\phi_N=\phi$. For $\chi\circ\det$, the determinant is unchanged by $n(x)$, so again $\phi_N=\phi$. Thus all one-dimensional automorphic representations lie outside the cuspidal spectrum.

The counterexample separates a Fourier condition from a geometric conclusion. Zero average is a
statement on each cross-section; rapid decay compares different cross-sections as height changes.
The automorphic differential equations and rational identifications provide that comparison.
Without them, the cusp condition would be too weak to support the compactness argument of Chapter
5.

### 4.4 Orthogonality to induced behavior

The constant-term operator is adjoint to forming functions from the Borel. Schematically, unfolding gives

$$
\langle\phi,E(f)\rangle
=\int_{B(F)\backslash G(\mathbf A)}\phi_N(g)\overline{f(g)}\,dg,
$$

where $E(f)$ is an Eisenstein series in a region of convergence. Hence cusp forms are orthogonal to the continuous spectrum generated from the Borel. This identity explains the terminology: the cusp condition is not an arbitrary boundary condition but the projection away from proper-parabolic induction.

### 4.5 Poincaré series as a source of cusp forms

Cuspidality can be built into a Poincaré series, but compact support by itself is not enough: one
needs a seed with zero local Jacquet module. Choose a finite place $v_0$, a supercuspidal
representation $\sigma$ of $G(F_{v_0})$ with trivial central character, and a
compactly supported-modulo-center matrix coefficient $f_{v_0}$ of $\sigma$. Complete it to a
factorizable smooth function $f=\otimes_vf_v$ on $G(\mathbf A)$, compactly supported modulo
$Z(\mathbf A)$ and invariant under the center. Form

$$
P_f(g)=\sum_{\gamma\in Z(F)\backslash G(F)}f(\gamma g).
$$

Discreteness of $G(F)$ and compactness of the support modulo the center make the sum locally
finite, and left $G(F)$-invariance is immediate. To calculate a proper-parabolic constant term,
insert the sum and unfold it by the two Bruhat cells. Every resulting orbital integral contains,
at $v_0$, an integral of a translate of $f_{v_0}$ along the unipotent radical of a proper
parabolic. Such an integral is zero: if one were nonzero, the matrix coefficient would define a
nonzero functional on the Jacquet module of $\sigma$, contradicting supercuspidality. Hence every
proper constant term of $P_f$ vanishes.

The series can be made nonzero. Choose $f_{v_0}(1)\ne0$. The support of this local matrix
coefficient is compact modulo the center. Discreteness of $G(F)/Z(F)$ in
$G(\mathbf A)/Z(\mathbf A)$ then lets us shrink the compact supports at the remaining places so
that the resulting global support meets no nonidentity rational translate at the identity. Thus
$P_f(1)=f(1)\ne0$.

At this stage $P_f$ is a nonzero smooth cuspidal $L^2$-vector; a compactly supported
archimedean seed need not be finite under the infinitesimal center and therefore need not itself
be an automorphic form in the narrower definition of Section 3.1. The discrete decomposition of
Theorem 5.1 below gives a nonzero projection of $P_f$ to some irreducible cuspidal summand.
Choose a nonzero smooth vector there that is $K_\infty$-finite and fixed by a compact open
subgroup at the finite adeles. It is automatically finite under the infinitesimal center and is
a cuspidal automorphic form. Its Fourier expansion has a nonzero Whittaker coefficient, since
otherwise Theorem 8.1 would reconstruct it as zero. This supplies the cuspidal and generic
objects used later without confusing a Poincaré seed with a finite automorphic vector.

### 4.6 Equivalent forms of the cusp condition

For rank two, several formulations of cuspidality coincide. Stating the equivalence prevents a
later argument from silently changing the quantifier on $g$.

**Proposition 4.2.** Let $\phi$ be an automorphic form on $G(\mathbf A)$. The following are
equivalent.

1. $\phi_N(g)=0$ for every $g\in G(\mathbf A)$.
2. The constant term of every right translate $R(g)\phi$ vanishes at the identity.
3. The constant term of $\phi$ along every proper $F$-parabolic subgroup vanishes everywhere.
4. At a fixed finite level, every classical component of $\phi$ has zero constant Fourier
   coefficient at every cusp.

**Proof.** Since

$$
(R(g)\phi)_N(1)=\int_{F\backslash\mathbf A}\phi(n(x)g)\,dx=\phi_N(g),
$$

conditions 1 and 2 are identical. Every proper $F$-parabolic in $\mathrm{GL}_2$ stabilizes an
$F$-rational line in $F^2$. The group $G(F)$ acts transitively on these lines, so every such
parabolic is $\gamma B\gamma^{-1}$ for some $\gamma\in G(F)$. Changing variables and using left
$G(F)$-invariance turns its constant term into the standard one at a right translate. This proves
the equivalence with 3.

At fixed level, reduction theory decomposes the adelic quotient into finitely many arithmetic
quotients at infinity. A cusp of one component is represented by a rational parabolic together
with a finite-adelic translate. Averaging the corresponding classical function over the
unipotent period is exactly the adelic constant term at that translate. Hence 3 and 4 are
equivalent. $\square$

The proposition explains why checking only the standard cusp of only one connected component is
insufficient. Over a field of nontrivial class number, different determinant components can have
cusps not visible on the chosen component. Even over $\mathbf Q$, a form on $\Gamma_0(N)$ can
have zero constant term at infinity and a nonzero constant term at another cusp.

There is also an $L^2$ formulation. For a smooth finite-type vector, condition 1 is equivalent to
orthogonality to every incomplete Eisenstein series formed from a compactly supported smooth
section on $B(F)\backslash G(\mathbf A)$. One implication is the unfolding identity of Section
4.4. For the converse, if $\phi_N$ is nonzero near some point, choose a section supported in a
small neighborhood on which its inner product with $\phi_N$ is nonzero; unfolding gives a
nonzero pairing. Thus the cusp space is exactly the orthogonal complement of the parabolically
generated channel inside the smooth spectrum.

For $\mathrm{GL}_2$, the Fourier expansion makes the condition especially transparent:

$$
\phi(n(x)g)=\phi_N(g)+
\sum_{\alpha\in F^\times}W_\phi
\left(\begin{pmatrix}\alpha&0\\0&1\end{pmatrix}g\right)
\psi(\alpha x).
$$

Cuspidality deletes exactly the zero orbit in the character group of $F\backslash\mathbf A$.
The diagonal torus is transitive on the remaining rational characters, so one Whittaker orbit
contains all nonzero coefficients. In higher rank there are several proper parabolics and several
nonzero unipotent orbits; the rank-two equivalence is correspondingly special.

## 5. The cuspidal spectrum

### 5.1 The Hilbert space with central character

Fix a unitary Hecke character $\omega$. Let

$$
L^2(G(F)\backslash G(\mathbf A),\omega)
$$

be the measurable functions satisfying

$$
f(\gamma zg)=\omega(z)f(g)
$$

and square integrable over $X_G$. Define $L^2_{\mathrm{cusp}}(\omega)$ as the closed subspace whose constant term vanishes almost everywhere. Smooth cuspidal automorphic forms are dense in it.

Right translation is unitary:

$$
\|R(h)f\|^2
=\int_{X_G}|f(gh)|^2\,dg
=\|f\|^2,
$$

because $G(\mathbf A)$ is unimodular. Notice that left translation would conflict with the left $G(F)$ quotient; the right action is forced by the geometry.

### 5.2 Why the cuspidal spectrum is discrete

Rapid decay converts noncompactness into compactness of the relevant analytic embeddings. At fixed finite level, fixed $K_\infty$-types, and bounded infinitesimal character, cusp forms satisfy uniform Sobolev estimates and vanish rapidly in every cusp. Rellich compactness on a truncated quotient and negligible tails together make the resolvent of a positive elliptic operator compact.

**Theorem 5.1 (discrete cuspidal decomposition).** There is a Hilbert direct sum

$$
L^2_{\mathrm{cusp}}(\omega)
\cong\widehat{\bigoplus}_{\pi}m(\pi)\,\pi,
$$

where $\pi$ runs over irreducible unitary representations of $G(\mathbf A)$ with central character $\omega$, each multiplicity $m(\pi)$ is finite, and only finitely many constituents occur with prescribed finite level, prescribed finite set of $K_\infty$-types, and bounded archimedean spectral parameter.

**Proof strategy.** First freeze level and compact type so that the problem lives on a finite union of locally symmetric quotients. A positive elliptic operator from the archimedean center controls derivatives. Cuspidal rapid decay prevents mass from escaping into the cusps. Compact resolvent gives a discrete eigenspace decomposition, and commuting right translations assemble the eigenspaces into irreducible representations.

**Proof.** Let $U\subset G(\mathbf A_f)$ be compact open and let $\tau$ be a finite set of
$K_\infty$-types. On the $U$-fixed, $\tau$-isotypic cuspidal subspace, choose a positive
elliptic combination $\Delta$ of Casimir and compact-direction operators. Local elliptic
estimates control a first Sobolev norm on compact truncations. In a cusp, the same mean-zero
torus spectral gap used in the proof of Theorem 4.1, now in its $L^2$ Poincaré form, gives the uniform
tail bound

$$
\|u\|_{L^2(H\ge Y)}
\le CY^{-1/[F:\mathbf Q]}\|u\|_{H^1(H\ge Y)}.
$$

This estimate is uniform on the $H^1$ unit ball and over the finitely many cusps. Rellich
compactness on a fixed truncation and uniform smallness of the tails therefore make the global
inclusion of the first cuspidal Sobolev domain into $L^2$ compact. Hence
$(1+\Delta)^{-1}$ is compact and has discrete spectrum with finite-dimensional eigenspaces.

The compact-convolution argument of Section 5.6 converts these typewise compact embeddings into
an actual Hilbert direct sum of irreducibles and proves finite multiplicity. The finite-dimensional
frozen eigenspaces give the stated local finiteness. $\square$

Later automorphic multiplicity one, proved from global Whittaker uniqueness, will imply $m(\pi)=1$. Strong multiplicity one is a different theorem: it recognizes a global representation from almost all local components and cannot by itself rule out two copies of the same representation. It would be circular to use automorphic multiplicity one here, since discreteness and finite multiplicity are analytic facts needed before the Whittaker argument can be applied to individual summands.

### 5.3 Admissibility of global constituents

Let $\pi$ occur in the cuspidal spectrum. For every compact open $U\subset G(\mathbf A_f)$ and irreducible $K_\infty$-type $\tau$, the space

$$
\operatorname{Hom}_{K_\infty}(\tau,\pi^U)
$$

is finite dimensional. Indeed it sits in a fixed-level cuspidal eigenspace for the infinitesimal character of $\pi_\infty$. Thus global spectral discreteness implies the admissibility needed to extract local components.

There is an important asymmetry. At a finite place, admissibility means finite-dimensional invariants under every compact open subgroup. At infinity, it means finite multiplicity of each maximal-compact type in the smooth representation. Both express finite complexity, but the definitions reflect the different topologies.

### 5.4 The residual boundary

The orthogonal complement of the cuspidal space is not empty. Characters $\chi\circ\det$ occur discretely when unitary, and residues of Eisenstein series can also produce square-integrable representations. For $\mathrm{GL}_2$, the residual irreducible constituents are one dimensional: they are representations $\chi\circ\det$ satisfying $\chi^2=\omega$. There may be several such $\chi$, or none.

The continuous spectrum is built from unitary normalized principal series. Its vectors have nonzero constant terms and are parametrized continuously along an imaginary axis. We need this boundary only to prevent a false identification:

$$
\text{discrete automorphic}\ne\text{cuspidal automorphic}.
$$

Every cuspidal representation is discrete, but the determinant characters are discrete and not cuspidal.

### 5.5 Compact-open projectors

For compact open $U\subset G(\mathbf A_f)$, put

$$
e_U=\operatorname{vol}(U)^{-1}\mathbf1_U.
$$

Then $R(e_U)$ is the orthogonal projector onto $U$-fixed vectors. If $U'\subset U$, one has $e_U*e_{U'}=e_U=e_{U'}*e_U$. At infinity, convolution with $\dim(\tau)\overline{\operatorname{tr}\tau(k)}$ projects to a maximal-compact type $\tau$.

Combining these projectors isolates the finite-dimensional shadows used in the discreteness proof. On one irreducible constituent, the trace of $R(e_U)$ is $\dim\pi_f^U$. This makes clear why an infinite-dimensional representation nevertheless yields finite Hecke matrices at every fixed level.

### 5.6 Atomicity and finite multiplicity in detail

The final sentence of the proof of Theorem 5.1 conceals a subtle point. Compact resolvent at
fixed level and compact type must be converted into a representation-theoretic direct sum; it is
not enough to invoke an unspecified direct-integral decomposition. The compact-convolution
argument gives that conversion directly.

Let $\mathcal D$ be the convolution algebra generated by tensors $f_\infty\otimes f_f$ for
which $f_\infty$ is smooth, compactly supported, and finite under left and right
$K_\infty$-translation, while $f_f$ is compactly supported, locally constant, and bi-invariant
under some compact open subgroup. On the cuspidal Hilbert space, $R(f)$ has image in one finite
level and finitely many $K_\infty$-types. Differentiating under the integral gives

$$
\|D R(f)u\|_2\le \|D_Lf_\infty\|_1\|f_f\|_1\|u\|_2.
\tag{5.1}
$$

Thus $R(f)$ maps boundedly into the first cuspidal Sobolev space at those fixed types. The
compact cuspidal embedding used in Section 5.2 shows that its inclusion back into $L^2$ is
compact. Hence every $R(f)$ is compact.

Let

$$
\mathfrak A=\overline{R(\mathcal D)}^{\|\cdot\|}.
$$

Then $\mathfrak A$ is a separable $C^*$-algebra of compact operators. It acts nondegenerately,
because $\mathcal D$ contains an $L^1$ approximate identity whose right-convolution operators
converge strongly to the identity.

We use the elementary structure theorem for such an algebra. If $0\ne a\in\mathfrak A$ is
positive, a continuous function supported away from zero produces by functional calculus a
nonzero finite-rank projection in $\mathfrak A$. A minimal projection exists in its
finite-dimensional corner. Group equivalent minimal projections and use the partial isometries
between them as matrix units. A maximal orthogonal family of the resulting elementary ideals has
zero annihilator; otherwise the same construction in the annihilator would produce another
minimal projection. Separability makes the family countable. Therefore

$$
L^2_{\rm cusp}(\omega)
\cong\widehat\bigoplus_\rho M_\rho\otimes\mathcal H_\rho,
\tag{5.2}
$$

where $\mathfrak A$ acts on each summand as
$1_{M_\rho}\otimes\mathcal K(\mathcal H_\rho)$. Each $M_\rho$ is finite dimensional: if it
were infinite dimensional, $1_{M_\rho}\otimes b$ would fail to be compact for every nonzero
finite-rank $b$.

Finally, invariant subspaces for $\mathfrak A$ are exactly invariant subspaces for
$G(\mathbf A)$. One direction follows by integration. Conversely, left translates of an
approximate identity belong to $\mathfrak A$: although a translate need not remain finite under
the originally chosen left $K_\infty$-action, Peter--Weyl truncation on the two compact sides
approximates it in $L^1$ by elements of $\mathcal D$, and the integrated representation is
$L^1$-contractive. Moreover they satisfy

$$
R(L_g\eta_j)u\longrightarrow R(g)u,
$$

so an $\mathfrak A$-invariant closed subspace is group invariant. The irreducible modules in
(5.2) are therefore precisely irreducible unitary group representations, and equivalence for
the algebra is equivalence for the group. This proves atomicity and finite automorphic
multiplicity without importing an unproved type-I decomposition. It does not prove
$\dim M_\rho=1$; that sharper statement requires the Whittaker argument of Chapter 9.

We have proved the precise form of Theorem 5.1:

$$
L^2_{\rm cusp}(\omega)
=\widehat\bigoplus_{\rho}M_\rho\otimes\mathcal H_\rho,
\qquad 1\le\dim M_\rho<\infty,
\tag{5.3}
$$

and every bounded window at fixed level and type receives contributions from only finitely many
$\rho$, counted with their multiplicities and intrinsic type dimensions.

Two false shortcuts are now visible. Finite volume does not force (5.3), because continuous
Eisenstein spectrum lives on the same finite-volume quotient. Nor does finite-dimensionality of
each local fixed space bound $M_\rho$: one could tensor an irreducible representation with an
infinite-dimensional trivial multiplicity space without changing any intrinsic local
admissibility. The global finite-rank spectral projector is what excludes both failures.

## 6. Restricted tensor products and local components

### 6.1 Why a global irreducible representation should factor

The adelic group is a restricted product, so a finite-level vector is fixed by $K_v$ at almost every finite place. One expects independent local actions to generate local representations and the original vector to be a tensor of local vectors. The word “restricted” is essential: an unrestricted algebraic tensor product would allow infinitely many factors to deviate simultaneously and would not carry a natural action of an adelic element.

Given representations $\pi_v$ and nonzero reference vectors $e_v\in\pi_v^{K_v}$ for almost every finite $v$, the restricted tensor product

$$
\bigotimes_v'\pi_v
$$

is the union, over finite sets $S$, of

$$
\left(\bigotimes_{v\in S}\pi_v\right)
\otimes\left(\bigotimes_{v\notin S}\mathbf Ce_v\right).
$$

If $g=(g_v)\in G(\mathbf A)$, then $g_v\in K_v$ almost everywhere, so $\pi_v(g_v)e_v=e_v$ almost everywhere and the componentwise action is defined.

### 6.2 Factorization theorem

**Theorem 6.1 (factorization of a cuspidal constituent).** Let $\pi$ be an irreducible cuspidal automorphic representation of $G(\mathbf A)$. Then there are uniquely determined irreducible admissible local representations $\pi_v$ such that

$$
\pi^{\mathrm{fin}}\cong
\pi_\infty^{K_\infty\text{-fin}}\otimes
\bigotimes_{v<\infty}'\pi_v.
$$

For almost every finite $v$, $\pi_v^{K_v}$ is one dimensional, and a choice of nonzero vector in each such line supplies the reference vectors. The unitary completion is the corresponding Hilbert restricted tensor product.

Here $\pi^{\mathrm{fin}}$ denotes the vectors that are $K_\infty$-finite and fixed by some compact open subgroup of $G(\mathbf A_f)$.

**Proof strategy.** Apply the product-group factorization theorem to the irreducible unitary
summand, then pass to its admissible smooth finite vectors. Compatibility as the finite set of
places grows and the one-dimensional spherical lines produce the restricted tensor product.
This route does not assume that an arbitrarily chosen global vector is already a pure tensor.

**Proof.** We first record the restricted-product factorization lemma. Let

$$
H=H_\infty\times\prod_{v<\infty}'(H_v,K_v)
$$

and let $\mathcal V$ be an irreducible unitary representation whose archimedean finite-vector
and nonarchimedean smooth module $V=\mathcal V^{\rm fin}$ is admissible. Then there are unique
irreducible admissible $V_v$, spherical with a one-dimensional $K_v$-fixed space for almost every
finite $v$, such that

$$
V\cong V_\infty\otimes\bigotimes_{v<\infty}'V_v.
$$

Here is the algebra behind the lemma. For a finite set $T$ containing the archimedean places, write

$$
H_T=\prod_{v\in T}H_v,
\qquad
H^T=\prod_{v\notin T}'(H_v,K_v).
$$

The product-group factorization theorem proved in Book 92, Section 3.3, and
recalled as Book 94, Theorem 2.2, applies to these admissible representations
of products of local reductive groups. It gives

$$
\mathcal V\cong\mathcal V_T\widehat\otimes\mathcal V^T
$$

with both factors irreducible. Its local type-I and admissibility hypotheses are part of that
proved theorem; scalarity of the joint commutant alone would not suffice for arbitrary groups.
Iterating inside the finite product and then taking finite vectors gives

$$
V_T\cong\bigotimes_{v\in T}V_v.
$$

If $T\subset T'$, factor $\mathcal V^T$ once more. Uniqueness in the product-group theorem, equivalently Schur's lemma applied to the two commuting factor actions, shows that the already extracted $V_v$ do not change. Thus the local factors are compatible as $T$ grows.

Choose a nonzero smooth vector. It is fixed by $K_v$ outside a finite set $S$. The compatible factorization of its cyclic span then gives $V_v^{K_v}\ne0$ for $v\notin S$. The spherical multiplicity-one theorem makes this line one dimensional; choose $0\ne e_v\in V_v^{K_v}$. Compatible finite tensor stages now give a nonzero equivariant map

$$
V_\infty\otimes\bigotimes_{v<\infty}'(V_v,e_v)
\longrightarrow V^{\rm fin}.
$$

The source is irreducible: a nonzero vector lies in a finite tensor stage, finite-product irreducibility generates that stage, and acting at one new place generates the next. The image contains a cyclic smooth vector and is therefore all of $V^{\rm fin}$; irreducibility makes the kernel zero. This proves existence. If a second restricted factorization existed, currying an isomorphism while fixing nonzero vectors in every factor except one would produce a nonzero intertwiner between the two factors at that place. Schur's lemma makes it an isomorphism, proving uniqueness place by place.

Apply the lemma to the irreducible finite-vector module of the cuspidal constituent $\pi$. Admissibility was proved in Section 5.3. We obtain the displayed factorization and one-dimensional spherical lines at almost every finite place. Completing the algebraic tensor product with the product inner product gives the Hilbert restricted tensor product, because the automorphic realization is unitary. $\square$

The proof explains both factorization and almost-everywhere unramifiedness. It is not enough to say that the group is a restricted product: irreducibility, admissibility, and the one-dimensional spherical lines are the decisive representation-theoretic inputs.

### 6.3 Finite and archimedean local components

At a finite place, $\pi_v$ is an irreducible admissible smooth representation of $\mathrm{GL}_2(F_v)$. It is therefore a principal-series constituent, a special representation, a supercuspidal representation, or one dimensional. A cuspidal global representation is infinite dimensional and generic, and its finite local components are generic; hence no finite component is one dimensional. The generic local possibilities are irreducible principal series, special representations, and supercuspidals.

The classification sentence uses only the rank-one Jacquet alternative, not a classification of primitive supercuspidals. If the normalized Jacquet module $(\pi_v)_N$ vanishes, then $\pi_v$ is supercuspidal by definition. If it does not vanish, it has a character quotient $\chi_1\otimes\chi_2$ because the torus is abelian and the Jacquet module is finite dimensional. Normalized Frobenius reciprocity gives a nonzero map between $\pi_v$ and $I(\chi_1,\chi_2)$ in the appropriate direction. Irreducibility makes $\pi_v$ an irreducible constituent of that principal series. Away from the two reducibility ratios it is the irreducible principal series itself; at a reducibility ratio the constituents are a one-dimensional determinant character and a generic special representation. Global genericity excludes the first. This proves the stated list without attaching an inducing datum to an arbitrary supercuspidal representation.

At an archimedean place, $\pi_v$ is an irreducible admissible representation of $\mathrm{GL}_2(\mathbf R)$ or $\mathrm{GL}_2(\mathbf C)$, with a unitary completion in the $L^2$ normalization. Principal series, limits, and discrete series may occur according to the infinity type. Holomorphic modular forms select lowest-weight discrete series at real places; general Maass forms usually select principal series.

At a real place, normalized principal series are induced from characters

$$
x\longmapsto\operatorname{sgn}(x)^{\epsilon_i}|x|^{s_i}.
$$

Unitary principal series have purely imaginary relative exponent; a bounded real relative exponent gives the complementary range. Discrete series are indexed by a lowest or highest compact weight, together with a central twist. The holomorphic representation $D_k^{\rm hol}$ has lowest $\mathrm{SO}_2(\mathbf R)$-weight $k$, while its antiholomorphic companion has highest weight $-k$. A representation of the full group $\mathrm{GL}_2(\mathbf R)$ must also specify how the negative-determinant component relates these pieces.

At a complex place, the maximal compact is $U(2)$ and irreducible admissible representations relevant here arise as constituents of normalized induction from characters of $\mathbf C^\times$. There is no holomorphic discrete series analogous to the real upper-half-plane case. An algebraic infinity type is encoded by integral powers $z^p\bar z^q$ after a norm twist; a general unitary infinity type can have continuous imaginary exponents.

The finite and infinite notions of “unramified” are consequently not identical pieces of terminology. At a finite place it means a $K_v$-fixed line. At infinity one instead records an infinitesimal character and maximal-compact types. The analytic conductor later packages both, but the ideal conductor of Chapter 11 has only finite-place exponents.

Global cuspidality does **not** force $\pi_v$ to be supercuspidal at any particular place. For example, a level-one classical cusp form has spherical principal-series components at every finite prime. The adjective “cuspidal” lives globally in the vanishing constant term; “supercuspidal” is a local Jacquet-module condition.

### 6.4 Almost-everywhere spherical vectors

For $v$ outside a finite set, $\pi_v^{K_v}$ is a line. The normalized vector $e_v$ is determined only up to scalar. A pure tensor $\otimes_vW_v$ or $\otimes_vf_v$ is therefore meaningful only after choosing normalizations such as $W_v(1)=1$ in a Whittaker model. Changing $e_v$ at infinitely many places by arbitrary scalars changes the restricted tensor product datum and can destroy convergence of factorizable integrals.

At a ramified place, $K_v$-invariants may vanish while invariants under a smaller compact open are nonzero. The conductor will identify the smallest $K_1$-level with a distinguished line. Thus spherical vectors and newvectors are the same organizing idea at different depths: both provide canonical local anchors for a global tensor product.

Almost-everywhere sphericality is the representation-theoretic shadow of the adelic restricted
product. It is what makes a global Euler product have standard factors outside a finite set and
what permits a Hecke eigensystem to be recorded by finitely supported convolution operators. The
exceptional finite set is not canonical—one may always enlarge it—but the statement that some
such set exists is intrinsic.

### 6.5 Central characters and reference vectors

Under factorization, Schur's lemma gives

$$
\omega_\pi=\prod_v\omega_{\pi_v}.
$$

At almost every finite place, $\omega_{\pi_v}$ is unramified because scalar units fix the spherical vector. For $z=(z_v)\in\mathbf A^\times$, only finitely many local factors act nontrivially on the reference tensor, so the product is defined. Its triviality on $F^\times$ follows from automorphy.

The local characters are not freely specifiable. A family unramified almost everywhere gives an adelic character only when the product is continuous and trivial on $F^\times$. This global condition contains both parity at the real places and compatibility of norm exponents.

Changing $e_v$ by $c_ve_v$ at finitely many places gives a canonically isomorphic restricted tensor product. An infinite rescaling is not harmless unless the product of scalars is controlled. Whittaker normalization $W_v(1)=1$ at almost every place removes this ambiguity.

### 6.6 Invariant spaces and restricted tensor products

Factorization becomes useful only when it converts a global level condition into finitely many
local conditions. Let

$$
U_f=\prod_{v<\infty}U_v\subset G(\mathbf A_f)
$$

be compact open, with $U_v=K_v$ for almost every $v$. For a restricted tensor product
$\pi_f=\otimes_{v<\infty}'\pi_v$, there is a natural map

$$
\bigotimes_{v<\infty}\pi_v^{U_v}\longrightarrow \pi_f^{U_f}.
\tag{6.1}
$$

Only finitely many factors on the left differ from the reference spherical lines, so this is an
ordinary finite tensor product in substance. The point is that (6.1) is an isomorphism.

**Proposition 6.2 (factorization of compact invariants).** With the preceding notation,

$$
\pi_f^{U_f}\cong\bigotimes_{v<\infty}\pi_v^{U_v}.
\tag{6.2}
$$

In particular, the left side is finite dimensional and its dimension is the product of the local
dimensions.

**Proof strategy.** Averaging over a product compact open is the tensor product of the local
averaging projectors. On a finite tensor stage this is elementary linear algebra. Every global
smooth vector belongs to such a stage, so no vector can hide in an infinite tail.

**Proof.** Give each $U_v$ probability Haar measure and write

$$
e_{U_v}=\operatorname{vol}(U_v)^{-1}\mathbf1_{U_v}.
$$

Choose a finite set $S$ containing every $v$ for which $U_v\ne K_v$, every ramified place of
$\pi$, and all places at which a given vector differs from its reference component. On the stage

$$
V_S=\bigotimes_{v\in S}\pi_v\otimes
\bigotimes_{v\notin S}\mathbf Ce_v,
$$

the averaging operator is

$$
\pi_f(e_{U_f})=
\bigotimes_{v\in S}\pi_v(e_{U_v})
\otimes\bigotimes_{v\notin S}\operatorname{id}_{\mathbf Ce_v}.
$$

The image of a tensor product of idempotents is the tensor product of their images. Thus the
$U_f$-fixed vectors in $V_S$ are exactly the tensors of local $U_v$-fixed vectors. Taking the
directed union over $S$ proves (6.2). Local admissibility makes the finitely many exceptional
factors finite dimensional. $\square$

The same argument applies after selecting an archimedean compact type $\tau$. If
$\tau=\otimes_{v\mid\infty}\tau_v$, then the $\tau$-multiplicity space is the tensor product of
the local $\tau_v$-multiplicity spaces. Hence a finite-level, finite-type part of the cuspidal
spectrum has the concrete form

$$
\bigoplus_{\pi}
\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty)
\otimes\bigotimes_{v<\infty}\pi_v^{U_v}.
\tag{6.3}
$$

The sum is discrete by Chapter 5 and multiplicity free by Chapter 9. Formula (6.3) is the bridge
between spectral decomposition and finite Hecke modules.

There is a useful converse test. Suppose $\pi_f^{U_f}\ne0$. Then every local fixed space
$\pi_v^{U_v}$ is nonzero. Indeed, if one local factor vanished, the right side of (6.2) would
vanish. Thus a global vector of level $U_f$ can exist only if every local component admits the
corresponding level. This apparently obvious assertion depends on factorization; it is not a
formal consequence of restricting an arbitrary global function to one local subgroup.

Finally, pure tensors span but need not exhaust the set of distinguished eigenvectors. If two
local fixed spaces have dimensions greater than one, a general global fixed vector is a sum of
pure tensors. A simultaneous eigenvector for a commutative subalgebra may nevertheless be
entangled across the exceptional places. The canonical pure tensor appears at minimal conductor,
where every finite local fixed space is a line. This is why newvectors, rather than arbitrary
fixed vectors, provide the cleanest global normalization.

### 6.7 The local families inside a global representation

The factorization theorem assigns a local representation at every place, but it imposes no rule
that all places belong to the same local family. A single cuspidal representation can be
spherical principal series at almost every prime, special at some level primes, and
supercuspidal at others. Its archimedean factors can be discrete series at real places or
principal series at complex places. Global coherence is expressed by the common central
character, Whittaker model, and Hecke system, not by a uniform family label.

At a finite place the generic possibilities and their elementary invariants are as follows.

| local component               | genericity condition  | conductor exponent                     | standard factor |
| ----------------------------- | --------------------- | -------------------------------------- | --------------- |
| $I(\chi_1,\chi_2)$            | $\chi_1\chi_2^{-1}\ne | \cdot                                  | ^{\pm1}$        |
| $\operatorname{St}\otimes\mu$ | always generic        | $1$ if $a(\mu)=0$, otherwise $2a(\mu)$ | $L(s+1/2,\mu)$  |
| supercuspidal $\sigma$        | intrinsic             | $a(\sigma)\ge2$                        | $1$             |

The table uses the unitary representation normalization. In the principal-series row, a ramified
character contributes the factor $1$ to its degree-one local $L$-function, so the displayed
product can have degree zero, one, or two. The assertion for every supercuspidal, including a
primitive wild one for which no parameter has been invoked, follows directly from the zeta-ideal
definition. Its Kirillov functions are compactly supported in $F_v^\times$ because the Jacquet
module is zero. Their Mellin integrals are Laurent polynomials in $q_v^{-s}$,
and translating a compactly supported unit-shell function produces every Laurent monomial. The
generated fractional ideal is therefore the whole Laurent polynomial ring, whose normalized
generator is $1$. In parameterized supercuspidal classes this agrees with the inertia-invariant
definition, but the parameter is a compatibility check rather than an input to the general row.

The conductor and standard factor do not classify the local representation. For instance, let
$\chi_1$ and $\chi_2$ both have conductor one. The principal series has exponent two and standard
factor $1$. A depth-zero supercuspidal also has exponent two and standard factor $1$. They are
distinguished by their local type, by their Jacquet modules, and by the action of deeper Hecke
algebras. Thus the pair

$$
(a(\pi_v),L(s,\pi_v))
$$

is useful but incomplete.

At exponent one, more can be said. If $\pi_v$ is infinite dimensional, generic, has unramified
central character, and $a(\pi_v)=1$, the principal-series formula cannot apply: a ramified
inducing character of exponent one would force the other character to have the same ramification
on the center if the product were unramified, giving total exponent at least two. A
supercuspidal has exponent at least two. Hence

$$
\pi_v\cong\operatorname{St}\otimes\mu
$$

with $\mu$ unramified. This is why squarefree level with unramified nebentype produces special
local factors.

At a real place, a holomorphic weight-$k$ form selects $D_k$ in unitary central normalization.
At a finite good place, the same global representation is normally an unramified principal
series. There is no contradiction: the discrete-series label refers to square integrability
modulo the real center, whereas finite-place sphericality refers to a hyperspecial fixed vector.
The restricted tensor product is designed precisely to assemble these different local
geometries.

## 7. Unramified Hecke data

### 7.1 Convolution and the fixed-level viewpoint

Let $v$ be finite, $K=K_v$, and normalize Haar measure by $\operatorname{vol}(K)=1$. The spherical Hecke algebra

$$
\mathcal H(G_v,K)=C_c(K\backslash G_v/K)
$$

acts on $\pi_v^K$ by

$$
\pi_v(h)w=\int_{G_v}h(g)\pi_v(g)w\,dg.
$$

If $KgK=\coprod_i g_iK$, this is the finite sum $\sum_i\pi_v(g_i)w$. Globally, for $U=\prod_vU_v$, convolution by a pure tensor $\otimes_vh_v$, with $h_v=\mathbf1_{U_v}$ almost everywhere, acts on $U$-fixed automorphic forms. Operators at distinct places commute because their group elements occupy different factors.

This viewpoint separates two objects that are often conflated. The abstract restricted tensor product of local Hecke algebras may be an infinite polynomial algebra, while its image on one fixed-level, fixed-weight cuspidal space is finite dimensional and can have relations. A Hecke eigensystem is a character of the acting image, or equivalently a compatible system of eigenvalues for the abstract operators.

### 7.2 Satake parameters and the raw operator

Suppose $\pi_v$ is spherical. It is the spherical constituent of the normalized principal series

$$
I(\chi_{1,v},\chi_{2,v}),
$$

where the unordered characters $\chi_{i,v}$ are unramified. Its functions satisfy, for $b=\begin{pmatrix}a&*\\0&d\end{pmatrix}$,

$$
f(bg)=\left|\frac ad\right|_v^{1/2}
\chi_{1,v}(a)\chi_{2,v}(d)f(g).
$$

The group acts by right translation. The half-modulus in this formula is the source of the symmetric Satake normalization; removing it would change every power of $q_v$ below. Put

$$
\alpha_v=\chi_{1,v}(\varpi_v),
\qquad \beta_v=\chi_{2,v}(\varpi_v).
$$

These are the representation-normalized Satake parameters. Let

$$
T_v^{\rm raw}=\mathbf1_{K_v\operatorname{diag}(\varpi_v,1)K_v},
\qquad
S_v=\mathbf1_{K_v(\varpi_vI_2)K_v}.
$$

On the spherical line,

$$
T_v^{\rm raw}=q_v^{1/2}(\alpha_v+\beta_v),
\qquad S_v=\alpha_v\beta_v=\omega_{\pi_v}(\varpi_v).
$$

Thus the spectrally normalized operator

$$
\mathsf T_v=q_v^{-1/2}T_v^{\rm raw}
$$

has eigenvalue $\alpha_v+\beta_v$. The sanity check is the trivial representation. It corresponds to the exceptional normalized inducing pair with parameters $q_v^{1/2},q_v^{-1/2}$; the raw eigenvalue is $q_v+1$, the number of right cosets.

### 7.3 The local polynomial and standard factor

The representation-normalized Hecke polynomial is

$$
P_v(X)=(1-\alpha_vX)(1-\beta_vX)
=1-(\alpha_v+\beta_v)X+\omega_{\pi_v}(\varpi_v)X^2.
$$

Accordingly,

$$
L(s,\pi_v)=P_v(q_v^{-s})^{-1}.
$$

In terms of the raw operator eigenvalue $t_v^{\rm raw}$ and central eigenvalue $s_v$, the same polynomial is

$$
1-q_v^{-1/2}t_v^{\rm raw}X+s_vX^2.
$$

There is also an **integral raw normalization** in which

$$
P_v^{\rm ar}(X)=1-a_vX+q_vs_vX^2.
$$

Its reciprocal roots are $q_v^{1/2}\alpha_v$ and $q_v^{1/2}\beta_v$, and $a_v=t_v^{\rm raw}$. This integral normalization belongs to the double-coset algebra; it should not be confused with the weight-dependent algebraic normalization of a holomorphic eigenform in Chapter 13. Both conventions are valid. The error is to use the raw eigenvalue as the middle coefficient while retaining $\alpha_v\beta_v=s_v$ as the constant coefficient. The missing $q_v$ would mix normalizations.

In normalized Satake language,

$$
\mathcal S(T_v^{\rm raw})=q_v^{1/2}(X_1+X_2),
\qquad \mathcal S(S_v)=X_1X_2.
$$

The half-modulus in this transform matches normalized induction. Omitting both gives a consistent but asymmetric unnormalized transform; omitting only one gives wrong eigenvalues.

### 7.4 Twists and a worked unramified example

If $\mu_v$ is unramified, then

$$
(\pi_v\otimes\mu_v)(g)=\mu_v(\det g)\pi_v(g)
$$

has parameters

$$
\mu_v(\varpi_v)\alpha_v,
\qquad \mu_v(\varpi_v)\beta_v.
$$

Its central character is $\omega_{\pi_v}\mu_v^2$. Both roots scale once, while their product scales twice. This is the quickest normalization test for a proposed Hecke polynomial.

For example, let $F_v=\mathbf Q_p$ and take unitary unramified characters with values $A,B$ on $p$. Then

$$
T_p^{\rm raw}e=p^{1/2}(A+B)e,\qquad
S_p e=ABe,\qquad
L(s,\pi_p)=\frac1{(1-Ap^{-s})(1-Bp^{-s})}.
$$

If one uses the integral raw roots $p^{1/2}A,p^{1/2}B$, the polynomial becomes

$$
1-p^{1/2}(A+B)X+pABX^2.
$$

No assertion about Frobenius is needed to define either polynomial. If reciprocity later sends a uniformizer to arithmetic Frobenius, the representation-normalized parameters match arithmetic-Frobenius eigenvalues in that convention; geometric Frobenius gives their inverses. Naming the Frobenius without its direction is incomplete.

### 7.5 Radial recurrences

Put

$$
A_{v,n}=\mathbf1_{K_v\operatorname{diag}(\varpi_v^n,1)K_v},
\qquad n\ge0.
$$

The tree of homothety classes of lattices shows that the first double coset moves a vertex to its $q_v+1$ neighbors. One edge points back and $q_v$ point forward. Keeping track of central homothety gives

$$
A_{v,1}*A_{v,1}=A_{v,2}+(q_v+1)S_v
$$

and, for $n\ge2$,

$$
A_{v,1}*A_{v,n}=A_{v,n+1}+q_vS_v*A_{v,n-1}.
$$

Equivalently,

$$
\sum_{n\ge0}A_{v,n}X^n
=\frac{1-S_vX^2}{1-T_v^{\rm raw}X+q_vS_vX^2}.
$$

Evaluating this identity on a spherical line recovers every radial eigenvalue from the trace and determinant operators. The denominator is the integral raw polynomial; rescaling $T_v$ and $X$ gives the representation-normalized polynomial of Section 7.3.

### 7.6 Proof of the rank-two Satake calculation

The formulas above are short enough to memorize, but the calculation is worth carrying out once.
It explains simultaneously the factor $q_v^{1/2}$, the determinant operator, and the fact that the
spherical algebra has only two independent parameters.

Suppress $v$ and write $K=\mathrm{GL}_2(\mathcal O)$, $q=q_v$, and $\varpi=\varpi_v$. Let
$f^\circ$ be the spherical vector in $I(\chi_1,\chi_2)$ normalized by $f^\circ(1)=1$. The double
coset has the disjoint right-coset decomposition

$$K\begin{pmatrix}\varpi&0\\0&1\end{pmatrix}K=

\coprod_{u\in\mathcal O/\mathfrak p}
\begin{pmatrix}\varpi&u\\0&1\end{pmatrix}K
\;\sqcup\;
\begin{pmatrix}1&0\\0&\varpi\end{pmatrix}K.
\tag{7.1}
$$

To verify disjointness, apply both sides to the lattice $\mathcal O^2$. The sublattices of index
$q$ are the inverse images of the $q+1$ lines in $k^2$: $q$ lines have a representative of slope
$u$, and the remaining line is vertical. This also proves that the list is exhaustive.

Because convolution acts by right translation,

$$
(T^{\rm raw}f^\circ)(1)
=\sum_{u\in\mathcal O/\mathfrak p}
f^\circ\!\left(\begin{pmatrix}\varpi&u\\0&1\end{pmatrix}\right)
+f^\circ\!\left(\begin{pmatrix}1&0\\0&\varpi\end{pmatrix}\right).
$$

The first $q$ matrices lie in $B$ and contribute

$$
|\varpi|^{1/2}\chi_1(\varpi)=q^{-1/2}\alpha
$$

each. The last matrix contributes

$$
|\varpi^{-1}|^{1/2}\chi_2(\varpi)=q^{1/2}\beta.
$$

There are $q$ first terms, so their total is $q^{1/2}\alpha$. Adding the last term gives

$$
T^{\rm raw}f^\circ=q^{1/2}(\alpha+\beta)f^\circ.
\tag{7.2}
$$

A less convention-sensitive proof uses the Satake transform. For $h\in\mathcal H(G,K)$ define

$$
(\mathcal Sh)(t)=\delta_B(t)^{1/2}
\int_Nh(tn)\,dn.
$$

The integral is a finite sum on each torus coset. Direct counting for the first double coset gives

$$
\mathcal S(T^{\rm raw})=q^{1/2}(X_1+X_2),
\qquad
\mathcal S(S)=X_1X_2.
\tag{7.3}
$$

Here $X_i$ evaluates at $\chi_i(\varpi)$. Convolution becomes multiplication because decomposing
$N$ into the fibers of $N\times N\to N$ and changing variables by torus conjugation produces
exactly the two half-modulus factors. Thus $\mathcal S$ is an algebra homomorphism.

For rank two, every diagonal double coset is, up to a central power, represented by
$\operatorname{diag}(\varpi^n,1)$ with $n\ge0$. The leading term of its Satake transform is
$q^{n/2}(X_1^n+X_2^n)$, plus terms of smaller $n$. Triangular induction therefore shows that the
image is the symmetric Laurent algebra

$$
\mathbf C[X_1^{\pm1},X_2^{\pm1}]^{\mathfrak S_2}
=\mathbf C[X_1+X_2,(X_1X_2)^{\pm1}].
\tag{7.4}
$$

It also proves injectivity: a nonzero Hecke function has a largest Cartan double coset, whose
leading symmetric monomial cannot cancel. Hence the spherical Hecke character is equivalent to
the unordered pair $\{\alpha,\beta\}$, and the trace and determinant operators determine the
unramified representation.

The trivial representation provides a complete check. It is the spherical quotient at the
reducibility point with $\{\alpha,\beta\}=\{q^{1/2},q^{-1/2}\}$. Formula (7.2) gives $q+1$, which
is the number of index-$q$ neighbor lattices. The determinant operator gives $1$. Any proposed
normalization failing either test has misplaced a half-power or a central factor.

## 8. Global Whittaker expansions

### 8.1 Why the nonconstant coefficient should determine the form

Cuspidality deletes the constant term, leaving only nonzero Fourier modes along $N$. Rational diagonal matrices act transitively on the nonzero characters of $F\backslash\mathbf A$. Therefore all nonzero Fourier coefficients are translates of one coefficient. This rank-one orbit statement is the source of global genericity and multiplicity one.

Fix a nontrivial unitary character

$$
\psi:F\backslash\mathbf A\longrightarrow\mathbf C^\times,
\qquad \psi=\prod_v\psi_v.
$$

For a cusp form $\phi$, define

$$
W_\phi(g)=\int_{F\backslash\mathbf A}
\phi(n(x)g)\psi(-x)\,dx.
$$

Then

$$
W_\phi(n(u)g)=\psi(u)W_\phi(g).
$$

The sign is consistent: translating $x$ to $x+u$ changes $\psi(-x)$ by $\psi(u)$.

### 8.2 Fourier expansion and injectivity

**Theorem 8.1 (global Whittaker expansion).** Every smooth cuspidal automorphic form has the absolutely and locally uniformly convergent expansion

$$
\boxed{
\phi(g)=\sum_{\alpha\in F^\times}
W_\phi\left(\begin{pmatrix}\alpha&0\\0&1\end{pmatrix}g\right).}
$$

The series remains convergent after right-invariant differentiation.

**Proof strategy.** Apply Fourier inversion on the compact group $F\backslash\mathbf A$. Cuspidality removes the zero coefficient. Conjugating $n(x)$ by $\operatorname{diag}(\alpha,1)$ identifies the coefficient indexed by $\alpha$ with the chosen coefficient indexed by $1$. Rapid decay supplies convergence.

**Proof.** For fixed $g$, Fourier inversion gives

$$
\phi(n(x)g)=\sum_{\alpha\in F}W_{\phi,\alpha}(g)\psi(\alpha x).
$$

The coefficient at $0$ is $\phi_N(g)=0$. Since $|\alpha|_{\mathbf A}=1$ for $\alpha\in F^\times$, change of variables in $F\backslash\mathbf A$ introduces no measure factor, and

$$
W_{\phi,\alpha}(g)
=W_\phi\left(\begin{pmatrix}\alpha&0\\0&1\end{pmatrix}g\right).
$$

Set $x=0$. To justify this pointwise operation, fix a compact set of $g$ and a compact open
subgroup fixing $\phi$ at the finite places. The finite Fourier integral forces $\alpha$ into one
fixed fractional ideal. On the resulting compact archimedean torus let

$$
\Delta_N=1-\sum_{j=1}^{[F:\mathbf Q]}X_j^2
$$

for a basis of invariant unipotent fields. On the $\alpha$-character,
$\Delta_N^r$ acts by a multiplier comparable to $(1+\|\alpha\|^2)^r$. Integration by parts on
the torus gives

$$
|W_{\phi,\alpha}(g)|
\le C_{r,K}(1+\|\alpha\|)^{-2r}
\sup_{g'\in K'}|\Delta_N^r\phi(g')|.
$$

The enlarged set $K'$ is compact. Taking $2r>[F:\mathbf Q]$ makes the fractional-ideal sum
absolutely and locally uniformly convergent. Applying the same estimate after a right-invariant
derivative proves normal convergence of every derived series. $\square$

In particular, $W_\phi=0$ implies $\phi=0$. The single Whittaker coefficient is not merely an invariant; on the cuspidal space it is a faithful coordinate system.

### 8.3 Global and local uniqueness

Let $\pi$ be an irreducible cuspidal representation. A global Whittaker functional is the
restriction to $\pi^{\mathrm{fin}}$ of a continuous linear functional on the smooth
Casselman--Wallach globalization at infinity, with the usual inductive smooth topology at the
finite adeles, such that

$$
\Lambda:\pi^{\mathrm{fin}}\longrightarrow\mathbf C,
\qquad
\Lambda(\pi(n(x))v)=\psi(x)\Lambda(v).
$$

The integral above gives a nonzero continuous functional of this kind. Merely algebraic,
possibly discontinuous functionals are not included; archimedean uniqueness would not justify a
claim about that larger space. Local Whittaker uniqueness says

$$
\dim\operatorname{Hom}_{N(F_v)}(\pi_v,\psi_v)\le1.
$$

At a finite place this is Book 73, Theorem 8.2, the rank-one distribution theorem for local $\mathrm{GL}_2$.
At a real or complex place it is the Casselman--Wallach Whittaker multiplicity-one
input used in Book 92, Sections 3.3--3.4; continuity is understood in the smooth
Fréchet topology. The archimedean assertion is not obtained by repeating the nonarchimedean
Bruhat-cell argument without its regularity input.

Every local component of a cuspidal representation is generic. To see this without assuming it, first write a vector on which $\Lambda$ is nonzero as a finite sum of pure tensors; at least one summand $v=\otimes_uv_u$ still has $\Lambda(v)\ne0$. For a chosen place $v$, holding every other factor fixed turns

$$
w_v\longmapsto
\Lambda\left(w_v\otimes\bigotimes_{u\ne v}v_u\right)
$$

into a nonzero local Whittaker functional.

This proves genericity for the chosen $\psi_v$. Every other nontrivial additive character has
the form $x\mapsto\psi_v(ax)$ for some $a\in F_v^\times$, and conjugation by
$\operatorname{diag}(a,1)$ transports a $\psi_v$-functional to a
$\psi_v(a\,\cdot)$-functional. Hence genericity holds for every nontrivial local additive
character, as asserted below.

**Theorem 8.2 (global uniqueness and factorization).** The space of global Whittaker functionals on $\pi$ is one dimensional. After choosing nonzero local functionals $\lambda_v$ and normalizing them by $\lambda_v(e_v)=1$ at almost every unramified finite place,

$$
\Lambda\left(\bigotimes_vv_v\right)=\prod_v\lambda_v(v_v).
$$

Consequently a pure tensor has a factorizable Whittaker function

$$
W_v(g)=\lambda_v(\pi_v(g)v_v),
\qquad
W(g)=\prod_vW_v(g_v).
$$

**Proof strategy.** On each finite tensor stage, successive local uniqueness bounds a Whittaker functional by a tensor product of the local lines. The spherical normalization makes these finite-stage scalars compatible when a new unramified place is added. The restricted tensor product is the union of the finite stages.

**Proof.** First construct the product functional. At almost every finite place, the spherical
generic representation has a unique Whittaker functional nonzero on its spherical line; scale it
so that $\lambda_v(e_v)=1$. Choose any nonzero local functional at each exceptional place. Then

$$
\Lambda^{\rm prod}\left(\bigotimes_vv_v\right)
=\prod_v\lambda_v(v_v)
$$

is a well-defined $N(\mathbf A)$-equivariant functional on the algebraic restricted tensor
product, since almost every factor is one on a reference tensor. It is continuous on each finite
tensor stage, hence on the restricted smooth inductive limit.

Now let $\Lambda$ be any global Whittaker functional. Choose a pure tensor $v^0$ with
$\Lambda^{\rm prod}(v^0)\ne0$ and enlarge a finite set $S_0$ until $v^0$ is standard outside
$S_0$. On the tensor space obtained by varying the factors in a finite $S\supseteq S_0$ and
fixing the others as in $v^0$, successive local uniqueness makes the restriction of $\Lambda$
a scalar multiple $c_S$ of the restriction of $\Lambda^{\rm prod}$. Evaluation at $v^0$
shows that $c_S$ is independent of $S$. The union of these finite tensor spaces is the whole
restricted tensor product, so $\Lambda=c\Lambda^{\rm prod}$ globally.

This argument also covers the case in which $\Lambda$ vanishes on the original spherical
reference tensor: the comparison tensor $v^0$ is chosen where the product functional is nonzero,
not assumed in advance. The automorphic Whittaker integral is a nonzero global functional, so
after one overall rescaling it equals $\Lambda^{\rm prod}$. Applying it to $\pi(g)v$ gives the
factorization of Whittaker functions. $\square$

### 8.4 The spherical Whittaker function

At an unramified finite place choose $W_v^\circ(1)=1$. If the Satake parameters are $\alpha_v,\beta_v$, then for $m\ge0$,

$$
W_v^\circ\left(\begin{pmatrix}\varpi_v^m&0\\0&1\end{pmatrix}\right)
=q_v^{-m/2}
\frac{\alpha_v^{m+1}-\beta_v^{m+1}}{\alpha_v-\beta_v},
$$

with the evident limiting formula $(m+1)q_v^{-m/2}\alpha_v^m$ if $\alpha_v=\beta_v$, and the value is $0$ for $m<0$. Therefore

$$
\sum_{m\ge0}W_v^\circ
\left(\begin{pmatrix}\varpi_v^m&0\\0&1\end{pmatrix}\right)
q_v^{m/2}X^m
=\frac1{(1-\alpha_vX)(1-\beta_vX)}.
$$

This calculation unifies Hecke and Fourier data: the same two parameters govern the spherical Hecke polynomial and the diagonal values of the normalized Whittaker function.

### 8.5 Standard zeta integrals

For a local Whittaker function, set initially in a right half-plane

$$
Z_v(s,W_v)=\int_{F_v^\times}
W_v\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
|y|_v^{s-1/2}\,d^\times y.
$$

For $W_v^\circ$, valuation-shell decomposition and Section 8.4 give $Z_v(s,W_v^\circ)=L(s,\pi_v)$. At a ramified place, all such integrals form a fractional ideal in $\mathbf C[q_v^s,q_v^{-s}]$ whose distinguished generator is the standard local factor. For an irreducible principal series it is the product of the factors attached to its unramified inducing characters. For $\operatorname{St}\otimes\mu$ in unitary normalization it is $L(s+1/2,\mu)$. For a supercuspidal representation of $\mathrm{GL}_2(F_v)$ it is $1$.

For a factorizable global Whittaker function, the corresponding integral is over $\mathbf A^\times$, not over $F^\times\backslash\mathbf A^\times$:

$$
Z(s,W)=\int_{\mathbf A^\times}
W\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
|y|_{\mathbf A}^{s-1/2}\,d^\times y.
$$

The distinction matters because $W(\operatorname{diag}(\alpha,1)g)$ is the Fourier coefficient indexed by $\alpha$, not generally $W(g)$. The integral factors into local integrals and at unramified places produces $\prod_vL(s,\pi_v)$. Equivalently, one starts with a Mellin integral of the automorphic form over $F^\times\backslash\mathbf A^\times$ and unfolds its Whittaker expansion to the displayed integral over $\mathbf A^\times$. Fourier transform supplies continuation and a functional equation involving $\pi^\vee$. The Rankin--Selberg product of Chapter 9, rather than this degree-two integral, is the analytic engine used for strong multiplicity one.

### 8.6 Global genericity and Euler products

The preceding constructions prove more than the existence of Fourier coefficients. They identify
the global representation with a subrepresentation of one canonical function space. Define the
global Whittaker model

$$
\mathcal W(\pi,\psi)=\{W_v:g\mapsto\Lambda(\pi(g)v):v\in\pi^{\rm fin}\}.
$$

The map $v\mapsto W_v$ is injective: if $W_v=0$, then every translate of the corresponding
automorphic form has zero coefficient, and Theorem 8.1 reconstructs every translate as zero. It
is equivariant for right translation, since

$$
W_{\pi(h)v}(g)=W_v(gh).
$$

Thus $\mathcal W(\pi,\psi)$ is not merely a collection of coefficients; it is a realization of
$\pi$ itself.

**Theorem 8.3 (global genericity package).** Let $\pi$ be an irreducible cuspidal automorphic
representation of $\mathrm{GL}_2(\mathbf A_F)$. Then:

1. every local component $\pi_v$ is generic for every nontrivial $\psi_v$;
2. the global Whittaker model is unique up to one scalar;
3. for a pure tensor $v=\otimes_vv_v$, its Whittaker function factors as

   $$
   W_v(g)=\prod_wW_{v_w,w}(g_w);
   $$

4. if the finite local vectors are spherical and normalized by $W_w(1)=1$ outside a finite set
   $S$, then the unfolded Mellin integral has Euler product

   $$
   Z(s,W_v)=\prod_wZ_w(s,W_{v_w,w})
   =\left(\prod_{w\notin S}L(s,\pi_w)\right)
   \left(\prod_{w\in S}Z_w(s,W_{v_w,w})\right)
   $$

   in a common right half-plane.

**Proof.** Parts 1--3 were proved in Sections 8.2 and 8.3; it remains to justify the analytic
factorization in part 4. A ramified principal-series or special Whittaker function need not be
compactly supported in the valuation direction, so compact support cannot be used here. Instead
start with the Mellin integral of the rapidly decreasing automorphic cusp form over
$F^\times\backslash\mathbf A^\times$ and unfold its normally convergent Whittaker expansion.
In a sufficiently far right half-plane this proves that the absolute adelic integral

$$
\int_{\mathbf A^\times}
\prod_w\left|W_w\!\left(\begin{pmatrix}y_w&0\\0&1\end{pmatrix}\right)\right|
|y|_{\mathbf A}^{\operatorname{Re}(s)-1/2}\,d^\times y
$$

is finite. Finite-stage Fubini followed by monotone convergence for the absolute values then
separates it into the product of local absolute integrals. Equivalently, the convergence of the
unramified Euler tail is deduced from the global integral, not from an unproved bound on individual
Satake roots. Almost every local integral is the normalized spherical series of Section 8.4 and equals
$L(s,\pi_w)$. Only the finite set $S$ leaves a different factor. This proves the formula.
$\square$

The qualification “in a common right half-plane” is essential. An Euler product is first an
identity of absolutely convergent expressions. Meromorphic continuation of the global integral
then continues the product; it does not license termwise multiplication of arbitrary
meromorphic local expressions outside the convergence region.

There is also a useful nonvanishing statement. Given a finite set $S$ and prescribed nonzero
local Whittaker functions at $S$, one may choose spherical functions outside $S$ and form their
restricted tensor. The resulting global Whittaker vector is nonzero because its value at the
identity is the product of finitely many prescribed values after translating locally so that
each is nonzero. Hence the restricted tensor product of local Whittaker models really occurs in
the global one; it is not merely an upper bound furnished by uniqueness.

Global genericity also explains why no finite local component of a cuspidal representation can
be one dimensional. A determinant character is trivial on $N(F_v)$, so it admits no nonzero
$\psi_v$-equivariant functional when $\psi_v$ is nontrivial. Principal series, special
representations, and supercuspidals do admit one. This is the precise local consequence of
global cuspidality; it still does not say that any local component is supercuspidal.

## 9. Multiplicity one

### 9.1 Two logically distinct assertions

There are two multiplicity-one statements. **Global multiplicity one** says that an irreducible cuspidal representation occurs only once in the cuspidal spectrum. **Strong multiplicity one** says that two cuspidal representations with isomorphic local components outside a finite set are globally isomorphic. The first controls copies of one representation; the second reconstructs a representation from almost all of its local data.

Both ultimately arise from the Whittaker coefficient, but strong multiplicity one requires a decisive global analytic input. We give the Rankin--Selberg route because it makes that input visible.

The distinction governs the rest of the book. Unit multiplicity makes the finite newvector line
occur only once in the automorphic Hilbert space. Strong multiplicity one lets good-prime Hecke
data identify which global summand owns that line. Neither assertion contains the other, so they
are proved by different mechanisms before being combined in newform theory.

### 9.2 Global multiplicity one from Whittaker expansion

**Theorem 9.1.** Every irreducible cuspidal representation of $G(\mathbf A)$ occurs in $L^2_{\mathrm{cusp}}(\omega)$ with multiplicity one.

**Proof strategy.** Each occurrence maps equivariantly and injectively into the same global Whittaker model. Global Whittaker uniqueness leaves room for only one such embedding.

**Proof.** Let $M=\operatorname{Hom}_{G(\mathbf A)}(\pi,L^2_{\mathrm{cusp}}(\omega))$ be the multiplicity space. For an embedding $i\in M$, composition with the Whittaker integral gives a functional $\Lambda_i$ on $\pi$. If $\Lambda_i=0$, every form in the image of $i$ has zero Whittaker coefficient and hence is zero by Theorem 8.1; thus $i=0$. The map

$$
M\longrightarrow\operatorname{Hom}_{N(\mathbf A)}(\pi,\psi),
\qquad i\longmapsto\Lambda_i,
$$

is injective. The target is one dimensional by Theorem 8.2, so $\dim M\le1$. Since $\pi$ occurs, equality holds. $\square$

The proof uses global uniqueness, not only local uniqueness. A collection of one-dimensional local Hom spaces would not by itself exclude two independent global embeddings with different global scalars.

### 9.3 The Rankin--Selberg integral

Let $\pi$ and $\pi'$ be unitary cuspidal representations with the same central character, and choose cusp forms $\phi$ and $\phi'$. Form an Eisenstein series $E(g,s)$ from the normalized induction attached to the standard Borel, with trivial central character. For $\operatorname{Re}(s)$ large, consider

$$
I(s)=\int_{X_G}\phi(g)\overline{\phi'(g)}E(g,s)\,dg.
$$

The common-central-character hypothesis is what makes the integrand descend to $X_G$: the two unitary central factors cancel. For unequal central characters one uses the corresponding character-adjusted Rankin--Selberg datum, but strong multiplicity one below first proves that no adjustment is needed.

Unfolding the Eisenstein series, then inserting the Whittaker expansions, gives an Euler product. For factorizable pure vectors and suitable local Schwartz data,

$$
I(s)=\prod_vZ_v(s,W_v,\overline{W_v'},f_{v,s}),
$$

and at every unramified place the local integral equals

$$
L(s,\pi_v\times\pi_v'{}^\vee)
=\prod_{i,j=1}^2(1-\alpha_{i,v}\alpha_{j,v}'{}^{-1}q_v^{-s})^{-1}.
$$

At a ramified place, however, a preferred local integral can vanish. The safe canonical argument
uses the full local zeta ideal. Every local integral is the normalized local factor times a
Laurent-polynomial correction, and finitely many corrections $P_j$ satisfy a Bezout identity

$$
\sum_jA_jP_j=1.
$$

At infinity an analogous finite polynomial-Gaussian family removes common gamma corrections.
Tensoring the finitely many choices gives global integrals $I_j(s)$ and entire coefficient
functions $A_j(s)$ such that

$$
\Lambda(s,\pi\times\pi'{}^\vee)
=\sum_jA_j(s)I_j(s).
\tag{9.1}
$$

No division by a possibly vanishing preferred correction is involved.

The Eisenstein series continues meromorphically and has at most a simple pole at $s=1$ in the
untwisted unitary case. Its residue is a nonzero constant, so

$$
\operatorname*{Res}_{s=1}I(s)
=c\langle\phi,\phi'\rangle,
\qquad c\ne0.
\tag{9.2}
$$

Cuspidal rapid decay justifies the pairing and the unfolding. If $\pi'\not\cong\pi$, the
invariant pairing vanishes by irreducibility; if $\pi'=\pi$, paired nonzero vectors make it a
positive multiple of their norm. The finite-family identity (9.1) transfers both continuation
and this exact pole alternative to the canonical completed function. Finally, every finite or
archimedean local factor deleted in forming an incomplete product is finite and nonzero at
$s=1$ for unitary generic data. Therefore deletion does not change the polar order.

The analytic input can consequently be stated without auxiliary vectors:

Write $\operatorname{pord}_{s=1}$ for the nonnegative polar order: it is one for a simple pole
and zero for a function holomorphic at $1$, whether or not that function vanishes there. Then

$$
\boxed{
\operatorname{pord}_{s=1}L^S(s,\rho\times\pi^\vee)
=\dim\operatorname{Hom}_{G(\mathbf A)}(\rho,\pi),}
\tag{9.3}
$$

for unitary irreducible cuspidal $\rho,\pi$ and every finite $S$ containing the archimedean
places. The right side is zero or one. This is the Rankin--Selberg criterion used below; it is a
theorem about the canonical incomplete product, not an inference from formal Euler factors or
from one lucky test vector.

### 9.4 Strong multiplicity one

**Theorem 9.2 (strong multiplicity one).** If $\pi$ and $\pi'$ are irreducible cuspidal automorphic representations of $\mathrm{GL}_2(\mathbf A_F)$ and

$$
\pi_v\cong\pi_v'
$$

for all but finitely many places $v$, then $\pi\cong\pi'$.

**Proof strategy.** Outside a finite set, the two Rankin--Selberg products against $\pi^\vee$ are identical. The self-product has a pole at $1$. If $\pi'$ were distinct, the cross-product would be holomorphic there. Ramified local factors cannot create or cancel that distinction.

**Proof.** First the central characters agree. Indeed, put

$$
\eta=\omega_\pi\omega_{\pi'}^{-1}.
$$

The local character $\eta_v$ is trivial for $v$ outside a finite set $S$. Enlarge $S$ to contain the archimedean places. Since $\eta$ is trivial on $F^\times$, the product character $\prod_{v\in S}\eta_v$ is trivial on the diagonal copy of $F^\times$. Weak approximation makes that diagonal copy dense in $\prod_{v\in S}F_v^\times$, and continuity therefore makes every remaining local product trivial. Hence $\eta=1$.

Now enlarge $S$ further so it contains all ramified places and $\pi_v\cong\pi_v'$ for $v\notin S$. Then term by term

$$
L^S(s,\pi\times\pi^\vee)
=L^S(s,\pi'\times\pi^\vee).
$$

The left side has a simple pole at $s=1$ by the Rankin--Selberg analysis. If $\pi'\not\cong\pi$, the right side is holomorphic there. The finite set has already been omitted, so no exceptional ramified factor can alter the equality. This contradiction proves $\pi'\cong\pi$. $\square$

Equality of almost all normalized Hecke polynomials is equivalent to equality of almost all unramified local components, because the Satake transform recovers the unordered parameter pair. Thus a cuspidal representation is determined by almost all $T_v$ and $S_v$ eigenvalues. Omitting the central eigenvalues is safe only when the central character has already been fixed.

### 9.5 Why the pole comparison is logically complete

The proof of Theorem 9.2 is short because several analytic facts have already been assembled. It
is worth isolating the exact logical content, especially the role of the omitted finite set.

For a finite set $S$ containing all archimedean and ramified places, define

$$
L^S(s,\pi\times\pi'^\vee)
=\prod_{v\notin S}L(s,\pi_v\times\pi_v'^\vee).
$$

Absolute convergence for $\operatorname{Re}(s)>1$ makes this an honest product there. The
canonical continuation and polar order are supplied by (9.3). The finite Bezout family in
(9.1), rather than a claim that one preferred correction never vanishes, is what transfers the
Eisenstein residue calculation to the canonical local-factor product. Local unitarity then shows
that every factor removed in forming $L^S$ is finite and nonzero at one. Consequently the
incomplete product has a simple pole exactly in the self case and is holomorphic in the cross
case. It may vanish in the cross case; the proof requires only its polar order and makes no
unproved nonvanishing assertion.

One may also remove unequal central characters without the density shortcut. If the unramified
local representations agree outside $S$, their local central characters agree there. Thus
$\eta=\omega_\pi\omega_{\pi'}^{-1}$ is a Hecke character trivial on $F_v^\times$ for
$v\notin S$. For $(x_v)_{v\in S}\in\prod_{v\in S}F_v^\times$, weak approximation supplies a
sequence $a_n\in F^\times$ tending to $(x_v)_{v\in S}$ while remaining in a sufficiently small
unit neighborhood at every place in a fixed finite enlargement of $S$. Since $\eta$ is trivial
outside $S$ and on the principal ideles $a_n$, continuity gives

$$
\prod_{v\in S}\eta_v(x_v)=1.
$$

Setting all but one $x_v$ equal to $1$ shows $\eta_v=1$ for every $v\in S$. Hence $\eta=1$.
This argument uses that $\eta_v$ is already identically trivial, not merely unramified, outside
$S$.

The distinction matters. A nontrivial ideal-class character is unramified at every finite place,
yet it need not be trivial there: its value on a uniformizer may be nontrivial. Equality of local
representations supplies equality of the full local central characters and therefore triviality,
which is stronger than equality on units.

We can now state the recognition form most often used in arithmetic.

**Corollary 9.3 (Hecke-polynomial recognition).** Let $\pi$ and $\pi'$ be irreducible cuspidal
automorphic representations. Suppose that for all but finitely many finite $v$ both are
unramified and

$$
P_v(\pi;X)=P_v(\pi';X).
$$

Then $\pi\cong\pi'$.

**Proof.** Equality of the polynomials gives equality of the unordered Satake pairs by unique
factorization in $\mathbf C[X]$. The rank-two Satake isomorphism then identifies the spherical
local representations. Theorem 9.2 applies. $\square$

Equality of only the middle coefficients is insufficient unless the determinant terms are fixed.
For example, unordered pairs $\{a,b\}$ and $\{c,d\}$ can have $a+b=c+d$ but $ab\ne cd$.
Fixing the central character makes the products equal and restores sufficiency. This is the exact
reason a classical statement may mention only $T_v$ eigenvalues after the nebentype has been
fixed.

### 9.6 Recognition limits and counterexamples

Strong multiplicity one is powerful because its hypotheses are exact. Several nearby statements
have different status.

First, agreement at infinitely many places is not enough. A finite-order Hecke character $\chi$
can take the value $1$ at infinitely many unramified primes and a nontrivial value at infinitely
many others. If $\pi\otimes\chi\not\cong\pi$, then $\pi_v$ and
$(\pi\otimes\chi)_v$ can still agree at every prime where $\chi_v(\varpi_v)=1$. The agreement set
may be large, but its complement is not finite. The pole proof needs equality of the entire Euler
tail outside one finite set.

Second, matching standard local $L$-factors need not match local representations at ramified
places. A ramified principal series with both inducing characters ramified and a supercuspidal
representation both have standard factor $1$. Strong multiplicity one avoids this ambiguity by
requiring equality at almost every place, where both representations are spherical and the full
quadratic polynomial recovers the local class. Once the global classes are identified, all
ramified factors agree automatically.

Third, strong multiplicity one does not prove automorphic multiplicity one. If two orthogonal
copies of the same representation appeared in the Hilbert space, their local components would
agree everywhere. Strong recognition would merely identify both copies with the same isomorphism
class. Chapter 8 excludes the second copy by mapping the multiplicity space injectively into the
one-dimensional global Whittaker-functional space.

Fourth, representation recognition does not recognize a higher-level vector. Suppose $\pi_p$ is
unramified and raise the local $K_1$-level from exponent zero to exponent one. The fixed space is
two dimensional. Every vector in it has the same Hecke eigenvalues away from $p$, since all lie
in the same global representation. The two degeneracy vectors can be separated by an operator at
$p$, but strong multiplicity one alone cannot choose between them. Minimal level and Whittaker
normalization are what select the newvector.

There is a useful refinement in the opposite direction. Suppose $\omega_\pi=\omega_{\pi'}$ and
the normalized trace eigenvalues satisfy

$$
\alpha_v+\beta_v=\alpha'_v+\beta'_v
$$

outside a finite set. Equality of the central characters gives equality of the products
$\alpha_v\beta_v=\alpha'_v\beta'_v$. Hence the two quadratic polynomials agree and strong
multiplicity one applies. Thus, with central character fixed, one good-prime Hecke operator per
place suffices.

Finally, the theorem concerns irreducible cuspidal representations. An Eisenstein representation
induced from $(\chi_1,\chi_2)$ is already determined locally by the unordered pair of characters,
but global induced representations can be presented with Weyl-related data and can specialize at
reducibility points. Residual determinant characters sit on that boundary. Their recognition is
an induction problem, not the cuspidal pole argument proved here.

## 10. Contragredients, twists, and central characters

### 10.1 The contragredient in the automorphic realization

For an admissible representation $\pi$, the contragredient $\pi^\vee$ has local factors $\pi_v^\vee$. Its central character is $\omega_\pi^{-1}$, and

$$
(\pi^\vee)_v\cong\pi_v^\vee,
\qquad
\pi^\vee\cong\bigotimes_v'\pi_v^\vee.
$$

If $\pi_v$ is unramified with parameters $\alpha_v,\beta_v$, then $\pi_v^\vee$ has parameters $\alpha_v^{-1},\beta_v^{-1}$. It follows that

$$
P_{\pi_v^\vee}(X)
=(1-\alpha_v^{-1}X)(1-\beta_v^{-1}X).
$$

Complex conjugation and contragredience agree for a unitary representation, but not as an algebraic identity for an arbitrary nonunitary normalization. It is safer to say $\overline\pi\cong\pi^\vee$ in the unitary category and to retain $\pi^\vee$ elsewhere.

The Whittaker model of $\pi^\vee$ uses $\psi^{-1}$. This inverse is forced by the invariant pairing:

$$
\langle\pi(n(x))v,\pi^\vee(n(x))\lambda\rangle
=\langle v,\lambda\rangle.
$$

### 10.2 Twisting by a Hecke character

Let $\chi:F^\times\backslash\mathbf A^\times\to\mathbf C^\times$ be a Hecke character. Define

$$
(\pi\otimes\chi)(g)=\chi(\det g)\pi(g).
$$

On automorphic forms this is realized by

$$
\phi(g)\longmapsto\chi(\det g)\phi(g).
$$

The factor is left $G(F)$-invariant because $\chi$ is trivial on $F^\times$. Since $\det n(x)=1$, the constant term is multiplied by $\chi(\det g)$; cuspidality is preserved. Locally,

$$
(\pi\otimes\chi)_v\cong\pi_v\otimes\chi_v,
$$

and the central character becomes

$$
\omega_{\pi\otimes\chi}=\omega_\pi\chi^2.
$$

Also

$$
(\pi\otimes\chi)^\vee\cong\pi^\vee\otimes\chi^{-1}.
$$

These formulas explain why quadratic twists preserve the central character but need not preserve conductor or Hecke eigenvalues.

### 10.3 Finite-order and algebraic characters

A finite-order Hecke character is unitary and has archimedean components of finite order: at a real place it is $\operatorname{sgn}^{\epsilon_v}$, while at a complex place a continuous finite-order character is trivial on the connected group $\mathbf C^\times$. Such characters change nebentype and finite local types without shifting infinitesimal characters.

An **algebraic Hecke character** has archimedean form

$$
\chi_v(x)=x^{p_v}\bar x^{q_v}
$$

at a complex embedding, and $\chi_v(x)=x^{m_v}$ times a sign character at a real embedding, with integral exponents, subject to the condition that the product be trivial on $F^\times$. Its unitary normalization divides by an appropriate power of $|\cdot|_{\mathbf A}$. Algebraic and unitary are therefore different adjectives. A character can be both, as finite-order characters are, but an algebraic norm power is not unitary unless its exponent is zero.

### 10.4 Self-twists and a warning

It can happen that $\pi\otimes\chi\cong\pi$ for a nontrivial character $\chi$. Strong multiplicity one then forces

$$
\{\chi_v(\varpi_v)\alpha_v,\chi_v(\varpi_v)\beta_v\}
=\{\alpha_v,\beta_v\}
$$

at almost every unramified place. Such self-twists are rigid, but they are not excluded by multiplicity one.

There is no formula for $a(\pi_v\otimes\chi_v)$ in terms of only $a(\pi_v)$ and $a(\chi_v)$. If two characters have the same depth, their leading ramification can cancel. Exact conductor calculations must use the local representation: for a principal series they use the two inducing characters, and for a special or supercuspidal representation they use its corresponding local formula.

### 10.5 Local factors under duality

At an unramified place,

$$
L(s,\pi_v^\vee)
=\frac1{(1-\alpha_v^{-1}q_v^{-s})(1-\beta_v^{-1}q_v^{-s})}.
$$

An unramified twist multiplies both inverse roots by $\chi_v(\varpi_v)$. At ramified places the analogous statement is defined through Whittaker zeta integrals; one must not invent a pair of nonzero Satake roots when the local factor has degree one or zero.

Contragredience preserves conductor:

$$
a(\pi_v^\vee)=a(\pi_v),
\qquad
\mathfrak f(\pi^\vee)=\mathfrak f(\pi).
$$

The $K_1$-fixed spaces dualize, and the newvector lines pair nontrivially. This stable behavior contrasts with twisting, which can alter conductor through cancellation.

## 11. Conductors and compact-open invariants

### 11.1 The local exponent and global ideal

For $n\ge0$, define

$$
K_{1,v}(\mathfrak p_v^n)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(\mathcal O_v):
c\in\mathfrak p_v^n,\ d\equiv1\pmod{\mathfrak p_v^n}
\right\}.
$$

At $n=0$ the congruence is vacuous and this is $K_v$. For an infinite-dimensional irreducible generic $\pi_v$, its conductor exponent is

$$
a(\pi_v)=\min\{n:\pi_v^{K_{1,v}(\mathfrak p_v^n)}\ne0\}.
$$

The local newvector theorem gives

$$
\dim\pi_v^{K_{1,v}(\mathfrak p_v^m)}=
\begin{cases}
0,&m<a(\pi_v),\\
m-a(\pi_v)+1,&m\ge a(\pi_v).
\end{cases}
$$

The generality here is deliberate. Book 76, Theorem 10.1, proves the formula for
principal series, special representations, and the depth-zero and tame-dihedral
supercuspidals in its selected range, but does not claim it for primitive wild supercuspidals.
Book 94, Theorem 5.1, closes that boundary for every irreducible
admissible generic representation by the two-filtration argument in the Kirillov model. Upper
unipotent and unit invariance put the Kirillov function in one valuation flag; lower-unipotent
invariance puts its Weyl transform in the opposite flag. Each new shell has dimension at most
one. The compactly supported Kirillov core proves that the two flags meet at some finite level,
and diagonal translates of the first nonzero line meet every successive shell. Hence the first
intersection is one dimensional and the dimension at level $m$ is exactly
$m-a(\pi_v)+1$. Thus no unclassified wild local component is omitted from the theorem used
below.

Only finitely many exponents are nonzero for an automorphic representation, so its finite conductor is the ideal

$$
\mathfrak f(\pi)=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v)},
$$

and its norm is

$$
N(\pi)=\mathbf N_{F/\mathbf Q}\mathfrak f(\pi)
=\prod_{v<\infty}q_v^{a(\pi_v)}.
$$

The ideal is the more precise invariant; the integer norm can identify different ideals.

### 11.2 Global level groups and existence of invariants

For an integral ideal $\mathfrak n=\prod_v\mathfrak p_v^{n_v}$, put

$$
K_1(\mathfrak n)=\prod_{v<\infty}K_{1,v}(\mathfrak p_v^{n_v}).
$$

Factorization gives

$$
\pi_f^{K_1(\mathfrak n)}
\cong\bigotimes_{v<\infty}
\pi_v^{K_{1,v}(\mathfrak p_v^{n_v})}.
$$

Hence

$$
\pi_f^{K_1(\mathfrak n)}\ne0
\quad\Longleftrightarrow\quad
\mathfrak f(\pi)\mid\mathfrak n.
$$

Moreover, if $\mathfrak f(\pi)\mid\mathfrak n$, then

$$
\boxed{
\dim\pi_f^{K_1(\mathfrak n)}
=\prod_{v\mid\mathfrak n}
(n_v-a(\pi_v)+1).}
$$

Factors at places with $n_v=0=a(\pi_v)$ equal $1$ and may be omitted. This product formula is the global oldform multiplicity inside one automorphic representation.

If $v_f=\otimes_vv_v^{\rm new}$ is the tensor of normalized local newvectors, then

$$
\mathbf Cv_f=\pi_f^{K_1(\mathfrak f(\pi))}.
$$

Thus the global finite newvector exists and is unique up to scalar. Its uniqueness is a product of local uniqueness; global multiplicity one ensures that there is not a second automorphic copy carrying another such line.

### 11.3 $K_0$ and the central-character correction

Classical modular forms are often presented at

$$
K_{0,v}(\mathfrak p_v^n)
=\left\{\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_v:
c\in\mathfrak p_v^n\right\}.
$$

The quotient $K_0/K_1$ is represented by the lower-right entry in $(\mathcal O_v/\mathfrak p_v^n)^\times$. A local newvector does not generally remain fixed by $K_0$. With the right-translation convention it transforms by the character prescribed by the central character on that lower-right entry, after fixing the standard convention for the classical nebentype:

$$
\pi_v(k)v_v^{\rm new}=\omega_{\pi_v}(d)v_v^{\rm new}
\qquad
k=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_{0,v}(\mathfrak p_v^{a(\pi_v)}).
$$

Some classical conventions place the inverse character here because they use $f|g$ with an inverse right action. The formula must be derived from the chosen adelization, not memorized independently. Literal $K_0$-invariance in the presence of ramified central character is generally false.

Scalar matrices in $K_{1,v}(\mathfrak p_v^n)$ show the necessary inequality

$$
a(\omega_{\pi_v})\le a(\pi_v).
$$

The inequality can be strict. An unramified Steinberg twist has conductor exponent $1$ but unramified central character; a ramified quadratic twist of Steinberg can have trivial central character and conductor exponent $2$.

### 11.4 Conductors of local families

The local formulas give useful global diagnostics. For an irreducible principal series,

$$
a(I(\chi_{1,v},\chi_{2,v}))
=a(\chi_{1,v})+a(\chi_{2,v}).
$$

For a special representation,

$$
a(\operatorname{St}\otimes\mu_v)=
\begin{cases}
1,&a(\mu_v)=0,\\
2a(\mu_v),&a(\mu_v)>0.
\end{cases}
$$

Supercuspidal conductors are determined by their local newvectors; in tame dihedral constructions they can be computed from the quadratic extension, character conductor, and different. The global conductor simply multiplies these local contributions. It does not acquire an additional archimedean ideal factor. Archimedean parameters instead enter the analytic conductor, which also depends on the spectral parameter and is a different invariant.

### 11.5 Worked conductor profiles

Suppose over $\mathbf Q$ that

$$
\pi_2=\operatorname{St}\otimes\mu_2,\qquad
\pi_3=I(\chi_1,\chi_2),
$$

with $\mu_2$ unramified, $a(\chi_1)=1$, and $a(\chi_2)=2$, while every other finite component is spherical. Then

$$
a(\pi_2)=1,\qquad a(\pi_3)=3,\qquad
N(\pi)=2\cdot3^3=54.
$$

At level $2^2 3^5$, this representation contributes

$$
(2-1+1)(5-3+1)=6
$$

finite $K_1$-fixed vectors.

Now twist by a character of conductor $3$. The exponent at $2$ stays fixed if the local twist there is unramified, but at $3$ the new exponent is

$$
a(\chi_1\eta_3)+a(\chi_2\eta_3).
$$

Its value depends on the characters, not only their old exponents: equal-depth leading characters may cancel. This concrete example is why conductor tables must record local types and twists, not just an integer level.

## 12. Newforms and oldforms

### 12.1 Why minimal level singles out an eigenform

At a level divisible by $\mathfrak f(\pi)$, one representation contributes several invariant vectors. Most are inherited from smaller level. Newform theory isolates the minimal vector that contains the intrinsic finite ramification of $\pi$, then describes every higher-level vector as a controlled translate.

Let $n=a(\pi_v)$ and choose $v_v^{\rm new}\ne0$. For $m\ge n$, the local oldvectors

$$
v_{v,j}=\pi_v\left(\begin{pmatrix}\varpi_v^{-j}&0\\0&1\end{pmatrix}\right)v_v^{\rm new},
\qquad0\le j\le m-n,
$$

form a basis of $\pi_v^{K_{1,v}(\mathfrak p_v^m)}$. Each step of level raising adds one valuation shell in the Kirillov model, hence one dimension.

Globally, if

$$
\mathfrak n=\mathfrak f(\pi)\mathfrak r,
\qquad \mathfrak r=\prod_v\mathfrak p_v^{r_v},
$$

then tensors of the vectors above, indexed by $0\le j_v\le r_v$, form a basis. The number of oldvectors is

$$
\prod_v(r_v+1)=\prod_v(n_v-a(\pi_v)+1).
$$

### 12.2 Degeneracy maps and level raising

The translate by $\operatorname{diag}(\varpi_v^{-1},1)$ is the adelic form of a degeneracy map. Over $\mathbf Q$, raising level from $N$ to $Np$ produces the familiar pair

$$
f(z),\qquad f(pz)
$$

when $p\nmid N$, after the scalar factors dictated by the slash convention are inserted. Representation theory explains why there are exactly two: the local fixed-space dimension rises from $1$ to $2$.

If the exponent is raised by $r$, the translates corresponding to $f(p^jz)$ for $0\le j\le r$ give $r+1$ local vectors. At several primes, degeneracy maps tensor, so their multiplicities multiply rather than add.

This count concerns one representation. A full fixed-level cusp space is the direct sum

$$
S_{\mathrm{cusp}}(K_1(\mathfrak n),\tau)
\cong\bigoplus_{\pi:\,\mathfrak f(\pi)\mid\mathfrak n}
\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty)
\otimes\pi_f^{K_1(\mathfrak n)},
$$

with multiplicity one. Therefore its dimension is the sum, over representations of compatible infinity type, of the product oldform multiplicities. Confusing this sum with the multiplicity of one representation leads to incorrect dimension formulas.

### 12.3 The new subspace

At exact level $\mathfrak n$, the **new subspace** is

$$
\widehat\bigoplus_{\pi:\,\mathfrak f(\pi)=\mathfrak n}
\mathcal H_{\pi,\infty}\widehat\otimes\mathbf Cv_f^{\rm new}.
$$

After fixing an archimedean type $\tau$, its $\pi$-contribution is
$\mathcal H_{\pi,\infty}(\tau)\otimes\mathbf Cv_f^{\rm new}$. This is a line only when the
chosen archimedean type space is one dimensional, as for a specified holomorphic lowest-weight
line. Equivalently, after choosing the standard invariant inner product, the newspace is the
orthogonal complement of the closed span of the images of all degeneracy maps from proper
divisor levels. The closure matters before an archimedean spectral window is fixed; in every
finite-dimensional window it is automatic. The
equivalence rests on the local oldvector basis and multiplicity one.

**Proof strategy.** Decompose the fixed-level space by irreducible cuspidal representations. Inside each summand, local newvector theory describes exactly which lower levels map into it. If the representation conductor is a proper divisor, its entire fixed space is old. If its conductor equals the level, its fixed space is the tensor of new lines and has no lower-level source.

The orthogonal-complement definition depends on a Hilbert structure, while the representation-theoretic direct sum does not. Over $\mathbf C$ they agree. Over more general coefficient rings, orthogonal complements may fail to be direct summands, so the characteristic-zero representation decomposition is the clean statement used here.

### 12.4 A counterexample to “new means ramified everywhere”

A global newform of level $\mathfrak n$ is unramified at every $v\nmid\mathfrak n$. It need not be supercuspidal at $v\mid\mathfrak n$. If $v$ divides the level exactly once and the local central character is unramified, the local component is often an unramified twist of Steinberg. At higher exponent it may be a ramified principal series, a ramified special representation, or supercuspidal. Newness specifies a minimal invariant vector, not a local classification family.

This distinction is indispensable when level information is transported through another theorem.
Preserving the conductor exponent preserves the first $K_1$-level, but it does not by itself
preserve a local type. Any argument needing special or supercuspidal behavior must carry that
extra hypothesis explicitly rather than infer it from the word “new.”

### 12.5 Recovering new dimensions

In a one-prime tower, let $D(m)$ be the full fixed-space dimension at exponent $m$ and let $N(n)$ count new lines of exact exponent $n$, with archimedean type fixed. Then

$$
D(m)=\sum_{0\le n\le m}(m-n+1)N(n).
$$

Taking two successive differences yields

$$
N(m)=D(m)-2D(m-1)+D(m-2),
$$

where $D(-1)=D(-2)=0$. At several primes, apply this second-difference operator separately in each valuation coordinate. This is the numerical shadow of the tensor-product oldvector basis.

The formula assumes the characteristic-zero spectral decomposition and local newvector theorem. Over coefficient rings with torsion, degeneracy images can intersect unexpectedly and this direct-sum count need not survive unchanged.

### 12.6 The complete newform theorem

We now collect the local and global assertions in a form that can be invoked without rebuilding
the level tower.

**Theorem 12.1 (global conductor and newforms).** Let $\pi$ be an irreducible unitary cuspidal
automorphic representation of $\mathrm{GL}_2(\mathbf A_F)$.

1. The conductor ideal

   $$
   \mathfrak f(\pi)=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v)}
   $$

   is finite and satisfies $a(\omega_{\pi_v})\le a(\pi_v)$ at every finite place.
2. For every integral ideal $\mathfrak n=\prod_v\mathfrak p_v^{n_v}$,

   $$
   \dim\pi_f^{K_1(\mathfrak n)}=
   \begin{cases}
   \displaystyle\prod_{v<\infty}(n_v-a(\pi_v)+1),
   &\mathfrak f(\pi)\mid\mathfrak n,\\
   0,&\text{otherwise}.
   \end{cases}
   \tag{12.1}
   $$

3. At $\mathfrak n=\mathfrak f(\pi)$ the fixed space is one dimensional. A generator is the
   restricted tensor of the local newvectors.
4. If $\mathfrak f(\pi)\mid\mathfrak n$, the translates

   $$
   \pi_f\!\left(\prod_{v<\infty}
   \begin{pmatrix}\varpi_v^{-j_v}&0\\0&1\end{pmatrix}\right)v_f^{\rm new},
   \qquad 0\le j_v\le n_v-a(\pi_v),
   \tag{12.2}
   $$

   form a basis; only finitely many $j_v$ are nonzero.
5. In a fixed archimedean type $\tau$, the orthogonal complement of the closed span of all
   degeneracy images from proper divisor levels is the direct sum of
   $\mathcal H_{\pi,\infty}(\tau)\otimes\mathbf Cv_f^{\rm new}$ for precisely those $\pi$
   with $\mathfrak f(\pi)=\mathfrak n$.

**Proof strategy.** Sphericality almost everywhere makes the conductor product finite. The local
newvector theorem gives the first line and the translate basis at each exceptional place.
Factorization of invariants tensors those local assertions. Finally, multiplicity one lets us
test oldness inside each irreducible summand independently.

**Proof.** Almost every $\pi_v$ has a $K_v$-fixed vector, so $a(\pi_v)=0$ there and the product
defining $\mathfrak f(\pi)$ is finite. If a scalar unit $zI_2$ belongs to
$K_{1,v}(\mathfrak p_v^n)$, then $z\equiv1\pmod{\mathfrak p_v^n}$. A fixed vector is acted on by
$\omega_{\pi_v}(z)$, so existence at $n=a(\pi_v)$ forces $\omega_{\pi_v}$ to be trivial on
$1+\mathfrak p_v^n$. Hence $a(\omega_{\pi_v})\le a(\pi_v)$.

By Proposition 6.2,

$$
\pi_f^{K_1(\mathfrak n)}
\cong\bigotimes_{v<\infty}
\pi_v^{K_{1,v}(\mathfrak p_v^{n_v})}.
$$

The local newvector theorem says that the $v$th factor vanishes for
$n_v<a(\pi_v)$ and otherwise has dimension $n_v-a(\pi_v)+1$, with basis given by the indicated
diagonal translates. Tensoring proves (12.1), the one-dimensional minimal assertion, and the
basis (12.2).

For the last part, decompose the fixed-level cuspidal space into its multiplicity-one irreducible
summands. If $\mathfrak f(\pi)$ properly divides $\mathfrak n$, choose a prime $v$ at which
$n_v>a(\pi_v)$. The local translate basis at exponent $n_v$ is the sum of the two images from
exponent $n_v-1$; tensoring with the other local factors shows that the whole $\pi$-summand is
old. If $\mathfrak f(\pi)=\mathfrak n$, the finite fixed space is the minimal tensor line and no
lower level has a nonzero $\pi$-fixed vector. Tensoring that finite line with the selected
archimedean type space therefore lies in the orthogonal complement. Distinct irreducible
summands are orthogonal, proving the claimed decomposition. $\square$

The proof reveals three different uniqueness statements. The local theorem makes each minimal
finite line unique. Their tensor product makes the finite global line unique inside one
restricted tensor product. Automorphic multiplicity one ensures that this restricted tensor
product occurs only once in the cusp spectrum. All three are needed before one can speak of “the”
normalized global newform.

## 13. Classical modular forms over $\mathbf Q$

### 13.1 The adelization problem

Let $f$ be a holomorphic cusp form of weight $k\ge2$, level $\Gamma_0(N)$, and nebentype $\varepsilon$. We use the classical convention

$$
f(\gamma z)=\varepsilon(d)(cz+d)^kf(z)
\qquad
\left(\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\Gamma_0(N)\right).
$$

The compatibility condition at $-I$ is

$$
\varepsilon(-1)=(-1)^k.
$$

Adelization must absorb three transformation laws at once: rational matrices act on the left, the finite level acts on the right, and rotation at infinity records weight. The determinant factor that appears below is not cosmetic; it makes the archimedean action unitary and removes the positive real central character.

For $g_\infty\in\mathrm{GL}_2(\mathbf R)^+$, write

$$
j(g_\infty,i)=ci+d,
$$

and set

$$
\Phi_f(g_\infty)
=\det(g_\infty)^{k/2}j(g_\infty,i)^{-k}f(g_\infty i).
$$

Let $K_0(N)\subset\mathrm{GL}_2(\widehat{\mathbf Z})$ be defined by $c\equiv0\pmod N$. Extend $\varepsilon$ to its lower-right entry. Strong approximation gives decompositions

$$
g=\gamma g_\infty k_f,
\qquad \gamma\in\mathrm{GL}_2(\mathbf Q),\quad
k_f\in K_0(N),
$$

after accounting for the determinant class and the second real component. Define

$$
\phi_f(\gamma g_\infty k_f)
=\varepsilon(k_f)^{-1}\Phi_f(g_\infty),
$$

on the positive-determinant component. To reach the other real component, multiply on the left by a rational matrix of negative determinant and reapply the same decomposition. Left rational invariance makes the result independent of that auxiliary matrix. This is not an additional holomorphic choice: a negative-determinant element exchanges the holomorphic and antiholomorphic discrete-series pieces, thereby producing a representation of the full group $\mathrm{GL}_2(\mathbf R)$.

Why is this well defined? If a second decomposition differs by $\delta\in\Gamma_0(N)$, then both $g_\infty$ and $k_f$ are multiplied on the left by $\delta$. The classical law multiplies $\Phi_f$ by $\varepsilon(d_\delta)$, while $\varepsilon(k_f)^{-1}$ is multiplied by its inverse. The two factors cancel. This calculation also fixes the inverse appearing in the right $K_0(N)$ law; changing the classical slash convention changes both inverses together.

### 13.2 Weight, level, and central character

For a rotation

$$
r(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix},
$$

one has

$$
\phi_f(gr(\theta))=e^{ik\theta}\phi_f(g)
$$

with this choice of rotation orientation. On the positive-determinant component, $\phi_f$ lies in the lowest compact type of weight $k$ and generates the holomorphic discrete series of lowest weight $k$. The full $\mathrm{GL}_2(\mathbf R)$-representation also contains the conjugate antiholomorphic piece, exchanged by a negative-determinant element. For $k=1$ one obtains a limit-type representation and several statements need separate treatment, which is why we assume $k\ge2$ here.

At finite level,

$$
\phi_f(gk)=\varepsilon(k)^{-1}\phi_f(g)
\qquad(k\in K_0(N)).
$$

The adelic central character $\omega_\varepsilon$ is the Hecke character attached to the Dirichlet character $\varepsilon$. With the present classical convention its ramified local restriction to units appears by the inverse in the displayed $K_0$ law, while for $p\nmid N$ one has

$$
\omega_{\varepsilon,p}(p)=\varepsilon(p).
$$

At infinity $\omega_{\varepsilon,\infty}(-1)=(-1)^k$, exactly the parity condition. On positive real scalars the determinant factor in $\Phi_f$ makes the unitary central character trivial.

The level $N$ of a chosen form need not equal the conductor of its generated representation. If $f$ is obtained from level $M\mid N$ by a degeneracy map, its representation has conductor $M$. A normalized classical newform is precisely the vector of minimal finite conductor together with the lowest-weight line at infinity.

### 13.3 Cuspidality and Fourier expansions

Write

$$
f(z)=\sum_{n\ge1}a_n(f)e^{2\pi inz}.
$$

The absence of an $n=0$ term at every classical cusp is equivalent to adelic cuspidality. One direction is immediate at the standard cusp: the adelic constant term specializes to the horizontal average of $f$. The other cusps are obtained by right translating $g$, which is why the adelic definition requires vanishing for every $g$.

For the standard additive character and compatible measures, the adelic Whittaker coefficient evaluated on

$$
\begin{pmatrix}y&x\\0&1\end{pmatrix}
$$

recovers $a_n(f)$ after a rational diagonal translate, multiplied by the explicit archimedean factor $y^{k/2}e^{-2\pi ny}$ and the finite normalization. Normalizing $a_1(f)=1$ is exactly the global choice $W(1)=1$ after the standard local newvectors and archimedean Whittaker vector have been fixed.

This is why multiplicativity of Fourier coefficients is not an accidental identity among integers. For coprime indices it comes from factorization of $W=\prod_vW_v$; at powers of one prime it comes from the local spherical recurrence.

### 13.4 Hecke eigenvalues and the unitary shift

Suppose $f$ is a normalized eigenform and $p\nmid N$. Its classical Hecke polynomial is

$$
P_{f,p}(X)=1-a_p(f)X+\varepsilon(p)p^{k-1}X^2.
$$

Let its reciprocal roots be $A_p,B_p$. The automorphic representation in the $L^2$ or unitary normalization has Satake parameters

$$
\alpha_p=p^{-(k-1)/2}A_p,
\qquad
\beta_p=p^{-(k-1)/2}B_p.
$$

Therefore

$$
\alpha_p+\beta_p=p^{-(k-1)/2}a_p(f),
\qquad
\alpha_p\beta_p=\varepsilon(p).
$$

The spectrally normalized operator $\mathsf T_p$ acts on the unitary spherical line by $p^{-(k-1)/2}a_p(f)$, while the raw characteristic double coset acts by

$$
p^{1/2}(\alpha_p+\beta_p)=p^{1-k/2}a_p(f).
$$

The classical operator $T_p$ therefore differs from the raw adelic convolution operator by $p^{k/2-1}$ under this adelization.

It is often more convenient arithmetically to define

$$
\pi^{\rm alg}=\pi^{\rm u}\otimes|\det|_{\mathbf A}^{-(k-1)/2}.
$$

Its local Satake parameters are $A_p,B_p$, so the normalized local Hecke polynomial is literally $P_{f,p}(X)$. Its central character is no longer unitary:

$$
\omega_{\pi^{\rm alg}}
=\omega_\varepsilon|\cdot|_{\mathbf A}^{-(k-1)}.
$$

Correspondingly,

$$
L(s,f)=L\left(s-\frac{k-1}{2},\pi^{\rm u}\right)
=L(s,\pi^{\rm alg}).
$$

This shift accounts for most apparent disagreements between analytic and arithmetic Euler factors.

### 13.5 Primes dividing the level

If $p\mid N$, the local component is determined by more than the unramified polynomial. At exact conductor exponent one, with unramified central character, it is a twist of Steinberg and contributes a one-factor local $L$-function. If only one inducing character in a principal series is unramified, one Euler factor remains. If both inducing characters are ramified, or if the component is supercuspidal, the standard local factor can be $1$ even though the representation carries substantial conductor and type information.

The classical $U_p$ eigenvalue is read from the action on the newvector or an Iwahori line, with a scaling depending on the unitary or algebraic normalization. It is not a Satake eigenvalue of the hyperspecial algebra, because there is no hyperspecial fixed vector. Treating $U_p$ as if it were the good-prime $T_p$ loses the local type.

For example, an elliptic newform of squarefree level and trivial character has a Steinberg twist at each $p\mid N$. Its conductor exponent is one and its $U_p$ eigenvalue records the unramified twisting character. By contrast, a depth-zero supercuspidal component has exponent two and no Iwahori-fixed vector. Both are “ramified,” but their fixed-vector geometry is entirely different.

### 13.6 The classical correspondence

**Theorem 13.1.** Normalized holomorphic newforms of weight $k\ge2$, nebentype $\varepsilon$, and exact level $N$ correspond to cuspidal automorphic representations $\pi$ such that:

- $\pi_\infty$ is the discrete-series representation of the full group $\mathrm{GL}_2(\mathbf R)$ whose restriction to the positive-determinant component contains the holomorphic discrete series of lowest weight $k$;
- $\omega_\pi=\omega_\varepsilon$ in unitary normalization;
- $\mathfrak f(\pi)=N\mathbf Z$;
- the finite newvector transforms under $K_0(N)$ by the inverse lower-right character $\varepsilon^{-1}$ used in Section 13.1;
- for every $p\nmid N$, the arithmetic Satake polynomial is $P_{f,p}(X)$.

The correspondence is one-to-one after the normalization $a_1(f)=1$.

**Proof strategy.** Adelization sends a classical newform to a cusp form with the required local vectors. Its Hecke eigensystem generates an irreducible cuspidal constituent. Strong multiplicity one makes that constituent unique. Conversely, evaluate a lowest-weight, finite-newvector cusp form on the real orbit of $i$; its transformation laws give a classical form, and the Whittaker expansion gives holomorphy and the Fourier series. The local newvector theorem proves exact level.

The normalization is essential. Without $a_1=1$, a single representation corresponds to a line of classical forms, not a distinguished vector. Without “exact level,” all degeneracy images of that line would occur at every multiple of $N$.

### 13.7 Proof of the two-way classical dictionary

The proof strategy in Theorem 13.1 contains several compatibility checks. We now carry them out.

Start with a normalized newform $f$. The adelization of Section 13.1 is well defined because two
strong-approximation decompositions differ by an element of $G(\mathbf Q)$ whose finite component
lies in $K_0(N)$. The classical modular law and the inverse lower-right character cancel exactly.
The factor $\det(g_\infty)^{k/2}j(g_\infty,i)^{-k}$ makes positive real scalars act trivially and
makes right rotation act by $e^{ik\theta}$. Hence the archimedean cyclic module contains the
lowest-weight $k$ line. The raising and lowering relations at infinity then identify it with the
holomorphic discrete series, not merely with some representation having the same Casimir.

The constant term of the adelization at a right translate $g$ is the constant Fourier coefficient
of $f$ at the cusp represented by $g$. A classical cusp form vanishes at every cusp, so the
adelization is cuspidal. Conversely, adelic cuspidality gives vanishing at every rational cusp,
not only at infinity. The finite-level and archimedean-type conditions place the adelization in a
finite-dimensional simultaneous Hecke module. A normalized Hecke eigenform therefore generates
an irreducible cuspidal constituent $\pi_f$.

At $p\nmid N$, the classical double-coset formula and Section 7.6 give

$$
P_p(\pi_f^{\rm u};X)=
1-p^{-(k-1)/2}a_p(f)X+\varepsilon(p)X^2.
\tag{13.1}
$$

At $p\mid N$, the vector is fixed by $K_1(p^{v_p(N)})$, so
$a(\pi_{f,p})\le v_p(N)$. If the inequality were strict at some $p$, Theorem 12.1 would express
the finite vector as a linear combination of degeneracy images from a proper divisor of $N$.
That would make $f$ old, contrary to newness. Thus

$$
a(\pi_{f,p})=v_p(N)
$$

at every $p$, and the global conductor is exactly $N\mathbf Z$.

Suppose two normalized newforms $f$ and $g$ yield the same automorphic representation. Their
finite newvector lines agree, and their lowest-weight $k$ lines agree. Therefore their
adelizations differ by a scalar. The Whittaker coefficient at $1$ is the first Fourier
coefficient, so $a_1(f)=a_1(g)=1$ makes that scalar $1$. This proves injectivity. Alternatively,
equality of almost all good Hecke polynomials first gives equality of representations by strong
multiplicity one, and the same line argument gives equality of forms.

For the converse, let $\pi$ have the stated infinity type, conductor, and central character.
Choose the finite newvector $v_f^\circ$, unique up to scalar, and a lowest-weight vector
$v_\infty^+$ in the holomorphic half of $\pi_\infty$. Automorphic multiplicity one realizes
$v_\infty^+\otimes v_f^\circ$ as a cusp form $\phi$ unique up to scalar. Define for $z=x+iy$

$$
f_\phi(z)=y^{-k/2}\phi(g_z),
\qquad
g_z=\begin{pmatrix}y^{1/2}&xy^{-1/2}\\0&y^{-1/2}\end{pmatrix}.
\tag{13.2}
$$

The exact scalar power in (13.2) is inverse to the adelization convention. Left rational
invariance, the right $K_0(N)$ character of the newvector, and the weight-$k$ rotation law imply

$$
f_\phi(\gamma z)=\varepsilon(d)(cz+d)^k f_\phi(z)
$$

for $\gamma\in\Gamma_0(N)$, with the chosen nebentype convention.

It remains to prove holomorphy. The lowering operator at infinity annihilates the lowest-weight
vector. In Iwasawa coordinates, that operator is a nonzero scalar multiple of

$$
y\left(\frac\partial{\partial x}+i\frac\partial{\partial y}\right)
$$

after the factor $y^{k/2}$ has been removed. Hence it gives the Cauchy--Riemann equation
$\partial f_\phi/\partial\bar z=0$. Cuspidality and the Whittaker expansion give

$$
f_\phi(z)=\sum_{n\ge1}a_n e^{2\pi inz};
$$

negative $n$ are absent because the holomorphic discrete-series Whittaker function is supported
on the positive real orbit. Rapid decrease gives convergence on compact subsets and vanishing at
all cusps. Thus $f_\phi$ is a holomorphic cusp form.

The minimality of $v_f^\circ$ makes the form new of exact level $N$, and the spherical Hecke
calculation recovers (13.1). Finally scale $\phi$ so that $a_1=1$. This constructs the inverse
map and completes the proof of Theorem 13.1. $\square$

Two edge cases explain the hypotheses. Weight one selects a limit of discrete series, so the
square-integrable and cohomological arguments used above change. A form of level $N$ that is not
new still adelizes, but its representation conductor is only a divisor of $N$ and several
oldvectors may share all good-prime eigenvalues. Neither case contradicts the dictionary; each
requires a different statement.

### 13.8 A complete level-one example

The discriminant form

$$
\Delta(z)=q\prod_{n\ge1}(1-q^n)^{24}
=\sum_{n\ge1}\tau(n)q^n,
\qquad q=e^{2\pi iz},
$$

is a normalized cusp form of weight $12$, level $1$, and trivial nebentype. Its first
coefficients include

$$
\tau(1)=1,\qquad \tau(2)=-24,\qquad \tau(3)=252.
$$

Let $\pi_\Delta^{\rm u}$ be its unitary automorphic representation. The dictionary gives

$$
\pi_{\Delta,\infty}^{\rm u}\cong D_{12},
\qquad
\mathfrak f(\pi_\Delta)=1,
\qquad
\omega_{\pi_\Delta}=1.
$$

Thus every finite component is spherical. If $A_p,B_p$ are the reciprocal roots of

$$
1-\tau(p)X+p^{11}X^2,
$$

then the unitary Satake parameters are

$$
\alpha_p=p^{-11/2}A_p,
\qquad
\beta_p=p^{-11/2}B_p.
$$

They satisfy

$$
\alpha_p+\beta_p=p^{-11/2}\tau(p),
\qquad
\alpha_p\beta_p=1.
$$

Consequently the spectrally normalized Hecke operator acts by $p^{-11/2}\tau(p)$, whereas the
raw characteristic function of
$K_p\operatorname{diag}(p,1)K_p$ acts by

$$
p^{1/2}(\alpha_p+\beta_p)=p^{-5}\tau(p).
$$

The classical $T_p$ acts by $\tau(p)$. The three eigenvalues differ because the three operators
use different normalizations; they describe the same spherical representation.

The spherical Whittaker recurrence gives

$$
\tau(p^{r+2})=\tau(p)\tau(p^{r+1})-p^{11}\tau(p^r),
\qquad r\ge0.
$$

Factorization of the global Whittaker function gives

$$
\tau(mn)=\tau(m)\tau(n)
\qquad ((m,n)=1).
$$

These classical identities are therefore local and global tensor statements respectively. For
example,

$$
\tau(4)=\tau(2)^2-2^{11}=-1472.
$$

At a higher level $M$, the same representation contributes an oldspace of dimension
$\prod_{p\mid M}(v_p(M)+1)$, spanned by the adelic translates corresponding classically to
$\Delta(dz)$ for $d\mid M$. All those vectors have the same $T_\ell$ eigenvalues for
$\ell\nmid M$. The unique level-one newvector is selected by minimality and by the normalization
$\tau(1)=1$.

Finally,

$$
L(s,\Delta)
=L\left(s-\frac{11}{2},\pi_\Delta^{\rm u}\right).
$$

This example simultaneously checks weight, conductor, central character, the unitary shift, the
raw half-power, the Whittaker recurrence, oldform growth, and the $L$-function translation.

## 14. Hilbert modular representations

### 14.1 Several real places, one adelic object

Now suppose $F$ is totally real of degree $d$. Its symmetric space is a product of $d$ upper half-planes, one for each embedding $\tau:F\hookrightarrow\mathbf R$. A Hilbert modular form has a weight vector

$$
\mathbf k=(k_\tau)_{\tau:F\hookrightarrow\mathbf R}.
$$

The adelic construction is the same as over $\mathbf Q$, but it removes a serious classical nuisance: different ideal classes give different connected components and sometimes different congruence groups. The quotient

$$
G(F)\backslash G(\mathbf A)/(K_\infty^+U)
$$

holds all components at once. The narrow class group indexes determinant components after positive archimedean scalars are taken into account.

A holomorphic Hilbert cusp form adelizes to a cusp form whose restriction to the positive-determinant component at each real place contains the holomorphic discrete series of lowest weight $k_\tau$. The representation of the full local group also contains the conjugate piece exchanged by negative determinant. The finite part has a level and central character exactly as in Chapters 11 and 12. The tensor product across real places replaces the single lowest-weight line over $\mathbf Q$.

### 14.2 Algebraic and cohomological weights

The clean algebraic parametrization uses integers $a_\tau\ge b_\tau$ and the coefficient representation

$$
V_{a,b}=\bigotimes_\tau
\left(\operatorname{Sym}^{a_\tau-b_\tau}\mathbf C^2
\otimes\det^{b_\tau}\right).
$$

The associated holomorphic discrete-series weight is

$$
k_\tau=a_\tau-b_\tau+2.
$$

For an algebraic representation of the group with a single rational central weight, one requires

$$
a_\tau+b_\tau=w
$$

independent of $\tau$. Hence

$$
k_\tau\equiv w\pmod2
$$

for every $\tau$. This is the parity constraint on a cohomological weight. It is not imposed by local representation theory at one real place; it comes from asking the archimedean data and the global algebraic central character to agree on $F^\times$.

The frequently used “cohomological” or “$L$-algebraic” normalization differs from the unitary normalization by a norm power. In the above convention, the arithmetic determinant term at an unramified prime ideal has size governed by $q_v^{w+1}$, while the unitary central character has removed that power. For the classical weight-$k$ case, $a=k-2$, $b=0$, so $w=k-2$ and $w+1=k-1$, recovering Chapter 13.

### 14.3 Parity from the center

At a real place, the lowest-weight discrete series of weight $k_\tau$ sends the scalar $-1$ to $(-1)^{k_\tau}$. On the principal idele $-1$, the product of all local central-character values must be $1$. Therefore the parities of the $k_\tau$, the finite central character, and any prescribed archimedean sign characters must satisfy this product constraint.

This gives a simple counterexample to an overly local construction. Choose two real places and weights $2$ and $3$, with trivial finite central character and no compensating signs. Each discrete series exists locally, but their tensor product cannot be the infinity type of an automorphic representation with trivial global central character: on the principal idele $-1$, the product of the two archimedean scalar actions is $(-1)^2(-1)^3=-1$, whereas a Hecke character must be trivial on $F^\times$.

More generally, an algebraic Hecke central character supplies sign exponents at real places and a common norm exponent. Its restriction to $F^\times$ imposes both the parity equations and the compatibility of central weights. These are global arithmetic conditions, not optional conventions.

### 14.4 Hilbert Hecke data and conductor

Let $\mathfrak p\nmid\mathfrak n$ be a prime ideal at which $\pi$ is unramified. The representation-normalized polynomial is

$$
1-(\alpha_\mathfrak p+\beta_\mathfrak p)X
+\omega_\pi(\varpi_\mathfrak p)X^2.
$$

After the algebraic twist appropriate to the central weight $w$, the polynomial takes the arithmetic form

$$
1-a_\mathfrak pX
+\varepsilon(\mathfrak p)q_\mathfrak p^{w+1}X^2.
$$

The first coefficient is the Hilbert Hecke eigenvalue in the corresponding classical normalization. The formula assumes that the algebraic normalization has been fixed globally; when weights are described with a different determinant twist, both the norm exponent and the $L$-function shift change together.

At primes dividing the level, the ideal conductor exponent $a(\pi_\mathfrak p)$ determines the minimal $K_1$-level, and the local type distinguishes principal-series, special, and supercuspidal behavior. The global newvector is the tensor of these local newvectors. Oldform multiplicity at $\mathfrak n$ remains

$$
\prod_{\mathfrak p\mid\mathfrak n}
\bigl(v_\mathfrak p(\mathfrak n)-a(\pi_\mathfrak p)+1\bigr).
$$

Nothing in this formula requires the narrow class number to be one. Adeles have already assembled the class-group components.

### 14.5 The Hilbert correspondence

A normalized holomorphic Hilbert newform of cohomological weight $(a_\tau,b_\tau)$, exact ideal level $\mathfrak n$, and compatible nebentype determines a unique cuspidal automorphic representation $\pi$. At each real place, $\pi_\tau$ is the full-group discrete-series representation with the central twist dictated by $(a_\tau,b_\tau)$, and its restriction to the positive-determinant component contains $D_{k_\tau}^{\rm hol}$. If that full representation is denoted $D_{k_\tau,s_\tau}$, the exact statement is

$$
\pi_\infty\cong\bigotimes_{\tau}D_{k_\tau,s_\tau},
\qquad
\mathfrak f(\pi)=\mathfrak n.
$$

The customary expression $\otimes_\tau D_{k_\tau}^{\rm hol}$ names the chosen lowest-weight line
in the restriction to the identity components; it is not an irreducible representation of the
product of the full disconnected groups.

At unramified primes its Hecke eigenvalues determine $\pi_\mathfrak p$ by the Satake polynomial. Conversely, a cuspidal representation with these holomorphic infinity types and a finite newvector produces a Hilbert newform on every connected component; the adelic transformation law glues those componentwise forms.

The statement is representation theoretic. No passage to a quaternion algebra, no transfer, and no change of base field is involved. Those operations require separate global theorems.

### 14.6 Components, ideals, and the proof of descent

Over a totally real field, the main extra difficulty is not local representation theory but the
absence of one preferred connected component. We explain why the adelic correspondence handles
that difficulty without a class-number hypothesis.

Fix a compact open $U\subset G(\mathbf A_{F,f})$. The determinant induces a map from the adelic
double quotient to

$$
F_{>0}^\times\backslash\mathbf A_{F,f}^\times/\det U,
\tag{14.1}
$$

where $F_{>0}^\times$ denotes the totally positive elements. The quotient is finite: after
discarding a congruence subgroup of finite index it is a narrow ray class group. Choose finite
ideles $t_1,\ldots,t_h$ representing it and matrices $g_i$ with determinant $t_i$. Strong
approximation for $\mathrm{SL}_2$ gives

$$
G(F)\backslash G(\mathbf A)/(U K_\infty^+)
=\coprod_{i=1}^h
\Gamma_i\backslash\mathfrak H^d,
\tag{14.2}
$$

where $K_\infty^+$ is the product of positive scalar groups and rotations, and
$\Gamma_i=G(F)\cap g_iUg_i^{-1}G(F_\infty)^+$ acts through fractional linear transformations at
the $d$ real embeddings.

**Proof of (14.2).** The determinant class of an adelic matrix selects one $t_i$. Multiplying on
the left by $G(F)$ and on the right by $U$ reduces its determinant to $t_i$ times a totally
positive archimedean scalar. After removing that scalar, the quotient matrix has determinant one.
Strong approximation for $\mathrm{SL}_2$ moves its finite component into the determinant-one part
of $g_iUg_i^{-1}$. What remains is an archimedean point modulo the rational stabilizer
$\Gamma_i$. Two such points give the same adelic class precisely when they differ by
$\Gamma_i$. This proves the disjoint union. $\square$

An adelic form of finite level therefore restricts to a tuple $(f_i)$ of functions on
$\mathfrak H^d$. Its right transformation under $U$, its central character, and its lowest
compact types become the componentwise Hilbert modular laws. Conversely, suppose such a tuple is
given and satisfies those laws. Define an adelic function on the $i$th piece of (14.2) by reversing
the automorphy factor. Invariance under $\Gamma_i$ makes the definition independent of the
archimedean representative. The determinant classes are disjoint, so the definitions glue. This
constructs the two-way passage between adelic forms and componentwise Hilbert modular forms.

Cuspidality is also componentwise. Rational parabolics and their cusps meet every component, and
the adelic constant term at a translate specializes to the constant Fourier coefficient at the
corresponding cusp of some $\Gamma_i\backslash\mathfrak H^d$. Thus vanishing of every component
constant term is equivalent to adelic cuspidality.

Holomorphy is local at infinity. At each real place, choosing the lowest-weight line and applying
the same lowering-operator calculation as in Section 13.7 gives a Cauchy--Riemann equation in the
corresponding variable. The tensor of these equations makes the component function holomorphic
on $\mathfrak H^d$. The negative-determinant components provide the conjugate pieces required for
a representation of the full local groups; they do not add independent holomorphic data.

At finite places, Theorem 12.1 applies without change. If the form is new of exact ideal level
$\mathfrak n$, then

$$
a(\pi_\mathfrak p)=v_\mathfrak p(\mathfrak n)
$$

for every prime ideal $\mathfrak p$. Conversely the tensor of local newvectors gives exact level.
At an unramified prime, the Satake polynomial supplies the classical Hilbert Hecke polynomial
after the common algebraic norm twist has been made. Strong multiplicity one shows that almost
all these polynomials determine the same global representation across all the components in
(14.2).

This proves the Hilbert correspondence of Section 14.5. The narrow class group changes the number
of classical components, but not the automorphic multiplicity, the conductor, or the uniqueness
of the newvector. Treating each component as a separate automorphic representation would count
one global object several times.

### 14.7 Parallel weight two as a global test case

Let $F$ be totally real of degree $d$ and consider the parallel-weight-two, unitary infinity type

$$
\pi_\infty=\bigotimes_{v\mid\infty}D_2.
$$

Each factor has trivial central character, minimal rotation weights $2$ and $-2$, and contributes
in relative Lie algebra cohomological degree one with trivial algebraic coefficients. Their tensor
product contributes in degree $d$. Relative to the connected maximal compact, the cohomology has
$2^d$ sign lines, one for each choice of holomorphic or antiholomorphic direction at the $d$ real
places. These sign lines belong to one archimedean representation; they are not $2^d$ different
automorphic multiplicities.

Suppose $\pi$ is cuspidal with this infinity type, finite conductor $\mathfrak n$, and trivial
central character. Its finite newvector line is

$$
\mathbf Cv_f^\circ
=\bigotimes_{v<\infty}\mathbf Cv_v^\circ.
$$

Choosing the all-holomorphic archimedean line gives a tuple of parallel-weight-two Hilbert
newforms on the components (14.2). The other sign choices give the conjugate and mixed
cohomological realizations. Automorphic multiplicity one says that all these realizations arise
from the same $\pi$.

At a prime $\mathfrak p\nmid\mathfrak n$, write the unitary polynomial as

$$
1-(\alpha_\mathfrak p+\beta_\mathfrak p)X+X^2.
$$

The arithmetic weight-two roots are

$$
A_\mathfrak p=q_\mathfrak p^{1/2}\alpha_\mathfrak p,
\qquad
B_\mathfrak p=q_\mathfrak p^{1/2}\beta_\mathfrak p,
$$

so the Hilbert Hecke polynomial is

$$
1-a_\mathfrak pX+q_\mathfrak pX^2,
\qquad
a_\mathfrak p=A_\mathfrak p+B_\mathfrak p.
$$

The product term $q_\mathfrak p$ is forced by the weight, while the unitary determinant term is
$1$. Confusing these two polynomials would incorrectly assign a nonunitary central character to
the $L^2$ representation.

If $v_\mathfrak p(\mathfrak n)=1$, trivial central character forces
$\pi_\mathfrak p$ to be an unramified twist of Steinberg by Section 6.7. If the exponent is two,
the local component could be principal series, a ramified special representation, or
supercuspidal; conductor alone does not decide. This is exactly the local information later
comparisons must preserve.

Strong multiplicity one gives the recognition statement: the polynomials

$$
1-a_\mathfrak pX+q_\mathfrak pX^2
$$

outside a finite set determine $\pi$, including its components at primes dividing
$\mathfrak n$. The newvector theorem then recovers the exact conductor and its componentwise
Hilbert newform. Thus parallel weight two supplies a stringent test of the whole dictionary: the
archimedean normalization is cohomological with trivial coefficients, the finite determinant
shift is $q_\mathfrak p^{1/2}$ per root, and the finite minimal level is the conductor ideal.

## 15. Algebraicity and rationality

### 15.1 What finite-dimensionality proves

The analytic automorphic theory developed so far does not by itself construct a number-field
model of a space of forms. In this chapter assume that a holomorphic classical or Hilbert space
of fixed cohomological weight, level, and nebentype has been equipped with its arithmetic
$q$-expansion structure: a finite-dimensional model over a number field $E_0$ containing the
nebentype values, together with Hecke operators defined over $E_0$. Constructing this structure
from integral models and proving the $q$-expansion principle are separate arithmetic inputs; no
result in Chapters 1--14 or 16--17 depends on them.

Under this explicit hypothesis, the eigenvalues of a simultaneous Hecke eigenform are algebraic
numbers. Indeed, extend scalars from the $E_0$-space to $\mathbf C$. Each Hecke operator has a
matrix over $E_0$, so every eigenvalue is a root of its characteristic polynomial in $E_0[X]$.
The image of the full commuting Hecke algebra is a finite-dimensional $E_0$-algebra and is
therefore generated by finitely many elements. The values of one eigencharacter consequently
lie in the finite extension generated by the eigenvalues of those finitely many generators.

Define the **Hecke field** of a normalized cohomological eigenform by

$$
E_f=\mathbf Q\bigl(a_\mathfrak p(f),
\varepsilon(\mathfrak p):\mathfrak p\nmid\mathfrak n\bigr),
$$

or include the finitely many bad-place eigenvalues when the complete finite eigensystem is desired. Strong multiplicity one shows that the good-prime system determines the complex cuspidal representation, but it does not say that every vector in that representation has coordinates in $E_f$.

### 15.2 Field of rationality versus field of definition

The **field of rationality** of $\pi_f$ is the fixed field of automorphisms
$\sigma\in\operatorname{Aut}(\mathbf C)$ for which the finite representation $\pi_f^\sigma$
is isomorphic to $\pi_f$. When the arithmetic structure of Section 15.1 is present, Galois
conjugation produces the conjugate eigensystems, and strong multiplicity one shows that fixing
the unramified Hecke eigenvalues and central-character values is equivalent to fixing the finite
isomorphism class. Under that hypothesis the field of rationality is the corresponding Hecke
field, after the normalization data are included.

A **field of definition** is a number field $E$ over which a representation model and its group action can actually be realized. A field of rationality need not automatically be a field of definition: descent can be obstructed by a nontrivial division algebra of endomorphisms, and choosing a particular local type or archimedean model can enlarge the necessary field. For the one-dimensional newvector eigensystem, the normalized eigenline is often defined over the Hecke field; this does not by itself descend the entire infinite-dimensional representation.

This distinction prevents a common overstatement. Algebraic Hecke eigenvalues prove that the eigencharacter is number-field valued. They do not prove that every local representation, every invariant pairing, and every chosen Whittaker normalization descends to exactly that same field.

### 15.3 Galois conjugation of eigenforms

Retain the arithmetic $q$-expansion structure assumed in Section 15.1 and let
$\sigma\in\operatorname{Aut}(\mathbf C)$. Applying $\sigma$ to the algebraic Fourier
coefficients, the defining $E_0$-linear relations, and the nebentype values gives another
eigenform, with

$$
a_\mathfrak p(f^\sigma)=\sigma(a_\mathfrak p(f)),
\qquad
\varepsilon^\sigma=\sigma\circ\varepsilon.
$$

The associated finite automorphic representation has unramified Satake polynomials obtained by applying $\sigma$ to the algebraically normalized coefficients. At infinity one must retain the cohomological weight through its algebraic coefficient system; applying a wild automorphism directly to analytic quantities such as $q_v^{1/2}$ is not a meaningful replacement for this rational structure.

The orbit of the eigensystem under such conjugation is finite because its values lie in a number
field. A form with rational coefficients has Hecke field $\mathbf Q$, but this still does not
imply that all analytic normalizations are rational: periods, Petersson norms, and unitary
square-root scalings generally are not.

### 15.4 The boundary of the algebraicity assertion

For a general Maass cusp form, spectral theory gives complex Hecke eigenvalues but does not by itself prove that they are algebraic. Finite dimensionality over $\mathbf C$ only says that an eigenvalue is a root of a characteristic polynomial with complex coefficients. The algebraic conclusion for holomorphic cohomological forms used an independently constructed number-field structure.

Similarly, an arbitrary unitary automorphic representation can have archimedean spectral parameters with no established algebraicity. One must not transfer the cohomological theorem to all cusp forms merely because their unramified Hecke operators look formally identical.

This boundary keeps the logical direction clear. The analytic theory constructs complex
representations and proves rigidity from their Hecke data. Arithmetic rational structures add a
new layer; they are not consequences of multiplicity one. Accordingly, this chapter records only
the rationality of the cohomological eigensystem and does not assert an integral lattice or a
canonical field of definition for the full packet.

## 16. Hecke algebras on fixed-level spaces

### 16.1 The restricted tensor algebra

Let $U=\prod_vU_v\subset G(\mathbf A_f)$ be compact open. Its Hecke algebra is

$$
\mathcal H(G(\mathbf A_f),U)
=\bigotimes_{v<\infty}'\mathcal H(G_v,U_v),
$$

where the reference element is the idempotent $\mathbf1_{U_v}$ with $\operatorname{vol}(U_v)=1$. A pure tensor differs from the reference element at only finitely many places. Convolution factors place by place.

If $\Sigma$ contains the primes dividing the level and the ramification of the central character, the away-from-$\Sigma$ spherical algebra is generated by $T_v^{\rm raw}$ and $S_v^{\pm1}$ for $v\notin\Sigma$. It is commutative. At primes in the level, $\mathcal H(G_v,U_v)$ can be noncommutative, and operators called $U_v$ depend on the chosen $K_0$, $K_1$, or Iwahori level. Commutativity away from level does not imply commutativity of the full Hecke algebra.

### 16.2 Spectral decomposition of the action

Fix a finite set of $K_\infty$-types $\tau$. The cuspidal fixed-level space decomposes as

$$
\mathcal A_{\mathrm{cusp}}(U,\tau,\omega)
\cong\bigoplus_\pi
\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty)
\otimes\pi_f^U.
$$

Only finitely many $\pi$ occur after the infinitesimal character is also fixed or bounded appropriately. The local Hecke algebra acts on $\pi_f^U$ and trivially on the archimedean multiplicity factor. At hyperspecial places its character is the Satake character of $\pi_v$.

If the space is holomorphic of fixed weight, it is already finite dimensional. The commuting good-place Hecke operators then admit simultaneous eigenvectors. Strong multiplicity one says that a full good-place eigensystem belongs to at most one cuspidal representation, but the corresponding eigenspace at nonminimal level can have dimension greater than one because of oldvectors.

### 16.3 Eigenvalue multiplicity versus representation multiplicity

Suppose $f$ is a level-$N$ newform and view it at level $Np$ with $p\nmid N$. The two degeneracy images have the same $T_\ell$ eigenvalues for every $\ell\nmid Np$. Thus the away-from-$Np$ Hecke eigenspace has dimension at least two. This does not contradict multiplicity one: both vectors lie in the single automorphic representation $\pi_f$, whose local $K_1(p)$-fixed space is two dimensional.

Adding the operator at $p$ may split this oldspace into two stabilized eigenlines when its characteristic polynomial has distinct roots. If the roots coincide, the action may have a generalized eigenspace. Thus “one good-prime eigensystem” identifies a representation, while “one-dimensional eigenspace at a chosen level” is a separate linear-algebra statement.

The section therefore reconciles two uses of the word multiplicity. Representation multiplicity
counts copies in the cuspidal spectrum and is one. Eigenvalue multiplicity counts vectors after a
level has been fixed and can grow with every oldform direction. Hecke algebras at the bad places
organize that larger space but do not create new global representations.

### 16.4 Central operators and fixed character

Before fixing $\omega$, the scalar double cosets $S_v$ carry genuine information. On the $\omega$-central-character subspace they act by known scalars $\omega_v(\varpi_v)$. One may then suppress them from the list of generators, but their values still form the determinant term of every Hecke polynomial.

Forgetting them without fixing the central character can identify different representations whose normalized trace parameters agree but determinant parameters differ. Strong multiplicity one uses the full unramified local component, equivalently both symmetric functions of the two Satake parameters.

Central operators are thus redundant only after central character has been made part of the
ambient space. This is why classical uniqueness statements safely compare only $T_p$ eigenvalues
when the nebentype is fixed, while a representation-theoretic statement with varying central
character must retain the $S_v$ data as well.

## 17. The global dictionary

### 17.1 From eigenform data to local representations

For a normalized classical or Hilbert eigenform $f$, the passage to $\pi_f$ can be read one place at a time:

| form-theoretic datum                              | automorphic datum                  | local meaning                                                                                        |
| ------------------------------------------------- | ---------------------------------- | ---------------------------------------------------------------------------------------------------- |
| weight $k_\tau$                                   | $\pi_\tau$ at a real place         | full discrete series whose positive component contains the holomorphic lowest-weight $k_\tau$ member |
| nebentype $\varepsilon$                           | central character $\omega_{\pi_f}$ | scalar action; parity at infinity                                                                    |
| exact level $\mathfrak n$                         | conductor $\mathfrak f(\pi_f)$     | $a(\pi_v)=v(\mathfrak n)$                                                                            |
| normalized newform                                | pure tensor newvector              | local newvectors and lowest-weight vectors                                                           |
| $a_\mathfrak p$ for $\mathfrak p\nmid\mathfrak n$ | arithmetic Satake trace            | sum of algebraically normalized parameters                                                           |
| determinant term of the Hecke polynomial          | central Satake eigenvalue          | product of the two parameters                                                                        |
| Fourier coefficient                               | global Whittaker value             | product of local Whittaker values                                                                    |
| degeneracy images                                 | oldvectors                         | diagonal translates of the local newvector                                                           |
| twist by a character                              | $\pi_f\otimes\chi$                 | determinant twist at every place                                                                     |

At a good finite place, the polynomial determines an unramified principal-series constituent. At a bad place, conductor plus the $U_v$ eigenvalue may distinguish special from some principal-series cases, but conductor alone never determines the local representation. A local type, its Hecke action, or further local factors can be needed.

### 17.2 Normalization dictionary

Let a classical weight-$k$ form have arithmetic roots $A_v,B_v$. Then the central conversion is

$$
\begin{array}{c|c|c}
&\text{unitary representation}&\text{algebraic normalization}\\ \hline
\text{Satake roots}&q_v^{-(k-1)/2}A_v,\ q_v^{-(k-1)/2}B_v&A_v,B_v\\
\text{trace}&q_v^{-(k-1)/2}a_v&a_v\\
\text{product}&\varepsilon(v)&\varepsilon(v)q_v^{k-1}\\
\text{central character}&\omega_\varepsilon&\omega_\varepsilon|\cdot|^{-(k-1)}\\
\text{$L$-function}&L(s,\pi^{\rm u})&L(s,f)=L(s,\pi^{\rm alg})
\end{array}
$$

The raw characteristic double coset contributes one further factor $q_v^{1/2}$ to the trace eigenvalue. These three rows—unitary Satake, algebraic Satake, and raw convolution—must not be collapsed.

### 17.3 Reading local types from global data

The following implications are reliable:

- $v\nmid\mathfrak f(\pi)$ if and only if $\pi_v$ is spherical;
- $a(\pi_v)=1$ with unramified central character forces an infinite-dimensional generic representation to be an unramified twist of Steinberg;
- an irreducible principal series has conductor equal to the sum of the character conductors;
- an unramified twist of Steinberg has exponent $1$, and a ramified twist has twice the character exponent;
- a depth-zero supercuspidal has exponent $2$ and no Iwahori-fixed vector.

The converses must be used carefully. Conductor exponent $2$ does not force depth-zero supercuspidal: it can also arise from a principal series with two conductor-one characters or a ramified Steinberg twist. Likewise, a one-factor local $L$-function suggests special or partly ramified principal-series behavior but is not, by itself, a complete local type.

### 17.4 Twists through the dictionary

If $f$ corresponds to $\pi$ and $\chi$ is a finite-order Hecke character, the twisted representation has

$$
\omega_{\pi\otimes\chi}=\omega_\pi\chi^2,
$$

and at every unramified place

$$
a_v(f\otimes\chi)=\chi_v(\varpi_v)a_v(f)
$$

in the algebraic normalization. The two Satake roots both acquire the same factor. At ramified places the conductor must be recomputed locally; it can rise, stay fixed, or in cancellation cases fall.

The archimedean weight is unchanged by a finite-order character except for compatible sign data. A norm-power twist changes the normalization and infinitesimal central character rather than producing a new holomorphic weight in the naive sense.

### 17.5 Reconstruction and its limits

Almost all Hecke polynomials reconstruct a cuspidal representation by strong multiplicity one. They do not reconstruct a chosen vector at a higher level, because oldspaces can have dimension greater than one. Adding the conductor and choosing the newvector line recovers the normalized eigenform, once the archimedean lowest-weight vector and first Whittaker coefficient are normalized.

The dictionary deliberately stops at the automorphic representation. It does not construct a representation of a Galois group from the Hecke polynomials, does not transfer $\pi$ to a quaternion algebra, and does not compare it across field extensions. Those later constructions must preserve the central character, conductor, twists, and unramified polynomials assembled here.

The limit is part of the dictionary rather than a defect in it. Good-prime data name the global
isomorphism class; conductor names its first finite level; local type refines its ramified behavior;
and a vector normalization selects one form. Asking the same data to produce an object in a
different category would require a new existence theorem, so no such theorem is hidden in the
word “reconstruction.”

### 17.6 The automorphic representation package

The principal conclusions can be stated as one theorem. Its purpose is not compression but
dependency control: each item records exactly which hypotheses later arguments may use.

**Theorem 17.1 (cuspidal automorphic representations of $\mathrm{GL}_2$).** Let $F$ be a number
field and let $\omega:F^\times\backslash\mathbf A_F^\times\to\mathbf C^\times$ be unitary.

1. The fixed-central-character cuspidal Hilbert space is a multiplicity-free discrete sum

   $$
   L^2_{\rm cusp,\omega}
   =\widehat\bigoplus_{\pi\in\mathcal A_{\rm cusp}(G,\omega)}\mathcal H_\pi.
   $$

2. Every summand has a unique factorization

   $$
   \pi\cong\bigotimes_v'\pi_v
   $$

   into irreducible admissible local representations, unitary in this normalization and
   spherical at almost every finite place.
3. Every $\pi_v$ is generic. A global Whittaker coefficient realizes $\pi$ faithfully, is unique
   up to scalar, and factors on pure tensors into the product of the local Whittaker functions.
4. At a spherical finite place, the unordered Satake pair $\{\alpha_v,\beta_v\}$ is determined by
   the normalized polynomial

   $$
   P_v(X)=1-(\alpha_v+\beta_v)X
   +\omega_v(\varpi_v)X^2,
   $$

   while the raw double coset acts by $q_v^{1/2}(\alpha_v+\beta_v)$.
5. If two irreducible cuspidal representations have the same local components, equivalently the
   same unramified Hecke polynomials, outside a finite set, then they are isomorphic.
6. The local conductor exponents form a finite ideal $\mathfrak f(\pi)$; the minimal global
   $K_1$-fixed space is a line; higher fixed spaces have the translate basis and dimension formula
   of Theorem 12.1; and the orthogonal newspace at level $\mathfrak n$ consists exactly of the
   summands of conductor $\mathfrak n$.
7. For $F=\mathbf Q$, holomorphic newforms of weight $k\ge2$ and exact level are equivalent to
   representations with the matching discrete-series infinity type and finite newvector. For
   totally real $F$, the analogous statement holds for cohomological Hilbert newforms on all
   narrow-class components. The unitary and algebraic Satake parameters differ by the prescribed
   half-power of the residue norm.

**Proof.** Discreteness and finite multiplicity are Theorem 5.1, obtained from reduction theory
and typewise compactness. The factorization theorem is Theorem 6.1. Fourier inversion, local
uniqueness, and restricted tensor compatibility prove part 3 in Theorems 8.1--8.3. The Satake
calculation is Section 7.6. Global Whittaker uniqueness turns finite multiplicity into unit
multiplicity in Theorem 9.1, while the Rankin--Selberg pole comparison proves part 5 in Theorem
9.2 and Section 9.5. Theorem 12.1 proves part 6. Sections 13.7 and 14.6 prove the two classical
dictionaries, including exact level and component gluing. $\square$

The unitary hypothesis belongs to the Hilbert-space and pole statements. An essentially unitary
cuspidal representation is obtained from a unitary one by a real norm twist; translating every
local parameter, central character, and complex variable by that same twist gives the analogous
package. An arbitrary nonunitary normalization should not be inserted into the pole criterion
without making this translation.

The theorem is deliberately about cuspidal representations. One-dimensional determinant
characters and residual representations belong to the noncuspidal discrete spectrum; Eisenstein
families contribute continuous spectrum. They do not satisfy the cuspidal Whittaker reconstruction
used here. Likewise, a higher-level vector is not determined by the representation alone: the
oldvector space can have dimension greater than one. The theorem determines the representation
and its minimal line, which is exactly the rigidity required for the form--representation
dictionary.

## 18. Conclusion: one form across all places

A cusp form begins as a function on a noncompact arithmetic quotient. Its vanishing constant term removes the only parabolic asymptotic, produces rapid decay, and places it in a discrete Hilbert spectrum. Irreducibility then separates the global symmetry into local components, spherical almost everywhere and anchored by unique newvectors at the remaining finite places.

The Whittaker coefficient is the central organizing device. Fourier inversion reconstructs the cusp form from that one coefficient; local uniqueness factors it into place-by-place functions; its unramified values reproduce the Satake polynomial; and its global uniqueness proves multiplicity one. Rankin--Selberg continuation then turns agreement of almost all local data into global isomorphism.

Level, weight, and nebentype consequently cease to be unrelated decorations. Level is the product of local conductor exponents. Weight is the archimedean representation and its lowest compact type. Nebentype is the global central character, constrained at infinity by parity. Hecke eigenvalues are symmetric functions of unramified local parameters, with the powers of $q_v$ determined by the choice between unitary, algebraic, and raw-convolution normalizations. Oldforms are higher-level fixed vectors inside the same representation, while the newform is the tensor of minimal local lines.

This synthesis is the durable global language of $\mathrm{GL}_2$. It retains enough analysis to explain why cusp forms are discrete, enough harmonic analysis to prove factorization and multiplicity one, and enough arithmetic normalization to recover classical and Hilbert modular forms without ambiguity. Every later comparison can now be tested against one coherent set of invariants: local component, central character, Whittaker model, Hecke polynomial, conductor, newvector, contragredient, and twist.
