# Hecke Characters and Automorphic Induction from $\mathrm{GL}_1$

## Contents

1. [The induction problem](#1-the-induction-problem)
   - [Why characters should produce rank two objects](#11-why-characters-should-produce-rank-two-objects)
   - [Standing notation and normalizations](#12-standing-notation-and-normalizations)
   - [The three compatibilities to be proved](#13-the-three-compatibilities-to-be-proved)
   - [Boundaries of the theory](#14-boundaries-of-the-theory)
2. [Hecke characters as global multiplicative data](#2-hecke-characters-as-global-multiplicative-data)
   - [Why the idele class group is the correct source](#21-why-the-idele-class-group-is-the-correct-source)
   - [Local components and finite conductors](#22-local-components-and-finite-conductors)
   - [The central modulus direction](#23-the-central-modulus-direction)
   - [Algebraic infinity types](#24-algebraic-infinity-types)
   - [Ideals, units, and a first obstruction](#25-ideals-units-and-a-first-obstruction)
3. [Reciprocity and one-dimensional Galois characters](#3-reciprocity-and-one-dimensional-galois-characters)
   - [Arithmetic reciprocity without inversions](#31-arithmetic-reciprocity-without-inversions)
   - [Algebraic characters and $\ell$-adic avatars](#32-algebraic-characters-and-ell-adic-avatars)
   - [Norm pullback, restriction, and conjugation](#33-norm-pullback-restriction-and-conjugation)
   - [Restriction of a character to $C_F$](#34-restriction-of-a-character-to-c_f)
4. [Quadratic induction on the Galois side](#4-quadratic-induction-on-the-galois-side)
   - [The induced representation in a fixed basis](#41-the-induced-representation-in-a-fixed-basis)
   - [Irreducibility and the dihedral pattern](#42-irreducibility-and-the-dihedral-pattern)
   - [The determinant and the missing sign](#43-the-determinant-and-the-missing-sign)
   - [When the character descends](#44-when-the-character-descends)
   - [A useful counterexample](#45-a-useful-counterexample)
5. [Local automorphic induction](#5-local-automorphic-induction)
   - [The local problem as an étale quadratic algebra](#51-the-local-problem-as-an-étale-quadratic-algebra)
   - [Split places](#52-split-places)
   - [Inert and ramified field places](#53-inert-and-ramified-field-places)
   - [Why special representations do not occur](#54-why-special-representations-do-not-occur)
   - [Archimedean places](#55-archimedean-places)
6. [Local invariants and exceptional behavior](#6-local-invariants-and-exceptional-behavior)
   - [Central characters and twists](#61-central-characters-and-twists)
   - [Exact conductor formulas](#62-exact-conductor-formulas)
   - [Local $L$- and epsilon factors](#63-local-l--and-epsilon-factors)
   - [Unramified local polynomials](#64-unramified-local-polynomials)
7. [An explicit global construction](#7-an-explicit-global-construction)
   - [Why a restricted tensor product is insufficient](#71-why-a-restricted-tensor-product-is-insufficient)
   - [Schwartz data and local Whittaker functions](#72-schwartz-data-and-local-whittaker-functions)
   - [The global Whittaker series](#73-the-global-whittaker-series)
   - [Factorization and irreducibility](#74-factorization-and-irreducibility)
8. [Cuspidality and descent through the norm](#8-cuspidality-and-descent-through-the-norm)
   - [The constant term detects conjugation](#81-the-constant-term-detects-conjugation)
   - [The descended case and isobaric decomposition](#82-the-descended-case-and-isobaric-decomposition)
   - [Cuspidality is global, supercuspidality is local](#83-cuspidality-is-global-supercuspidality-is-local)
   - [Uniqueness from local data](#84-uniqueness-from-local-data)
9. [Local--global compatibility](#9-local--global-compatibility)
   - [One global character, several local algebras](#91-one-global-character-several-local-algebras)
   - [Compatibility theorem at every place](#92-compatibility-theorem-at-every-place)
   - [Determinants, centers, and conductors match](#93-determinants-centers-and-conductors-match)
   - [A counterexample to good-place complacency](#94-a-counterexample-to-good-place-complacency)
10. [Good primes and Frobenius polynomials](#10-good-primes-and-frobenius-polynomials)
    - [The split-prime calculation](#101-the-split-prime-calculation)
    - [The inert-prime calculation](#102-the-inert-prime-calculation)
    - [Ramified primes and what the polynomial omits](#103-ramified-primes-and-what-the-polynomial-omits)
    - [Ideal-theoretic coefficients](#104-ideal-theoretic-coefficients)
11. [Infinity types and cohomological weights](#11-infinity-types-and-cohomological-weights)
    - [Why infinity type becomes weight](#111-why-infinity-type-becomes-weight)
    - [Purity and the common central weight](#112-purity-and-the-common-central-weight)
    - [Parity from the center](#113-parity-from-the-center)
    - [Regular and nonregular infinity types](#114-regular-and-nonregular-infinity-types)
    - [Fields with split real places or complex base places](#115-fields-with-split-real-places-or-complex-base-places)
12. [Theta series over $\mathbf Q$ and CM forms](#12-theta-series-over-mathbf-q-and-cm-forms)
    - [Finite-order characters and weight one](#121-finite-order-characters-and-weight-one)
    - [Why the invariant case is not a cusp form](#122-why-the-invariant-case-is-not-a-cusp-form)
    - [Algebraic characters and holomorphic CM forms](#123-algebraic-characters-and-holomorphic-cm-forms)
    - [A concrete splitting example](#124-a-concrete-splitting-example)
    - [Hilbert theta series](#125-hilbert-theta-series)
13. [Coefficient fields, lattices, and reduction](#13-coefficient-fields-lattices-and-reduction)
    - [The field generated by a character](#131-the-field-generated-by-a-character)
    - [Integrality of good Hecke data](#132-integrality-of-good-hecke-data)
    - [Stable lattices in the induced representation](#133-stable-lattices-in-the-induced-representation)
    - [Residual dihedral representations](#134-residual-dihedral-representations)
    - [A practical residual irreducibility test](#135-a-practical-residual-irreducibility-test)
14. [Twists, conjugation, and controlled ramification](#14-twists-conjugation-and-controlled-ramification)
    - [Global twists](#141-global-twists)
    - [Conjugating coefficients and conjugating the field](#142-conjugating-coefficients-and-conjugating-the-field)
    - [Preserving prescribed local ramification after reduction](#143-preserving-prescribed-local-ramification-after-reduction)
    - [Building a character with chosen local behavior](#144-building-a-character-with-chosen-local-behavior)
    - [Minimality under norm twists](#145-minimality-under-norm-twists)
15. [Cyclic induction in general degree](#15-cyclic-induction-in-general-degree)
    - [The pattern behind the quadratic case](#151-the-pattern-behind-the-quadratic-case)
    - [The local construction for cyclic étale algebras](#152-the-local-construction-for-cyclic-étale-algebras)
    - [The global cyclic induction theorem](#153-the-global-cyclic-induction-theorem)
    - [Stabilizers and intermediate fields](#154-stabilizers-and-intermediate-fields)
    - [Central characters and the permutation determinant](#155-central-characters-and-the-permutation-determinant)
    - [What has and has not been used](#156-what-has-and-has-not-been-used)
16. [Examples and the final dictionary](#16-examples-and-the-final-dictionary)
    - [A finite dihedral example](#161-a-finite-dihedral-example)
    - [A norm-descended counterexample](#162-a-norm-descended-counterexample)
    - [Reading a splitting prime in both languages](#163-reading-a-splitting-prime-in-both-languages)
    - [The complete quadratic dictionary](#164-the-complete-quadratic-dictionary)
    - [Conclusion: rank two without losing rank-one control](#165-conclusion-rank-two-without-losing-rank-one-control)

## 1. The induction problem

### 1.1 Why characters should produce rank two objects

Class field theory makes one-dimensional arithmetic unusually explicit. A continuous character of an idele class group can be read locally on uniformizers and units, globally on ideals, and Galois-theoretically on Frobenius and inertia. Rank-two automorphic and Galois objects are usually much less accessible. A quadratic extension provides the simplest mechanism for turning the former into the latter without discarding the explicit information.

Let $M/F$ be quadratic, with nontrivial automorphism $\sigma$. A character of $M$ has two conjugates, $\psi$ and $\psi^\sigma$. From the Galois viewpoint one induces a character of $G_M$ to a two-dimensional representation of $G_F$. From the automorphic viewpoint one seeks a representation of $\mathrm{GL}_2(\mathbf A_F)$ whose local parameters are the corresponding local inductions. The central purpose of this book is to construct that automorphic representation, rather than merely predict it, and to prove that the two constructions have the same local data.

The construction is called **automorphic induction from $\mathrm{GL}_1$**. In the quadratic case we write

$$
\operatorname{AI}_{M/F}(\psi).
$$

It is a particularly transparent instance of functoriality. Splitting of primes controls Hecke coefficients, the discriminant supplies part of the level, conjugation controls cuspidality, and the infinity type controls weight. Each phenomenon can be seen directly.

### 1.2 Standing notation and normalizations

Throughout, $F$ is a number field, $M/F$ is a quadratic extension unless another degree is explicitly stated, and

$$
C_K=K^\times\backslash\mathbf A_K^\times
$$

for any number field $K$. The norm $N=N_{M/F}$ is used for fields, local multiplicative groups, ideles, and ideals; its source makes the meaning clear. The quadratic Hecke character attached to $M/F$ is denoted

$$
\eta=\eta_{M/F}:C_F\longrightarrow\{\pm1\}.
$$

Its kernel is $N(C_M)$.

Reciprocity is normalized arithmetically. Thus a uniformizer at an unramified finite place maps to **arithmetic Frobenius**, acting on the residue field by $x\mapsto x^{q_v}$. A Hecke character unramified at $v$ and its Galois avatar therefore have the same value on a uniformizer and on arithmetic Frobenius. No hidden inversion will occur later.

At a finite place $v$ of $F$, write $q_v$ for the residue cardinality, $\nu_v=|\cdot|_v$, and $U_v^r=1+\mathfrak p_v^r$ for $r\geq1$, with $U_v^0=\mathcal O_v^\times$. Normalized parabolic induction on $\mathrm{GL}_2(F_v)$ is denoted

$$
I(\chi_1,\chi_2)
=\operatorname{Ind}_{B(F_v)}^{\mathrm{GL}_2(F_v)}
(\chi_1\boxtimes\chi_2),
$$

where the covariance includes the square root of the Borel modulus. With this normalization, the local parameter of an irreducible principal series is $\chi_1\oplus\chi_2$.

For Galois induction we use the right-translation model. If $H\subset G$ and $\chi$ is a character of $H$, then

$$
\operatorname{Ind}_H^G\chi
=\{f:G\to E:f(hg)=\chi(h)f(g)\},
\qquad (g_0f)(g)=f(gg_0).
$$

For an index-two normal subgroup, the resulting isomorphism class is independent of the coset representative. Fixing the model now prevents the determinant sign from becoming a matter of guesswork later.

### 1.3 The three compatibilities to be proved

The phrase “induce the character” hides three logically different assertions.

First is **local existence**: for every place $v$, the characters at the places $w\mid v$ must determine an irreducible admissible representation $\pi_v$ of $\mathrm{GL}_2(F_v)$. Split, inert, ramified, real, and complex places behave differently.

Second is **global automorphy**: the restricted tensor product $\bigotimes_v'\pi_v$ must actually occur in automorphic forms. A list of plausible local factors does not prove this. We will build global Whittaker series from Schwartz data and use Poisson summation to establish automorphy.

Third is **arithmetic compatibility**: after converting an algebraic Hecke character to an $\ell$-adic Galois character, induction must commute with the local dictionaries. This includes characteristic polynomials, central characters, conductors, twists, and archimedean weights.

The order of the book follows these tasks. We first make the character and Galois sides exact, then solve the local representation problem, then globalize explicitly, and only afterward extract arithmetic consequences.

### 1.4 Boundaries of the theory

This book uses induction from characters. It does not develop restriction of a general $\mathrm{GL}_2$ parameter to an extension field, nor a descent theorem for arbitrary automorphic representations. Those are different transfer problems. Likewise, reductions of the induced representations will be studied one prime at a time; organizing them into compatible systems belongs to a later theory.

The restriction is productive. Character induction already produces dihedral representations, weight-one theta series, CM forms of every regular algebraic weight, and many residual representations with precisely controlled image and ramification. It is the smallest setting in which local and global functoriality can be proved down to explicit coefficients.

## 2. Hecke characters as global multiplicative data

### 2.1 Why the idele class group is the correct source

An ideal character sees finite primes but loses archimedean size and signs. A collection of local characters sees too much: its values on a diagonal element of $M^\times$ need not cancel. The idele class group imposes exactly the missing global relation.

A **Hecke quasicharacter** of $M$ is a continuous homomorphism

$$
\psi:C_M=M^\times\backslash\mathbf A_M^\times
\longrightarrow\mathbf C^\times.
$$

We generally say **Hecke character**, allowing nonunitary values. It factors as a restricted product $\psi=\prod_w\psi_w$, where $\psi_w:M_w^\times\to\mathbf C^\times$ and $\psi_w$ is unramified for almost every finite $w$. The factorization is characterized by evaluating $\psi$ on an idele supported at one place. Its product is trivial on $M^\times$.

Continuity is essential. It forces finite conductor at every finite place and makes the archimedean character differentiable in the real directions. An arbitrary homomorphism of the underlying abstract group need have neither property and cannot define automorphic data of finite level.

### 2.2 Local components and finite conductors

At a finite place $w$, define

$$
a_w(\psi)=\min\{r\geq0:\psi_w|_{U_w^r}=1\}.
$$

Thus $a_w(\psi)=0$ exactly when $\psi_w$ is unramified. The finite conductor is

$$
\mathfrak f(\psi)=\prod_{w<\infty}\mathfrak p_w^{a_w(\psi)}.
$$

Only finitely many exponents are nonzero. At an unramified place the number

$$
\alpha_w=\psi_w(\varpi_w)
$$

is independent of the choice of uniformizer, since two uniformizers differ by a unit. These numbers form the Euler data of the character.

Conductor behaves well under unequal depths but can cancel at equal depths. If $a_w(\psi_w)>a_w(\phi_w)$, then

$$
a_w(\psi_w\phi_w)=a_w(\psi_w),
$$

whereas $\phi_w=\psi_w^{-1}$ makes the product unramified. This elementary counterexample will matter when twists are used to minimize a dihedral level.

The character has an Euler product

$$
L(s,\psi)=
\prod_{w\nmid\mathfrak f(\psi)}
\left(1-\psi_w(\varpi_w)q_w^{-s}\right)^{-1},
$$

initially in a right half-plane after removing its real modulus exponent. Archimedean gamma factors and conductor powers complete it to $\Lambda(s,\psi)$. Fourier analysis on $\mathbf A_M$ gives a functional equation relating $\Lambda(s,\psi)$ to $\Lambda(1-s,\psi^{-1})$, with an epsilon factor built from the local Gauss sums. This analytic package will not be reconstructed later on $\mathrm{GL}_2$: induction preserves it place by place.

At a ramified place, the Euler factor convention uses inertia invariants. A ramified one-dimensional character has no inertia invariants, so its factor is $1$, although its epsilon factor and conductor are nontrivial. Thus “missing Euler factor” does not mean “no local information.”

### 2.3 The central modulus direction

The idele module gives characters $|\cdot|_{\mathbf A_M}^s$. Since the norm-one idele class group is compact, the absolute value of any Hecke character is trivial on it. Consequently every Hecke character has a unique decomposition

$$
\psi=\psi^{\mathrm u}|\cdot|_{\mathbf A_M}^{t},
\qquad t\in\mathbf R,
$$

with $\psi^{\mathrm u}$ unitary. Complex oscillation $|\cdot|^{iu}$ belongs to the unitary factor. We call $t$ the **central modulus exponent**.

Conjugation preserves the idele module, so $\psi$ and $\psi^\sigma$ have the same exponent $t$. Their ratio is therefore unitary. This small observation rules out misleading reducibility phenomena in local principal series: conjugate inducing characters cannot differ by the nonunitary character $|\cdot|^{\pm1}$.

A Hecke character has finite order precisely when it is unitary, trivial on the connected component of $C_M$, and has finite image on the resulting profinite quotient. Unitary does not imply finite order: $|\cdot|^{iu}$ is the simplest counterexample.

### 2.4 Algebraic infinity types

At infinity, continuity alone permits arbitrary complex exponents. Arithmetic applications require integrality. For every embedding $\tau:M\hookrightarrow\mathbf C$, choose an integer $n_\tau$. We call $\psi$ **algebraic** if, on a sufficiently small connected subgroup at infinity,

$$
\psi_\infty(x)=\prod_{\tau:M\hookrightarrow\mathbf C}\tau(x)^{-n_\tau}.
$$

At a complex place represented by a pair $\{\tau,\bar\tau\}$, this reads $z^{-n_\tau}\bar z^{-n_{\bar\tau}}$. At a real place it is $x^{-n_\tau}$ on $\mathbf R_{>0}$, with an independent sign character on $\mathbf R^\times$. The sign is finite order and is not encoded by the differential exponent.

The minus sign matches the ideal convention: if $\mathfrak a=(a)$ with $a\equiv1$ modulo the finite conductor, the associated ideal character satisfies

$$
\psi(\mathfrak a)=\prod_\tau\tau(a)^{n_\tau}.
$$

Algebraic does not mean pure. Purity of weight $w$ adds

$$
n_\tau+n_{\bar\tau}=w
$$

for every complex pair, and the corresponding real condition. We will impose it only when discussing cohomological and arithmetic weights.

### 2.5 Ideals, units, and a first obstruction

Away from $\mathfrak f(\psi)$, an algebraic Hecke character can be described by a multiplicative function on fractional ideals. But not every formula on principal ideals extends. If one prescribes infinity type $(p,q)$ over an imaginary quadratic field, then every unit $u\equiv1\pmod{\mathfrak f}$ must satisfy

$$
u^p\bar u^q=1.
$$

This is the unit compatibility condition. Enlarging the conductor removes the obstruction because the unit group is finite. In a field with positive unit rank the relation is more restrictive and expresses the global compatibility among infinity types.

This example explains why infinity type and finite conductor cannot be chosen entirely independently. The adelic definition packages their compatibility automatically; the ideal description is convenient only after the unit condition has been checked.

## 3. Reciprocity and one-dimensional Galois characters

### 3.1 Arithmetic reciprocity without inversions

Global class field theory gives a continuous homomorphism with dense image

$$
\operatorname{Art}_M:C_M\longrightarrow G_M^{\mathrm{ab}}.
$$

At a finite unramified place $w$, the class of a uniformizer maps to arithmetic Frobenius. Hence a finite-order Hecke character $\psi$ gives the finite-image Galois character

$$
\chi_\psi:G_M\longrightarrow\mathbf C^\times,
\qquad
\chi_\psi(\operatorname{Art}_M(x))=\psi(x).
$$

In particular,

$$
\chi_\psi(\operatorname{Frob}_w)=\psi_w(\varpi_w).
$$

If reciprocity were normalized geometrically, the right side would be inverted. All Frobenius polynomials in this book use the displayed arithmetic convention.

The conductor exponent of $\chi_\psi|_{G_{M_w}}$ equals $a_w(\psi)$. Units correspond to inertia and higher units to the corresponding abelian ramification filtration. Thus the ideal conductor of a finite-order Hecke character is literally its global Artin conductor.

### 3.2 Algebraic characters and $\ell$-adic avatars

A non-finite algebraic character does not factor continuously through the profinite Galois group with its complex topology. To obtain a Galois character, choose an embedding

$$
\iota_\ell:\overline{\mathbf Q}\hookrightarrow\overline{\mathbf Q}_\ell
$$

and suppose the finite ideal values of $\psi$ are algebraic. Transport those values through $\iota_\ell$ and correct at places above $\ell$ by the algebraic infinity type. The result is a continuous character

$$
\chi_{\psi,\ell}:G_M\longrightarrow\overline{\mathbf Q}_\ell^\times
$$

unramified outside $\ell\mathfrak f(\psi)$ and locally algebraic above $\ell$.

The correction is forced by principal ideles. Transporting the finite components alone would not be trivial on $M^\times$; the factors $\tau(a)^{n_\tau}$, viewed $\ell$-adically through the embeddings selected by $\iota_\ell$, cancel precisely that defect. Away from $\ell\mathfrak f(\psi)$ one still has the clean formula

$$
\chi_{\psi,\ell}(\operatorname{Frob}_w)
=\iota_\ell(\psi(\mathfrak p_w)).
$$

The avatar depends on $\iota_\ell$. The algebraic ideal values and infinity type are the invariant data; an $\ell$-adic realization is one incarnation of them.

### 3.3 Norm pullback, restriction, and conjugation

Functoriality is easiest to remember by testing Frobenius. If $\mu$ is a Hecke character of $F$, then

$$
\mu_M=\mu\circ N_{M/F}
$$

corresponds to restriction of its Galois character:

$$
\chi_{\mu_M}=\chi_\mu|_{G_M}.
$$

For a place $w\mid v$, its local component is $\mu_v\circ N_{M_w/F_v}$. The direction is important: field extension gives Galois restriction but multiplicative norm pullback.

Conjugation is defined by

$$
\psi^\sigma(x)=\psi(\sigma x).
$$

On Galois characters, after choosing a lift $s\in G_F$ of $\sigma$,

$$
\chi_\psi^\sigma(h)=\chi_\psi(shs^{-1}).
$$

Changing $s$ multiplies it by an inner conjugation from $G_M$, invisible because $\chi_\psi$ is one dimensional. Thus $\psi=\psi^\sigma$ is an intrinsic condition.

### 3.4 Restriction of a character to $C_F$

The diagonal embedding $\mathbf A_F^\times\hookrightarrow\mathbf A_M^\times$ gives a Hecke character $\psi|_{C_F}$. On the Galois side this is not ordinary restriction, since $G_F$ is larger than $G_M$. It corresponds to composing $\chi_\psi$ with the transfer homomorphism

$$
\operatorname{Ver}:G_F^{\mathrm{ab}}\longrightarrow G_M^{\mathrm{ab}}.
$$

This distinction is exactly what appears in the determinant of an induced representation. Confusing norm pullback with diagonal restriction would omit the quadratic factor and reverse the functorial direction.

## 4. Quadratic induction on the Galois side

### 4.1 The induced representation in a fixed basis

Let $G=G_F$, $H=G_M$, and let $\chi:H\to E^\times$ be a continuous character over a characteristic-zero field $E$. Choose $s\in G\setminus H$. Since $H$ is normal of index two, $s^2\in H$. In the right-translation induction model, choose basis vectors supported on $H$ and $Hs$. A direct calculation gives, up to exchanging the two basis vectors,

$$
\rho(h)=
\begin{pmatrix}
\chi(h)&0\\
0&\chi^\sigma(h)
\end{pmatrix}
\quad(h\in H),
\qquad
\rho(s)=
\begin{pmatrix}
0&\chi(s^2)\\
1&0
\end{pmatrix}.
$$

Here $\rho=\operatorname{Ind}_{G_M}^{G_F}\chi$. Changing $s$ or the basis conjugates these matrices. The formulas make three structural facts visible: restriction to $G_M$ splits as $\chi\oplus\chi^\sigma$; an element outside $G_M$ exchanges the two lines; and its square acts through $\chi(s^2)$.

### 4.2 Irreducibility and the dihedral pattern

**Theorem 4.1 (quadratic irreducibility criterion).** The representation $\rho$ is irreducible if and only if $\chi\ne\chi^\sigma$.

**Proof strategy.** Any invariant line remains invariant under $H$, so the diagonal restriction nearly determines it. If the two $H$-characters differ, its only eigenlines are the coordinate lines, and $s$ exchanges them. If they agree, the matrix of $s$ can be diagonalized in characteristic zero.

**Proof.** Suppose $\chi\ne\chi^\sigma$. Choose $h\in H$ on which their values differ. Then every $H$-stable line is one of the two coordinate lines. Neither is $G$-stable because $\rho(s)$ exchanges them. Hence $\rho$ is irreducible.

Conversely, if $\chi=\chi^\sigma$, then $H$ acts by scalars. Choose a square root of $\chi(s^2)$ in an algebraic closure of $E$; the two eigenspaces of $\rho(s)$ are $G$-stable. Thus $\rho$ is reducible after scalar extension, and over a sufficiently large coefficient field it is a sum of two characters. $\square$

Projectively, the image of $H$ is represented by

$$
h\longmapsto
\begin{bmatrix}
\chi(h)/\chi^\sigma(h)&0\\0&1
\end{bmatrix},
$$

while $s$ acts by inversion on this diagonal subgroup. If $\chi/\chi^\sigma$ has finite order $m>2$, the projective image is the dihedral group of order $2m$. For finite-order $\chi$ this always gives a finite generalized dihedral image, with the familiar small degeneracies when $m\leq2$. For an algebraic $\ell$-adic character of infinite projective order, “dihedral” describes the normalizer-of-a-torus structure, not a finite group.

The character of the induction makes the same pattern visible:

$$
\operatorname{tr}\rho(g)=
\begin{cases}
\chi(g)+\chi^\sigma(g),&g\in G_M,\\
0,&g\notin G_M.
\end{cases}
$$

When the projective image is genuinely dihedral, $G_M$ is the subgroup preserving each of the two eigenlines. The trace formula also proves that two irreducible inductions $\operatorname{Ind}\chi$ and $\operatorname{Ind}\chi'$ are isomorphic precisely when $\chi'=\chi$ or $\chi^\sigma$.

### 4.3 The determinant and the missing sign

Taking determinants in the matrices above gives

$$
\det\rho(h)=\chi(h)\chi^\sigma(h),
\qquad
\det\rho(s)=-\chi(s^2).
$$

Let $\eta_{M/F}:G_F\to\{\pm1\}$ be the quadratic character, trivial on $G_M$ and equal to $-1$ outside it. The transfer sends $h\in H$ to $h\,shs^{-1}$ and sends $s$ to $s^2$. Therefore

$$
\boxed{\det(\operatorname{Ind}_{G_M}^{G_F}\chi)
=\eta_{M/F}\,(\chi\circ\operatorname{Ver}).}
$$

The factor $\eta_{M/F}$ is the determinant of the permutation representation on $G_F/G_M$. It cannot be dropped: for the trivial character, induction is $1\oplus\eta$, whose determinant is $\eta$, not $1$.

By reciprocity, if $\chi$ comes from $\psi$, the Hecke character corresponding to the determinant is

$$
\eta_{M/F}\,\psi|_{C_F}.
$$

This will be the central character of automorphic induction.

### 4.4 When the character descends

If $\chi=\chi^\sigma$, it extends to $G_F$. Indeed, choose a square root of $\chi(s^2)$ and prescribe that value to $s$; the conjugation relation is exactly the invariance hypothesis. There are two extensions, say $\widetilde\chi$ and $\widetilde\chi\eta$, and

$$
\operatorname{Ind}_{G_M}^{G_F}\chi
\cong\widetilde\chi\oplus\widetilde\chi\eta.
$$

On the Hecke side, the corresponding statement is that an invariant character has the form

$$
\psi=\mu\circ N_{M/F}
$$

for a Hecke character $\mu$ of $F$, determined up to multiplication by $\eta$. The two assertions are equivalent by class field theory. This is the precise meaning of “descent through the norm.” Invariance alone should not be confused with diagonal restriction from $C_M$ to $C_F$.

### 4.5 A useful counterexample

Take $\chi=1$. It is tempting to call induction from a quadratic field automatically irreducible because the field extension is nontrivial. But

$$
\operatorname{Ind}_{G_M}^{G_F}1=1\oplus\eta_{M/F}.
$$

The extension supplies the permutation action; it does not supply distinct eigencharacters on the subgroup. This counterexample foreshadows the automorphic cuspidality criterion: the inducing character, not merely the inducing field, must have a full conjugacy orbit.

## 5. Local automorphic induction

### 5.1 The local problem as an étale quadratic algebra

Fix a place $v$ of $F$. The algebra

$$
M_v=M\otimes_FF_v=\prod_{w\mid v}M_w
$$

is a quadratic étale $F_v$-algebra. It is either $F_v\times F_v$ or a quadratic field. The local component of $\psi$ is a character

$$
\psi_v^M=\prod_{w\mid v}\psi_w:M_v^\times\longrightarrow\mathbf C^\times.
$$

Local automorphic induction must turn this character into an irreducible admissible representation of $\mathrm{GL}_2(F_v)$. The correct rule is dictated by the two-dimensional Weil parameter

$$
\Phi_v=\operatorname{Ind}_{W_{M_v}}^{W_{F_v}}\psi_v^M.
$$

For the split algebra this notation means the direct sum of the two characters. Local class field theory is again arithmetically normalized. We now describe the corresponding representation without treating the parameter as an unexplained label.

### 5.2 Split places

Suppose $v=ww^\sigma$ splits. Identifying

$$
M_v^\times=F_v^\times\times F_v^\times,
$$

write $\psi_v^M=\psi_w\boxtimes\psi_{w^\sigma}$. Then

$$
\operatorname{AI}_{M_v/F_v}(\psi_v^M)
=I(\psi_w,\psi_{w^\sigma}).
$$

The order of the two characters is immaterial up to the standard intertwiner. Since $\psi_w/\psi_{w^\sigma}$ is unitary after removing the common global modulus power, it cannot equal $\nu_v^{\pm1}$. Hence this normalized principal series is irreducible. In particular, equality $\psi_w=\psi_{w^\sigma}$ does **not** cause reducibility: $I(\chi,\chi)$ is irreducible because its ratio is $1$, not $\nu_v^{\pm1}$.

The center acts by

$$
z\longmapsto\psi_w(z)\psi_{w^\sigma}(z).
$$

At a split place $\eta_v=1$, so this is exactly $\eta_v\psi_v^M|_{F_v^\times}$.

For example, suppose both local characters are unramified with values $\alpha$ and $\beta$ on $\varpi_v$. The spherical Hecke roots are $\alpha,\beta$. If instead $\psi_w$ has conductor two and $\psi_{w^\sigma}$ is unramified, the principal series has conductor two, not four. Split places add two independent depths and have no discriminant correction.

### 5.3 Inert and ramified field places

Now let $E=M_w$ be a quadratic field over $K=F_v$, with nontrivial automorphism $\tau$. A character $\theta:E^\times\to\mathbf C^\times$ gives a character of $W_E$ by local reciprocity. If $\theta\ne\theta^\tau$, the induced Weil representation is irreducible. Its local automorphic induction is the unique supercuspidal representation whose parameter is that induction:

$$
\operatorname{AI}_{E/K}(\theta)=\pi(\theta).
$$

This representation can be constructed from the elliptic torus $E^\times\subset\mathrm{GL}_2(K)$, but the phrase “compactly induce $\theta$” suppresses real work. In depth zero, $E/K$ is unramified and the reduction of a suitably rectified torus character is a regular character of $k_E^\times$; the associated cuspidal representation of $\mathrm{GL}_2(k_K)$ is inflated and compactly induced from $K^\times\mathrm{GL}_2(\mathcal O_K)$. At positive depth the torus character must be extended, sometimes through a finite Heisenberg representation, across a compact subgroup supplied by an $E$-stable lattice chain. In wild residue characteristic the construction requires the corresponding simple-type machinery. Regularity of the Weil character is what makes the parameter irreducible, while a rectifying character reconciles a chosen torus parameterization with the local correspondence. We therefore define $\pi(\theta)$ by its Weil parameter; this avoids silently identifying the raw character in one compact-induction convention with the character in another.

The ramified case uses a period-two lattice chain rather than the hyperspecial lattice. This difference accounts for the discriminant term in the conductor. It does not change the basic dichotomy: regular character data give a supercuspidal representation.

The depth-zero case displays regularity concretely. If $E/K$ is unramified and $a_E(\theta)=1$, then $\theta|_{\mathcal O_E^\times}$ factors through $k_E^\times$. Conjugation becomes $x\mapsto x^{q_K}$, so regularity says

$$
\bar\theta^{q_K}\ne\bar\theta.
$$

The finite cuspidal representation attached to the corresponding rectified regular residue character has dimension $q_K-1$, and compact induction gives a supercuspidal of conductor two. If equality holds, $\bar\theta$ factors through $N_{k_E/k_K}$ and the construction belongs to a principal series instead.

If $\theta=\theta^\tau$, local class field theory gives

$$
\theta=\mu\circ N_{E/K}
$$

for a character $\mu$ of $K^\times$, unique up to $\eta_{E/K}$. Then

$$
\operatorname{AI}_{E/K}(\theta)
=I(\mu,\mu\eta_{E/K}).
$$

This principal series is irreducible because $\eta_{E/K}$ is unitary and not $\nu^{\pm1}$. Thus a nonsplit quadratic torus does not automatically produce a supercuspidal; regularity is decisive.

### 5.4 Why special representations do not occur

A special representation has a Weil--Deligne parameter with nonzero monodromy $N$. Induction of a character has $N=0$, both before and after induction. Consequently local automorphic induction from $\mathrm{GL}_1$ produces principal series or supercuspidals, but never a Steinberg twist.

There is a nearby degeneracy worth separating. For arbitrary characters $\chi_1,\chi_2$, the normalized principal series $I(\chi_1,\chi_2)$ reduces when $\chi_1/\chi_2=\nu^{\pm1}$; its constituents are a character and a special representation. The semisimple parameter $\chi_1\oplus\chi_2$ corresponds to the one-dimensional constituent at that boundary, whereas the special constituent requires $N\ne0$. Conjugate components of a global Hecke character have a common real modulus exponent, so this boundary never arises in the quadratic induction considered here.

### 5.5 Archimedean places

If $F_v=\mathbf C$, then $M_v=\mathbf C\times\mathbf C$ and the induction is a complex principal series. If $F_v=\mathbf R$ and $M_v=\mathbf R\times\mathbf R$, it is a real principal series from the two real characters.

The interesting case is $M_w=\mathbf C$ over $F_v=\mathbf R$. The algebraic infinity type is

$$
\theta_{\mathrm{alg}}(z)=z^{-p}\bar z^{-q},
$$

with $p,q\in\mathbf Z$. Reattaching the unique global modulus factor $|\cdot|_{\mathbf A_M}^t$ multiplies this local character by $|z|_{\mathbf C}^t=|z|^{2t}$ and does not change $p-q$. A continuous character of $\mathbf C^\times$ has angular part $(z/|z|)^m$ for an integer $m$; there is no additional nontrivial finite-order character because $\mathbf C^\times$ is connected. Conjugation exchanges $p$ and $q$. If $p\ne q$, induction from $W_\mathbf C$ to $W_\mathbf R$ is irreducible and corresponds, after the common modulus twist, to a discrete series of lowest weight

$$
k=|p-q|+1.
$$

If $p=q$, the character is conjugation invariant and factors through the norm $z\mapsto |z|^2$; induction splits into two real Weil characters. The local correspondence packages them as the irreducible real principal series $I(\mu,\mu\operatorname{sgn})$, with the common modulus twist understood. The parity of $k$ in the regular case and the sign of the central character are linked by the action of $-1$.

In particular, for $p=q=0$ one obtains the limit-type principal series that occurs at infinity for finite-image weight-one theta series. The direct sum belongs to the parameter side; it must not be confused with a direct sum of two representations of $\mathrm{GL}_2(\mathbf R)$.

This archimedean dichotomy is the analytic reflection of the same regularity condition seen at finite field places.

## 6. Local invariants and exceptional behavior

### 6.1 Central characters and twists

For every place $v$, split or nonsplit,

$$
\boxed{\omega_{\operatorname{AI}_{M_v/F_v}(\psi_v^M)}
=\eta_v\,\psi_v^M|_{F_v^\times}.}
$$

At a field place this follows from the determinant of induction; at a split place $\eta_v=1$ and it is the product of the two inducing characters. The formula is uniform because $\eta_v$ is the determinant of the local permutation representation.

If $\mu_v:F_v^\times\to\mathbf C^\times$, then

$$
\operatorname{AI}_{M_v/F_v}(\psi_v^M)
\otimes(\mu_v\circ\det)
\cong
\operatorname{AI}_{M_v/F_v}
(\psi_v^M(\mu_v\circ N_{M_v/F_v})).
$$

This is immediate on split principal series and on Weil induction follows by pulling a character through induction. It is the local prototype of global twist compatibility.

Contragredience is equally clean:

$$
\operatorname{AI}_{M_v/F_v}(\psi_v^M)^\vee
\cong\operatorname{AI}_{M_v/F_v}((\psi_v^M)^{-1}).
$$

### 6.2 Exact conductor formulas

At a split finite place $v=ww^\sigma$, the conductor exponent is

$$
a_v(\operatorname{AI}\psi)=a_w(\psi)+a_{w^\sigma}(\psi).
$$

At a quadratic field place $E/K$, let $d(E/K)$ be the exponent of the discriminant ideal of $E/K$ in $K$, and let $f(E/K)$ be the residue degree. Then the Artin conductor induction formula gives

$$
\boxed{a_K(\operatorname{AI}_{E/K}\theta)
=d(E/K)+f(E/K)a_E(\theta).}
$$

For an unramified quadratic extension, this is $2a_E(\theta)$. A regular tame character of conductor one therefore gives a depth-zero supercuspidal of conductor two. For a ramified quadratic extension, $f=1$, so the formula is $d(E/K)+a_E(\theta)$.

**Proof strategy.** Separate the contribution already present in the permutation representation from the ramification of the character. The first is the discriminant exponent. For the second, compare codimensions of inertia invariants on the induced space; each ramification layer over $E$ contributes with residue-degree multiplicity $f(E/K)$.

More formally, induction of the trivial character has conductor $d(E/K)$. Tensoring the induced permutation module along each ramification quotient and applying the conductor integral shows that the incremental character contribution is $f(E/K)a_E(\theta)$. This proves the formula. It remains valid in the invariant case, where the left side can also be checked as $a_K(\mu)+a_K(\mu\eta)$.

Three examples calibrate the formula.

First, if $E/K$ is unramified and $\theta$ is unramified, the induction is spherical and has conductor zero. Second, if $E/K$ is unramified and $a_E(\theta)=1$, then $a_K(\pi)=2$; this is the familiar depth-zero supercuspidal level. Third, if $E/K$ is tamely ramified quadratic with odd residue characteristic, then $d(E/K)=1$. An unramified regular character cannot occur, because every unramified character is conjugation invariant; the first regular characters have positive conductor, and the induced conductor begins at least at two.

The discriminant coefficient is $d(E/K)$, not $2d(E/K)$, and the character coefficient is the residue degree $f(E/K)$, not the ramification index. Both errors can be detected in the tame ramified example: there $f=1$ even though $[E:K]=2$.

Globally the finite conductor ideal is therefore

$$
\boxed{\mathfrak f(\operatorname{AI}_{M/F}\psi)
=\mathfrak d_{M/F}\,N_{M/F}(\mathfrak f(\psi)).}
$$

The norm of the conductor carries the local residue-degree factors. The formula uses the actual character, not a twist-minimal representative. Twisting may create cancellation, so one must recompute the right side after replacing $\psi$ by $\psi(\mu\circ N)$.

### 6.3 Local $L$- and epsilon factors

Choose a nontrivial additive character $\Psi_v:F_v\to\mathbf C^\times$, and put $\Psi_w=\Psi_v\circ\operatorname{Tr}_{M_w/F_v}$. Inductivity of local factors gives

$$
L(s,\operatorname{AI}_{M_v/F_v}\psi_v^M)
=\prod_{w\mid v}L(s,\psi_w).
$$

At a field place the product has one factor, but its residue degree is built into that Euler factor. For epsilon factors,

$$
\epsilon(s,\operatorname{AI}_{E/K}\theta,\Psi_K)
=\lambda(E/K,\Psi_K)\,
\epsilon(s,\theta,\Psi_K\circ\operatorname{Tr}_{E/K}),
$$

where $\lambda(E/K,\Psi_K)$ is the epsilon factor of the induced trivial character divided by that of the trivial character over $E$. At a split place the lambda factor is one and the epsilon factor is the product of the two character factors. Keeping the additive character in the notation is necessary: changing it alters epsilon factors, though not conductors or $L$-factors.

Multiplying over all places makes the global lambda factors and additive-character changes obey the product formula. Thus

$$
L(s,\operatorname{AI}_{M/F}\psi)=L(s,\psi)
$$

in compatible automorphic normalization, including completed archimedean factors.

### 6.4 Unramified local polynomials

If $v$ is unramified in $M$ and $\psi$ is unramified above $v$, define the local polynomial

$$
P_v(X)=\det(1-\Phi_v(\operatorname{Frob}_v)X).
$$

If $v=ww^\sigma$ splits, then

$$
P_v(X)=
(1-\psi_w(\varpi_v)X)(1-\psi_{w^\sigma}(\varpi_v)X).
$$

If $v$ is inert with unique $w$, arithmetic Frobenius exchanges the two induced lines and

$$
\boxed{P_v(X)=1-\psi_w(\varpi_w)X^2.}
$$

Thus the trace is zero and the determinant is $-\psi_w(\varpi_w)$. The minus sign agrees with $\eta_v(\varpi_v)=-1$. These formulas will become explicit Hecke eigenvalues after globalization.

## 7. An explicit global construction

### 7.1 Why a restricted tensor product is insufficient

The local work supplies an irreducible admissible representation $\pi_v$ at every place and a spherical vector at almost all finite places. Hence one can form

$$
\pi^{\mathrm{loc}}=\bigotimes_v'\pi_v.
$$

Nothing in this formal tensor product says that it occurs in functions on

$$
\mathrm{GL}_2(F)\backslash\mathrm{GL}_2(\mathbf A_F).
$$

Automorphy imposes invariance under rational matrices, and cuspidality imposes a global vanishing integral. We now construct actual forms whose local Whittaker spaces realize the tensor product.

### 7.2 Schwartz data and local Whittaker functions

Fix a nontrivial additive character

$$
\Psi:F\backslash\mathbf A_F\longrightarrow\mathbf C^\times
$$

and use $\Psi_M=\Psi\circ\operatorname{Tr}_{M/F}$. Let $\mathcal S(\mathbf A_M)$ be the Schwartz--Bruhat space. For a factorable $\varphi=\otimes_v\varphi_v$ and a Hecke character $\psi$, a local Mellin projection followed by Fourier transform on the two-dimensional $F_v$-space $M_v$ produces a function

$$
W_{\varphi_v,\psi_v}(g_v)
$$

in the $\Psi_v$-Whittaker model of $\operatorname{AI}_{M_v/F_v}(\psi_v^M)$. An invariant description uses the quadratic $F_v$-space $(M_v,N_{M_v/F_v})$. Its Weil action makes $n(b)$ multiply a Schwartz function by $\Psi_v(bN(x))$, makes the diagonal torus rescale $x$, and makes the Weyl element act by Fourier transform. Mellin projection under the torus extracts the $\psi_v$-isotypic part. This defines $W_{\varphi_v,\psi_v}$ without choosing square roots of elements or representatives of norm fibers.

At almost every finite $v$, take $\varphi_v=1_{\mathcal O_{M_v}}$. The resulting $W_v$ is spherical and normalized by $W_v(1)=1$. The local zeta integral unfolds to

$$
\int_{F_v^\times}W_v
\left(\begin{pmatrix}a&0\\0&1\end{pmatrix}\right)
|a|_v^{s-1/2}\,d^\times a
=L(s,\psi_v^M).
$$

This calculation identifies the local representation rather than merely naming it.

There is an equivalent theta-kernel picture that makes the geometry visible. Regard $M$ as a two-dimensional quadratic space over $F$ with quadratic form $N_{M/F}$. Multiplication by $t\in M^\times$ is a similitude of ratio $N(t)$. On the matching-similitude group

$$
R(\mathbf A_F)=
\{(g,t)\in\mathrm{GL}_2(\mathbf A_F)\times
\mathbf A_M^\times:\det g=N(t)\},
$$

the Weil action is defined, and

$$
\theta(g,t;\varphi)=\sum_{x\in M}\omega(g,t)\varphi(x)
$$

is invariant under $R(F)$. Mellin projection of the $t$-variable against $\psi$ gives the same functions as the Whittaker construction. The norm-one torus quotient occurring in this projection is compact because $M$ is a field. This gives convergence and explains why the quadratic norm, rather than an arbitrary binary form, carries the inducing character.

### 7.3 The global Whittaker series

Put $W_\varphi=\prod_vW_{\varphi_v,\psi_v}$. Define

$$
\Theta_{\varphi,\psi}(g)
=\sum_{a\in F^\times}
W_\varphi\left(
\begin{pmatrix}a&0\\0&1\end{pmatrix}g
\right).
$$

This is the nonconstant part of the theta lift. It is already the whole form when $\psi\ne\psi^\sigma$; when $\psi=\psi^\sigma$, two boundary terms must be added. Keeping this distinction visible prevents a serious false argument: a Whittaker series indexed only by $F^\times$ has zero unipotent constant term, so it cannot by itself realize the noncuspidal induction.

For unitary $\psi$, rapid decay at infinity and compact support in the nonarchimedean Kirillov variables give absolute convergence on compact sets. If $\psi=\psi^{\mathrm u}|\cdot|_{\mathbf A_M}^t$, construct the unitary induction first and twist it by $|\det|_{\mathbf A_F}^t$; the identity $|N_{M/F}x|_{\mathbf A_F}=|x|_{\mathbf A_M}$ gives the desired general character. No separate analytic continuation is needed in the regular case. The series is visibly left invariant under $N(F)$ because $\Psi$ is trivial on $F$. Diagonal rational invariance follows by reindexing $a$ and using the central character.

The nontrivial step is invariance under the Weyl element

$$
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
$$

The local definition makes right translation by $w$ into Fourier transform on $M_v$. Global Poisson summation on the additive space $M$ says that the sum of $\varphi$ over $M$ equals the sum of its Fourier transform over $M$. After Mellin projection, the zero orbit contributes a boundary functional proportional to the average of $\psi/\psi^\sigma$ on the norm-one torus quotient. When $\psi\ne\psi^\sigma$, character orthogonality kills this functional, so Poisson summation gives the exact Weyl transformation of $\Theta_{\varphi,\psi}$. Since $N(F)$, the diagonal torus, and $w$ generate $\mathrm{GL}_2(F)$ through Bruhat decomposition, the regular series is automorphic.

When $\psi=\psi^\sigma$, the boundary functional does not vanish. Writing $\psi=\mu\circ N_{M/F}$, the two zero-orbit contributions transform through $\mu$ and $\mu\eta$. Adding them to the displayed nonconstant series gives the standard Eisenstein realization of the isobaric sum $\mu\boxplus\mu\eta$, initially in a convergence chamber and then at the desired parameter by the usual continuation of Eisenstein series. Thus Poisson summation proves a precise alternative: the Whittaker-only series is a cusp form in the regular case, while in the descended case its automorphic completion has the two required constant terms.

No rational invariance is hidden here. For $u\in F$, left translation by $n(u)$ multiplies the summand indexed by $a$ by $\Psi(ua)=1$. For $r\in F^\times$, left translation by $\operatorname{diag}(r,1)$ replaces $a$ by $ra$. Rational scalar matrices act through $\eta\psi|_{C_F}$, which is trivial on diagonal $F^\times$. Bruhat decomposition reduces every remaining rational matrix to the Weyl calculation.

Moderate growth follows from Schwartz estimates at infinity. Smoothness and finite level follow because $\varphi_f$ is locally constant and compactly supported. Differentiation at infinity preserves the Schwartz space, so the generated functions have the required finiteness under maximal compact and central actions. The series therefore satisfies the full automorphic conditions, not just rational invariance.

This is the decisive global argument. The same Fourier transform that gives the local functional equation supplies rational Weyl invariance globally; Poisson summation turns compatible local models into an automorphic form and records, rather than discards, the zero-orbit obstruction.

### 7.4 Factorization and irreducibility

Assume first that $\psi\ne\psi^\sigma$, and let $V(\psi)$ be the space generated by right translates of all $\Theta_{\varphi,\psi}$. Its nonzero Whittaker coefficient is $W_\varphi$, so the local representation generated at $v$ is exactly $\operatorname{AI}_{M_v/F_v}(\psi_v^M)$. The local theta calculation shows that varying one local Schwartz factor while keeping all others fixed spans the full local Whittaker model. Consequently

$$
V(\psi)\cong\bigotimes_v'
\operatorname{AI}_{M_v/F_v}(\psi_v^M).
$$

The boundary calculation shows that $V(\psi)$ lies in the cuspidal spectrum. Multiplicity one for generic cuspidal representations then makes it irreducible. In the invariant case, the completed series described above realizes the Eisenstein representation $\mu\boxplus\mu\eta$. Thus neither global representation is inferred from almost-everywhere Hecke data: the regular one is generated by explicit cusp forms, while the descended one is supplied by its explicit Eisenstein completion, and both are then identified locally.

## 8. Cuspidality and descent through the norm

### 8.1 The constant term detects conjugation

For an automorphic form $f$ on $\mathrm{GL}_2(\mathbf A_F)$, the obstruction to cuspidality is

$$
f_N(g)=\int_{F\backslash\mathbf A_F}
f(n(x)g)\,dx.
$$

In the theta construction, integrating kills every nonzero additive Fourier orbit. The remaining zero-orbit functional is the boundary term exposed by Poisson summation. After the two Bruhat cells are separated, its two transforms carry the character data $\psi$ and $\psi^\sigma$. If the two characters differ, orthogonality on the compact norm-one quotient makes the boundary functional vanish. If they agree, its two transforms survive and become the constant terms with inducing characters $\mu$ and $\mu\eta$.

To see the orthogonality, restrict $\psi$ to the compact torus quotient generated by classes $x/\sigma x$. The boundary integral is a scalar multiple of the integral of this character and is zero unless the restriction is trivial. Hilbert 90 identifies this quotient with the part of the norm-one torus relevant to the theta kernel. Triviality is equivalent to

$$
\psi(x)=\psi(\sigma x)
$$

for every idele class $x$, which is precisely $\psi=\psi^\sigma$. In the invariant case the two zero orbits are the two sections attached to $\mu$ and $\mu\eta$.

The calculation also shows why one locally invariant component does not destroy cuspidality. The integral is over a global torus quotient; it vanishes as soon as the global ratio character is nontrivial somewhere.

This computation proves the fundamental criterion.

**Theorem 8.1 (quadratic automorphic induction).** For every Hecke character $\psi$ of $M$, there is an automorphic representation

$$
\operatorname{AI}_{M/F}(\psi)
$$

with local component $\operatorname{AI}_{M_v/F_v}(\psi_v^M)$ at every place. It is cuspidal if and only if

$$
\psi\ne\psi^\sigma.
$$

Its central character, conductor, twists, contragredient, and standard $L$-function are

$$
\begin{aligned}
\omega_{\operatorname{AI}(\psi)}&=\eta_{M/F}\psi|_{C_F},\\
\mathfrak f(\operatorname{AI}(\psi))&=\mathfrak d_{M/F}N_{M/F}(\mathfrak f(\psi)),\\
\operatorname{AI}(\psi)\otimes\mu&\cong
\operatorname{AI}(\psi(\mu\circ N)),\\
\operatorname{AI}(\psi)^\vee&\cong\operatorname{AI}(\psi^{-1}),\\
L(s,\operatorname{AI}(\psi))&=L(s,\psi).
\end{aligned}
$$

Here twisting by $\mu$ means by $\mu\circ\det$ on $\mathrm{GL}_2$.

### 8.2 The descended case and isobaric decomposition

Suppose $\psi=\psi^\sigma$. Then $\psi=\mu\circ N_{M/F}$ for a Hecke character $\mu$ of $F$, unique up to $\eta$. Local induction gives the pair of characters $\mu_v$ and $\mu_v\eta_v$ at every place. Globally,

$$
\boxed{
\operatorname{AI}_{M/F}(\mu\circ N)
=\mu\boxplus\mu\eta_{M/F}.}
$$

The symbol $\boxplus$ denotes the isobaric automorphic sum. Its standard $L$-function is

$$
L(s,\mu)L(s,\mu\eta)=L(s,\mu\circ N),
$$

the familiar factorization of the character $L$-function over the quadratic extension.

This representation is not cuspidal. It belongs to the Eisenstein spectrum, though its local components are usually irreducible principal series. Thus local irreducibility at every place does not imply global cuspidality. The constant term, or equivalently global conjugation invariance, is the missing global test.

### 8.3 Cuspidality is global, supercuspidality is local

If $\psi\ne\psi^\sigma$, the global induction is cuspidal even though almost every split local component is principal series. Conversely, a globally noncuspidal induction can have supercuspidal-looking ramification nowhere, because invariant local characters induce principal series everywhere. These observations prevent two common errors:

- global cuspidality is not the assertion that each $\pi_v$ is supercuspidal;
- a nonsplit local field place produces a supercuspidal only when the local character is noninvariant.

A global noninvariant character may nevertheless be invariant at some nonsplit places. The associated global representation remains cuspidal, while those exceptional local components are principal series. Cuspidality requires only that conjugation fail somewhere globally.

### 8.4 Uniqueness from local data

In the cuspidal case, strong multiplicity one shows that the automorphic representation is uniquely determined by its components outside any finite set. Nevertheless, the construction above established compatibility at **every** place before invoking uniqueness. This order matters: almost-everywhere matching alone would not determine conductors, ramified types, or archimedean weights without further argument.

## 9. Local--global compatibility

### 9.1 One global character, several local algebras

Let $\chi$ be the Galois character attached to a finite-order Hecke character $\psi$, or let $\chi_{\psi,\ell}$ be the $\ell$-adic avatar of an algebraic one. Put

$$
\rho=\operatorname{Ind}_{G_M}^{G_F}\chi.
$$

Choose an embedding $\overline F\hookrightarrow\overline{F_v}$ and a place $w\mid v$. Mackey decomposition gives

$$
\rho|_{G_{F_v}}
\cong
\bigoplus_{w\mid v}
\operatorname{Ind}_{G_{M_w}}^{G_{F_v}}\chi|_{G_{M_w}},
$$

where in the split case each induction has degree one. More concretely,

$$
\rho|_{G_{F_v}}\cong
\begin{cases}
\chi_w\oplus\chi_{w^\sigma},&v=ww^\sigma,\\
\operatorname{Ind}_{G_{M_w}}^{G_{F_v}}\chi_w,&M_w/F_v\text{ is a field}.
\end{cases}
$$

This is precisely the parameter used to define $\operatorname{AI}_{M_v/F_v}(\psi_v^M)$. Thus restriction of global Galois induction and localization of global automorphic induction obey the same double-coset formula.

### 9.2 Compatibility theorem at every place

**Theorem 9.1 (local--global compatibility).** Let $\psi$ be a Hecke character of $M$. For every place $v$ of $F$,

$$
(\operatorname{AI}_{M/F}\psi)_v
\cong\operatorname{AI}_{M_v/F_v}(\psi_v^M).
$$

For finite-order or algebraic $\psi$, the local parameter of the right side is the localization of $\operatorname{Ind}_{G_M}^{G_F}\chi_\psi$ or of its $\ell$-adic avatar, after applying the chosen coefficient embedding and the standard algebraic normalization at $v\mid\ell$.

**Proof strategy.** At good finite places, compare the spherical Whittaker function and its zeta integral. At ramified finite places, vary the local Schwartz function and use the uniqueness of the Whittaker model to identify the full representation, not merely its $L$-factor. At infinity, Fourier transform on $M_v$ gives the induced Weil representation and hence the stated principal or discrete series.

**Proof.** The global construction uses a restricted tensor $W_\varphi=\prod_vW_v$. Fix all factors except $v$. As $\varphi_v$ varies, the $v$-component of the generated representation is the representation spanned by the local Whittaker functions $W_v$. At an unramified place the spherical zeta integral is the character Euler factor, which identifies the unramified parameter. At a ramified place the torus action, Weyl Fourier transform, and Whittaker uniqueness identify the compact-induction or principal-series model described in Chapter 5. The archimedean Fourier action gives induction from $W_{M_w}$ to $W_{F_v}$. Mackey decomposition identifies each of these parameters with the localization of global Galois induction. $\square$

The theorem includes split and ramified places; it is stronger than equality of Euler factors outside a finite set.

### 9.3 Determinants, centers, and conductors match

Compatibility turns the two determinant formulas into one statement:

$$
\det\rho
=\eta_{M/F}(\chi\circ\operatorname{Ver})
\quad\longleftrightarrow\quad
\omega_{\operatorname{AI}(\psi)}
=\eta_{M/F}\psi|_{C_F}.
$$

Likewise, the local Artin conductor of $\rho|_{G_{F_v}}$ equals the local newvector conductor of $\pi_v$:

$$
a_v(\rho)=
\begin{cases}
a_w(\chi)+a_{w^\sigma}(\chi),&v\text{ split},\\
d(M_w/F_v)+f(M_w/F_v)a_w(\chi),&v\text{ nonsplit}.
\end{cases}
$$

For $v\nmid\ell$, $a_w(\chi)=a_w(\psi)$. At $v\mid\ell$, the algebraic correction can contribute to the Galois-theoretic ramification, so the finite automorphic conductor and the full $\ell$-adic Artin conductor should not be equated without specifying normalization. Away from $\ell$, the equality is literal.

### 9.4 A counterexample to good-place complacency

Two characters may agree at all unramified places outside a finite set only if they agree globally, but knowing merely that their induced traces agree can identify $\psi$ only up to conjugation. Indeed,

$$
\operatorname{AI}(\psi)\cong\operatorname{AI}(\psi^\sigma).
$$

This is not an ambiguity in the construction; induction forgets the labeling of the two cosets. It is the only ambiguity in the regular quadratic case. Ramified local data still matter for conductor and type even though strong multiplicity one determines the final cuspidal representation from almost all traces.

## 10. Good primes and Frobenius polynomials

### 10.1 The split-prime calculation

Let $v$ be finite, unramified in $M$, and prime to the conductor of $\psi$. Suppose $v=ww^\sigma$. Put

$$
\alpha_v=\psi_w(\varpi_v),
\qquad
\beta_v=\psi_{w^\sigma}(\varpi_v).
$$

The local representation is the unramified principal series $I(\psi_w,\psi_{w^\sigma})$. Its Hecke polynomial in arithmetic normalization is

$$
P_v(X)=(1-\alpha_vX)(1-\beta_vX)
=1-a_vX+b_vX^2,
$$

where

$$
a_v=\alpha_v+\beta_v,
\qquad
b_v=\alpha_v\beta_v
=\omega_\pi(\varpi_v).
$$

On the Galois side, arithmetic Frobenius belongs to $G_M$ at a split prime and acts diagonally with the same eigenvalues. Hence

$$
\det(1-\rho(\operatorname{Frob}_v)X)=P_v(X).
$$

This is a direct matrix calculation, not an appeal to density.

### 10.2 The inert-prime calculation

Suppose $v$ is inert, with unique place $w$. Then $q_w=q_v^2$, and $\operatorname{Frob}_v$ lies outside $G_{M_w}$. It exchanges the two induced lines. Its square is $\operatorname{Frob}_w$, so in a suitable basis

$$
\rho(\operatorname{Frob}_v)=
\begin{pmatrix}
0&\psi_w(\varpi_w)\\
1&0
\end{pmatrix}.
$$

Therefore

$$
a_v=0,
\qquad
b_v=-\psi_w(\varpi_w),
\qquad
P_v(X)=1-\psi_w(\varpi_w)X^2.
$$

The determinant formula gives the same sign because $\eta_v(\varpi_v)=-1$. The local standard Euler factor

$$
(1-\psi_w(\varpi_w)q_v^{-2s})^{-1}
$$

is exactly the degree-one Euler factor over $M$, since $q_w^{-s}=q_v^{-2s}$.

The vanishing $a_v=0$ at inert good primes is the most visible signature of a quadratic theta series.

The identity $\operatorname{Frob}_v^2=\operatorname{Frob}_w$ in the unramified quotient explains both the exponent $X^2$ and $q_w=q_v^2$. With geometric reciprocity every character value in these polynomials would be inverted. Trace zero would survive, but all nonzero coefficient comparisons would change.

### 10.3 Ramified primes and what the polynomial omits

At a prime ramified in $M/F$, the quadratic character $\eta_v$ is ramified and the automorphic induction cannot be spherical, even if $\psi_w$ is unramified. The discriminant term forces positive conductor. One may still form an inertia-invariant Euler polynomial

$$
\det(1-\operatorname{Frob}_vX\mid\rho^{I_v}),
$$

but its degree can drop below two. It does not by itself record the conductor or the inertial character. This is why statements of local--global compatibility cannot be reduced to good-prime characteristic polynomials.

### 10.4 Ideal-theoretic coefficients

Let $\Psi$ be the ideal character associated with $\psi$. The Dirichlet series of the induction is

$$
L(s,\pi)=L(s,\psi)
=\sum_{\mathfrak A\subset\mathcal O_M}
\Psi(\mathfrak A)N_{M/\mathbf Q}(\mathfrak A)^{-s},
$$

with the usual omission or modification at conductor primes. Grouping ideals by their norm to $F$ gives coefficients on ideals $\mathfrak a$ of $F$:

$$
A(\mathfrak a)=
\sum_{N_{M/F}\mathfrak A=\mathfrak a}\Psi(\mathfrak A).
$$

For a good prime $\mathfrak p$, this says

$$
A(\mathfrak p)=
\begin{cases}
\Psi(\mathfrak P)+\Psi(\mathfrak P^\sigma),
&\mathfrak p=\mathfrak P\mathfrak P^\sigma,\\
0,&\mathfrak p\text{ inert}.
\end{cases}
$$

The formula gives both a computational method and an intuitive picture: a coefficient counts norm fibers, weighted by the character.

## 11. Infinity types and cohomological weights

### 11.1 Why infinity type becomes weight

Finite local components control level and Hecke eigenvalues, but a modular or Hilbert modular form also has a weight. The weight is the archimedean shadow of the difference between conjugate algebraic exponents.

Assume first that $F$ is totally real and $M$ is CM, so every real place $v$ of $F$ has a complex place $w$ above it. Write the local infinity type as

$$
\psi_w(z)=z^{-p_w}\bar z^{-q_w}
$$

up to a common real modulus twist. Conjugation exchanges $p_w$ and $q_w$. If $p_w\ne q_w$, the local induction is a discrete series with lowest weight

$$
k_v=|p_w-q_w|+1.
$$

Thus **regularity** at $v$ means $p_w\ne q_w$. Parallel weight is the special case in which all $k_v$ are equal.

### 11.2 Purity and the common central weight

Suppose

$$
p_w+q_w=W
$$

is independent of $w$. Then the inducing character is pure of weight $W$, and the induced rank-two object has Hodge-type pair $\{p_w,q_w\}$ at the embedding corresponding to $v$. The determinant has weight $W$ and the two Frobenius roots have the expected common complex absolute value after unitary normalization.

For cohomological conventions on $\mathrm{GL}_2$, it is often convenient to order $p_w>q_w$ and twist by a common power so that $q_w=0$. Then

$$
k_v=p_w+1.
$$

Undoing that twist restores the central algebraic weight without changing the difference $k_v-1$.

### 11.3 Parity from the center

At a real place, the discrete series of lowest weight $k_v$ has central action on $-1$ equal to $(-1)^{k_v}$, up to the chosen common determinant twist. On the Hecke-character side, the same sign is obtained from

$$
\eta_v(-1)\psi_w(-1).
$$

Since $M_w=\mathbf C$, the local quadratic character is the sign character of $\mathbf R^\times$. The global central character must be trivial on $F^\times$, so the parities at all real places and the finite central character satisfy a single global compatibility. One cannot choose Hilbert weights and nebentype independently.

In a standard algebraic Hilbert normalization, if the central algebraic exponent is $W$, the condition may be expressed as

$$
k_v\equiv W+1\pmod2
$$

after fixing the same determinant twist at every $v$. What matters is not the isolated congruence but its origin: $-1$ is simultaneously a rational central element and a local component at every real place.

### 11.4 Regular and nonregular infinity types

If $p_w=q_w$, then $\psi_w$ factors through $N_{\mathbf C/\mathbf R}$ and the local induction is reducible at the parameter level, giving two real characters rather than a discrete series. A globally noninvariant character can be nonregular at one archimedean place and still yield a cuspidal automorphic representation, but it will not be regular algebraic or cohomological in the usual degree.

This supplies a useful counterexample: global cuspidality does not imply cohomological regularity. Cuspidality asks whether $\psi$ equals its conjugate globally; regularity asks for inequality of two infinity exponents at every relevant place.

### 11.5 Fields with split real places or complex base places

If a real place of $F$ splits in $M$, the local factor is a real principal series and does not contribute a holomorphic discrete-series weight. If $F_v=\mathbf C$, then $M_v=\mathbf C\times\mathbf C$ and the local factor is a complex principal series whose infinitesimal character is the pair of algebraic exponents from the two embeddings.

The clean Hilbert modular picture therefore belongs to CM extensions of totally real fields. Automorphic induction itself needs no such signature hypothesis; only its interpretation as a holomorphic Hilbert form does.

## 12. Theta series over $\mathbf Q$ and CM forms

### 12.1 Finite-order characters and weight one

Let $M/\mathbf Q$ be imaginary quadratic and let $\psi$ be a finite-order Hecke character with $\psi\ne\psi^\sigma$. Its infinity type is $(0,0)$, and its component on $M\otimes_\mathbf Q\mathbf R=\mathbf C$ is trivial because $\mathbf C^\times$ is connected. Induction at infinity is the reducible two-dimensional parameter $1\oplus\operatorname{sgn}$, whose real local representation has weight-one limit type. The global automorphic induction is nevertheless cuspidal by the global noninvariance of $\psi$, and it gives a cuspidal weight-one theta series.

Its Fourier expansion can be written

$$
f_\psi(z)=
\sum_{\substack{\mathfrak a\subset\mathcal O_M\\
(\mathfrak a,\mathfrak f)=1}}
\psi(\mathfrak a)q^{N\mathfrak a},
\qquad q=e^{2\pi iz},
$$

with the standard finite-conductor convention. The coefficient of a prime $p$ away from the discriminant and conductor is

$$
a_p=
\begin{cases}
\psi(\mathfrak p)+\psi(\bar{\mathfrak p}),&p=\mathfrak p\bar{\mathfrak p},\\
0,&p\text{ inert}.
\end{cases}
$$

The associated complex Galois representation is

$$
\rho_\psi=\operatorname{Ind}_{G_M}^{G_\mathbf Q}\chi_\psi.
$$

It has finite image and odd determinant: complex conjugation lies outside $G_M$ and has determinant $-1$. Its projective image is dihedral when the ratio $\chi_\psi/\chi_\psi^\sigma$ has order greater than two. These are the Artin-type theta series of weight one.

### 12.2 Why the invariant case is not a cusp form

If $\psi=\mu\circ N_{M/\mathbf Q}$, the same formal ideal sum has an Eisenstein decomposition. Automorphically,

$$
\operatorname{AI}_{M/\mathbf Q}(\psi)
=\mu\boxplus\mu\eta_{M/\mathbf Q}.
$$

For $\psi=1$, this is $1\boxplus\eta$. Its $L$-function is the Dedekind zeta factorization

$$
\zeta_M(s)=\zeta_\mathbf Q(s)L(s,\eta).
$$

This example is the simplest possible warning that a theta-shaped series need not be cuspidal; the constant term records descent.

### 12.3 Algebraic characters and holomorphic CM forms

Now let $\psi$ have ideal infinity type $(k-1,0)$ with $k\ge2$:

$$
\psi((a))=a^{k-1}
$$

for $a\equiv1$ modulo the conductor in the chosen complex embedding. The associated series

$$
f_\psi(z)=\sum_{\mathfrak a}\psi(\mathfrak a)q^{N\mathfrak a}
$$

is a holomorphic cuspidal eigenform of weight $k$ whenever $\psi\ne\psi^\sigma$. Its level is

$$
N=|D_M|\,N_{M/\mathbf Q}(\mathfrak f(\psi)),
$$

and its nebentype is determined by

$$
\omega_\pi=\eta_{M/\mathbf Q}\psi|_{\mathbf A_\mathbf Q^\times},
$$

after separating the standard $|\cdot|^{k-1}$ algebraic factor from the finite Dirichlet character.

At every good prime,

$$
X^2-a_pX+\varepsilon(p)p^{k-1}
$$

is both the classical Hecke polynomial and the characteristic polynomial of arithmetic Frobenius on the $\ell$-adic induction. The factor $p^{k-1}$ comes from the algebraic infinity type, while $\varepsilon$ is the finite nebentype.

Such a form has **complex multiplication by $M$**: for every inert prime $p$ away from the level, $a_p=0$, and twisting by $\eta_{M/\mathbf Q}$ leaves the automorphic representation unchanged. Indeed,

$$
\operatorname{AI}(\psi)\otimes\eta
\cong\operatorname{AI}(\psi),
$$

because $\eta\circ N_{M/\mathbf Q}=1$.

### 12.4 A concrete splitting example

Take $M=\mathbf Q(i)$. Away from $2$ and the conductor, a prime $p\equiv3\pmod4$ is inert, so $a_p=0$. A prime $p\equiv1\pmod4$ can be written

$$
p=\pi\bar\pi,
$$

with $\pi=a+bi$ determined up to a unit and conjugation. For an algebraic character of type $(k-1,0)$ whose finite part chooses a primary generator,

$$
a_p=\pi^{k-1}+\bar\pi^{k-1}.
$$

For $k=2$, this is $2a$; for $k=3$, it is $2(a^2-b^2)$. The unit and conductor condition is what makes the choice of primary $\pi$ well defined. Omitting it would make the displayed coefficient depend on multiplying $\pi$ by $i$.

For instance $5=(2+i)(2-i)$ and $13=(3+2i)(3-2i)$. Using these representatives, the raw weight-two conjugate sums are $4$ and $6$, while the raw weight-three sums are $6$ and $10$. The finite component and its primary-generator convention may multiply them by the permitted roots of unity. Meanwhile $3,7,11\equiv3\pmod4$ are inert and have coefficient zero for every such character. The finite component changes split coefficients but cannot change inert-prime vanishing.

### 12.5 Hilbert theta series

Let $F$ be totally real and $M/F$ CM. Choose an algebraic Hecke character with infinity types $(p_v,q_v)$ and $p_v>q_v$ at every real place. The automorphic induction is a cuspidal Hilbert modular representation of weights

$$
k_v=p_v-q_v+1,
$$

provided $\psi\ne\psi^\sigma$. Its conductor is $\mathfrak d_{M/F}N\mathfrak f(\psi)$, and at a good prime $\mathfrak p$ its coefficient is the same norm-fiber sum as before.

Inert primes have zero coefficient, split primes have a sum of conjugate character values, and the several infinity-type differences give the possibly nonparallel Hilbert weight. This supplies automorphic forms over totally real fields with completely explicit Galois inductions and is one source of residual automorphy in later applications.

## 13. Coefficient fields, lattices, and reduction

### 13.1 The field generated by a character

Let $\psi$ be algebraic. Its **coefficient field** $E_\psi$ is generated over $\mathbf Q$ by its values on ideals prime to the conductor, together with the finite roots of unity needed for its finite local components. Under the usual algebraicity hypotheses this is a number field. The Hecke field of $\pi=\operatorname{AI}(\psi)$ is contained in the subfield of $E_\psi$ generated by the symmetric good-prime data, because good split Hecke traces are sums

$$
\psi(\mathfrak P)+\psi(\mathfrak P^\sigma).
$$

It can be strictly smaller than $E_\psi$. For example, a character may take values in a cyclotomic field while all its conjugate sums lie in the maximal real subfield. There need not be a coefficient-field automorphism carrying every value of $\psi$ to the corresponding value of $\psi^\sigma$, so describing the Hecke field as a fixed field requires an additional hypothesis and is avoided here.

The field of rationality and a field of definition should be distinguished. The former fixes the isomorphism class under coefficient automorphisms; the latter supports a chosen model. For a two-dimensional induced representation, any field containing the character values supports the coset-basis model of Chapter 4: the off-diagonal entry is $\chi(s^2)$, so no square root is needed. A square root enters only if one tries to split an invariant induction into its two extensions. The characteristic polynomials themselves already lie in the field generated by traces and determinants.

### 13.2 Integrality of good Hecke data

Suppose $\psi$ has been put in an arithmetic algebraic normalization so that its good ideal values are algebraic integers. Then

$$
a_v=\psi(\mathfrak P)+\psi(\mathfrak P^\sigma)
$$

at split primes and $a_v=0$ at inert primes are algebraic integers. The determinant values are products of good ideal values and are therefore algebraic integers as well. Under a pure arithmetic normalization they take the familiar form of a finite-order value times a power of $q_v$. Hence the good Hecke polynomials lie in $\mathcal O_{E_\psi}[X]$.

Without the arithmetic normalization, integrality can fail. Twisting by $|\cdot|^{-1/2}$ makes Satake parameters unitary but may introduce square roots and denominators. Unitary normalization is analytically natural; arithmetic normalization is the one suited to lattices and reduction. Formulas must specify which is being used.

### 13.3 Stable lattices in the induced representation

Fix a finite extension $E_\lambda/\mathbf Q_\ell$ containing the values of the $\ell$-adic character, with valuation ring $\mathcal O_\lambda$, uniformizer $\varpi_\lambda$, and residue field $k_\lambda$. The continuous character

$$
\chi:G_M\to E_\lambda^\times
$$

takes values in $\mathcal O_\lambda^\times$: its image is compact, and the valuation has no nontrivial compact subgroup. Thus the induction model has an evident stable lattice

$$
T=\operatorname{Ind}_{G_M}^{G_F}\mathcal O_\lambda(\chi).
$$

In the coset basis of Chapter 4, all matrices are integral and invertible over $\mathcal O_\lambda$. Reducing gives

$$
T/\varpi_\lambda T
\cong\operatorname{Ind}_{G_M}^{G_F}\bar\chi.
$$

If one starts with an arbitrary stable lattice in the same characteristic-zero representation, its reduction may be a different extension when the residual representation is reducible. Nevertheless its semisimplification is independent of the lattice. Thus residual statements not tied to the explicit induced lattice should be written

$$
\bar\rho^{\mathrm{ss}}
\cong
(T/\varpi_\lambda T)^{\mathrm{ss}}.
$$

Omitting semisimplification is harmless only when residual irreducibility has already been proved.

### 13.4 Residual dihedral representations

The same index-two argument works over $k_\lambda$, with one caveat in characteristic two. If

$$
\bar\chi\ne\bar\chi^\sigma,
$$

then $\operatorname{Ind}\bar\chi$ is absolutely irreducible: an element of $G_M$ with distinct eigenvalues forces the only stable lines to be the two coordinate lines, and an element outside $G_M$ exchanges them.

If $\bar\chi=\bar\chi^\sigma$, the semisimplification is a sum of extensions to $G_F$ when those extensions exist over the residue field; after a finite scalar extension they do. In odd residual characteristic they differ by $\bar\eta$. In characteristic two, $\bar\eta=1$, so the two characteristic-zero extensions can have the same reduction and a nonsplit self-extension may appear before semisimplification. This is a concrete reason to retain the superscript $\mathrm{ss}$.

When $\bar\chi/\bar\chi^\sigma$ has order $m>2$, the residual projective image is dihedral of order $2m$. If the order is one, the representation is reducible after semisimplification; if it is two, the projective image is a Klein four group, which is dihedral only under a broad naming convention.

### 13.5 A practical residual irreducibility test

The criterion can be checked at one element:

$$
\bar\rho\text{ absolutely irreducible}
\quad\Longleftrightarrow\quad
\exists h\in G_M:
\chi(h)\not\equiv\chi^\sigma(h)\pmod\lambda.
$$

By Chebotarev, one may often take $h=\operatorname{Frob}_\mathfrak P$ at a prime away from all ramification. Thus it is enough to find $\mathfrak P$ with

$$
\psi(\mathfrak P)\not\equiv
\psi(\mathfrak P^\sigma)\pmod\lambda.
$$

Only finitely many $\lambda$ divide a fixed nonzero difference. Hence if $\psi\ne\psi^\sigma$, residual induction is irreducible for all but finitely many coefficient primes. This finiteness conclusion is much stronger than checking a separate matrix calculation for every $\lambda$.

## 14. Twists, conjugation, and controlled ramification

### 14.1 Global twists

For a Hecke character $\mu$ of $F$,

$$
\boxed{
\operatorname{AI}_{M/F}(\psi(\mu\circ N))
\cong\operatorname{AI}_{M/F}(\psi)\otimes(\mu\circ\det).}
$$

On Galois representations the matching formula is

$$
\operatorname{Ind}_{G_M}^{G_F}(\chi\cdot\chi_\mu|_{G_M})
\cong(\operatorname{Ind}_{G_M}^{G_F}\chi)\otimes\chi_\mu.
$$

Twisting does not alter the conjugate ratio:

$$
\frac{\psi(\mu\circ N)}
{(\psi(\mu\circ N))^\sigma}
=\frac\psi{\psi^\sigma}.
$$

It therefore preserves cuspidality and dihedral projective image. It can, however, change the determinant and local conductor. At a place where the two character depths coincide, cancellation may lower the conductor; no universal “maximum” formula is valid.

### 14.2 Conjugating coefficients and conjugating the field

Field conjugation gives

$$
\operatorname{AI}_{M/F}(\psi^\sigma)
\cong\operatorname{AI}_{M/F}(\psi).
$$

Coefficient conjugation is different. For an embedding $\gamma:E_\psi\hookrightarrow\mathbf C$,

$$
\operatorname{AI}_{M/F}(\psi)^\gamma
\cong\operatorname{AI}_{M/F}(\psi^\gamma).
$$

The first identity exchanges the two cosets in induction; the second applies $\gamma$ to every eigenvalue. They can coincide in special cases but should never be conflated.

The contragredient is induced from $\psi^{-1}$. Hence $\operatorname{AI}(\psi)$ is essentially self-dual if and only if, for some $\mu$ on $F$,

$$
\psi^{-1}=\psi(\mu\circ N)
\quad\text{or}\quad
\psi^{-1}=\psi^\sigma(\mu\circ N).
$$

The second alternative is the usual polarization relation for CM characters.

### 14.3 Preserving prescribed local ramification after reduction

Let $w$ be a finite place of $M$ and suppose $\chi|_{I_w}$ has finite image. Ramification survives modulo $\lambda$ provided some inertial value remains nontrivial:

$$
\exists t\in I_w:
\chi(t)\not\equiv1\pmod\lambda.
$$

If $w$ lies over a nonsplit place of $F$ and the local goal is not merely ramification but noninvariance of the induced type, the correct test is

$$
\exists t\in I_w:
\chi(t)/\chi^\sigma(t)\not\equiv1\pmod\lambda.
$$

Then the residual local Galois induction remains irreducible and ramified; its two inertial characters remain distinct. On the characteristic-zero automorphic side, the corresponding nonsplit local component is supercuspidal. Only finitely many coefficient primes divide the nonzero algebraic integers $\chi(t)-1$ or $\chi(t)-\chi^\sigma(t)$. Therefore finitely many prescribed local conditions can be preserved simultaneously after excluding finitely many $\lambda$.

At $w\mid\ell$, reduction can interact with pro-$\ell$ inertia and the algebraic correction. A finite-order character of $\ell$-power order reduces trivially, so ramification need not survive. Prescribed-ramification arguments should either work away from $\ell$ or explicitly control the $\ell$-adic Hodge and inertia data.

### 14.4 Building a character with chosen local behavior

Suppose one wants a residual dihedral representation ramified in prescribed ways at a finite set $S$ of places of $M$. Choose local finite-order characters $\theta_w$ on $M_w^\times$ whose restrictions to units have the desired orders, and impose conjugate data at $w^\sigma$ consistently. Their product must be trivial on every global element lying in the prescribed local unit subgroups. The ray class exact sequence turns this into the precise extension problem for a character of a subgroup of a finite ray class group. When the obstruction is nonzero, one chooses one or more auxiliary conductor places and new local characters that cancel it; their existence is an additional class-field-theoretic choice, not an automatic consequence of merely enlarging a modulus.

Choose one additional prime $\mathfrak P$ at which

$$
\psi(\mathfrak P)\ne\psi(\mathfrak P^\sigma).
$$

This ensures characteristic-zero cuspidality and, away from finitely many coefficient primes, residual irreducibility. Finally exclude coefficient primes dividing the finitely many local differences that certify ramification. The result is a family of residual dihedral representations that is absolutely irreducible and has the prescribed local ramification for all remaining $\lambda$.

The auxiliary global-unit condition is essential. Arbitrary local characters do not necessarily multiply to a character of $C_M$; global units are the obstruction.

### 14.5 Minimality under norm twists

For a local quadratic field extension $E/K$, characters in the set

$$
\{\theta(\mu\circ N_{E/K}):\mu:K^\times\to\mathbf C^\times\}
$$

give determinant twists of the same projective parameter. A **twist-minimal** representative minimizes $a_E(\theta)$ in this set. Its induced conductor is then the smallest among determinant twists, by

$$
a_K(\operatorname{AI}\theta)=d(E/K)+f(E/K)a_E(\theta).
$$

Minimality is local and need not be achieved simultaneously by a single global twist at arbitrarily prescribed places, because a global Hecke character $\mu$ must satisfy its own class-group and unit relations. This is another instance where independent local optimization can fail to globalize.

## 15. Cyclic induction in general degree

### 15.1 The pattern behind the quadratic case

Let $L/F$ be cyclic of degree $n$, with group generated by $\sigma$, and let $\psi$ be a Hecke character of $L$. The conjugacy orbit

$$
\psi,\psi^\sigma,\ldots,\psi^{\sigma^{n-1}}
$$

suggests an $n$-dimensional parameter

$$
\operatorname{Ind}_{G_L}^{G_F}\chi_\psi.
$$

At a split prime it is the direct sum of $n$ characters; at an inert unramified prime arithmetic Frobenius cyclically permutes $n$ lines, so most low traces vanish. The quadratic zero at inert primes is the first instance of this cyclic-permutation phenomenon.

### 15.2 The local construction for cyclic étale algebras

At a place $v$, write

$$
L\otimes_FF_v=\prod_{w\mid v}L_w.
$$

Local class field theory turns the characters $\psi_w$ into characters of $W_{L_w}$. The local induced parameter is

$$
\Phi_v=
\bigoplus_{w\mid v}
\operatorname{Ind}_{W_{L_w}}^{W_{F_v}}\psi_w,
$$

of total dimension $n$. The local correspondence for general linear groups assigns an irreducible admissible representation of $\mathrm{GL}_n(F_v)$ to $\Phi_v$. In the completely split case this is the irreducible Langlands constituent of normalized induction from the $n$ characters, in the order determined by their real exponents. For a field place and a character with full local orbit, the parameter is irreducible and the representation is supercuspidal.

Character induction still has zero monodromy. If normalized parabolic induction reaches a reducibility boundary, the local correspondence selects the constituent with the prescribed semisimple parameter and $N=0$. A generalized Steinberg constituent has $N\ne0$ and is never created by inducing a one-dimensional Weil representation.

The exact local conductor formula is

$$
a_{F_v}(\Phi_v)=
\sum_{w\mid v}
\left(d(L_w/F_v)+f(L_w/F_v)a_w(\psi)\right),
$$

Here $d(L_w/F_v)$ denotes the exponent in $F_v$ of the local discriminant ideal; for a split degree-one factor both $d$ and the extension correction vanish. Local $L$-factors satisfy

$$
L(s,\Phi_v)=\prod_{w\mid v}L(s,\psi_w).
$$

### 15.3 The global cyclic induction theorem

The quadratic Whittaker--Poisson argument is special to rank two. For $n>2$, Poisson summation on the additive space $L$ does not by itself verify the several independent Weyl relations, nor do the functional equations of character twists alone supply a general higher-rank converse theorem. Claiming that one can simply iterate the preceding calculation would therefore leave a genuine automorphy gap. The correct higher-degree interface is the global cyclic automorphic-induction theorem.

**Theorem 15.1 (cyclic automorphic induction).** Let $L/F$ be cyclic of degree $n$ and $\psi$ a Hecke character of $L$. There is an isobaric automorphic representation

$$
\operatorname{AI}_{L/F}(\psi)
$$

of $\mathrm{GL}_n(\mathbf A_F)$ whose local parameter at every $v$ is $\Phi_v$. It satisfies

$$
L(s,\operatorname{AI}_{L/F}\psi)=L(s,\psi)
$$

and is compatible with twists, contragredients, conductors, and coefficient conjugation. It is cuspidal exactly when the stabilizer of $\psi$ in $\operatorname{Gal}(L/F)$ is trivial.

This theorem is recorded here with its exact local and cuspidality assertions, but its higher-rank global proof is not a formal extension of Chapter 7 and is not reproduced. It requires a separate global transfer argument strong enough to prove automorphy of the prescribed local tensor. The quadratic case above remains the complete explicit construction used in this book. No restriction of a $\mathrm{GL}_2$ parameter to $L$, no descent criterion for a pre-existing automorphic representation, and no base-change theorem is being asserted or used here.

### 15.4 Stabilizers and intermediate fields

Let $H$ be the stabilizer of $\psi$ in $\operatorname{Gal}(L/F)$, and let $K=L^H$. Then $\psi$ descends through $N_{L/K}$ to a character $\psi_K$ of $K$, with the expected ambiguity by characters of $K$ that are trivial after norm pullback. The extensions across $H$ are obtained by multiplying one choice by the characters of $H$. Induction in stages therefore decomposes $\operatorname{AI}_{L/F}(\psi)$ isobarically into the automorphic inductions from $K$ of those extensions. Each constituent has degree $[K:F]$, the orbit size of $\psi$. In the extreme case $H=\operatorname{Gal}(L/F)$, one obtains a sum of $n$ characters of $F$.

Thus the degree of a cuspidal constituent is the orbit size of the inducing character. Quadratic induction has only the two extremes: orbit size two gives a cusp form, and orbit size one gives $\mu\boxplus\mu\eta$.

### 15.5 Central characters and the permutation determinant

Let

$$
\delta_{L/F}=\det\operatorname{Ind}_{G_L}^{G_F}1.
$$

This is the sign character of the permutation action on the $n$ cosets. The determinant formula is

$$
\det\operatorname{Ind}_{G_L}^{G_F}\chi
=\delta_{L/F}(\chi\circ\operatorname{Ver}),
$$

and hence

$$
\omega_{\operatorname{AI}_{L/F}(\psi)}
=\delta_{L/F}\psi|_{C_F}.
$$

For odd $n$, an $n$-cycle has positive sign and $\delta_{L/F}$ is trivial. For even $n$, it is the quadratic character cutting out the unique quadratic subextension of $L/F$. The quadratic formula with $\eta_{M/F}$ is exactly the case $n=2$.

The global conductor formula becomes

$$
\mathfrak f(\operatorname{AI}_{L/F}\psi)
=\mathfrak d_{L/F}N_{L/F}(\mathfrak f(\psi)).
$$

### 15.6 What has and has not been used

The theorem moves a character upward from $L$ to a representation over $F$. No construction here starts with a representation over $F$ and restricts its parameter to $L$. The degree-two construction is proved directly above, and the degree-$n$ statement is isolated as a higher-rank global input. The restriction operation and its descent or image criterion belong to the subsequent theory and are not developed here.

## 16. Examples and the final dictionary

### 16.1 A finite dihedral example

Let $M/F$ be quadratic and let $\psi$ be a ray class character of order $m$ such that $\psi/\psi^\sigma$ also has order $m>2$. Then $\pi=\operatorname{AI}(\psi)$ is cuspidal, has finite-order central character

$$
\omega_\pi=\eta\psi|_{C_F},
$$

and gives a finite-image Galois representation with projective image $D_{2m}$. At a good split prime $v=ww^\sigma$,

$$
a_v=\psi(w)+\psi(w^\sigma),
$$

while at a good inert prime $a_v=0$. At a ramified prime of $M/F$, the conductor of $\pi$ contains the local discriminant even if $\psi$ is unramified.

This last feature distinguishes field ramification from character ramification: the former enters through the permutation action, the latter through the character itself.

A concrete unramified example comes from $M=\mathbf Q(\sqrt{-23})$, whose ideal class group is cyclic of order three. Let $\psi$ be a nontrivial class-group character. Complex conjugation inverts ideal classes, so $\psi^\sigma=\psi^{-1}\ne\psi$. The induction is a weight-one cusp form of level $23$ and quadratic nebentype attached to $M$. Its projective Galois image is the dihedral group of order six, equivalently $S_3$.

At an inert prime its coefficient is zero. At a split prime $p=\mathfrak p\bar{\mathfrak p}$, the coefficient is

$$
a_p=\psi(\mathfrak p)+\psi(\mathfrak p)^{-1}.
$$

It equals $2$ when $\mathfrak p$ is principal and $-1$ when its class is nontrivial. Thus the Hecke eigenvalues distinguish splitting completely in the Hilbert class field: inertness in $M$ gives $0$, while the two split Frobenius classes above $M$ give $2$ or $-1$.

### 16.2 A norm-descended counterexample

Let $\mu$ be any Hecke character of $F$ and put $\psi=\mu\circ N$. Then the character may be highly ramified and algebraic, but

$$
\operatorname{AI}(\psi)=\mu\boxplus\mu\eta
$$

is never cuspidal. Its split-prime coefficients still look like sums of two character values, and its local principal series can be irreducible everywhere. Neither elaborate ramification nor local irreducibility repairs the failure of the global orbit condition.

### 16.3 Reading a splitting prime in both languages

Suppose $v=ww^\sigma$ is good. The entire correspondence can be read in one line:

$$
\begin{array}{c}
\text{prime values }\psi(w),\psi(w^\sigma)\\
\downarrow\\
I(\psi_w,\psi_{w^\sigma})\text{ with Satake roots }
\psi(w),\psi(w^\sigma)\\
\downarrow\\
\rho(\operatorname{Frob}_v)
\sim\operatorname{diag}(\psi(w),\psi(w^\sigma)).
\end{array}
$$

Thus the Hecke trace, Frobenius trace, and ideal-theoretic norm-fiber sum are the same number. At an inert prime the diagonal picture is replaced by a permutation matrix, explaining trace zero.

### 16.4 The complete quadratic dictionary

For quick use, the construction may be summarized as follows.

| Character datum over $M$ | Automorphic datum over $F$ | Galois datum over $F$ |
|---|---|---|
| Hecke character $\psi$ | $\pi=\operatorname{AI}_{M/F}(\psi)$ | $\rho=\operatorname{Ind}_{G_M}^{G_F}\chi_\psi$ |
| conjugate $\psi^\sigma$ | same $\pi$ | conjugate induction, isomorphic to $\rho$ |
| $\psi\ne\psi^\sigma$ | $\pi$ cuspidal | $\rho$ irreducible |
| $\psi=\mu\circ N$ | $\mu\boxplus\mu\eta$ | $\chi_\mu\oplus\chi_\mu\eta$ |
| diagonal restriction $\psi|_{C_F}$ | central character $\eta\psi|_{C_F}$ | determinant $\eta(\chi\circ\operatorname{Ver})$ |
| norm twist $\psi(\mu\circ N)$ | $\pi\otimes(\mu\circ\det)$ | $\rho\otimes\chi_\mu$ |
| inverse $\psi^{-1}$ | contragredient $\pi^\vee$ | dual $\rho^\vee$ |
| $v=ww^\sigma$ split | $I(\psi_w,\psi_{w^\sigma})$ | $\chi_w\oplus\chi_{w^\sigma}$ |
| $M_w/F_v$ field, local ratio regular | supercuspidal | irreducible local induction |
| $\psi_w=\mu_v\circ N$ | $I(\mu_v,\mu_v\eta_v)$ | $\chi_{\mu_v}\oplus\chi_{\mu_v}\eta_v$ |
| conductor $\mathfrak f(\psi)$ | $\mathfrak d_{M/F}N\mathfrak f(\psi)$ | Artin conductor with the same local formula |
| infinity type $(p_v,q_v)$ | weight $|p_v-q_v|+1$ | labeled weights $\{p_v,q_v\}$ |
| good split prime | $a_v=\psi(\mathfrak P)+\psi(\mathfrak P^\sigma)$ | same Frobenius trace |
| good inert prime | $a_v=0$ | Frobenius exchanges the two lines |
| reduction with $\bar\psi\ne\bar\psi^\sigma$ | residual eigensystem is non-Eisenstein | residual induction is absolutely irreducible |

The local conductor entry at a nonsplit finite place is

$$
d(M_w/F_v)+f(M_w/F_v)a_w(\psi),
$$

and at a split place it is the sum of the two character conductors. No special representation occurs because the induced character parameter has zero monodromy.

### 16.5 Conclusion: rank two without losing rank-one control

Automorphic induction preserves the explicit nature of a character while adding genuinely nonabelian structure. Conjugation turns one local eigenline into two; an element outside the quadratic subgroup exchanges them; the sign of that exchange produces the quadratic determinant factor. The same exchange makes inert-prime traces vanish and gives the projective image its dihedral shape.

In quadratic degree, Poisson summation is the mechanism that turns the local induced models into automorphic forms. The constant term then reads the conjugacy orbit exactly: a full orbit gives cuspidality, while a descended character gives an Eisenstein isobaric sum. Conductors split into a discriminant contribution from the extension and a normed conductor contribution from the character. Infinity-type differences become cohomological weights, and arithmetic reciprocity makes good-prime Hecke polynomials identical to Frobenius characteristic polynomials.

Because every part of the construction remains visible, one can choose coefficient fields, integral lattices, and reductions with precision. Residual irreducibility is the survival of the conjugate ratio; prescribed ramification is the survival of selected inertia values; semisimplification records exactly what remains when those distinctions collapse. In higher cyclic degree the same ideas persist: conjugacy orbits determine rank and cuspidality, permutation signs determine the extra central factor, and stabilizers explain isobaric decomposition.

The resulting dictionary is more than a source of examples. It is a reusable bridge from class-field-theoretic characters to explicit cuspidal automorphic representations and irreducible Galois representations, with every local invariant accounted for and every normalization exposed.
