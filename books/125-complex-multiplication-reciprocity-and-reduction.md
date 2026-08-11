# Complex Multiplication, Reciprocity, and Reduction

## Contents

1. [The arithmetic problem behind complex multiplication](#1-the-arithmetic-problem-behind-complex-multiplication)
   - [From structure to arithmetic](#11-from-structure-to-arithmetic)
   - [Standing conventions](#12-standing-conventions)
   - [The three actions that must be compared](#13-the-three-actions-that-must-be-compared)
   - [What will be proved](#14-what-will-be-proved)
2. [CM data and their adelic symmetries](#2-cm-data-and-their-adelic-symmetries)
   - [The analytic CM object](#21-the-analytic-cm-object)
   - [Finite ideles and commensurable lattices](#22-finite-ideles-and-commensurable-lattices)
   - [Polarizations and the weight identity](#23-polarizations-and-the-weight-identity)
   - [Level structures remember generators](#24-level-structures-remember-generators)
   - [Orders and the bad set](#25-orders-and-the-bad-set)
3. [Artin reciprocity and normalization](#3-artin-reciprocity-and-normalization)
   - [Arithmetic Artin maps](#31-arithmetic-artin-maps)
   - [Local-to-global compatibility](#32-local-to-global-compatibility)
   - [Prime ideles and ideal symbols](#33-prime-ideles-and-ideal-symbols)
   - [A variance test in the quadratic case](#34-a-variance-test-in-the-quadratic-case)
4. [The comparison theorem](#4-the-comparison-theorem)
   - [A precise form of the main theorem](#41-a-precise-form-of-the-main-theorem)
   - [The algebraic CM locus](#42-the-algebraic-cm-locus)
   - [Rigidity, algebraicity, and the canonical moduli model](#43-rigidity-algebraicity-and-the-canonical-moduli-model)
   - [The structural ray action](#44-the-structural-ray-action)
   - [The clean-prime Frobenius calculation](#45-the-clean-prime-frobenius-calculation)
   - [From prime Frobenius to arbitrary Artin action](#46-from-prime-frobenius-to-arbitrary-artin-action)
   - [Theta values, torsion, and lattices](#47-theta-values-torsion-and-lattices)
   - [Idele independence and the descent cocycle](#48-idele-independence-and-the-descent-cocycle)
   - [Polarized and order-valued forms](#49-polarized-and-order-valued-forms)
5. [Galois orbits and class fields](#5-galois-orbits-and-class-fields)
   - [The stabilizer of a CM datum](#51-the-stabilizer-of-a-cm-datum)
   - [The class field of a rigidified CM point](#52-the-class-field-of-a-rigidified-cm-point)
   - [Orbit and degree formulas](#53-orbit-and-degree-formulas)
   - [Ring class fields in dimension one](#54-ring-class-fields-in-dimension-one)
   - [Why the reflex class group need not act faithfully](#55-why-the-reflex-class-group-need-not-act-faithfully)
6. [Effective descent and canonical models](#6-effective-descent-and-canonical-models)
   - [Field of moduli versus field of definition](#61-field-of-moduli-versus-field-of-definition)
   - [Rigidification kills the descent obstruction](#62-rigidification-kills-the-descent-obstruction)
   - [The canonical descent datum](#63-the-canonical-descent-datum)
   - [Forgetting level and polarization](#64-forgetting-level-and-polarization)
   - [Endomorphisms and fields of definition](#65-endomorphisms-and-fields-of-definition)
7. [CM points in ambient Shimura data](#7-cm-points-in-ambient-shimura-data)
   - [The torus attached to a CM point](#71-the-torus-attached-to-a-cm-point)
   - [Reciprocity after an ambient embedding](#72-reciprocity-after-an-ambient-embedding)
   - [Double cosets and level](#73-double-cosets-and-level)
   - [Hilbert, quaternionic, and unitary realizations](#74-hilbert-quaternionic-and-unitary-realizations)
   - [Functoriality](#75-functoriality)
8. [Potential good reduction](#8-potential-good-reduction)
   - [Why CM forbids persistent monodromy](#81-why-cm-forbids-persistent-monodromy)
   - [The potential-good-reduction theorem](#82-the-potential-good-reduction-theorem)
   - [A criterion for good reduction over the given field](#83-a-criterion-for-good-reduction-over-the-given-field)
   - [Integral CM data and excluded primes](#84-integral-cm-data-and-excluded-primes)
9. [Unramified primes and Frobenius](#9-unramified-primes-and-frobenius)
   - [The Frobenius ideal relation](#91-the-frobenius-ideal-relation)
   - [Frobenius as a CM endomorphism](#92-frobenius-as-a-cm-endomorphism)
   - [The norm equation and Weil size](#93-the-norm-equation-and-weil-size)
   - [Characteristic polynomials](#94-characteristic-polynomials)
   - [Split, inert, and ramified behavior](#95-split-inert-and-ramified-behavior)
10. [Newton slopes and ordinary reduction](#10-newton-slopes-and-ordinary-reduction)
    - [Valuations of the reflex ideal](#101-valuations-of-the-reflex-ideal)
    - [The slope formula](#102-the-slope-formula)
    - [The ordinary criterion](#103-the-ordinary-criterion)
    - [Elliptic and quartic examples](#104-elliptic-and-quartic-examples)
11. [Bad reduction, conductors, and boundaries](#11-bad-reduction-conductors-and-boundaries)
    - [Four different meanings of bad](#111-four-different-meanings-of-bad)
    - [Ramified reciprocity has no prime Frobenius](#112-ramified-reciprocity-has-no-prime-frobenius)
    - [Nonmaximal orders and integral failure](#113-nonmaximal-orders-and-integral-failure)
    - [Changing the field of definition](#114-changing-the-field-of-definition)
12. [The finite-place reciprocity package](#12-the-finite-place-reciprocity-package)
    - [A reusable theorem](#121-a-reusable-theorem)
    - [A normalization checklist](#122-a-normalization-checklist)
    - [Conclusion](#123-conclusion)

## 1. The arithmetic problem behind complex multiplication

The preceding theory constructs a complex abelian variety from a CM field, a type, and a lattice. It also constructs a reflex field and a reflex norm. Those constructions do not yet say what happens when an automorphism of the complex numbers acts on the coefficients of the abelian variety. The central arithmetic problem is to identify that Galois action with the ideal action already visible in the complex uniformization.

This comparison is the main theorem of complex multiplication. Once its direction is fixed, several consequences become parts of one mechanism. CM points acquire canonical fields of definition; their Galois orbits become class-field-theoretic; inertia becomes a test for good reduction; and at an unramified good prime, Frobenius is described by a reflex ideal. The purpose of this book is to prove that comparison in the CM cases needed for polarized PEL data and to draw its finite-place consequences without erasing any hypothesis.

### 1.1 From structure to arithmetic

Let $K$ be a CM field of degree $2g$, let $c$ be CM conjugation, let $\Phi$ be a CM type, and let

$$
E=E(K,\Phi)
$$

be the reflex field. Structural CM theory gives the torus morphism

$$
r_\Phi:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m
\longrightarrow \operatorname{Res}_{K/\mathbf Q}\mathbf G_m. \tag{1.1}
$$

Its direction is from the reflex field to the CM field. On finite ideles it is

$$
r_\Phi:\mathbf A_{E,f}^{\times}\longrightarrow
\mathbf A_{K,f}^{\times}. \tag{1.2}
$$

By contrast, the elementary type norm sends $K^\times$ toward $E^\times$. The two maps are not interchangeable.

For a fractional $K$-ideal $\mathfrak a$, the complex torus

$$
A(\mathfrak a,\Phi)=\mathbf C^\Phi/\Phi(\mathfrak a) \tag{1.3}
$$

has CM by the multiplier order of $\mathfrak a$. If $\mathfrak c$ is an invertible $K$-ideal, our ideal-action convention is

$$
\mathfrak c*A(\mathfrak a,\Phi)
=A(\mathfrak c^{-1}\mathfrak a,\Phi). \tag{1.4}
$$

Thus the inverse in the lattice is already built into the symbol $*$. The reciprocity theorem will say that arithmetic Artin acting through an idele $s$ has the same effect as $r_\Phi(s)*$. Formula (1.4), not an additional inverse on the Artin map, is responsible for the inverse lattice.

### 1.2 Standing conventions

All number fields lie in a fixed $\overline{\mathbf Q}\subset\mathbf C$. For a number field $F$,

$$
\operatorname{Art}_F:\mathbf A_F^\times/F^\times
\longrightarrow G_F^{\mathrm{ab}} \tag{1.5}
$$

denotes arithmetic global reciprocity. At a finite place $v$, a uniformizer maps in the maximal unramified quotient to arithmetic Frobenius

$$
x\longmapsto x^{q_v}. \tag{1.6}
$$

Only the finite component of an idele enters $r_\Phi$. When an idele class is represented by $s=(s_f,s_\infty)$, we write $r_\Phi(s_f)$. Principal ideles are killed by (1.5), while the reflex norm of a principal element need not be $1$; it instead gives the isomorphism between two lattice presentations of the same CM object.

For an automorphism $\sigma$ of $\mathbf C$ and a complex variety $X$, $X^\sigma$ means base change by $\sigma$ on coefficients. If $x$ is a geometric point, its image is written $x^\sigma$. Composition is normalized by

$$
(X^\sigma)^\tau=X^{\tau\sigma}. \tag{1.7}
$$

This convention matters in cocycle formulas.

We normally work with a maximal order $\mathcal O_K$. When an order $\mathcal O\subset K$ is used, every ideal action is restricted to invertible proper $\mathcal O$-ideals, and primes dividing its conductor are explicitly excluded from ideal-theoretic good-prime assertions.

### 1.3 The three actions that must be compared

There are three actions:

$$
\begin{array}{ccccc}
\mathbf A_{E,f}^\times
&\xrightarrow{\ r_\Phi\ }&
\mathbf A_{K,f}^\times
&\longrightarrow&
\{\text{CM lattice data}\},\\
\downarrow&&&&\uparrow\\
G_E^{\mathrm{ab}}
&\longrightarrow&&&
\{\text{Galois conjugates}\}.
\end{array} \tag{1.8}
$$

The left arrow is global Artin reciprocity; it is naturally a quotient map after passage to the profinite completion of the idele class group. The top-right route uses the reflex norm followed by the inverse ideal action. The bottom route is ordinary Galois conjugation of algebraic coefficients. The main theorem asserts that the two routes agree on CM objects, including their endomorphisms and prime-to-bad level data.

This is not formal. The reflex norm was defined from a Hodge cocharacter, whereas Galois conjugation is defined algebraically. The bridge will have two parts. First, the determinant condition cuts out a finite étale algebraic CM locus over $E$, which proves algebraicity. Second, at clean primes its Hodge filtration determines the elementary divisors of crystalline Frobenius, and those divisors are the inverse-incidence exponents of the reflex norm. Global class field theory then upgrades prime Frobenius to arbitrary Artin action. The simultaneous torsion and lattice comparison follows from the resulting identities at every fine level.

### 1.4 What will be proved

The central statement has four layers.

First, if $\sigma\in\operatorname{Aut}(\mathbf C/E)$ and $s$ represents $\sigma$ under arithmetic reciprocity, then

$$
A^\sigma\simeq r_\Phi(s_f)*A. \tag{1.9}
$$

Second, after a sufficiently fine level rigidifies the datum, the isomorphisms in (1.9) satisfy descent and cocycle identities. The resulting CM point is defined over the class field cut out by its adelic stabilizer.

Third, every CM abelian variety has potentially good reduction. At a place where it already has good reduction, inertia and Frobenius can be read from local reciprocity.

Fourth, at a prime unramified in the relevant class field and away from the order, polarization, and level discriminants, the Frobenius isogeny has ideal prescribed by the reflex norm. This produces its norm equation, characteristic polynomial, and Newton slopes.

Statements about a prime ideal will never be made at a ramified prime as though a canonical Frobenius existed. Statements about a Frobenius endomorphism will always specify a finite residue field and a field over which the full CM action is defined.

## 2. CM data and their adelic symmetries

Reciprocity compares Galois conjugation with an adelic operation. Before proving the comparison, we must say exactly what the adelic operation does to the lattice, polarization, order action, and level structure. Each extra datum changes the stabilizer and therefore changes the field of definition.

### 2.1 The analytic CM object

Fix a fractional ideal $\mathfrak a$ of $K$. Under the type embedding

$$
\Phi:K\longrightarrow\mathbf C^\Phi,
\qquad x\longmapsto(\varphi(x))_{\varphi\in\Phi},
$$

the quotient (1.3) is a complex abelian variety. Let $\xi\in K$ satisfy

$$
\bar\xi=-\xi,
\qquad \operatorname{Im}\varphi(\xi)>0\quad(\varphi\in\Phi), \tag{2.1}
$$

and

$$
\xi\mathfrak a\bar{\mathfrak a}\subseteq\mathfrak D_K^{-1}. \tag{2.2}
$$

Then

$$
E_\xi(x,y)=\operatorname{Tr}_{K/\mathbf Q}(\xi\bar x y) \tag{2.3}
$$

is an integral Riemann form. Equality in (2.2) gives a principal polarization. Multiplication by $K$ on homology is the chosen CM labeling

$$
\iota:K\hookrightarrow\operatorname{End}^0(A). \tag{2.4}
$$

The rational homology $V=H_1(A,\mathbf Q)$ is a one-dimensional $K$-vector space. Choosing a $K$-basis identifies $V$ with $K$ and its integral lattice with $\mathfrak a$. Changing that basis by $u\in K^\times$ replaces

$$
(\mathfrak a,\xi)
\quad\text{by}\quad
(u\mathfrak a,\xi/(u\bar u)). \tag{2.5}
$$

Thus formulas involving $\mathfrak a$ are presentations of an intrinsic object, not extra canonical choices.

### 2.2 Finite ideles and commensurable lattices

For $t\in\mathbf A_{K,f}^\times$, define the fractional ideal $\mathfrak c(t)$ by

$$
\mathfrak c(t)\widehat{\mathcal O}_K=t\widehat{\mathcal O}_K. \tag{2.6}
$$

Equivalently, its exponent at a prime $\mathfrak q$ is $v_\mathfrak q(t_\mathfrak q)$. The adelic transform of the lattice is characterized by

$$
\widehat{\mathfrak a_t}=t^{-1}\widehat{\mathfrak a}; \tag{2.7}
$$

hence $\mathfrak a_t=\mathfrak c(t)^{-1}\mathfrak a$. This extends (1.4).

Multiplication by a principal element $u\in K^\times$ gives an isomorphism

$$
A(u^{-1}\mathfrak a,\Phi)\xrightarrow{\ u\ }
A(\mathfrak a,\Phi). \tag{2.8}
$$

Multiplication by an integral unit idele changes the local trivialization but not the ideal. Consequently an unrigidified CM isomorphism class sees the quotient

$$
K^\times\backslash\mathbf A_{K,f}^\times/\widehat{\mathcal O}_K^\times, \tag{2.9}
$$

whereas a level structure sees more of the finite idele itself.

The action is multiplicative. From (2.7),

$$
(t_1t_2)*A=t_1*(t_2*A). \tag{2.10}
$$

This elementary identity later becomes the descent cocycle after $t_i$ are reflex norms of Artin ideles.

### 2.3 Polarizations and the weight identity

The reflex norm satisfies on finite ideles

$$
r_\Phi(s)\overline{r_\Phi(s)}=N_{E/\mathbf Q}(s), \tag{2.11}
$$

where the right side is a finite idele of $\mathbf Q$. If $\mathfrak b$ is an integral ideal of $E$ prime to all excluded primes and

$$
\mathfrak c=R_\Phi(\mathfrak b),
\qquad n=N_{E/\mathbf Q}(\mathfrak b), \tag{2.12}
$$

then

$$
\mathfrak c\bar{\mathfrak c}=n\mathcal O_K. \tag{2.13}
$$

Therefore the transformed polarized lattice is

$$
(\mathfrak a,\xi)
\longmapsto
(\mathfrak c^{-1}\mathfrak a,n\xi). \tag{2.14}
$$

Indeed,

$$
(n\xi)(\mathfrak c^{-1}\mathfrak a)
\overline{(\mathfrak c^{-1}\mathfrak a)}
=\xi\mathfrak a\bar{\mathfrak a}. \tag{2.15}
$$

Thus principal polarizations remain principal, although the natural isogeny pulls the new polarization back to $n$ times the old one. One should not replace $n$ in (2.14) by a local norm component or by $\mathfrak c\bar{\mathfrak c}$ without first passing from ideles to ideals; those expressions live in different groups.

### 2.4 Level structures remember generators

For an integer $N\geq3$, prime to the conductor of the order in use, the $N$-torsion is

$$
A[N](\mathbf C)=N^{-1}\mathfrak a/\mathfrak a. \tag{2.16}
$$

A full $\mathcal O$-linear level structure chooses an isomorphism from a fixed free rank-one $\mathcal O/N\mathcal O$-module to (2.16). If $t$ is a unit at every prime dividing $N$, multiplication by $t^{-1}$ on finite completions transports this structure. Two ideles defining the same ideal can act differently modulo $N$. That is why class groups suffice for unlevelled CM varieties but ray class groups occur after level is imposed.

For a symplectic level structure, the Weil pairing is also fixed. The multiplier of $r_\Phi(s)$ is the reduction of $N_{E/\mathbf Q}(s)$ modulo $N$. A strict symplectic level is preserved only when this multiplier is $1$; a similitude level records it. This distinction will be built into the stabilizer rather than hidden in the notation.

The condition $N\geq3$ has a geometric purpose. An automorphism of a polarized abelian variety acting trivially on full level $N$ is the identity. Indeed, its action on every $N$-torsion point is trivial, and the injectivity of the action of a finite-order polarized automorphism on prime-to-characteristic Tate modules forces it to be trivial. Rigidification will make descent effective.

### 2.5 Orders and the bad set

Let $\mathcal O\subset K$ have conductor $\mathfrak f$. A proper invertible $\mathcal O$-ideal is locally free of rank one. The ideal action and its inverse lattice remain valid for such ideals. At a prime dividing $\mathfrak f$, however, an arbitrary proper ideal need not be invertible, and

$$
\mathbf A_{K,f}^\times/\widehat{\mathcal O}^{\times}
$$

does not identify with the group of all fractional $\mathcal O$-ideals without qualifications.

We therefore attach to a CM datum a finite **integral bad set** $S$ containing:

- primes dividing the conductor of $\mathcal O$;
- primes dividing the discriminant of the CM algebra, where its integral local factors cease to be étale;
- primes dividing the degree of the chosen polarization;
- primes dividing the chosen level;
- primes where an ambient PEL lattice or pairing is not self-dual;
- primes ramified in a field extension whenever an unramified Frobenius symbol is to be used.

Outside $S$, every order lattice is locally free, every relevant isogeny is represented by an invertible ideal, and prime-to-level torsion is finite étale. This does not assert good reduction; it identifies the primes at which the clean integral formulas are even eligible to be applied.

## 3. Artin reciprocity and normalization

The main theorem contains an inverse that can migrate among three conventions: arithmetic versus geometric Frobenius, covariant homology versus contravariant cohomology, and direct versus inverse ideal action. We fix all three before stating it.

### 3.1 Arithmetic Artin maps

For a number field $F$, global class field theory gives

$$
\operatorname{Art}_F:C_F=\mathbf A_F^\times/F^\times
\longrightarrow G_F^{\mathrm{ab}}. \tag{3.1}
$$

At finite level $L/F$, its quotient has kernel $N_{L/F}C_L$ and induces

$$
C_F/N_{L/F}C_L\simeq\operatorname{Gal}(L/F). \tag{3.2}
$$

At a nonarchimedean place $v$, a uniformizer maps to arithmetic Frobenius in every unramified quotient. Units map to inertia. Thus if $L/F$ is unramified at $v$,

$$
\operatorname{Art}_{L/F}(\mathfrak p_v)
=\operatorname{Frob}^{\mathrm{arith}}_v. \tag{3.3}
$$

At a ramified place, a prime ideal alone has no Artin symbol. A uniformizer maps to a lift of residue Frobenius, but changing it by a unit changes the lift by inertia.

### 3.2 Local-to-global compatibility

Embed $F_v^\times$ into the ideles at the $v$-component. The composite with global reciprocity equals local reciprocity followed by the inclusion of the decomposition group into the global abelianized Galois group. Consequently:

$$
\begin{aligned}
\mathcal O_v^\times&\longleftrightarrow I_v^{\mathrm{ab}},\\
U_v^n&\longleftrightarrow G_v^n\text{ in the abelian inertia quotient}\quad(n\geq1),\\
\pi_v&\longleftrightarrow\text{arithmetic Frobenius modulo inertia}.
\end{aligned} \tag{3.4}
$$

Norm functoriality has a direction that will matter. If $F'/F$ is finite, then

$$
\operatorname{Art}_F(N_{F'/F}s)
=\operatorname{Art}_{F'}(s)|_{F^{\mathrm{ab}}}. \tag{3.5}
$$

Thus norm on ideles corresponds to restriction of Galois automorphisms. This agrees with functoriality of reflex norms and will ensure that changing the field over which a CM point is considered does not change its geometric action.

### 3.3 Prime ideles and ideal symbols

Let $v$ be a finite place of $E$, and choose a uniformizer $\pi_v$. The finite idele equal to $\pi_v$ at $v$ and $1$ elsewhere represents the prime ideal $\mathfrak p_v$. Its reflex image represents

$$
R_\Phi(\mathfrak p_v). \tag{3.6}
$$

If a class field $H/E$ is unramified at $v$, (3.3) and the desired comparison predict

$$
A^{\operatorname{Frob}_v}\simeq
R_\Phi(\mathfrak p_v)*A
=A(R_\Phi(\mathfrak p_v)^{-1}\mathfrak a,\Phi). \tag{3.7}
$$

Equation (3.7) is our primary direction check. If global reciprocity were normalized geometrically, $\mathfrak p_v$ would have to be replaced by $\mathfrak p_v^{-1}$. If the ideal action were defined by $\mathfrak c\mathfrak a$ rather than $\mathfrak c^{-1}\mathfrak a$, the displayed lattice would also reverse. We make neither change.

### 3.4 A variance test in the quadratic case

Let $K$ be imaginary quadratic and let $\Phi=\{\iota\}$. Then $E=K$ and $r_\Phi$ is the identity. The predicted formula is

$$
A(\mathfrak a)^\operatorname{Frob}_{\mathfrak p}
\simeq A(\mathfrak p^{-1}\mathfrak a) \tag{3.8}
$$

at an unramified prime $\mathfrak p$. The two sides are connected by the $\mathfrak p$-isogeny in the ideal-action convention. Iterating around a prime of residue degree $f$ gives

$$
\mathfrak p^{-f}\mathfrak a=u^{-1}\mathfrak a
$$

for a generator $u$ of $\mathfrak p^f$ in the relevant class field stabilizer. The resulting $q$-power Frobenius endomorphism is multiplication by $u$ up to a root of unity, and

$$
u\bar u=q. \tag{3.9}
$$

This matches the degree $q$ of Frobenius. Reversing only one of Artin or the lattice action would produce the dual isogeny and fail this consistent orbit calculation.

## 4. The comparison theorem

We now prove the arithmetic assertion that structural CM theory leaves open. An analytic theta-transformation formula is not enough: it compares two complex presentations after an adelic change, but by itself it neither puts a CM point over $\overline{\mathbf Q}$ nor identifies the action of an arbitrary automorphism of $\mathbf C$. Those are the two arithmetic steps that must be supplied rather than hidden in the word “reciprocity.”

The proof below is algebraic and noncircular. We put rigidified CM objects of fixed type in a zero-dimensional PEL moduli scheme over the reflex field and prove that this scheme is finite étale. This gives algebraicity and a canonical algebraic moduli model. We then spread the finite scheme and its universal abelian variety over a localization of $\mathcal O_E$. At every clean prime, contravariant Dieudonné theory and the determinant condition identify the relative Frobenius kernel with the kernel of the reflex-ideal isogeny. Finally, a zeta-function generation argument upgrades those prime identities to the action of the whole absolute Galois group; global class field theory then gives every idele and every Artin automorphism. Torsion, theta values, lattices, and descent are consequences of that arithmetic comparison.

### 4.1 A precise form of the main theorem

Let $A/\mathbf C$ carry a faithful action $\iota:K\hookrightarrow\operatorname{End}^0(A)$ of type $\Phi$, and choose a $K$-linear identification

$$
H_1(A,\mathbf Q)\simeq K
$$

under which $H_1(A,\mathbf Z)=\mathfrak a$. Write $\widehat{\mathfrak a}=\mathfrak a\otimes\widehat{\mathbf Z}$.

**Theorem 4.1 (main theorem of complex multiplication, arithmetic normalization).** Let $\sigma\in\operatorname{Aut}(\mathbf C/E)$. Choose an idele $s\in\mathbf A_E^\times$ whose Artin image is the restriction of $\sigma$ to $E^{\mathrm{ab}}$. Then there is a $K$-linear identification

$$
H_1(A^\sigma,\mathbf Q)\simeq K \tag{4.1}
$$

for which

$$
H_1(A^\sigma,\widehat{\mathbf Z})
=r_\Phi(s_f)^{-1}\widehat{\mathfrak a}. \tag{4.2}
$$

Equivalently,

$$
(A^\sigma,\iota^\sigma)
\simeq r_\Phi(s_f)*(A,\iota). \tag{4.3}
$$

The isomorphism respects every prime-to-bad order action and transports level by multiplication with $r_\Phi(s_f)^{-1}$. With a polarization, the comparison is a similitude whose multiplier is prescribed by the weight identity.

More intrinsically, if $x=(A,\iota,\lambda,\eta)$ is any sufficiently rigid finite-level CM datum and the right side means transport of all displayed structures, then

$$
x^\sigma=r_\Phi(s_f)*x. \tag{4.3a}
$$

This equality is an equality of geometric points of the algebraic fine moduli scheme. It is therefore stronger than an equality of unpolarized complex tori.

The theorem concerns $\sigma$ fixing $E$. For arbitrary $\tau\in\operatorname{Aut}(\mathbf C)$, first transport $(K,\Phi,E)$ to $(\tau K,\tau\Phi,\tau E)$ and then apply the theorem over $\tau E$. One must not feed such a $\tau$ directly into $\operatorname{Art}_E$ unless it fixes $E$.

### 4.2 The algebraic CM locus

We first construct the algebraic object on which the comparison will be proved. Choose an order $\mathcal O\subset K$ preserving the lattice of $A$, a CM-compatible polarization $\lambda$ of degree $d_\lambda$, and an integer $N\geq3$ prime to the conductor of $\mathcal O$ and to $d_\lambda$. Choose a full $\mathcal O/N\mathcal O$-linear similitude level $\eta_N$. We use a similitude level, or equivalently the union of the symplectic components with their cyclotomic descent, so that the moduli problem is defined over $E$ rather than over a field obtained by choosing one primitive $N$-th root of unity. If desired, add a theta-group frame of an auxiliary symmetric power of $\lambda$. We write $\rho$ for this entire finite rigidification.

The fine PEL construction gives a separated algebraic scheme $\mathscr M_{N,d_\lambda}$ of finite type, with a universal abelian scheme and universal displayed structures. Inside it impose the $\mathcal O$-action, the Rosati relation

$$
\iota(a)^\dagger=\iota(\bar a), \tag{4.4}
$$

and the determinant condition of type $\Phi$:

$$
\det\bigl(T-\iota(a)\mid\operatorname{Lie}A\bigr)
=\prod_{\varphi\in\Phi}(T-\varphi(a))
\qquad(a\in\mathcal O). \tag{4.5}
$$

It is enough to impose (4.5) on a finite set of generators of $\mathcal O$. The coefficients on the right are fixed by exactly the stabilizer of the type, so they lie in the reflex field $E$. Thus these equations define an algebraic PEL subfunctor over $E$; call its fine moduli scheme

$$
\mathscr C=\mathscr C(\mathcal O,\Phi,d_\lambda,N,\rho). \tag{4.6}
$$

This construction is the first place where the reflex field enters arithmetically. It uses the field of definition of the Hodge type, but no reciprocity theorem and no assertion about the coordinates of a CM point.

Every complex CM datum with the chosen numerical invariants gives a point of $\mathscr C(\mathbf C)$. Conversely, the degree equality $[K:\mathbf Q]=2\dim A$ and (4.5) force the rational homology of every characteristic-zero geometric fiber to be a rank-one $K$-module of type $\Phi$. The complex classification therefore identifies its geometric points with the familiar polarized ideal data, together with the chosen finite rigidification. In particular, the ideal classification is being used only to describe the geometric fibers of an already algebraic moduli problem.

The full level $N\geq3$ kills automorphisms. Hence $\mathscr C$ represents a sheaf rather than merely a stack, and its universal family is an honest abelian scheme. A theta frame is optional for this conclusion. Its later role is to turn theta sections into algebraic projective coordinates; it is not an arithmetic substitute for the construction of $\mathscr C$.

### 4.3 Rigidity, algebraicity, and the canonical moduli model

**Proposition 4.2 (rigidity and algebraicity).** The $E$-scheme $\mathscr C$ is finite étale. Consequently every rigidified CM point of type $\Phi$, every value at it of an $E$-rational moduli function, and every normalized theta-null ratio on a theta-framed cover is algebraic over $E$.

**Proof.** Let $k$ be an algebraically closed field of characteristic zero containing $E$, and let $x\in\mathscr C(k)$. Put

$$
H=H^1_{\mathrm{dR}}(A_x/k),
\qquad F^1=H^0(A_x,\Omega^1_{A_x/k}). \tag{4.7}
$$

After extending $k$ if necessary, the étale algebra $K\otimes_\mathbf Q k$ splits and its idempotents decompose $H$. Condition (4.5) gives one Hodge line for each character in $\Phi$. The polarization pairs the $\tau$- and $\bar\tau$-summands perfectly, its Rosati involution being CM conjugation, and $F^1$ is Lagrangian. It therefore gives one complementary line for each character in $\bar\Phi$. Since $\Phi\sqcup\bar\Phi$ is the full embedding set, $H$ is rank one over $K\otimes_\mathbf Q k$ and

$$
H=\bigoplus_{\tau:K\hookrightarrow k}H_\tau,
\qquad \dim_kH_\tau=1. \tag{4.8}
$$

The determinant condition says

$$
F^1=\bigoplus_{\varphi\in\Phi}H_\varphi, \tag{4.9}
$$

after the chosen embedding of the reflex data in $k$. A first-order deformation of an abelian variety is a first-order deformation of its Hodge filtration. Requiring the $\mathcal O$-action to lift cuts its tangent space down to

$$
\operatorname{Hom}_{\mathcal O\otimes k}(F^1,H/F^1). \tag{4.10}
$$

The source is a sum of the characters in $\Phi$ and the target a sum of the complementary characters. No character occurs on both sides, so (4.10) is zero. The polarization and level conditions can only cut the tangent space down further. Thus every geometric point has zero tangent space.

The PEL scheme is of finite type over $E$. Zero tangent space implies that every local ring of $\mathscr C_{\overline E}$ has dimension zero and is reduced. Hence $\mathscr C$ is a zero-dimensional reduced scheme of finite type over a characteristic-zero field. Such a scheme is finite étale. In particular, every map $\operatorname{Spec}\mathbf C\to\mathscr C$ factors through a finite extension of $E$ inside $\overline{\mathbf Q}$. This proves algebraicity without evaluating a theta series. $\square$

There are two useful consequences.

First, the residue field $E(x)$ of a point $x$ is already a field of definition for the *fine moduli object*: the universal abelian scheme, $\mathcal O$-action, polarization homomorphism, and finite level restrict to $E(x)$. This is a canonical model in the exact moduli sense required here. It has not yet been proved that $E(x)/E$ is abelian; that will be a conclusion of the arithmetic comparison.

Second, finite étale schemes and abelian schemes spread out. After enlarging a finite set $S_0$ of finite places of $E$, there are

$$
R=\mathcal O_E[S_0^{-1}],
\qquad \mathscr C_R\longrightarrow\operatorname{Spec}R \tag{4.11}
$$

with $\mathscr C_R$ finite étale, and an abelian scheme $\mathscr A\to\mathscr C_R$ carrying all universal structures whose generic fiber is the one above. We enlarge $S_0$ so that the order is maximal and étale at every remaining residue characteristic, the polarization degree and level are invertible, and every finite rigidification is étale. This spread is obtained from the finite algebraic data just constructed; it is not an assumed integral canonical-model theorem.

### 4.4 The structural ray action

We next construct an adelic action without mentioning Galois. Let $\mathfrak b$ be an integral ideal of $E$ prime to $S_0$, and put

$$
\mathfrak c=R_\Phi(\mathfrak b),
\qquad n=N_{E/\mathbf Q}(\mathfrak b). \tag{4.12}
$$

If $\mathcal O$ is nonmaximal, $S_0$ contains its conductor and $\mathfrak c$ in this paragraph means the unique proper invertible $\mathcal O$-ideal prime to the conductor whose extension to $\mathcal O_K$ is $R_\Phi(\mathfrak b)$. Extension and contraction give this ideal, and the local equality with the maximal order away from the conductor preserves the weight identity. We suppress this harmless subscript only at the clean primes where it is valid.

For a geometric point $x=(A,\iota,\lambda,\rho)$, the finite subgroup

$$
A[\mathfrak c]=\{P:aP=0\text{ for every }a\in\mathfrak c\} \tag{4.13}
$$

is the kernel of the ideal isogeny. The quotient exists algebraically, and the complex classification identifies it with the inverse lattice transform

$$
q_\mathfrak c:A\longrightarrow A/A[\mathfrak c]
=\mathfrak c*A. \tag{4.14}
$$

The weight identity $\mathfrak c\bar{\mathfrak c}=n\mathcal O_K$ supplies the unique target polarization for which

$$
q_\mathfrak c^*\lambda_\mathfrak c=n\lambda. \tag{4.15}
$$

Because $\mathfrak b$ is prime to the level, $q_\mathfrak c$ is an isomorphism on the relevant level torsion and transports $\rho$. Thus $\mathfrak b$ defines a permutation $T_\mathfrak b$ of the finite geometric set $\mathscr C(\overline E)$. Quotients in succession give

$$
T_{\mathfrak b_1\mathfrak b_2}
=T_{\mathfrak b_1}T_{\mathfrak b_2}. \tag{4.16}
$$

For a principal ideal $(a)$, formula $R_\Phi((a))=(r_\Phi(a))$ is not a claim that the reflex ideal vanishes. Multiplication by $r_\Phi(a)$ is the actual isomorphism

$$
r_\Phi(a)*x\xrightarrow{\ \sim\ }x. \tag{4.17}
$$

It respects (4.15), because

$$
r_\Phi(a)\overline{r_\Phi(a)}=N_{E/\mathbf Q}(a), \tag{4.18}
$$

and it respects the transported level and theta frame by their definition. If $a$ is sufficiently close to $1$ at the finitely many level and frame primes, the displayed isomorphism fixes the chosen rigidification.

It follows that there is a modulus $\mathfrak m$ whose finite part is supported on a finite enlargement $S$ of $S_0$ such that the structural action factors through a finite ray class group; if the reflex datum has real places, the required sign conditions are included in the infinite part of $\mathfrak m$:

$$
\theta_\rho:\operatorname{Cl}_{\mathfrak m}(E)
\longrightarrow\operatorname{Perm}\bigl(\mathscr C(\overline E)\bigr),
\qquad [\mathfrak b]\longmapsto T_\mathfrak b. \tag{4.19}
$$

Equivalently, on ideles it is the action $x\mapsto r_\Phi(s_f)*x$, with principal ideles acting through (4.17) and the connected archimedean component acting trivially. The existence of $\mathfrak m$ is elementary: the finite level and frame see only a finite quotient of the local unit groups, and a sufficiently deep principal congruence subgroup acts trivially. At this stage (4.19) is only a finite group of explicitly constructed ideal correspondences. We have not identified it with a Galois group.

### 4.5 The clean-prime Frobenius calculation

The arithmetic bridge is a calculation on the special fibers of (4.11). Let $v\notin S$ have residue characteristic $p$ and cardinality

$$
q_v=p^d. \tag{4.20}
$$

Enlarge $S$ once and for all so that $p$ is unramified in $K$ and $E$. Put

$$
\mathfrak c_v=R_\Phi(\mathfrak p_v). \tag{4.21}
$$

Choose a geometric point of $\mathscr C_R$ above an algebraic closure of $k_v$, and denote its abelian variety by $\widetilde A$. Write

$$
F_{q_v}:\widetilde A\longrightarrow\widetilde A^{(q_v)} \tag{4.22}
$$

for relative $q_v$-power Frobenius.

**Proposition 4.3 (reflex kernel lemma).** With these hypotheses,

$$
\ker F_{q_v}=\widetilde A[\mathfrak c_v] \tag{4.23}
$$

as finite flat $\mathcal O_K$-stable subgroup schemes. Under the induced target isomorphism, the polarization, prime-to-$p$ level, and every chosen prime-to-$p$ theta frame agree. Consequently the arithmetic Frobenius permutation of the geometric special fiber is

$$
\widetilde x^{\operatorname{Frob}_v}
=\mathfrak c_v*\widetilde x. \tag{4.24}
$$

**Proof.** Work over $W=W(\overline{k}_v)$. In the contravariant convention, let

$$
M=H^1_{\mathrm{cris}}(\widetilde A/W). \tag{4.25}
$$

The order is maximal and étale at $p$. After extending Witt coefficients, its idempotents split $M$ as

$$
M=\bigoplus_{\varphi:K\hookrightarrow\overline{\mathbf Q}_p}M_\varphi,
\qquad \operatorname{rank}_W M_\varphi=1. \tag{4.26}
$$

The ranks are one because the same idempotent summands have rank one on the generic de Rham fiber of the abelian scheme, and ranks of direct summands are locally constant. Crystalline Frobenius permutes these lines by Witt Frobenius.

Modulo $p$, contravariant Dieudonné theory identifies the Hodge subspace by

$$
\omega_{\widetilde A}=\ker(F:M/pM\to M/pM). \tag{4.27}
$$

The determinant condition (4.5), which remains true on the integral model, says exactly that the idempotent lines in $\omega_{\widetilde A}$ are the $p$-adic transports of the embeddings in $\Phi$. On a rank-one summand the pullback induced by one relative $p$-Frobenius has elementary divisor either $1$ or $p$. Indeed, $FV=VF=p$ bounds the exponent by one, and (4.27) says that the exponent is one precisely on the translated type line.

Iterate through the $d$ Witt-Frobenius translates belonging to $v$. If $e_\varphi$ is the exponent of $p$ in the image of $F^d$ on the $\varphi$-summand, then

$$
e_\varphi
=\sum_{\tau:E\hookrightarrow\overline{\mathbf Q}_p\atop \tau\text{ induces }v}
m(\tau,\varphi),
\qquad
m(\tau,\varphi)=
\begin{cases}
1,&\gamma_\tau^{-1}\varphi\in\Phi,\\
0,&\gamma_\tau^{-1}\varphi\notin\Phi.
\end{cases} \tag{4.28}
$$

The inverse on $\gamma_\tau$ is the contravariant transport of the Hodge character. Formula (4.28) is also exactly the valuation formula obtained by applying the reflex-norm exponent matrix to a prime idele at $v$. Therefore

$$
\operatorname{im}(F^d\mid M)
=\bigoplus_\varphi p^{e_\varphi}M_\varphi
=\mathfrak c_v M. \tag{4.29}
$$

This is the point at which the Hodge cocharacter becomes an integral Frobenius kernel. It also fixes the variance: the type norm has the wrong source and target, while replacing $m(\tau,\varphi)$ by the direct incidence would give the conjugate or transpose kernel.

For an isogeny $u:B\to C$ with finite $p$-power kernel $G$, contravariance gives

$$
0\longrightarrow D(C[p^\infty])
\xrightarrow{u^*}D(B[p^\infty])
\longrightarrow D(G)\longrightarrow0. \tag{4.30}
$$

Thus $D(\ker F_{q_v})$ is the quotient of $M$ by the left side of (4.29). Locally at $p$, the invertible ideal $\mathfrak c_v$ has a generator whose component valuations are the same $e_\varphi$, so the identical quotient is $D(\widetilde A[\mathfrak c_v])$. Finite Dieudonné theory is an exact anti-equivalence over the perfect residue field. It follows that the two finite flat subgroup schemes are equal, proving (4.23).

The generic ideal isogeny between the two corresponding fibers of $\mathscr A$ extends uniquely over the strict henselian discrete valuation ring: abelian schemes have the extension property for homomorphisms over a normal trait. Its schematic kernel is the finite flat $\mathfrak c_v$-kernel just computed, and formation of the quotient by that kernel commutes with base change. Hence the quotient appearing in the special fiber is genuinely the specialization of the structural transform $T_{\mathfrak p_v}x$, not merely an abstract abelian variety with an isomorphic $p$-divisible group.

The quotient by a specified finite flat subgroup is unique up to a unique target isomorphism. Relative Frobenius pulls the Frobenius twist of a polarization back to its $q_v$-fold multiple; the ideal quotient does the same by

$$
\mathfrak c_v\bar{\mathfrak c}_v=q_v\mathcal O_K. \tag{4.31}
$$

Both maps are isomorphisms on prime-to-$p$ torsion, where they transport the same conjugated level and theta-group labels. Since the level is rigid, the target isomorphism has no residual automorphism. The target of (4.22) is therefore precisely the ideal transform as a rigidified PEL object. This is (4.24). $\square$

The direction in (4.24) is worth recording. With arithmetic reciprocity, residue Frobenius acts on $\overline{k}_v$ by $a\mapsto a^{q_v}$, and conjugating the coefficients of a special-fiber object by that automorphism produces the target $\widetilde A^{(q_v)}$ of relative Frobenius. Thus the calculation gives $\mathfrak c_v$, not $\mathfrak c_v^{-1}$ or $\overline{\mathfrak c}_v$. The inverse appears later only in the lattice of the ideal transform.

There is a useful generic-fiber consequence. A finite étale scheme over a strict henselian discrete valuation ring is a disjoint union of copies of the base. Hence specialization gives a bijection between its geometric generic points in a fixed unramified closure and its geometric special points. Applying this to $\mathscr C_R$ and (4.24) gives

$$
x^{\operatorname{Frob}_v}=\mathfrak c_v*x \tag{4.32}
$$

for every geometric generic point and every arithmetic Frobenius at a place over $v$. No global CM reciprocity has been used in proving (4.32): the inputs were the algebraic PEL model, its determinant condition, and finite Dieudonné theory.

### 4.6 From prime Frobenius to arbitrary Artin action

Let $L/E$ be a finite Galois extension through which the action of $G_E$ on the finite set $\mathscr C(\overline E)$ factors, and replace $L$ by the fixed field of the kernel so that

$$
G=\operatorname{Gal}(L/E)
\hookrightarrow\operatorname{Perm}\bigl(\mathscr C(\overline E)\bigr) \tag{4.33}
$$

is faithful. Enlarge $S$ to contain the primes ramified in $L$. Equation (4.32) says that, for every $v\notin S$ and every place of $L$ above it, the corresponding arithmetic Frobenius element acts as the structural permutation $T_{\mathfrak p_v}$.

We need a small generation lemma. It is weaker than the Chebotarev density theorem and follows from the zeta-function facts already available in global class field theory.

**Lemma 4.4 (Frobenius generation outside a finite set).** If $L/E$ is finite Galois, the Frobenius elements at the primes outside any finite set containing the ramified primes generate $\operatorname{Gal}(L/E)$.

**Proof.** Let $H$ be the subgroup generated by all those Frobenius elements, for all choices of primes above $v$. Conjugation merely changes the prime above $v$, so $H$ is normal. Every prime outside $S$ splits completely in $L^H/E$. If $d=[L^H:E]$, then, outside the finitely many Euler factors in $S$,

$$
\zeta_{L^H}(s)=\zeta_E(s)^d\cdot U_S(s), \tag{4.34}
$$

where $U_S(s)$ is a finite product of Euler factors holomorphic and nonzero at $s=1$. The left side has a simple pole at $1$, whereas the right side has a pole of order $d$. Hence $d=1$, so $H=G$. $\square$

All permutations $T_{\mathfrak p_v}$ lie in the abelian image of the ray action (4.19). By Lemma 4.4 they generate the faithful group $G$. Therefore $G$ itself is abelian. This is where abelianity of the field of CM moduli values is proved; it was not assumed in order to move the support of an idele or to choose an Artin symbol.

Now global reciprocity applies to the already proved abelian extension $L/E$. Enlarge the modulus $\mathfrak m$ so that both $L/E$ and the structural action (4.19) factor through $\operatorname{Cl}_{\mathfrak m}(E)$. The two homomorphisms

$$
\operatorname{Cl}_{\mathfrak m}(E)
\rightrightarrows
\operatorname{Perm}\bigl(\mathscr C(\overline E)\bigr) \tag{4.35}
$$

are the global Artin action through $L$ and the structural reflex action. They agree on every prime ideal outside $\mathfrak m$ by (4.32). Every ideal prime to $\mathfrak m$ is a product of such prime ideals, so they agree everywhere. In idelic notation,

$$
x^{\operatorname{Art}_E(s)}
=r_\Phi(s_f)*x
\qquad(s\in\mathbf A_E^\times). \tag{4.36}
$$

Here the left side means the action of any lift of the indicated element of $G_E^{\mathrm{ab}}$. The coordinates of $x$ lie in the abelian extension $L$, so the result is independent of the lift. Equation (4.36) includes ramified Artin elements and local units: their action follows from global class field theory after the clean-prime comparison has identified the two finite ray-class homomorphisms. We are not pretending that a ramified prime ideal has a canonical Frobenius.

Finally let $\sigma\in\operatorname{Aut}(\mathbf C/E)$. Proposition 4.2 puts $x$ and its universal fine-moduli object over $\overline{\mathbf Q}$. Thus $\sigma$ acts through its restriction to $G_E$, and then through $G_E^{\mathrm{ab}}$ by the abelianity just proved. If $s$ represents $\sigma|_{E^{\mathrm{ab}}}$, (4.36) gives (4.3a). This proves the moduli form of Theorem 4.1 for an arbitrary automorphism, not merely for Frobenius elements or automorphisms detected on cyclotomic coefficients.

### 4.7 Theta values, torsion, and lattices

We can now state the arithmetic theta-value consequence with the necessary coefficient qualification. Let $Y$ be a theta-framed fine moduli cover defined over $E$ by cyclotomic descent, let $x\in Y(\overline E)$ be a CM point, and let $f$ be an $E$-rational function on $Y$ regular at every point under consideration. Then (4.36) gives

$$
f(x)^\sigma=f\bigl(r_\Phi(s_f)*x\bigr) \tag{4.37}
$$

for every $\sigma\in\operatorname{Aut}(\mathbf C/E)$ and every $s$ representing $\sigma|_{E^{\mathrm{ab}}}$. In particular $f(x)\in\overline{\mathbf Q}$ and in fact lies in an abelian extension of $E$.

For a theta quotient whose coefficients lie in a cyclotomic extension $F$ rather than in $E$, the semilinear formula is

$$
f(x)^\sigma=f^\sigma\bigl(r_\Phi(s_f)*x\bigr). \tag{4.38}
$$

If $\sigma$ fixes the coefficients, this reduces to (4.37). Equivalently one may incorporate the cyclotomic change of characteristic into the finite adelic action on the theta frame. This distinction prevents an incorrect claim about a modular function whose coefficients themselves move. Also, the algebraic quantities are projective theta-null coordinates and equal-weight ratios. A raw analytic theta constant carries a period-scale factor and is not asserted to be algebraic.

We next recover the simultaneous torsion statement. Write

$$
V_f(A)=H_1(A,\mathbf Q)\otimes\mathbf A_f,
\qquad T_f(A)=H_1(A,\mathbf Z)\otimes\widehat{\mathbf Z}. \tag{4.39}
$$

The quotient $V_f(A)/T_f(A)$ is canonically the full torsion subgroup $A_{\mathrm{tors}}(\mathbf C)$. Galois acts on torsion algebraically even though (4.39) was described analytically.

Galois conjugation of algebraic torsion gives a canonical $\mathcal O\otimes\widehat{\mathbf Z}$-linear isomorphism

$$
\sigma_*:T_f(A)\xrightarrow{\sim}T_f(A^\sigma), \tag{4.40}
$$

where the integral $\mathcal O$-action on the target, and the rational $K$-action after inverting denominators, are the transported CM labeling. It is the inverse limit of $P\mapsto P^\sigma$ on $A[N]$ and therefore carries the source Tate lattice onto the target Tate lattice.

**Corollary 4.5 (torsion comparison).** Under the hypotheses of Theorem 4.1, there is a $K$-linear marking

$$
j_{\sigma,s}:H_1(A^\sigma,\mathbf Q)\xrightarrow{\sim}K \tag{4.41}
$$

such that, after tensoring with $\mathbf A_f$,

$$
(j_{\sigma,s}\otimes1)\bigl(\sigma_*x\bigr)
=r_\Phi(s_f)^{-1}x
\qquad(x\in\widehat{\mathfrak a}). \tag{4.42}
$$

In particular,

$$
(j_{\sigma,s}\otimes1)T_f(A^\sigma)
=r_\Phi(s_f)^{-1}\widehat{\mathfrak a}. \tag{4.43}
$$

This is a well-typed assertion about Tate lattices. On torsion quotients it gives the commutative diagram

$$
\begin{array}{ccc}
(K\otimes\mathbf A_f)/\widehat{\mathfrak a}
&\xrightarrow{\ x\mapsto r_\Phi(s_f)^{-1}x\ }&
(K\otimes\mathbf A_f)/(r_\Phi(s_f)^{-1}\widehat{\mathfrak a})\\
\downarrow\wr&&\downarrow\wr\\
A_{\mathrm{tors}}(\mathbf C)&\xrightarrow{\ P\mapsto P^\sigma\ }&
A^\sigma_{\mathrm{tors}}(\mathbf C).
\end{array} \tag{4.44}
$$

**Proof.** For each $M$ divisible by the fixed rigidifying level $N$, equip $A$ with the level-$M$ structure induced by the chosen adelic marking. There is no prime-to-bad restriction here: over characteristic zero, the sheaf of full $\mathbf Z/M\mathbf Z$-linear frames of $A[M]$ is a finite étale cover of the already fine CM scheme. When proving reciprocity for that cover, one merely adds the primes dividing $M$ to its clean spreading set; infinitely many other primes remain for Lemma 4.4.

Apply (4.36) to this enhanced point. It identifies its Galois conjugate with the level transported by multiplication with $r_\Phi(s_f)^{-1}$. The underlying isomorphisms for different $M$ agree after forgetting to level $N$, because an isomorphism preserving full level $N\geq3$ is unique. Passing through the cofinal system of $M$ gives (4.42) on every finite torsion group and hence on the inverse limit. The analytic uniformization of the target ideal transform gives the marking (4.41), and (4.43)--(4.44) follow. $\square$

The assertion is simultaneous over all primes. A family of unrelated $\ell$-adic comparisons could differ by rational $K^\times$-scalars. Compatibility through one tower of fine levels and the principal-idele isomorphism (4.17) remove that ambiguity.

The torsion itself remembers the commensurability class of the lattice. If $V$ is a finite-dimensional rational vector space and $\Lambda\subset V$ a full lattice, then

$$
V/\Lambda=\varinjlim_N N^{-1}\Lambda/\Lambda. \tag{4.45}
$$

Conversely, the kernels of multiplication by $N$ together with their transition maps recover $\Lambda\otimes\widehat{\mathbf Z}$ inside $V\otimes\mathbf A_f$. This explains why the compatible finite-level calculation recovers the finite adelic lattice rather than merely its local isomorphism class.

#### Analytic theta compatibility

The preceding proof is complete without analytic theta transformation. It is nevertheless useful to check that the algebraic action agrees with the classical analytic formulas and that no hidden transpose has entered the reflex norm.

Choose an integer $N\geq3$ divisible by none of the primes at which the order or polarization data are defective. A symplectic basis of $A[N]$ gives a point $x$ of the fine moduli scheme $\mathcal A_{g,d,N}$ of polarized abelian varieties of fixed degree with full level $N$. A component with a selected Weil-pairing value is defined over the corresponding cyclotomic field; the union with its cyclotomic descent is the similitude-level scheme used in Section 4.2.

To use theta functions without claiming that a theta characteristic is intrinsic to this moduli problem, pass to the finite theta-framed cover $Y\to\mathcal A_{g,d,N}$: a point of $Y$ also chooses an isomorphism of the theta group of a sufficiently high symmetric power of the polarization with the standard finite Heisenberg group. The finite change-of-frame group $\Delta$ acts on $Y$, and $\mathcal A_{g,d,N}=Y/\Delta$ because the original level has trivial inertia. On $Y$, theta constants give a projective embedding; equal-weight quotients of homogeneous polynomials in them generate its function field. A rational function on $\mathcal A_{g,d,N}$ pulls back to a $\Delta$-invariant such quotient, and conversely a $\Delta$-invariant quotient descends. Thus it is enough to calculate on $Y$ and then take invariants. This is the precise role of theta coordinates below.

On the analytic uniformization of $Y$, the relevant functions are quotients of theta constants of a common weight and level. We need two transformation facts.

1. If a rational symplectic similitude $u$ carries one polarized lattice to another, substitution in the theta series carries the associated moduli value to the value at the transformed lattice. The finite residue of $u$ records its action on level.
2. If $a\in E^\times$ is principal, the finite transformation attached to $r_\Phi(a)$ is the analytic change of $K$-basis induced by the same principal element. After descending from the theta frame, these are two presentations of the same polarized level object. Consequently the action on every algebraic moduli value is trivial. The product formula is what cancels the scalar automorphy factors in the theta-framed calculation.

For completeness, the decisive cancellation can be seen term by term. A theta series has the form

$$
\vartheta_m(z,\tau)=
\sum_{n\in\mathbf Z^g}
\exp\!\left(\pi i(n+m_1)^t\tau(n+m_1)
+2\pi i(n+m_1)^t(z+m_2)\right). \tag{4.46}
$$

A change of symplectic lattice multiplies it by a determinant square root and a root of unity depending only on the level characteristic $m$. In a quotient of equal total weight the determinant factors cancel. The remaining roots of unity are acted on by the cyclotomic component of Artin reciprocity; local reciprocity sends a unit to exactly the inverse change of the level characteristic. For a principal $a$, the product of these local root-of-unity factors is $1$. The exponent matrix governing the change of the CM lattice is the Galois orbit of the Hodge cocharacter. By the defining identity

$$
(r_\Phi)_*[\iota_E]=\mu_\Phi, \tag{4.47}
$$

that exponent matrix is precisely the reflex norm, with no type norm and no transpose.

Here is a derivation of the transformation facts. The integral symplectic group is generated by matrices of the three forms

$$
\begin{pmatrix}U&0\\0&U^{-t}\end{pmatrix},
\qquad
\begin{pmatrix}1&B\\0&1\end{pmatrix},
\qquad
\begin{pmatrix}0&-1\\1&0\end{pmatrix},
$$

where $U\in\operatorname{GL}_g(\mathbf Z)$ and $B$ is integral symmetric. For the first generator, reindex the theta sum by $n\mapsto U^{-1}n$; this changes only the characteristic. For the second, expand the new quadratic term. Its integral part contributes $1$, and its half-integral part contributes a root of unity determined by the characteristic modulo the level. For the third, apply Poisson summation to the Gaussian

$$
x\longmapsto
\exp\!\left(\pi i x^t\tau x+2\pi i x^tz\right).
$$

Its Fourier transform is

$$
\det(-i\tau)^{-1/2}
\exp\!\left(-\pi i(y-z)^t\tau^{-1}(y-z)\right),
$$

with the square root selected continuously on Siegel space. Summing over $y\in\mathbf Z^g$ gives the determinant factor and exchanges the two halves of the characteristic. This proves the integral transformation formula on generators.

A rational symplectic similitude becomes integral after clearing a denominator. Factor the resulting lattice correspondence into an integral change of basis and finite inclusions of lattices. Decomposing the original theta sum into residue classes modulo those indices proves the distribution relation in both directions. Thus the only scalar factors are determinant powers and roots of unity. In a quotient of equal weight the determinant powers cancel. For a $\Delta$-invariant rational moduli function, the product of characteristic multipliers depends only on the induced finite-level torsion action. Arithmetic local reciprocity gives the inverse cyclotomic action on those characteristics. For a principal idele the global product formula makes their product $1$, while multiplication by $r_\Phi(a)$ supplies the actual isomorphism of lattice presentations. This proves the two transformation facts without assuming the CM orbit formula.

The arithmetic CM value identity is (4.37), already proved from the finite étale CM locus and the Frobenius calculation. The analytic calculation above verifies that its right side is represented by the classical theta transformation, including the cyclotomic action on characteristics and the principal-idele cancellation. It does **not** by itself identify the left side for an arbitrary $\sigma$: a theta transformation law sees a change of analytic lattice and finitely many roots of unity, but it does not prove that the CM point is algebraic or that the commutator subgroup of $G_E$ fixes its coordinates. Proposition 4.2, Proposition 4.3, and Lemma 4.4 supply exactly those missing arithmetic facts.

We expand the exponent calculation, since this is where the reflex norm rather than the type norm enters. Work in a finite Galois extension $L/\mathbf Q$ containing $K$ and $E$. If $\tau:E\hookrightarrow L$ and $\varphi:K\hookrightarrow L$, the exponent with which the $\tau$-component of $s$ changes the $\varphi$-component of the CM lattice is

$$
m(\tau,\varphi)=
\begin{cases}
1,&\gamma_\tau^{-1}\varphi\in\Phi,\\
0,&\gamma_\tau^{-1}\varphi\notin\Phi,
\end{cases} \tag{4.48}
$$

where $\gamma_\tau|_E=\tau$. Consequently

$$
\varphi(r_\Phi(s))
=\prod_{\tau:E\hookrightarrow L}\tau(s)^{m(\tau,\varphi)}. \tag{4.49}
$$

The inverse on $\gamma_\tau$ in (4.48) is forced by transporting a coordinate function contravariantly. In the primitive Galois case it changes the type set $S$ into $S^{-1}$. Multiplying the original type embeddings instead would give $N_\Phi:K^\times\to E^\times$, which cannot act on the $K$-lattice at all. Formula (4.49) therefore checks both the direction and the inverse incidence. It is the same exponent matrix that appeared integrally in (4.28), so the analytic and crystalline calculations meet at the definition of the reflex norm rather than borrowing conclusions from one another.

#### Passage from torsion to lattices

We finish the homological formulation of Theorem 4.1 from Corollary 4.5. A full lattice in a rational vector space is recovered from all of its finite completions:

$$
\mathfrak a=K\cap\widehat{\mathfrak a}
\quad\text{inside }K\otimes\mathbf A_f. \tag{4.50}
$$

Indeed, membership in a fractional ideal is the collection of its lower valuation bounds at all finite primes. Equation (4.43) therefore determines the target integral homology lattice uniquely. It is

$$
\mathfrak a^\sigma
=K\cap r_\Phi(s_f)^{-1}\widehat{\mathfrak a}. \tag{4.51}
$$

The right side is the fractional ideal represented adelically by $r_\Phi(s_f)^{-1}\widehat{\mathfrak a}$, so it is exactly the inverse ideal transform. The analytic classification of CM abelian varieties then turns equality of lattices into the algebraic isomorphism (4.3). Together with the fine-moduli identity (4.3a), this completes the proof of Theorem 4.1 in its homological, level, endomorphism, and polarized forms.

### 4.8 Idele independence and the descent cocycle

Suppose $s'$ has the same image as $s$ in $G_E^{\mathrm{ab}}$. Global reciprocity says that $s's^{-1}$ lies in $E^\times E_\infty^{\times,0}$. Write it as $az$ with $a\in E^\times$ and $z$ in the connected archimedean component. Its finite component is the principal idele $a$. Multiplication by $r_\Phi(a)$ therefore compares the two transformed lattice presentations. At a fixed finite level one may instead quotient by the larger open stabilizer $U_x$; that changes the Galois element by an element fixing the rigidified point, not merely by an element in the kernel of the full Artin map.

If $s$ is replaced by $as$ with $a\in E^\times$, then

$$
r_\Phi(as_f)=r_\Phi(a)r_\Phi(s_f). \tag{4.52}
$$

Multiplication by $r_\Phi(a)$ identifies the two lattice presentations, since one target lattice is $r_\Phi(a)^{-1}$ times the other. Thus principal ideles change the comparison isomorphism, not the resulting isomorphism class.

For $\sigma,\tau\in G_E^{\mathrm{ab}}$ represented by $s,t$, multiplicativity of Artin, the reflex norm, and the ideal action gives

$$
r_\Phi(st)*(A)=r_\Phi(s)*(r_\Phi(t)*A). \tag{4.53}
$$

With the base-change convention (1.7), both composites from $x^{\tau\sigma}$ to the transform indexed by $st$ preserve the full level. They are therefore equal, because the target has no automorphisms preserving level $N\geq3$. Thus the comparison isomorphisms satisfy the descent cocycle as actual morphisms, not merely in a set of isomorphism classes.

This also explains the logical order of canonical descent. The finite étale scheme $\mathscr C/E$ is the canonical algebraic model of the *set of rigidified CM points*. Equation (4.36) identifies its arithmetic Galois action. For the field fixed by the stabilizer of one point, the unique fine-level comparison isomorphisms give a cocycle. Effective fpqc descent then descends the universal fiber, its group law, the $\mathcal O$-action, polarization homomorphism, and finite level. Before rigidification the comparisons can differ by an automorphism of the CM object; that is the field-of-moduli obstruction, not a failure of reciprocity.

### 4.9 Polarized and order-valued forms

Assume $(A,\iota,\lambda)$ is represented by $(\mathfrak a,\xi)$. For an integral ideal $\mathfrak b$ of $E$ away from the bad set, put

$$
\mathfrak c=R_\Phi(\mathfrak b),
\qquad n=N_{E/\mathbf Q}(\mathfrak b). \tag{4.54}
$$

Then the comparison sends the polarized datum to

$$
(\mathfrak c^{-1}\mathfrak a,n\xi). \tag{4.55}
$$

Equation (2.15) proves that the polarization type is unchanged. The canonical isogeny has degree

$$
N_{K/\mathbf Q}(\mathfrak c)=n^g \tag{4.56}
$$

and pulls the new polarization back to $n\lambda$. The equality of degrees

$$
(n^g)^2=n^{2g}=\deg[n]_A \tag{4.57}
$$

is a useful check on the conjugate factor in the reflex norm.

For a nonmaximal order, the same statement holds away from its conductor with proper invertible ideals. At conductor primes the rational theorem (4.2) remains meaningful, but an assertion about integral ideal actions requires a separate local lattice calculation. Reciprocity never repairs noninvertibility.

There is also a useful representation-theoretic form. Fix a model over a number field $L\supset E$ on which the CM action is defined, a prime $\ell$, and a $K\otimes\mathbf Q_\ell$-basis of $V_\ell(A)$. Galois acts through a character

$$
\rho_\ell:G_L\longrightarrow(K\otimes\mathbf Q_\ell)^\times. \tag{4.58}
$$

If $\gamma\in G_L$ is represented, after norm to $E$, by an idele $s$, the comparison theorem says that $\rho_\ell(\gamma)$ differs from $r_\Phi(s_f)^{-1}$ by the principal $K^\times$ factor used to identify the transformed CM datum with the chosen model. That principal correction is essential: the orbit formula determines an isomorphism class, while $\rho_\ell$ depends on a specific descended model and basis. It is also the source of the algebraic Hecke character attached to $A$. Suppressing it would incorrectly make every local unit preserving the lattice act trivially on the Tate module.

## 5. Galois orbits and class fields

The comparison theorem turns the orbit of a CM point into a quotient of an idele class group. The quotient depends on exactly which data are remembered. Forgetting a level structure enlarges the stabilizer; forgetting a CM labeling can enlarge it again by allowing automorphisms of the CM field.

### 5.1 The stabilizer of a CM datum

Let $x=(A,\iota,\lambda,\eta)$ be a polarized CM datum of type $(K,\Phi)$ with a chosen level structure. Define

$$
U_x=\{s\in\mathbf A_E^\times:
r_\Phi(s_f)*x\simeq x\}. \tag{5.1}
$$

The isomorphism in (5.1) is required to preserve every displayed datum. Because the archimedean connected component acts trivially on the finite lattice, $E^\times E_{\infty}^{\times,0}\subset U_x$. At almost every finite prime the maximal unit subgroup also lies in $U_x$. At primes dividing the level, $U_x$ contains a principal congruence subgroup. Hence $U_x/E^\times$ is an open subgroup of finite index in $C_E$.

For an unpolarized maximal-order object with no level, the stabilizer has the concrete form

$$
U_A=
\{s:r_\Phi(s_f)\in K^\times\widehat{\mathcal O}_K^\times\}. \tag{5.2}
$$

For a polarized object, a principal factor $u\in K^\times$ must also preserve the polarization, so its norm $u\bar u$ must match the reflex similitude multiplier. For full level $N$, the remaining integral unit must satisfy the prescribed congruence modulo $N$. These conditions explain why a single phrase such as “the CM class field” is ambiguous until the moduli datum is specified.

### 5.2 The class field of a rigidified CM point

Global class field theory associates to $U_x$ a finite abelian extension $H_x/E$ characterized by

$$
\operatorname{Gal}(H_x/E)
\simeq C_E/(U_x/E^\times). \tag{5.3}
$$

Theorem 4.1 says that the Galois stabilizer of $x$ is precisely the Artin image of $U_x$. Therefore the coordinates of the rigidified CM point lie in $H_x$, and every conjugate over $E$ is obtained by a reflex ideal transform.

**Theorem 5.1.** If the level is fine enough that $x$ has no nontrivial automorphisms, then $H_x$ is the field of moduli relative to $E$ and a field of definition of $x$. Moreover, for $s\in\mathbf A_E^\times$,

$$
x^{\operatorname{Art}_E(s)}=r_\Phi(s_f)*x. \tag{5.4}
$$

**Proof.** By Theorem 4.1, an Artin element fixes $x$ if and only if its representing idele belongs to $U_x$. Thus the fixed field of the Galois stabilizer is (5.3). The comparison isomorphisms satisfy the cocycle law by (4.53). Since the automorphism group is trivial, equality up to automorphism is equality, and effective fpqc descent applies to the universal fine-moduli object. Formula (5.4) is the descended form of (4.3). $\square$

### 5.3 Orbit and degree formulas

The orbit of $x$ is a torsor under the finite quotient in (5.3), provided the action is faithful by definition of $U_x$. Hence

$$
[H_x:E]=[C_E:U_x/E^\times]. \tag{5.5}
$$

At level prime to the bad set this quotient may be computed in a ray class group. Let $U(\mathfrak m)$ be the standard congruence subgroup for a modulus $\mathfrak m$ divisible by the level and bad primes. If

$$
E^\times U(\mathfrak m)\subseteq U_x, \tag{5.6}
$$

then $H_x$ is contained in the ray class field of modulus $\mathfrak m$. It is usually a proper subfield: the kernel of the reflex norm and automorphisms of the datum enlarge $U_x$.

The equality (5.5) is safer than a blanket class-number formula. It automatically handles degenerate CM types, nontrivial units, polarization conditions, and level. A numerical formula obtained by dividing a ray class number must account for all of those stabilizers.

### 5.4 Ring class fields in dimension one

Let $K$ be imaginary quadratic, let $\mathcal O\subset K$ be an order of conductor $f$, and let $A$ have endomorphism ring exactly $\mathcal O$. Here $E=K$ and $r_\Phi$ is the identity. Proper invertible $\mathcal O$-ideal classes act simply transitively on complex elliptic curves with endomorphism ring $\mathcal O$. The stabilizer consists of principal ideles times $\widehat{\mathcal O}^\times$, so

$$
\operatorname{Gal}(H_\mathcal O/K)
\simeq K^\times\backslash\mathbf A_{K,f}^\times/\widehat{\mathcal O}^\times
\simeq\operatorname{Pic}(\mathcal O). \tag{5.7}
$$

The field $H_\mathcal O$ is the ring class field. If $j(A)$ is the $j$-invariant, then

$$
j(A)^{\operatorname{Art}_K(s)}=j(s*A). \tag{5.8}
$$

For a prime ideal $\mathfrak p$ prime to $f$, this becomes

$$
j(\mathfrak a)^{\operatorname{Frob}_\mathfrak p}
=j(\mathfrak p^{-1}\mathfrak a). \tag{5.9}
$$

The exceptional units for discriminants $-3$ and $-4$ do not change the unlabelled $j$-orbit, but they matter for rigidified level and for descent of a chosen differential. Full level $N\geq3$ removes them.

As a small class-field calculation, take $K=\mathbf Q(\sqrt{-5})$ and $\mathcal O=\mathcal O_K=\mathbf Z[\sqrt{-5}]$. Minkowski's bound for an imaginary quadratic field says that every ideal class contains an integral ideal of norm at most

$$
\frac{2}{\pi}\sqrt{20}<3. \tag{5.10}
$$

Thus every class is represented by the unit ideal or an ideal of norm $2$. There is one prime

$$
\mathfrak p=(2,1+\sqrt{-5})
$$

of norm $2$. It is not principal, because the norm equation

$$
a^2+5b^2=2
$$

has no integral solution. Since $2$ ramifies, $\mathfrak p^2=(2)$, and therefore

$$
\operatorname{Pic}(\mathcal O_K)\simeq\mathbf Z/2\mathbf Z. \tag{5.11}
$$

There are exactly two unlevelled CM elliptic curves with this labeled endomorphism ring, up to complex isomorphism, and their $j$-invariants are conjugate over a quadratic extension of $K$. At every prime ideal $\mathfrak q$ in the nontrivial ideal class and away from the discriminant, arithmetic Frobenius interchanges them by

$$
\mathfrak a\longmapsto\mathfrak q^{-1}\mathfrak a. \tag{5.12}
$$

Because the class has order two, inverse and direct ideal classes happen to agree in this example. It therefore illustrates the orbit theorem but cannot detect the reciprocity inverse; a class group with an element of order greater than two is needed for that test.

### 5.5 Why the reflex class group need not act faithfully

The reflex norm can have a nontrivial kernel on ideal classes. If $R_\Phi(\mathfrak b)$ is principal, its ideal transform is isomorphic to the original unpolarized CM variety. Even when the ideal is not principal, it may preserve a polarized isomorphism class because of an automorphism or a rational similitude. Thus the orbit is not generally the whole ideal class group of $E$.

At the torus level, the image of $r_\Phi$ is the Mumford--Tate torus, not usually all of $\operatorname{Res}_{K/\mathbf Q}\mathbf G_m$. Degeneracy of the type produces a positive-dimensional kernel of tori; at finite level this can produce extra stabilizer classes. The correct statement is always the quotient by (5.1).

## 6. Effective descent and canonical models

Knowing every Galois conjugate is not yet the same as constructing an object over the fixed field. Descent requires compatible isomorphisms, and automorphisms can obstruct their compatibility. CM reciprocity supplies the isomorphisms; sufficiently fine level makes them unique.

### 6.1 Field of moduli versus field of definition

For an object $x$ over $\overline E$, its field of moduli relative to $E$ is the fixed field of

$$
\{\sigma:x^\sigma\simeq x\}. \tag{6.1}
$$

This definition records isomorphism classes only. To descend $x$ to a field $H$, one needs isomorphisms

$$
\varphi_\sigma:x^\sigma\xrightarrow{\sim}x
\qquad(\sigma\in G_H) \tag{6.2}
$$

satisfying

$$
\varphi_{\tau\sigma}
=\varphi_\tau\circ(\varphi_\sigma)^\tau. \tag{6.3}
$$

If $x$ has automorphisms, arbitrary choices in (6.2) can fail (6.3) by a two-cocycle valued in $\operatorname{Aut}(x)$. Thus “the moduli point is fixed” does not by itself descend a chosen abelian variety, polarization, CM action, or line bundle.

### 6.2 Rigidification kills the descent obstruction

Let $N\geq3$ and include a full level-$N$ structure in $x$. Any automorphism preserving the polarization, CM action, and level is the identity. Therefore an isomorphism $x^\sigma\simeq x$, if it exists, is unique. Both sides of (6.3) are then isomorphisms between the same rigidified objects, so they agree automatically.

This proves a general principle.

**Proposition 6.1.** A rigidified polarized CM datum with trivial automorphism group descends effectively to its field of moduli.

**Proof.** Choose the unique isomorphism (6.2) for each $\sigma$ in the stabilizer. Uniqueness gives (6.3). After passing to a finite Galois extension containing the coefficients of the datum, this is a finite fpqc descent datum. Effective fpqc descent for abelian schemes descends the abelian variety together with its identity section, multiplication, inverse, and group law; their identities can be checked after the faithfully flat base change. The dual abelian scheme and the polarization homomorphism descend functorially. Each element of the finitely generated order action and each finite level morphism descends by full faithfulness, and their relations again descend because they hold after base change. Thus the whole rigidified PEL object, not only its coarse point, descends. $\square$

The descended polarization is the homomorphism $A\to A^\vee$. A particular ample line bundle inducing it can have a separate scalar descent issue; polarized moduli do not require that line bundle as part of the datum.

### 6.3 The canonical descent datum

Let $H_x/E$ be the class field of Section 5. For $\sigma\in G_{H_x}$, choose an idele $s_\sigma$ mapping to its abelianized restriction. Membership in the stabilizer gives a unique isomorphism

$$
\varphi_\sigma:r_\Phi(s_{\sigma,f})*x\xrightarrow{\sim}x. \tag{6.4}
$$

Compose this with the reciprocity comparison $x^\sigma\simeq r_\Phi(s_{\sigma,f})*x$. The result is independent of the idele choice and obeys (6.3). This is the **canonical CM descent datum**.

There is an equivalent moduli description that makes effectivity completely transparent. Section 4 constructs the finite étale fine CM scheme $\mathscr C/E$ and proves that the residue field of $x$ is the abelian field fixed by its Artin stabilizer, namely $H_x$. Hence $x$ is an $H_x$-rational point of $\mathscr C$, and the desired canonical model is the pullback of the universal PEL abelian scheme along

$$
\operatorname{Spec}H_x\xrightarrow{x}\mathscr C. \tag{6.4a}
$$

The cocycle construction above is the Galois-descent presentation of this same pullback. Thus no canonical model of a zero-dimensional Shimura variety has been assumed: the required model was built as an algebraic fine moduli scheme, its arithmetic action was proved by specialization, and the universal family supplies the descended object.

The adjective “canonical” is relative to the chosen Artin normalization, type convention, and moduli data. Switching to geometric reciprocity inverts the idele action. Switching from homology to cohomology inverts the Hodge cocharacter. Forgetting level can reintroduce automorphisms. A statement that suppresses all three choices is not genuinely canonical.

### 6.4 Forgetting level and polarization

Suppose $x_N$ is a fine-level object over $H_N$. Forgetting level gives an object $x$ whose field of moduli $H$ is contained in $H_N$. The finite group of deck transformations acts on $x_N$, and descent along $H_N/H$ is controlled by that action. The coarse moduli point descends to $H$ automatically, but a representative abelian variety may require a further finite extension.

For a principally polarized abelian variety, the automorphism group is finite. Thus the obstruction is finite and disappears after a finite extension. In many CM applications one keeps an auxiliary level throughout a construction and forgets it only after passing to a coarse canonical model. This is not cosmetic: it is the clean way to separate the canonical point from the choice of a universal family.

Forgetting the polarization enlarges the automorphism group and can shrink the field of moduli. Forgetting the CM labeling permits Galois to conjugate the embedding $K\hookrightarrow\operatorname{End}^0(A)$, so the relevant stabilizer can be larger than $G_E$. These fields should never be identified without checking what the moduli problem remembers.

### 6.5 Endomorphisms and fields of definition

Let $A/H$ be a descended CM abelian variety. An endomorphism $u\in\operatorname{End}(A_{\overline H})$ is defined over $H$ exactly when it is fixed by $G_H$. Reciprocity describes this action. If the CM labeling is part of the descended datum, then every $a\in\mathcal O$ is fixed, so the full order action is defined over $H$. If only the unlabelled variety descends, Galois may act on $\mathcal O$ through automorphisms of $K$.

There is always a finite extension over which all geometric endomorphisms are defined, because the endomorphism group is finitely generated and the continuous Galois action on it has finite image. But neither the reflex field nor the unlevelled field of moduli necessarily has this property. The class field $H_x$ does when the labeled action belongs to the rigidified datum.

## 7. CM points in ambient Shimura data

The classical theorem concerns an abelian variety with CM. Applications place that variety inside a PEL moduli problem or a Shimura variety. The passage is functorial: the CM torus maps into an ambient reductive group, and the reflex reciprocity map is obtained by composing the toric reflex norm with that embedding.

### 7.1 The torus attached to a CM point

Let $V$ be the rational homology of a polarized CM abelian variety. Multiplication by $K$ gives a torus

$$
T_K=\operatorname{Res}_{K/\mathbf Q}\mathbf G_m
$$

acting on $V$. Polarization restricts this to the unitary similitude torus

$$
T=\{a\in T_K:a\bar a\in\mathbf G_m\}. \tag{7.1}
$$

The Hodge structure is a morphism from the Deligne torus to $T_\mathbf R$; its cocharacter is $\mu_\Phi$. The Mumford--Tate torus $M_\Phi$ is the image of $r_\Phi$ and is contained in $T$ by the weight identity.

An ambient PEL datum supplies a reductive group $G$ of similitudes and an embedding

$$
j:T\hookrightarrow G. \tag{7.2}
$$

The CM point is represented analytically by the Hodge morphism together with a finite adelic coordinate $g\in G(\mathbf A_f)$.

### 7.2 Reciprocity after an ambient embedding

The reciprocity morphism attached to the CM point is

$$
r_x:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m
\xrightarrow{r_\Phi}T_K
\longrightarrow T
\xrightarrow{j}G. \tag{7.3}
$$

The middle factorization through $T$ follows from (2.11). If the ambient group remembers an exact symplectic form rather than a similitude class, one restricts the source to the norm-one subgroup appropriate to the moduli problem.

For $s\in\mathbf A_{E,f}^\times$, arithmetic reciprocity acts by

$$
[h,g]^{\operatorname{Art}_E(s)}
=[h,r_x(s)g]. \tag{7.4}
$$

Here the placement on the left of $g$ follows the left ideal action used throughout. An ambient convention using right double cosets may rewrite (7.4) as multiplication by $r_x(s)^{-1}$ on the right. These are the same formula after changing the quotient convention; combining the left formula with a right-coset convention without inversion would be an error.

**Proof.** The point $[h,g]$ represents the same rational Hodge structure as the CM abelian variety, while $g$ records its integral lattice and level. Theorem 4.1 sends that lattice to $r_\Phi(s)^{-1}$ times itself. In a left-quotient presentation this is represented by $r_x(s)g$. The polarization multiplier is correct by (2.11), so the transformed datum remains in the same PEL problem. $\square$

### 7.3 Double cosets and level

Let $C\subset G(\mathbf A_f)$ be a compact open subgroup. A zero-dimensional CM orbit is described by

$$
T(\mathbf Q)\backslash T(\mathbf A_f)/C_T,
\qquad C_T=T(\mathbf A_f)\cap gCg^{-1}. \tag{7.5}
$$

The stabilizer in $C_E$ is the inverse image under $r_x$ of $T(\mathbf Q)C_T$. Thus its field is the abelian extension corresponding to

$$
E^\times\backslash r_x^{-1}(T(\mathbf Q)C_T). \tag{7.6}
$$

Neatness of $C$ eliminates torsion in arithmetic stabilizers and makes the moduli problem fine. Without neatness, (7.5) still describes geometric points, but universal objects and effective descent require stack language or an auxiliary neat cover.

### 7.4 Hilbert, quaternionic, and unitary realizations

In a Hilbert modular realization, $G$ is built from $\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2$ and a CM quadratic extension $K/F$ embeds as a maximal torus. The determinant of multiplication by $a\in K^\times$ is $a\bar a=N_{K/F}(a)$, matching the polarization similitude.

For a quaternionic realization, an embedding $K\hookrightarrow B$ into a quaternion algebra identifies $K^\times$ with a maximal torus in $B^\times$. Such an embedding exists only when no place at which $B$ ramifies splits in $K$. The reciprocity law for the corresponding CM point is still (7.4); the quaternion algebra changes the ambient double coset and level stabilizer, not the reflex norm.

For a unitary realization, the CM algebra may be a product and the polarization is Hermitian. The determinant condition fixes the multiplicities of embeddings on the Lie algebra. Reflex norms and weight identities are taken componentwise, and the scalar multiplier must agree across the components used by the common similitude group. Failure of that common multiplier means the proposed torus does not map to the chosen PEL group.

These statements identify the CM points inside the selected data. The construction of the ambient Shimura varieties, their canonical models, and their integral models is a separate geometric task; no such later construction is used to prove Theorem 4.1.

### 7.5 Functoriality

Suppose $f:G\to G'$ carries one PEL datum to another and sends the CM point $x$ to $x'$. Then

$$
r_{x'}=f\circ r_x. \tag{7.7}
$$

Applying $f$ to (7.4) proves reciprocity for $x'$. Similarly, if a type is induced from a subfield, the norm compatibility of reflex morphisms makes the Galois actions commute with the corresponding isogeny decomposition. These functorialities are useful safeguards: reciprocity for a product, a restriction of scalars, or an inner-form realization is not a new sign choice.

## 8. Potential good reduction

Complex multiplication severely restricts monodromy. Once all CM endomorphisms are defined, the Tate module has rank one over a commutative semisimple algebra. Semistable unipotent inertia cannot act nontrivially inside such an algebra. This yields potential good reduction at every finite place.

### 8.1 Why CM forbids persistent monodromy

Let $A/L$ be a CM abelian variety over a number field, and enlarge $L$ so that the full order $\mathcal O\subset K$ acts over $L$. Choose a rational prime $\ell$ not equal to the residue characteristic at a finite place $w$ and not dividing the conductor of $\mathcal O$. Then

$$
V_\ell(A)=T_\ell(A)\otimes\mathbf Q_\ell
$$

is a free rank-one module over

$$
K\otimes\mathbf Q_\ell. \tag{8.1}
$$

Because the endomorphisms are defined over $L$, Galois commutes with $K$, so

$$
\rho_\ell:G_L\longrightarrow
(K\otimes\mathbf Q_\ell)^\times. \tag{8.2}
$$

The algebra $K\otimes\mathbf Q_\ell$ is a product of finite separable field extensions. Multiplication by any of its elements is semisimple after extending scalars to an algebraic closure. The only element that is both semisimple and unipotent is $1$.

### 8.2 The potential-good-reduction theorem

**Theorem 8.1.** Every abelian variety with complex multiplication over a number field has potentially good reduction at every finite place.

**Proof strategy.** First obtain semistable reduction after a finite extension. Semistable reduction makes inertia unipotent on a prime-to-residue-characteristic Tate module. The CM action makes the same inertia operators semisimple. They must therefore be trivial, and the good-reduction criterion finishes the proof.

**Proof.** Fix a finite place $w$ of $L$. The potential semistable-reduction theorem proved earlier gives a finite extension $L'/L$ over which $A$ has semistable reduction at a place $w'$ above $w$; enlarge it once more so that all CM endomorphisms are defined. The semistable criterion makes inertia unipotent on $V_\ell(A)$ for $\ell$ different from the residue characteristic. By (8.2) it is also multiplication by elements of the étale algebra $K\otimes\mathbf Q_\ell$, hence semisimple. Therefore inertia acts trivially. The previously proved Néron--Ogg--Shafarevich criterion says that an abelian variety has good reduction precisely when inertia acts trivially on one such Tate module. Thus $A$ has good reduction over $L'_{w'}$. $\square$

The theorem is potential, not absolute. CM elliptic curves can have additive reduction over a small field even though they acquire good reduction after a finite extension. Complex multiplication eliminates the toric part after extension; it does not assert that the original model was already smooth.

### 8.3 A criterion for good reduction over the given field

Let $A/L$ have all its CM endomorphisms defined over $L$, let $w\nmid\ell$, and let

$$
\rho_{\ell,w}:G_{L_w}\to(K\otimes\mathbf Q_\ell)^\times \tag{8.3}
$$

be the local representation. Then

$$
A\text{ has good reduction at }w
\Longleftrightarrow
\rho_{\ell,w}(I_w)=1. \tag{8.4}
$$

When $A$ is a canonical CM object covered by Theorem 4.1, local-global reciprocity gives a more explicit version of (8.4), but a principal correction must be retained. Assume here that $L\supset E$, and let $v$ be the place of $E$ below $w$. For $u\in\mathcal O_{L_w}^\times$, form $N_{L_w/E_v}(u)$ and its reflex image. Since $u$ lies in inertia, the associated ideal transform fixes the isomorphism class of the descended CM object. Choose the unique principal factor $a(u)\in K^\times$ compatible with the rigidification. In a fixed CM basis the inertia character is

$$
\psi_w(u)
=a(u)\,r_\Phi(N_{L_w/E_v}u)_\ell^{-1}
\in(K\otimes\mathbf Q_\ell)^\times. \tag{8.5}
$$

The uniqueness is literal with fine level; without it, $a(u)$ is determined only up to a finite CM automorphism. Formula (8.5) is multiplicative because the descent comparisons obey the cocycle law.

The good-reduction criterion is therefore

$$
A\text{ has good reduction at }w
\Longleftrightarrow
\psi_w(\mathcal O_{L_w}^\times)=1. \tag{8.6}
$$

It would be wrong to replace (8.6) by the statement that the reflex image merely preserves the lattice. Every integral unit preserves the lattice as a set, but it can act nontrivially on its Tate module. Good reduction asks for trivial inertia, not just invariance of an isomorphism class.

Put $U_w^0=\mathcal O_{L_w}^\times$ and $U_w^n=1+\mathfrak m_w^n$ for $n\geq1$. The least $n\geq0$ for which $\psi_w$ is trivial on $U_w^n$ is its local conductor exponent. It is zero exactly when the character is unramified, hence exactly when $A$ has good reduction under the standing CM hypotheses. This turns the geometric criterion into the same unit-filtration language used by local class field theory.

### 8.4 Integral CM data and excluded primes

Assume the order is maximal at the residue characteristic $p$, the polarization degree and level are prime to $p$, the ambient lattice is self-dual at $p$, and the class field of definition is unramified at the place under consideration. These assumptions make the integral moduli datum unramified, but good reduction of a chosen abelian variety also requires the CM descent character (8.5) to be unramified. We include its conductor among the bad primes. Outside this enlarged finite set, (8.6) gives good reduction.

Why is this conductor set finite? The model $A/L$ is an abelian variety over a number field, so it extends to an abelian scheme over a nonempty open subscheme of the integers of $L$. At every omitted prime smooth proper base change makes the prime-to-$p$ Tate representation unramified. Equivalently, the compatible CM characters $\psi_w$ are unramified there. Thus adding their conductor does not turn the bad set into an infinite or circular condition.

If any assumption fails, a different conclusion may still hold, but it requires separate work:

- a conductor prime may make the order action nonfree on the integral Tate or Dieudonné module;
- a prime dividing the polarization degree can make the polarization kernel non-étale;
- a level prime requires a finite flat level structure rather than geometric torsion points;
- ramification of the class field over $E$ destroys the canonical prime Artin symbol, even when the abelian variety itself has good reduction;
- an ambient integral model can be singular despite good reduction of the abelian variety.

Thus “good CM prime” means good for a specified package, not merely unramified in $K$.

## 9. Unramified primes and Frobenius

At a good unramified prime, the reciprocity theorem becomes an isogeny formula. Iterating that isogeny around the residue-field orbit turns it into the Frobenius endomorphism. The resulting ideal identity is the most useful finite-place form of complex multiplication.

### 9.1 The Frobenius ideal relation

Let $x=(A,\iota,\lambda,\eta)$ be a rigidified CM datum defined over its class field $H/E$. Let $v$ be a finite place of $E$ satisfying all of the following:

1. $H/E$ is unramified at $v$;
2. $v$ lies outside the integral bad set of Section 2.5 and the clean spreading set of Section 4.5;
3. $A$ has good reduction at a chosen place $w$ of $H$ above $v$;
4. the full CM action is defined over $H$ and extends to the good model at $w$.

Put

$$
q_v=|k_v|,
\qquad f=f(w/v),
\qquad q_w=q_v^f, \tag{9.1}
$$

and

$$
\mathfrak c_v=R_\Phi(\mathfrak p_v). \tag{9.2}
$$

Arithmetic Frobenius $\sigma=\operatorname{Frob}_v$ acts by

$$
A^\sigma\simeq\mathfrak c_v*A. \tag{9.3}
$$

The passage from this characteristic-zero isogeny to relative Frobenius is an integral assertion, so it must be proved separately.

**Frobenius-comparison lemma.** Under hypotheses 2--4, the reduction of the $\mathfrak c_v$-isogeny in (9.3) is the relative $q_v$-power Frobenius from $\widetilde A$ to its arithmetic-Frobenius twist.

**Proof.** This is Proposition 4.3 after base change to the strict henselization at $w$. Hypothesis 2 makes $\mathcal O_K\otimes\mathbf Z_p$ étale and the polarization and rigidifying level prime to $p$; hypotheses 3--4 identify the generic CM datum with a fiber of the clean integral PEL spread. The proof of Proposition 4.3 computed, independently of Theorem 4.1, that

$$
\ker F_{q_v}=\widetilde A[R_\Phi(\mathfrak p_v)] \tag{9.3a}
$$

by comparing the elementary divisors of crystalline Frobenius with the inverse-incidence exponents of the reflex norm. Formation of the finite flat ideal kernel and its quotient commutes with this base change. Its target polarization and prime-to-$p$ level are also the ones transported in characteristic zero, so the unique rigid target isomorphism identifies the reduction of the ideal isogeny with relative $q_v$-Frobenius. $\square$

This lemma explains why good reduction and exclusion of discriminant and conductor primes appear in the theorem. A rational lattice calculation alone cannot identify a connected finite flat Frobenius kernel.

Its order in the decomposition group of $w$ is $f$. Composing (9.3) through the orbit

$$
A\longrightarrow A^\sigma\longrightarrow\cdots
\longrightarrow A^{\sigma^f}=A \tag{9.4}
$$

gives, after reduction, the $q_w$-power Frobenius endomorphism $\pi_w$ of $\widetilde A/k_w$.

**Theorem 9.1 (Frobenius ideal formula).** Under the four hypotheses above, $\pi_w$ belongs to $K$, and

$$
(\pi_w)=\mathfrak c_v^f
=R_\Phi(\mathfrak p_v)^f. \tag{9.5}
$$

**Proof.** Each arrow in (9.4) is the $K$-linear integral isogeny attached to $\mathfrak c_v$. Its analytic lattice changes by $\mathfrak c_v^{-1}$. The descent identification after $f$ steps preserves the labeled CM action, so the characteristic-zero composite is a $K$-linear endomorphism of the rank-one $K$-space $H_1(A,\mathbf Q)$. It is therefore multiplication by a unique element $\alpha_w\in K$. Since the composite carries $\mathfrak c_v^{-f}\mathfrak a$ to $\mathfrak a$, one has

$$
(\alpha_w)=\mathfrak c_v^f. \tag{9.4a}
$$

By the Frobenius-comparison lemma, the reductions of the arrows are the successive relative $q_v$-Frobenius maps, so the reduction of $\alpha_w$ is the $q_w$-power Frobenius endomorphism. We denote that reduction, and the element of $K$ inducing it, by the same symbol $\pi_w$. Equation (9.4a) is (9.5). This direct argument also shows exactly where the hypothesis that the labeled CM action descends is used. $\square$

The exponent $f$ is essential. The ideal $R_\Phi(\mathfrak p_v)$ describes one $q_v$-Frobenius step between conjugate fibers. It becomes an endomorphism of the fiber over $k_w$ only after the entire residue orbit has been traversed.

### 9.2 Frobenius as a CM endomorphism

The conclusion $\pi_w\in K$ uses the hypothesis that the full CM action is defined over the residue field. Without it, Frobenius may normalize $K$ while acting nontrivially on it, and only a power of Frobenius lies in the centralizer. Likewise, if one remembers only a suborder, the centralizer calculation takes place in $K$ rationally but the Frobenius need not lie in that order integrally.

The ideal formula determines $\pi_w$ only up to a unit of $\mathcal O_K$. The actual Frobenius endomorphism is selected by its action on torsion, or equivalently by the descent comparison around (9.4). Polarization removes most of the remaining ambiguity through the norm equation below. Roots of unity can remain, as is already familiar for CM elliptic curves with extra automorphisms.

If $A$ is defined over a larger field $L\supset H$ and $z$ lies above $w$ with residue degree $d$, then

$$
\pi_z=\pi_w^d,
\qquad (\pi_z)=R_\Phi(\mathfrak p_v)^{fd}. \tag{9.6}
$$

This is the correct base-change behavior. Reusing (9.5) without changing the residue degree would give the wrong norm.

### 9.3 The norm equation and Weil size

For every abelian variety over $k_w$, Verschiebung composed with Frobenius is multiplication by $q_w$. Under a polarization, Verschiebung is the Rosati adjoint $\pi_w^\dagger$ of Frobenius, and therefore

$$
\pi_w^\dagger\pi_w=[q_w]. \tag{9.7}
$$

Under a polarization whose Rosati involution restricts to CM conjugation, (9.7) becomes

$$
\pi_w\bar\pi_w=q_w. \tag{9.8}
$$

The ideal version follows already from the reflex weight identity:

$$
\begin{aligned}
(\pi_w)(\bar\pi_w)
&=(\mathfrak c_v\bar{\mathfrak c}_v)^f\\
&=(q_v\mathcal O_K)^f
=q_w\mathcal O_K.
\end{aligned} \tag{9.9}
$$

Equation (9.7) fixes the totally positive unit left undetermined by (9.9).

For every complex embedding $\varphi:K\hookrightarrow\mathbf C$, applying $\varphi$ to (9.8) gives

$$
|\varphi(\pi_w)|^2=q_w. \tag{9.10}
$$

Thus all conjugates of Frobenius have absolute value $q_w^{1/2}$. The Weil size is not an additional analytic estimate in the CM case; it is the polarization identity.

### 9.4 Characteristic polynomials

On $V_\ell(A)$, $K\otimes\mathbf Q_\ell$ acts through its regular representation and $\pi_w$ acts by multiplication. Hence its characteristic polynomial is

$$
P_w(T)=N_{K/\mathbf Q}(T-\pi_w)
=\prod_{\varphi:K\hookrightarrow\mathbf C}
(T-\varphi(\pi_w)). \tag{9.11}
$$

It lies in $\mathbf Z[T]$: Frobenius is integral over $\mathbf Z$, and its characteristic polynomial on the integral Tate module has integer coefficients independent of $\ell$. Its degree is $2g$, its constant term is $q_w^g$, and (9.8) gives the functional equation

$$
T^{2g}P_w(q_w/T)=q_w^gP_w(T). \tag{9.12}
$$

If the special fiber acquires extra endomorphisms, (9.11) remains valid because it describes the action on the original $2g$-dimensional Tate module. Extra endomorphisms do not increase the multiplicity of the embeddings of $K$.

### 9.5 Split, inert, and ramified behavior

The cleanest illustration is an imaginary quadratic field. Let $p$ be a rational prime away from the conductor and discriminant.

If

$$
p\mathcal O_K=\mathfrak p\bar{\mathfrak p}, \tag{9.13}
$$

then the chosen type selects one of the two prime directions. The Frobenius ideal is a power of that prime, and the reduction is ordinary.

If $p$ is inert, the unique prime is fixed by conjugation. The reflex ideal and its conjugate have the same support; (9.8) forces equal $p$-adic slopes $1/2$. The reduction is supersingular. This statement concerns a field over which good reduction and the full CM action are present; over a smaller residue field, Frobenius may normalize rather than centralize $K$.

If $p$ ramifies in $K$, it lies in the discriminant part of the bad set for the clean integral theorem. A CM elliptic curve may still have good reduction there after extension, but the split/inert dichotomy and the étale local-order calculation no longer apply.

Consider the concrete curve

$$
A:y^2=x^3-x,
$$

which has CM by $\mathbf Z[i]$ over a field defining the automorphism $(x,y)\mapsto(-x,iy)$. At $p=5$ one finds

$$
\#A(\mathbf F_5)=8,
\qquad P_5(T)=T^2+2T+5.
$$

Thus a Frobenius is $\pi=-1+2i$ or its conjugate, according to the chosen embedding and place. Since

$$
5=(-1+2i)(-1-2i),
$$

the two primes above $5$ are separated and the reduction is ordinary. Notice that the ideal relation alone permits unit associates; the actual model and descent datum select the trace $-2$ rather than another trace obtainable from an associate.

At $p=3$, direct counting gives

$$
\#A(\mathbf F_3)=4,
\qquad P_3(T)=T^2+3.
$$

The prime $3$ is inert in $\mathbf Q(i)$, and both roots have $3$-adic slope $1/2$. This is supersingular reduction. The $3$-power Frobenius over $\mathbf F_3$ normalizes but does not centralize the displayed $\mathbf Q(i)$-action, which is not fully defined over $\mathbf F_3$; indeed its polynomial roots do not lie in $\mathbf Q(i)$. After base change to $\mathbf F_9$, Frobenius is its square, namely $-3$, which does lie in $\mathbf Q(i)$ and satisfies $(-3)\overline{(-3)}=9$. Thus the example also demonstrates why the field-of-definition hypothesis in Theorem 9.1 cannot be omitted.

## 10. Newton slopes and ordinary reduction

The ideal of Frobenius contains more information than its complex absolute values. Its valuations at primes of $K$ above the residue characteristic are exactly the Newton slopes. The reflex ideal therefore turns the combinatorics of a CM type into the isogeny type of the reduction.

### 10.1 Valuations of the reflex ideal

Retain the hypotheses and notation of Chapter 9, and let $p$ be the residue characteristic. For a prime $\mathfrak q$ of $K$ above $p$, write $v_\mathfrak q$ for the additive valuation. From (9.5),

$$
v_\mathfrak q(\pi_w)
=f\,v_\mathfrak q(R_\Phi(\mathfrak p_v)). \tag{10.1}
$$

The product formula for the reflex norm computes the exponent on the right. In a common finite Galois closure, it counts the embeddings in the inverse incidence relation defining $r_\Phi$ whose chosen prime lies over $\mathfrak q$. Ramification weights are already contained in the normalized valuations; inserting an extra residue degree would count them twice.

Conjugation and the weight identity give

$$
v_\mathfrak q(R_\Phi(\mathfrak p_v))
+v_\mathfrak q(\overline{R_\Phi(\mathfrak p_v)})
=v_\mathfrak q(q_v). \tag{10.2}
$$

This is the local source of the symmetry $\lambda\leftrightarrow1-\lambda$ in the Newton polygon.

### 10.2 The slope formula

**Theorem 10.1 (CM slope formula).** For each $\mathfrak q\mid p$, the slope contributed by the $K_\mathfrak q$-factor of the rational Dieudonné module is

$$
\lambda_\mathfrak q
=\frac{v_\mathfrak q(\pi_w)}{v_\mathfrak q(q_w)}
=\frac{v_\mathfrak q(R_\Phi(\mathfrak p_v))}
{v_\mathfrak q(q_v)}. \tag{10.3}
$$

It occurs with multiplicity $[K_\mathfrak q:\mathbf Q_p]$. Conjugate primes have complementary slopes:

$$
\lambda_{\bar{\mathfrak q}}=1-\lambda_\mathfrak q. \tag{10.4}
$$

**Proof.** Because the full $K$-action is defined over $k_w$, the linear $q_w$-Frobenius commutes with $K\otimes\mathbf Q_p$ and acts on the $K_\mathfrak q$-factor by the scalar $\pi_w$. After a coefficient field splits $K_\mathfrak q$, its eigenvalues are the $\mathbf Q_p$-embeddings of $\pi_w$ coming from that one local field. Every such embedding preserves the unique extension of the $p$-adic valuation, so all these eigenvalues have valuation $v_\mathfrak q(\pi_w)$. The factor is therefore isoclinic, with slope the valuation of $\pi_w$ divided by the valuation of $q_w$. Equation (10.1) and $q_w=q_v^f$ give the second equality. Equation (10.2) gives (10.4). The number of embeddings, hence the multiplicity, is $[K_\mathfrak q:\mathbf Q_p]$. $\square$

The formula is unchanged after enlarging the residue field: both numerator and denominator are multiplied by the same residue degree. Newton slopes are geometric invariants.

### 10.3 The ordinary criterion

An abelian variety of dimension $g$ is ordinary when its slopes are $0$ and $1$, each with multiplicity $g$. At a clean unramified prime, Theorem 10.1 yields:

**Corollary 10.2.** The CM reduction is ordinary if and only if

$$
R_\Phi(\mathfrak p_v)
+\overline{R_\Phi(\mathfrak p_v)}
=\mathcal O_K, \tag{10.5}
$$

that is, the reflex ideal and its conjugate have disjoint prime support.

**Proof.** By (10.2), the two nonnegative exponents at a prime sum to the exponent of $q_v$. Their ratio in (10.3) is $0$ or $1$ exactly when one exponent is zero. This holds for every $\mathfrak q\mid p$ exactly when no prime divides both ideals. Conjugation then pairs the slope-zero and slope-one multiplicities, each totaling $g$. $\square$

A sufficient, but not necessary in every higher-dimensional configuration, condition is that $p$ split completely in the normal closure containing the type. Then every prime direction corresponds to one embedding, and the type selects exactly one from each conjugate pair. The criterion (10.5) is sharper because it remains valid when the decomposition group is nontrivial.

### 10.4 Elliptic and quartic examples

For an imaginary quadratic $K$, a split prime has two conjugate factors. The type assigns the reflex ideal to one factor, so (10.5) holds and the reduction is ordinary. An inert prime is fixed by conjugation, so the two reflex ideals have the same support and the only possible slope is $1/2$ with multiplicity two.

Now let $K/\mathbf Q$ be cyclic quartic with Galois group generated by $a$ and complex conjugation $a^2$. Take

$$
\Phi=\{1,a\}. \tag{10.6}
$$

The reflex type is represented by the inverse set $\{1,a^{-1}\}$. At a rational prime splitting completely in $K$, the reflex ideal chooses two prime factors, one from each conjugate pair. Its conjugate chooses the other two, so the reduction is ordinary.

At a prime whose decomposition group is $\langle a^2\rangle$, conjugation fixes each decomposition orbit. Each relevant prime receives equal contribution from the reflex ideal and its conjugate, producing slope $1/2$; the same conclusion holds for an inert prime with full decomposition group. More general non-Galois types and higher-degree decomposition orbits can produce mixed multisets containing $0$, intermediate fractions, and $1$, always with the symmetry forced by (10.4). The example shows why “split means ordinary, inert means supersingular” is a dimension-one slogan, while (10.3) is the general theorem.

## 11. Bad reduction, conductors, and boundaries

The clean Frobenius formula has several hypotheses because several unrelated phenomena are often called bad reduction. Keeping them separate prevents a rational theorem from being misused as an integral one.

### 11.1 Four different meanings of bad

For a CM moduli datum at a finite prime, at least four failures can occur.

First, the abelian variety itself may not extend to an abelian scheme. This is geometric bad reduction and is detected by inertia on a prime-to-$p$ Tate module.

Second, the abelian variety may have good reduction while a chosen polarization has non-étale kernel. This happens at primes dividing its degree.

Third, the order action may cease to be maximal or locally free. This is controlled by the conductor of the order and the discriminant of the CM algebra.

Fourth, the ambient moduli space may have bad integral reduction because its level or lattice is defective. This can occur even when the particular abelian variety has good reduction.

Only the first is cured by Theorem 8.1 after a finite extension. The other three concern the extra integral structure and must be repaired by changing level, lattice, or moduli problem.

### 11.2 Ramified reciprocity has no prime Frobenius

If $H/E$ is ramified at $v$, the ideal $\mathfrak p_v$ has no Artin symbol in $\operatorname{Gal}(H/E)$. Local reciprocity still supplies a map

$$
E_v^\times\longrightarrow D_w, \tag{11.1}
$$

but a uniformizer chooses only a lift of residue Frobenius and units move that lift through inertia. The correct ramified orbit statement is therefore

$$
x^{\operatorname{rec}_{E_v}(s)}
=r_\Phi(s)*x,
\qquad s\in E_v^\times, \tag{11.2}
$$

where $E_v^\times$ is embedded as the $v$-component of the ideles and the right side includes its action on prime-to-$p$ level. This compares conjugate moduli objects; it is not a linear representation of $D_w$ on one fixed Tate module unless descent data identify those conjugates.

For the local representation of a model over $H_w$, an element $u\in H_w^\times$ first enters reciprocity through $N_{H_w/E_v}(u)$. After choosing the principal factor $a(u)\in K^\times$ supplied by the rigidified descent, its action in a fixed $K\otimes\mathbf Q_\ell$-basis is

$$
\rho_{\ell,w}(\operatorname{rec}_{H_w}(u))
=a(u)\,r_\Phi(N_{H_w/E_v}u)_\ell^{-1}. \tag{11.2a}
$$

This is the local formula already used in (8.5). There is no canonical replacement of (9.5) using only $\mathfrak p_v$.

After passing to an extension over which inertia is killed and good reduction is acquired, one may apply the unramified formula there. Norm compatibility (3.5) relates the new reflex ideal to the old local idele. This process depends on the extension and should not be compressed into a fictitious “ramified Frobenius ideal.”

### 11.3 Nonmaximal orders and integral failure

Suppose $\operatorname{End}(A)=\mathcal O$ is nonmaximal. Away from the conductor, $\mathcal O\otimes\mathbf Z_p=\mathcal O_K\otimes\mathbf Z_p$, so all maximal-order formulas apply. At a conductor prime, the rational CM representation still has rank one over $K\otimes\mathbf Q_\ell$, and Theorem 4.1 still determines its adelic rational transform. But an $\mathcal O$-ideal can fail to be invertible, the reduction can acquire a larger endomorphism order, and the naive ideal class action is no longer a group action.

For elliptic curves this is visible in isogeny volcanoes: prime-to-conductor isogenies stay on a fixed order level, while conductor-prime isogenies can move to a larger or smaller order. The phenomenon is not a failure of reciprocity. It is the failure of the integral category to be described by invertible ideals of one fixed order.

### 11.4 Changing the field of definition

Potential good reduction often requires enlarging the base field. Three quantities then change in a controlled way:

$$
\begin{array}{c|c}
\text{quantity}&\text{effect of residue degree }d\\ \hline
\text{Frobenius}&\pi\mapsto\pi^d\\
\text{Frobenius ideal}&(\pi)\mapsto(\pi)^d\\
\text{residue cardinality}&q\mapsto q^d.
\end{array} \tag{11.3}
$$

Consequently $\pi\bar\pi=q$ and all Newton slopes are invariant. Ramification can kill inertia and improve reduction, but then an ideal symbol should be formed only after reaching an unramified quotient. If the larger field no longer contains $E$ as the specified reflex base, norm functoriality must first transport its local idele back to $E$.

## 12. The finite-place reciprocity package

The results can now be assembled into a form reusable in the study of special points and integral models. The point of the package is not brevity alone: it records precisely which conclusions are rational, which are integral, and which require good reduction.

### 12.1 A reusable theorem

**Theorem 12.1 (CM reciprocity and reduction package).** Let $K$ be a CM field, $\Phi$ a CM type with reflex field $E$, and

$$
x=(A,\iota,\lambda,\eta)
$$

a polarized CM datum of type $\Phi$. Assume the level is sufficiently fine to rigidify the object, and let $H/E$ be the class field cut out by its adelic stabilizer.

1. For $s\in\mathbf A_E^\times$,

   $$
   x^{\operatorname{Art}_E(s)}=r_\Phi(s_f)*x, \tag{12.1}
   $$

   with arithmetic Artin reciprocity and inverse lattice action. The rigidified CM locus is finite étale over $E$; hence the point and all $E$-rational moduli values at it are algebraic. Their fields of values are abelian over $E$, and (12.1) holds for every lift in $\operatorname{Aut}(\mathbf C/E)$, not only for unramified Frobenius elements.

2. The comparison is compatible with the CM action, polarization similitude, prime-to-bad level, products, induced types, and embeddings into ambient PEL similitude groups.

3. The datum has a canonical effective descent to $H$. After forgetting rigidification, the coarse point descends to its field of moduli, while a chosen representative can retain a finite automorphism obstruction.

4. The abelian variety has potentially good reduction at every finite place.

5. Let $v$ be unramified in $H$, away from all integral bad primes, and let $w\mid v$ be a place of good reduction with residue degree $f$. If the full CM action is defined over $H$, then the $q_w$-power Frobenius belongs to $K$ and satisfies

   $$
   (\pi_w)=R_\Phi(\mathfrak p_v)^f,
   \qquad
   \pi_w\bar\pi_w=q_w. \tag{12.2}
   $$

6. Its characteristic polynomial and slopes are

   $$
   P_w(T)=N_{K/\mathbf Q}(T-\pi_w),
   \qquad
   \lambda_\mathfrak q=
   \frac{v_\mathfrak q(R_\Phi(\mathfrak p_v))}
   {v_\mathfrak q(q_v)}. \tag{12.3}
   $$

   At a clean unramified prime, the reduction is ordinary exactly when the reflex ideal and its conjugate are coprime.

**Proof.** Proposition 4.2 gives algebraicity and the canonical finite étale CM locus. Proposition 4.3 and Lemma 4.4 identify its clean-prime Frobenius permutations and then its full Galois group; global reciprocity gives Theorem 4.1 and assertion 1. The compatibility in assertion 2 follows from the weight identity, the simultaneous finite-level calculation, and functoriality of the reflex norm. Sections 5 and 6 prove assertion 3 by stabilizers and effective descent. Theorem 8.1 proves assertion 4. The independent reflex-kernel lemma and the orbit composition in Theorem 9.1, followed by the polarization identity, prove assertion 5. The regular representation calculation and Theorem 10.1 prove assertion 6. $\square$

### 12.2 A normalization checklist

The package can be checked quickly in any application.

- **Artin direction:** a uniformizer maps to arithmetic Frobenius.
- **Reflex direction:** $r_\Phi$ goes from $E$ to $K$; the type norm goes from $K$ to $E$.
- **Lattice direction:** $t*A$ has lattice $t^{-1}\mathfrak a$.
- **Principal change:** replacing $s$ by $as$ changes the target presentation by multiplication with $r_\Phi(a)$.
- **Weight:** $r_\Phi(s)\overline{r_\Phi(s)}=N_{E/\mathbf Q}(s)$.
- **Field:** $\operatorname{Art}_E(s)$ acts only on automorphisms fixing $E$; a general conjugation first transports the reflex datum.
- **Frobenius:** a prime symbol is used only in an unramified quotient.
- **Residue degree:** one prime step gives an isogeny between conjugate fibers; $f$ steps give the Frobenius endomorphism.
- **Integrality:** conductor, polarization, level, and ambient-lattice primes are removed before using ideal formulas.
- **Reduction:** potential good reduction does not imply good reduction over the original local field.

These checks are mutually reinforcing. For example, (12.2) and the weight identity give

$$
(\pi_w\bar\pi_w)=q_w\mathcal O_K,
$$

while the polarization makes this an equality of elements. A misplaced inverse would reverse the Frobenius ideal; a missing residue degree would give $q_v$ instead of $q_w$; a type norm in place of the reflex norm would land in the wrong field.

### 12.3 Conclusion

The main theorem of complex multiplication identifies two actions that begin in different worlds. The Hodge cocharacter produces the reflex norm

$$
r_\Phi:\operatorname{Res}_{E/\mathbf Q}\mathbf G_m
\longrightarrow\operatorname{Res}_{K/\mathbf Q}\mathbf G_m,
$$

and arithmetic class field theory turns an idele of $E$ into a Galois automorphism. The finite étale CM locus first makes CM moduli values algebraic. Its clean-prime crystalline Frobenius calculation realizes the inverse-incidence matrix of the Hodge cocharacter as the kernel of the reflex-ideal isogeny; Frobenius generation and global reciprocity then identify arbitrary Galois action. The resulting simultaneous torsion comparison recovers the inverse lattice transform

$$
A(\mathfrak a,\Phi)^{\operatorname{Art}_E(s)}
\simeq A(r_\Phi(s_f)^{-1}\mathfrak a,\Phi).
$$

The weight identity preserves polarized data with the exact norm multiplier, while level structures refine ideal classes to ray classes and eliminate descent ambiguity. The stabilizer of a rigidified CM point therefore cuts out its canonical abelian field of definition. After embedding the CM torus into Hilbert, quaternionic, or unitary similitude data, the same formula gives the Galois action on the corresponding special point.

At finite places, commutative semisimple CM action rules out persistent unipotent monodromy and proves potential good reduction. Where the datum is integral, unramified, and already good, one Artin prime step is the reflex-ideal isogeny. Iterating through the residue orbit produces Frobenius:

$$
(\pi_w)=R_\Phi(\mathfrak p_v)^{f(w/v)},
\qquad
\pi_w\bar\pi_w=|k_w|.
$$

Its characteristic polynomial, Weil absolute values, Newton slopes, and ordinary criterion follow from these two identities. At ramified, conductor, polarization, or level primes the book has kept the rational reciprocity theorem separate from integral claims, so no nonexistent prime Frobenius or noninvertible ideal action is smuggled into the conclusion.

The resulting package is the precise bridge needed for arithmetic geometry: CM types determine reflex norms; reflex norms determine canonical Galois orbits; and, at eligible finite places, those same orbits determine reduction and Frobenius.
