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
   - [The torsion comparison lemma](#42-the-torsion-comparison-lemma)
   - [Proof of the torsion comparison lemma](#43-proof-of-the-torsion-comparison-lemma)
   - [Passage from torsion to lattices](#44-passage-from-torsion-to-lattices)
   - [Independence of choices and the cocycle law](#45-independence-of-choices-and-the-cocycle-law)
   - [Polarized and order-valued forms](#46-polarized-and-order-valued-forms)
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

This is not formal. The reflex norm was defined from a Hodge cocharacter, whereas Galois conjugation is defined algebraically. A proof needs a bridge from Hodge data to algebraic torsion data. The bridge will be a torsion comparison lemma: it identifies the action on all finite torsion simultaneously, and therefore identifies the corresponding commensurable lattices.

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
K^\times\backslash\mathbf A_{K,f}^\times/widehat{\mathcal O}_K^\times, \tag{2.9}
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
U_v^n&\longleftrightarrow I_v^n\quad(n\geq1),\\
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
A^{\operatorname{Frob}_v}simeq
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

We now prove the arithmetic assertion that structural CM theory leaves open. The proof first works on torsion. Finite torsion detects the finite adelic lattice, and polarization controls the scalar ambiguity. This is the point at which the Hodge cocharacter, global reciprocity, and algebraic Galois action meet.

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

The theorem concerns $\sigma$ fixing $E$. For arbitrary $\tau\in\operatorname{Aut}(\mathbf C)$, first transport $(K,\Phi,E)$ to $(\tau K,\tau\Phi,\tau E)$ and then apply the theorem over $\tau E$. One must not feed such a $\tau$ directly into $\operatorname{Art}_E$ unless it fixes $E$.

### 4.2 The torsion comparison lemma

Write

$$
V_f(A)=H_1(A,\mathbf Q)\otimes\mathbf A_f,
\qquad T_f(A)=H_1(A,\mathbf Z)\otimes\widehat{\mathbf Z}. \tag{4.4}
$$

The quotient $V_f(A)/T_f(A)$ is canonically the full torsion subgroup $A_{\mathrm{tors}}(\mathbf C)$. Galois acts on torsion algebraically even though (4.4) was described analytically.

**Lemma 4.2 (torsion comparison).** Under the hypotheses of Theorem 4.1, there is a $K\otimes\mathbf A_f$-linear isomorphism

$$
\beta_{\sigma,s}:V_f(A)\xrightarrow{\sim}V_f(A^\sigma) \tag{4.5}
$$

such that

$$
\beta_{\sigma,s}(T_f(A))
=r_\Phi(s_f)T_f(A^\sigma), \tag{4.6}
$$

and on the quotient by the lattices it induces the ordinary map $x\mapsto x^\sigma$ on torsion points. Equivalently, after using $\beta_{\sigma,s}$ to identify both rational spaces, the target integral lattice is $r_\Phi(s_f)^{-1}T_f(A)$.

The assertion is simultaneous over all primes. A family of separate $\ell$-adic comparisons would leave an uncontrolled rational scalar; the adelic statement and the principal-idele relation remove that ambiguity.

Before entering the proof, two algebraicity points deserve emphasis. A CM complex torus is projective because its positive trace form is a Riemann form. Its analytic homomorphisms are algebraic, because their graphs are polarized complex subtori. Finally, every polarized abelian variety with level is represented by a point of an algebraic moduli scheme of finite type. Thus both Galois conjugation and the ideal isogenies below act on algebraic objects. No conclusion is being drawn merely from a homeomorphism of complex tori.

The torsion itself remembers the commensurability class of the lattice. If $V$ is a finite-dimensional rational vector space and $\Lambda\subset V$ a full lattice, then

$$
V/\Lambda=\varinjlim_N N^{-1}\Lambda/\Lambda. \tag{4.7}
$$

Conversely, the kernels of multiplication by $N$ together with their transition maps recover $\Lambda\otimes\widehat{\mathbf Z}$ inside $V\otimes\mathbf A_f$. Hence it is enough to prove a compatible comparison at every finite level; compatibility is what upgrades separate finite statements to a single finite-adelic statement.

### 4.3 Proof of the torsion comparison lemma

We give the comparison argument in enough detail to isolate its only genuinely arithmetic step.

Choose an integer $N\geq3$ divisible by none of the primes at which the order or polarization data are defective. A symplectic basis of $A[N]$ embeds the rigidified polarized CM object into the fine moduli scheme $\mathcal A_{g,d,N}$ of polarized abelian varieties of fixed degree with full level $N$. This scheme is defined over the cyclotomic field required by the Weil pairing. Its algebraic coordinate functions separate geometric points.

We may replace $N$ by a multiple without losing the original level, and we do so until theta constants of level dividing $2N$ give projective coordinates on the chosen fine moduli scheme. Ratios of homogeneous polynomials of the same degree in those constants then generate its function field. This reduction is useful because it lets us prove the required transformation statement on explicit convergent series.

On the analytic uniformization, such functions may be represented by quotients of theta constants of a common weight and level. We need two elementary transformation facts.

1. If a rational symplectic similitude $u$ carries one polarized lattice to another, substitution in the theta series carries the associated moduli value to the value at the transformed lattice. The finite residue of $u$ records its action on level.
2. If $a\in E^\times$ is principal, the product formula together with the transformation formula makes its finite action cancel its archimedean action. Consequently the induced action on every algebraic moduli value is trivial.

For completeness, the decisive cancellation can be seen term by term. A theta series has the form

$$
\vartheta_m(z,\tau)=
\sum_{n\in\mathbf Z^g}
\exp\!\left(\pi i(n+m_1)^t\tau(n+m_1)
+2\pi i(n+m_1)^t(z+m_2)\right). \tag{4.8}
$$

A change of symplectic lattice multiplies it by a determinant square root and a root of unity depending only on the level characteristic $m$. In a quotient of equal total weight the determinant factors cancel. The remaining roots of unity are acted on by the cyclotomic component of Artin reciprocity; local reciprocity sends a unit to exactly the inverse change of the level characteristic. For a principal $a$, the product of these local root-of-unity factors is $1$. The exponent matrix governing the change of the CM lattice is the Galois orbit of the Hodge cocharacter. By the defining identity

$$
(r_\Phi)_*[\iota_E]=\mu_\Phi, \tag{4.9}
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

A rational symplectic similitude becomes integral after multiplication by a denominator. Factor it into an integral change of basis and the finite isogeny induced by inclusion of lattices. Decomposing the original theta sum into residue classes modulo that denominator proves the distribution relation. Thus the only scalar factors are determinant powers and roots of unity. In a ratio of equal weight the determinant powers cancel. In a rational moduli function, the total degree in the characteristics is zero, so the remaining root of unity depends only on the action on level torsion. Arithmetic local reciprocity gives precisely the inverse multiplication convention on that torsion. This proves the two transformation facts without assuming the desired orbit formula.

Now let $f$ be any rational function on the fine moduli scheme regular at the CM point $x$. For the chosen $\sigma\in\operatorname{Aut}(\mathbf C/E)$ and an idele $s$ with $\operatorname{Art}_E(s)=\sigma|_{E^{\mathrm{ab}}}$, the preceding calculation gives the **CM value identity**

$$
f(x)^\sigma
=f(r_\Phi(s_f)*x). \tag{4.10}
$$

Initially this is obtained when the finite Artin class can be represented away from the denominators of the theta quotient and the level. Weak approximation moves the support of an idele away from any prescribed finite set without changing its class in the relevant ray quotient. Theta quotients generate the function field of the fine moduli scheme, so clearing numerator and denominator extends the identity to every regular moduli function. In particular, (4.10) proves rather than assumes that all such CM values lie in an abelian extension of $E$: two automorphisms with the same restriction to $E^{\mathrm{ab}}$ give the same right side.

Because regular functions separate the rigidified geometric points, (4.10) identifies $x^\sigma$ with $r_\Phi(s_f)*x$. Under analytic uniformization, the target lattice is $r_\Phi(s_f)^{-1}\widehat{\mathfrak a}$, and the level transformation is multiplication by the same inverse. Passing over all admissible levels gives (4.5)--(4.6).

Two observations protect this proof from circularity. The algebraicity of the moduli functions and their $q$-expansions comes from the algebraic moduli scheme, not from a presumed canonical model of the CM point. And global reciprocity is used only to identify the action on cyclotomic coefficients and to kill principal ideles; the desired CM orbit formula is then forced by the independently computed theta transformation.

We expand the exponent calculation, since this is where the reflex norm rather than the type norm enters. Work in a finite Galois extension $L/\mathbf Q$ containing $K$ and $E$. If $\tau:E\hookrightarrow L$ and $\varphi:K\hookrightarrow L$, the exponent with which the $\tau$-component of $s$ changes the $\varphi$-component of the CM lattice is

$$
m(\tau,\varphi)=
\begin{cases}
1,&\gamma_\tau^{-1}\varphi\in\Phi,\\
0,&\gamma_\tau^{-1}\varphi\notin\Phi,
\end{cases} \tag{4.11}
$$

where $\gamma_\tau|_E=\tau$. Consequently

$$
\varphi(r_\Phi(s))
=\prod_{\tau:E\hookrightarrow L}\tau(s)^{m(\tau,\varphi)}. \tag{4.12}
$$

The inverse on $\gamma_\tau$ in (4.11) is forced by transporting a coordinate function contravariantly. In the primitive Galois case it changes the type set $S$ into $S^{-1}$. Multiplying the original type embeddings instead would give $N_\Phi:K^\times\to E^\times$, which cannot act on the $K$-lattice at all. Formula (4.12) therefore checks both the direction and the inverse incidence.

For clarity, the support-moving step does not presuppose that the field $E(f(x))$ is abelian. Choose a finite Galois field containing the coefficients of the theta quotient and the coordinates of $x$. The explicit transformation calculation depends on an automorphism only through its action on the finitely many roots of unity and torsion labels occurring in the formula. Those actions form a finite abelian ray quotient by local and global reciprocity. An idele representing the class in that quotient may be moved away from the denominator set. Applying the good-idele calculation there proves (4.10); it then shows that the commutator subgroup fixes $f(x)$. Thus abelianity is a consequence of the calculation, not an input to it.

### 4.4 Passage from torsion to lattices

We derive Theorem 4.1 from Lemma 4.2. A full lattice in a rational vector space is recovered from all of its finite completions:

$$
\mathfrak a=K\cap\widehat{\mathfrak a}
\quad\text{inside }K\otimes\mathbf A_f. \tag{4.13}
$$

Indeed, membership in a fractional ideal is the collection of its lower valuation bounds at all finite primes. Equation (4.6) therefore determines the target integral homology lattice uniquely. It is

$$
\mathfrak a^\sigma
=K\cap r_\Phi(s_f)^{-1}\widehat{\mathfrak a}. \tag{4.14}
$$

The right side is the fractional ideal represented adelically by $r_\Phi(s_f)^{-1}\widehat{\mathfrak a}$, so it is exactly the inverse ideal transform. The analytic classification of CM abelian varieties then turns equality of lattices into the algebraic isomorphism (4.3).

### 4.5 Independence of choices and the cocycle law

Suppose $s'$ has the same Artin image as $s$. Their quotient belongs to the kernel of the relevant finite Artin quotient. For the action on a fixed rigidified datum, that kernel is its adelic stabilizer, so $r_\Phi(s_f')*A$ and $r_\Phi(s_f)*A$ are canonically isomorphic with the specified level. In the unrestricted infinite statement the quotient may also contain a connected archimedean component, which has no finite reflex contribution.

If $s$ is replaced by $as$ with $a\in E^\times$, then

$$
r_\Phi(as_f)=r_\Phi(a)r_\Phi(s_f). \tag{4.15}
$$

Multiplication by $r_\Phi(a)$ identifies the two lattice presentations, since one target lattice is $r_\Phi(a)^{-1}$ times the other. Thus principal ideles change the comparison isomorphism, not the resulting isomorphism class.

For $\sigma,\tau\in G_E^{\mathrm{ab}}$ represented by $s,t$, multiplicativity of Artin, the reflex norm, and the ideal action gives

$$
r_\Phi(st)*(A)=r_\Phi(s)*(r_\Phi(t)*A). \tag{4.16}
$$

With the base-change convention (1.7), the resulting isomorphisms satisfy the descent cocycle. Before rigidification they do so only up to an automorphism of the CM object; this is the precise source of the field-of-moduli obstruction discussed later.

### 4.6 Polarized and order-valued forms

Assume $(A,\iota,\lambda)$ is represented by $(\mathfrak a,\xi)$. For an integral ideal $\mathfrak b$ of $E$ away from the bad set, put

$$
\mathfrak c=R_\Phi(\mathfrak b),
\qquad n=N_{E/\mathbf Q}(\mathfrak b). \tag{4.17}
$$

Then the comparison sends the polarized datum to

$$
(\mathfrak c^{-1}\mathfrak a,n\xi). \tag{4.18}
$$

Equation (2.15) proves that the polarization type is unchanged. The canonical isogeny has degree

$$
N_{K/\mathbf Q}(\mathfrak c)=n^g \tag{4.19}
$$

and pulls the new polarization back to $n\lambda$. The equality of degrees

$$
(n^g)^2=n^{2g}=\deg[n]_A \tag{4.20}
$$

is a useful check on the conjugate factor in the reflex norm.

For a nonmaximal order, the same statement holds away from its conductor with proper invertible ideals. At conductor primes the rational theorem (4.2) remains meaningful, but an assertion about integral ideal actions requires a separate local lattice calculation. Reciprocity never repairs noninvertibility.

There is also a useful representation-theoretic form. Fix a model over a number field $L\supset E$ on which the CM action is defined, a prime $\ell$, and a $K\otimes\mathbf Q_\ell$-basis of $V_\ell(A)$. Galois acts through a character

$$
\rho_\ell:G_L\longrightarrow(K\otimes\mathbf Q_\ell)^\times. \tag{4.21}
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

**Theorem 5.1.** If the level is fine enough that $x$ has no nontrivial automorphisms, then $H_x$ is both the field of moduli and a field of definition of $x$. Moreover, for $s\in\mathbf A_E^\times$,

$$
x^{\operatorname{Art}_E(s)}=r_\Phi(s_f)*x. \tag{5.4}
$$

**Proof.** By Theorem 4.1, an Artin element fixes $x$ if and only if its representing idele belongs to $U_x$. Thus the fixed field of the Galois stabilizer is (5.3). The comparison isomorphisms satisfy the cocycle law by (4.16). Since the automorphism group is trivial, equality up to automorphism is equality, and ordinary Galois descent is effective. Formula (5.4) is the descended form of (4.3). $\square$

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
\simeq K^\times\backslash\mathbf A_{K,f}^\times/widehat{\mathcal O}^\times
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

For an object $x$ over $\overline E$, its field of moduli is the fixed field of

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

**Proof.** Choose the unique isomorphism (6.2) for each $\sigma$ in the stabilizer. Uniqueness gives (6.3). Effective descent for projective varieties and finite morphisms descends the abelian variety, its group law, the polarization homomorphism, the order action, and the finite level sections. $\square$

The descended polarization is the homomorphism $A\to A^\vee$. A particular ample line bundle inducing it can have a separate scalar descent issue; polarized moduli do not require that line bundle as part of the datum.

### 6.3 The canonical descent datum

Let $H_x/E$ be the class field of Section 5. For $\sigma\in G_{H_x}$, choose an idele $s_\sigma$ mapping to its abelianized restriction. Membership in the stabilizer gives a unique isomorphism

$$
\varphi_\sigma:r_\Phi(s_{\sigma,f})*x\xrightarrow{\sim}x. \tag{6.4}
$$

Compose this with the reciprocity comparison $x^\sigma\simeq r_\Phi(s_{\sigma,f})*x$. The result is independent of the idele choice and obeys (6.3). This is the **canonical CM descent datum**.

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
r_x:operatorname{Res}_{E/\mathbf Q}\mathbf G_m
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

**Proof.** Fix a finite place $w$ of $L$. After a finite extension $L'/L$, the abelian variety has semistable reduction at a place $w'$ above $w$, and all CM endomorphisms are defined. For $\ell$ different from the residue characteristic, the inertia action on $V_\ell(A)$ is then unipotent. By (8.2) it is multiplication by elements of the étale algebra $K\otimes\mathbf Q_\ell$, hence semisimple. Therefore inertia acts trivially. The Néron--Ogg--Shafarevich criterion says that an abelian variety has good reduction precisely when inertia acts trivially on one such Tate module. Thus $A$ has good reduction over $L'_{w'}$. $\square$

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

When $A$ is a canonical CM object covered by Theorem 4.1, local-global reciprocity gives a more explicit version of (8.4), but a principal correction must be retained. Let $v$ be the place of $E$ below $w$. For $u\in\mathcal O_{L_w}^\times$, form $N_{L_w/E_v}(u)$ and its reflex image. Since $u$ lies in inertia, the associated ideal transform fixes the isomorphism class of the descended CM object. Choose the unique principal factor $a(u)\in K^\times$ compatible with the rigidification. In a fixed CM basis the inertia character is

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

The least $n\geq0$ for which $\psi_w$ is trivial on $1+\mathfrak m_w^n$ is its local conductor exponent. It is zero exactly when the character is unramified, hence exactly when $A$ has good reduction under the standing CM hypotheses. This turns the geometric criterion into the same unit-filtration language used by local class field theory.

### 8.4 Integral CM data and excluded primes

Assume the order is maximal at the residue characteristic $p$, the polarization degree and level are prime to $p$, the ambient lattice is self-dual at $p$, and the class field of definition is unramified at the place under consideration. These assumptions make the integral moduli datum unramified, but good reduction of a chosen abelian variety also requires the CM descent character (8.5) to be unramified. We include its conductor among the bad primes. Outside this enlarged finite set, (8.6) gives good reduction.

Why is this conductor set finite? The model $A/L$ is an abelian variety over a number field, so it extends to an abelian scheme over a nonempty open subscheme of the integers of $L$. At every omitted prime smooth proper base change makes the prime-to-$p$ Tate representation unramified. Equivalently, the compatible CM characters $\psi_w$ are unramified there. Thus adding their conductor does not turn the bad set into an infinite or circular condition.

If any assumption fails, a different conclusion may still hold, but it requires separate work:

- a conductor prime may make the order action nonfree on the integral Tate or Dieudonné module;
- a prime dividing the polarization degree can make the polarization kernel non-étale;
- a level prime requires a finite flat level structure rather than geometric torsion points;
- a ramified field of definition has nontrivial inertia even if the underlying abelian variety happens to have good reduction;
- an ambient integral model can be singular despite good reduction of the abelian variety.

Thus “good CM prime” means good for a specified package, not merely unramified in $K$.

## 9. Unramified primes and Frobenius

At a good unramified prime, the reciprocity theorem becomes an isogeny formula. Iterating that isogeny around the residue-field orbit turns it into the Frobenius endomorphism. The resulting ideal identity is the most useful finite-place form of complex multiplication.

### 9.1 The Frobenius ideal relation

Let $x=(A,\iota,\lambda,\eta)$ be a rigidified CM datum defined over its class field $H/E$. Let $v$ be a finite place of $E$ satisfying all of the following:

1. $H/E$ is unramified at $v$;
2. $v$ lies outside the integral bad set of Section 2.5;
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

**Proof.** Work over the completed maximal unramified extension at $w$. Because the residue characteristic is outside the discriminant and conductor, the integral CM algebra splits étale-locally into factors indexed by its $p$-adic embeddings. The covariant Dieudonné module of the special fiber decomposes accordingly:

$$
M=\bigoplus_{\tau:K\hookrightarrow\overline{\mathbf Q}_p}M_\tau.
$$

The determinant condition says exactly which summands occur in the Hodge quotient attached to $\operatorname{Lie}\widetilde A$: they are the $p$-adic transports of the embeddings in $\Phi$. Relative Frobenius sends the $\tau$-summand toward the arithmetic-Frobenius translate of $\tau$, and its elementary divisor is $p$ precisely when that translated summand occurs in the Hodge quotient. Following one residue-Frobenius step, the exponent with which a prime component occurs is therefore

$$
m(\rho,\tau)=1
\quad\Longleftrightarrow\quad
\gamma_\rho^{-1}\tau\in\Phi.
$$

This is the inverse-incidence matrix defining $r_\Phi$. Hence the finite flat kernel of relative Frobenius and the finite flat kernel of the $R_\Phi(\mathfrak p_v)$-isogeny have the same Dieudonné submodule. The Dieudonné functor is faithful on finite commutative $p$-power group schemes over the perfect residue field, so the kernels, and therefore the quotient isogenies, agree. Their prime-to-$p$ parts are both trivial. $\square$

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

**Proof.** Each arrow in (9.4) is the integral isogeny attached to $\mathfrak c_v$. Its analytic lattice changes by $\mathfrak c_v^{-1}$. After $f$ steps the target lattice is $\mathfrak c_v^{-f}\mathfrak a$. Because $\sigma^f$ fixes the chosen point over the residue field, the composite is an endomorphism. Under the rank-one $K$-description, an endomorphism carrying $\mathfrak c_v^{-f}\mathfrak a$ back to $\mathfrak a$ is multiplication by an element whose principal ideal is $\mathfrak c_v^f$. By the Frobenius-comparison lemma, the reductions of the arrows are the successive relative $q_v$-Frobenius maps, so their composite is $\pi_w$.

Every element of $K$ is defined over $H$ and hence its reduction commutes with $\pi_w$. On a prime-to-$p$ Tate module, $K$ is a maximal commutative semisimple subalgebra of dimension $2g$; its centralizer is itself. Thus $\pi_w\in K$, and the lattice computation gives (9.5). $\square$

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

**Proof.** The isocrystal with $K_\mathfrak q$-action is isoclinic because it is one-dimensional over the field factor $K_\mathfrak q$ after a splitting extension. Frobenius acts there by $\pi_w$, so its slope is the valuation of $\pi_w$ divided by the valuation of the scalar $q_w$. Equation (10.1) and $q_w=q_v^f$ give the second equality. Equation (10.2) gives (10.4). The underlying $\mathbf Q_p$-dimension of the factor is $[K_\mathfrak q:\mathbf Q_p]$, which gives the multiplicity. $\square$

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

but a uniformizer chooses only a lift of residue Frobenius and units move that lift through inertia. The correct ramified statement is therefore the full local comparison

$$
\rho(T)(\operatorname{rec}_{E_v}(s))
\quad\text{is governed by}\quad r_\Phi(s),
\qquad s\in E_v^\times, \tag{11.2}
$$

on prime-to-$p$ Tate modules and level data. There is no canonical replacement of (9.5) using only $\mathfrak p_v$.

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

   with arithmetic Artin reciprocity and inverse lattice action.

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

**Proof.** Assertion 1 is Theorem 4.1. The compatibility in assertion 2 follows from the weight identity, the level calculation, and functoriality of the reflex norm. Sections 5 and 6 prove assertion 3. Theorem 8.1 proves assertion 4. The orbit composition in Theorem 9.1 and the polarization identity prove assertion 5. The regular representation calculation and Theorem 10.1 prove assertion 6. $\square$

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

and arithmetic class field theory turns an idele of $E$ into a Galois automorphism. The torsion comparison proves that these meet in the inverse lattice transform

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
