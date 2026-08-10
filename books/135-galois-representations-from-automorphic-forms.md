# Galois Representations Attached to Weight-Two Automorphic Forms

## Contents

1. [The reciprocity problem](#1-the-reciprocity-problem)
   - [From Hecke numbers to Galois matrices](#11-from-hecke-numbers-to-galois-matrices)
   - [Standing fields and Frobenius conventions](#12-standing-fields-and-frobenius-conventions)
   - [The normalization ledger](#13-the-normalization-ledger)
2. [The automorphic input](#2-the-automorphic-input)
   - [Cohomological cusp representations](#21-cohomological-cusp-representations)
   - [Eigenforms and coefficient fields](#22-eigenforms-and-coefficient-fields)
   - [A finite place of coefficients](#23-a-finite-place-of-coefficients)
   - [Why cuspidality and algebraicity are indispensable](#24-why-cuspidality-and-algebraicity-are-indispensable)
3. [The geometric receptacle](#3-the-geometric-receptacle)
   - [Weight two and the Jacobian](#31-weight-two-and-the-jacobian)
   - [Higher weight and the lisse coefficient system](#32-higher-weight-and-the-lisse-coefficient-system)
   - [Parabolic cohomology and the boundary](#33-parabolic-cohomology-and-the-boundary)
   - [Shimura curves and nonparallel weights](#34-shimura-curves-and-nonparallel-weights)
4. [Two commuting symmetries](#4-two-commuting-symmetries)
   - [Hecke and Galois actions](#41-hecke-and-galois-actions)
   - [Abstract, image, and scalar Hecke algebras](#42-abstract-image-and-scalar-hecke-algebras)
   - [Localization is not an eigenspace](#43-localization-is-not-an-eigenspace)
   - [Coefficient extension](#44-coefficient-extension)
5. [Rational extraction of a two-dimensional factor](#5-rational-extraction-of-a-two-dimensional-factor)
   - [The automorphic decomposition](#51-the-automorphic-decomposition)
   - [Multiplicity one with exact hypotheses](#52-multiplicity-one-with-exact-hypotheses)
   - [Eigenspaces, quotients, and duality](#53-eigenspaces-quotients-and-duality)
   - [What goes wrong at old level](#54-what-goes-wrong-at-old-level)
6. [The good-prime polynomial](#6-the-good-prime-polynomial)
   - [The geometric relation recalled](#61-the-geometric-relation-recalled)
   - [Arithmetic Frobenius on the covariant realization](#62-arithmetic-frobenius-on-the-covariant-realization)
   - [The weight and character conversion](#63-the-weight-and-character-conversion)
   - [Why annihilation becomes a characteristic polynomial](#64-why-annihilation-becomes-a-characteristic-polynomial)
7. [Continuity, ramification, and uniqueness](#7-continuity-ramification-and-uniqueness)
   - [Continuity inherited from geometry](#71-continuity-inherited-from-geometry)
   - [Finite ramification](#72-finite-ramification)
   - [Chebotarev and semisimplification](#73-chebotarev-and-semisimplification)
   - [A reducible warning](#74-a-reducible-warning)
8. [Polarization and determinant](#8-polarization-and-determinant)
   - [The pairing on the extracted factor](#81-the-pairing-on-the-extracted-factor)
   - [Contragredients and essential self-duality](#82-contragredients-and-essential-self-duality)
   - [Determinants from two independent directions](#83-determinants-from-two-independent-directions)
   - [Complex conjugation and oddness](#84-complex-conjugation-and-oddness)
9. [Stable lattices and residual representations](#9-stable-lattices-and-residual-representations)
   - [Constructing a stable lattice](#91-constructing-a-stable-lattice)
   - [Reduction and dependence on the lattice](#92-reduction-and-dependence-on-the-lattice)
   - [Absolute irreducibility tests](#93-absolute-irreducibility-tests)
   - [A lattice counterexample](#94-a-lattice-counterexample)
10. [Integral extraction without a direct summand](#10-integral-extraction-without-a-direct-summand)
    - [The localized cohomology lattice](#101-the-localized-cohomology-lattice)
    - [Pseudorepresentations and Cayley--Hamilton algebras](#102-pseudorepresentations-and-cayley--hamilton-algebras)
    - [Specialization to one eigensystem](#103-specialization-to-one-eigensystem)
    - [Residual irreducibility upgrades the construction](#104-residual-irreducibility-upgrades-the-construction)
11. [Local behavior away from the coefficient prime](#11-local-behavior-away-from-the-coefficient-prime)
    - [Good places](#111-good-places)
    - [Level primes and inertia](#112-level-primes-and-inertia)
    - [Steinberg and supercuspidal regimes](#113-steinberg-and-supercuspidal-regimes)
    - [The precise boundary of local compatibility](#114-the-precise-boundary-of-local-compatibility)
12. [Places above the coefficient prime](#12-places-above-the-coefficient-prime)
    - [Why good reduction no longer means unramified](#121-why-good-reduction-no-longer-means-unramified)
    - [The weight-two finite-flat statement](#122-the-weight-two-finite-flat-statement)
    - [Ordinary and supersingular examples](#123-ordinary-and-supersingular-examples)
    - [What is not being asserted](#124-what-is-not-being-asserted)
13. [Twists, conjugation, and change of coefficients](#13-twists-conjugation-and-change-of-coefficients)
    - [Twisting both sides](#131-twisting-both-sides)
    - [Automorphisms of the coefficient field](#132-automorphisms-of-the-coefficient-field)
    - [Changing the place above $\ell$](#133-changing-the-place-above-ell)
14. [Three geometric settings](#14-three-geometric-settings)
    - [Classical modular forms over $\mathbf Q$](#141-classical-modular-forms-over-mathbf-q)
    - [Hilbert forms in the curve-realizable range](#142-hilbert-forms-in-the-curve-realizable-range)
    - [Quaternionic forms and transfer](#143-quaternionic-forms-and-transfer)
15. [Hecke algebras acting on families](#15-hecke-algebras-acting-on-families)
    - [A pseudorepresentation over the local Hecke algebra](#151-a-pseudorepresentation-over-the-local-hecke-algebra)
    - [The density argument](#152-the-density-argument)
    - [From a family determinant to a family representation](#153-from-a-family-determinant-to-a-family-representation)
    - [Reducible residual systems](#154-reducible-residual-systems)
16. [The theorem package](#16-the-theorem-package)
    - [The curve-realization theorem](#161-the-curve-realization-theorem)
    - [The integral and residual theorem](#162-the-integral-and-residual-theorem)
    - [The family theorem](#163-the-family-theorem)
17. [Three worked examples](#17-three-worked-examples)
    - [An elliptic-curve form](#171-an-elliptic-curve-form)
    - [A higher-weight modular form](#172-a-higher-weight-modular-form)
    - [A quaternionic eigensystem](#173-a-quaternionic-eigensystem)
18. [A construction protocol and its failure tests](#18-a-construction-protocol-and-its-failure-tests)
    - [The protocol](#181-the-protocol)
    - [Normalization and multiplicity audits](#182-normalization-and-multiplicity-audits)
    - [Local and integral audits](#183-local-and-integral-audits)
19. [Toward deformation rings and compatible systems](#19-toward-deformation-rings-and-compatible-systems)
    - [The deformation-theoretic bridge](#191-the-deformation-theoretic-bridge)
    - [The compatible-system bridge](#192-the-compatible-system-bridge)
    - [Conclusion](#193-conclusion)

## 1. The reciprocity problem

### 1.1 From Hecke numbers to Galois matrices

An eigenform presents arithmetic as a list of scalars. At almost every finite place $v$ there is a Hecke eigenvalue $a_v$ and a second scalar $d_v$ coming from the center. A two-dimensional Galois representation presents arithmetic differently: it assigns a matrix to every element of an enormous profinite group. The reciprocity problem asks whether these two descriptions are shadows of one object, in the precise sense that

$$
\det\bigl(X-\rho(\operatorname{Frob}_v)\bigr)
=X^2-a_vX+d_v
$$

at every good place.

This is a surprisingly rigid request. The good Frobenius classes are dense, so their traces determine a semisimple representation. Yet density does not create the representation. Geometry supplies existence: an arithmetic curve has first étale cohomology, Galois acts on it, and Hecke correspondences commute with that action. The task is to isolate the two dimensions carrying the chosen eigensystem and to do so without losing integral information.

There are consequently three layers. Over a characteristic-zero coefficient field, automorphic multiplicity one and duality cut out the desired two-dimensional factor. Over a valuation ring, eigenspaces may collide and cease to split; localization, stable lattices, and Cayley--Hamilton identities replace diagonalization. At bad places, the global polynomial no longer determines inertia, so geometric reduction and the local automorphic classification must be invoked with their exact hypotheses.

This book develops those layers as one construction. Weight two is central because the representation is literally a factor of a Jacobian Tate module. Higher cohomological weights enter through a lisse coefficient system, and quaternionic forms enter after the transfer established earlier. The final result is an individual representation, its residual semisimplification, and a two-dimensional pseudorepresentation over a local Hecke algebra. A theory relating all coefficient primes simultaneously, and the deformation arguments that exploit the local Hecke algebra, lie beyond this endpoint.

### 1.2 Standing fields and Frobenius conventions

Let $F$ be a totally real number field, $G_F=\operatorname{Gal}(\overline F/F)$, and $v$ a finite place with residue cardinality $q_v$. Write $D_v\subset G_F$ for a decomposition group and $I_v$ for inertia. Our **arithmetic Frobenius** is the class

$$
\operatorname{Frob}_v:x\longmapsto x^{q_v}
$$

in $D_v/I_v$. Geometric Frobenius is its inverse. The cyclotomic character $\chi_\ell:G_F\to\mathbf Z_\ell^\times$ therefore satisfies

$$
\chi_\ell(\operatorname{Frob}_v)=q_v
\qquad(v\nmid\ell).
$$

Tate modules are covariant. For an abelian variety $A/F$,

$$
T_\ell A=\varprojlim_n A[\ell^n](\overline F),
$$

and a homomorphism $A\to B$ induces $T_\ell A\to T_\ell B$. For a smooth proper curve $X$ with Jacobian $J$,

$$
T_\ell J\simeq H^1(X_{\overline F},\mathbf Z_\ell(1)),
\qquad
H^1(X_{\overline F},\mathbf Z_\ell)\simeq T_\ell J(-1).
$$

These declarations settle the direction of every later twist. In particular, the usual elliptic-curve representation on $T_\ell E$ has determinant $\chi_\ell$ and arithmetic-Frobenius polynomial $X^2-a_vX+q_v$.

We write $E_\pi$ for a number field of Hecke eigenvalues, $\lambda\mid\ell$ for a finite place of $E_\pi$, $E_\lambda$ for its completion, $\mathcal O_\lambda$ for its valuation ring, $\varpi_\lambda$ for a uniformizer, and $k_\lambda$ for its residue field. A bar denotes reduction modulo $\varpi_\lambda$, while a superscript $\mathrm{ss}$ denotes semisimplification.

### 1.3 The normalization ledger

Book 122 used the unnormalized right-double-coset operators $T_v$ and the scalar correspondence $S_v$. On untwisted cohomology its geometric Frobenius $G_v$ satisfies

$$
G_v^2-T_vG_v+q_vS_v=0. \tag{1.1}
$$

On the covariant Tate-module realization, arithmetic Frobenius $F_v$ instead satisfies

$$
F_v^2-S_v^{-1}T_vF_v+q_vS_v^{-1}=0. \tag{1.2}
$$

It is useful to name the coefficients in the arithmetic polynomial:

$$
A_v:=S_v^{-1}T_v,
\qquad
\Delta_v:=q_vS_v^{-1}. \tag{1.3}
$$

Thus a weight-two eigensystem $\theta$ gives

$$
a_v=\theta(A_v),
\qquad
d_v=\theta(\Delta_v),
$$

and not, in general, $a_v=\theta(T_v)$. For a $\Gamma_1$-type component on which the point-map diamond $\langle v\rangle$ acts by $\varepsilon(v)$, Book 122 has $S_v=\langle v\rangle^{-1}$. Consequently

$$
\theta(S_v)^{-1}=\varepsilon(v),\qquad
d_v=\varepsilon(v)q_v.
$$

The trace is also multiplied by the same inverse central scalar. This apparently fussy adjustment is forced by the orientation of the correspondence. It is the test that prevents an inverse nebentype from entering the determinant.

Following Book 92, write $w$ for the common algebraic central weight $a_\tau+b_\tau$. The associated two-dimensional Galois representation has motivic weight $w+1$, and we use the algebraic Hecke normalization in which

$$
P_{\pi,v}(X)=X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}. \tag{1.4}
$$

Here $\psi_\pi$ is the finite-order part of the algebraic central character. For a classical form of weight $k$, Book 92's convention gives $w=k-2$ and $\psi_\pi=\varepsilon$. Formula (1.2) is the case $w=0$, equivalently classical weight two, after the central conversion. The extra power in higher weight comes from the coefficient system, not from changing the meaning of Frobenius.

## 2. The automorphic input

### 2.1 Cohomological cusp representations

Geometry does not realize an arbitrary smooth automorphic representation. Its archimedean component must carry algebraic data that can be encoded by a finite-dimensional coefficient system. Let

$$
\pi=\bigotimes_v'\pi_v
$$

be a cuspidal automorphic representation of $\mathrm{GL}_2(\mathbf A_F)$. We assume it is regular algebraic and cohomological. At each real embedding $\tau:F\hookrightarrow\mathbf R$, its archimedean factor is the discrete-series representation associated with an integer $k_\tau\ge2$. There is an integer $w$ such that

$$
k_\tau\equiv w\pmod2
$$

for every $\tau$, and the algebraic central character has finite-order part $\psi_\pi$ and norm part determined by $w$.

The tuple $((k_\tau),w)$ is not decorative bookkeeping. The integers $k_\tau-2$ are symmetric-power degrees in the coefficient system, while

$$
b_\tau=\frac{w-k_\tau+2}{2}
$$

supplies the determinant twists that make the coefficient system descend and give the same total motivic weight at every embedding. Indeed, if $a_\tau-b_\tau=k_\tau-2$ and $a_\tau+b_\tau=w$, then the displayed formula is forced. The parity condition is precisely what makes these exponents integral.

For the main geometric construction we impose a **curve-realization hypothesis**: $\pi$ occurs in the cuspidal cohomology of a modular curve over $\mathbf Q$, or, after the established quaternionic transfer, in the first cohomology of a quaternionic Shimura curve with the algebraic local system dictated by $((k_\tau),w)$. This includes classical modular forms, Hilbert forms whose local components satisfy the transfer condition for a quaternion algebra split at exactly one real place, and automorphic eigensystems already living on such a quaternionic curve. It does not assert that every Hilbert form is realized on a curve; general Hilbert modular varieties have dimension $[F:\mathbf Q]$.

### 2.2 Eigenforms and coefficient fields

Choose a sufficiently small level $K\subset\mathrm{GL}_2(\mathbf A_{F,f})$, or its quaternionic counterpart, and a vector in the $K$-fixed new line or specified local-type space. Away from a finite set $\Sigma$ containing the conductor, the discriminant of the quaternion algebra, and all auxiliary level, the spherical Hecke algebra acts through a character

$$
\theta_\pi:\mathbb T^{\Sigma,\mathrm{abs}}\longrightarrow\overline{\mathbf Q}.
$$

The **coefficient field** $E_\pi$ is generated by the algebraically normalized values $a_v(\pi)$ and the values of $\psi_\pi$ for $v\notin\Sigma$. Strong multiplicity one shows that the almost-everywhere eigensystem determines $\pi$, but it does not by itself show that a cohomological vector or the whole infinite-dimensional representation has a model over exactly $E_\pi$. What we require is the finite-dimensional Hecke eigensystem and its cohomological realization; after enlarging $E_\pi$ finitely, these are defined over it.

For a normalized classical newform

$$
f(q)=\sum_{n\ge1}a_n(f)q^n
$$

of weight $k$, level $N$, and nebentype $\varepsilon$, one may take

$$
E_f=\mathbf Q(a_n(f):n\ge1).
$$

At $p\nmid N$ the algebraic polynomial is

$$
X^2-a_p(f)X+\varepsilon(p)p^{k-1}.
$$

The unitary Satake parameters are obtained by dividing its roots by $p^{(k-1)/2}$. We never insert that unitary shift into a Galois polynomial.

### 2.3 A finite place of coefficients

Fix an embedding $E_\pi\hookrightarrow\overline{\mathbf Q}_\ell$, equivalently a place $\lambda\mid\ell$, and enlarge $E_\lambda$ when necessary to contain all eigenvalues and split the relevant semisimple Hecke algebra. The desired representation will be

$$
\rho_{\pi,\lambda}:G_F\longrightarrow
\mathrm{GL}_2(E_\lambda).
$$

The choice of $\lambda$ matters locally: it selects a completion, a topology, and a residue field. It does not change the algebraic numbers $a_v(\pi)$. At a good $v\nmid\ell$, these algebraic numbers are simply viewed in $E_\lambda$, and the expected identity is

$$
\det\bigl(X-\rho_{\pi,\lambda}(\operatorname{Frob}_v)\bigr)
=X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}. \tag{2.1}
$$

One must distinguish three scalar extensions. Passing from $E_\pi$ to $E_\lambda$ completes at a place. Passing further to a finite extension of $E_\lambda$ may split idempotents or residual endomorphism algebras. Extending the residue field changes the field over which absolute irreducibility is tested. None of these operations changes the good-prime polynomial; they change only the field in which it is interpreted.

### 2.4 Why cuspidality and algebraicity are indispensable

Two counterexamples locate the hypotheses. The constant function on a compact quaternionic quotient is a Hecke eigenfunction, often with $T_v$-eigenvalue $q_v+1$. Its formal polynomial factors as

$$
(X-1)(X-q_v),
$$

the Eisenstein pattern. It does not contribute a cuspidal two-dimensional factor of first cohomology. Removing the norm-character block on the quaternionic side is therefore essential.

At the other extreme, a nonalgebraic Maass cusp form is genuinely cuspidal and has spherical Hecke eigenvalues, but no algebraic coefficient system of the above kind is available. Almost-everywhere Hecke numbers alone do not place it in étale cohomology. Cuspidality removes boundary and character phenomena; algebraicity makes an arithmetic realization possible. Neither condition substitutes for the other.

## 3. The geometric receptacle

### 3.1 Weight two and the Jacobian

Let $X/F$ be the smooth proper modular or Shimura curve realizing $\pi$, and let $J=\operatorname{Jac}(X)$. In parallel weight two with the appropriate central normalization, the coefficient system is constant. The basic Galois module is

$$
V_\ell J=T_\ell J\otimes_{\mathbf Z_\ell}\mathbf Q_\ell
\simeq H^1(X_{\overline F},\mathbf Q_\ell(1)). \tag{3.1}
$$

This is the central case for two reasons. First, it is visibly geometric: the desired representation is an isogeny factor of a Jacobian. Second, its integral lattice is not manufactured after the fact; it begins as $T_\ell J$. Polarization, torsion, good reduction, and specialization are consequently available at once.

For a modular curve with cusps, $X$ denotes the compactification. Weight-two cusp forms occur in the interior part of $H^1(X)$; the Jacobian automatically discards degree-zero boundary artifacts. For a compact Shimura curve there is no cusp boundary. A genus-zero curve is a useful warning: its Hecke correspondences can be rich, but $J=0$ and no weight-two cuspidal representation is extracted from its $H^1$.

The covariant choice (3.1) is deliberate. If one extracted from untwisted $H^1$, the result would be the dual Tate module and the arithmetic-Frobenius roots would be inverted and divided by $q_v$. The Tate twist in (3.1) puts the elliptic-curve polynomial in its familiar arithmetic form.

### 3.2 Higher weight and the lisse coefficient system

Constant coefficients see only weight two. To realize weight $k>2$, the cohomology must remember how the universal elliptic or abelian object varies over the curve. On a modular curve $Y$ with universal elliptic curve $f:\mathcal E\to Y$, put

$$
\mathcal H_\lambda=R^1f_*\mathcal O_\lambda(1).
$$

Its geometric fiber is the covariant $\lambda$-adic Tate module of the elliptic fiber. For classical weight $k$, set

$$
\mathcal L_{k,\lambda}=\operatorname{Sym}^{k-2}\mathcal H_\lambda.
$$

The covariant cohomological realization is

$$
H^1_!\left(Y_{\overline F},\mathcal L_{k,\lambda}\right)(1). \tag{3.2}
$$

Indeed, $\mathcal H_\lambda$ already contains one twist for each of its $k-2$ tensor factors, and the outer $(1)$ supplies the curve direction. Relative to the fully untwisted cohomology of the corresponding fiber power, the total covariant twist is therefore $(k-1)$. In weight two, (3.2) reduces to (3.1); at good primes its determinant is $\varepsilon\chi_\ell^{k-1}$.

For a quaternionic Shimura curve over a totally real field, there is one split real place contributing the curve direction. The symmetric-power data at all archimedean places, including the split one, are encoded by an algebraic representation of the quaternionic group. If $n_\tau=k_\tau-2$ and $m_\tau=(w-k_\tau+2)/2$, the coefficient representation is built from

$$
\bigotimes_\tau
\left(\operatorname{Sym}^{n_\tau}\mathrm{Std}_\tau
\otimes\det^{m_\tau}\right), \tag{3.3}
$$

followed by the descent dictated by the moduli datum. We use the covariant relative-Tate realization of this representation; its $\lambda$-adic incarnation is a lisse sheaf $\mathcal L_{\mathbf k,w,\lambda}$. Formula (3.3) explains both the symmetric powers and the parity condition. Omitting the determinant exponent changes the central character and hence the determinant of the resulting Galois representation.

The required cohomology is

$$
H^1_{!}(Y_{\overline F},\mathcal L_{\mathbf k,w,\lambda})(1). \tag{3.4}
$$

The displayed outer twist is the covariant curve twist, just as in (3.2); it is not already hidden in $\mathcal L_{\mathbf k,w,\lambda}$. In the proper quaternionic case $H^1_!=H^1$. The construction may alternatively be obtained from a projector on the cohomology of a fiber power of the universal abelian scheme. That description makes geometric origin vivid; the lisse-sheaf description keeps the degree-one argument visible.

### 3.3 Parabolic cohomology and the boundary

Why use $H^1_!$ rather than ordinary cohomology of the open modular curve? Let $j:Y\hookrightarrow X$ be the compactification. Define

$$
H^1_!(Y_{\overline F},\mathcal L)
=\operatorname{im}\left(
H^1_c(Y_{\overline F},\mathcal L)
\longrightarrow H^1(Y_{\overline F},\mathcal L)
\right). \tag{3.5}
$$

The source suppresses sections escaping through the cusps, while the target suppresses compact-support artifacts. Their image is the self-dual interior contribution. In weight two it agrees with the cohomology of the compactification in the cuspidal range.

Ordinary $H^1(Y,\mathcal L)$ also contains boundary cohomology. Boundary classes can have Hecke polynomials that split into characters, mimicking a reducible two-dimensional system. If one extracted from the full open-curve group without removing this part, an Eisenstein eigensystem could be mistaken for a cuspidal Galois representation. Parabolic cohomology solves exactly that problem and is stable under Hecke and Galois.

Poincaré duality pairs the coefficient system with its dual and produces a perfect characteristic-zero pairing between the $\pi$ and $\pi^\vee$ parts, with a Tate twist determined by $w$. Integral perfectness requires a self-dual lattice and may fail at primes dividing its discriminant. We will use characteristic-zero duality for dimension and state integral self-duality only when that discriminant is a unit.

### 3.4 Shimura curves and nonparallel weights

A curve has only one complex tangent direction, so it may seem unable to carry a tuple of Hilbert weights. The quaternionic construction separates the roles. The unique split real place supplies degree-one cohomology; compact real factors contribute finite-dimensional algebraic representations, which become part of the local system. Thus nonparallel weights are not additional cohomological degrees.

There is nevertheless an exact transfer restriction. To move a Hilbert cusp representation $\pi$ to a quaternion algebra $D$, every place where $D$ is ramified must carry a discrete-series local component of $\pi$. At ramified real places this holds for cohomological discrete series. If parity forces $D$ to ramify at an extra finite place, $\pi$ must be discrete series there as well. A spherical principal series at that place has no quaternionic preimage. Good-prime Hecke agreement cannot repair this local failure.

When the restriction is met, global transfer preserves the coefficient field, central character, twists, contragredient, and all split-place Hecke polynomials. The representation extracted from the quaternionic curve is therefore attached to the original split-group representation, not merely to an unrelated form with similar eigenvalues.

## 4. Two commuting symmetries

### 4.1 Hecke and Galois actions

Let $M_\lambda$ denote a Hecke-stable torsion-free integral parabolic cohomology lattice, obtained from integral cohomology by quotienting coefficient torsion and saturating inside its characteristic-zero realization, or let $M_\lambda=T_\ell J\otimes_{\mathbf Z_\ell}\mathcal O_\lambda$ in weight two. This convention deliberately excludes purely torsion cohomology classes, which need not lift to the characteristic-zero eigensystems studied here. The lattice carries two actions:

$$
G_F\longrightarrow\operatorname{Aut}_{\mathcal O_\lambda}(M_\lambda),
\qquad
\mathbb T\longrightarrow\operatorname{End}_{\mathcal O_\lambda}(M_\lambda). \tag{4.1}
$$

Every Hecke correspondence is defined over the arithmetic base. Pullback and trace are therefore Galois equivariant, so

$$
g(tm)=t(gm)
\qquad(g\in G_F, t\in\mathbb T, m\in M_\lambda). \tag{4.2}
$$

This elementary commutation is the hinge of the construction. If $W\subset M_\lambda\otimes E_\lambda$ is defined by simultaneous Hecke equations, then (4.2) makes $W$ Galois stable. If $Q$ is a Hecke quotient, its kernel is Galois stable and $Q$ inherits a Galois action. If the Hecke algebra is localized at a maximal ideal, the localized module remains a Galois module.

The actions must live on the same realization. An equality of abstract Hecke eigenvalues on automorphic forms and a Galois action on cohomology are not enough until Book 122's comparison identifies the geometric pull--trace operator with the same right-double-coset operator. That comparison also retains stabilizer multiplicities and the central operator $S_v$.

### 4.2 Abstract, image, and scalar Hecke algebras

Three rings recur. The abstract away-from-$\Sigma$ algebra is generated formally by $T_v,S_v^{\pm1}$. Its image on $M_\lambda$ is a finite $\mathcal O_\lambda$-algebra

$$
\mathbb T_M\subseteq\operatorname{End}_{\mathcal O_\lambda}(M_\lambda).
$$

After fixing the central character, one may quotient further so that $S_v$ acts by its prescribed scalar. These rings need not have the same kernels on different levels or coefficient systems.

Localization must use the faithful image appropriate to the chosen lattice. Let $\mathfrak m\subset\mathbb T_M$ be the maximal ideal cut out by the residual eigenvalues. Then

$$
M_{\mathfrak m}=M_\lambda\otimes_{\mathbb T_M}(\mathbb T_M)_{\mathfrak m} \tag{4.3}
$$

retains all characteristic-zero eigensystems congruent to $\pi$. It is generally larger than the reduction attached to one eigenform. This is a feature: congruences are precisely the integral information needed later.

### 4.3 Localization is not an eigenspace

For a characteristic-zero character $\theta:\mathbb T_M\to E_\lambda$, the ordinary eigenspace is

$$
M_{E_\lambda}[\theta]
=\{m:(t-\theta(t))m=0\text{ for every }t\}. \tag{4.4}
$$

The generalized eigenspace permits a power of each $t-\theta(t)$ to kill $m$. The localization $M_{\mathfrak m}$ is larger still: it retains every generalized characteristic-zero packet whose reduction has support at $\mathfrak m$.

A two-by-two example makes the distinction unavoidable. Let one operator act over $\mathcal O_\lambda$ by

$$
C=\begin{pmatrix}0&1\\0&\varpi_\lambda\end{pmatrix}.
$$

Its two characteristic-zero eigenvalues are $0$ and $\varpi_\lambda$, but modulo $\varpi_\lambda$ the operator is a nonzero nilpotent. There is one residual ordinary eigenline, a two-dimensional residual generalized eigenspace, and one localization containing both generic branches. Declaring the residual eigenspace to be the localized module would discard the nilpotent extension and miscount dimensions.

### 4.4 Coefficient extension

Suppose $L/E_\lambda$ is finite. Flatness gives

$$
M_{\mathfrak m}\otimes_{\mathcal O_\lambda}\mathcal O_L
$$

with the same commuting actions, and after inverting the uniformizer the semisimple Hecke algebra may split into field factors. Idempotents can then isolate a character. Descent back to $E_\lambda$ follows when the character values and traces lie in $E_\lambda$ and the resulting absolutely irreducible representation has scalar endomorphisms.

Extension is harmless for characteristic polynomials but not invisible integrally. A lattice may become self-dual only after ramified extension; the residue field may enlarge; a representation irreducible over $k_\lambda$ may become reducible over its algebraic closure. Hence statements about residual irreducibility will always say **absolute** irreducibility when that is what is used.

## 5. Rational extraction of a two-dimensional factor

### 5.1 The automorphic decomposition

Over a splitting field of characteristic zero, cuspidal cohomology decomposes by automorphic representations. Schematically,

$$
H^1_!(Y_{\overline F},\mathcal L)\otimes E_\lambda
\cong
\bigoplus_{\pi'}
(\pi'_f)^K\otimes R_{\pi',\lambda}, \tag{5.1}
$$

where $R_{\pi',\lambda}$ is the Galois multiplicity space. In the curve-realizable regular cohomological range, the contribution of the selected archimedean cohomological type has dimension two. The finite fixed-vector factor records oldform or local-type multiplicity; it is not part of the desired Galois dimension.

The strategy is therefore clear. Choose level and local types so that the $\pi_f$-isotypic finite factor is one dimensional, use global multiplicity one to exclude a second automorphic copy, and use duality to show the remaining multiplicity space has exactly the two expected dimensions. Then the simultaneous Hecke eigenspace or its dual quotient is $R_{\pi,\lambda}$.

This argument is more than a dimension count. It identifies which factor Galois acts on. Hecke acts on $(\pi_f)^K$ by the chosen character and trivially on $R_{\pi,\lambda}$; Galois acts on $R_{\pi,\lambda}$ and commutes with the Hecke factor.

### 5.2 Multiplicity one with exact hypotheses

**Two-dimensional extraction theorem.** Assume:

1. $\pi$ is cuspidal, regular algebraic, and lies in the curve-realizable range;
2. the chosen Hecke module is parabolic or cuspidal cohomology with the correct coefficient system;
3. at each finite place in the level, a new line or a specified local type of multiplicity one has been selected;
4. the chosen archimedean cohomological type occurs with multiplicity one;
5. the away-from-$\Sigma$ eigensystem separates $\pi$ from other cuspidal representations, by strong multiplicity one;
6. coefficient scalars have been enlarged enough to split the relevant characteristic-zero Hecke factor.

Then the $\theta_\pi$-isotypic cohomological quotient, after removing the finite fixed-vector line, is a two-dimensional $E_\lambda$-space stable under $G_F$.

**Proof strategy.** First decompose the characteristic-zero cuspidal cohomology spectrally. Global multiplicity one gives one copy of $\pi$. Local newvector or type multiplicity one makes its chosen finite-level line one dimensional. Relative Lie-algebra cohomology at the unique split real place contributes the holomorphic and antiholomorphic, equivalently the two Galois, dimensions. Poincaré duality pairs this contribution nondegenerately with the contragredient contribution and excludes a hidden radical. Strong multiplicity one shows that no different $\pi'$ shares every away-from-$\Sigma$ eigenvalue. Thus the Hecke-isotypic multiplicity space has dimension two. Commutation (4.2) makes it Galois stable. $\square$

The theorem does not say that an arbitrary fixed-level eigenspace is two dimensional. If $K$ is deeper than the conductor, $(\pi_f)^K$ can have dimension greater than one. Nor does it say that an integral localization is free of rank two over its Hecke algebra. Those are different multiplicity statements.

### 5.3 Eigenspaces, quotients, and duality

There are two natural extractions:

$$
V[\theta]=\bigcap_{t\in\mathbb T}\ker(t-\theta(t)),
\qquad
V_\theta=V\otimes_{\mathbb T,\theta}E_\lambda. \tag{5.2}
$$

The first is a subspace; the second is the largest quotient on which Hecke acts through $\theta$. They need not be canonically equal. A Hecke-equivariant perfect pairing identifies

$$
V_\theta^\vee\simeq V^\vee[\theta], \tag{5.3}
$$

with the adjoint character inserted if the operators are not self-adjoint. On a fixed central-character block, transpose sends $T_v$ to its inverse-coset adjoint, so the character on the paired side is the one belonging to $\pi^\vee$.

Under the hypotheses of Section 5.2, both sides have dimension two. One may define $\rho_{\pi,\lambda}$ on the covariant quotient $V_\theta$, or on the dual of the corresponding untwisted eigenspace. We choose the realization whose arithmetic polynomial is (2.1). This declaration avoids a silent dual or Tate twist.

### 5.4 What goes wrong at old level

Let a classical newform have conductor $N$, and view it at level $Np$ with $p\nmid N$. The two degeneracy vectors $f(z)$ and $f(pz)$ have identical Hecke eigenvalues away from $Np$. Hence the away-from-level eigenspace contains

$$
E_\lambda^2\otimes R_{f,\lambda}
$$

and has dimension four. Strong multiplicity one has not failed: there is still one automorphic representation, but it contributes a two-dimensional fixed-vector space at the enlarged level.

There are three correct repairs. Work at the new level, project to the new quotient using characteristic-zero old/new decomposition, or include enough local Hecke/type data at $p$ to select one line. Simply asserting “multiplicity one” does none of these. Integrally, the old and new lattices may meet with finite index, so the characteristic-zero projector may have a denominator. This is precisely where localization and pseudorepresentations become preferable to an integral idempotent.

## 6. The good-prime polynomial

### 6.1 The geometric relation recalled

Let $v\notin\Sigma$, $v\nmid\ell$, and assume the curve, coefficient system, and $v$-neighbor correspondence extend over a smooth proper integral model with finite locally free legs. On untwisted weight-two cohomology, Book 122 proves

$$
G_v^2-T_vG_v+q_vS_v=0, \tag{6.1}
$$

where $G_v$ is geometric Frobenius. The relation arises because the special-fiber Hecke cycle is the sum of the transpose Frobenius graph and the $S_v$-twisted forward Frobenius graph. Both branches occur with multiplicity one.

Equation (6.1) is an operator identity on the entire cohomology. It does not yet say that the quadratic is a characteristic polynomial. It also uses geometric Frobenius, untwisted cohomology, and Book 122's central convention $S_v=\langle v\rangle^{-1}$ in the modular $\Gamma_1$ case. Every one of those features changes when we pass to the desired representation.

### 6.2 Arithmetic Frobenius on the covariant realization

Let $F_v$ be arithmetic Frobenius on $T_\ell J\simeq H^1(1)$. Frobenius--Verschiebung duality gives the conversion already established:

$$
F_v^2-S_v^{-1}T_vF_v+q_vS_v^{-1}=0. \tag{6.2}
$$

One can check it algebraically. On untwisted $H^1$, the arithmetic action is inverse to $G_v$. Twisting by $(1)$ multiplies arithmetic Frobenius by $q_v$. Thus the operator on $H^1(1)$ is $F_v=q_vG_v^{-1}$. Substitute $G_v=q_vF_v^{-1}$ into (6.1), multiply by the invertible operator $q_v^{-1}S_v^{-1}F_v^2$, and obtain (6.2).

Now specialize the Hecke action through $\theta_\pi$. If $s_v=\theta_\pi(S_v)$ and $t_v=\theta_\pi(T_v)$, the extracted two-dimensional factor is annihilated by

$$
X^2-s_v^{-1}t_vX+q_vs_v^{-1}. \tag{6.3}
$$

For a nebentype $\varepsilon$, $s_v=\varepsilon(v)^{-1}$. Hence the determinant is $\varepsilon(v)q_v$, and the arithmetic trace is $\varepsilon(v)t_v$. If the classical eigenvalue is called $a_v$, the comparison of Hecke normalizations says $t_v=\varepsilon(v)^{-1}a_v$. Both corrections are necessary.

### 6.3 The weight and character conversion

For higher weight, the same correspondence acts simultaneously on the base curve and on the fibers of the coefficient system. This requires more than the constant-coefficient identity of Book 122: the lisse system, or the algebraic projector realizing it, must extend over the good integral model, and pullback--trace along the two correspondence legs must agree with the algebraically normalized Hecke action on that system. Under this coefficient-system comparison, an isogeny transports the symmetric-power tensor over the good special fiber. Each of the $k_\tau-2$ standard factors contributes its prescribed Frobenius scaling, while the determinant powers in (3.3) correct the central action. After the covariant normalization, the result is

$$
\rho_{\pi,\lambda}(\operatorname{Frob}_v)^2
-a_v(\pi)\rho_{\pi,\lambda}(\operatorname{Frob}_v)
+\psi_\pi(v)q_v^{w+1}=0. \tag{6.4}
$$

Here is the geometric calculation behind that assertion. Realize the local system as the algebraic projector on the appropriate fiber power of the universal elliptic or PEL abelian scheme. The two components of the special-fiber $v$-correspondence remain the Frobenius and Verschiebung components of Book 122, but each component now also acts on every fiber factor. Apply the symmetric-power projector and the determinant powers before passing to cohomology. The forward and transpose components then give the two roots of the standard algebraic Hecke polynomial. The $k-2$ fiber directions together with the one curve direction account for the total covariant exponent $k-1$ in the classical case; in weight $((k_\tau),w)$ the determinant factors equalize these contributions to $w+1$. Transported level still contributes the inverse of $S_v$, exactly as in (6.2).

This is not obtained by tensoring the weight-two quadratic with a symmetric power: a symmetric power of a two-dimensional operator has dimension $k-1$, whereas the desired Galois factor remains two dimensional. The projector and the degree-one cohomology select the standard two-root factor. Constant coefficients would retain only the base-curve weight-two factor and would give the wrong determinant in higher weight.

The conversion can be summarized as follows:

| realization | Frobenius named | middle coefficient | constant coefficient |
|---|---|---:|---:|
| untwisted weight-two $H^1$ | geometric $G_v$ | $T_v$ | $q_vS_v$ |
| covariant weight-two $H^1(1)$ | arithmetic $F_v$ | $S_v^{-1}T_v$ | $q_vS_v^{-1}$ |
| covariant weight $((k_\tau),w)$ factor | arithmetic $\operatorname{Frob}_v$ | $a_v(\pi)$ | $\psi_\pi(v)q_v^{w+1}$ |

There is a useful consistency test. Twisting the coefficient system by $(r)$ multiplies each arithmetic-Frobenius eigenvalue by $q_v^r$. The trace must therefore multiply by $q_v^r$ and the determinant by $q_v^{2r}$. Likewise, twisting $\pi$ by a finite-order Hecke character $\eta$ multiplies the trace by $\eta(v)$ and determinant by $\eta(v)^2$. Formula (6.4) has exactly these behaviors.

For a classical weight-$k$ form, (6.4) becomes

$$
X^2-a_v(f)X+\varepsilon(v)q_v^{k-1}. \tag{6.5}
$$

Using the raw unitary Hecke eigenvalue in the middle of (6.5) would be wrong by a power of $q_v$. Using $S_v$ rather than $S_v^{-1}$ in its constant term would replace $\varepsilon$ by $\varepsilon^{-1}$. These two errors arise from different sources and do not cancel in general.

### 6.4 Why annihilation becomes a characteristic polynomial

The geometric relation says only that a quadratic annihilates Frobenius. The extraction theorem supplies the missing dimension. On a two-dimensional vector space, a monic quadratic annihilating an operator need not always be its characteristic polynomial: a scalar operator is annihilated by many quadratics. Here the determinant is independently fixed by polarization, or equivalently both eigenvalues occur in the dual automorphic decomposition. To see the decisive point, write the characteristic polynomial as $X^2-cX+d$ and the Hecke polynomial as $X^2-aX+d$. Both annihilate the invertible Frobenius operator, so subtraction gives $(c-a)F_v=0$; hence $c=a$. Therefore

$$
\det\bigl(X-\rho_{\pi,\lambda}(\operatorname{Frob}_v)\bigr)
=P_{\pi,v}(X). \tag{6.6}
$$

Alternatively, the characteristic polynomial divides a power of the Hecke polynomial in the full cohomology. The selected automorphic constituent has degree-two standard local factor; comparison of traces on a dense set, together with the known determinant, forces equality. The dimension-two theorem is indispensable in either argument.

The conclusion immediately gives purity at good places whenever the established bounds on automorphic parameters apply: every complex embedding of a Frobenius root has absolute value $q_v^{(w+1)/2}$. We use this only as a diagnostic here, not as the foundation of extraction.

## 7. Continuity, ramification, and uniqueness

### 7.1 Continuity inherited from geometry

A representation assembled only from matrices assigned to Frobenius elements might have no topology at all. The geometric construction avoids that problem. The $\lambda$-adic cohomology lattice $M_\lambda$ is constructed from its compatible finite-coefficient systems with the inverse-limit and possible derived-limit terms controlled as in the cohomology theory of curves; it is not obtained by simply assuming that cohomology commutes with every inverse limit. Its $G_F$-action is continuous for the $\lambda$-adic topology. A Galois-stable subspace of $M_\lambda\otimes E_\lambda$ inherits the subspace topology, and a finite-dimensional quotient inherits the quotient topology. Hence

$$
\rho_{\pi,\lambda}:G_F\to\mathrm{GL}_2(E_\lambda)
$$

is continuous.

For completeness, choose a stable lattice $L$ in the extracted space. Continuity is equivalent to continuity of the action on $L$, and that follows because for every $n$ the kernel of

$$
G_F\longrightarrow\operatorname{Aut}(L/\varpi_\lambda^nL)
$$

is open. The target is finite. Thus the action is the inverse limit of finite continuous actions. This argument also applies to representations obtained from a localized Cayley--Hamilton module once that module is finite over the coefficient ring.

### 7.2 Finite ramification

Let $\Sigma$ contain the level primes, primes where the curve or coefficient datum has bad reduction, primes where the quaternion algebra or auxiliary PEL datum is ramified, primes where the central character is ramified, and primes above $\ell$. At $v\notin\Sigma$, the compactified curve and the correspondence have smooth proper reduction, while the coefficient system extends over the good open model with controlled boundary. Proper base change for the resulting constructible extensions $j_!\mathcal L$ and $Rj_*\mathcal L$ makes inertia act trivially on parabolic cohomology; in the proper constant-coefficient case this is the usual smooth proper base-change statement. Inertia therefore acts trivially on every extracted subquotient, including $\rho_{\pi,\lambda}$.

Thus $\rho_{\pi,\lambda}$ is unramified outside the finite set $\Sigma$. Enlarging $\Sigma$ is harmless for this statement but weakens it. The meaningful theorem records a set coming from the actual conductor, integral model, coefficient prime, and auxiliary choices, then removes auxiliary primes when the geometry or transfer permits.

There is no converse hidden here. A cohomological factor may be unramified at a place even when the chosen curve model is bad, because the relevant subquotient can kill the monodromy. Conversely, good reduction of a model at a place above $\ell$ does not make its $\ell$-adic Tate module unramified. The proof above explicitly excluded those places.

### 7.3 Chebotarev and semisimplification

The good-prime polynomial determines the semisimple representation uniquely.

**Chebotarev uniqueness theorem.** Let $\rho_1,\rho_2:G_F\to\mathrm{GL}_n(E)$ be continuous representations over a characteristic-zero local field, each unramified outside a finite set. If

$$
\operatorname{tr}\rho_1(\operatorname{Frob}_v)
=\operatorname{tr}\rho_2(\operatorname{Frob}_v)
$$

for all $v$ outside a finite set, then

$$
\rho_1^{\mathrm{ss}}\simeq\rho_2^{\mathrm{ss}}.
$$

**Proof strategy.** Frobenius conjugacy classes outside any finite set are dense in $G_F$. Continuity extends equality of trace from that dense set to every group element. The character of a finite-dimensional characteristic-zero representation determines its semisimplification. Applying this character criterion gives the result. $\square$

For our two-dimensional representations, equality of characteristic polynomials is stronger than equality of traces and also checks determinants. If $\rho_{\pi,\lambda}$ is known irreducible, it is already semisimple, so the good-prime polynomials determine it up to isomorphism. Without irreducibility the word “semisimplification” cannot be removed.

### 7.4 A reducible warning

Let $\alpha,\beta:G_F\to E_\lambda^\times$ be characters, and let $c$ be a nonzero class defining an extension

$$
0\longrightarrow E_\lambda(\alpha)
\longrightarrow V_c
\longrightarrow E_\lambda(\beta)
\longrightarrow0.
$$

Every matrix on $V_c$ is upper triangular with diagonal entries $\alpha(g),\beta(g)$. Hence its characteristic polynomial is

$$
(X-\alpha(g))(X-\beta(g)),
$$

independent of $c$. The split sum and every nonsplit extension have the same Frobenius polynomials at all unramified places. Chebotarev sees the semisimplification $\alpha\oplus\beta$, not the extension class. This example explains why residual representations are canonically attached to a lattice only after semisimplification and why pseudorepresentations cannot recover reducible extensions without extra data.

## 8. Polarization and determinant

### 8.1 The pairing on the extracted factor

The Jacobian carries a polarization pairing

$$
T_\ell J\times T_\ell J\longrightarrow\mathbf Z_\ell(1), \tag{8.1}
$$

and the higher-weight coefficient system carries the tensor product of its natural alternating and symmetric pairings. After cup product and trace, parabolic cohomology obtains a Galois-equivariant pairing whose multiplier is the character

$$
\mu_{\pi,\lambda}=\psi_{\pi,\lambda}\chi_\ell^{w+1}. \tag{8.2}
$$

Hecke transpose is adjoint for this pairing. Consequently the $\pi$ factor pairs perfectly with the $\pi^\vee$ factor. On a two-dimensional realization, after identifying the central-character conjugate correctly, this becomes a nondegenerate alternating pairing

$$
\langle\ ,\ \rangle_\pi:
R_{\pi,\lambda}\times R_{\pi,\lambda}
\longrightarrow E_\lambda(\mu_{\pi,\lambda}) \tag{8.3}
$$

when the automorphic data are essentially self-dual. In general it is better to regard it as a perfect pairing between $R_{\pi,\lambda}$ and $R_{\pi^\vee,\lambda}$.

The qualification about central character matters. Poincaré duality does not say that the $\theta$-eigenspace is paired with itself under the same Hecke character. It pairs an operator with its transpose, so the opposite factor carries the contragredient eigensystem. Only after twisting by the determinant character do the two become identified.

### 8.2 Contragredients and essential self-duality

Every two-dimensional representation satisfies the linear-algebra identity

$$
V^\vee\simeq V\otimes(\det V)^{-1}. \tag{8.4}
$$

For the automorphic representation this reads

$$
\rho_{\pi,\lambda}^\vee
\simeq
\rho_{\pi,\lambda}\otimes
(\psi_{\pi,\lambda}\chi_\ell^{w+1})^{-1}. \tag{8.5}
$$

It agrees with the Galois representation attached to the suitably algebraically normalized contragredient $\pi^\vee$. At a good place, the roots $\alpha_v,\beta_v$ of $P_{\pi,v}$ are replaced by $\alpha_v^{-1},\beta_v^{-1}$, followed by the norm adjustment implicit in returning to the same algebraic normalization. Formula (8.5) performs that adjustment globally.

When $\psi_\pi=1$ and $w=0$, equivalently in classical weight two, (8.5) is the familiar $V^\vee\simeq V(-1)$ for an elliptic Tate module. Calling this ordinary self-duality would omit its multiplier. The correct phrase is **polarized** or **essentially self-dual**.

### 8.3 Determinants from two independent directions

At all good places, (6.6) gives

$$
\det\rho_{\pi,\lambda}(\operatorname{Frob}_v)
=\psi_\pi(v)q_v^{w+1}.
$$

The character $\psi_{\pi,\lambda}\chi_\ell^{w+1}$ has the same value there. Chebotarev therefore yields

$$
\boxed{
\det\rho_{\pi,\lambda}
=\psi_{\pi,\lambda}\chi_\ell^{w+1}.} \tag{8.6}
$$

Here $\psi_{\pi,\lambda}$ is the $\lambda$-adic character obtained from the finite-order central character by class field theory with the arithmetic convention fixed earlier.

There is also a geometric proof. The multiplier of the polarization pairing (8.3) is (8.2), and for a two-dimensional alternating similitude the multiplier equals the determinant. The two proofs are logically valuable: the Frobenius proof audits the central scalar, while the pairing proof applies at every Galois element and audits the Tate twist.

For weight two with point-map diamond $\varepsilon$, Book 122's $S_v=\langle v\rangle^{-1}$ gives $q_vS_v^{-1}=q_v\varepsilon(v)$, exactly the value of $\varepsilon\chi_\ell$. A formula with $q_vS_v$ would contradict both polarization and the classical polynomial.

### 8.4 Complex conjugation and oddness

Let $\tau:F\hookrightarrow\mathbf R$ and let $c_\tau\in G_F$ be complex conjugation at $\tau$. It has order two. Since the coefficient field has characteristic zero, $\rho(c_\tau)$ is semisimple with eigenvalues in $\{1,-1\}$. Cohomological discrete series contributes one holomorphic and one antiholomorphic line, exchanged by the real involution. Thus

$$
\operatorname{tr}\rho_{\pi,\lambda}(c_\tau)=0,
\qquad
\det\rho_{\pi,\lambda}(c_\tau)=-1. \tag{8.7}
$$

This is **total oddness**: it holds at every real place. It also follows from (8.6) and the parity condition on the algebraic central character. Since $\chi_\ell(c_\tau)=-1$, the finite character has precisely the sign needed to make $\psi_{\pi,\lambda}(c_\tau)(-1)^{w+1}=-1$.

Oddness is not the assertion that complex conjugation acts as $-1$ on the whole space. That would have determinant $+1$. In dimension two, oddness means the two eigenvalues are $1$ and $-1$. Modulo $2$ they coincide, so the determinant test no longer detects oddness in the residual representation; oddness belongs first to the characteristic-zero lift.

## 9. Stable lattices and residual representations

### 9.1 Constructing a stable lattice

Let $V$ be a finite-dimensional continuous $E_\lambda$-representation of the compact group $G_F$. Start with any full $\mathcal O_\lambda$-lattice $L_0\subset V$. The orbit of $L_0$ is bounded because the image of $G_F$ is compact. Equivalently, after choosing a basis there is an integer $r$ such that every matrix entry of every $\rho(g)$ and $\rho(g)^{-1}$ lies in $\varpi_\lambda^{-r}\mathcal O_\lambda$. The $\mathcal O_\lambda$-span

$$
L=\sum_{g\in G_F}\rho(g)L_0
$$

then lies between $L_0$ and $\varpi_\lambda^{-r}L_0$, so it is a finitely generated full lattice and is $G_F$-stable.

In the geometric construction one usually takes a more canonical lattice: the intersection of $V$ with $M_\lambda$ inside ambient cohomology, saturated to remove torsion from the quotient. In weight two, an isogeny quotient $A_\pi$ of the Jacobian supplies $T_\lambda A_\pi$. Different isogenous models can give different lattices, but the rational representation is unchanged.

### 9.2 Reduction and dependence on the lattice

A stable lattice gives

$$
\bar\rho_L:G_F\longrightarrow\mathrm{GL}_2(k_\lambda)
$$

by reduction modulo $\varpi_\lambda$. The isomorphism class of $\bar\rho_L$ can depend on $L$. Its semisimplification does not:

$$
\bar\rho_{\pi,\lambda}^{\mathrm{ss}}
:=(\bar\rho_L)^{\mathrm{ss}} \tag{9.1}
$$

is independent of the stable lattice.

**Proof strategy.** For every $g\in G_F$, the characteristic polynomial of $\rho(g)$ has integral coefficients because $g$ preserves a lattice. Reducing it gives the characteristic polynomial of $g$ on any residual lattice. Thus any two reductions have the same full characteristic-polynomial function, not merely the same trace. The residual Brauer--Nesbitt criterion identifies their semisimplifications after scalar extension to an algebraic closure, and descent gives the stated common semisimple class. Retaining the determinant coefficient is essential in characteristic two. $\square$

At a good $v\nmid\ell$, reduction of (2.1) yields

$$
\det\bigl(X-\bar\rho_{\pi,\lambda}^{\mathrm{ss}}(\operatorname{Frob}_v)\bigr)
\equiv X^2-a_v(\pi)X+
\psi_\pi(v)q_v^{w+1}\pmod\lambda. \tag{9.2}
$$

If $v\mid\ell$, there is no unramified Frobenius polynomial to reduce unless an unramified quotient has separately been identified.

### 9.3 Absolute irreducibility tests

The strongest practical test is to find a good place $v$ for which the discriminant

$$
a_v(\pi)^2-4\psi_\pi(v)q_v^{w+1}
$$

is nonsquare in $k_\lambda$. Then the Frobenius polynomial is irreducible over $k_\lambda$, so the residual representation is irreducible over $k_\lambda$. This alone does not always prove absolute irreducibility: over $\overline{k}_\lambda$ the polynomial splits. To prove absolute irreducibility one must exclude a common invariant line over the algebraic closure.

One useful criterion uses two Frobenius elements. If $g$ has distinct residual eigenvalues and $h$ does not preserve either of its two eigenlines, then the group generated by $g,h$ has no invariant line over $\overline{k}_\lambda$. Equivalently, after diagonalizing $g$, both off-diagonal entries of $h$ are not simultaneously forced into one triangular direction. Another criterion is the nonvanishing of the commutator invariant

$$
\operatorname{tr}([\bar\rho(g),\bar\rho(h)])-2,
$$

with the usual interpretation in small characteristic. Any successful test must concern the whole group, not one irreducible characteristic polynomial over the ground residue field.

If $\bar\rho^{\mathrm{ss}}=\bar\alpha\oplus\bar\beta$, it is reducible even when a chosen lattice reduction is a nonsplit extension. Conversely, if the semisimplification is absolutely irreducible, every stable lattice reduction is isomorphic, not merely semisimply isomorphic: there is no reducible extension shape into which it can vary.

### 9.4 A lattice counterexample

Let $V=E_\lambda e_1\oplus E_\lambda e_2$ and suppose a group acts through

$$
\rho(g)=
\begin{pmatrix}\alpha(g)&c(g)\\0&\beta(g)\end{pmatrix}
$$

where $\alpha$ and $\beta$ take values in $\mathcal O_\lambda^\times$ and $c(g)\in\mathcal O_\lambda$. The lattice $L=\mathcal O_\lambda e_1+\mathcal O_\lambda e_2$ can reduce to a nonsplit extension of $\bar\beta$ by $\bar\alpha$ when the residual cocycle $\bar c$ is nonzero. Now put

$$
L'=\mathcal O_\lambda e_1+
\mathcal O_\lambda(\varpi_\lambda e_2).
$$

This is again stable, because in the basis $e_1,\varpi_\lambda e_2$ the upper-right entry is $\varpi_\lambda c(g)$. Its reduction is therefore split. The extension class has changed, while the diagonal characters and every residual characteristic polynomial remain the same. Scaling in the opposite direction would require an extra divisibility hypothesis; scaling in this direction does not.

This is not a defect in the construction. A rational representation does not canonically remember an integral extension class. When later arguments need a particular residual extension, the geometric lattice or a deformation condition must be specified. When only the automorphic eigensystem is given, the canonical output is $\bar\rho^{\mathrm{ss}}$.

## 10. Integral extraction without a direct summand

### 10.1 The localized cohomology lattice

Characteristic-zero idempotents often have denominators. If two eigenforms are congruent modulo $\lambda$, the projector onto either generic branch lies in the normalization of the Hecke algebra but not in the local Hecke algebra itself. Intersecting the rational eigenspace with cohomology still gives an individual stable lattice, but it discards the congruence family and does not construct a rank-two direct summand over the local algebra.

The integral object is instead

$$
M_{\mathfrak m},
$$

the cohomology lattice localized at the maximal ideal of the faithful image Hecke algebra. It is finite free over $\mathcal O_\lambda$ and faithful over $\mathbb T_{\mathfrak m}$, but it need not be free of rank two over $\mathbb T_{\mathfrak m}$. Its residual generalized eigenspace can have dimension larger than two. Galois nevertheless acts continuously and commutes with $\mathbb T_{\mathfrak m}$.

What survives without freeness is the quadratic law at good primes:

$$
\sigma_v^2-A_v\sigma_v+\Delta_v=0
\quad\text{on the weight-two localized covariant realization}, \tag{10.1}
$$

with the higher-weight normalized coefficients replacing $A_v,\Delta_v$. This law is the seed of a two-dimensional pseudorepresentation.

### 10.2 Pseudorepresentations and Cayley--Hamilton algebras

Over a complete commutative ring $A$, the most robust object is a **two-dimensional determinant**: a continuous multiplicative polynomial law of degree two

$$
D:A[[G_F]]\longrightarrow A.
$$

On each group element it is recorded by functions

$$
t:G_F\to A,\qquad d:G_F\to A
$$

through

$$
D(1-Xg)=1-t(g)X+d(g)X^2.
$$

These functions behave as trace and determinant. Concretely,

$$
t(1)=2,\qquad d(gh)=d(g)d(h),\qquad t(gh)=t(hg), \tag{10.2}
$$

and the degree-two trace identity

$$
t(g)t(h)=t(gh)+d(h)t(gh^{-1}) \tag{10.3}
$$

holds for all $g,h$. The determinant assigns to every $x\in A[[G_F]]$ its degree-two characteristic polynomial $\chi_D(x,X)$. In particular, the polynomial assigned to a group element $g$ is

$$
\chi_D(g,X)=X^2-t(g)X+d(g). \tag{10.4}
$$

When $2$ is not invertible, the polynomial law is primary: trace identities by themselves can lose divided-power information. We will also use “two-dimensional pseudorepresentation” for this determinant package, not for an unsupported trace function alone. The identities in (10.2)--(10.3) describe the values on group elements but do not, by themselves, encode the polynomial law on arbitrary elements of the group algebra.

Form the completed group algebra and impose the full Cayley--Hamilton ideal:

$$
E_D=A[[G_F]]\big/
\overline{\bigl(\chi_D(x,x):x\in A[[G_F]]\bigr)}. \tag{10.5}
$$

The image of $G_F$ in $E_D^\times$ is the **universal Cayley--Hamilton representation** belonging to $D$. It is a genuine group action on an algebra, even when no free rank-two $A$-module has been selected. Every matrix representation inducing $D$ factors through (10.5). Imposing only the quadratics of the group elements would be insufficient in general, especially in residue characteristic two, because the Cayley--Hamilton condition must also hold for their $A$-linear combinations.

For the Hecke localization, the desired continuous determinant is characterized at good places by

$$
t(\operatorname{Frob}_v)=a_v^{\mathbb T},
\qquad
d(\operatorname{Frob}_v)=\psi^{\mathbb T}(v)q_v^{w+1}. \tag{10.6}
$$

Existence is not inferred from arbitrary numbers. It comes from the actual Galois action on localized cohomology: its characteristic polynomials satisfy polynomial identities, and the degree-two automorphic quotient on every characteristic-zero branch gives compatible functions $t,d$. Density and torsion-freeness descend these functions to the faithful Hecke algebra; Section 15 gives the detailed family argument.

### 10.3 Specialization to one eigensystem

Let $\theta:\mathbb T_{\mathfrak m}\to\mathcal O_L$ be a characteristic-zero eigencharacter. Composing $(t,d)$ with $\theta$ gives a two-dimensional pseudorepresentation over $\mathcal O_L$. After passing to $L$, characteristic-zero pseudorepresentation theory produces a unique semisimple representation

$$
\rho_\theta^{\mathrm{ss}}:G_F\to\mathrm{GL}_2(\overline L)
$$

with those traces and determinants. By Chebotarev it is the semisimplification of the geometric representation extracted on that branch.

This step closes a semisimplicity gap that a naive eigenspace argument leaves open. Even if the localized module contains Jordan blocks for Hecke and even if its rank exceeds two, the specialized determinant law has degree two. It therefore produces the correct two-dimensional semisimple Galois object. A direct integral eigenspace is neither assumed nor needed.

If the characteristic-zero branch is irreducible, the semisimplification sign may be dropped. If it is reducible, the pseudorepresentation deliberately forgets its extension class, as Section 7.4 showed.

### 10.4 Residual irreducibility upgrades the construction

Suppose the residual pseudorepresentation $\bar D=(\bar t,\bar d)$ comes from an absolutely irreducible

$$
\bar\rho:G_F\to\mathrm{GL}_2(k).
$$

Then the Cayley--Hamilton algebra has a matrix structure compatible with the residual one, unique up to inner change of matrix coordinates. More precisely, let $A$ be a complete Noetherian local coefficient algebra, separated for its maximal-ideal topology, with residue field $k$. Every continuous lift of the residual two-dimensional determinant is the trace and determinant of a continuous representation

$$
\rho_A:G_F\to\mathrm{GL}_2(A), \tag{10.7}
$$

unique up to conjugation by an element congruent to the identity, provided the coefficient convention has fixed the residual identification.

**Proof strategy.** Absolute irreducibility makes the residual image algebra all of $M_2(k)$. Choose four residual group elements whose images form a basis and lift them to the Cayley--Hamilton algebra. The nondegenerate residual trace pairing, the degree-two Cayley--Hamilton identities, and completeness lift the four matrix coordinates and identify the resulting algebra with $M_2(A)$. This is the residually absolutely irreducible Cayley--Hamilton structure theorem; nondegeneracy alone would not justify the rank-four conclusion without the Cayley--Hamilton identities. An isomorphism with $M_2(A)$ sends every group element to a matrix with the prescribed determinant law. Any two such identifications differ by an inner automorphism; after fixing the residual identification, its conjugating matrix can be chosen congruent to the identity. $\square$

If $\bar D$ is reducible, there is no full residual matrix algebra and the trace pairing degenerates, so this proof fails exactly where it should. A pseudorepresentation still exists. When its two residual characters are distinct, the Cayley--Hamilton algebra can often be organized as a generalized matrix algebra; when they coincide, even that idempotent decomposition requires additional hypotheses. In neither case does the determinant law alone choose extension modules or an extension direction.

## 11. Local behavior away from the coefficient prime

### 11.1 Good places

At $v\nmid\ell$ outside level, algebra, character, and model ramification, the representation is unramified and (2.1) holds. This is full local compatibility in the unramified sense: the two Frobenius eigenvalues agree with the algebraically normalized Satake parameters, and the inertia action is trivial.

The proof combines two independent inputs. Smooth proper base change kills inertia. The special-fiber correspondence relation computes Frobenius. Neither alone suffices: unramifiedness does not identify the polynomial, while a formal polynomial on inertia invariants does not prove the entire representation unramified.

For the residual representation, inertia remains trivial at such a place and (9.2) holds. If the two residual roots coincide, Frobenius can become nonsemisimple after reduction. The characteristic polynomial remains valid; it does not assert diagonalizability.

### 11.2 Level primes and inertia

Let $v\nmid\ell$ divide the conductor or the chosen level. The good-prime correspondence degenerates: $U_v$ is an oriented level correspondence, not the spherical $T_v$, and a semistable special fiber may carry vanishing cycles. Therefore (6.1) cannot simply be reused with $U_v$.

What can be proved geometrically depends on the reduction. In weight two, if the selected abelian quotient has semistable reduction, inertia acts unipotently on an open subgroup and there is a monodromy operator of rank at most one in dimension two. Good reduction gives trivial inertia; multiplicative reduction gives a nontrivial extension between a cyclotomic and an unramified line after the appropriate twist; potentially good reduction gives finite inertia image away from the residue characteristic. These statements concern the actual abelian quotient and do not follow merely from the exponent of the automorphic conductor.

The local automorphic representation gives a sharper predicted dictionary. Principal-series characters prescribe two characters of the local Weil group; a Steinberg twist prescribes nonzero monodromy; a supercuspidal representation prescribes an irreducible Weil representation. The local correspondence developed earlier fixes conductors and local factors for these types. Matching the Galois representation with that full local parameter is a local--global compatibility theorem, not a consequence of the good-prime polynomial.

### 11.3 Steinberg and supercuspidal regimes

In the regimes established by the modular or Shimura curve's semistable geometry, the expected dictionary can be proved directly. Suppose $\pi_v$ is an unramified twist of Steinberg and the curve has the corresponding Iwahori semistable model. Then inertia on $\rho_{\pi,\lambda}$ is unipotent, the invariant space is one dimensional, and the nilpotent monodromy is nonzero. The conductor exponent is one. The eigenvalue of $U_v$, in the fixed algebraic normalization, gives Frobenius on the invariant line.

If a quaternionic local component is an unramified norm character at a division place, transfer makes the split component an unramified Steinberg twist. This explains the conductor shift $0\mapsto1$: the quaternionic level is maximal, but the transferred two-dimensional Galois representation has Steinberg monodromy at that place.

For a higher-dimensional division representation, transfer is supercuspidal and its conductor is the exact transferred conductor established in the local dictionary. The present geometric extraction proves finite ramification and the good-prime polynomials. A claim identifying every inertia representation and conductor in arbitrary depth would require an additional local comparison theorem. We therefore record exact supercuspidal inertia only when that theorem is among the hypotheses of the chosen realization.

### 11.4 The precise boundary of local compatibility

The safe package is as follows.

- At split hyperspecial $v\nmid\ell$, unramifiedness and the complete Frobenius polynomial are proved.
- At semistable weight-two places with an identified toric part, unipotent inertia and the Steinberg conductor statement are proved.
- At places where a local comparison theorem for the chosen Shimura curve and coefficient system has been established, the associated Weil representation, monodromy, local factor, and conductor agree with the automorphic local parameter.
- At remaining level, division, deep-type, or badly reduced places, only finite ramification and any explicitly established conductor bound are asserted.

This distinction is substantive. The equality of almost all Euler factors determines the global semisimplification, but it does not calculate inertia at an omitted place. Strong multiplicity one recovers the automorphic local component from the other components; it does not by itself prove that geometric inertia realizes that component.

## 12. Places above the coefficient prime

### 12.1 Why good reduction no longer means unramified

Let $v\mid\ell$. The cyclotomic character is ramified at $v$, so (8.6) already shows that $\rho_{\pi,\lambda}$ usually cannot be unramified. Smooth proper base change in the prime-to-residue form used at good places does not identify the $\ell$-adic generic fiber with ordinary étale cohomology of the special fiber. The connected part of the $\ell$-divisible group contributes ramified torsion even under good reduction.

An elliptic curve with good ordinary reduction illustrates the point. Its $\ell$-divisible group has connected and étale pieces. After a suitable basis, the local Tate module has a filtration whose characters include a cyclotomic factor and an unramified factor. In the supersingular case no such rank-one ordinary filtration need exist. Both curves have good reduction; neither conclusion is “unramified.”

Thus the good-prime polynomial is stated only for $v\nmid\ell$. At $v\mid\ell$, one records integral geometric structures rather than pretending there is a spherical Frobenius conjugacy class on the whole representation.

### 12.2 The weight-two finite-flat statement

Suppose the form is in the untwisted parallel weight-two normalization, so $k_\tau=2$ and $w=0$, and the selected factor is realized by an abelian variety $A_\pi/F$ that has good reduction at $v\mid\ell$. A nonzero common determinant twist is handled by first untwisting and then retwisting the Galois representation; it is not literally the Tate module of the same abelian quotient. Let $\mathcal A_\pi/\mathcal O_{F_v}$ be the abelian scheme extending $A_\pi$. For every $n$,

$$
\mathcal A_\pi[\ell^n]
$$

is a finite flat commutative group scheme whose generic fiber is $A_\pi[\ell^n]$. To pass from this full $\ell$-power torsion to the chosen coefficient place, assume that the relevant coefficient order acts on $\mathcal A_\pi$ and that the idempotent selecting the $\lambda$-primary factor is integral. Then the kernel of $\varpi_\lambda^n$ on that factor is finite flat and has generic fiber

$$
T_\lambda A_\pi/\varpi_\lambda^nT_\lambda A_\pi.
$$

Without this integral coefficient action, finite flatness of $\mathcal A_\pi[\ell^n]$ does not by itself isolate the desired rank-two $\lambda$-adic quotient. Subobjects, quotients, and duals inherit such a statement only when the corresponding operation exists in the finite-flat category.

This is the exact finite-flat conclusion furnished by good-reduction geometry. It is a statement about a chosen lattice and its finite-level group schemes, not merely about the rational representation. If $A_\pi$ is only an isogeny factor defined using a denominator divisible by $\ell$, the integral projector may fail to extend. One can still choose a stable lattice, but finite flatness of that arbitrary lattice does not follow.

### 12.3 Ordinary and supersingular examples

For good ordinary elliptic reduction, the connected--étale sequence gives, after a finite unramified coefficient extension if needed,

$$
0\longrightarrow T_\ell(\mathcal E[\ell^\infty]^0)
\longrightarrow T_\ell E
\longrightarrow T_\ell(\mathcal E[\ell^\infty]^{\mathrm{et}})
\longrightarrow0. \tag{12.1}
$$

The first line has cyclotomic-type inertia and the quotient is unramified. The sequence need not split over $G_{F_v}$. Reducing modulo $\lambda$ can produce either a split or nonsplit ordinary residual representation depending on the extension class.

For supersingular good reduction, the connected part has height two and there is no étale rank-one quotient over the residue field. It would be false to infer an ordinary triangular representation merely from good reduction. Both torsion group schemes remain finite flat, but their connected--étale shapes differ decisively.

At multiplicative reduction, the Tate-curve sequence has a cyclotomic line and a trivial-type quotient, with extension class controlled by the Tate parameter. This representation is semistable rather than good-reduction finite flat in the preceding abelian-scheme sense.

### 12.4 What is not being asserted

We make no general claim here that every cohomological $\rho_{\pi,\lambda}$ has a specified crystalline, semistable, or Hodge--Tate structure, although such statements are expected and known in broader settings. We do not identify a universal finite-flat deformation condition, prove uniqueness of finite flat models, or assert that every extension between finite-flat generic fibers extends integrally.

For higher-weight local systems, a geometric origin alone does not turn the two-dimensional extracted lattice into the torsion of an abelian scheme. The weight-two finite-flat argument therefore does not transfer verbatim. Any sharper assertion at $v\mid\ell$ must state its weight range, reduction hypothesis, integral projector, and local comparison input.

## 13. Twists, conjugation, and change of coefficients

### 13.1 Twisting both sides

First let $\eta$ be a finite-order Hecke character whose $\lambda$-adic avatar is $\eta_\lambda:G_F\to E_\lambda^\times$. At a good place,

$$
a_v(\pi\otimes\eta)=\eta(v)a_v(\pi),
$$

while the central character changes by $\eta^2$. Therefore

$$
P_{\pi\otimes\eta,v}(X)
=X^2-\eta(v)a_v(\pi)X
+\eta(v)^2\psi_\pi(v)q_v^{w+1}. \tag{13.1}
$$

The tensor product

$$
\rho_{\pi,\lambda}\otimes\eta_\lambda
$$

has exactly this polynomial. Chebotarev gives

$$
\rho_{\pi\otimes\eta,\lambda}^{\mathrm{ss}}
\simeq
(\rho_{\pi,\lambda}\otimes\eta_\lambda)^{\mathrm{ss}}. \tag{13.2}
$$

In the irreducible cuspidal range the semisimplification signs may be removed. A finite-order twist changes no cohomological weight. More generally, suppose an algebraic character has avatar

$$
\eta_\lambda=\eta_{0,\lambda}\chi_\ell^r
$$

with $\eta_0$ finite order in the convention of this book. Then the good-prime trace is multiplied by $\eta_0(v)q_v^r$, the determinant by $\eta_0(v)^2q_v^{2r}$, and the central-weight parameter changes from $w$ to $w+2r$. Thus the determinant exponent becomes $w+1+2r$. Suppressing the distinction between finite-order and norm twists is a common source of half-integral or sign-reversed powers.

### 13.2 Automorphisms of the coefficient field

Let $\sigma\in\operatorname{Aut}(\overline{\mathbf Q})$. Applying $\sigma$ to the embedded coefficient field and to the eigenvalues gives a conjugate automorphic representation $\pi^\sigma$ with

$$
a_v(\pi^\sigma)=\sigma(a_v(\pi)),
\qquad
\psi_{\pi^\sigma}(v)=\sigma(\psi_\pi(v)).
$$

Choose compatible embeddings into $\overline{\mathbf Q}_\ell$, and write $\sigma\lambda$ for the induced place of $\sigma(E_\pi)$. The resulting isomorphism of completed coefficient fields lets us apply $\sigma$ to the scalar structure of $\rho_{\pi,\lambda}$; this is not an entrywise operation until that field isomorphism has been chosen. The conjugated representation has the good-prime polynomials of $\pi^\sigma$. Hence

$$
\rho_{\pi^\sigma,\sigma\lambda}^{\mathrm{ss}}
\simeq {}^\sigma\rho_{\pi,\lambda}^{\mathrm{ss}}. \tag{13.3}
$$

This is a statement about conjugating the coefficient structure, not about conjugating elements of $G_F$. It also explains why the field generated by traces is the natural field of definition of the semisimple representation.

### 13.3 Changing the place above $\ell$

Two places $\lambda_1,\lambda_2$ above the same rational prime give representations over different completions. There is generally no canonical isomorphism between them. Their common arithmetic content is the algebraic polynomial $P_{\pi,v}(X)\in E_\pi[X]$ at every $v$ away from the level and from $\ell$.

For any fixed $\lambda$, Chebotarev recovers the semisimple representation from these polynomials. Varying $\lambda$ suggests a compatible family, but proving all independence, purity, local compatibility, and integral properties of that family is a separate global theory. Here we record only the common good-place polynomials and construct each $\lambda$-adic member individually.

## 14. Three geometric settings

### 14.1 Classical modular forms over $\mathbf Q$

Let $f$ be a normalized cuspidal newform of weight $k\ge2$, level $N$, and nebentype $\varepsilon$. Put

$$
E_f=\mathbf Q(a_n(f):n\ge1),
$$

fix $\lambda\mid\ell$, and pass, when necessary, to a harmless auxiliary fine level on which a universal elliptic curve exists. Pullback along the resulting finite level cover does not change the $f$-packet after the corresponding old multiplicity is removed. On that fine modular curve $Y$, the parabolic group

$$
H^1_!\left(Y_{\overline{\mathbf Q}},
\operatorname{Sym}^{k-2}\mathcal H_\lambda\right)(1)
$$

with the covariant normalization of Chapter 3 contains the $f$-system. At new level its automorphic multiplicity line is one dimensional, and the associated Galois multiplicity space is two dimensional. It gives

$$
\rho_{f,\lambda}:G_\mathbf Q\to\mathrm{GL}_2(E_{f,\lambda})
$$

such that, for $p\nmid N\ell$,

$$
\det(X-\rho_{f,\lambda}(\operatorname{Frob}_p))
=X^2-a_p(f)X+\varepsilon(p)p^{k-1}. \tag{14.1}
$$

Moreover,

$$
\det\rho_{f,\lambda}=\varepsilon_\lambda\chi_\ell^{k-1},
\qquad
\det\rho_{f,\lambda}(c)=-1. \tag{14.2}
$$

When $k=2$, the factor occurs in the covariant Tate module of $J_1(N)$. If the Hecke idempotent defines an abelian quotient $A_f$ over $\mathbf Q$, then $V_\lambda A_f$ is the desired representation over the coefficient field, with dimension two after taking the $E_f$-linear factor. The underlying abelian variety has dimension $[E_f:\mathbf Q]$, so its rational $\ell$-adic Tate module has dimension $2[E_f:\mathbf Q]$; forgetting the coefficient-field action would overcount.

At a prime $p\mid N$, the statement depends on the local type. Squarefree conductor with unramified central character gives a Steinberg twist and semistable monodromy. Deeper principal-series or supercuspidal types require their own local comparison. The symbol $U_p$ alone does not determine which case occurs.

### 14.2 Hilbert forms in the curve-realizable range

Let $F$ be totally real and let $\pi$ be a regular algebraic cuspidal representation of weight $((k_\tau),w)$. Choose a quaternion algebra $D/F$ split at exactly one real place and assume that $\pi_v$ is discrete series at every place where $D$ ramifies. Global transfer produces $\Pi$ on $D^\times(\mathbf A_F)$ with the same central character and the same local components at split finite places.

A Shimura curve for $D$ with coefficient system (3.3) realizes $\Pi$. Extraction gives

$$
\rho_{\pi,\lambda}:G_F\to\mathrm{GL}_2(E_\lambda)
$$

and, at every finite $v\nmid\ell$ away from conductor, discriminant, and auxiliary level,

$$
\det(X-\rho_{\pi,\lambda}(\operatorname{Frob}_v))
=X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}. \tag{14.3}
$$

It is totally odd and has determinant $\psi_{\pi,\lambda}\chi_\ell^{w+1}$. Nonparallel weights alter the coefficient system but not the dimension of the extracted factor.

The phrase “curve-realizable range” carries real content. If no suitable $D$ exists because a required finite ramified place is principal series, this argument stops. One must then use a higher-dimensional Hilbert modular variety or another construction. The existence of (14.3) in broader generality should not be credited to the curve proof given here.

### 14.3 Quaternionic forms and transfer

Begin instead with a noncharacter cuspidal automorphic representation $\Pi$ of $D^\times(\mathbf A_F)$ for a quaternion algebra split at one real place. Its eigensystem acts directly on a Shimura curve. The cohomological construction attaches $\rho_{\Pi,\lambda}$. Global transfer gives a cuspidal $\pi=\operatorname{JL}_D(\Pi)$ on $\mathrm{GL}_2$, and at every split unramified place the Hecke polynomials agree. Chebotarev therefore identifies

$$
\rho_{\Pi,\lambda}^{\mathrm{ss}}
\simeq\rho_{\pi,\lambda}^{\mathrm{ss}}. \tag{14.4}
$$

At a division place, the transfer dictionary supplies the automorphic local type. An unramified norm character becomes a Steinberg twist; a higher-dimensional division representation becomes supercuspidal with the established conductor shift. These facts predict and, in the semistable cases covered by the curve model, prove the corresponding Galois monodromy.

The exclusion of quaternionic characters is essential. A constant class-set function can have perfectly integral Brandt eigenvalues, but its split transfer belongs to the exceptional character spectrum rather than to a cuspidal degree-two factor. One first removes the character block, then extracts.

## 15. Hecke algebras acting on families

### 15.1 A pseudorepresentation over the local Hecke algebra

Fix an integral cuspidal cohomology module $M$, its faithful image Hecke algebra $\mathbb T$, and a maximal ideal $\mathfrak m$ of residue characteristic $\ell$. We call $\mathfrak m$ **non-Eisenstein** when its residual two-dimensional determinant is not the sum of the two boundary characters occurring in the Eisenstein part. Absolute irreducibility implies this condition, but non-Eisenstein need not by itself supply matrices. Assume $\mathfrak m$ is non-Eisenstein, and let

$$
A=\mathbb T_{\mathfrak m}.
$$

Assume $A$ is finite torsion-free over $\mathcal O_\lambda$, its characteristic-zero fiber is reduced, and every characteristic-zero branch is a curve-realizable cuspidal eigensystem of the fixed cohomological type. The reducedness hypothesis holds, for example, when the commuting Hecke operators are semisimple for a positive definite characteristic-zero pairing. It is stated because an arbitrary finite local algebra need not be recovered from its generic eigencharacters.

For $v$ outside a finite set $\Sigma$ define the universal coefficients

$$
a_v^A=S_v^{-1}T_v
$$

in weight two, with the weight-normalized analogue in general, and

$$
d_v^A=\psi^A(v)q_v^{w+1}. \tag{15.1}
$$

Here $\psi^A$ is the continuous finite-order Galois character obtained from the central diamond action on the chosen Hecke block by the arithmetic reciprocity convention. If the central character is allowed to vary, its finite ray-class quotient must be included among the Hecke operators so that this universal character is actually defined over $A$. There is a unique continuous two-dimensional determinant

$$
D_A:A[[G_{F,\Sigma}]]\longrightarrow A. \tag{15.2}
$$

whose values on group elements define trace and determinant functions satisfying

$$
t_A(\operatorname{Frob}_v)=a_v^A,
\qquad
d_A(\operatorname{Frob}_v)=d_v^A
\quad(v\notin\Sigma). \tag{15.3}
$$

The quotient $G_{F,\Sigma}$ is the Galois group of the maximal extension unramified outside $\Sigma$. Calling (15.2) a determinant emphasizes that it remains meaningful in residue characteristic two.

### 15.2 The density argument

We explain why (15.2) exists rather than merely announcing its Frobenius values.

Let

$$
A_E=A\otimes_{\mathcal O_\lambda}E_\lambda
\hookrightarrow\prod_{i=1}^r E_i
$$

be the product of its characteristic-zero eigenfields. Each projection corresponds to an eigensystem $\pi_i$ and hence to a representation $\rho_i$. Their product defines trace and determinant functions

$$
t_E(g)=(\operatorname{tr}\rho_i(g))_i,
\qquad
d_E(g)=(\det\rho_i(g))_i. \tag{15.4}
$$

They satisfy all two-dimensional determinant identities coordinatewise. At every good Frobenius, (15.3) shows that their values lie in the subring $A\subset A_E$, not merely in its normalization.

To extend integrality from Frobenius to every $g$, reduce modulo $\varpi_\lambda^n$. The image of the product representation modulo a stable product lattice is finite. Chebotarev says that every conjugacy class in this finite quotient is represented by a Frobenius element outside $\Sigma$ and away from finitely many additionally excluded places. Because trace and determinant are class functions, $t_E(g)$ and $d_E(g)$ reduce modulo $\varpi_\lambda^n$ to elements of the image of $A$ for every $n$. The finite torsion-free algebra $A$ is complete and closed inside $A_E$, so the values themselves lie in $A$.

The coordinatewise polynomial identities now hold in $A$ because $A\hookrightarrow A_E$ is injective. There is no hidden division by two in descending the determinant law: for two-dimensional matrices,

$$
\det(x+y)=\det(x)+\det(y)
+\operatorname{tr}(x)\operatorname{tr}(y)-\operatorname{tr}(xy),
$$

and repeated use of this polarization formula expresses the determinant of every finite $A$-linear combination of group elements in terms of the integral trace and determinant values already obtained. Passage to the completed group algebra follows by continuity. Uniqueness follows from Frobenius density and continuity. This constructs (15.2) without assuming that $M_{\mathfrak m}$ is free of rank two over $A$.

If the generic fiber were nonreduced, evaluation at eigencharacters would not detect its nilpotents and this proof would construct only a determinant over the reduced quotient. A determinant over a genuinely nonreduced Hecke algebra requires a direct Cayley--Hamilton action on the family or an independent lifting argument. One must not invent nilpotent trace values from their vanishing at every generic point.

### 15.3 From a family determinant to a family representation

Assume the residual determinant $\bar D_A$ is represented by an absolutely irreducible

$$
\bar\rho_{\mathfrak m}:G_{F,\Sigma}\to\mathrm{GL}_2(k(\mathfrak m)).
$$

Section 10.4 upgrades $D_A$ to

$$
\rho_{\mathfrak m}:G_{F,\Sigma}\to\mathrm{GL}_2(A), \tag{15.5}
$$

unique up to strict conjugacy, with

$$
\operatorname{tr}\rho_{\mathfrak m}(\operatorname{Frob}_v)=a_v^A,
\qquad
\det\rho_{\mathfrak m}(\operatorname{Frob}_v)=d_v^A. \tag{15.6}
$$

Its determinant globally equals $\psi^A\chi_\ell^{w+1}$. Every continuous local homomorphism $A\to B$ to a complete local coefficient algebra specializes (15.5) to the representation belonging to the specialized Hecke system.

The matrix representation (15.5) is much stronger than an action on the large localized cohomology module. It is rank two over the Hecke algebra itself. Absolute residual irreducibility is what turns degree-two characteristic data into matrices; Hecke-module freeness is not needed for this upgrade.

### 15.4 Reducible residual systems

If $\bar D_A=\bar\alpha+\bar\beta$, the determinant still records every good Hecke polynomial, but it does not choose whether the family is upper triangular, lower triangular, split, or generically irreducible with reducible special fiber. When $\bar\alpha\ne\bar\beta$, the two residual idempotents lift and the Cayley--Hamilton algebra has the shape of a generalized matrix algebra

$$
\begin{pmatrix}A&B\\C&A\end{pmatrix}, \tag{15.7}
$$

where the product ideal $BC\subset A$ measures reducibility. Neither $B$ nor $C$ is determined by trace alone. If $\bar\alpha=\bar\beta$, the residual idempotents cannot be separated, and (15.7) is not automatic; one must retain the undivided Cayley--Hamilton algebra or supply further structure.

An Eisenstein maximal ideal is the clearest example: its residual trace is a sum of two characters, and boundary cohomology supplies one realization. A cuspidal congruence may provide a nonsplit extension, but the pseudorepresentation cannot select its direction. Later deformation arguments that require a representation must either assume absolute residual irreducibility or add an oriented filtration and extension data.

## 16. The theorem package

### 16.1 The curve-realization theorem

We now collect the construction in a form usable without repeating its choices.

**Theorem 16.1 (automorphic form to Galois representation).** Let $F$ be totally real and let $\pi$ be a regular algebraic cuspidal representation of $\mathrm{GL}_2(\mathbf A_F)$ of cohomological weight $((k_\tau),w)$ and finite central character part $\psi_\pi$. Assume $\pi$ has a curve realization of one of the following forms:

1. $F=\mathbf Q$ and $\pi$ is realized in parabolic cohomology of a modular curve with its weight local system; or
2. $\pi$ transfers to a noncharacter automorphic representation on a quaternion algebra split at exactly one real place and is realized in the first cohomology of the corresponding Shimura curve with coefficient system (3.3).

Assume the selected finite newvector or local type and archimedean cohomological type each have multiplicity one. In weights beyond two, also assume the coefficient-system comparison stated in Section 6.3: at every place where the good-prime polynomial is claimed, the lisse system or algebraic projector extends over the integral model and the geometric correspondence induces the algebraically normalized Hecke operator. Let $E_\pi$ contain the algebraically normalized Hecke eigenvalues, let $\lambda\mid\ell$, and enlarge $E_{\pi,\lambda}$ finitely if necessary. Then there is a continuous representation

$$
\rho_{\pi,\lambda}:G_F\longrightarrow
\mathrm{GL}_2(E_{\pi,\lambda})
$$

with the following properties.

1. It is unramified outside finitely many places, contained in the union of primes above $\ell$, the automorphic conductor, quaternionic discriminant, coefficient-system ramification, and explicitly chosen auxiliary bad level.
2. If $v\nmid\ell$ is split hyperspecial and all geometric data have good reduction, then
   $$
   \det(X-\rho_{\pi,\lambda}(\operatorname{Frob}_v))
   =X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}.
   $$
3. Its determinant is
   $$
   \det\rho_{\pi,\lambda}
   =\psi_{\pi,\lambda}\chi_\ell^{w+1}.
   $$
4. It is totally odd: for every real place $\tau$,
   $$
   \operatorname{tr}\rho_{\pi,\lambda}(c_\tau)=0,
   \qquad
   \det\rho_{\pi,\lambda}(c_\tau)=-1.
   $$
5. It satisfies the polarized duality (8.5) and is compatible with algebraic twists and coefficient-field conjugation. Its semisimplification is uniquely determined up to isomorphism by its good-prime polynomials; the representation itself is so determined when it is semisimple, in particular when it is irreducible.
6. At $v\nmid\ell$ where the chosen geometric realization has an established semistable or full local comparison theorem, its inertia, monodromy, local factor, and conductor have the corresponding compatibility with $\pi_v$. At other bad places only the explicitly proved finite-ramification statement is included.

**Proof.** Chapters 3--5 extract a two-dimensional stable factor from the simultaneous Hecke and Galois action; no semisimplicity of the ambient cohomology is silently used. Chapter 6 converts the geometric Frobenius relation to arithmetic Frobenius and obtains the polynomial. Chapter 7 proves continuity, finite ramification, and uniqueness after semisimplification. Polarization gives determinant, duality, and oddness in Chapter 8. The local qualifications concern the extracted geometric representation itself and are exactly those of Chapters 11--12. If a separate semisimplicity or irreducibility theorem is available, Chebotarev upgrades the uniqueness statement accordingly. $\square$

The theorem is intentionally conditional on a curve realization. It is exact in the weight-two setting central to modularity arguments, and it includes higher cohomological weight when the correct local system on a modular or quaternionic Shimura curve is available.

### 16.2 The integral and residual theorem

**Theorem 16.2 (lattices and reduction).** Under Theorem 16.1, $\rho_{\pi,\lambda}$ admits a $G_F$-stable $\mathcal O_\lambda$-lattice $L$. Its reduction has a lattice-independent semisimplification

$$
\bar\rho_{\pi,\lambda}^{\mathrm{ss}}:G_F\to
\mathrm{GL}_2(\overline{k}_\lambda),
$$

characterized at every good $v\nmid\ell$ by

$$
\det(X-\bar\rho_{\pi,\lambda}^{\mathrm{ss}}(\operatorname{Frob}_v))
\equiv
X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}\pmod\lambda.
$$

Its determinant is the reduction of $\psi_{\pi,\lambda}\chi_\ell^{w+1}$. If the residual semisimplification is absolutely irreducible, all stable-lattice reductions are isomorphic. In weight two, if $L$ is obtained from the Tate module of a good-reduction abelian quotient through an integral factor, then at $v\mid\ell$ every $L/\varpi_\lambda^nL$ is the generic fiber of the corresponding finite flat group-scheme factor.

**Proof.** Compactness constructs $L$. Integral characteristic polynomials and the residual character criterion prove lattice independence after semisimplification. Absolute irreducibility eliminates extension ambiguity. The last assertion comes from torsion in the abelian scheme and requires the stated integral factor. $\square$

No finite-flat claim is made for an arbitrary stable lattice, an abelian quotient with an $\ell$-denominator in its projector, or a higher-weight cohomological factor.

### 16.3 The family theorem

**Theorem 16.3 (local Hecke determinant).** Let $A=\mathbb T_{\mathfrak m}$ arise from a faithful integral cuspidal cohomology module of fixed curve-realizable weight and level. Assume $A$ is finite torsion-free, its generic fiber is reduced, and every generic branch satisfies Theorem 16.1. Then there is a unique continuous two-dimensional determinant $D_A$ of $G_{F,\Sigma}$ with good-prime coefficients (15.3). If its residual determinant is absolutely irreducible, there is a continuous representation

$$
\rho_{\mathfrak m}:G_{F,\Sigma}\to\mathrm{GL}_2(A)
$$

realizing $D_A$, unique up to strict conjugacy.

**Proof.** Form the product of the representations on all generic branches. Good Frobenius traces and determinants lie in $A$. Finite-quotient Chebotarev and completeness show that the trace and determinant of every Galois element lie in $A$. Polynomial identities descend through the injection into the generic fiber. Absolute residual irreducibility identifies the Cayley--Hamilton algebra with $M_2(A)$. $\square$

The generic reducedness hypothesis may be replaced by an independently constructed Cayley--Hamilton action over the full nonreduced algebra. Without one of these inputs, generic eigenforms see only $A_{\mathrm{red}}$.

## 17. Three worked examples

### 17.1 An elliptic-curve form

Take the elliptic curve

$$
E:\quad y^2+y=x^3-x^2-10x-20.
$$

Its discriminant is $-11^5$ and its conductor is $11$. Let $f$ be its normalized weight-two newform with rational coefficients and trivial nebentype. The modular parametrization gives a quotient

$$
J_0(11)\twoheadrightarrow E.
$$

The extracted representation is not merely abstractly isomorphic to a cohomological factor: it is

$$
\rho_{f,\ell}=T_\ell E\otimes\mathbf Q_\ell.
$$

For $p\nmid11\ell$,

$$
a_p(f)=p+1-\#E(\mathbf F_p)
$$

and

$$
\det(X-\rho_{f,\ell}(\operatorname{Frob}_p))
=X^2-a_p(f)X+p. \tag{17.1}
$$

As a concrete check, take $\ell\ne2$ and reduce the curve modulo $2$. For each $x=0,1$, the right side is zero and both $y=0,1$ solve $y^2+y=0$; including the point at infinity gives $\#E(\mathbf F_2)=5$. Hence

$$
a_2=2+1-5=-2,
\qquad
P_{E,2}(X)=X^2+2X+2.
$$

The determinant is $\chi_\ell$, the Weil pairing gives $V^\vee\simeq V(-1)$, and complex conjugation has eigenvalues $1,-1$. At a prime of good reduction above $\ell$, every $E[\ell^n]$ extends to a finite flat group scheme, although $T_\ell E$ is generally ramified.

At $p=11$ the curve has multiplicative reduction. Inertia acts unipotently with a one-dimensional invariant space. Split and nonsplit multiplicative reduction change the unramified twisting character, not the fact that the monodromy is Steinberg. This is a proved bad-place statement arising from the Tate curve, stronger than finite ramification but narrower than arbitrary local compatibility.

Reducing (17.1) modulo $\ell$ gives the residual representation on $E[\ell]$. A rational $\ell$-isogeny makes it reducible; the choice of the isogeny direction can change the nonsplit residual extension, while its semisimplification remains the sum of the two diagonal characters.

### 17.2 A higher-weight modular form

Consider the normalized discriminant form

$$
\Delta(q)=q\prod_{n\ge1}(1-q^n)^{24}
=\sum_{n\ge1}\tau(n)q^n.
$$

It has weight $12$, level one, trivial character, and rational coefficient field. The relevant local system is $\operatorname{Sym}^{10}\mathcal H_\ell$, not the constant sheaf. Its two-dimensional factor satisfies, for every $p\ne\ell$,

$$
\det(X-\rho_{\Delta,\ell}(\operatorname{Frob}_p))
=X^2-\tau(p)X+p^{11}. \tag{17.2}
$$

Thus $\det\rho_{\Delta,\ell}=\chi_\ell^{11}$. The exponent $11$ is an immediate audit of the coefficient system: extracting from the Jacobian of the base modular curve would have produced weight one in cohomology and determinant $p$, not $p^{11}$.

For instance $\tau(2)=-24$, so at $p=2$ the polynomial is

$$
X^2+24X+2^{11}.
$$

Its product of roots is $2^{11}$ and, under every complex embedding, each root has size $2^{11/2}$. The form has no level primes, but the place $\ell$ remains exceptional: nothing in the good-prime argument says that the $\ell$-adic representation is unramified at $\ell$, and the weight-two abelian finite-flat argument does not apply.

### 17.3 A quaternionic eigensystem

Let $D/\mathbf Q$ be the quaternion algebra ramified at $11$ and $\infty$, and take maximal finite level and trivial algebraic weight. The finite ideal-class module has a constant line and a complementary nonconstant eigensystem. The constant line is the quaternionic character block and must be removed. The nonconstant system transfers to the weight-two cuspidal newform of level $11$.

At every prime $p\ne11,\ell$, the Brandt operator and the modular Hecke operator have the same eigenvalue $a_p$, while the central scalar is trivial. The representation extracted after transfer has

$$
\det(X-\rho(\operatorname{Frob}_p))
=X^2-a_pX+p. \tag{17.3}
$$

At $11$, maximal division level means that the local quaternionic component is an unramified norm character. Transfer makes it an unramified Steinberg twist, so the split conductor exponent is one and the Galois representation has the corresponding one-dimensional inertia invariants and nonzero monodromy in the semistable realization.

This example exhibits the whole route:

$$
\text{Brandt eigensystem}
\longrightarrow
\text{quaternionic automorphic constituent}
\longrightarrow
\text{split weight-two constituent}
\longrightarrow
\text{Jacobian factor}
\longrightarrow
\rho_\lambda.
$$

The first arrow requires deleting constants, the second requires the local transfer condition, the fourth requires multiplicity-one extraction, and the Frobenius polynomial requires the inverse-central conversion of Chapter 6. Skipping any arrow replaces a theorem by an analogy.

## 18. A construction protocol and its failure tests

### 18.1 The protocol

A reliable construction proceeds in the following order.

1. Fix the algebraic automorphic normalization, the weight $((k_\tau),w)$, the finite central character $\psi_\pi$, and the coefficient field $E_\pi$.
2. Choose $\lambda\mid\ell$ and a curve realization. For a quaternionic realization, verify the transfer condition at every ramified place.
3. Put the correct lisse coefficient system on the curve; in weight two use the covariant Jacobian Tate module.
4. Work in cuspidal or parabolic cohomology, removing boundary and quaternionic character blocks.
5. Form the faithful image Hecke algebra on the chosen integral lattice and verify that Hecke commutes with $G_F$.
6. At characteristic zero, use newvector or type multiplicity one, global multiplicity one, and duality to isolate a two-dimensional subquotient.
7. Convert Book 122's geometric polynomial using $F_v=q_vG_v^{-1}$ and $S_v^{-1}$; only then specialize the Hecke character.
8. Use geometry for continuity and ramification, polarization for determinant and duality, and Chebotarev for uniqueness.
9. Choose a stable lattice, define residual semisimplification, and test absolute irreducibility over the algebraic residue field.
10. For a local Hecke family, retain the entire localization and construct a determinant; upgrade it to matrices only under absolute residual irreducibility or another explicit Cayley--Hamilton input.

The order matters. In particular, taking an ordinary residual eigenspace before localization can erase congruent branches, while specializing the unconverted operator $T_v$ can put the central character on the wrong side.

### 18.2 Normalization and multiplicity audits

Four quick tests catch most errors.

**Elliptic test.** In weight two with trivial character, the polynomial must be $X^2-a_vX+q_v$ and the determinant must be cyclotomic.

**Diamond test.** If Book 122's scalar is $S_v=\langle v\rangle^{-1}$ and the diamond eigenvalue is $\varepsilon(v)$, the covariant determinant must be $q_v\varepsilon(v)$, never $q_v\varepsilon(v)^{-1}$.

**Twist test.** Tensoring by a character $\eta$ multiplies trace once and determinant twice. A Tate twist by $(r)$ multiplies arithmetic-Frobenius trace by $q_v^r$ and determinant by $q_v^{2r}$.

**Oldform test.** Raising an unramified local level once doubles the fixed-vector multiplicity of one representation. If the alleged eigenspace remains two dimensional without a new quotient or local type operator, a multiplicity factor has been overlooked.

A fifth test concerns variance. Untwisted $H^1$ is dual to the covariant Tate module. If one switches between them while retaining the same arithmetic-Frobenius roots, a dual and a Tate twist have been lost.

### 18.3 Local and integral audits

At a good place, verify separately that inertia is trivial and that Frobenius has the Hecke polynomial. At a level place, ask whether the model is good, semistable, or worse; whether the local automorphic type is principal series, Steinberg, or supercuspidal; and whether a local comparison theorem has actually been established. A conductor predicted by transfer is not automatically a conductor proved for geometric inertia.

At a place above $\ell$, reject the implication “good reduction implies unramified.” Ask instead whether a weight-two abelian scheme supplies finite flat torsion, whether the chosen factor is integral, and whether ordinary or supersingular reduction changes the filtration. Do not transfer this finite-flat conclusion to higher weight without another argument.

Integrally, distinguish:

$$
\text{ordinary eigenspace}
\subseteq
\text{generalized eigenspace}
\subseteq
\text{localization}.
$$

The inclusions can be strict. A stable-lattice reduction is not canonical, its semisimplification is. A pseudorepresentation controls characteristic polynomials, not reducible extension classes. A representation over a local Hecke algebra follows from absolute residual irreducibility, not from faithfulness or finite freeness of the ambient cohomology module.

## 19. Toward deformation rings and compatible systems

### 19.1 The deformation-theoretic bridge

Let $\mathfrak m$ be a maximal ideal for which $\bar\rho_{\mathfrak m}$ is absolutely irreducible. The family representation

$$
\rho_{\mathfrak m}:G_{F,\Sigma}\to\mathrm{GL}_2(\mathbb T_{\mathfrak m})
$$

is then a deformation of $\bar\rho_{\mathfrak m}$. If a global deformation problem has been defined with determinant $\psi\chi_\ell^{w+1}$ and local conditions that the representation is proved to satisfy, universality produces a homomorphism

$$
R\longrightarrow\mathbb T_{\mathfrak m}. \tag{19.1}
$$

Surjectivity is often visible because the traces of good Frobenius elements are the Hecke generators. An isomorphism is vastly deeper: it requires comparing tangent spaces, congruence modules, and local deformation conditions. Nothing in the extraction theorem proves it.

The local qualifications of Chapters 11--12 now become structural. One may impose only conditions actually verified for $\rho_{\mathfrak m}$. At $v\nmid\ell$, minimal unramified or established Steinberg conditions are available in the stated regimes. At $v\mid\ell$, the weight-two good-reduction lattice supplies finite-flat torsion only under the integral abelian-scheme hypotheses. A blanket finite-flat condition for arbitrary higher weight or arbitrary localized lattice has not been constructed here.

### 19.2 The compatible-system bridge

For each $\lambda$ we have built a representation whose good-place polynomial is the image in $E_{\pi,\lambda}[X]$ of the single algebraic polynomial

$$
P_{\pi,v}(X)
=X^2-a_v(\pi)X+\psi_\pi(v)q_v^{w+1}
\in E_\pi[X]. \tag{19.2}
$$

This is the visible beginning of a compatible system. It says that away from $v$, the level, and the coefficient residue characteristic, the characteristic polynomial is independent of $\lambda$ before completion. Twists and coefficient conjugation behave as expected, and purity supplies a common weight in the regimes already established.

A full compatible-system theory asks more: uniform control of exceptional sets, independence of conductor and monodromy, comparison at primes above $\ell$, coefficient-field descent, and behavior under restriction and induction. Those questions deserve their own treatment. The present endpoint supplies the indispensable input—one rigorously normalized member at every finite coefficient place and one common collection of algebraic Frobenius polynomials.

### 19.3 Conclusion

The passage from an automorphic form to a Galois representation is not a mysterious interpolation of Hecke eigenvalues. It is an extraction from geometry. A modular or Shimura curve supplies cohomology; the weight supplies its lisse coefficient system; Hecke correspondences and arithmetic Galois act simultaneously; multiplicity one and duality isolate two dimensions. In weight two those dimensions sit in a covariant Jacobian Tate module, so polarization and integral torsion are visible at their source.

The good-prime polynomial is where every convention meets. Book 122 gives geometric Frobenius on untwisted cohomology and the scalar $S_v=\langle v\rangle^{-1}$. Passing to arithmetic Frobenius on the covariant realization replaces $T_v$ by $S_v^{-1}T_v$ and $q_vS_v$ by $q_vS_v^{-1}$. The coefficient system then raises the determinant to $\psi_\pi(v)q_v^{w+1}$. Dimension two turns the resulting annihilating polynomial into the characteristic polynomial, and polarization confirms its determinant.

Integral arithmetic requires more restraint. Congruent eigensystems do not split by integral idempotents; a localization is not an eigenspace; a stable lattice is not unique; and residual characteristic polynomials remember only semisimplification. The Cayley--Hamilton determinant preserves the degree-two system over a local Hecke algebra without assuming freeness. Absolute residual irreducibility is the decisive condition that upgrades trace and determinant to a genuine rank-two family representation.

At good places the result is exact: unramifiedness and the full arithmetic-Frobenius polynomial. At bad places it says precisely what the geometry proves—semistable Steinberg monodromy and finite-flat weight-two torsion in their proper regimes—and no more. This disciplined boundary is what makes the construction reliable enough for the next stage. The local Hecke representation can now receive a map from a global deformation ring, while the algebraic polynomials (19.2) point toward the later theory in which the separate $\lambda$-adic realizations are organized into a compatible system.
