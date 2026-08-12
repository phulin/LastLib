# Automorphic Decomposition of Shimura-Curve $H^1$

## Contents

- [1. The realization problem](#1-the-realization-problem)
  - [1.1 Why first cohomology is the right degree](#11-why-first-cohomology-is-the-right-degree)
  - [1.2 The geometric datum](#12-the-geometric-datum)
  - [1.3 Actions and normalization](#13-actions-and-normalization)
  - [1.4 What is proved, and what is not](#14-what-is-proved-and-what-is-not)
- [2. Compact Shimura curves and their components](#2-compact-shimura-curves-and-their-components)
  - [2.1 Complex uniformization](#21-complex-uniformization)
  - [2.2 Compactness and the absence of boundary](#22-compactness-and-the-absence-of-boundary)
  - [2.3 Component-stable curves](#23-component-stable-curves)
  - [2.4 Fine, stacky, and coarse level](#24-fine-stacky-and-coarse-level)
- [3. The cohomology package of a proper curve](#3-the-cohomology-package-of-a-proper-curve)
  - [3.1 Betti, de Rham, and etale realizations](#31-betti-de-rham-and-etale-realizations)
  - [3.2 Jacobians and the integral lattice](#32-jacobians-and-the-integral-lattice)
  - [3.3 Pairings and Tate twists](#33-pairings-and-tate-twists)
  - [3.4 Galois descent](#34-galois-descent)
- [4. Hecke correspondences on the curve](#4-hecke-correspondences-on-the-curve)
  - [4.1 The two-legged construction](#41-the-two-legged-construction)
  - [4.2 Composition, transpose, and component routing](#42-composition-transpose-and-component-routing)
  - [4.3 Agreement with adelic convolution](#43-agreement-with-adelic-convolution)
  - [4.4 The common rational and integral actions](#44-the-common-rational-and-integral-actions)
- [5. The compact automorphic spectrum](#5-the-compact-automorphic-spectrum)
  - [5.1 Automorphic representations of the quaternion algebra](#51-automorphic-representations-of-the-quaternion-algebra)
  - [5.2 Fixed level and multiplicity spaces](#52-fixed-level-and-multiplicity-spaces)
  - [5.3 Quaternionic multiplicity one](#53-quaternionic-multiplicity-one)
  - [5.4 Characters and noncharacters](#54-characters-and-noncharacters)
- [6. Matsushima's formula for the curve](#6-matsushimas-formula-for-the-curve)
  - [6.1 Differential forms as automorphic cochains](#61-differential-forms-as-automorphic-cochains)
  - [6.2 Relative Lie algebra cohomology](#62-relative-lie-algebra-cohomology)
  - [6.3 Harmonic forms and the direct sum](#63-harmonic-forms-and-the-direct-sum)
  - [6.4 Hecke equivariance](#64-hecke-equivariance)
- [7. The archimedean weight-two calculation](#7-the-archimedean-weight-two-calculation)
  - [7.1 The tangent weights of the half-plane](#71-the-tangent-weights-of-the-half-plane)
  - [7.2 Holomorphic and antiholomorphic discrete series](#72-holomorphic-and-antiholomorphic-discrete-series)
  - [7.3 Compact real factors and parallel weight two](#73-compact-real-factors-and-parallel-weight-two)
  - [7.4 Exclusion of all other constituents](#74-exclusion-of-all-other-constituents)
- [8. The complex automorphic decomposition](#8-the-complex-automorphic-decomposition)
  - [8.1 The decomposition theorem](#81-the-decomposition-theorem)
  - [8.2 Exact multiplicities](#82-exact-multiplicities)
  - [8.3 Holomorphic differentials](#83-holomorphic-differentials)
  - [8.4 Relation with global Jacquet--Langlands](#84-relation-with-global-jacquet--langlands)
- [9. Rational structures and coefficient fields](#9-rational-structures-and-coefficient-fields)
  - [9.1 The finite correspondence algebra](#91-the-finite-correspondence-algebra)
  - [9.2 Semisimplicity and rational blocks](#92-semisimplicity-and-rational-blocks)
  - [9.3 Hecke fields, fields of definition, and Schur indices](#93-hecke-fields-fields-of-definition-and-schur-indices)
  - [9.4 Galois conjugation of packets](#94-galois-conjugation-of-packets)
- [10. Isolating two-dimensional constituents](#10-isolating-two-dimensional-constituents)
  - [10.1 Minimal-level eigenpackets](#101-minimal-level-eigenpackets)
  - [10.2 Old level and the multiplicity module](#102-old-level-and-the-multiplicity-module)
  - [10.3 The double-centralizer extraction](#103-the-double-centralizer-extraction)
  - [10.4 Independence of auxiliary splitting data](#104-independence-of-auxiliary-splitting-data)
  - [10.5 The polarized double-centralizer](#105-the-polarized-double-centralizer)
- [11. Hodge, de Rham, and Galois realizations](#11-hodge-de-rham-and-galois-realizations)
  - [11.1 Weight-one Hodge structures](#111-weight-one-hodge-structures)
  - [11.2 De Rham blocks](#112-de-rham-blocks)
  - [11.3 Etale blocks and continuous Galois action](#113-etale-blocks-and-continuous-galois-action)
  - [11.4 Duality on an isolated constituent](#114-duality-on-an-isolated-constituent)
  - [11.5 Component covariance and the determinant line](#115-component-covariance-and-the-determinant-line)
- [12. Good primes and Frobenius](#12-good-primes-and-frobenius)
  - [12.1 The good-prime hypotheses](#121-the-good-prime-hypotheses)
  - [12.2 The geometric Frobenius polynomial](#122-the-geometric-frobenius-polynomial)
  - [12.3 What the quadratic relation does and does not prove](#123-what-the-quadratic-relation-does-and-does-not-prove)
  - [12.4 Arithmetic Frobenius and the covariant Tate module](#124-arithmetic-frobenius-and-the-covariant-tate-module)
- [13. Integral lattices, congruences, and boundary phenomena](#13-integral-lattices-congruences-and-boundary-phenomena)
  - [13.1 The natural cohomological lattice](#131-the-natural-cohomological-lattice)
  - [13.2 Projector denominators and saturation](#132-projector-denominators-and-saturation)
  - [13.3 Coarse-level denominators](#133-coarse-level-denominators)
  - [13.4 What compactness removes](#134-what-compactness-removes)
- [14. Examples and diagnostic calculations](#14-examples-and-diagnostic-calculations)
  - [14.1 A minimal packet](#141-a-minimal-packet)
  - [14.2 An old packet](#142-an-old-packet)
  - [14.3 A component-permuting central operator](#143-a-component-permuting-central-operator)
  - [14.4 Four normalization failures](#144-four-normalization-failures)
- [15. The automorphic realization theorem](#15-the-automorphic-realization-theorem)
  - [15.1 Complete statement](#151-complete-statement)
  - [15.2 Proof](#152-proof)
  - [15.3 Hypothesis and dependency ledger](#153-hypothesis-and-dependency-ledger)
  - [15.4 Conclusion](#154-conclusion)

## 1. The realization problem

A compact Shimura curve sits at a meeting point of two theories. Analytically it is an arithmetic quotient of a half-plane, so its differential forms are controlled by automorphic representations. Algebraically it is a smooth projective curve over a number field, so its first cohomology carries rational, Hodge, integral, and Galois structures. The aim of this book is to prove that these descriptions select exactly the same finite collection of parallel-weight-two packets and to keep every multiplicity and coefficient field visible while passing between them.

### 1.1 Why first cohomology is the right degree

At the unique split real place of the quaternion algebra, the symmetric domain is a half-plane. Its complex cotangent space has one holomorphic and one antiholomorphic direction. The discrete series of minimal weight two contributes one class in each of these directions and contributes in no other degree. Constant coefficients therefore put a weight-two automorphic representation in $H^1$.

This statement already predicts the number two which later appears in arithmetic. One automorphic occurrence and one finite-level vector contribute a pair

$$
H^{1,0}\oplus H^{0,1}.
$$

That pair is two-dimensional, but it should not be confused with automorphic multiplicity or with the dimension of the level-invariant space. At old level, one global representation can have several fixed vectors; its cohomological contribution then has dimension twice that number. The two-dimensional arithmetic constituent is recovered as the multiplicity space for the finite Hecke module, not by pretending that the old eigenspace is itself two-dimensional.

The character spectrum provides an equally important test. A one-dimensional automorphic representation is trivial on the derived real group. Its invariant differential forms occur in degrees zero and two, not in degree one. Thus a proper Shimura curve has no character contribution to $H^1$. This is an archimedean vanishing statement, not a subtraction of cusps.

### 1.2 The geometric datum

Let $F$ be a totally real number field and let $B/F$ be a quaternion division algebra split at exactly one real embedding $\tau_0$. Put

$$
G=\operatorname{Res}_{F/\mathbf Q}B^\times
$$

or, when explicitly stated, take a connected central modification with the same adjoint datum and a genuine quaternionic PEL realization. Let $(G,X)$ be the resulting one-dimensional Shimura datum and let $E$ be its reflex field. For the basic group, $E$ is the embedded copy $\tau_0(F)$.

Fix a compact open $K\subset G(\mathbf A_f)$. At first we assume that $K$ is neat and detects the rational center. Fix also a union $\mathcal C$ of connected-component labels which is stable under the canonical action of $G_E$ and under every Hecke correspondence used below. The canonical model of this union is denoted

$$
C_K/E.
$$

It is a smooth projective curve, possibly disconnected geometrically. Writing a union rather than an arbitrarily chosen component is necessary: a geometric component need not be defined over $E$, and a Hecke operator can route one component to another.

There is a small but essential scope convention behind the phrase “every Hecke correspondence used below.” The packet-by-packet formulas use the full finite Hecke algebra, including the central and component translations needed to distinguish full automorphic representations. Accordingly, $\mathcal C$ is taken to be a full orbit for that routing algebra; for the basic group this is the full canonical curve at level $K$. A proper union may instead be studied with only the subalgebra preserving it, but then restriction can mix automorphic representations differing by component characters. In that setting the canonical statements are the rational finite-Hecke blocks of Chapters 9--11, not the individual-$\Pi$ dimension formula (8.2), unless a component-character idempotent has first separated the packet. This qualification prevents the cohomology of one component from being counted once for every character of the component permutation group.

The preceding construction of quaternionic PEL curves supplies the exact hypotheses behind this notation: a positive weight-one PEL realization, the determinant law, compatible lattice and polarization type, a selected integral component union, and fine level when a universal abelian family is invoked. The cohomology of $C_K$ depends only on the curve; it is not the cohomology of that universal abelian family.

### 1.3 Actions and normalization

The rational group acts on the left of the analytic double quotient and the finite adelic group acts by right translation. For $a\in G(\mathbf A_f)$ set

$$
K_a=K\cap aKa^{-1}.
$$

The Hecke span has two finite legs

$$
C_K\xleftarrow{p_1}C_{K_a}\xrightarrow{p_2}C_K,
$$

where $p_1$ forgets level and $p_2$ is right translation by $a$ followed by the required forgetful map. It acts on cohomology by

$$
T(a)=(p_1)_*p_2^*. \tag{1.1}
$$

Thus $p_2$ is the declared source leg and $p_1$ the declared target leg. This orientation, which is easy to reverse when reading the displayed span from left to right, is the unnormalized right-double-coset convention. When

$$
KaK=\coprod_i a_iK,
$$

its action on automorphic functions is $f(g)\mapsto\sum_i f(ga_i)$, with no averaging factor.

Fix a prime $\ell$. We use arithmetic Galois actions. Over $\mathbf F_q$, arithmetic Frobenius is $x\mapsto x^q$ and geometric Frobenius is its inverse. On the Tate twist, arithmetic Frobenius acts on $\mathbf Q_\ell(1)$ by $q$, while geometric Frobenius acts by $q^{-1}$. Thus

$$
H^2(C^\circ_{\overline{\mathbf F}_q},\mathbf Q_\ell)
\simeq\mathbf Q_\ell(-1)
$$

has geometric Frobenius eigenvalue $q$ for every geometrically connected component $C^\circ$. For a disconnected curve, top cohomology is the direct sum of these lines and Frobenius can also permute them. At good places the Hecke polynomial in this book is written for geometric Frobenius on untwisted $H^1$.

At a split hyperspecial finite place $v$, write

$$
T_v=[K_v\operatorname{diag}(\varpi_v,1)K_v],
\qquad
S_v=[K_v\varpi_v I K_v].
$$

The raw polynomial is

$$
P_v(X)=X^2-T_vX+q_vS_v. \tag{1.2}
$$

No normalized Satake square root occurs in (1.2).

### 1.4 What is proved, and what is not

We prove a Hecke-equivariant automorphic decomposition of constant-coefficient $H^1$, including the precise fixed-level and archimedean multiplicities. We descend the decomposition to rational blocks, identify their coefficient fields, transport them to de Rham and etale cohomology, and isolate a two-dimensional Galois-stable multiplicity space from each simple weight-two Hecke block. For the basic group $\operatorname{Res}_{F/\mathbf Q}B^\times$, the contragredient is the canonical finite reduced-norm twist. Its component multiplier is defined after a normal fine refinement, and a pull--trace construction returns the resulting form to the original level. The compact automorphic mass pairing is then symmetric and perfect on the complete finite-level module, including all oldvectors. Factoring the Jacobian polarization through these data gives an alternating self-pairing on the rank-two factor with its exact Tate and central-component twist. Consequently the determinant is known independently, and at a good prime the specialization of (1.2) is the characteristic polynomial even when Frobenius is scalar.

Several nearby statements are deliberately not folded into this theorem. We do not assert irreducibility or semisimplicity of the resulting Galois representation or prove local--global compatibility at bad places. We do not construct residual representations or canonical integral direct summands. For a connected central modification, equality of adjoint data alone does not produce the character identifying a packet with its contragredient; the polarized conclusion is asserted there only under the explicit hypothesis (10.8) on the actual abelian quotient. The determinant identity is a characteristic-zero consequence of the Poincare form and the descended self-transpose return correspondence; perfect integral reduction of the resulting form still requires its discriminant and all projector, component, level-return, and Morita denominators to be units.

The phrase **parallel weight two** will first refer intrinsically to a representation of $B^\times(\mathbf A_F)$: minimal weight-two discrete series at the unique split real place and trivial algebraic type on the compact adjoint group at every ramified real place, with the compatible scalar central character. Local Jacquet--Langlands identifies the latter compact type with weight two. When a global split transfer is already supplied under the exact hypotheses of global Jacquet--Langlands, the same phrase agrees with parallel weight two on $\operatorname{GL}_2(\mathbf A_F)$. We do not use a theorem proved only for a totally definite algebra to manufacture a transfer for an arbitrary one-split-place algebra.

## 2. Compact Shimura curves and their components

The automorphic calculation is clean because the curve is compact. Before using that fact, we recall exactly why it holds and why it does not permit component labels or stack inertia to be ignored.

### 2.1 Complex uniformization

Quaternionic PEL uniformization gives

$$
C_K(\mathbf C)
\simeq
G(\mathbf Q)\backslash
\bigl(X\times G(\mathbf A_f)/K\bigr)^{\mathcal C}. \tag{2.1}
$$

Choose an upper-half-plane component $X^+\simeq\mathfrak H$. For a finite adelic representative $g$, put

$$
\Gamma_g=G(\mathbf Q)_+\cap gKg^{-1}.
$$

At neat level, (2.1) is a disjoint union of Riemann surfaces

$$
\Gamma_g\backslash\mathfrak H. \tag{2.2}
$$

The uniformization theorem proves more than a bijection of points. On a PEL component, the point $[h,g]$ corresponds to the polarized complex torus built from

$$
L_g=V(\mathbf Q)\cap g\widehat\Lambda.
$$

The finite adelic coordinate restores the integral lattice which a rational Hodge structure alone remembers only up to quasi-isogeny. Holomorphic variation of $h$ gives the analytic curve, and normal algebraization identifies it with the canonical model.

### 2.2 Compactness and the absence of boundary

Because $B$ is a division algebra, $PB^\times$ has no proper rational parabolic subgroup. Indeed, a rational parabolic would stabilize a nonzero proper right ideal of $B$, while a division algebra has no such ideal. Conversely, for a split matrix algebra the stabilizer of a line is a rational parabolic and produces cusps. Thus every quotient (2.2) is compact.

The canonical curve is consequently projective. Therefore

$$
H_c^i(C_K,L)=H^i(C_K,L)=H_!^i(C_K,L) \tag{2.3}
$$

for the characteristic-zero coefficient fields used here. No boundary long exact sequence contributes to $H^1$, and there is no Eisenstein cohomology coming from cusps.

Compactness does not eliminate one-dimensional automorphic characters from the discrete spectrum. It merely ensures that they are honest discrete summands rather than boundary terms. Their absence from $H^1$ will be proved by the real cohomology calculation in Chapter 7.

### 2.3 Component-stable curves

The exact component set is

$$
G(\mathbf Q)_+\backslash G(\mathbf A_f)/K. \tag{2.4}
$$

Under the simply connected derived-group and strong-approximation hypotheses already verified for the quaternionic datum, abelianization gives

$$
\pi_0(C_K(\mathbf C))
\simeq
T(\mathbf Q)^\dagger\backslash
\nu(G(\mathbf A_f))/\nu(K). \tag{2.5}
$$

For $G=\operatorname{Res}_{F/\mathbf Q}B^\times$, this becomes

$$
F_+^\times\backslash
\mathbf A_{F,f}^\times/\operatorname{Nrd}(K). \tag{2.6}
$$

Total positivity in (2.6) has two sources: orientation at the split real place and positivity of reduced norms at the Hamiltonian real places.

Canonical reciprocity acts on the left of (2.5), while the two legs of the $a$-span relate a $p_1$-label $c$ to the $p_2$-label $c\nu(a)$. Hence a union $\mathcal C$ must satisfy two conditions:

$$
r(s)\mathcal C=\mathcal C
\quad\text{and}\quad
\mathcal C\nu(a)=\mathcal C. \tag{2.7}
$$

The first gives descent to the desired field; the second makes the correspondence an endomorphism of the chosen union. If the second fails, the correspondence is a map between cohomologies of different unions. Restricting it to one component would be ill typed.

With the right-convolution orientation (1.1), the covariant cohomology operator traces from the $p_2$ endpoint back to the $p_1$ endpoint; as a source-to-target permutation of component summands its displacement is therefore $\nu(a)^{-1}$. The stability condition is unchanged because a finite union is stable under $\nu(a)$ exactly when it is stable under its inverse. Keeping the leg relation and the covariant direction distinct prevents a second hidden inversion.

### 2.4 Fine, stacky, and coarse level

At non-neat level choose a normal fine subgroup $K'\triangleleft K$ with effective deck group $\Delta$. The natural object is the quotient stack $[C_{K'}/\Delta]$; the coarse curve is the finite categorical quotient. With characteristic-zero coefficients, pullback and trace give

$$
H^i(C_K,\mathbf Q)
\simeq H^i(C_{K'},\mathbf Q)^\Delta. \tag{2.8}
$$

The proof is the familiar pair of identities

$$
p_*p^*=|\Delta|,
\qquad
p^*p_*=\sum_{\delta\in\Delta}\delta.
$$

Division by $|\Delta|$ makes invariants exact. Integrally over $\mathbf Z_\ell$, (2.8) need not hold when $\ell\mid|\Delta|$. Stabilizer orders can introduce torsion or destroy a direct-summand description. We therefore prove the rational automorphic decomposition on a neat cover and descend it rationally; every integral statement at coarse level retains this warning.

## 3. The cohomology package of a proper curve

The automorphic spectrum first describes complex cohomology. Arithmetic applications require the rational Betti lattice, the Hodge filtration, the etale lattice, the Jacobian, and the Galois action. For a smooth proper curve these structures are already known to agree with pullback, trace, and finite correspondences.

### 3.1 Betti, de Rham, and etale realizations

For an embedding $E\hookrightarrow\mathbf C$, let

$$
H_B^1=H^1(C_K(\mathbf C),\mathbf Q),
\qquad
H_{\mathrm{dR}}^1=H^1_{\mathrm{dR}}(C_K/E).
$$

Integration gives

$$
H_{\mathrm{dR}}^1\otimes_E\mathbf C
\simeq H_B^1\otimes_{\mathbf Q}\mathbf C. \tag{3.1}
$$

For every prime $\ell$ and every chosen embedding $\bar E\hookrightarrow\mathbf C$, finite-coefficient comparison followed by inverse limits gives

$$
H_B^1\otimes\mathbf Q_\ell
\simeq
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Q_\ell). \tag{3.2}
$$

The integral form is

$$
H^1_B(C_K(\mathbf C),\mathbf Z)\otimes\mathbf Z_\ell
\simeq
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell). \tag{3.3}
$$

For a proper smooth curve the integral group is finite free, so no derived inverse-limit term or torsion correction occurs. Equations (3.1)--(3.3) commute with finite pullback, trace, cup product, transpose, and algebraic correspondences.

### 3.2 Jacobians and the integral lattice

Let $J_K$ be the product of the Jacobians of the geometrically connected components of $C_K$. With the covariant Tate-module convention,

$$
T_\ell J_K
\simeq H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell(1)), \tag{3.4}
$$

and hence

$$
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell)
\simeq T_\ell J_K(-1). \tag{3.5}
$$

If a correspondence is represented by

$$
C_K\xleftarrow{s}Z\xrightarrow{t}C_K,
$$

with $t$ the source leg and $s$ the target leg, it acts on $J_K$ by $s_*t^*$ and on cohomology by the same pull--trace formula. The Kummer isomorphism (3.4) intertwines the two actions. Thus the lattice

$$
\Lambda_\ell=H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell) \tag{3.6}
$$

is canonical, Galois stable, and stable under every integral Hecke correspondence.

### 3.3 Pairings and Tate twists

Cup product and trace give a perfect alternating pairing

$$
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Q_\ell)
\times
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Q_\ell)
\longrightarrow\mathbf Q_\ell(-1). \tag{3.7}
$$

Equivalently, one may pair untwisted $H^1$ with $H^1(1)$ into the trivial coefficient. The two formulations must not be mixed. From (3.7),

$$
(H^1_{\mathrm{et}})^\vee\simeq H^1_{\mathrm{et}}(1). \tag{3.8}
$$

For a correspondence $T$, transpose is adjoint:

$$
\langle Tx,y\rangle
=\langle x,T^t y\rangle. \tag{3.9}
$$

For the adelic correspondence, $T(a)^t=T(a^{-1})$, with any central similitude factor already included in the chosen double-coset convention. The same adjunction is Rosati adjunction on $J_K$.

This statement is integral and componentwise. On

$$
\Lambda_\ell=H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell)
$$

the cup--trace form is perfect with values in $\mathbf Z_\ell(-1)$, and the summands belonging to distinct geometric connected components are orthogonal. It is the Weil pairing transported from the product principal polarization on the component Jacobians. Thus no degree, Haar-volume, or similitude scalar may be inserted into (3.9). A central factor appears only when the inverse double coset is rewritten using the chosen generators. In particular, at a split hyperspecial place,

$$
T_v^t=S_v^{-1}T_v,
\qquad
S_v^t=S_v^{-1}.
$$

These are identities before a central character is specialized. They are the geometric source of every central twist in the packet pairing below.

### 3.4 Galois descent

The canonical descent of Hecke spans proves that every correspondence used here is defined over $E$ on the stable component union. Pullback and trace are functorial under base change, so

$$
T(a)\sigma=\sigma T(a)
\qquad(\sigma\in G_E). \tag{3.10}
$$

Thus there are commuting actions

$$
G_E\longrightarrow\operatorname{Aut}_{\mathbf Q_\ell}(H^1_{\mathrm{et}}),
\qquad
\mathcal H_K\longrightarrow\operatorname{End}_{\mathbf Q_\ell}(H^1_{\mathrm{et}}). \tag{3.11}
$$

Descent of a numerical characteristic polynomial would not suffice for (3.10); it is descent of the cycle and its two legs which supplies equivariance. If a correspondence is defined only over $E'/E$, its operator commutes only with $G_{E'}$ unless an actual descent datum is given.

## 4. Hecke correspondences on the curve

The cohomological and automorphic decompositions agree only after their Hecke actions have been shown to be the same action. This chapter fixes that identification before any eigensystem is chosen.

### 4.1 The two-legged construction

For $a\in G(\mathbf A_f)$, the inclusion $K_a\subset K$ gives the first finite map $p_1$. Right translation sends level $K_a$ to $a^{-1}K_aa$, which is contained in $K$; the translated map followed by forgetting level is $p_2$. The second forgetful map is indispensable: right translation alone does not have target $C_K$.

Define $T(a)$ by (1.1), pulling back along the translated leg $p_2$ and tracing along the forgetful leg $p_1$. If one instead uses $(p_2)_*p_1^*$, the right-coset calculation gives $Ka^{-1}K$. If $a$ is integral relative to the PEL lattice, the intermediate curve carries a universal isogeny whose kernel is the corresponding finite lattice quotient. The existence of that isogeny proves the moduli interpretation, while the two finite legs already suffice to define the action on constant-coefficient cohomology.

The graph test fixes variance. For a finite map $f:X\to Y$, its graph from $X$ to $Y$ acts by $f_*$, and its transpose acts by $f^*$. Consequently $f_*f^*=\deg(f)$ on $H^1(Y)$, while $f^*f_*$ on $H^1(X)$ need not be scalar.

### 4.2 Composition, transpose, and component routing

Fiber products of intermediate level curves encode two-step lattice modifications. If $m(a,b;c)$ is the coefficient of $1_{KcK}$ in $1_{KaK}*1_{KbK}$ for $\operatorname{vol}(K)=1$, then decomposition of the fiber product into connected finite correspondences, with scheme-theoretic multiplicity, gives

$$
T(a)T(b)=\sum_c m(a,b;c)T(c). \tag{4.1}
$$

Proper base change and the projection formula prove that the action of the left side equals the sum on the right.

Interchanging the two legs gives

$$
T(a)^t=T(a^{-1}). \tag{4.2}
$$

Under (2.5), the first leg retains the component label and the second multiplies it by $\nu(a)$. Formula (4.2) reverses that displacement. These statements ensure that convolution, adjunction, and component routing are three shadows of one finite span.

### 4.3 Agreement with adelic convolution

Normalize Haar measure by $\operatorname{vol}(K)=1$. Write

$$
KaK=\coprod_i a_iK.
$$

Over a point $[h,g]$, the fiber of $p_1$ is indexed, with stabilizer multiplicity, by the right cosets $a_iK$. Evaluation through the translated source leg sends those points to $[h,ga_i]$. Pulling back through $p_2$ and then tracing along $p_1$ therefore gives

$$
(T(a)f)(g)=\sum_i f(ga_i). \tag{4.3}
$$

More explicitly, one first evaluates the pulled-back class $p_2^*f$ at those points and then applies the trace $(p_1)_*$. This proves that the oriented geometric pull--push is the unnormalized right-convolution operator. No degree denominator occurs. At non-neat level, one proves (4.3) on a neat normal cover and descends the equivariant trace; counting one coarse isomorphism class per orbit would undercount stabilizers.

At distinct finite places the operators commute. At a split hyperspecial place the local spherical Hecke algebra is commutative and generated by $T_v,S_v,S_v^{-1}$. At level primes the oriented operator $U_v$ can have a distinct adjoint and is not assigned the good-prime polynomial (1.2).

### 4.4 The common rational and integral actions

Let $\mathbb T_K^{\mathrm{abs}}$ be the integral algebra generated by the chosen double cosets. It maps to the endomorphism rings of

$$
H_B^1(C_K,\mathbf Z),\quad
J_K,\quad T_\ell J_K,\quad
H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell),
$$

and to the corresponding automorphic fixed-level space. These maps need not have the same kernel; “the same Hecke algebra” means that they arise from the same abstract correspondences and have compatible operator labels.

Comparison isomorphisms commute with these actions because they commute separately with pullback and trace. Hence every Hecke operator has one rational Betti characteristic polynomial, whose de Rham and etale characteristic polynomials are obtained by scalar extension. Integral cycles preserve the Betti and etale lattices, so those characteristic polynomials lie in $\mathbf Z[X]$ on the full cohomology, though individual rational blocks can require a number field.

## 5. The compact automorphic spectrum

We now turn from geometry to the right regular action on the compact quaternionic quotient. The key outputs already established for a quaternion division algebra are restricted tensor factorization, finite fixed-level spaces, and multiplicity one.

### 5.1 Automorphic representations of the quaternion algebra

Let

$$
[PG]=Z(\mathbf A)G(\mathbf Q)\backslash G(\mathbf A).
$$

Since $B$ is a division algebra, $[PG]$ is compact. For a compatible unitary central character $\omega$, let $L^2(G,\omega)$ be the space of functions on $G(\mathbf Q)\backslash G(\mathbf A)$ with the prescribed $Z(\mathbf A)$-equivariance, square-integrable over $[PG]$. The trivial-character case is ordinary $L^2([PG])$. Its right regular representation has a purely discrete decomposition

$$
L^2(G,\omega)
\simeq
\widehat\bigoplus_{\Pi}
\mathcal M(\Pi)\widehat\otimes\Pi. \tag{5.1}
$$

If the component datum allows several compatible finite central characters, the automorphic space is the finite direct sum of these $\omega$-spaces. Writing $Z(\mathbf A)$ in the denominator while simultaneously allowing nontrivial central equivariance would be ill typed; the projective quotient is used only for the norm.

Every irreducible automorphic representation factors uniquely as a restricted tensor product

$$
\Pi\simeq\bigotimes_v'\Pi_v. \tag{5.2}
$$

At almost every finite place, $B$ is split, $\Pi_v$ is spherical, and $\Pi_v^{K_v}$ is a line. Its spherical Hecke character gives raw eigenvalues $t_v(\Pi),s_v(\Pi)$ and polynomial

$$
X^2-t_v(\Pi)X+q_vs_v(\Pi). \tag{5.3}
$$

The factors at the unique split real place are representations of $\operatorname{GL}_2(\mathbf R)$ after choosing a splitting; the other real factors are finite-dimensional representations of $\mathbf H^\times$.

### 5.2 Fixed level and multiplicity spaces

Let $K_\infty$ be a product of maximal compact subgroups, used here only to name compact types. It is distinct from the symmetric-space stabilizer $K_\infty^\dagger$ of Chapter 6, which also contains the connected split center and uses the connected rotation group at the active place. Taking $K$-fixed vectors in (5.1) and selecting an irreducible $K_\infty$-type $\tau$ yields

$$
\mathcal A(K,\tau)[\Pi]
\simeq
\mathcal M(\Pi)\otimes
\operatorname{Hom}_{K_\infty}(\tau,\Pi_\infty)
\otimes\Pi_f^K. \tag{5.4}
$$

The three factors answer different questions. The multiplicity space counts automorphic embeddings; the Hom space counts occurrences of the chosen real compact type inside one representation; the last factor counts level vectors. Fixed level and fixed archimedean type make the total space finite-dimensional, so only finitely many $\Pi$ contribute.

Old level enlarges $\Pi_f^K$ without changing $\mathcal M(\Pi)$. At a split place the newvector line can grow into a multi-dimensional oldspace. At a division place a normal principal congruence subgroup can fix either zero or the entire finite-dimensional local representation. Neither phenomenon is repeated global occurrence.

### 5.3 Quaternionic multiplicity one

For a division quaternion algebra, every irreducible automorphic representation occurs with multiplicity one:

$$
\dim\mathcal M(\Pi)=1. \tag{5.5}
$$

The result is stronger than compactness. Compactness gives only finite multiplicity. It is also not a consequence of the tempting additive theta kernel on the four-dimensional space underlying $B$. Poisson summation does transpose that kernel, but its operator on a $\Pi$-isotypic summand is

$$
1_{\mathcal M(\Pi)}\otimes \Pi(f),
$$

so it cannot detect off-diagonal endomorphisms of $\mathcal M(\Pi)$. Treating those kernels as though they separated the multiplicity space would assume the desired conclusion.

The proved argument is instead the character-clean two-place trace comparison. At two division places, elliptic transfer kills induced traces and split regular orbital integrals. After norm characters and the scalar germ are removed by finite interpolation, the compact quaternionic trace is compared with the cuspidal $\operatorname{GL}_2$ trace. Global Whittaker multiplicity one and strong multiplicity one leave at most one split cuspidal constituent with the prescribed good Hecke data. At every ramified place, the elliptic character coefficients satisfy a Bessel bound. The quaternionic occurrence multiplicity is a positive integer equal to a product of those coefficients, each of absolute value at most one; hence it equals one. This proof applies to every quaternion division algebra and does not require total definiteness or global Jacquet--Langlands as an input.

For a norm character, multiplicity one is elementary: a function transforming by that character is determined by its value at the identity. We retain the line $\mathcal M(\Pi)$ in canonical formulas because it has no preferred basis, even though its dimension is one.

### 5.4 Characters and noncharacters

Every one-dimensional automorphic representation factors through reduced norm. Such characters occur discretely and with multiplicity one. They should not be called Eisenstein boundary classes: the curve is compact and has no boundary.

The distinction relevant to $H^1$ is instead archimedean. A norm character is trivial on the real derived group. Relative cohomology of the trivial derived representation is generated in degrees zero and two by constants and the invariant area form. It vanishes in degree one. Hence norm characters contribute to $H^0$ and $H^2$, with component characters where permitted, but not to $H^1$.

All of $H^1$ therefore belongs to noncharacter representations. This fact makes the degree-one decomposition unusually clean: there is neither a geometric boundary quotient nor a character projector to remove.

## 6. Matsushima's formula for the curve

The analytic bridge from differential forms to automorphic representations is Matsushima's formula. In dimension one it can be proved directly from invariant differential forms and compact Hodge theory.

### 6.1 Differential forms as automorphic cochains

At the active split real place, let $K_{\tau_0}^0\simeq\operatorname{SO}(2)$ be the stabilizer of a point of the chosen half-plane component. Adjoin the connected real split center at every real place and the full connected compact adjoint factors at the ramified real places; denote the resulting stabilizer by $K_\infty^\dagger$. Thus the active factor is $\mathbf R_{>0}\operatorname{SO}(2)$, not $\operatorname O(2)$, and the positive central direction has been divided out. On Lie algebras we have

$$
\mathfrak g_\mathbf C
=\mathfrak k_\mathbf C^\dagger\oplus\mathfrak p_\mathbf C,
$$

where $\mathfrak p_\mathbf C$ is the complexified tangent space of $X$. Using a maximal compact alone would leave an extra central tangent line and would put the same semisimple class in two adjacent degrees. A differential $q$-form on the quotient is equivalently a smooth function

$$
\Phi:G(\mathbf Q)\backslash G(\mathbf A)
\longrightarrow \bigwedge^q\mathfrak p_\mathbf C^*
$$

which is right $K$-invariant at finite places, is invariant under the connected split center in the constant-coefficient normalization, and transforms under the compact part of $K_\infty^\dagger$ by the exterior cotangent representation. Thus the de Rham complex is

$$
C^q_{\mathrm{aut}}
=\operatorname{Hom}_{K_\infty^\dagger}
(\bigwedge^q\mathfrak p_\mathbf C,
\mathcal A(G)^K). \tag{6.1}
$$

On each connected chart this is the ordinary complex of smooth differential forms on $\Gamma_g\backslash\mathfrak H$. The exterior derivative agrees with the relative Lie algebra differential because both differentiate the right regular action and use the bracket to correct alternation.

### 6.2 Relative Lie algebra cohomology

For an admissible real representation $V$, define

$$
C^q(\mathfrak g,K_\infty^\dagger;V)
=\operatorname{Hom}_{K_\infty^\dagger}
(\bigwedge^q\mathfrak p_\mathbf C,V). \tag{6.2}
$$

Its differential is

$$
\begin{aligned}
(d\varphi)(X_0,\ldots,X_q)
&=\sum_i(-1)^iX_i\varphi(X_0,\widehat X_i,\ldots,X_q)\\
&\quad+\sum_{i<j}(-1)^{i+j}
\varphi([X_i,X_j]_{\mathfrak p},X_0,\widehat X_i,\widehat X_j,\ldots,X_q).
\end{aligned}
$$

In our symmetric rank-one space, $[\mathfrak p,\mathfrak p]\subset\mathfrak k^\dagger$, so the projected bracket term vanishes. The infinitesimal action remains, and its kernel detects precisely those compact types which can be harmonic differential forms.

The invariance in (6.2) includes the positive split center. If that center acts nontrivially after tensoring with the coefficient system, its one-dimensional relative complex is contractible and the entire cohomology vanishes. Constant coefficients therefore impose central cancellation rather than allowing an unnoticed norm-power twist.

Inserting the smooth vectors of (5.1) into (6.1) gives a direct sum of the complexes (6.2), tensored with $\mathcal M(\Pi)$ and $\Pi_f^K$.

### 6.3 Harmonic forms and the direct sum

Because $C_K(\mathbf C)$ is compact, every de Rham class has a unique harmonic representative. The Laplacian is elliptic and has finite-dimensional kernel. On automorphic cochains it commutes with the right regular action and with the finite Hecke action.

Consequently only finitely many summands of the Hilbert direct sum (5.1) meet the harmonic kernel in a fixed degree. Taking kernels therefore commutes with the automorphic direct sum. We obtain

$$
H_B^q(C_K,\mathbf C)
\simeq
\bigoplus_\Pi
\mathcal M(\Pi)\otimes\Pi_f^K\otimes
H^q(\mathfrak g,K_\infty^\dagger;\Pi_\infty). \tag{6.3}
$$

For the full component-routing orbit fixed in Section 1.2, the two orientations and all compatible component characters are retained in the automorphic sum. For a proper union with a smaller preserving algebra, one first applies its open-and-closed component projector to the full formula and groups the representations that it mixes. Formula (6.3) is finite in each degree.

This proof does not interchange cohomology with an uncontrolled infinite algebraic sum. Compact Hodge theory first reduces to a finite-dimensional harmonic kernel, and only then is the spectral decomposition applied.

### 6.4 Hecke equivariance

The finite adelic action on $\Pi_f^K$ in (6.3) is convolution with characteristic functions of double cosets. Chapter 4 proved that this is exactly the pull--push action of the algebraic Hecke span. Therefore (6.3) is Hecke equivariant with the operator names fixed by (4.3).

The same argument gives adjunction. Inversion is the adjoint of right convolution under the automorphic $L^2$ pairing, and transpose is the adjoint of pull--push under Poincare duality. Both send $a$ to $a^{-1}$, so the analytic and geometric adjoint operations agree.

The agreement includes the form itself, not only its adjoints. On differential forms the Betti Poincare pairing is

$$
(\alpha,\beta)\longmapsto
\int_{C_K(\mathbf C)}\alpha\wedge\beta.
$$

For a packet $\Pi$, this first pairs its automorphic realization with the contragredient realization. If a finite-order character twist through the actual abelian quotient identifies those two packets and is trivial on $\nu(K)$, multiplication by that character turns the mass pairing into a bilinear form on one finite-level module. Its finite/component factor is symmetric: it is an integral, or a finite component-weighted sum, of a pointwise product. The exterior factor in degree one is alternating. Pullback and trace commute with the calculation. Section 10.5 will first make the twisting operator at a sufficiently fine level and then return it to an arbitrary level; no same-level preservation is being assumed here.

## 7. The archimedean weight-two calculation

Formula (6.3) becomes a classification only after computing its real cohomology. Since there is exactly one noncompact rank-one factor, the calculation is short enough to make explicit.

### 7.1 The tangent weights of the half-plane

At the active real place, pass first to the identity component and write $K^0\simeq\operatorname{SO}(2)$. If $r(\theta)$ is rotation through $\theta$, the complex cotangent representation splits as

$$
\mathfrak p_\mathbf C^*
=\mathfrak p^{1,0,*}\oplus\mathfrak p^{0,1,*}, \tag{7.1}
$$

where the two lines have $K^0$-weights $2$ and $-2$. Thus a degree-one relative cochain can exist only if the real representation contains one of these two $K^0$-types.

The trivial representation has no such type, so its degree-one cochain space is zero. It has invariant cochains in degrees zero and two. This proves the character vanishing asserted in Section 5.4.

### 7.2 Holomorphic and antiholomorphic discrete series

Let $D_2^+$ and $D_2^-$ denote the discrete series with minimal $K^0$-types $2$ and $-2$. In (6.2), each has a one-dimensional degree-one cochain space. The neighboring $K^0$-types occur only on one side of the minimal type, so the relative differential into and out of this cochain is zero. Hence

$$
H^q(\mathfrak{gl}_2, \mathbf R_{>0}K^0;D_2^\pm)
=
\begin{cases}
\mathbf C,&q=1,\\
0,&q\ne1.
\end{cases} \tag{7.2}
$$

The $+$ class has Hodge type $(1,0)$ and the $-$ class has type $(0,1)$. For the full real group, the cohomological representation contains the two orientations; on the complete algebraic curve its relative cohomology is

$$
A^1(\Pi_{\tau_0})
=\mathbf C\eta^+\oplus\mathbf C\eta^-. \tag{7.3}
$$

The real structure on the local $D_2$ exchanges $\eta^+$ and $\eta^-$. Globally, complex conjugation also conjugates the finite Hecke module, so it can carry the $\Pi$ summand to the $\overline\Pi$ summand rather than preserve one coefficient embedding. A component presentation using only $X^+$ does not discard the antiholomorphic direction: holomorphic and antiholomorphic differential forms both live on the same Riemann surface.

There are two convention checks hidden in this compact calculation. First, the relative group is $K_{\tau_0}^\dagger=\mathbf R_{>0}\operatorname{SO}(2)$, so the positive split center has been removed but the reflection in $\operatorname O(2)/\operatorname{SO}(2)$ has not been used to identify the two orientation lines. Taking invariants under the full orthogonal group would retain only one combination and would compute a different quotient. Second, the full $\operatorname{GL}_2(\mathbf R)$ representation $D_2$ restricts to $D_2^+\oplus D_2^-$ on the positive-determinant component. Thus the two lines in (7.3) are archimedean cohomology, not two automorphic occurrences.

### 7.3 Compact real factors and parallel weight two

At every real place $\tau\ne\tau_0$, $B_\tau^\times/\mathbf R^\times$ is compact. Constant coefficients require the trivial representation of this compact adjoint group. A scalar character may remain on the center, but it is fixed by the global central compatibility condition.

Under local real Jacquet--Langlands, the trivial compact algebraic type corresponds to discrete series of minimal weight two. At the active split place, (7.2) already selects the same minimal weight. We therefore call an automorphic representation **parallel weight two** when

- $\Pi_{\tau_0}$ is the weight-two cohomological discrete series;
- every compact real adjoint factor acts trivially;
- the connected real center acts trivially in the unitary constant-coefficient normalization, while any remaining finite scalar action is compatible with the rational center and the selected component data.

This definition is intrinsic to the quaternionic representation and makes no unsupported global transfer assertion.

The last clause also fixes the archimedean part of any contragredient character used below. The connected positive center is already killed in the relative complex. At the active place the negative scalar $-1$ is rotation through $\pi$, so the weight-two types $2$ and $-2$ both give the value $1$; at a compact real place the adjoint type is trivial. For the basic group, the central character $\omega_\Pi$ is consequently trivial at infinity and the reduced-norm twist in (10.8) is finite order. For a central modification, the same conclusion is included in the explicit hypothesis on $\kappa_\Pi$; it is not inferred from equality of adjoint groups. In either case the descended component character is even at every real place of $E$.

### 7.4 Exclusion of all other constituents

Suppose $\Pi$ contributes to $H^1$. At a compact real factor, its type must contain the trivial coefficient type, hence must be the required scalar extension of the trivial adjoint representation. At the active factor, the infinitesimal-character homotopy for the relative standard resolution shows that nonzero cohomology forces the same Casimir character as the trivial coefficient system. The rank-one classification and ladder calculation established for $\operatorname{GL}_2(\mathbf R)$ then leave precisely $D_2^+$ and $D_2^-$, joined in the full cohomological representation.

A principal series with the relevant infinitesimal character is the reducible endpoint with trivial quotient and discrete submodule $D_2$. The trivial quotient has no degree-one cochain, while its nontrivial discrete submodule is the weight-two case already listed. Higher discrete series have minimal $K$-weight of absolute value greater than two and cannot pair with (7.1); the limit $D_1$ would require an algebraic coefficient of highest weight $-1$; and principal or complementary series away from the endpoint have the wrong infinitesimal character. Thus no other archimedean type contributes.

We have proved the exact equivalence

$$
H^1(\mathfrak g,K_\infty^\dagger;\Pi_\infty)\ne0
\quad\Longleftrightarrow\quad
\Pi\text{ has parallel weight two}, \tag{7.4}
$$

and in that case the cohomology has dimension two with Hodge types $(1,0)$ and $(0,1)$.

## 8. The complex automorphic decomposition

The spectral, multiplicity, and archimedean calculations can now be assembled. The resulting formula is the analytic heart of the book.

### 8.1 The decomposition theorem

Let $\mathcal P_K$ be the finite set of noncharacter automorphic representations $\Pi$ of $B^\times(\mathbf A_F)$ such that

- $\Pi$ has parallel weight two;
- $\Pi_f^K\ne0$;
- its central and component characters occur on the selected union $\mathcal C$.

Then there is a canonical Hecke-equivariant decomposition

$$
\boxed{
H_B^1(C_K,\mathbf C)
\simeq
\bigoplus_{\Pi\in\mathcal P_K}
\mathcal M(\Pi)\otimes\Pi_f^K\otimes A^1(\Pi_\infty),}
\tag{8.1}
$$

where $\dim\mathcal M(\Pi)=1$ and $\dim A^1(\Pi_\infty)=2$.

**Proof.** Matsushima's formula (6.3) expresses $H^1$ as a sum over all automorphic representations. Section 7.4 shows that precisely the parallel-weight-two representations have nonzero relative cohomology, and (7.3) computes that cohomology. Norm characters vanish in degree one by Section 7.1. Quaternionic multiplicity one gives the dimension of $\mathcal M(\Pi)$. Fixed-level finiteness makes the sum finite. Hecke equivariance was proved in Section 6.4. $\square$

### 8.2 Exact multiplicities

Taking dimensions in (8.1) gives

$$
\dim_\mathbf C H_B^1(C_K,\mathbf C)[\Pi]
=2\dim_\mathbf C\Pi_f^K. \tag{8.2}
$$

More generally, before applying multiplicity one the right side would be

$$
m(\Pi)\cdot\dim\Pi_f^K\cdot2.
$$

Thus every factor in (8.2) has been accounted for. At minimal level, where $\Pi_f^K$ is a line, the packet is two-dimensional. At old level its dimension can be $2r$ with $r=\dim\Pi_f^K$. The number $r$ belongs to local level theory and does not change automorphic multiplicity.

If the selected union contains several component characters above the same derived packet, those are distinct full automorphic representations or distinct finite Hecke modules and must be retained separately. Grouping them by the same away-from-level eigenvalues can create an additional finite multiplicity which is neither $m(\Pi)$ nor $\dim\Pi_f^K$.

### 8.3 Holomorphic differentials

The Hodge decomposition of a proper complex curve is

$$
H_B^1(C_K,\mathbf C)
=H^{1,0}\oplus H^{0,1},
\qquad
H^{0,1}=\overline{H^{1,0}}. \tag{8.3}
$$

Under (8.1), the line $\mathbf C\eta^+$ gives the holomorphic part and $\mathbf C\eta^-$ gives the antiholomorphic part. Hence

$$
H^0(C_K,\Omega^1)
\simeq
\bigoplus_{\Pi\in\mathcal P_K}
\mathcal M(\Pi)\otimes\Pi_f^K\otimes\mathbf C\eta^+. \tag{8.4}
$$

Formula (8.4) is the weight-two differential realization. The action is still the pull--push action fixed in Chapter 4; on differential forms, covariance can transpose an operator if one compares with a differently oriented classical convention. The common right-double-coset convention prevents that ambiguity here.

### 8.4 Relation with global Jacquet--Langlands

At every real place, the local types in Section 7.3 have the parallel-weight-two split shadow. At every finite place where $B$ is split, the local representation and its spherical Hecke character are already representations of $\operatorname{GL}_2(F_v)$. Thus a global Jacquet--Langlands transfer, whenever established for the packet in question, has the same good eigenvalues $t_v,s_v$, the same central character, and parallel weight two.

The global theorem available in the selected range has explicit hypotheses, including its stated inner form and local packet restrictions. Under those hypotheses it preserves multiplicity and coefficient fields. It does not, merely by being a theorem about quaternion algebras, prove transfer for every one-split-place algebra. The decomposition (8.1) needs no such extrapolation: it is a decomposition by automorphic representations of the actual quaternionic group defining the curve.

Consequently there are two legitimate readings of a packet in (8.1). Intrinsically it is a parallel-weight-two quaternionic representation. If an independently justified global transfer $\pi$ exists, it is also the geometric realization of the corresponding parallel-weight-two $\operatorname{GL}_2$ eigensystem. Equality of almost all good Hecke polynomials is then a theorem, not a definition.

## 9. Rational structures and coefficient fields

The direct sum (8.1) is over $\mathbf C$, but the curve and its correspondences are algebraic. Their rational Betti action groups conjugate complex packets into finite rational blocks. The correct language is the finite image algebra, not a choice of eigenvectors.

### 9.1 The finite correspondence algebra

Let $\mathcal H_K$ be the convolution algebra of compactly supported $K$-bi-invariant functions on $G(\mathbf A_f)$ with rational values, enlarged by the component and central correspondences required to separate the chosen full representations. Let

$$
A_{K,\mathbf Q}
=\operatorname{im}\bigl(
\mathcal H_K\longrightarrow\operatorname{End}_{\mathbf Q}(H_B^1)
\bigr). \tag{9.1}
$$

This is finite-dimensional because $H_B^1$ is finite-dimensional. It is stable under the anti-involution induced by transpose. Its complexification acts on (8.1) through the finite Hecke modules $\Pi_f^K$.

At a fixed level only finitely many such modules occur. Restricted tensor factorization and the equivalence between representations generated by $K$-fixed vectors and modules over the full $K$-Hecke algebra show that nonisomorphic finite parts yield nonisomorphic simple Hecke modules. If one retains only the spherical algebra away from a bad set, several nearly equivalent representations or oldvectors can remain grouped together; the full image algebra separates precisely as much as the geometry at level $K$ permits.

### 9.2 Semisimplicity and rational blocks

Choose the positive Hodge Hermitian form obtained from the Poincare polarization and the Weil operator. Algebraic correspondences preserve Hodge type, so they commute with the Weil operator; Poincare adjunction therefore makes transpose their adjoint also for this positive form. Hence $A_{K,\mathbf C}$ is a finite-dimensional adjoint-stable algebra of operators. Its Jacobson radical is adjoint stable. If $x$ lies in the radical, then $x^*x$ is nilpotent and positive semidefinite, hence zero; thus $x=0$. Therefore

$$
A_{K,\mathbf C}\text{ is semisimple}. \tag{9.2}
$$

Faithful scalar extension then shows that $A_{K,\mathbf Q}$ is semisimple. Hence

$$
1=e_1+\cdots+e_r \tag{9.3}
$$

is the unique decomposition into primitive central idempotents over $\mathbf Q$, grouped according to simple rational blocks. Each

$$
H_B^1[e_i]=e_iH_B^1 \tag{9.4}
$$

is a rational Hodge substructure because $e_i$ is represented by a rational combination of algebraic correspondences and preserves Hodge type. A rational sub-Hodge structure of a polarizable Hodge structure is again polarizable, so no self-adjointness of the individual idempotent is being assumed. Tensoring with $\mathbf C$ groups together the complex packets in one algebraic conjugacy orbit, with possible Schur-index multiplicity.

This proof does not assume that a commuting family has a simultaneous eigenbasis. The full finite Hecke algebra can be noncommutative at level primes; semisimplicity follows from the adjoint-stable image.

### 9.3 Hecke fields, fields of definition, and Schur indices

For a complex packet $\Pi$, its good Hecke field is

$$
L_\Pi
=\mathbf Q\bigl(t_v(\Pi),s_v(\Pi):v\notin\Sigma\bigr), \tag{9.5}
$$

with central and component-character values adjoined when they are not already fixed. Since the Hecke operators act on a finite-dimensional rational space, all these values are algebraic and $L_\Pi$ is a number field.

The field $L_\Pi$ is a field of rationality for the good eigensystem. It need not be a field over which the entire simple module $\Pi_f^K$ is defined. A simple factor of $A_{K,\mathbf Q}$ can be a matrix algebra over a division algebra whose center is a number field. Splitting that division algebra may require a finite extension $L/L_\Pi$. This is the Schur-index obstruction.

Accordingly, individual packet projectors are asserted over a finite splitting field $L$, while the sum over the rational conjugacy orbit is defined over $\mathbf Q$. When $\Pi_f^K$ is a one-dimensional simultaneous eigenspace for a commutative Hecke algebra, no nontrivial Schur index occurs and the eigenline is defined over its eigenvalue field.

### 9.4 Galois conjugation of packets

Let $\sigma\in\operatorname{Aut}(\mathbf C)$. Applying $\sigma$ to the rational Hecke matrices and an eigenvector equation gives

$$
t_v(\Pi^\sigma)=\sigma(t_v(\Pi)),
\qquad
s_v(\Pi^\sigma)=\sigma(s_v(\Pi)). \tag{9.6}
$$

The infinity labels remain the algebraic weight-two labels; one does not apply $\sigma$ to a chosen analytic square root of $q_v$. Equation (9.6) shows that conjugation permutes the summands of (8.1). Their orbit sum is the complexification of a rational block (9.4).

Equality of good eigenvalues determines at least a near-equivalence class. When a justified global split transfer and strong multiplicity one apply, it determines the global packet. Without those hypotheses, the full finite Hecke module and central data, rather than the good eigenvalues alone, are used to label the rational block.

## 10. Isolating two-dimensional constituents

The phrase “the two-dimensional constituent” has two meanings which coincide at minimal level and diverge at old level. At minimal level it is the whole eigenspace. At old level it is the multiplicity space of a simple finite Hecke module. The second formulation is the canonical one.

### 10.1 Minimal-level eigenpackets

Suppose a packet $\Pi$ is separated by a commutative Hecke character $\lambda$ and

$$
\dim_L\Pi_f^K=1
$$

over a coefficient field $L$. Since automorphic multiplicity is one and the archimedean cohomology has dimension two, (8.2) gives

$$
\dim_L H_B^1[\lambda]=2. \tag{10.1}
$$

Because only finitely many characters occur, a finite interpolation projector isolates it. If $\mu$ runs over the other characters, choose $T_\mu$ with $\lambda(T_\mu)\ne\mu(T_\mu)$ and put

$$
e_\lambda
=\prod_{\mu\ne\lambda}
\frac{T_\mu-\mu(T_\mu)}
{\lambda(T_\mu)-\mu(T_\mu)}. \tag{10.2}
$$

On the given cohomology space, $e_\lambda$ is an idempotent with image $H_B^1[\lambda]$. Its coefficients lie in a finite extension of the Hecke field. Summing its algebraic conjugates gives the rational orbit projector.

### 10.2 Old level and the multiplicity module

Now let

$$
P_\Pi=\Pi_f^K
$$

have dimension $r>1$ over a splitting field $L$. The whole $\Pi$-block has dimension $2r$ and decomposes as

$$
H_B^1[\Pi]_L\simeq P_\Pi\otimes_L W_\Pi, \tag{10.3}
$$

where

$$
W_\Pi=\mathcal M(\Pi)\otimes A^1(\Pi_\infty)
$$

has dimension two. The finite Hecke algebra acts on $P_\Pi$ and trivially on $W_\Pi$. The Hodge structure lies on $W_\Pi$: it has one holomorphic and one antiholomorphic line.

Choosing a single eigenvector in $P_\Pi$ can fail to be canonical, and at a noncommutative level algebra a simultaneous eigenbasis need not exist. Formula (10.3), rather than a choice of oldform, is the invariant statement.

### 10.3 The double-centralizer extraction

Let $A_L=A_{K,\mathbf Q}\otimes L$, and let $e_\Pi$ be the central idempotent of the chosen simple block. Choose a simple left $A_L$-module $P_\Pi$ occurring in that block. Define

$$
W_{\Pi,B}
=\operatorname{Hom}_{A_L}
(P_\Pi,e_\Pi H_B^1(C_K,L)). \tag{10.4}
$$

Evaluation gives

$$
P_\Pi\otimes_L W_{\Pi,B}
\xrightarrow{\sim}e_\Pi H_B^1(C_K,L). \tag{10.5}
$$

**Proof.** Semisimplicity makes the block a finite direct sum of copies of $P_\Pi$. The multiplicity of $P_\Pi$ is the dimension of the Hom space (10.4). The complex automorphic formula (8.1) shows that this multiplicity is two: one copy for each of $\eta^+$ and $\eta^-$. The evaluation map is therefore an isomorphism after extension to $\mathbf C$, and faithful scalar extension makes it an isomorphism over $L$. $\square$

Because $G_E$ commutes with $A_L$ on etale cohomology, it acts on the analogous Hom space

$$
W_{\Pi,\ell}
=\operatorname{Hom}_{A_{L_\lambda}}
(P_{\Pi,\lambda},e_\Pi H^1_{\mathrm{et}}(C_{K,\bar E},L_\lambda)), \tag{10.6}
$$

and

$$
\dim_{L_\lambda}W_{\Pi,\ell}=2. \tag{10.7}
$$

This is the precise isolation of the two-dimensional constituent at arbitrary level.

### 10.4 Independence of auxiliary splitting data

The module in (10.4) depends on a choice of simple module over a splitting field, but its isomorphism class has the expected controlled ambiguity. If $P_\Pi'$ is another simple model of the same split block, then $P_\Pi'\simeq P_\Pi$, and composition with an isomorphism identifies the Hom spaces. A different isomorphism differs by a scalar by Schur's lemma, so the resulting two-dimensional representation is canonically determined up to isomorphism.

If the coefficient field is enlarged from $L$ to $L'$, flat base change gives

$$
W_{\Pi,B}\otimes_LL'
\simeq W_{\Pi,B}'
$$

and similarly in etale cohomology. Over the center field before splitting, the invariant object is a Morita module for the opposite division algebra. After splitting, one chooses an absolutely simple matrix module and applies (10.4); one does not simply regard the scalar extension of an unsplit simple module as absolutely simple, since it can acquire a matrix multiplicity. The automorphic multiplicity calculation then gives dimension two for the resulting absolute Hom factor. The theorem therefore distinguishes the rational block, which is canonical, from a split rank-two realization, which is canonical up to coefficient extension and isomorphism.

### 10.5 The polarized double-centralizer

The adjoint block is not an unrelated packet. Put $T=G^{\mathrm{ab}}$ and let $\nu:G\to T$ be the actual abelian quotient. For the basic group every contributing packet has a canonical finite-order character $\kappa_\Pi$ such that

$$
\Pi^\dagger=\Pi^\vee\simeq
\Pi\otimes(\kappa_\Pi^{-1}\circ\nu). \tag{10.8}
$$

For $G=\operatorname{Res}_{F/\mathbf Q}B^\times$, $T=\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$, $\nu=\operatorname{Nrd}$, and $\kappa_\Pi$ is the unitary central character $\omega_\Pi$ viewed as a character of the norm target. If $g\mapsto\bar g$ is canonical quaternion conjugation, then $g\mapsto\bar g^{-1}=g/\operatorname{Nrd}(g)$ is the automorphism which, after a splitting, is inner-conjugate to transpose-inverse. The standard contragredient identity therefore descends and gives $\Pi^\vee\simeq\Pi\otimes(\omega_\Pi^{-1}\circ\operatorname{Nrd})$. Section 7.3 makes this twist finite order and trivial at infinity. For a connected central modification, the conclusions of this section instead require (10.8), with a finite-order automorphic character $\kappa_\Pi$ of the relevant adelic quotient of $T$, trivial at infinity, as an additional packet hypothesis. The common adjoint datum does not by itself supply that character, and reduced norm must not be substituted for $\nu$.

There is an important level qualification. Multiplication by $\kappa_\Pi^{-1}\circ\nu$ preserves $K$-invariants only when that character is trivial on $K$. This need not follow from $\Pi_f^K\ne0$. Choose therefore a normal fine subgroup

$$
K^\circ\subset K\cap\ker(\kappa_\Pi\circ\nu). \tag{10.9}
$$

Take the full inverse image of the selected component union at this level. The packet remains present at $K^\circ$. On the finite component set

$$
\Delta_{K^\circ}
=T(\mathbf Q)^\dagger\backslash
\nu(G(\mathbf A_f))/\nu(K^\circ)
$$

the character $\kappa_\Pi$ is well defined. After adjoining its values, define the algebraic component multiplier

$$
M_{\kappa^{-1}}\bigm|_{H^1(C_t,L)}
=\kappa_\Pi(t)^{-1}\operatorname{id}
\qquad(t\in\Delta_{K^\circ}). \tag{10.10}
$$

It is an $L$-linear combination of the identity correspondences on the open-and-closed geometric components. It is defined over the finite component-splitting field, not asserted to be an $E$-rational correspondence. The point of (10.10) is its descent covariance.

First, right convolution and (10.10) give

$$
T(a)M_{\kappa^{-1}}
=\kappa_\Pi(\nu(a))^{-1}
M_{\kappa^{-1}}T(a). \tag{10.11}
$$

Thus $M_{\kappa^{-1}}$ carries the $\Pi$ block to the $\Pi^\dagger$ block, exactly as in (10.8). Second, distinct component summands are orthogonal for Poincare duality, so

$$
M_{\kappa^{-1}}^t=M_{\kappa^{-1}}. \tag{10.12}
$$

Finally, let $r_{(G,X)}$ be the reflex reciprocity morphism and define

$$
\eta_\Pi(\operatorname{Art}_E(s))
=\kappa_\Pi(r_{(G,X)}(s_f))^{-1}, \tag{10.13}
$$

using the positive-at-infinity representative required by component reciprocity. If $\sigma=\operatorname{Art}_E(s)$, left Galois translation and (10.10) give the exact covariance

$$
\sigma M_{\kappa^{-1}}
=\eta_\Pi(\sigma)^{-1}M_{\kappa^{-1}}\sigma. \tag{10.14}
$$

The principal and level ambiguities in (10.13) vanish in the component quotient. For the basic group, at a good place $u$ corresponding to $v$, the reciprocity morphism sends a positive arithmetic-Frobenius uniformizer to the class of $\varpi_v=\operatorname{Nrd}(\operatorname{diag}(\varpi_v,1))$. Here $\kappa_\Pi=\omega_\Pi$, while $S_v$ is right translation by $\varpi_v I$ and hence acts by $s_v(\Pi)=\omega_\Pi(\varpi_v)$. Thus

$$
\eta_\Pi(\operatorname{Frob}^{\mathrm{arith}}_u)
=s_v(\Pi)^{-1},
\qquad
\eta_\Pi(\Phi_u)=s_v(\Pi), \tag{10.15}
$$

where $\Phi_u$ is geometric Frobenius. This is the central/component correction; it is not a Tate twist. For a central modification, (10.15) is asserted only when the same equality has been checked in its actual abelian quotient and for its chosen central generator. Equality of adjoint data with the basic group does not imply that local normalization.

Let $\Omega$ be the alternating Poincare pairing. On the $\Pi$ block at level $K^\circ$ put

$$
\Psi^\circ(x,y)
=\Omega(x,M_{\kappa^{-1}}y). \tag{10.16}
$$

Equations (10.12) and the alternation of $\Omega$ show that $\Psi^\circ$ is alternating. Equations (3.7) and (10.14) say exactly that

$$
\Psi^\circ(\sigma x,\sigma y)
=\chi_\ell(\sigma)^{-1}\eta_\Pi(\sigma)
\Psi^\circ(x,y),
$$

so it is a Galois-equivariant pairing with target $L_\lambda(-1)\otimes\eta_\Pi$. Under the double-centralizer factorization

$$
H^1[\Pi]_{K^\circ}\simeq
P_\Pi^\circ\otimes W_\Pi,
$$

the automorphic calculation of Section 6.4 factors (10.16) as

$$
\Psi^\circ=b_{P,\Pi}^\circ\otimes\psi_\Pi. \tag{10.17}
$$

The finite form $b_{P,\Pi}^\circ$ is symmetric: after the component multiplier is inserted, its mass formula is a component-weighted integral of $f_1(g)f_2(g)$, unchanged when the two finite vectors are interchanged. It is nonzero by the nondegeneracy of the mass pairing between the $\Pi$ and $\Pi^\vee$ factors. Its adjoint rule carries the split simple image algebra to itself, so its radical is a submodule of the simple module $P_\Pi^\circ$; it is therefore zero or all of $P_\Pi^\circ$. Nonzero thus means perfect. Since (10.16) is perfect, $\psi_\Pi$ is also perfect, and its alternation follows from the symmetry of $b_{P,\Pi}^\circ$. This uses the whole oldspace $P_\Pi^\circ$, not a newvector, and remains valid when its dimension is greater than one and its Hecke algebra is noncommutative.

The adjoint on this symmetric finite form is exact. Equations (3.9) and (10.11) give

$$
b_{P,\Pi}^\circ(T(a)p,q)
=\kappa_\Pi(\nu(a))
b_{P,\Pi}^\circ(p,T(a^{-1})q).
$$

At a split hyperspecial place satisfying the local central normalization in (10.15), $T_v^t=S_v^{-1}T_v$ and $\kappa_\Pi(\nu(a_v))=s_v(\Pi)$, so $T_v$ becomes self-adjoint after specialization, while $S_v$ and its inverse remain visible before specialization. The returned form below has the conjugate adjoint transported by $S$; no commutative or self-adjoint level algebra is assumed.

The construction returns to the original, arbitrary level without assuming that the twist preserves $K$. Let $q:C_{K^\circ}\to C_K$ be the level map. On the split packet factors, $q^*$ is

$$
i\otimes1:P_\Pi^K\otimes W_\Pi
\longrightarrow P_\Pi^\circ\otimes W_\Pi. \tag{10.18}
$$

Over a characteristic-zero field, a nondegenerate symmetric form has a nondegenerate subspace of every dimension at most $\dim P_\Pi^\circ$: diagonalize the form and span the required number of nonisotropic basis vectors. The split simple Hecke image on $P_\Pi^\circ$ is its full matrix algebra, so its unit group is $\operatorname{GL}(P_\Pi^\circ)$. It acts transitively on subspaces of a fixed dimension. Hence an invertible $U$ in that image can be chosen with $Ui(P_\Pi^K)$ equal to a nondegenerate subspace. Set $S=Uq^*$. Then

$$
b_{P,\Pi}^K(p,q)
=b_{P,\Pi}^\circ(Ui(p),Ui(q)) \tag{10.19}
$$

is a perfect symmetric form on the complete finite module at level $K$, and

$$
R_{\Pi,K}=S^tM_{\kappa^{-1}}S \tag{10.20}
$$

is an actual coefficient-valued finite-level return correspondence. Because $S$ is built from descended level maps and Hecke correspondences, it commutes with $G_E$. Equations (10.12) and (10.14) therefore give

$$
R_{\Pi,K}^t=R_{\Pi,K},
\qquad
\sigma R_{\Pi,K}
=\eta_\Pi(\sigma)^{-1}R_{\Pi,K}\sigma.
$$

Pull--trace adjunction gives

$$
\Omega_K(x,R_{\Pi,K}y)
=b_{P,\Pi}^K\otimes\psi_\Pi. \tag{10.21}
$$

Thus a perfect alternating rank-two pairing with the same multiplier is obtained at every old level. The returned finite form and return correspondence depend on $K^\circ$ and $U$, and need not change only by a scalar. The rank-two alternating forms themselves do differ by a scalar, because $\bigwedge^2W_\Pi^\vee$ is one-dimensional. Therefore the Galois multiplier, essential self-duality, and determinant are independent of these choices.

There is no hidden Schur-index assumption. If a rational simple factor is $M_n(D)$ over its center, the invariant object before splitting is the corresponding Morita module with its adjoint involution. The mass calculation makes that involution orthogonal after algebraic closure. Choose one finite field $L$ containing the values of $\kappa_\Pi$, splitting the relevant simple factors at both levels, and containing the coefficients of $U$ and the return operator. Only then choose the simple matrix modules and the rank-two Hom factor. Enlarging $L$ base-changes the resulting rank-two representation, multiplier, and determinant, and changing the split models changes them only up to isomorphism. The particular return operator need not descend to the unsplit center, and no scalar-valued form or rank-two vector space is claimed there.

## 11. Hodge, de Rham, and Galois realizations

Once the rational block and its two-dimensional multiplicity space are correctly defined, comparison transports them without changing their dimension or Hecke labels.

### 11.1 Weight-one Hodge structures

Every rational idempotent correspondence preserves the Hodge decomposition. Thus each rational block $eH_B^1$ is a polarizable Hodge structure of weight one. After a splitting field $L$ is chosen, for every embedding $\iota:L\hookrightarrow\mathbf C$ the corresponding multiplicity space has

$$
W_{\Pi,B}\otimes_{L,\iota}\mathbf C
=W_\Pi^{1,0}\oplus W_\Pi^{0,1},
\qquad
\dim W_\Pi^{1,0}=\dim W_\Pi^{0,1}=1. \tag{11.1}
$$

Complex conjugation carries the $(1,0)$ line at $\iota$ to the $(0,1)$ line at the conjugate coefficient embedding and conjugate packet. It exchanges the two lines inside one split packet only when that packet and coefficient embedding are themselves stable under conjugation. Neither line is usually defined over the Hecke field by itself. The rank-two coefficient-field Hodge object is the split realization; the genuinely rational object is the whole algebraic-conjugacy-orbit block.

The alternating Poincare pairing pairs the $\Pi$ block with the adjoint block $\Pi^\dagger$. Under the packet hypothesis stated in Section 10.5, that section constructs the actual component twist at a fine refinement, proves its Galois covariance, and returns it to the chosen level. The compact mass factor gives a Poincare-compatible symmetric form on the complete finite Hecke module, while the exterior factor on the two relative-cohomology lines is alternating. This remains true at old level; all oldvectors lie in the symmetric module $P_\Pi$.

### 11.2 De Rham blocks

Algebraic de Rham comparison (3.1) commutes with Hecke correspondences. Therefore

$$
e_\Pi\bigl(H^1_{\mathrm{dR}}(C_K/E)
\otimes_{\mathbf Q}L\bigr)
$$

has the same finite Hecke factorization as (10.5), now over the coefficient ring $E\otimes_{\mathbf Q}L$. There is no implicit embedding $E\hookrightarrow L$. After passing to any field factor $M$ of $E\otimes_{\mathbf Q}L$, the induced multiplicity module $W_{\Pi,\mathrm{dR},M}$ is two-dimensional over $M$ and has Hodge filtration

$$
0\subset F^1W_{\Pi,\mathrm{dR},M}
\subset F^0W_{\Pi,\mathrm{dR},M}
=W_{\Pi,\mathrm{dR},M}, \tag{11.2}
$$

with $\dim F^1=1$. After extension to $\mathbf C$, $F^1$ becomes $W_\Pi^{1,0}$.

No canonical complement to $F^1$ over $E$ or the Hecke field is asserted. The Hodge decomposition exists over $\mathbf C$; the algebraic de Rham structure supplies only the filtration over the field of definition.

### 11.3 Etale blocks and continuous Galois action

Betti--etale comparison transports the rational projector and the finite Hecke module to etale cohomology. Since every defining correspondence descends to $E$, its image is $G_E$-stable. Equation (10.6) therefore defines a continuous representation

$$
\rho_{\Pi,\lambda}:G_E
\longrightarrow\operatorname{GL}(W_{\Pi,\ell}). \tag{11.3}
$$

Continuity is inherited from the finite-dimensional subquotient of $H^1_{\mathrm{et}}$: the ambient action preserves a lattice and is continuous, and the Hom construction is formed inside a finite-dimensional coefficient space.

At this stage (11.3) is a cohomological constituent. Its dimension, coefficient field, commuting Hecke action, good-prime quadratic Frobenius relation, and adjoint duality are known. For the basic group, or for a packet of a central modification satisfying (10.8), Section 10.5 also supplies the polarized determinant datum. Irreducibility, global semisimplicity, and bad-place local parameters are not consequences of the decomposition. The determinant will be deduced from that polarized datum; the scalar-Frobenius characteristic polynomial additionally requires the local normalization (10.15). Neither is inferred from two-dimensionality alone.

### 11.4 Duality on an isolated constituent

For the self-pairing statements in Sections 11.4--11.5, assume either that $G$ is the basic group or that the packet of the central modification satisfies the explicit essential-self-duality hypothesis (10.8). Without it, equations (11.4)--(11.5) below are the complete duality conclusion.

Let $\Pi^\dagger$ denote the packet on which inverse double cosets act as adjoints. Restricting (3.7) and using (10.5) produces a perfect pairing

$$
W_{\Pi,\ell}\times W_{\Pi^\dagger,\ell}
\longrightarrow L_\lambda(-1), \tag{11.4}
$$

after dual pairings on the finite Hecke modules have been chosen compatibly. Consequently

$$
W_{\Pi,\ell}^\vee
\simeq W_{\Pi^\dagger,\ell}(1). \tag{11.5}
$$

The component multiplier and return correspondence of Section 10.5 identify the adjoint multiplicity factor by

$$
W_{\Pi^\dagger,\ell}
\simeq W_{\Pi,\ell}\otimes\eta_\Pi^{-1}. \tag{11.6}
$$

Factoring (10.21) through the symmetric finite-module form therefore gives a perfect alternating pairing

$$
\psi_\Pi:
W_{\Pi,\ell}\times W_{\Pi,\ell}
\longrightarrow L_\lambda(-1)\otimes\eta_\Pi. \tag{11.7}
$$

Under the preceding packet hypothesis, this is an unconditional characteristic-zero statement at arbitrary old level. It does not assert that (11.7) is perfect on a preferred integral rank-two lattice.

### 11.5 Component covariance and the determinant line

The Galois character in (11.7) is the finite character (10.13), not a relabeling of the Tate twist. The pairing gives the exact essential self-duality

$$
W_{\Pi,\ell}^\vee
\simeq
W_{\Pi,\ell}(1)\otimes\eta_\Pi^{-1}. \tag{11.8}
$$

For a two-dimensional vector space, every nonzero alternating form is a determinant form. Hence a Galois-equivariant alternating pairing with one-dimensional target $M$ has multiplier $\det W$. Since $L_\lambda(-1)\otimes\eta_\Pi$ has character $\chi_\ell^{-1}\eta_\Pi$, (11.7) gives

$$
\boxed{
\det\rho_{\Pi,\lambda}
=\chi_\ell^{-1}\eta_\Pi.} \tag{11.9}
$$

This identity holds on every element of $G_E$ and is independent of semisimplicity. At a good place, (10.15) and $\chi_\ell(\Phi_u)=q_u^{-1}$ give

$$
\det(\Phi_u\mid W_{\Pi,\ell})
=q_us_v(\Pi). \tag{11.10}
$$

In the equal-residue-field range of Chapter 12, $q_u=q_v$. At a real place, Section 7.3 gives $\eta_\Pi(c)=1$, so (11.9) has determinant $-1$ on complex conjugation, as the two Hodge lines require.

## 12. Good primes and Frobenius

At a good finite place, the integral moduli problem compares the Hecke correspondence with Frobenius and Verschiebung. The resulting operator identity holds on the full cohomology and restricts to the two-dimensional constituent. Two-dimensionality alone does not identify its characteristic polynomial in the scalar case; under the polarized packet hypothesis and the local normalization (10.15), the independent determinant (11.10) does.

### 12.1 The good-prime hypotheses

Let $u$ be a finite place of $E$ corresponding to a finite place $v$ of $F$. Assume that the chosen unramified local reflex identification induces the same residue field, and write

$$
q_v=|\kappa(u)|=|\mathcal O_F/v|.
$$

Assume further:

- $B$ and the PEL endomorphism algebra are unramified at $v$;
- the polarization lattice is self-dual, its degree is prime to the residue characteristic, and every local level factor at that characteristic is hyperspecial;
- the determinant local model is the smooth one-dimensional unramified model;
- the added neighbor problem has the standard rank-one incidence local-model diagram;
- the rank-one Hasse invariant is not identically zero on any selected geometric component, equivalently the relevant $\mu$-ordinary locus is dense there;
- the selected component union extends over the local base;
- the level is neat, or the calculation is performed on the stack and descended through a tame neat cover;
- the residue characteristic $p$ is different from $\ell$.

Under these hypotheses the Shimura curve has a smooth proper integral model and $T_v,S_v$ extend with finite locally free legs. Smooth proper base change identifies generic and special-fiber $H^1$, compatibly with Hecke and Galois. In particular the etale representation is unramified at $u$.

Merely assuming that $B_v$ is split is not enough. Ramified level, a non-self-dual lattice, a bad determinant local model, an unproved incidence diagram, or failure of density on a selected component invalidates the two-branch calculation. A residue-degree mismatch would also replace the displayed $q_v$ by the cardinality of the actual reflex-field residue field, so it is excluded explicitly.

### 12.2 The geometric Frobenius polynomial

Let $G_v$ denote geometric Frobenius on untwisted $H^1$. The good-prime correspondence relation gives

$$
\boxed{G_v^2-T_vG_v+q_vS_v=0} \tag{12.1}
$$

on the full cohomology.

The geometric proof identifies the special fiber of the subgroup correspondence with two branches: the Frobenius direction and the Verschiebung direction, with the transported central level recorded by $S_v$. Their multiplicities are one. On the covariant Tate module, if $F_v$ is arithmetic Frobenius, Verschiebung is $q_vF_v^{-1}$. Thus

$$
T_v=q_vF_v^{-1}+S_vF_v.
$$

Substituting $G_v=q_vF_v^{-1}$ after accounting for the twist (3.4) gives (12.1).

### 12.3 What the quadratic relation does and does not prove

At a hyperspecial place, $T_v$ and $S_v$ lie in the center of the full finite $K$-Hecke algebra: the local spherical algebra is commutative and it commutes with all other local factors. They therefore act by scalars on the simple module $P_{\Pi,\lambda}$,

$$
T_v=t_v(\Pi),
\qquad
S_v=s_v(\Pi).
$$

Because Frobenius commutes with the full Hecke image, its action on

$$
P_{\Pi,\lambda}\otimes W_{\Pi,\ell}
$$

is $1\otimes G_v$ on this split block. Restricting (12.1) and applying the Hom construction therefore gives

$$
G_v^2-t_v(\Pi)G_v+q_vs_v(\Pi)=0. \tag{12.2}
$$

The polynomial in (12.2) is monic of degree two, but two-dimensionality alone does **not** make it the characteristic polynomial. If $G_v$ is scalar with value $c$, then every polynomial vanishing at $c$ annihilates it, while its characteristic polynomial is $(X-c)^2$. A nonscalar hypothesis or the independent determinant theorem is therefore logically necessary.

**Proposition 12.1.** Put

$$
Q_v(X)=X^2-t_v(\Pi)X+q_vs_v(\Pi).
$$

Then $Q_v(G_v)=0$. If $G_v$ is nonscalar, or if the polarized packet hypothesis of Section 11.4 and the local normalization (10.15) hold, then

$$
\det(X-G_v\mid W_{\Pi,\ell})=Q_v(X). \tag{12.3}
$$

**Proof.** Equation (12.2) gives the first assertion. If $G_v$ is nonscalar, its minimal polynomial has degree two, divides $Q_v$, and therefore equals both $Q_v$ and the characteristic polynomial. In the polarized case, Cayley--Hamilton gives

$$
G_v^2-\operatorname{Tr}(G_v)G_v+\det(G_v)I=0.
$$

By (11.10), $\det(G_v)=q_vs_v$. Subtracting (12.2) gives $(\operatorname{Tr}(G_v)-t_v)G_v=0$. Frobenius is invertible, so $\operatorname{Tr}(G_v)=t_v$, proving (12.3). This also covers $G_v=cI$: it forces $2c=t_v$ and $c^2=q_vs_v$, hence $Q_v=(X-c)^2$. $\square$

The coefficients are independent of the auxiliary prime in the precise sense that they are the algebraic Hecke eigenvalues in $L_\Pi$, embedded into $L_\lambda$. No compatible-system or bad-prime assertion is made here. Without the packet hypothesis and covariance of Section 10.5, only the quadratic annihilator and the nonscalar inference survive.

### 12.4 Arithmetic Frobenius and the covariant Tate module

On $T_\ell J_K\simeq H^1(1)$, arithmetic Frobenius $F_v$ satisfies

$$
F_v^2-S_v^{-1}T_vF_v+q_vS_v^{-1}=0. \tag{12.4}
$$

On the specialized two-dimensional Tate-module constituent this becomes

$$
X^2-s_v(\Pi)^{-1}t_v(\Pi)X
+q_vs_v(\Pi)^{-1}. \tag{12.5}
$$

Equations (12.3) and (12.5) are not competing normalizations. They concern different operators on differently twisted realizations: geometric Frobenius on untwisted cohomology and arithmetic Frobenius on the covariant Tate module. Inverting Frobenius without converting the twist is the standard source of a misplaced central character.

## 13. Integral lattices, congruences, and boundary phenomena

Rational semisimplicity is exact, but integral cohomology remembers congruences between packets. The correct integral output is a stable lattice inside each rational constituent, not an automatic direct-sum decomposition.

### 13.1 The natural cohomological lattice

The lattice

$$
\Lambda_\ell=H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell)
$$

is finite free, Galois stable, Hecke stable, and self-dual up to the Tate twist. It is also the dual of the covariant Tate module under the principal polarization of the Jacobian. No choice of eigenform enters its definition.

If the integral Hecke image is denoted $\mathbb T_{K,\ell}$, then

$$
\mathbb T_{K,\ell}\longrightarrow
\operatorname{End}_{\mathbf Z_\ell[G_E]}(\Lambda_\ell). \tag{13.1}
$$

The map need not be faithful. Its reductions can have nilpotents even though the rational image algebra is semisimple.

### 13.2 Projector denominators and saturation

Let $e_\Pi$ be the characteristic-zero packet projector over $L_\lambda$. Its interpolation denominators are differences of Hecke eigenvalues and may be divisible by $\lambda\mid\ell$. Then it need not preserve $\Lambda_\ell\otimes\mathcal O_{L_\lambda}$. Define instead the saturated lattice

$$
\Lambda_{\Pi,\lambda}
=\bigl(\Lambda_\ell\otimes_{\mathbf Z_\ell}
\mathcal O_{L_\lambda}\bigr)
\cap e_\Pi\bigl(\Lambda_\ell\otimes_{\mathbf Z_\ell}L_\lambda\bigr), \tag{13.2}
$$

where the intersection is taken inside $\Lambda_\ell\otimes_{\mathbf Z_\ell}L_\lambda$. It is an $\mathcal O_{L_\lambda}$-lattice, is Galois and Hecke stable, is saturated in the coefficient-extended ambient lattice, and spans the desired rational block. It need not be a direct summand of that ambient lattice. If two characteristic-zero packets are congruent modulo $\lambda$, their saturated lattices can meet after reduction, exactly as the denominators in (10.2) predict.

At old level, extracting a rank-two lattice from the multiplicity space also requires an integral Morita theory for the local Hecke module. The rational Hom construction (10.6) does not by itself prove that an integral rank-two Hom module is free, saturated, or canonical. Those are additional integral theorems.

The same distinction applies to the polarized pairing under the packet hypothesis of Section 11.4. Equation (11.7) is perfect over $L_\lambda$, and the determinant identity (11.9) therefore holds on every stable lattice after taking determinants. Perfect reduction of the form is stronger. Every denominator or lattice index contributed by the component multiplier, the fine-cover pull--trace maps, the coefficients of $U$ and $R_{\Pi,K}$, and integral Morita evaluation must be a unit at $\lambda$; the Gram discriminant of (10.19) must also be a unit. If one of these quantities is a nonunit, the rational form may reduce degenerately even though the determinant character still reduces on any stable rank-two lattice.

### 13.3 Coarse-level denominators

At coarse level, rational descent from a neat cover divides by the effective deck-group order. If $\ell$ divides that order, integral invariants need not be exact. Thus even before packet projectors are applied, the coarse lattice can differ from the invariant lattice on a fine cover by torsion.

There are therefore four logically independent sources of denominators:

1. level descent and stabilizer orders;
2. separation of congruent Hecke packets;
3. splitting the Hecke order and performing integral Morita evaluation;
4. the component-twist return construction and the discriminant of its finite-module form.

Avoiding one does not avoid the others. Working at fine level removes inertia but does not make Hecke eigenvalue differences, Morita indices, return coefficients, or pairing discriminants $\ell$-adic units.

### 13.4 What compactness removes

For the division quaternion algebra, compactness removes cusps, boundary cohomology, and the continuous spectrum. It does not remove component permutations, automorphic norm characters in degrees zero and two, oldvectors, integral congruences, or stack inertia at coarse level.

If $B=M_2(F)$, the quotient is noncompact and the present theorem no longer applies as stated. One must compactify, analyze cusp and Eisenstein contributions, and distinguish ordinary, compactly supported, and interior cohomology. Calling those contributions zero by analogy with the division case would be a genuine error.

## 14. Examples and diagnostic calculations

The abstract formulas become easier to use when their different multiplicities and normalizations are tested in small models.

### 14.1 A minimal packet

Suppose $\Pi$ is parallel weight two, occurs at level $K$, and $\Pi_f^K$ is a line. Assume its full Hecke character is separated from every other packet. Then

$$
H^1[\Pi]\simeq
\mathbf C\eta^+\oplus\mathbf C\eta^-.
$$

The first line is holomorphic and the second antiholomorphic. Complex conjugation identifies them only after also conjugating the finite eigenpacket; if the packet is conjugation-stable, they are conjugate inside the same block. Over the Hecke field completion the corresponding etale space is two-dimensional. For the basic group, or under (10.8) for a central modification, the polarized component twist gives determinant $\chi_\ell^{-1}\eta_\Pi$. Hence at a good place $v$ satisfying (10.15), including when Frobenius is scalar, its characteristic polynomial is $X^2-t_v(\Pi)X+q_vs_v(\Pi)$.

No basis of this two-dimensional space is canonical. A normalized holomorphic eigenform chooses a vector in the complex Hodge line, not a Galois-stable line in etale cohomology.

### 14.2 An old packet

Suppose a level change makes $\dim\Pi_f^K=3$. Then the automorphic occurrence is still one, while

$$
\dim H^1[\Pi]=6.
$$

As a module for the full finite Hecke algebra,

$$
H^1[\Pi]\simeq P_\Pi\otimes W_\Pi,
\qquad
\dim P_\Pi=3,
\quad\dim W_\Pi=2.
$$

The three oldvectors lie in $P_\Pi$. Galois acts on $W_\Pi$ because it commutes with the Hecke algebra. Choosing one oldvector gives a copy of $W_\Pi$ only after a noncanonical splitting; the Hom construction recovers it invariantly.

Assume the packet has the contragredient character of (10.8). After a fine refinement on which that character is trivial on the level, the weighted mass form is perfect and symmetric on the whole oldspace. The return construction (10.18)--(10.21) transports a perfect symmetric form to this three-dimensional $P_\Pi$ and leaves a perfect alternating form on $W_\Pi$. Thus oldvectors change neither the determinant character nor, at a good place satisfying (10.15), the scalar-Frobenius conclusion.

### 14.3 A component-permuting central operator

Let $S_v$ be central and suppose its class in the component quotient is nontrivial. On the disjoint union of all labels in one orbit, $S_v$ acts as a cyclic permutation, possibly multiplied by a scalar on an automorphic central-character line. On a single label it is not an endomorphism at all.

After passing to a component-stable union and a central-character summand, $S_v$ acts by $s_v$. Only then may the good polynomial be written as

$$
G_v^2-t_vG_v+q_vs_v=0.
$$

Replacing $S_v$ by $1$ before fixing the central character would erase both the component motion and the nebentype.

With the reciprocity normalization (10.13), the same scalar satisfies $\eta_\Pi(\Phi_u)=s_v$ for geometric Frobenius. The alternating rank-two target is therefore $L_\lambda(-1)\otimes\eta_\Pi$, whose Frobenius scalar is $q_vs_v$. This is the independent determinant used to handle a scalar $G_v$.

### 14.4 Four normalization failures

Four quick tests catch most errors.

First, reversing the span replaces $T(a)$ by $T(a^{-1})$. The graph test detects the reversal.

Second, dividing the trace by $[K:K_a]$ changes the unnormalized operator and makes constants have the wrong eigenvalue $q_v+1$ at a hyperspecial place.

Third, writing the same Frobenius polynomial on untwisted $H^1$ and on $T_\ell J$ ignores (3.4) and moves $S_v$ to the wrong side.

Fourth, concluding that a $2r$-dimensional old packet gives a $2r$-dimensional irreducible Galois representation confuses the Hecke module $P_\Pi$ with the two-dimensional multiplicity space $W_\Pi$.

## 15. The automorphic realization theorem

We finish by collecting the geometric, automorphic, rational, and arithmetic structures into one reusable theorem.

### 15.1 Complete statement

**Theorem 15.1 (automorphic decomposition of Shimura-curve $H^1$).** Let $F$ be totally real, let $B/F$ be a quaternion division algebra split at exactly one real place, and let $(G,X)$ be the basic quaternionic Shimura datum or a specified connected central modification with a genuine PEL realization. Let $K\subset G(\mathbf A_f)$ be any compact open, and let $C_K/E$ be the smooth projective coarse canonical curve attached to a Galois-stable union of selected components which is a full orbit under the finite Hecke and component-routing algebra used in the decomposition. At non-neat level, all characteristic-zero statements are obtained from a normal neat cover as in Section 2.4. Then:

1. The complex cohomology has the Hecke-equivariant decomposition

   $$
   H_B^1(C_K,\mathbf C)
   \simeq
   \bigoplus_{\Pi\in\mathcal P_K}
   \mathcal M(\Pi)\otimes\Pi_f^K\otimes A^1(\Pi_\infty),
   $$

   where $\mathcal P_K$ consists exactly of the noncharacter parallel-weight-two quaternionic automorphic representations compatible with the central and component data, $\dim\mathcal M(\Pi)=1$, and $A^1(\Pi_\infty)$ has dimension two with Hodge types $(1,0)$ and $(0,1)$.

2. In particular,

   $$
   \dim H_B^1[\Pi]=2\dim\Pi_f^K.
   $$

   Norm characters and all other infinity types contribute zero to $H^1$.

3. The finite rational Hecke image is semisimple. Its primitive rational central idempotents cut $H_B^1$ into polarizable rational Hodge structures. After a finite splitting field $L$ is chosen, every simple packet block has the form

   $$
   P_\Pi\otimes_L W_{\Pi,B},
   \qquad \dim_LW_{\Pi,B}=2.
   $$

4. Betti--de Rham and Betti--etale comparison transport these blocks and all Hecke actions. The de Rham block is a rank-two multiplicity module factor by factor over $E\otimes_{\mathbf Q}L$. For every $\lambda\mid\ell$, the etale multiplicity construction gives a continuous two-dimensional $L_\lambda$-representation

   $$
   W_{\Pi,\ell}
   =\operatorname{Hom}_{A_{L_\lambda}}
   (P_{\Pi,\lambda},e_\Pi H^1_{\mathrm{et}}(C_{K,\bar E},L_\lambda)).
   $$

5. Suppose $G$ is the basic group, or, for a connected central modification, suppose that the packet has a finite-order automorphic character $\kappa_\Pi$ on the actual abelian quotient, trivial at infinity, satisfying (10.8). Let $\eta_\Pi$ be its reflex-reciprocity character (10.13). The component multiplier on a normal fine refinement, followed by the return construction (10.18)--(10.21), supplies a Poincare-compatible perfect symmetric form on the complete finite module $P_{\Pi,\lambda}$ and a perfect alternating pairing

   $$
   W_{\Pi,\ell}\times W_{\Pi,\ell}
   \longrightarrow L_\lambda(-1)\otimes\eta_\Pi.
   $$

   Consequently

   $$
   W_{\Pi,\ell}^\vee
   \simeq W_{\Pi,\ell}(1)\otimes\eta_\Pi^{-1},
   \qquad
   \det\rho_{\Pi,\lambda}
   =\chi_\ell^{-1}\eta_\Pi.
   $$

   This includes nonminimal old level and rational blocks with nontrivial Schur algebra, after the stated finite splitting field is chosen.

6. At corresponding places $u$ of $E$ and $v$ of $F$, with equal residue fields, satisfying every unramified PEL, self-dual polarization, hyperspecial level, smooth determinant-model, rank-one incidence, $\mu$-ordinary-density, component-extension, and fine-or-tame hypothesis of Section 12.1, and with $v\nmid\ell$, the representation is unramified and geometric Frobenius is annihilated by

   $$
   X^2-t_v(\Pi)X+q_vs_v(\Pi).
   $$

   Under the hypothesis of assertion 5 and the central-generator reciprocity normalization (10.15), this polynomial is its characteristic polynomial, including when Frobenius is scalar.

7. The natural lattice $H^1_{\mathrm{et}}(C_{K,\bar E},\mathbf Z_\ell)$ is Galois and Hecke stable. After coefficient extension, a packet defines the saturated $\mathcal O_{L_\lambda}$-lattice (13.2) in its rational block. No integral direct-sum, rank-two Morita factor, or perfect integral self-pairing is asserted unless all level-descent, projector, splitting-order, evaluation, component-return, and pairing-discriminant denominators are $\ell$-adic units.

At arbitrary level the rational conclusions, including assertion 5 when its packet hypothesis holds, follow from a normal fine cover and the pull--trace return construction. Integral conclusions retain every denominator qualification above. For a proper component union preserved only by a smaller Hecke algebra, the rational block and comparison conclusions remain valid after applying its component projector, but assertions 1--2 are grouped by the component-character families which that projector mixes; the individual-$\Pi$ formula, determinant, and scalar-Frobenius conclusion require a separating component-character idempotent.

Assertion 5 is exactly the **curve determinant datum** used in Book 134, Section 6.3, and retained in Book 135, Sections 3.3 and 7.1: it supplies the actual component twist with (10.14), the symmetric perfect finite-module form at the stated level, and their compatibility with Poincare polarization. Together with the central-generator normalization required in assertion 6, it supplies the scalar-Frobenius clause; no additional determinant datum is required for the compact quaternionic curve packets satisfying this theorem. This interface does not manufacture such a datum for a different curve carrier lacking the component and return construction above.

### 15.2 Proof

**Proof strategy.** We pass in a fixed order: construct the proper curve and its correspondences, identify geometric pull--push with adelic convolution, decompose harmonic forms, compute the unique cohomological infinity type, descend the finite Hecke blocks to rational structures, and only then transport them to etale cohomology and specialize Frobenius.

The quaternionic PEL and canonical-model packages give the smooth projective curve, component labels, and canonical descent. Division of $B$ gives compactness. The uniformization and Hecke-descent theorem constructs the two finite legs, proves their component routing, and descends them to $E$. General curve correspondence theory turns the spans into actions on Jacobians and cohomology; comparison identifies those actions with the covariant Tate-module action. The common Hecke-action theorem declares the translated leg to be the source and the forgetful leg to be the target, identifies $(p_1)_*p_2^*$ with unnormalized right convolution, and proves the good-prime relation (12.1).

Compactness gives the discrete automorphic spectrum. Quaternionic automorphic theory gives restricted tensor factorization, fixed-level finiteness, and multiplicity one by the character-clean trace argument. The direct proof of Matsushima's formula in Chapter 6 identifies $H^1$ with finite-level vectors tensored with relative Lie algebra cohomology after the positive split center is removed. The rank-one classification and cohomology theorem recalled in Chapter 7 compute that cohomology: it is two-dimensional exactly for the parallel-weight-two type and zero for characters and all other types. This proves assertions 1 and 2.

Transpose correspondences make the finite complex Hecke image adjoint stable. The radical argument in Section 9.2 proves semisimplicity, yielding rational central idempotents. The double-centralizer calculation then proves the rank-two factorization and assertion 3. Comparison isomorphisms commute with all correspondences, and canonical descent makes their images Galois stable. Applying $\operatorname{Hom}_{A}(P_\Pi,-)$ proves assertion 4.

For assertion 5, canonical quaternion conjugation gives (10.8) for the basic group; for a central modification it is the stated packet hypothesis. Refine the level until the resulting character twist is level trivial. Multiplication by the character on the open-and-closed component summands is self-transpose and has the reciprocity covariance (10.14). The weighted compact mass form is symmetric and nondegenerate on the entire finite oldspace, so factoring the alternating Jacobian polarization leaves the perfect alternating form (11.7) on the rank-two factor. At the original level, a full-matrix Hecke return map embeds its finite module as a nondegenerate subspace; pull--trace adjunction returns a pairing with the same rank-two factor and multiplier. All relevant Schur algebras are split before this matrix argument. The two-dimensional determinant identity then gives (11.9).

At a good prime, smooth proper base change gives unramifiedness and transfers the special-fiber correspondence relation to generic cohomology. Restriction gives the quadratic annihilator. Under assertion 5 and (10.15), its constant term agrees with the independent determinant (11.10), and Proposition 12.1 then proves the characteristic polynomial even for scalar Frobenius. Without that polarized input, only the annihilator, and the nonscalar characteristic-polynomial inference, is asserted. Finally, integral curve cohomology is finite free and stable under integral correspondences. Intersecting the coefficient-extended lattice with the rational packet subspace gives (13.2), while Sections 13.2--13.3 retain every denominator obstructing a direct splitting or perfect integral pairing. This proves assertions 6--7 and the coarse-level clause. $\square$

### 15.3 Hypothesis and dependency ledger

| conclusion | input and retained hypothesis | failure if omitted |
|---|---|---|
| smooth projective Shimura curve | quaternionic canonical model and genuine PEL realization; $B$ division and split at exactly one real place | the moduli space can have the wrong dimension, or cusps can appear |
| componentwise Galois and Hecke action | selected union stable under reciprocity and Hecke routing | a correspondence maps between different curves or Galois permutes the component |
| algebraic Hecke span | exact intersection level and translated-then-forgotten second leg | right translation has the wrong target and the double coset is mislabeled |
| pull--push on $H^1$ and Jacobians | smooth proper curves; finite legs; constant coefficients | traces or norms can be undefined or need boundary data |
| perfect alternating geometric pairing | componentwise curve trace and the product principal polarization on component Jacobians | degrees or volume factors can corrupt adjunction and the Tate twist |
| integral etale lattice | $\ell$ invertible and smooth proper curve | torsion and derived-limit corrections can occur in other settings |
| complex automorphic decomposition | compact quotient, fixed level, harmonic theory | continuous and boundary spectra must be added in the split case |
| multiplicity one | quaternion division algebra and the character-clean two-place trace and Bessel argument | compactness alone gives only finite multiplicity; the additive transposition kernel cannot see the occurrence space |
| parallel-weight-two classification | exactly one active rank-one real factor; constant coefficients; connected split center removed | other degrees or coefficient weights require a different real calculation, and retaining the split-center line shifts degrees |
| rational packet projector | full finite adjoint-stable Hecke image | the away-from-bad commutative algebra can group near-equivalent packets |
| a vector-space rank-two factor | finite coefficient extension splitting the simple Hecke algebra | a Schur division algebra can remain over the rationality field |
| Galois stability | Hecke correspondences descended to $E$ | invariant eigenvalues do not descend an operator |
| descended adjoint twist | canonical quaternion-conjugation identity for the basic group, or hypothesis (10.8) for a central modification; normal fine refinement inside the character kernel; component reciprocity | common adjoint data do not produce the twist, multiplication by it need not preserve the original level, and equality of central eigenvalues gives no covariance |
| symmetric finite-module form at old level | weighted compact mass pairing at the refinement; full split Hecke image and pull--trace return | an arbitrary Morita pairing can have the wrong sign or be degenerate on the returned oldspace |
| determinant and essential self-duality | component covariance, symmetric finite-module form, and alternating Jacobian polarization | adjoint duality alone does not identify the determinant line |
| good Frobenius relation | every residue-field, unramified PEL, self-dual polarization, hyperspecial, determinant-model, incidence-model, $\mu$-ordinary-density, component, fineness, and $v\nmid\ell$ hypothesis of Section 12.1 | a level-prime $U_v$, bad local model, contracted branch, or residue-field mismatch has no displayed quadratic relation |
| good characteristic polynomial, including scalar Frobenius | quadratic relation plus the independently proved determinant | a degree-two annihilator alone need not be the characteristic polynomial of a scalar operator |
| rational comparison with a split packet | global Jacquet--Langlands only in its exact selected range | local matching alone does not globalize an automorphic representation |
| integral direct summand and perfect pairing | deck-group order and every projector, order, Morita, return, and discriminant denominator prime to $\ell$ | congruent packets or inertia can meet, and a rational perfect form can reduce degenerately |

The exact direct dependency row is

$$
\boxed{132\mid 20,\ 27,\ 37,\ 93,\ 94,\ 99,\ 122,\ 126,\ 127,\ 128.}
$$

The direct prerequisites close the argument as follows. Book 20 supplies continuous etale $H^1$, componentwise Poincare duality, the Tate-twist and Frobenius conventions, and Galois-equivariant pull--trace for smooth proper curves with $\ell$ invertible. Book 27 supplies Betti--de Rham--etale comparison and compatibility with rational correspondences for curves over a field embedded in $\mathbf C$. Book 37 supplies the Jacobian, its canonical principal polarization, the covariant Tate module, Kummer comparison, Weil--cup compatibility, and transpose--Rosati compatibility. Book 93 applies because $B$ is a division quaternion algebra; it supplies the discrete restricted tensor decomposition, quaternionic multiplicity one, finite norm twists, the precise warning that a twist preserves level only after refinement, contragredient finite modules, and the compact mass pairing. Book 94 is invoked only for a selected global transfer satisfying that book's totally real, totally definite, and local packet hypotheses; it is not used to transfer the one-split-place representation in general. Book 99 supplies the full $\operatorname{GL}_2(\mathbf R)$ discrete-series classification in the required infinitesimal-character range, the split-center convention, and the two-line constant-coefficient relative-cohomology calculation. These are substantial proof inputs, not consequences of tangent-weight counting alone.

Book 122 supplies the common geometric--adelic Hecke action, exact inverse-double-coset adjoints and central factors, and the good-prime operator relation under the complete list reproduced in Section 12.1. Book 126 supplies the one-split-place Shimura datum, reflex field, canonical model, actual abelian quotient, positive-at-infinity reflex reciprocity, and its action on components. Book 127 supplies the genuine PEL functor, fine representability, dimension-one local model, and projectivity in the division case. Book 128 supplies complex uniformization, exact component labels, normal fine/coarse level maps, the two underlying finite maps, component routing, span-level convolution and transpose, and canonical descent. Its displayed $p_{2*}p_1^*$ convention is not used to name the right double coset: Book 122's later orientation audit shows that the right-convolution action for those same maps is $(p_1)_*p_2^*$. The component multiplier, return operator, polarized Morita factorization, determinant, and scalar-Frobenius upgrade are proved here. No later cohomological extraction theorem is used.

### 15.4 Conclusion

The first cohomology of a compact quaternionic Shimura curve is now described by one coherent object seen in several realizations. Analytically, harmonic one-forms decompose through the discrete automorphic spectrum. The unique active real factor forces the minimal weight-two discrete series, and its two orientation classes become the holomorphic and antiholomorphic lines. Quaternionic multiplicity one removes repeated global occurrences, leaving the exact formula

$$
\dim H^1[\Pi]=2\dim\Pi_f^K.
$$

Geometrically, the same finite adelic double cosets are algebraic correspondences. Their pull--push action agrees with unnormalized right convolution, their transpose is inversion, and their component routing is governed by the actual abelian quotient. Canonical descent makes those operators commute with arithmetic Galois. The Jacobian and Kummer theory supply the integral lattice, while comparison identifies its Betti, de Rham, and etale forms.

Rationality requires one last distinction. A Hecke eigensystem, a simple finite Hecke module, and its two-dimensional cohomological multiplicity space are not the same object. The finite adjoint-stable Hecke image separates rational blocks; a splitting field resolves any Schur obstruction; and the double-centralizer Hom space extracts the intrinsic rank-two constituent even at old level. For the basic group, or for a central-modification packet satisfying (10.8), a fine-level component multiplier and its pull--trace return supply the missing polarized datum at every level. The finite oldspace form is symmetric, the rank-two form is alternating with target $L_\lambda(-1)\otimes\eta_\Pi$, and

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

Therefore, at a genuinely good place satisfying (10.15), the characteristic polynomial of geometric Frobenius, including in the scalar case, is

$$
X^2-t_vX+q_vs_v.
$$

The integral lattice remembers what rational semisimplicity forgets. Projector, coarse-level, Morita, return-map, and pairing-discriminant denominators can join packets or destroy perfect reduction, so saturation is unconditional, while the rational determinant requires the polarized packet hypothesis and direct integral splitting and perfect integral self-duality require the stated unit conditions. Compactness removes cusps, not congruences, components, or oldvectors. With those boundaries explicit, constant-coefficient $H^1$ gives the promised automorphic realization of every quaternionic parallel-weight-two packet occurring on the curve and isolates its two-dimensional arithmetic constituent without suppressing multiplicity, coefficient fields, twists, or level geometry.
